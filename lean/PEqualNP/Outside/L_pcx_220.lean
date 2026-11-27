import PEqualNP.Defs
import PEqualNP.Outside.L_clb_049

namespace PEqualNP.Outside.L_pcx_220_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.ProofComplexity

theorem dite_pos {p : Prop} [Decidable p] {α : Sort*} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h :=
  dite_eq_left_of_eq_true (eq_true h)

theorem dite_neg {p : Prop} [Decidable p] {α : Sort*} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h :=
  dite_eq_right_of_eq_false (eq_false h)

namespace GateBridge

variable {α : Type*}

def Scheduled (n : Nat) (F : α → (Fin n → Bool) → Bool) (k : Nat) (S : Set α) : Prop :=
  ∃ gs : List Gate, gs.length = k ∧ ReadsBack n ⟨gs, 0⟩ ∧ FanInTwo ⟨gs, 0⟩ ∧
    ∀ a ∈ S, ∃ i : Nat, i < n + k ∧
      ∀ x : Fin n → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = F a x

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

theorem start {n : Nat} {F : α → (Fin n → Bool) → Bool}
    (input : Fin n → α) (h : ∀ i x, F (input i) x = x i) :
    Scheduled n F 0 (Set.range input) := by
  refine ⟨[], rfl, ?_, ?_, ?_⟩
  · simp [ReadsBack]
  · simp [FanInTwo]
  · intro a ha
    obtain ⟨i, rfl⟩ := Set.mem_range.mp ha
    refine ⟨i.val, by simp, fun x => ?_⟩
    change (List.ofFn x).getD i.val false = F (input i) x
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn, h i x]

theorem restrict {n k : Nat} {F : α → (Fin n → Bool) → Bool} {S T : Set α}
    (h : Scheduled n F k S) (hsub : T ⊆ S) : Scheduled n F k T := by
  obtain ⟨gs, hs, hr, hf, hw⟩ := h
  exact ⟨gs, hs, hr, hf, fun a ha => hw a (hsub ha)⟩

theorem realizeDeps {n k : Nat} {F : α → (Fin n → Bool) → Bool} {S : Set α}
    {gs : List Gate}
    (hw : ∀ a ∈ S, ∃ i : Nat, i < n + k ∧
      ∀ x : Fin n → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = F a x)
    (deps : List α) (hdeps : ∀ a ∈ deps, a ∈ S) :
    ∃ is : List Nat, is.length = deps.length ∧ (∀ i ∈ is, i < n + k) ∧
      ∀ x : Fin n → Bool,
        is.map (fun i => ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false) =
          deps.map (fun a => F a x) := by
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

theorem push {n k : Nat} {F : α → (Fin n → Bool) → Bool} {S : Set α}
    (h : Scheduled n F k S) (op : GateOp) (deps : List α) (out : α)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : deps.length ≤ 2) (hdeps : ∀ a ∈ deps, a ∈ S)
    (hval : ∀ x, F out x = op.eval (deps.map fun a => F a x)) :
    Scheduled n F (k + 1) (insert out S) := by
  obtain ⟨gs, hgs, hr, hf, hw⟩ := h
  obtain ⟨is, his, hbound, hvalues⟩ := realizeDeps hw deps hdeps
  let g : Gate := ⟨op, is⟩
  have hlength (x : Fin n → Bool) :
      ((Circuit.mk gs 0).wires (List.ofFn x)).length = n + k := by
    rw [wireLength]
    simpa using congrArg (n + ·) hgs
  have hsnoc (x : Fin n → Bool) :
      (Circuit.mk (gs ++ [g]) 0).wires (List.ofFn x) =
        (Circuit.mk gs 0).wires (List.ofFn x) ++ [F out x] := by
    simp only [Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (Circuit.mk gs 0).wires (List.ofFn x) ++
      [op.eval (is.map fun i => ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false)] =
        (Circuit.mk gs 0).wires (List.ofFn x) ++ [F out x]
    rw [hvalues x, hval x]
  refine ⟨gs ++ [g], by simp [hgs], ?_, ?_, ?_⟩
  · intro j hj i hi
    change j < (gs ++ [g]).length at hj
    change i ∈ ((gs ++ [g]).getD j ⟨GateOp.or, []⟩).inputs at hi
    by_cases hj' : j < gs.length
    · rw [List.getD_append _ _ _ _ hj'] at hi
      exact hr j hj' i hi
    · have heq : j = gs.length := by
        simp only [List.length_append, List.length_singleton] at hj
        omega
      subst j
      rw [List.getD_append_right _ _ _ _ le_rfl] at hi
      have hi' : i ∈ is := by simpa [g] using hi
      simpa [hgs] using hbound i hi'
  · intro g' hg'
    change g' ∈ gs ++ [g] at hg'
    rcases List.mem_append.mp hg' with hg' | hg'
    · exact hf g' hg'
    · have heq : g' = g := List.mem_singleton.mp hg'
      subst g'
      refine ⟨hop, ?_⟩
      change is.length ≤ 2
      simpa only [his] using hlen
  · intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · refine ⟨n + k, by omega, fun x => ?_⟩
      rw [hsnoc x, List.getD_append_right _ _ _ _ (by simp [hlength x])]
      simp [hlength x]
    · obtain ⟨i, hi, hval'⟩ := hw a ha
      refine ⟨i, by omega, fun x => ?_⟩
      rw [hsnoc x, List.getD_append _ _ _ _ (by simpa [hlength x] using hi), hval' x]

end GateBridge

namespace Build220

variable {n : Nat}
abbrev Sig (n : Nat) := (Fin n → Bool) → Bool

def Build (A B : Set (Sig n)) (b : Nat) : Prop :=
  True ∧ (∀ {m S}, GateBridge.Scheduled n id m S → A ⊆ S →
    ∃ c ≤ b, GateBridge.Scheduled n id (m + c) (S ∪ B))

theorem Build.run {A B : Set (Sig n)} {b m S} (H : Build A B b)
    (HS : GateBridge.Scheduled n id m S) (hA : A ⊆ S) :
    ∃ c ≤ b, GateBridge.Scheduled n id (m + c) (S ∪ B) := H.2 HS hA

theorem idle {A B : Set (Sig n)} (h : B ⊆ A) : Build A B 0 := by
  refine ⟨trivial, ?_⟩
  intro m S HS hA
  refine ⟨0, Nat.le_refl _, ?_⟩
  simpa [Set.union_eq_left.mpr (h.trans hA)] using HS

theorem relax {A B C D : Set (Sig n)} {b d : Nat}
    (H : Build A B b) (hA : A ⊆ C) (hB : D ⊆ B) (h : b ≤ d) : Build C D d := by
  refine ⟨trivial, ?_⟩
  intro m S HS hC
  obtain ⟨c, hc, HS'⟩ := H.run HS (hA.trans hC)
  exact ⟨c, hc.trans h, GateBridge.restrict HS' (Set.union_subset_union le_rfl hB)⟩

theorem seq {A B C : Set (Sig n)} {b c : Nat}
    (H : Build A B b) (J : Build (A ∪ B) C c) : Build A (B ∪ C) (b + c) := by
  refine ⟨trivial, ?_⟩
  intro m S HS hA
  obtain ⟨d, hd, K⟩ := H.run HS hA
  obtain ⟨e, he, K'⟩ := J.run K (Set.union_subset_union hA le_rfl)
  exact ⟨d + e, Nat.add_le_add hd he, by simpa [Nat.add_assoc, Set.union_assoc] using K'⟩

theorem seqS {A B C D : Set (Sig n)} {b c : Nat}
    (H : Build A B b) (J : Build D C c) (hsub : D ⊆ A ∪ B) : Build A (B ∪ C) (b + c) :=
  seq H (relax J hsub le_rfl le_rfl)

theorem stepSub {α : Type*} {A B_acc B_new D : Set α} (hD : D ⊆ A ∪ B_acc) :
    D ∪ B_new ⊆ A ∪ (B_acc ∪ B_new) :=
  Set.union_subset (hD.trans (Set.union_subset_union_right A Set.subset_union_left))
    (Set.subset_union_right.trans Set.subset_union_right)

theorem one {A : Set (Sig n)} (op : GateOp) (deps : List (Sig n))
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (hlen : deps.length ≤ 2)
    (hd : ∀ g ∈ deps, g ∈ A) (f : Sig n)
    (hv : ∀ x, f x = op.eval (deps.map fun g => g x)) : Build A {f} 1 := by
  refine ⟨trivial, ?_⟩
  intro m S HS hA
  refine ⟨1, le_rfl, ?_⟩
  have h := GateBridge.push HS op deps f hop hlen (fun g hg => hA (hd g hg)) hv
  rw [Set.insert_eq] at h
  exact GateBridge.restrict h (by intro g hg; exact hg.elim Or.inr Or.inl)

def an (f g : Sig n) : Sig n := fun x => f x && g x
def or (f g : Sig n) : Sig n := fun x => f x || g x
def nt (f : Sig n) : Sig n := fun x => !f x

theorem andG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {an f g} 1 :=
  one .and [f, g] (by simp) (by simp) (by simpa using And.intro hf hg) _ (by simp [GateOp.eval, an])

theorem orG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {or f g} 1 :=
  one .or [f, g] (by simp) (by simp) (by simpa using And.intro hf hg) _ (by simp [GateOp.eval, or])

theorem notG {A : Set (Sig n)} {f : Sig n} (hf : f ∈ A) : Build A {nt f} 1 :=
  one .not [f] (by simp) (by simp) (by simpa using hf) _ (by simp [GateOp.eval, nt])

theorem constG {A : Set (Sig n)} (b : Bool) : Build A {fun _ => b} 1 := by
  cases b
  · exact one .or [] (by simp) (by simp) (by simp) _ (by intro; rfl)
  · exact one .and [] (by simp) (by simp) (by simp) _ (by intro; rfl)

theorem muxG {A : Set (Sig n)} {sw nsw t f : Sig n}
    (hsw : sw ∈ A) (hnsw : nsw ∈ A) (ht : t ∈ A) (hf : f ∈ A)
    (hneg : ∀ x, nsw x = !(sw x)) :
    Build A {fun x => if sw x then t x else f x} 3 := by
  have he : (fun x => if sw x then t x else f x) = or (an sw t) (an nsw f) := by
    funext x
    simp only [or, an, hneg x]
    cases sw x <;> cases t x <;> cases f x <;> rfl
  rw [he]
  have h1 := andG hsw ht
  have h2 := andG (A := A ∪ {an sw t}) (Or.inl hnsw) (Or.inl hf)
  have h3 := orG (A := A ∪ ({an sw t} ∪ {an nsw f}))
    (f := an sw t) (g := an nsw f) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
  exact relax (seq (seq h1 h2) h3) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl

theorem muxG4 {A : Set (Sig n)} {sw t f : Sig n}
    (hsw : sw ∈ A) (ht : t ∈ A) (hf : f ∈ A) :
    Build A {fun x => if sw x then t x else f x} 4 := by
  have h1 := notG hsw
  have h2 := muxG (A := A ∪ {nt sw}) (Or.inl hsw) (Or.inr rfl) (Or.inl ht) (Or.inl hf) (fun _ => rfl)
  exact relax (seq h1 h2) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl

theorem listBuild {α : Type*} {A : Set (Sig n)} (xs : List α)
    (F : α → Sig n) (c : Nat) (H : ∀ a ∈ xs, Build A {F a} c) :
    Build A {f | ∃ a ∈ xs, f = F a} (xs.length * c) := by
  induction xs with
  | nil =>
    exact relax (idle (A := A) (B := ∅) (by simp)) le_rfl (by simp) (by simp)
  | cons a xs ih =>
    have h1 := H a List.mem_cons_self
    have h2 := ih (fun b hb => H b (List.mem_cons_of_mem a hb))
    have h2' := relax h2 (C := A ∪ {F a}) Set.subset_union_left le_rfl le_rfl
    refine relax (seq h1 h2') le_rfl ?_ ?_
    · rintro f ⟨b, hb, rfl⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · exact Or.inl rfl
      · exact Or.inr ⟨b, hb, rfl⟩
    · simp only [List.length_cons]
      rw [Nat.succ_mul xs.length, Nat.add_comm]

theorem listBuildSet {α : Type*} {A : Set (Sig n)} (xs : List α)
    (B : α → Set (Sig n)) (c : Nat) (H : ∀ a ∈ xs, Build A (B a) c) :
    Build A (⋃ a ∈ xs, B a) (xs.length * c) := by
  induction xs with
  | nil =>
    exact relax (idle (A := A) (B := ∅) (by simp)) le_rfl (by simp) (by simp)
  | cons a xs ih =>
    have h1 := H a List.mem_cons_self
    have h2 := ih (fun b hb => H b (List.mem_cons_of_mem a hb))
    have h2' := relax h2 (C := A ∪ B a) Set.subset_union_left le_rfl le_rfl
    refine relax (seq h1 h2') le_rfl ?_ ?_
    · intro f hf
      simp only [Set.mem_iUnion, List.mem_cons] at hf
      rcases hf with ⟨b, rfl | hb, hfb⟩
      · exact Or.inl hfb
      · exact Or.inr (Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨hb, hfb⟩⟩)
    · simp only [List.length_cons]
      rw [Nat.succ_mul xs.length, Nat.add_comm]

theorem finG {k : Nat} {A : Set (Sig n)} (F : Fin k → Sig n) (c : Nat)
    (H : ∀ i, Build A {F i} c) : Build A (Set.range F) (k * c) := by
  have h := listBuild (List.finRange k) F c (fun i _ => H i)
  rw [List.length_finRange] at h
  refine relax h le_rfl ?_ le_rfl
  rintro _ ⟨i, rfl⟩
  exact ⟨i, List.mem_finRange i, rfl⟩

theorem orListG {A : Set (Sig n)} (fs : List (Sig n))
    (hfs : ∀ f ∈ fs, f ∈ A) (hfalse : (fun _ => false) ∈ A) :
    Build A {fun x => fs.any (fun f => f x)} fs.length := by
  induction fs with
  | nil =>
    have he : (fun x : Fin n → Bool => ([] : List (Sig n)).any (fun f => f x)) = (fun _ => false) := rfl
    rw [he]
    exact relax (idle (Set.singleton_subset_iff.mpr hfalse)) le_rfl le_rfl (by simp)
  | cons f fs ih =>
    have h1 := ih (fun g hg => hfs g (List.mem_cons_of_mem f hg))
    have h2 := orG (A := A ∪ {fun x => fs.any (fun g => g x)})
      (Or.inl (hfs f List.mem_cons_self)) (Or.inr rfl)
    refine relax (seq h1 h2) le_rfl ?_ (by simp)
    rw [Set.singleton_subset_iff]
    exact Or.inr rfl

theorem andListG {A : Set (Sig n)} (fs : List (Sig n))
    (hfs : ∀ f ∈ fs, f ∈ A) (htrue : (fun _ => true) ∈ A) :
    Build A {fun x => fs.all (fun f => f x)} fs.length := by
  induction fs with
  | nil =>
    have he : (fun x : Fin n → Bool => ([] : List (Sig n)).all (fun f => f x)) = (fun _ => true) := rfl
    rw [he]
    exact relax (idle (Set.singleton_subset_iff.mpr htrue)) le_rfl le_rfl (by simp)
  | cons f fs ih =>
    have h1 := ih (fun g hg => hfs g (List.mem_cons_of_mem f hg))
    have h2 := andG (A := A ∪ {fun x => fs.all (fun g => g x)})
      (Or.inl (hfs f List.mem_cons_self)) (Or.inr rfl)
    refine relax (seq h1 h2) le_rfl ?_ (by simp)
    rw [Set.singleton_subset_iff]
    exact Or.inr rfl

theorem xorG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {fun x => xor (f x) (g x)} 5 := by
  have he : (fun x => xor (f x) (g x)) = or (an f (nt g)) (an (nt f) g) := by
    funext x; simp only [or, an, nt]; cases f x <;> cases g x <;> rfl
  rw [he]
  have h1 := notG hf
  have h2 := notG (A := A ∪ {nt f}) (Or.inl hg)
  have h3 := andG (A := A ∪ ({nt f} ∪ {nt g})) (Or.inl hf) (Or.inr (Or.inr rfl))
  have h4 := andG (A := A ∪ (({nt f} ∪ {nt g}) ∪ {an f (nt g)})) (Or.inr (Or.inl (Or.inl rfl))) (Or.inl hg)
  have h5 := orG (A := A ∪ ((({nt f} ∪ {nt g}) ∪ {an f (nt g)}) ∪ {an (nt f) g}))
    (Or.inr (Or.inl (Or.inr rfl))) (Or.inr (Or.inr rfl))
  exact relax (seq (seq (seq (seq h1 h2) h3) h4) h5) le_rfl
    (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl

theorem beqG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {fun x => f x == g x} 6 := by
  have h1 := xorG hf hg
  have h2 := notG (A := A ∪ {fun x => xor (f x) (g x)}) (Or.inr rfl)
  have he : nt (fun x => xor (f x) (g x)) = (fun x => f x == g x) := by
    funext x; simp only [nt]; cases f x <;> cases g x <;> rfl
  rw [he] at h2
  exact relax (seq h1 h2) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl

def combMask (hasPos hasNeg m0 m1 : Bool) : Bool :=
  if !hasPos then m0 else if !hasNeg then m1 else m0 || m1

theorem combMask_eq (hasPos hasNeg m0 m1 : Bool) :
    combMask hasPos hasNeg m0 m1 = (((!hasPos || hasNeg) && m0) || (hasPos && m1)) := by
  cases hasPos <;> cases hasNeg <;> cases m0 <;> cases m1 <;> rfl

theorem combMaskG {A : Set (Sig n)} {hp c0 m0 m1 : Sig n}
    (hhp : hp ∈ A) (hc0 : c0 ∈ A) (hm0 : m0 ∈ A) (hm1 : m1 ∈ A)
    (hn : Sig n) (hc0_eq : ∀ x, c0 x = (!hp x || hn x)) :
    Build A {fun x => combMask (hp x) (hn x) (m0 x) (m1 x)} 3 := by
  have he : (fun x => combMask (hp x) (hn x) (m0 x) (m1 x)) = or (an c0 m0) (an hp m1) := by
    funext x; simp only [or, an, hc0_eq x, combMask_eq]
  rw [he]
  have h1 := andG hc0 hm0
  have h2 := andG (A := A ∪ {an c0 m0}) (Or.inl hhp) (Or.inl hm1)
  have h3 := orG (A := A ∪ ({an c0 m0} ∪ {an hp m1})) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
  exact relax (seq (seq h1 h2) h3) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl

theorem ltStepG {A : Set (Sig n)} {xm ym prev : Sig n}
    (hx : xm ∈ A) (hy : ym ∈ A) (hp : prev ∈ A) :
    Build A {fun v => (!(xm v) && ym v) || ((!(xm v) || ym v) && prev v)} 5 := by
  have h1 := notG hx
  have h2 := andG (A := A ∪ {nt xm}) (Or.inr rfl) (Or.inl hy)
  have h3 := orG (A := A ∪ ({nt xm} ∪ {an (nt xm) ym}))
    (Or.inr (Or.inl rfl)) (Or.inl hy)
  have h4 := andG (A := A ∪ (({nt xm} ∪ {an (nt xm) ym}) ∪ {or (nt xm) ym}))
    (Or.inr (Or.inr rfl)) (Or.inl hp)
  have h5 := orG (A := A ∪ ((({nt xm} ∪ {an (nt xm) ym}) ∪ {or (nt xm) ym}) ∪ {an (or (nt xm) ym) prev}))
    (Or.inr (Or.inl (Or.inl (Or.inr rfl)))) (Or.inr (Or.inr rfl))
  exact relax (seq (seq (seq (seq h1 h2) h3) h4) h5) le_rfl
    (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl

def bitsVal (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | m + 1 => bitsVal f m + if f m then 2 ^ m else 0

theorem bitsVal_lt (f : Nat → Bool) : ∀ m, bitsVal f m < 2 ^ m
  | 0 => by simp [bitsVal]
  | m + 1 => by
    have ih := bitsVal_lt f m
    simp only [bitsVal, Nat.pow_succ]
    cases f m <;> simp <;> omega

theorem bitsVal_testBit (f : Nat → Bool) : ∀ m i, i < m → (bitsVal f m).testBit i = f i
  | 0, _, hi => by omega
  | m + 1, i, hi => by
    simp only [bitsVal]
    have hlt := bitsVal_lt f m
    by_cases him : i = m
    · subst him
      cases hfm : f i
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        exact Nat.testBit_lt_two_pow hlt
      · simp only [↓reduceIte]
        rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]
        rfl
    · have him' : i < m := by omega
      cases hfm : f m
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        exact bitsVal_testBit f m i him'
      · simp only [↓reduceIte]
        rw [Nat.add_comm, Nat.testBit_two_pow_add_gt him']
        exact bitsVal_testBit f m i him'

theorem bitsVal_ext {f g : Nat → Bool} {m : Nat} (h : ∀ i < m, f i = g i) :
    bitsVal f m = bitsVal g m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [bitsVal, ih (fun i hi => h i (by omega)), h m (by omega)]

theorem bitsVal_inj {f g : Nat → Bool} {m : Nat} (heq : bitsVal f m = bitsVal g m) :
    ∀ i < m, f i = g i := by
  intro i hi
  rw [← bitsVal_testBit f m i hi, ← bitsVal_testBit g m i hi, heq]

theorem bitsVal_lt_step (f g : Nat → Bool) (m : Nat) :
    decide (bitsVal f (m + 1) < bitsVal g (m + 1)) =
      ((!(f m) && g m) || ((!(f m) || g m) && decide (bitsVal f m < bitsVal g m))) := by
  have hf := bitsVal_lt f m
  have hg := bitsVal_lt g m
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  simp only [bitsVal, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
  cases f m <;> cases g m <;> simp <;> omega

theorem ltWordG {A : Set (Sig n)} (f g : Nat → Sig n) (m : Nat)
    (hf : ∀ i < m, f i ∈ A) (hg : ∀ i < m, g i ∈ A) (hfalse : (fun _ => false) ∈ A) :
    Build A {fun v => decide (bitsVal (fun i => f i v) m < bitsVal (fun i => g i v) m)} (5 * m) := by
  induction m with
  | zero =>
    have he : (fun v : Fin n → Bool => decide (bitsVal (fun i => f i v) 0 < bitsVal (fun i => g i v) 0)) =
        (fun _ => false) := by
      funext v
      rfl
    rw [he]
    exact relax (idle (Set.singleton_subset_iff.mpr hfalse)) le_rfl le_rfl (by omega)
  | succ m ih =>
    have hprev := ih (fun i hi => hf i (by omega)) (fun i hi => hg i (by omega))
    let prev : Sig n := fun v => decide (bitsVal (fun i => f i v) m < bitsVal (fun i => g i v) m)
    have hstep : Build (A ∪ {prev})
        {fun v => (!(f m v) && g m v) || ((!(f m v) || g m v) && prev v)} 5 :=
      ltStepG (Or.inl (hf m (by omega))) (Or.inl (hg m (by omega))) (Or.inr rfl)
    have he : (fun v => (!(f m v) && g m v) || ((!(f m v) || g m v) && prev v)) =
        (fun v => decide (bitsVal (fun i => f i v) (m + 1) < bitsVal (fun i => g i v) (m + 1))) := by
      funext v
      exact (bitsVal_lt_step (fun i => f i v) (fun i => g i v) m).symm
    rw [he] at hstep
    refine relax (seq hprev hstep) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) ?_
    omega

theorem embedGates {m : Nat} {A : Set (Sig n)} (gs : List Gate)
    (hfan : FanInTwo ⟨gs, 0⟩) (hread : ReadsBack m ⟨gs, 0⟩)
    (inp : Fin m → Sig n) (hinp : ∀ i : Fin m, inp i ∈ A) :
    Build A
      {f | ∃ idx < m + gs.length,
        f = fun x => ((Circuit.mk gs 0).wires (List.ofFn (fun i => inp i x))).getD idx false}
      gs.length := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine relax (idle ?_) le_rfl le_rfl (by simp)
    rintro f ⟨idx, hidx, rfl⟩
    simp only [List.length_nil, Nat.add_zero] at hidx
    have he : (fun x => ((Circuit.mk [] 0).wires (List.ofFn (fun i => inp i x))).getD idx false) =
        inp ⟨idx, hidx⟩ := by
      funext x
      simp only [Circuit.wires, List.foldl_nil]
      rw [List.getD_eq_getElem _ _ (by simp [hidx]), List.getElem_ofFn]
    rw [he]
    exact hinp ⟨idx, hidx⟩
  | append_singleton gs g ih =>
    have hfan_pre : FanInTwo ⟨gs, 0⟩ := fun g' hg' => hfan g' (List.mem_append_left [g] hg')
    have hfan_g := hfan g (List.mem_append_right gs List.mem_cons_self)
    have hread_pre : ReadsBack m ⟨gs, 0⟩ := by
      intro j hj i hi
      change j < gs.length at hj
      change i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs at hi
      have hj' : j < (gs ++ [g]).length := by simp only [List.length_append, List.length_singleton]; omega
      have hget : ((gs ++ [g]).getD j ⟨GateOp.or, []⟩) = gs.getD j ⟨GateOp.or, []⟩ :=
        List.getD_append _ _ _ _ hj
      exact hread j hj' i (by change i ∈ ((gs ++ [g]).getD j ⟨GateOp.or, []⟩).inputs; rw [hget]; exact hi)
    have hread_g : ∀ i ∈ g.inputs, i < m + gs.length := by
      intro i hi
      have hj : gs.length < (gs ++ [g]).length := by simp
      have hget : ((gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩) = g := by
        rw [List.getD_append_right _ _ _ _ le_rfl]
        simp
      exact hread gs.length hj i (by change i ∈ ((gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩).inputs; rw [hget]; exact hi)
    have Hpre := ih hfan_pre hread_pre
    let Bpre : Set (Sig n) :=
      {f | ∃ idx < m + gs.length,
        f = fun x => ((Circuit.mk gs 0).wires (List.ofFn (fun i => inp i x))).getD idx false}
    let outSig : Sig n := fun x =>
      ((Circuit.mk (gs ++ [g]) 0).wires (List.ofFn (fun i => inp i x))).getD (m + gs.length) false
    let deps : List (Sig n) := g.inputs.map (fun i x =>
      ((Circuit.mk gs 0).wires (List.ofFn (fun k => inp k x))).getD i false)
    have hlen_w (x : Fin n → Bool) :
        ((Circuit.mk gs 0).wires (List.ofFn (fun k => inp k x))).length = m + gs.length := by
      rw [GateBridge.wireLength]
      simp
    have hsnoc (x : Fin n → Bool) :
        (Circuit.mk (gs ++ [g]) 0).wires (List.ofFn (fun k => inp k x)) =
          (Circuit.mk gs 0).wires (List.ofFn (fun k => inp k x)) ++
            [g.op.eval (g.inputs.map (fun i =>
              ((Circuit.mk gs 0).wires (List.ofFn (fun k => inp k x))).getD i false))] := by
      simp only [Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have Hstep : Build (A ∪ Bpre) {outSig} 1 := by
      apply one g.op deps hfan_g.1 (by simp [deps, hfan_g.2])
      · intro d hd
        rcases List.mem_map.mp hd with ⟨i, hi, rfl⟩
        exact Or.inr ⟨i, hread_g i hi, rfl⟩
      · intro x
        dsimp only [outSig, deps]
        rw [hsnoc x, List.getD_append_right _ _ _ _ (by rw [hlen_w x])]
        simp [hlen_w x, List.map_map, Function.comp_def]
    refine relax (seq Hpre Hstep) le_rfl ?_ (by simp)
    rintro f ⟨idx, hidx, rfl⟩
    simp only [List.length_append, List.length_singleton] at hidx
    by_cases hlt : idx < m + gs.length
    · left
      refine ⟨idx, hlt, ?_⟩
      funext x
      rw [hsnoc x, List.getD_append _ _ _ _ (by rw [hlen_w x]; exact hlt)]
    · have heq : idx = m + gs.length := by omega
      subst heq
      exact Or.inr rfl

theorem batchLookup {n w q : Nat} (hn : 0 < n) {A : Set (Sig (n * 2 ^ (w + 1)))}
    (row : Fin n)
    (addr : Fin q → Fin (w + 1) → Sig (n * 2 ^ (w + 1)))
    (haddr : ∀ j bit, addr j bit ∈ A)
    (hinp : ∀ a : Fin (n * 2 ^ (w + 1)), (fun x => x a) ∈ A) :
    Build A
      {f | ∃ j : Fin q, f = fun x =>
        x ⟨row.val * 2 ^ (w + 1) +
            bitsVal (fun b => if h : b < w + 1 then addr j ⟨b, h⟩ x else false) (w + 1),
          by
            have hlt := bitsVal_lt (fun b => if h : b < w + 1 then addr j ⟨b, h⟩ x else false) (w + 1)
            have hr : row.val + 1 ≤ n := row.isLt
            calc row.val * 2 ^ (w + 1) + bitsVal _ (w + 1)
                < row.val * 2 ^ (w + 1) + 2 ^ (w + 1) := Nat.add_lt_add_left hlt _
              _ = (row.val + 1) * 2 ^ (w + 1) := by rw [Nat.succ_mul]
              _ ≤ n * 2 ^ (w + 1) := Nat.mul_le_mul_right _ hr⟩}
      (128 * (2 ^ (w + 1) + q) * (w + 1 + 1 + Nat.log2 (q + 1) + 3) ^ 3) := by
  let words := 2 ^ (w + 1)
  let m := words * 1 + q * (w + 1)
  obtain ⟨C, outBit, hfan, hread, _, hsize, hspec⟩ := PEqualNP.Outside.L_clb_049 (w + 1) 1 q
  let inp : Fin m → Sig (n * 2 ^ (w + 1)) := fun idx x =>
    if h1 : idx.val < words then
      x ⟨row.val * words + idx.val, by
        have hr : row.val + 1 ≤ n := row.isLt
        calc row.val * words + idx.val < row.val * words + words := Nat.add_lt_add_left h1 _
          _ = (row.val + 1) * words := by rw [Nat.succ_mul]
          _ ≤ n * words := Nat.mul_le_mul_right _ hr⟩
    else
      let off := idx.val - words
      let j : Fin q := ⟨off / (w + 1), by
        have hlt : off < q * (w + 1) := by dsimp [off, m] at *; omega
        exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])⟩
      let bit : Fin (w + 1) := ⟨off % (w + 1), Nat.mod_lt _ (Nat.succ_pos w)⟩
      addr j bit x
  have hinp_mem : ∀ i : Fin m, inp i ∈ A := by
    intro i
    dsimp only [inp]
    split_ifs with h1
    · exact hinp _
    · exact haddr _ _
  have Hemb := embedGates (m := m) C.gates hfan hread inp hinp_mem
  refine relax Hemb le_rfl ?_ hsize
  rintro f ⟨j, rfl⟩
  refine ⟨(outBit j 0).val, (outBit j 0).isLt, ?_⟩
  funext x
  let tab : Fin words → Fin 1 → Bool := fun k _ =>
    x ⟨row.val * words + k.val, by
      have hr : row.val + 1 ≤ n := row.isLt
      calc row.val * words + k.val < row.val * words + words := Nat.add_lt_add_left k.isLt _
        _ = (row.val + 1) * words := by rw [Nat.succ_mul]
        _ ≤ n * words := Nat.mul_le_mul_right _ hr⟩
  let addrv : Fin q → Fin words := fun u =>
    ⟨bitsVal (fun b => if h : b < w + 1 then addr u ⟨b, h⟩ x else false) (w + 1),
      bitsVal_lt _ _⟩
  have hlist : List.ofFn (fun i : Fin m => inp i x) =
      (List.ofFn (fun k : Fin words => List.ofFn (tab k))).flatten ++
      (List.ofFn (fun u : Fin q =>
        List.ofFn (fun bit : Fin (w + 1) => (addrv u).val.testBit bit.val))).flatten := by
    have hfl_len : ∀ (L : List (List Bool)) (len : Nat),
        (∀ l ∈ L, l.length = len) → L.flatten.length = L.length * len := by
      intro L len
      induction L with
      | nil => intro _; simp
      | cons a as iha =>
        intro hlen
        simp only [List.flatten_cons, List.length_append, List.length_cons]
        rw [hlen a List.mem_cons_self, iha (fun l hl => hlen l (List.mem_cons_of_mem _ hl)),
            Nat.succ_mul, Nat.add_comm]
    have hlen_l : ((List.ofFn (fun k : Fin words => List.ofFn (tab k))).flatten).length = words := by
      rw [hfl_len _ 1 (by intro l hl; rcases List.mem_ofFn.mp hl with ⟨k, rfl⟩; simp)]
      simp
    have hlen_r : ((List.ofFn (fun u : Fin q =>
        List.ofFn (fun bit : Fin (w + 1) => (addrv u).val.testBit bit.val))).flatten).length = q * (w + 1) := by
      rw [hfl_len _ (w + 1) (by intro l hl; rcases List.mem_ofFn.mp hl with ⟨u, rfl⟩; simp)]
      simp
    apply List.ext_getElem
    · simp only [List.length_ofFn, List.length_append, hlen_l, hlen_r, m, Nat.mul_one]
    · intro idx h1 h2
      rw [List.getElem_ofFn]
      by_cases hw1 : idx < words
      · rw [List.getElem_append_left (by omega)]
        have hfl : (List.ofFn (fun k : Fin words => List.ofFn (tab k))).flatten =
            List.ofFn (fun k : Fin words => tab k 0) := by
          have h1s : (fun k : Fin words => List.ofFn (tab k)) = (fun k : Fin words => [tab k 0]) := by
            funext k
            apply List.ext_getElem
            · simp
            · intro i hi1 hi2
              have hi0 : i = 0 := by simp at hi2; omega
              subst hi0; simp
          rw [h1s]
          have hsing : ∀ (m : Nat) (f : Fin m → Bool),
              (List.ofFn (fun k : Fin m => [f k])).flatten = List.ofFn f := by
            intro m
            induction m with
            | zero => intro _; simp
            | succ m ihm =>
              intro f
              rw [List.ofFn_succ, List.ofFn_succ, List.flatten_cons, List.singleton_append, ihm]
          exact hsing words (fun k => tab k 0)
        simp only [hfl, List.getElem_ofFn, inp, hw1, ↓reduceDIte, tab]
      · rw [List.getElem_append_right (by omega)]
        simp only [hlen_l]
        have hoff : idx - words < q * (w + 1) := by
          simp only [List.length_ofFn] at h1
          dsimp only [m] at h1
          omega
        have hq_idx : (idx - words) / (w + 1) < q :=
          Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
        have hb_idx : (idx - words) % (w + 1) < w + 1 := Nat.mod_lt _ (Nat.succ_pos w)
        have hget_fl : ∀ (L : List (List Bool)) (k len : Nat)
            (hlen : ∀ l ∈ L, l.length = len) (hpos : 0 < len) (hk : k < L.length * len),
            L.flatten[k]'(by rw [hfl_len L len hlen]; exact hk) =
            (L[k / len]'(Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])))[k % len]'(by
              have hmem := hlen (L[k / len]'(Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm]))) (List.getElem_mem _)
              rw [hmem]; exact Nat.mod_lt _ hpos) := by
          intro L
          induction L with
          | nil => intro k len _ _ hk; simp at hk
          | cons a as iha =>
            intro k len hlen hpos hk
            have ha : a.length = len := hlen a List.mem_cons_self
            by_cases hkl : k < len
            · simp only [List.flatten_cons]
              rw [List.getElem_append_left (by omega)]
              have hd0 : k / len = 0 := Nat.div_eq_of_lt hkl
              have hm0 : k % len = k := Nat.mod_eq_of_lt hkl
              simp [hd0, hm0]
            · simp only [List.flatten_cons]
              rw [List.getElem_append_right (by omega)]
              have hk' : k - len < as.length * len := by
                simp only [List.length_cons, Nat.succ_mul] at hk; omega
              have hrec := iha (k - len) len (fun l hl => hlen l (List.mem_cons_of_mem _ hl)) hpos hk'
              have hd : k / len = (k - len) / len + 1 := by
                have := Nat.div_eq_sub_div hpos (by omega : len ≤ k)
                omega
              have hm : k % len = (k - len) % len := by
                have := Nat.mod_eq_sub_mod (by omega : len ≤ k)
                omega
              simp only [ha]
              rw [hrec]
              congr 1
              · simp [hd]
              · exact hm.symm
        have hfl_eq := hget_fl
          (List.ofFn (fun u : Fin q => List.ofFn (fun bit : Fin (w + 1) => (addrv u).val.testBit bit.val)))
          (idx - words) (w + 1)
          (by intro l hl; rcases List.mem_ofFn.mp hl with ⟨u, rfl⟩; simp)
          (Nat.succ_pos w)
          (by simp [hoff])
        rw [hfl_eq]
        simp only [List.getElem_ofFn, inp, hw1, ↓reduceDIte, addrv]
        rw [bitsVal_testBit _ (w + 1) _ hb_idx]
        simp [hb_idx]
  have hsp := hspec tab addrv j 0
  have hcw : (Circuit.mk C.gates 0).wires = C.wires := by rcases C with ⟨gs, o⟩; rfl
  rw [hcw, hlist, hsp]

end Build220

namespace Bitonic

open Build220

def bitonicMerge (off : Nat) : Nat → Bool → List (Nat × Nat × Bool)
  | 0, _ => []
  | k + 1, asc =>
    let h := 2 ^ k
    let stage := (List.range h).map (fun i => (off + i, off + h + i, asc))
    stage ++ bitonicMerge off k asc ++ bitonicMerge (off + h) k asc

def bitonicSort (off : Nat) : Nat → Bool → List (Nat × Nat × Bool)
  | 0, _ => []
  | k + 1, asc =>
    let h := 2 ^ k
    bitonicSort off k true ++ bitonicSort (off + h) k false ++ bitonicMerge off (k + 1) asc

theorem bitonicMerge_length (off : Nat) : ∀ k asc,
    2 * (bitonicMerge off k asc).length = k * 2 ^ k
  | 0, _ => by simp [bitonicMerge]
  | k + 1, asc => by
    simp only [bitonicMerge, List.length_append, List.length_map, List.length_range]
    have h1 := bitonicMerge_length off k asc
    have h2 := bitonicMerge_length (off + 2 ^ k) k asc
    have he : (k + 1) * 2 ^ (k + 1) = 2 * 2 ^ k + 2 * (k * 2 ^ k) := by
      rw [Nat.pow_succ, Nat.succ_mul]
      rw [← Nat.mul_assoc k (2 ^ k) 2, Nat.mul_comm (k * 2 ^ k) 2, Nat.mul_comm (2 ^ k) 2, Nat.add_comm]
    omega

theorem bitonicSort_length (off : Nat) : ∀ k asc,
    4 * (bitonicSort off k asc).length = k * (k + 1) * 2 ^ k
  | 0, _ => by simp [bitonicSort]
  | k + 1, asc => by
    simp only [bitonicSort, List.length_append]
    have h1 := bitonicSort_length off k true
    have h2 := bitonicSort_length (off + 2 ^ k) k false
    have hm := bitonicMerge_length off (k + 1) asc
    have he : (k + 1) * (k + 1 + 1) * 2 ^ (k + 1) =
        2 * (k * (k + 1) * 2 ^ k) + 2 * ((k + 1) * 2 ^ (k + 1)) := by
      rw [Nat.pow_succ]
      have e1 : k * (k + 1) * 2 ^ k = (k + 1) * k * 2 ^ k := by rw [Nat.mul_comm k (k + 1)]
      have e2 : (k + 1) * (k + 2) * (2 ^ k * 2) =
          (k + 1) * k * (2 ^ k * 2) + (k + 1) * 2 * (2 ^ k * 2) := by
        rw [Nat.mul_add (k + 1) k 2, Nat.add_mul]
      rw [e2]
      have e3 : 2 * (k * (k + 1) * 2 ^ k) = (k + 1) * k * (2 ^ k * 2) := by
        rw [e1, Nat.mul_comm 2, Nat.mul_assoc]
      have e4 : 2 * ((k + 1) * (2 ^ k * 2)) = (k + 1) * 2 * (2 ^ k * 2) := by
        rw [← Nat.mul_assoc 2 (k + 1), Nat.mul_comm 2 (k + 1)]
      omega
    omega

theorem bitonicMerge_mem (off : Nat) : ∀ k asc c,
    c ∈ bitonicMerge off k asc → off ≤ c.1 ∧ c.1 < c.2.1 ∧ c.2.1 < off + 2 ^ k
  | 0, _, c, hc => by simp [bitonicMerge] at hc
  | k + 1, asc, c, hc => by
    simp only [bitonicMerge, List.mem_append, List.mem_map, List.mem_range] at hc
    rcases hc with (⟨i, hi, rfl⟩ | hc) | hc
    · dsimp only; rw [Nat.pow_succ]; omega
    · have h := bitonicMerge_mem off k asc c hc; rw [Nat.pow_succ]; omega
    · have h := bitonicMerge_mem (off + 2 ^ k) k asc c hc; rw [Nat.pow_succ]; omega

theorem bitonicSort_mem (off : Nat) : ∀ k asc c,
    c ∈ bitonicSort off k asc → off ≤ c.1 ∧ c.1 < c.2.1 ∧ c.2.1 < off + 2 ^ k
  | 0, _, c, hc => by simp [bitonicSort] at hc
  | k + 1, asc, c, hc => by
    simp only [bitonicSort, List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · have h := bitonicSort_mem off k true c hc; rw [Nat.pow_succ]; omega
    · have h := bitonicSort_mem (off + 2 ^ k) k false c hc; rw [Nat.pow_succ]; omega
    · exact bitonicMerge_mem off (k + 1) asc c hc

def swapBit (k1 k2 : Nat) (asc : Bool) : Bool :=
  if asc then decide (k2 < k1) else decide (k1 < k2)

def applySwap {α : Type*} (u v : Nat) (sw : Bool) (st : Nat → α) : Nat → α :=
  fun idx =>
    if sw then
      if idx = u then st v else if idx = v then st u else st idx
    else st idx

theorem applySwap_invol {α : Type*} (u v : Nat) (sw : Bool) (st : Nat → α) :
    applySwap u v sw (applySwap u v sw st) = st := by
  funext idx
  simp only [applySwap]
  cases sw with
  | false => rfl
  | true =>
    simp only [↓reduceIte]
    by_cases h1 : idx = u
    · subst h1
      by_cases huv : idx = v
      · subst huv; simp
      · simp [Ne.symm huv]
    · by_cases h2 : idx = v
      · subst h2; simp [h1]
      · simp [h1, h2]

theorem applySwap_comp {α β : Type*} (u v : Nat) (sw : Bool) (f : α → β) (st : Nat → α) :
    applySwap u v sw (fun idx => f (st idx)) = fun idx => f (applySwap u v sw st idx) := by
  funext idx
  simp only [applySwap]
  cases sw <;> simp only [Bool.false_eq_true, ↓reduceIte]
  by_cases h1 : idx = u
  · simp [h1]
  · by_cases h2 : idx = v
    · subst h2; simp [h1]
    · simp [h1, h2]

def runNet {α : Type*} (key : α → Nat) : List (Nat × Nat × Bool) → (Nat → α) → (Nat → α)
  | [], st => st
  | (u, v, asc) :: rest, st =>
    let sw := swapBit (key (st u)) (key (st v)) asc
    runNet key rest (applySwap u v sw st)

theorem runNet_append {α : Type*} (key : α → Nat) (n1 n2 : List (Nat × Nat × Bool)) (st : Nat → α) :
    runNet key (n1 ++ n2) st = runNet key n2 (runNet key n1 st) := by
  induction n1 generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, asc⟩
    simp only [List.cons_append, runNet]
    exact ih _

def netSwaps {α : Type*} (key : α → Nat) : List (Nat × Nat × Bool) → (Nat → α) → List (Nat × Nat × Bool)
  | [], _ => []
  | (u, v, asc) :: rest, st =>
    let sw := swapBit (key (st u)) (key (st v)) asc
    (u, v, sw) :: netSwaps key rest (applySwap u v sw st)

theorem netSwaps_length {α : Type*} (key : α → Nat) (net : List (Nat × Nat × Bool)) (st : Nat → α) :
    (netSwaps key net st).length = net.length := by
  induction net generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, asc⟩
    simp only [netSwaps, List.length_cons, ih]

theorem netSwaps_getD_idx {α : Type*} (key : α → Nat) (net : List (Nat × Nat × Bool)) (st : Nat → α) :
    ∀ t < net.length,
      ((netSwaps key net st).getD t (0, 0, false)).1 = (net.getD t (0, 0, false)).1 ∧
      ((netSwaps key net st).getD t (0, 0, false)).2.1 = (net.getD t (0, 0, false)).2.1 := by
  induction net generalizing st with
  | nil => intro t ht; simp at ht
  | cons c rest ih =>
    rcases c with ⟨u, v, asc⟩
    intro t ht
    cases t with
    | zero => simp [netSwaps]
    | succ t =>
      simp only [List.length_cons] at ht
      simpa only [netSwaps, List.getD_cons_succ] using ih _ t (by omega)

def replaySwaps {β : Type*} : List (Nat × Nat × Bool) → (Nat → β) → (Nat → β)
  | [], st => st
  | (u, v, sw) :: rest, st => replaySwaps rest (applySwap u v sw st)

theorem replaySwaps_append {β : Type*} (s1 s2 : List (Nat × Nat × Bool)) (st : Nat → β) :
    replaySwaps (s1 ++ s2) st = replaySwaps s2 (replaySwaps s1 st) := by
  induction s1 generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, sw⟩
    simp only [List.cons_append, replaySwaps]
    exact ih _

theorem replaySwaps_comp {α β : Type*} (sws : List (Nat × Nat × Bool)) (f : α → β) (st : Nat → α) :
    replaySwaps sws (fun idx => f (st idx)) = fun idx => f (replaySwaps sws st idx) := by
  induction sws generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, sw⟩
    simp only [replaySwaps]
    rw [applySwap_comp]
    exact ih _

theorem replaySwaps_reverse_cancel {β : Type*} (sws : List (Nat × Nat × Bool)) (st : Nat → β) :
    replaySwaps sws.reverse (replaySwaps sws st) = st := by
  induction sws generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, sw⟩
    simp only [List.reverse_cons, replaySwaps, replaySwaps_append]
    rw [ih, applySwap_invol]

theorem replaySwaps_lt (N : Nat) (sws : List (Nat × Nat × Bool))
    (hsws : ∀ c ∈ sws, c.1 < N ∧ c.2.1 < N) (st : Nat → Nat)
    (hst : ∀ i < N, st i < N) :
    ∀ i < N, replaySwaps sws st i < N := by
  induction sws generalizing st with
  | nil => exact hst
  | cons c rest ih =>
    rcases c with ⟨u, v, sw⟩
    have hc := hsws (u, v, sw) List.mem_cons_self
    apply ih (fun c' hc' => hsws c' (List.mem_cons_of_mem _ hc'))
    intro i hi
    simp only [applySwap]
    cases sw
    · exact hst i hi
    · simp only [↓reduceIte]
      by_cases h1 : i = u
      · simp [h1, hst v hc.2]
      · by_cases h2 : i = v
        · subst h2; simp [h1, hst u hc.1]
        · simp [h1, h2, hst i hi]

theorem netSwaps_mem_bound {α : Type*} (N : Nat) (key : α → Nat) (net : List (Nat × Nat × Bool))
    (hnet : ∀ c ∈ net, c.1 < N ∧ c.2.1 < N) (st : Nat → α) :
    ∀ c ∈ netSwaps key net st, c.1 < N ∧ c.2.1 < N := by
  induction net generalizing st with
  | nil => intro c hc; simp [netSwaps] at hc
  | cons c rest ih =>
    rcases c with ⟨u, v, asc⟩
    have hc := hnet (u, v, asc) List.mem_cons_self
    intro c' hc'
    simp only [netSwaps, List.mem_cons] at hc'
    rcases hc' with rfl | hc'
    · exact hc
    · exact ih (fun x hx => hnet x (List.mem_cons_of_mem _ hx)) _ c' hc'

theorem runNet_eq_replay {α : Type*} (key : α → Nat) (net : List (Nat × Nat × Bool)) (st : Nat → α) :
    runNet key net st = replaySwaps (netSwaps key net st) st := by
  induction net generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, asc⟩
    simp only [runNet, netSwaps, replaySwaps]
    exact ih _

theorem runNet_unchanged {α : Type*} (key : α → Nat) (net : List (Nat × Nat × Bool))
    (st : Nat → α) (idx : Nat) (h : ∀ c ∈ net, idx ≠ c.1 ∧ idx ≠ c.2.1) :
    runNet key net st idx = st idx := by
  induction net generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, asc⟩
    have hc := h (u, v, asc) List.mem_cons_self
    simp only [runNet]
    rw [ih _ (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))]
    simp only [applySwap]
    cases swapBit (key (st u)) (key (st v)) asc
    · rfl
    · simp only [↓reduceIte, hc.1, hc.2]

theorem runNet_mono_map {α : Type*} (key : α → Nat) (f : Nat → Bool)
    (hf : ∀ x y, x ≤ y → f x = true → f y = true)
    (net : List (Nat × Nat × Bool)) (st : Nat → α) :
    (fun idx => f (key (runNet key net st idx))) =
      runNet (fun b : Bool => b.toNat) net (fun idx => f (key (st idx))) := by
  induction net generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, asc⟩
    simp only [runNet]
    rw [ih]
    congr 1
    funext idx
    simp only [applySwap, swapBit]
    have hpair :
        (f (key (if (if asc then decide (key (st v) < key (st u)) else decide (key (st u) < key (st v)))
          then st v else st u)) =
         if (if asc then decide ((f (key (st v))).toNat < (f (key (st u))).toNat)
             else decide ((f (key (st u))).toNat < (f (key (st v))).toNat))
          then f (key (st v)) else f (key (st u))) ∧
        (f (key (if (if asc then decide (key (st v) < key (st u)) else decide (key (st u) < key (st v)))
          then st u else st v)) =
         if (if asc then decide ((f (key (st v))).toNat < (f (key (st u))).toNat)
             else decide ((f (key (st u))).toNat < (f (key (st v))).toNat))
          then f (key (st u)) else f (key (st v))) := by
      cases asc <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · by_cases hlt : key (st u) < key (st v)
        · have hle : key (st u) ≤ key (st v) := Nat.le_of_lt hlt
          simp only [hlt, decide_true, ↓reduceIte]
          cases hfu : f (key (st u)) <;> cases hfv : f (key (st v))
          · simp
          · simp
          · exact absurd (hf _ _ hle hfu) (by rw [hfv]; decide)
          · simp
        · have hle : key (st v) ≤ key (st u) := Nat.le_of_not_lt hlt
          simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
          cases hfu : f (key (st u)) <;> cases hfv : f (key (st v))
          · simp
          · exact absurd (hf _ _ hle hfv) (by rw [hfu]; decide)
          · simp
          · simp
      · by_cases hlt : key (st v) < key (st u)
        · have hle : key (st v) ≤ key (st u) := Nat.le_of_lt hlt
          simp only [hlt, decide_true, ↓reduceIte]
          cases hfu : f (key (st u)) <;> cases hfv : f (key (st v))
          · simp
          · exact absurd (hf _ _ hle hfv) (by rw [hfu]; decide)
          · simp
          · simp
        · have hle : key (st u) ≤ key (st v) := Nat.le_of_not_lt hlt
          simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
          cases hfu : f (key (st u)) <;> cases hfv : f (key (st v))
          · simp
          · simp
          · exact absurd (hf _ _ hle hfu) (by rw [hfv]; decide)
          · simp
    by_cases h1 : idx = u
    · subst h1
      have hl := hpair.1
      by_cases hs1 : (if asc then decide (key (st v) < key (st idx)) else decide (key (st idx) < key (st v))) = true <;>
        by_cases hs2 : (if asc then decide ((f (key (st v))).toNat < (f (key (st idx))).toNat)
          else decide ((f (key (st idx))).toNat < (f (key (st v))).toNat)) = true <;>
        simp only [hs1, hs2, ↓reduceIte] at hl ⊢ <;> exact hl
    · by_cases h2 : idx = v
      · subst h2
        have hr := hpair.2
        by_cases hs1 : (if asc then decide (key (st idx) < key (st u)) else decide (key (st u) < key (st idx))) = true <;>
          by_cases hs2 : (if asc then decide ((f (key (st idx))).toNat < (f (key (st u))).toNat)
            else decide ((f (key (st u))).toNat < (f (key (st idx))).toNat)) = true <;>
          simp only [hs1, hs2, h1, ↓reduceIte] at hr ⊢ <;> exact hr
      · by_cases hs1 : (if asc then decide (key (st v) < key (st u)) else decide (key (st u) < key (st v))) = true <;>
          by_cases hs2 : (if asc then decide ((f (key (st v))).toNat < (f (key (st u))).toNat)
            else decide ((f (key (st u))).toNat < (f (key (st v))).toNat)) = true <;>
          simp only [hs1, hs2, h1, h2, Bool.false_eq_true, ↓reduceIte]

def IsBitonic (off len : Nat) (g : Nat → Bool) : Prop :=
  ∃ s e, s ≤ e ∧ e ≤ len ∧
    ((∀ i < len, g (off + i) = true ↔ s ≤ i ∧ i < e) ∨
     (∀ i < len, g (off + i) = false ↔ s ≤ i ∧ i < e))

def IsSortedBool (off len : Nat) (asc : Bool) (g : Nat → Bool) : Prop :=
  ∀ i j, i ≤ j → j < len →
    if asc then (g (off + i) = true → g (off + j) = true)
    else (g (off + j) = true → g (off + i) = true)

theorem runNet_bool_const (net : List (Nat × Nat × Bool)) (off len : Nat) (v : Bool)
    (g : Nat → Bool)
    (hnet : ∀ c ∈ net, off ≤ c.1 ∧ c.1 < off + len ∧ off ≤ c.2.1 ∧ c.2.1 < off + len)
    (hg : ∀ i < len, g (off + i) = v) :
    ∀ i < len, runNet (fun b : Bool => b.toNat) net g (off + i) = v := by
  induction net generalizing g with
  | nil => exact hg
  | cons c rest ih =>
    rcases c with ⟨x, y, asc⟩
    have hc := hnet (x, y, asc) List.mem_cons_self
    dsimp only at hc
    simp only [runNet]
    apply ih _ (fun c' hc' => hnet c' (List.mem_cons_of_mem _ hc'))
    intro i hi
    simp only [applySwap]
    have hx : g x = v := by
      have e : off + (x - off) = x := by omega
      rw [← e]; exact hg (x - off) (by omega)
    have hy : g y = v := by
      have e : off + (y - off) = y := by omega
      rw [← e]; exact hg (y - off) (by omega)
    cases swapBit (g x).toNat (g y).toNat asc
    · exact hg i hi
    · simp only [↓reduceIte]
      by_cases h1 : off + i = x
      · simp [h1, hy]
      · by_cases h2 : off + i = y
        · simp only [h1, ↓reduceIte]; simp only [h2, ↓reduceIte]; exact hx
        · simp [h1, h2, hg i hi]

theorem stage_eval (off h : Nat) (asc : Bool) (g : Nat → Bool) :
    ∀ m ≤ h, ∀ idx,
      let stage := (List.range m).map (fun i => (off + i, off + h + i, asc))
      runNet (fun b : Bool => b.toNat) stage g idx =
        if off ≤ idx ∧ idx < off + m then
          if asc then g idx && g (idx + h) else g idx || g (idx + h)
        else if off + h ≤ idx ∧ idx < off + h + m then
          if asc then g (idx - h) || g idx else g (idx - h) && g idx
        else g idx := by
  intro m
  induction m with
  | zero =>
    intro _ idx
    dsimp only
    simp only [List.range_zero, List.map_nil, runNet, Nat.add_zero]
    simp only [show ¬ (off ≤ idx ∧ idx < off) by omega,
      show ¬ (off + h ≤ idx ∧ idx < off + h) by omega, ↓reduceIte]
  | succ m ih =>
    intro hm idx
    dsimp only
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil, runNet_append]
    simp only [runNet, applySwap, swapBit]
    have h1 := ih (by omega) (off + m)
    have h2 := ih (by omega) (off + h + m)
    have h3 := ih (by omega) idx
    have h1' : runNet (fun b : Bool => b.toNat) ((List.range m).map (fun i => (off + i, off + h + i, asc))) g (off + m) = g (off + m) := by
      rw [h1]; simp only [show ¬ (off ≤ off + m ∧ off + m < off + m) by omega,
        show ¬ (off + h ≤ off + m ∧ off + m < off + h + m) by omega, ↓reduceIte]
    have h2' : runNet (fun b : Bool => b.toNat) ((List.range m).map (fun i => (off + i, off + h + i, asc))) g (off + h + m) = g (off + h + m) := by
      rw [h2]; simp only [show ¬ (off ≤ off + h + m ∧ off + h + m < off + m) by omega,
        show ¬ (off + h ≤ off + h + m ∧ off + h + m < off + h + m) by omega, ↓reduceIte]
    rw [h1', h2']
    by_cases hidx1 : idx = off + m
    · subst hidx1
      rw [h1']
      have e1 : off + m + h = off + h + m := by omega
      have hc1 : off ≤ off + m ∧ off + m < off + (m + 1) := by omega
      simp only [hc1, ↓reduceIte, e1]
      cases asc <;> cases g (off + m) <;> cases g (off + h + m) <;> rfl
    · by_cases hidx2 : idx = off + h + m
      · subst hidx2
        rw [h2']
        have e1 : off + h + m - h = off + m := by omega
        have hc1 : ¬ (off ≤ off + h + m ∧ off + h + m < off + (m + 1)) := by omega
        have hc2 : off + h ≤ off + h + m ∧ off + h + m < off + h + (m + 1) := by omega
        have hne : off + h + m ≠ off + m := by omega
        simp only [hc1, hc2, hne, ↓reduceIte, e1]
        cases asc <;> cases g (off + m) <;> cases g (off + h + m) <;> rfl
      · have hne1 : ¬ (idx = off + m) := hidx1
        have hne2 : ¬ (idx = off + h + m) := hidx2
        have heq : (if (if asc then decide ((g (off + h + m)).toNat < (g (off + m)).toNat)
            else decide ((g (off + m)).toNat < (g (off + h + m)).toNat)) then
            if idx = off + m then g (off + h + m) else if idx = off + h + m then g (off + m)
            else runNet (fun b : Bool => b.toNat) ((List.range m).map (fun i => (off + i, off + h + i, asc))) g idx
          else runNet (fun b : Bool => b.toNat) ((List.range m).map (fun i => (off + i, off + h + i, asc))) g idx) =
          runNet (fun b : Bool => b.toNat) ((List.range m).map (fun i => (off + i, off + h + i, asc))) g idx := by
          cases (if asc then decide ((g (off + h + m)).toNat < (g (off + m)).toNat)
            else decide ((g (off + m)).toNat < (g (off + h + m)).toNat)) <;> simp [hne1, hne2]
        rw [heq, h3]
        by_cases c1 : off ≤ idx ∧ idx < off + m
        · have c1' : off ≤ idx ∧ idx < off + (m + 1) := by omega
          simp only [c1, c1', and_self, ↓reduceIte]
        · by_cases c2 : off + h ≤ idx ∧ idx < off + h + m
          · have c1' : ¬ (off ≤ idx ∧ idx < off + (m + 1)) := by omega
            have c2' : off + h ≤ idx ∧ idx < off + h + (m + 1) := by omega
            simp only [c1, c2, c1', c2', ↓reduceIte]
          · have c1' : ¬ (off ≤ idx ∧ idx < off + (m + 1)) := by omega
            have c2' : ¬ (off + h ≤ idx ∧ idx < off + h + (m + 1)) := by omega
            simp only [c1, c2, c1', c2', ↓reduceIte]

theorem bitonic_split_true (off h : Nat) (g : Nat → Bool) (hb : IsBitonic off (2 * h) g) :
    let lo : Nat → Bool := fun idx => g idx && g (idx + h)
    let hi : Nat → Bool := fun idx => g (idx - h) || g idx
    IsBitonic off h lo ∧ IsBitonic (off + h) h hi ∧
      ((∀ i < h, lo (off + i) = false) ∨ (∀ i < h, hi (off + h + i) = true)) := by
  intro lo hi
  rcases hb with ⟨s, e, hse, he2h, htr | hfa⟩
  · by_cases hlen : e - s ≤ h
    · have hlo_all : ∀ i < h, lo (off + i) = false := by
        intro i hi_lt
        dsimp only [lo]
        cases h1 : g (off + i) with
        | false => rfl
        | true =>
          have hi1 := (htr i (by omega)).mp h1
          cases h2 : g (off + i + h) with
          | false => rfl
          | true =>
            have e1 : off + i + h = off + (h + i) := by omega
            rw [e1] at h2
            have hi2 := (htr (h + i) (by omega)).mp h2
            omega
      refine ⟨⟨0, 0, Nat.le_refl 0, Nat.zero_le h, Or.inl (fun i hi_lt => by rw [hlo_all i hi_lt]; simp)⟩,
        ?_, Or.inl hlo_all⟩
      have hhi_iff : ∀ i < h, hi (off + h + i) = true ↔ (s ≤ i ∧ i < e) ∨ (s ≤ h + i ∧ h + i < e) := by
        intro i hi_lt
        dsimp only [hi]
        have e1 : off + h + i - h = off + i := by omega
        have e2 : off + h + i = off + (h + i) := by omega
        rw [e1, e2, Bool.or_eq_true, htr i (by omega), htr (h + i) (by omega)]
      by_cases heh : e ≤ h
      · exact ⟨s, e, hse, heh, Or.inl (fun i hi_lt => by rw [hhi_iff i hi_lt]; omega)⟩
      · by_cases hhs : h ≤ s
        · exact ⟨s - h, e - h, by omega, by omega, Or.inl (fun i hi_lt => by rw [hhi_iff i hi_lt]; omega)⟩
        · refine ⟨e - h, s, by omega, by omega, Or.inr (fun i hi_lt => ?_)⟩
          have h1 := hhi_iff i hi_lt
          cases hval : hi (off + h + i) with
          | false =>
            have hnt : ¬ ((s ≤ i ∧ i < e) ∨ (s ≤ h + i ∧ h + i < e)) := fun hp => by
              have := h1.mpr hp; rw [hval] at this; cases this
            constructor
            · intro _; omega
            · intro _; rfl
          | true =>
            have ht := h1.mp hval
            constructor
            · intro hc; cases hc
            · intro hr; omega
    · have hhi_all : ∀ i < h, hi (off + h + i) = true := by
        intro i hi_lt
        dsimp only [hi]
        have e1 : off + h + i - h = off + i := by omega
        have e2 : off + h + i = off + (h + i) := by omega
        rw [e1, e2, Bool.or_eq_true, htr i (by omega), htr (h + i) (by omega)]
        omega
      refine ⟨⟨s, e - h, by omega, by omega, Or.inl (fun i hi_lt => ?_)⟩,
        ⟨0, h, Nat.zero_le h, Nat.le_refl h, Or.inl (fun i hi_lt => by rw [hhi_all i hi_lt]; simp [hi_lt])⟩,
        Or.inr hhi_all⟩
      dsimp only [lo]
      have e1 : off + i + h = off + (h + i) := by omega
      rw [e1, Bool.and_eq_true, htr i (by omega), htr (h + i) (by omega)]
      omega
  · by_cases hlen : e - s ≤ h
    · have hhi_all : ∀ i < h, hi (off + h + i) = true := by
        intro i hi_lt
        dsimp only [hi]
        have e1 : off + h + i - h = off + i := by omega
        have e2 : off + h + i = off + (h + i) := by omega
        rw [e1, e2]
        cases h1 : g (off + i) with
        | true => rfl
        | false =>
          have hi1 := (hfa i (by omega)).mp h1
          cases h2 : g (off + (h + i)) with
          | true => rfl
          | false =>
            have hi2 := (hfa (h + i) (by omega)).mp h2
            omega
      refine ⟨?_, ⟨0, h, Nat.zero_le h, Nat.le_refl h, Or.inl (fun i hi_lt => by rw [hhi_all i hi_lt]; simp [hi_lt])⟩,
        Or.inr hhi_all⟩
      have hlo_iff : ∀ i < h, lo (off + i) = false ↔ (s ≤ i ∧ i < e) ∨ (s ≤ h + i ∧ h + i < e) := by
        intro i hi_lt
        dsimp only [lo]
        have e1 : off + i + h = off + (h + i) := by omega
        rw [e1, Bool.and_eq_false_iff, hfa i (by omega), hfa (h + i) (by omega)]
      by_cases heh : e ≤ h
      · exact ⟨s, e, hse, heh, Or.inr (fun i hi_lt => by rw [hlo_iff i hi_lt]; omega)⟩
      · by_cases hhs : h ≤ s
        · exact ⟨s - h, e - h, by omega, by omega, Or.inr (fun i hi_lt => by rw [hlo_iff i hi_lt]; omega)⟩
        · refine ⟨e - h, s, by omega, by omega, Or.inl (fun i hi_lt => ?_)⟩
          have h1 := hlo_iff i hi_lt
          cases hval : lo (off + i) with
          | true =>
            have hnf : ¬ ((s ≤ i ∧ i < e) ∨ (s ≤ h + i ∧ h + i < e)) := fun hp => by
              have := h1.mpr hp; rw [hval] at this; cases this
            constructor
            · intro _; omega
            · intro _; rfl
          | false =>
            have hf := h1.mp hval
            constructor
            · intro hc; cases hc
            · intro hr; omega
    · have hlo_all : ∀ i < h, lo (off + i) = false := by
        intro i hi_lt
        dsimp only [lo]
        have e1 : off + i + h = off + (h + i) := by omega
        rw [e1, Bool.and_eq_false_iff, hfa i (by omega), hfa (h + i) (by omega)]
        omega
      refine ⟨⟨0, 0, Nat.le_refl 0, Nat.zero_le h, Or.inl (fun i hi_lt => by rw [hlo_all i hi_lt]; simp)⟩,
        ⟨s, e - h, by omega, by omega, Or.inr (fun i hi_lt => ?_)⟩,
        Or.inl hlo_all⟩
      dsimp only [hi]
      have e1 : off + h + i - h = off + i := by omega
      have e2 : off + h + i = off + (h + i) := by omega
      rw [e1, e2, Bool.or_eq_false_iff, hfa i (by omega), hfa (h + i) (by omega)]
      omega

theorem bitonicMerge_sorted (off : Nat) : ∀ k asc (g : Nat → Bool),
    IsBitonic off (2 ^ k) g →
    IsSortedBool off (2 ^ k) asc (runNet (fun b : Bool => b.toNat) (bitonicMerge off k asc) g)
  | 0, asc, g, _ => by
    intro i j hij hj
    have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    subst hi0; subst hj0
    cases asc <;> exact fun h => h
  | k + 1, asc, g, hb => by
    let h := 2 ^ k
    have h2 : 2 ^ (k + 1) = 2 * h := by dsimp [h]; rw [Nat.pow_succ, Nat.mul_comm]
    rw [h2] at hb ⊢
    simp only [bitonicMerge, runNet_append]
    let stage := (List.range h).map (fun i => (off + i, off + h + i, asc))
    let g1 := runNet (fun b : Bool => b.toNat) stage g
    let g2 := runNet (fun b : Bool => b.toNat) (bitonicMerge off k asc) g1
    let g3 := runNet (fun b : Bool => b.toNat) (bitonicMerge (off + h) k asc) g2
    change IsSortedBool off (2 * h) asc g3
    have hstage := stage_eval off h asc g h (Nat.le_refl h)
    have hg1_L : ∀ i < h, g1 (off + i) = if asc then g (off + i) && g (off + i + h) else g (off + i) || g (off + i + h) := by
      intro i hi_lt
      have hs := hstage (off + i)
      dsimp only at hs
      have hc1 : off ≤ off + i ∧ off + i < off + h := by omega
      simp only [hc1, and_self, ↓reduceIte] at hs
      exact hs
    have hg1_R : ∀ i < h, g1 (off + h + i) = if asc then g (off + h + i - h) || g (off + h + i) else g (off + h + i - h) && g (off + h + i) := by
      intro i hi_lt
      have hs := hstage (off + h + i)
      dsimp only at hs
      have hc1 : ¬ (off ≤ off + h + i ∧ off + h + i < off + h) := by omega
      have hc2 : off + h ≤ off + h + i ∧ off + h + i < off + h + h := by omega
      simp only [hc1, hc2, and_self, ↓reduceIte] at hs
      exact hs
    have hsp := bitonic_split_true off h g hb
    have hleft_bit : IsBitonic off h g1 := by
      cases asc with
      | true =>
        rcases hsp.1 with ⟨s, e, h1, h2', h3⟩
        refine ⟨s, e, h1, h2', ?_⟩
        rcases h3 with h3 | h3
        · left; intro i hi_lt; rw [hg1_L i hi_lt]; exact h3 i hi_lt
        · right; intro i hi_lt; rw [hg1_L i hi_lt]; exact h3 i hi_lt
      | false =>
        rcases hsp.2.1 with ⟨s, e, h1, h2', h3⟩
        refine ⟨s, e, h1, h2', ?_⟩
        rcases h3 with h3 | h3
        · left
          intro i hi_lt
          have e1 : off + h + i - h = off + i := by omega
          have e2 : off + h + i = off + i + h := by omega
          have h3' := h3 i hi_lt; dsimp only at h3'; rw [e1, e2] at h3'; rw [hg1_L i hi_lt]; exact h3'
        · right
          intro i hi_lt
          have e1 : off + h + i - h = off + i := by omega
          have e2 : off + h + i = off + i + h := by omega
          have h3' := h3 i hi_lt; dsimp only at h3'; rw [e1, e2] at h3'; rw [hg1_L i hi_lt]; exact h3'
    have hright_bit : IsBitonic (off + h) h g2 := by
      have hg2_eq : ∀ i < h, g2 (off + h + i) = g1 (off + h + i) := by
        intro i hi_lt
        apply runNet_unchanged
        intro c hc
        have hm := bitonicMerge_mem off k asc c hc
        dsimp only [h] at hi_lt ⊢; omega
      cases asc with
      | true =>
        rcases hsp.2.1 with ⟨s, e, h1, h2', h3⟩
        refine ⟨s, e, h1, h2', ?_⟩
        rcases h3 with h3 | h3
        · left; intro i hi_lt; rw [hg2_eq i hi_lt, hg1_R i hi_lt]; exact h3 i hi_lt
        · right; intro i hi_lt; rw [hg2_eq i hi_lt, hg1_R i hi_lt]; exact h3 i hi_lt
      | false =>
        rcases hsp.1 with ⟨s, e, h1, h2', h3⟩
        refine ⟨s, e, h1, h2', ?_⟩
        rcases h3 with h3 | h3
        · left
          intro i hi_lt
          have e1 : off + h + i - h = off + i := by omega
          have e2 : off + h + i = off + i + h := by omega
          rw [hg2_eq i hi_lt, hg1_R i hi_lt]; simp only [Bool.false_eq_true, ↓reduceIte]; rw [e1, e2]; exact h3 i hi_lt
        · right
          intro i hi_lt
          have e1 : off + h + i - h = off + i := by omega
          have e2 : off + h + i = off + i + h := by omega
          rw [hg2_eq i hi_lt, hg1_R i hi_lt]; simp only [Bool.false_eq_true, ↓reduceIte]; rw [e1, e2]; exact h3 i hi_lt
    have hsL : IsSortedBool off h asc g2 := bitonicMerge_sorted off k asc g1 hleft_bit
    have hsR : IsSortedBool (off + h) h asc g3 := bitonicMerge_sorted (off + h) k asc g2 hright_bit
    have hg3_left : ∀ i < h, g3 (off + i) = g2 (off + i) := by
      intro i hi_lt
      apply runNet_unchanged
      intro c hc
      have hm := bitonicMerge_mem (off + h) k asc c hc
      dsimp only [h] at hi_lt ⊢; omega
    have hnetL : ∀ c ∈ bitonicMerge off k asc, off ≤ c.1 ∧ c.1 < off + h ∧ off ≤ c.2.1 ∧ c.2.1 < off + h := by
      intro c hc; have hm := bitonicMerge_mem off k asc c hc; dsimp [h]; omega
    have hnetR : ∀ c ∈ bitonicMerge (off + h) k asc,
        off + h ≤ c.1 ∧ c.1 < off + h + h ∧ off + h ≤ c.2.1 ∧ c.2.1 < off + h + h := by
      intro c hc; have hm := bitonicMerge_mem (off + h) k asc c hc; dsimp [h]; omega
    intro i j hij hj
    by_cases hjh : j < h
    · rw [hg3_left i (by omega), hg3_left j hjh]; exact hsL i j hij hjh
    · by_cases hih : h ≤ i
      · have ei : off + i = off + h + (i - h) := by omega
        have ej : off + j = off + h + (j - h) := by omega
        rw [ei, ej]; exact hsR (i - h) (j - h) (by omega) (by omega)
      · have hi_lt : i < h := by omega
        have hj_lt : j - h < h := by omega
        have ej : off + j = off + h + (j - h) := by omega
        rw [hg3_left i hi_lt, ej]
        cases asc with
        | true =>
          simp only [↓reduceIte]
          rcases hsp.2.2 with hlo | hhi
          · have hg1L : ∀ x < h, g1 (off + x) = false := by intro x hx; rw [hg1_L x hx]; exact hlo x hx
            have hg2i : g2 (off + i) = false := runNet_bool_const (bitonicMerge off k true) off h false g1 hnetL hg1L i hi_lt
            intro ht; rw [hg2i] at ht; cases ht
          · have hg2R : ∀ x < h, g2 (off + h + x) = true := by
              intro x hx
              have heq : g2 (off + h + x) = g1 (off + h + x) := by
                apply runNet_unchanged; intro c hc; have hm := bitonicMerge_mem off k true c hc; dsimp [h] at hx ⊢; omega
              rw [heq, hg1_R x hx]; exact hhi x hx
            intro _; exact runNet_bool_const (bitonicMerge (off + h) k true) (off + h) h true g2 hnetR hg2R (j - h) hj_lt
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          rcases hsp.2.2 with hlo | hhi
          · have hg2R : ∀ x < h, g2 (off + h + x) = false := by
              intro x hx
              have heq : g2 (off + h + x) = g1 (off + h + x) := by
                apply runNet_unchanged; intro c hc; have hm := bitonicMerge_mem off k false c hc; dsimp [h] at hx ⊢; omega
              rw [heq, hg1_R x hx]; simp only [Bool.false_eq_true, ↓reduceIte]
              have e1 : off + h + x - h = off + x := by omega
              have e2 : off + h + x = off + x + h := by omega
              rw [e1, e2]; exact hlo x hx
            have hg3j : g3 (off + h + (j - h)) = false :=
              runNet_bool_const (bitonicMerge (off + h) k false) (off + h) h false g2 hnetR hg2R (j - h) hj_lt
            intro ht; rw [hg3j] at ht; cases ht
          · have hg1L : ∀ x < h, g1 (off + x) = true := by
              intro x hx
              rw [hg1_L x hx]; simp only [Bool.false_eq_true, ↓reduceIte]
              have e1 : off + h + x - h = off + x := by omega
              have e2 : off + h + x = off + x + h := by omega
              have hhi' := hhi x hx; dsimp only at hhi'; rw [e1, e2] at hhi'; exact hhi'
            intro _; exact runNet_bool_const (bitonicMerge off k false) off h true g1 hnetL hg1L i hi_lt

theorem sorted_asc_desc_bitonic (off h : Nat) (g : Nat → Bool)
    (hL : IsSortedBool off h true g) (hR : IsSortedBool (off + h) h false g) :
    IsBitonic off (2 * h) g := by
  have hexL : ∃ s ≤ h, ∀ i < h, g (off + i) = true ↔ s ≤ i := by
    have hgenL : ∀ n, IsSortedBool off n true g → ∃ s ≤ n, ∀ i < n, g (off + i) = true ↔ s ≤ i := by
      intro n
      induction n with
      | zero => intro _; exact ⟨0, Nat.le_refl 0, fun i hi => by omega⟩
      | succ m ih =>
        intro hLm
        rcases ih (fun i j hij hj => hLm i j hij (by omega)) with ⟨s, hsm, hs⟩
        cases hgm : g (off + m) with
        | false =>
          refine ⟨m + 1, Nat.le_refl _, fun i hi => ?_⟩
          constructor
          · intro ht
            by_cases him : i = m
            · subst him; rw [hgm] at ht; cases ht
            · have hgt := hLm i m (by omega) (by omega); simp only [↓reduceIte] at hgt
              have := hgt ht; rw [hgm] at this; cases this
          · intro hc; omega
        | true =>
          refine ⟨s, by omega, fun i hi => ?_⟩
          by_cases him : i = m
          · subst i; rw [hgm]; simp [show s ≤ m from hsm]
          · exact hs i (by omega)
    exact hgenL h hL
  have hexR : ∃ e ≤ h, ∀ i < h, g (off + h + i) = true ↔ i < e := by
    have hgen : ∀ n (g' : Nat → Bool), IsSortedBool 0 n false g' →
        ∃ e ≤ n, ∀ i < n, g' i = true ↔ i < e := by
      intro n g'
      induction n with
      | zero => intro _; exact ⟨0, Nat.le_refl 0, fun i hi => by omega⟩
      | succ m ih =>
        intro hg'
        rcases ih (fun i j hij hj => hg' i j hij (by omega)) with ⟨e, hem, he⟩
        cases hgm : g' m with
        | false =>
          refine ⟨e, by omega, fun i hi => ?_⟩
          by_cases him : i = m
          · subst i; rw [hgm]; simp [show ¬ m < e by omega]
          · exact he i (by omega)
        | true =>
          refine ⟨m + 1, Nat.le_refl _, fun i hi => ?_⟩
          constructor
          · intro _; omega
          · intro _
            have := hg' i m (by omega) (by omega)
            simp only [Nat.zero_add, Bool.false_eq_true, ↓reduceIte] at this
            exact this hgm
    have hR' : IsSortedBool 0 h false (fun i => g (off + h + i)) := by
      intro i j hij hj; simpa only [Nat.zero_add] using hR i j hij hj
    exact hgen h (fun i => g (off + h + i)) hR'
  rcases hexL with ⟨s, hsh, hs⟩
  rcases hexR with ⟨e, heh, he⟩
  refine ⟨s, h + e, by omega, by omega, Or.inl (fun i hi => ?_)⟩
  by_cases hih : i < h
  · rw [hs i hih]; omega
  · have e1 : off + i = off + h + (i - h) := by omega
    rw [e1, he (i - h) (by omega)]; omega

theorem bitonicSort_sorted_bool (off : Nat) : ∀ k asc (g : Nat → Bool),
    IsSortedBool off (2 ^ k) asc (runNet (fun b : Bool => b.toNat) (bitonicSort off k asc) g)
  | 0, asc, g => by
    intro i j hij hj
    have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    subst hi0; subst hj0
    cases asc <;> exact fun h => h
  | k + 1, asc, g => by
    let h := 2 ^ k
    simp only [bitonicSort, runNet_append]
    let g1 := runNet (fun b : Bool => b.toNat) (bitonicSort off k true) g
    let g2 := runNet (fun b : Bool => b.toNat) (bitonicSort (off + h) k false) g1
    have hsL : IsSortedBool off h true g1 := bitonicSort_sorted_bool off k true g
    have hsR : IsSortedBool (off + h) h false g2 := bitonicSort_sorted_bool (off + h) k false g1
    have hg2L : IsSortedBool off h true g2 := by
      intro i j hij hj
      have e1 : g2 (off + i) = g1 (off + i) := by
        apply runNet_unchanged; intro c hc; have hm := bitonicSort_mem (off + h) k false c hc; dsimp [h] at hij hj ⊢; omega
      have e2 : g2 (off + j) = g1 (off + j) := by
        apply runNet_unchanged; intro c hc; have hm := bitonicSort_mem (off + h) k false c hc; dsimp [h] at hj ⊢; omega
      rw [e1, e2]; exact hsL i j hij hj
    have hbit : IsBitonic off (2 ^ (k + 1)) g2 := by
      rw [Nat.pow_succ, Nat.mul_comm]
      exact sorted_asc_desc_bitonic off h g2 hg2L hsR
    exact bitonicMerge_sorted off (k + 1) asc g2 hbit

theorem bitonicSort_sorted {α : Type*} (key : α → Nat) (p : Nat) (st : Nat → α) :
    ∀ i j, i ≤ j → j < 2 ^ p →
      key (runNet key (bitonicSort 0 p true) st i) ≤ key (runNet key (bitonicSort 0 p true) st j) := by
  intro i j hij hj
  let T := key (runNet key (bitonicSort 0 p true) st i)
  let f : Nat → Bool := fun x => decide (T ≤ x)
  have hf : ∀ x y, x ≤ y → f x = true → f y = true := by
    intro x y hxy hx; simp only [f, decide_eq_true_eq] at hx ⊢; omega
  have hs := bitonicSort_sorted_bool 0 p true (fun idx => f (key (st idx))) i j hij hj
  simp only [Nat.zero_add, ↓reduceIte] at hs
  rw [← runNet_mono_map key f hf] at hs
  have hiT : f (key (runNet key (bitonicSort 0 p true) st i)) = true := by simp [f, T]
  have hjT := hs hiT
  simp only [f, decide_eq_true_eq] at hjT
  exact hjT

structure SortRec (kw bw : Nat) where
  keyBit : Nat → Bool
  valBit : Fin bw → Bool

def sortRecKey {kw bw : Nat} (r : SortRec kw bw) : Nat :=
  bitsVal r.keyBit kw

theorem netCircuit {n kw bw : Nat} {A : Set (Sig n)} (N : Nat)
    (net : List (Nat × Nat × Bool))
    (hnet : ∀ c ∈ net, c.1 < N ∧ c.2.1 < N)
    (st0 : (Fin n → Bool) → Nat → SortRec kw bw)
    (hK : ∀ idx < N, ∀ j < kw, (fun v => (st0 v idx).keyBit j) ∈ A)
    (hV : ∀ idx < N, ∀ j : Fin bw, (fun v => (st0 v idx).valBit j) ∈ A)
    (hfalse : (fun _ => false) ∈ A) :
    Build A
      ({f | ∃ idx < N, ∃ j < kw, f = fun v => (runNet sortRecKey net (st0 v) idx).keyBit j} ∪
       {f | ∃ idx < N, ∃ j : Fin bw, f = fun v => (runNet sortRecKey net (st0 v) idx).valBit j} ∪
       {f | ∃ t < net.length,
         f = (fun v => ((netSwaps sortRecKey net (st0 v)).getD t (0, 0, false)).2.2) ∨
         f = (fun v => !(((netSwaps sortRecKey net (st0 v)).getD t (0, 0, false)).2.2))})
      (net.length * (11 * kw + 6 * bw + 1)) := by
  induction net generalizing st0 A with
  | nil =>
    refine relax (idle ?_) le_rfl le_rfl (by simp)
    rintro f ((⟨idx, hidx, j, hj, rfl⟩ | ⟨idx, hidx, j, rfl⟩) | ⟨t, ht, _⟩)
    · exact hK idx hidx j hj
    · exact hV idx hidx j
    · simp at ht
  | cons c rest ih =>
    rcases c with ⟨u, v, asc⟩
    have hc := hnet (u, v, asc) List.mem_cons_self
    let swSig : Sig n := fun x => swapBit (sortRecKey (st0 x u)) (sortRecKey (st0 x v)) asc
    have Hsw : Build A {swSig} (5 * kw) := by
      cases asc with
      | true =>
        exact ltWordG (fun j x => (st0 x v).keyBit j) (fun j x => (st0 x u).keyBit j) kw
          (fun j hj => hK v hc.2 j hj) (fun j hj => hK u hc.1 j hj) hfalse
      | false =>
        exact ltWordG (fun j x => (st0 x u).keyBit j) (fun j x => (st0 x v).keyBit j) kw
          (fun j hj => hK u hc.1 j hj) (fun j hj => hK v hc.2 j hj) hfalse
    let nswSig : Sig n := nt swSig
    have Hnsw : Build (A ∪ {swSig}) {nswSig} 1 := notG (Or.inr rfl)
    let st1 : (Fin n → Bool) → Nat → SortRec kw bw := fun x => applySwap u v (swSig x) (st0 x)
    let A1 := A ∪ ({swSig} ∪ {nswSig})
    have hsw1 : swSig ∈ A1 := Or.inr (Or.inl rfl)
    have hnsw1 : nswSig ∈ A1 := Or.inr (Or.inr rfl)
    let K1 : Fin kw → Sig n := fun j x => (st1 x u).keyBit j.val
    let K2 : Fin kw → Sig n := fun j x => (st1 x v).keyBit j.val
    let V1 : Fin bw → Sig n := fun j x => (st1 x u).valBit j
    let V2 : Fin bw → Sig n := fun j x => (st1 x v).valBit j
    have HK1 : Build A1 (Set.range K1) (kw * 3) := finG K1 3 fun j => by
      have he : K1 j = fun x => if swSig x then (st0 x v).keyBit j.val else (st0 x u).keyBit j.val := by
        funext x; simp only [K1, st1, applySwap]; cases swSig x <;> simp
      rw [he]
      exact muxG hsw1 hnsw1 (Or.inl (hK v hc.2 j.val j.isLt)) (Or.inl (hK u hc.1 j.val j.isLt)) (fun _ => rfl)
    have HK2 : Build (A1 ∪ Set.range K1) (Set.range K2) (kw * 3) := finG K2 3 fun j => by
      have he : K2 j = fun x => if swSig x then (st0 x u).keyBit j.val else (st0 x v).keyBit j.val := by
        funext x; simp only [K2, st1, applySwap]
        by_cases huv : v = u
        · subst huv; cases swSig x <;> simp
        · cases swSig x <;> simp [huv]
      rw [he]
      exact muxG (Or.inl hsw1) (Or.inl hnsw1) (Or.inl (Or.inl (hK u hc.1 j.val j.isLt)))
        (Or.inl (Or.inl (hK v hc.2 j.val j.isLt))) (fun _ => rfl)
    have HV1 : Build (A1 ∪ (Set.range K1 ∪ Set.range K2)) (Set.range V1) (bw * 3) := finG V1 3 fun j => by
      have he : V1 j = fun x => if swSig x then (st0 x v).valBit j else (st0 x u).valBit j := by
        funext x; simp only [V1, st1, applySwap]; cases swSig x <;> simp
      rw [he]
      exact muxG (Or.inl hsw1) (Or.inl hnsw1) (Or.inl (Or.inl (hV v hc.2 j)))
        (Or.inl (Or.inl (hV u hc.1 j))) (fun _ => rfl)
    have HV2 : Build (A1 ∪ ((Set.range K1 ∪ Set.range K2) ∪ Set.range V1)) (Set.range V2) (bw * 3) := finG V2 3 fun j => by
      have he : V2 j = fun x => if swSig x then (st0 x u).valBit j else (st0 x v).valBit j := by
        funext x; simp only [V2, st1, applySwap]
        by_cases huv : v = u
        · subst huv; cases swSig x <;> simp
        · cases swSig x <;> simp [huv]
      rw [he]
      exact muxG (Or.inl hsw1) (Or.inl hnsw1) (Or.inl (Or.inl (hV u hc.1 j)))
        (Or.inl (Or.inl (hV v hc.2 j))) (fun _ => rfl)
    let B1 := ({swSig} ∪ {nswSig}) ∪ (((Set.range K1 ∪ Set.range K2) ∪ Set.range V1) ∪ Set.range V2)
    have Hstep : Build A B1 (11 * kw + 6 * bw + 1) := by
      have H0 := seq Hsw Hnsw
      have H1 := seq (seq (seq HK1 HK2) HV1) HV2
      exact relax (seq H0 H1) le_rfl le_rfl (by omega)
    have hK1 : ∀ idx < N, ∀ j < kw, (fun x => (st1 x idx).keyBit j) ∈ A ∪ B1 := by
      intro idx hidx j hj
      by_cases hu : idx = u
      · subst hu; exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl ⟨⟨j, hj⟩, rfl⟩))))
      · by_cases hv : idx = v
        · subst hv; exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr ⟨⟨j, hj⟩, rfl⟩))))
        · have he : (fun x => (st1 x idx).keyBit j) = (fun x => (st0 x idx).keyBit j) := by
            funext x; simp only [st1, applySwap]; cases swSig x <;> simp [hu, hv]
          rw [he]; exact Or.inl (hK idx hidx j hj)
    have hV1 : ∀ idx < N, ∀ j : Fin bw, (fun x => (st1 x idx).valBit j) ∈ A ∪ B1 := by
      intro idx hidx j
      by_cases hu : idx = u
      · subst hu; exact Or.inr (Or.inr (Or.inl (Or.inr ⟨j, rfl⟩)))
      · by_cases hv : idx = v
        · subst hv; exact Or.inr (Or.inr (Or.inr ⟨j, rfl⟩))
        · have he : (fun x => (st1 x idx).valBit j) = (fun x => (st0 x idx).valBit j) := by
            funext x; simp only [st1, applySwap]; cases swSig x <;> simp [hu, hv]
          rw [he]; exact Or.inl (hV idx hidx j)
    have Hrest := ih (fun c' hc' => hnet c' (List.mem_cons_of_mem _ hc')) st1 hK1 hV1 (Or.inl hfalse)
    refine relax (seq Hstep Hrest) le_rfl ?_ ?_
    · rintro f ((⟨idx, hidx, j, hj, rfl⟩ | ⟨idx, hidx, j, rfl⟩) | ⟨t, ht, hft⟩)
      · exact Or.inr (Or.inl (Or.inl ⟨idx, hidx, j, hj, rfl⟩))
      · exact Or.inr (Or.inl (Or.inr ⟨idx, hidx, j, rfl⟩))
      · cases t with
        | zero =>
          rcases hft with rfl | rfl
          · exact Or.inl (Or.inl (Or.inl rfl))
          · exact Or.inl (Or.inl (Or.inr rfl))
        | succ t =>
          simp only [List.length_cons] at ht
          exact Or.inr (Or.inr ⟨t, by omega, hft⟩)
    · simp only [List.length_cons]
      rw [Nat.succ_mul rest.length, Nat.add_comm]

theorem replayCircuit {n bw : Nat} {A : Set (Sig n)} (N : Nat)
    (sws : (Fin n → Bool) → List (Nat × Nat × Bool))
    (L : Nat) (hL : ∀ v, (sws v).length = L)
    (hidx_fixed : ∀ t < L, ∃ u v, u < N ∧ v < N ∧
      ∀ x, ((sws x).getD t (0, 0, false)).1 = u ∧ ((sws x).getD t (0, 0, false)).2.1 = v)
    (hsw_mem : ∀ t < L,
      (fun x => ((sws x).getD t (0, 0, false)).2.2) ∈ A ∧
      (fun x => !(((sws x).getD t (0, 0, false)).2.2)) ∈ A)
    (ans0 : (Fin n → Bool) → Nat → Fin bw → Bool)
    (hA0 : ∀ idx < N, ∀ j : Fin bw, (fun x => ans0 x idx j) ∈ A) :
    Build A {f | ∃ idx < N, ∃ j : Fin bw, f = fun x => replaySwaps (sws x) (ans0 x) idx j} (L * (6 * bw)) := by
  induction L generalizing sws ans0 A with
  | zero =>
    refine relax (idle ?_) le_rfl le_rfl (by simp)
    rintro f ⟨idx, hidx, j, rfl⟩
    have he : (fun x => replaySwaps (sws x) (ans0 x) idx j) = (fun x => ans0 x idx j) := by
      funext x
      have hnil : sws x = [] := List.eq_nil_of_length_eq_zero (hL x)
      rw [hnil]; rfl
    rw [he]; exact hA0 idx hidx j
  | succ L ih =>
    rcases hidx_fixed 0 (Nat.zero_lt_succ L) with ⟨u, v, hu, hv, huv⟩
    let swSig : Sig n := fun x => ((sws x).getD 0 (0, 0, false)).2.2
    let nswSig : Sig n := fun x => !(((sws x).getD 0 (0, 0, false)).2.2)
    have hsw0 := hsw_mem 0 (Nat.zero_lt_succ L)
    let ans1 : (Fin n → Bool) → Nat → Fin bw → Bool := fun x => applySwap u v (swSig x) (ans0 x)
    let V1 : Fin bw → Sig n := fun j x => ans1 x u j
    let V2 : Fin bw → Sig n := fun j x => ans1 x v j
    have HV1 : Build A (Set.range V1) (bw * 3) := finG V1 3 fun j => by
      have he : V1 j = fun x => if swSig x then ans0 x v j else ans0 x u j := by
        funext x; simp only [V1, ans1, applySwap]; cases swSig x <;> simp
      rw [he]
      exact muxG hsw0.1 hsw0.2 (hA0 v hv j) (hA0 u hu j) (fun _ => rfl)
    have HV2 : Build (A ∪ Set.range V1) (Set.range V2) (bw * 3) := finG V2 3 fun j => by
      have he : V2 j = fun x => if swSig x then ans0 x u j else ans0 x v j := by
        funext x; simp only [V2, ans1, applySwap]
        by_cases hvu : v = u
        · subst hvu; cases swSig x <;> simp
        · cases swSig x <;> simp [hvu]
      rw [he]
      exact muxG (Or.inl hsw0.1) (Or.inl hsw0.2) (Or.inl (hA0 u hu j)) (Or.inl (hA0 v hv j)) (fun _ => rfl)
    have Hstep := seq HV1 HV2
    let sws' : (Fin n → Bool) → List (Nat × Nat × Bool) := fun x => (sws x).tail
    have hL' : ∀ x, (sws' x).length = L := by intro x; simp [sws', List.length_tail, hL x]
    have hget_tail : ∀ t < L, ∀ x, (sws' x).getD t (0, 0, false) = (sws x).getD (t + 1) (0, 0, false) := by
      intro t _ x
      cases hs : sws x with
      | nil => have := hL x; rw [hs] at this; simp at this
      | cons c cs => simp [sws', hs]
    have hA1 : ∀ idx < N, ∀ j : Fin bw, (fun x => ans1 x idx j) ∈ A ∪ (Set.range V1 ∪ Set.range V2) := by
      intro idx hidx j
      by_cases h1 : idx = u
      · subst h1; exact Or.inr (Or.inl ⟨j, rfl⟩)
      · by_cases h2 : idx = v
        · subst h2; exact Or.inr (Or.inr ⟨j, rfl⟩)
        · have he : (fun x => ans1 x idx j) = (fun x => ans0 x idx j) := by
            funext x; simp only [ans1, applySwap]; cases swSig x <;> simp [h1, h2]
          rw [he]; exact Or.inl (hA0 idx hidx j)
    have Hrest := ih sws' hL'
      (fun t ht => by
        rcases hidx_fixed (t + 1) (by omega) with ⟨u', v', hu', hv', huv'⟩
        exact ⟨u', v', hu', hv', fun x => by rw [hget_tail t ht x]; exact huv' x⟩)
      (fun t ht => by
        have hm := hsw_mem (t + 1) (by omega)
        constructor
        · have he : (fun x => ((sws' x).getD t (0, 0, false)).2.2) =
              (fun x => ((sws x).getD (t + 1) (0, 0, false)).2.2) := by funext x; rw [hget_tail t ht x]
          rw [he]; exact Or.inl hm.1
        · have he : (fun x => !(((sws' x).getD t (0, 0, false)).2.2)) =
              (fun x => !(((sws x).getD (t + 1) (0, 0, false)).2.2)) := by funext x; rw [hget_tail t ht x]
          rw [he]; exact Or.inl hm.2)
      ans1 hA1
    refine relax (seq Hstep Hrest) le_rfl ?_ ?_
    · rintro f ⟨idx, hidx, j, rfl⟩
      right
      refine ⟨idx, hidx, j, ?_⟩
      funext x
      cases hs : sws x with
      | nil => have := hL x; rw [hs] at this; simp at this
      | cons c cs =>
        rcases c with ⟨u', v', sw'⟩
        have hc := huv x
        simp only [hs, List.getD_cons_zero] at hc
        have hsw_eq : swSig x = sw' := by simp [swSig, hs]
        have hu_eq : u' = u := hc.1
        have hv_eq : v' = v := hc.2
        subst hu_eq; subst hv_eq
        simp only [replaySwaps, sws', hs, List.tail_cons, ans1, hsw_eq]
    · rw [Nat.succ_mul L]; omega

def copyScan {bw : Nat} (isRep : Nat → Bool) (src : Nat → Fin bw → Bool) :
    Nat → (Fin bw → Bool) × (Nat → Fin bw → Bool)
  | 0 => (fun _ => false, fun _ _ => false)
  | m + 1 =>
    let prev := copyScan isRep src m
    let cur' := fun j => if isRep m then src m j else prev.1 j
    (cur', fun idx => if idx = m then cur' else prev.2 idx)

theorem copyScan_circuit {n bw : Nat} {A : Set (Sig n)} (N : Nat)
    (isRep : (Fin n → Bool) → Nat → Bool)
    (src : (Fin n → Bool) → Nat → Fin bw → Bool)
    (hRep : ∀ idx < N, (fun x => isRep x idx) ∈ A)
    (hSrc : ∀ idx < N, ∀ j : Fin bw, (fun x => src x idx j) ∈ A)
    (hfalse : (fun _ => false) ∈ A) :
    ∀ m ≤ N,
      Build A
        ({f | ∃ j : Fin bw, f = fun x => (copyScan (isRep x) (src x) m).1 j} ∪
         {f | ∃ idx < m, ∃ j : Fin bw, f = fun x => (copyScan (isRep x) (src x) m).2 idx j})
        (m * (3 * bw + 1)) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine relax (idle ?_) le_rfl le_rfl (by simp)
    rintro f (⟨j, rfl⟩ | ⟨idx, hidx, _⟩)
    · exact hfalse
    · omega
  | succ m ih =>
    intro hm
    have Hprev := ih (by omega)
    let Bprev :=
      {f | ∃ j : Fin bw, f = fun x => (copyScan (isRep x) (src x) m).1 j} ∪
      {f | ∃ idx < m, ∃ j : Fin bw, f = fun x => (copyScan (isRep x) (src x) m).2 idx j}
    let A1 := A ∪ Bprev
    let rSig : Sig n := fun x => isRep x m
    have Hr : Build A1 {nt rSig} 1 := notG (Or.inl (hRep m (by omega)))
    let curF : Fin bw → Sig n := fun j x => (copyScan (isRep x) (src x) (m + 1)).1 j
    have Hcur : Build (A1 ∪ {nt rSig}) (Set.range curF) (bw * 3) := finG curF 3 fun j => by
      have he : curF j = fun x => if rSig x then src x m j else (copyScan (isRep x) (src x) m).1 j := rfl
      rw [he]
      exact muxG (Or.inl (Or.inl (hRep m (by omega)))) (Or.inr rfl)
        (Or.inl (Or.inl (hSrc m (by omega) j)))
        (Or.inl (Or.inr (Or.inl ⟨j, rfl⟩)))
        (fun _ => rfl)
    have Htot := seq Hprev (seq Hr Hcur)
    refine relax Htot le_rfl ?_ ?_
    · rintro f (⟨j, rfl⟩ | ⟨idx, hidx, j, rfl⟩)
      · exact Or.inr (Or.inr ⟨j, rfl⟩)
      · by_cases him : idx = m
        · subst him
          exact Or.inr (Or.inr ⟨j, by funext x; simp [curF, copyScan]⟩)
        · exact Or.inl (Or.inr ⟨idx, by omega, j, by funext x; simp [copyScan, him]⟩)
    · rw [Nat.succ_mul m]; omega

theorem copyScan_spec {bw : Nat} (isRep : Nat → Bool) (src : Nat → Fin bw → Bool) :
    ∀ m i0 i, i0 ≤ i → i < m → isRep i0 = true →
      (∀ t, i0 < t → t ≤ i → isRep t = false) →
      (copyScan isRep src m).2 i = src i0 := by
  intro m
  induction m with
  | zero => intro i0 i _ hi _ _; omega
  | succ m ih =>
    intro i0 i hi0i him hrep hmid
    by_cases him' : i = m
    · subst him'
      simp only [copyScan, ↓reduceIte]
      by_cases h0 : i0 = i
      · subst h0; simp [hrep]
      · have hfi : isRep i = false := hmid i (by omega) le_rfl
        simp only [hfi, Bool.false_eq_true, ↓reduceIte]
        have hprev_eq : ∀ k, i0 < k → (∀ t, i0 < t → t < k → isRep t = false) →
            (copyScan isRep src k).1 = src i0 := by
          intro k
          induction k with
          | zero => intro hk _; omega
          | succ k ihk =>
            intro hk hmk
            simp only [copyScan]
            by_cases h0k : i0 = k
            · subst h0k; simp [hrep]
            · have hfk : isRep k = false := hmk k (by omega) (by omega)
              simp only [hfk, Bool.false_eq_true, ↓reduceIte]
              exact ihk (by omega) (fun t ht1 ht2 => hmk t ht1 (by omega))
        exact hprev_eq i (by omega) (fun t ht1 ht2 => hmid t ht1 (by omega))
    · simp only [copyScan, him', ↓reduceIte]
      exact ih i0 i hi0i (by omega) hrep hmid

end Bitonic

namespace Algo220

open Build220 Bitonic

def posOf {n : Nat} (hn : 0 < n) (v : Nat) : Fin n := ⟨v % n, Nat.mod_lt _ hn⟩

def sortDeg (K : Nat) : Nat := Nat.log2 (2 * K) + 1
def sortM (K : Nat) : Nat := 2 ^ sortDeg K
def sortNet (K : Nat) : List (Nat × Nat × Bool) := bitonicSort 0 (sortDeg K) true

theorem two_mul_K_lt_sortM {K : Nat} (hK : 1 ≤ K) : 2 * K < sortM K := by
  unfold sortM sortDeg
  exact Nat.lt_log2_self

theorem sortM_le_four_mul {K : Nat} (hK : 1 ≤ K) : sortM K ≤ 4 * K := by
  unfold sortM sortDeg
  rw [Nat.pow_succ]
  have hne : 2 * K ≠ 0 := by omega
  have hle : 2 ^ Nat.log2 (2 * K) ≤ 2 * K := Nat.log2_self_le hne
  omega

theorem sortDeg_le {w K : Nat} (hK_hi : K ≤ 4 ^ w) : sortDeg K ≤ 2 * w + 2 := by
  unfold sortDeg
  by_cases hK0 : K = 0
  · subst hK0; simp
  · have h2 : 2 * K < 2 ^ (2 * w + 2) := by
      have h4 : 4 ^ w = 2 ^ (2 * w) := by
        rw [show (4 : Nat) = 2 ^ 2 by rfl, ← Nat.pow_mul]
      rw [Nat.pow_succ, Nat.pow_succ, ← h4]
      have hpos : 0 < 4 ^ w := Nat.pow_pos (by omega)
      omega
    have hlog : Nat.log2 (2 * K) < 2 * w + 2 := (Nat.log2_lt (by omega)).mpr h2
    omega

theorem sortNet_length_le {n w K : Nat} (hw : w ≤ n) (hK_lo : 1 ≤ K) (hK_hi : K ≤ 4 ^ w) :
    (sortNet K).length ≤ 6 * (n + 1) ^ 2 * K := by
  have hlen := bitonicSort_length 0 (sortDeg K) true
  have hd : sortDeg K ≤ 2 * n + 2 := (sortDeg_le hK_hi).trans (by omega)
  have hm : 2 ^ sortDeg K ≤ 4 * K := sortM_le_four_mul hK_lo
  have hmul : sortDeg K * (sortDeg K + 1) * 2 ^ sortDeg K ≤ (2 * n + 2) * (2 * n + 3) * (4 * K) := by
    apply Nat.mul_le_mul _ hm
    exact Nat.mul_le_mul hd (by omega)
  have hq : (2 * n + 2) * (2 * n + 3) ≤ 6 * (n + 1) ^ 2 := by
    have h1 : 2 * n + 2 = 2 * (n + 1) := by omega
    have h2 : 2 * n + 3 ≤ 3 * (n + 1) := by omega
    calc (2 * n + 2) * (2 * n + 3)
        ≤ 2 * (n + 1) * (3 * (n + 1)) := Nat.mul_le_mul (by omega) h2
      _ = 6 * (n + 1) ^ 2 := by ring
  have h4 : 4 * (sortNet K).length ≤ 4 * (6 * (n + 1) ^ 2 * K) := by
    calc 4 * (sortNet K).length
        = sortDeg K * (sortDeg K + 1) * 2 ^ sortDeg K := hlen
      _ ≤ (2 * n + 2) * (2 * n + 3) * (4 * K) := hmul
      _ ≤ (6 * (n + 1) ^ 2) * (4 * K) := Nat.mul_le_mul_right _ hq
      _ = 4 * (6 * (n + 1) ^ 2 * K) := by ring
  omega

theorem lookup_cost_le {n w q K : Nat} (hn : 0 < n) (hw : w ≤ n)
    (hK_lo : 2 ^ w ≤ K) (hK_hi : K ≤ 4 ^ w) (hq : q ≤ 2 * K) :
    128 * (2 ^ (w + 1) + q) * (w + 1 + 1 + Nat.log2 (q + 1) + 3) ^ 3 ≤ 46656 * (n + 1) ^ 3 * K := by
  have h2w : 2 ^ (w + 1) ≤ 2 * K := by rw [Nat.pow_succ]; omega
  have hsum : 2 ^ (w + 1) + q ≤ 4 * K := by omega
  have hlog : Nat.log2 (q + 1) ≤ 2 * w + 1 := by
    have hlt : q + 1 < 2 ^ (2 * w + 2) := by
      have h4 : 4 ^ w = 2 ^ (2 * w) := by
        rw [show (4 : Nat) = 2 ^ 2 by rfl, ← Nat.pow_mul]
      rw [Nat.pow_succ, Nat.pow_succ, ← h4]
      have hpos : 0 < 4 ^ w := Nat.pow_pos (by omega)
      omega
    have h := (Nat.log2_lt (by omega)).mpr hlt
    omega
  have hbase : 2 * (w + 1 + 1 + Nat.log2 (q + 1) + 3) ≤ 9 * (n + 1) := by omega
  have hcube : 8 * (w + 1 + 1 + Nat.log2 (q + 1) + 3) ^ 3 ≤ 729 * (n + 1) ^ 3 := by
    have hpow := Nat.pow_le_pow_left hbase 3
    calc 8 * (w + 1 + 1 + Nat.log2 (q + 1) + 3) ^ 3
        = (2 * (w + 1 + 1 + Nat.log2 (q + 1) + 3)) ^ 3 := by ring
      _ ≤ (9 * (n + 1)) ^ 3 := hpow
      _ = 729 * (n + 1) ^ 3 := by ring
  calc 128 * (2 ^ (w + 1) + q) * (w + 1 + 1 + Nat.log2 (q + 1) + 3) ^ 3
      ≤ 128 * (4 * K) * (w + 1 + 1 + Nat.log2 (q + 1) + 3) ^ 3 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hsum)
    _ = 64 * K * (8 * (w + 1 + 1 + Nat.log2 (q + 1) + 3) ^ 3) := by ring
    _ ≤ 64 * K * (729 * (n + 1) ^ 3) := Nat.mul_le_mul_left _ hcube
    _ = 46656 * (n + 1) ^ 3 * K := by ring

def readRow {n w : Nat} (x : Fin (n * 2 ^ (w + 1)) → Bool) (r : Fin n) (pat : Fin (w + 1) → Bool) : Bool :=
  x ⟨r.val * 2 ^ (w + 1) + bitsVal (fun b => if h : b < w + 1 then pat ⟨b, h⟩ else false) (w + 1),
    by
      have hlt := bitsVal_lt (fun b => if h : b < w + 1 then pat ⟨b, h⟩ else false) (w + 1)
      have hr : r.val + 1 ≤ n := r.isLt
      calc r.val * 2 ^ (w + 1) + bitsVal _ (w + 1)
          < r.val * 2 ^ (w + 1) + 2 ^ (w + 1) := Nat.add_lt_add_left hlt _
        _ = (r.val + 1) * 2 ^ (w + 1) := by rw [Nat.succ_mul]
        _ ≤ n * 2 ^ (w + 1) := Nat.mul_le_mul_right _ hr⟩

def shiftPair (w : Nat) (p : Fin (2 * w) → Bool) (b : Bool) : Fin (2 * w) → Bool :=
  fun k =>
    if h1 : k.val < w then p k
    else if h2 : k.val + 1 < 2 * w then p ⟨k.val + 1, h2⟩
    else b

def extPat (w : Nat) (p : Fin (2 * w) → Bool) (b : Bool) : Fin (w + 1) → Bool :=
  fun k => if hk : k.val < w then p ⟨w + k.val, by omega⟩ else b

def wrapPat (n w r : Nat) (hr1 : n - w ≤ r) (hr2 : r < n) (hw : w ≤ n)
    (p : Fin (2 * w) → Bool) : Fin (w + 1) → Bool :=
  fun k =>
    if hlt : r + k.val < n then p ⟨w + (r + k.val - (n - w)), by omega⟩
    else p ⟨r + k.val - n, by omega⟩

structure FwdState (w K : Nat) where
  val : Fin K → Bool
  pair : Fin K → Fin (2 * w) → Bool

def fwdInit (w K : Nat) : FwdState w K where
  val j := decide (j.val < 2 ^ w)
  pair j k := if k.val < w then j.val.testBit k.val else j.val.testBit (k.val - w)

structure StepData (w K : Nat) where
  ok : Fin (2 * K) → Bool
  cval : Nat → Bool
  cpair : Nat → Fin (2 * w) → Bool
  s1 : Nat → SortRec (2 * w + 1) 0
  sw1 : List (Nat × Nat × Bool)
  isRep : Nat → Bool
  s2 : Nat → SortRec 1 (2 * w)
  sw2 : List (Nat × Nat × Bool)
  next : FwdState w K

def runFwdStep {n w K : Nat} (hn : 0 < n) (hK : 1 ≤ K)
    (h : Nat) (st : FwdState w K) (x : Fin (n * 2 ^ (w + 1)) → Bool) : StepData w K :=
  let ok : Fin (2 * K) → Bool := fun u =>
    readRow x (posOf hn h) (extPat w (st.pair ⟨u.val / 2, by omega⟩) (decide (u.val % 2 = 1)))
  let cval : Nat → Bool := fun i =>
    if hi : i < 2 * K then st.val ⟨i / 2, by omega⟩ && ok ⟨i, hi⟩ else false
  let cpair : Nat → Fin (2 * w) → Bool := fun i =>
    if hi : i < 2 * K then shiftPair w (st.pair ⟨i / 2, by omega⟩) (decide (i % 2 = 1)) else fun _ => false
  let rec1 : Nat → SortRec (2 * w + 1) 0 := fun i =>
    ⟨fun j => if hj : j < 2 * w then cpair i ⟨j, hj⟩ else !(cval i), Fin.elim0⟩
  let s1 := runNet sortRecKey (sortNet K) rec1
  let sw1 := netSwaps sortRecKey (sortNet K) rec1
  let isRep : Nat → Bool := fun i =>
    !((s1 i).keyBit (2 * w)) &&
      (decide (i = 0) || (List.finRange (2 * w)).any (fun k => xor ((s1 i).keyBit k.val) ((s1 (i - 1)).keyBit k.val)))
  let rec2 : Nat → SortRec 1 (2 * w) := fun i =>
    ⟨fun _ => !(isRep i), fun k => (s1 i).keyBit k.val⟩
  let s2 := runNet sortRecKey (sortNet K) rec2
  let sw2 := netSwaps sortRecKey (sortNet K) rec2
  let next : FwdState w K := ⟨fun j => !((s2 j.val).keyBit 0), fun j => (s2 j.val).valBit⟩
  ⟨ok, cval, cpair, s1, sw1, isRep, s2, sw2, next⟩

def fwdState {n w K : Nat} (hn : 0 < n) (hK : 1 ≤ K) :
    Nat → (Fin (n * 2 ^ (w + 1)) → Bool) → FwdState w K
  | 0, _ => fwdInit w K
  | h + 1, x => (runFwdStep hn hK h (fwdState hn hK h x) x).next

def stepAt {n w K : Nat} (hn : 0 < n) (hK : 1 ≤ K) (h : Nat)
    (x : Fin (n * 2 ^ (w + 1)) → Bool) : StepData w K :=
  runFwdStep hn hK h (fwdState hn hK h x) x

def wrapOk {n w K : Nat} (hn : 0 < n) (hw : w ≤ n) (hK : 1 ≤ K)
    (r : Fin w) (j : Fin K) (x : Fin (n * 2 ^ (w + 1)) → Bool) : Bool :=
  readRow x (posOf hn (n - w + r.val))
    (wrapPat n w (n - w + r.val) (by omega) (by omega) hw ((fwdState hn hK (n - w) x).pair j))

def firstBadScan {n w K : Nat} (hn : 0 < n) (hw : w ≤ n) (hK : 1 ≤ K)
    (j : Fin K) (x : Fin (n * 2 ^ (w + 1)) → Bool) : Nat → Bool × (Nat → Bool)
  | 0 => (false, fun _ => false)
  | t + 1 =>
    let prev := firstBadScan hn hw hK j x t
    let bad := if ht : t < w then !(wrapOk hn hw hK ⟨t, ht⟩ j x) else false
    let pick := !(prev.1) && bad
    (prev.1 || bad, fun r => if r = t then pick else prev.2 r)

def termBad {n w K : Nat} (hn : 0 < n) (hw : w ≤ n) (hK : 1 ≤ K)
    (j : Fin K) (x : Fin (n * 2 ^ (w + 1)) → Bool) : Bool :=
  (firstBadScan hn hw hK j x w).1

def termPick {n w K : Nat} (hn : 0 < n) (hw : w ≤ n) (hK : 1 ≤ K)
    (j : Fin K) (r : Fin w) (x : Fin (n * 2 ^ (w + 1)) → Bool) : Bool :=
  (firstBadScan hn hw hK j x w).2 r.val

def wrapUses (n w r : Nat) (k : Fin (2 * w)) : Bool :=
  if k.val < w then
    (List.finRange (w + 1)).any (fun o => decide (n ≤ n - w + r + o.val ∧ n - w + r + o.val - n = k.val))
  else
    (List.finRange (w + 1)).any (fun o => decide (n - w + r + o.val < n ∧ n - w + r + o.val - (n - w) = k.val - w))

def termMask {n w K : Nat} (hn : 0 < n) (hw : w ≤ n) (hK : 1 ≤ K)
    (j : Fin K) (x : Fin (n * 2 ^ (w + 1)) → Bool) (k : Fin (2 * w)) : Bool :=
  ((List.finRange w).filter (fun r => wrapUses n w r.val k)).any (fun r => termPick hn hw hK j r x)

def outSig {n w K : Nat} (hn : 0 < n) (hw : w ≤ n) (hK : 1 ≤ K)
    (x : Fin (n * 2 ^ (w + 1)) → Bool) : Bool :=
  (List.finRange K).all (fun j => !((fwdState hn hK (n - w) x).val j) || termBad hn hw hK j x)

structure BwdStepData (w K : Nat) where
  rev2 : Nat → Fin (2 * w) → Bool
  copied : Nat → Fin (2 * w) → Bool
  rev1 : Nat → Fin (2 * w) → Bool
  hasPos : Fin K → Bool
  hasNeg : Fin K → Bool
  bm0 : Fin K → Fin (2 * w) → Bool
  bm1 : Fin K → Fin (2 * w) → Bool
  mask : Fin K → Fin (2 * w) → Bool

def runBwdStep {n w K : Nat} (hn : 0 < n) (hK : 1 ≤ K)
    (h : Nat) (mNext : Fin K → Fin (2 * w) → Bool) (x : Fin (n * 2 ^ (w + 1)) → Bool) : BwdStepData w K :=
  let sd := stepAt hn hK h x
  let u2 : Nat → Fin (2 * w) → Bool := fun i => if hi : i < K then mNext ⟨i, hi⟩ else fun _ => false
  let rev2 := replaySwaps sd.sw2.reverse u2
  let copied := (copyScan sd.isRep rev2 (sortM K)).2
  let rev1 := replaySwaps sd.sw1.reverse copied
  let ok0 : Fin K → Bool := fun j => sd.ok ⟨2 * j.val, by omega⟩
  let ok1 : Fin K → Bool := fun j => sd.ok ⟨2 * j.val + 1, by omega⟩
  let hasPos : Fin K → Bool := fun j =>
    !(ok0 j) || (if hw0 : 0 < w then rev1 (2 * j.val) ⟨2 * w - 1, by omega⟩ else false)
  let hasNeg : Fin K → Bool := fun j =>
    !(ok1 j) || (if hw0 : 0 < w then rev1 (2 * j.val + 1) ⟨2 * w - 1, by omega⟩ else false)
  let bm0 : Fin K → Fin (2 * w) → Bool := fun j k =>
    if k.val < w then ok0 j && rev1 (2 * j.val) k
    else if k.val = w then !(ok0 j)
    else !(ok0 j) || rev1 (2 * j.val) ⟨k.val - 1, by omega⟩
  let bm1 : Fin K → Fin (2 * w) → Bool := fun j k =>
    if k.val < w then ok1 j && rev1 (2 * j.val + 1) k
    else if k.val = w then !(ok1 j)
    else !(ok1 j) || rev1 (2 * j.val + 1) ⟨k.val - 1, by omega⟩
  let mask : Fin K → Fin (2 * w) → Bool := fun j k =>
    combMask (hasPos j) (hasNeg j) (bm0 j k) (bm1 j k)
  ⟨rev2, copied, rev1, hasPos, hasNeg, bm0, bm1, mask⟩

def bwdMaskRem {n w K : Nat} (hn : 0 < n) (hw : w ≤ n) (hK : 1 ≤ K) :
    Nat → (Fin (n * 2 ^ (w + 1)) → Bool) → Fin K → Fin (2 * w) → Bool
  | 0, x => fun j => termMask hn hw hK j x
  | rem + 1, x => (runBwdStep hn hK (n - w - (rem + 1)) (bwdMaskRem hn hw hK rem x) x).mask

def bwdStepAt {n w K : Nat} (hn : 0 < n) (hw : w ≤ n) (hK : 1 ≤ K) (h : Nat)
    (x : Fin (n * 2 ^ (w + 1)) → Bool) : BwdStepData w K :=
  runBwdStep hn hK h (bwdMaskRem hn hw hK (n - w - (h + 1)) x) x

def bwdMaskAt {n w K : Nat} (hn : 0 < n) (hw : w ≤ n) (hK : 1 ≤ K) (h : Nat)
    (x : Fin (n * 2 ^ (w + 1)) → Bool) : Fin K → Fin (2 * w) → Bool :=
  bwdMaskRem hn hw hK (n - w - h) x

def seedMaskRem {n w K : Nat} (hn : 0 < n) (hw : w ≤ n) (hK_lo : 2 ^ w ≤ K) (hK : 1 ≤ K) :
    Nat → (Fin (n * 2 ^ (w + 1)) → Bool) → Nat → Fin w → Bool
  | 0, x, p, a =>
    if hp : p < K then
      bwdMaskRem hn hw hK (n - w) x ⟨p, hp⟩ ⟨a.val, by omega⟩ ||
      bwdMaskRem hn hw hK (n - w) x ⟨p, hp⟩ ⟨w + a.val, by omega⟩
    else false
  | rem + 1, x, p, a =>
    let d := w - (rem + 1)
    let prev := seedMaskRem hn hw hK_lo hK rem x
    if hd : d < w then
      let hp := prev p ⟨d, hd⟩
      let hneg := prev (p + 2 ^ d) ⟨d, hd⟩
      if a.val < d then combMask hp hneg (prev p a) (prev (p + 2 ^ d) a) else false
    else false

def seedEn {n w K : Nat} (hn : 0 < n) (hw : w ≤ n) (hK_lo : 2 ^ w ≤ K) (hK : 1 ≤ K)
    (d p : Nat) (hd : d < w) (x : Fin (n * 2 ^ (w + 1)) → Bool) : Bool :=
  let prev := seedMaskRem hn hw hK_lo hK (w - (d + 1)) x
  prev p ⟨d, hd⟩ && prev (p + 2 ^ d) ⟨d, hd⟩

def pairClauseMem {n w : Nat} (h : Nat) (pair mask : Fin (2 * w) → Bool)
    (lit : Fin n × Bool) : Bool :=
  let inL :=
    if hv : lit.1.val < w then
      mask ⟨lit.1.val, by omega⟩ && (!(pair ⟨lit.1.val, by omega⟩) == lit.2)
    else false
  let inR :=
    if hv : h ≤ lit.1.val ∧ lit.1.val < h + w then
      mask ⟨w + (lit.1.val - h), by omega⟩ && (!(pair ⟨w + (lit.1.val - h), by omega⟩) == lit.2)
    else false
  inL || inR

def axBranchMem {n w : Nat} (h : Nat) (pair : Fin (2 * w) → Bool) (b : Bool)
    (lit : Fin n × Bool) : Bool :=
  if hv : h ≤ lit.1.val ∧ lit.1.val < h + w then
    !(pair ⟨w + (lit.1.val - h), by omega⟩) == lit.2
  else if lit.1.val = h + w then
    (!b) == lit.2
  else false

def semEnable {n w K : Nat} (hn : 0 < n) (hw : w ≤ n) (hK_lo : 2 ^ w ≤ K) (hK : 1 ≤ K)
    (s : Fin ((3 * (n - w) + 2) * K)) (x : Fin (n * 2 ^ (w + 1)) → Bool) : Bool :=
  if hs1 : s.val < K then
    if hs2 : s.val < 2 ^ w - 1 then
      let d := Nat.log2 (s.val + 1)
      let p := s.val + 1 - 2 ^ d
      if hd : d < w then seedEn hn hw hK_lo hK d p hd x else false
    else false
  else if hs3 : s.val < K + 3 * (n - w) * K then
    let off := s.val - K
    let h := off / (3 * K)
    let rem := off % (3 * K)
    let kind := rem / K
    let j : Fin K := ⟨rem % K, Nat.mod_lt _ (by omega)⟩
    let v := (fwdState hn hK h x).val j
    if kind = 0 then
      let bd := bwdStepAt hn hw hK h x
      v && bd.hasPos j && bd.hasNeg j
    else if kind = 1 then
      v && !((stepAt hn hK h x).ok ⟨2 * j.val, by omega⟩)
    else
      v && !((stepAt hn hK h x).ok ⟨2 * j.val + 1, by omega⟩)
  else
    let j : Fin K := ⟨s.val - (K + 3 * (n - w) * K), by
      have hlt := s.isLt
      have heq : (3 * (n - w) + 2) * K = K + 3 * (n - w) * K + K := by ring
      omega⟩
    (fwdState hn hK (n - w) x).val j && termBad hn hw hK j x

def semMember {n w K : Nat} (hn : 0 < n) (hw : w ≤ n) (hK_lo : 2 ^ w ≤ K) (hK : 1 ≤ K)
    (s : Fin ((3 * (n - w) + 2) * K)) (lit : Fin n × Bool) (x : Fin (n * 2 ^ (w + 1)) → Bool) : Bool :=
  if hs1 : s.val < K then
    if hs2 : s.val < 2 ^ w - 1 then
      let d := Nat.log2 (s.val + 1)
      let p := s.val + 1 - 2 ^ d
      if hd : d < w then
        if hv : lit.1.val < d then
          if !(p.testBit lit.1.val) == lit.2 then
            seedMaskRem hn hw hK_lo hK (w - d) x p ⟨lit.1.val, by omega⟩
          else false
        else false
      else false
    else false
  else if hs3 : s.val < K + 3 * (n - w) * K then
    let off := s.val - K
    let h := off / (3 * K)
    let rem := off % (3 * K)
    let kind := rem / K
    let j : Fin K := ⟨rem % K, Nat.mod_lt _ (by omega)⟩
    let pair := (fwdState hn hK h x).pair j
    if kind = 0 then
      pairClauseMem h pair (bwdMaskAt hn hw hK h x j) lit
    else if kind = 1 then
      axBranchMem h pair false lit
    else
      axBranchMem h pair true lit
  else
    let j : Fin K := ⟨s.val - (K + 3 * (n - w) * K), by
      have hlt := s.isLt
      have heq : (3 * (n - w) + 2) * K = K + 3 * (n - w) * K + K := by ring
      omega⟩
    pairClauseMem (n - w) ((fwdState hn hK (n - w) x).pair j) (termMask hn hw hK j x) lit

theorem fwdStep_build {n w K : Nat} (hn : 0 < n) (hw : w ≤ n) (hK_lo : 2 ^ w ≤ K) (hK_hi : K ≤ 4 ^ w)
    {A : Set (Sig (n * 2 ^ (w + 1)))} (h : Nat)
    (st : (Fin (n * 2 ^ (w + 1)) → Bool) → FwdState w K)
    (hVal : ∀ j : Fin K, (fun x => (st x).val j) ∈ A)
    (hPair : ∀ (j : Fin K) (k : Fin (2 * w)), (fun x => (st x).pair j k) ∈ A)
    (hinp : ∀ a : Fin (n * 2 ^ (w + 1)), (fun x => x a) ∈ A)
    (hfalse : (fun _ => false) ∈ A) (htrue : (fun _ => true) ∈ A) :
    have hK1 : 1 ≤ K := le_trans (Nat.one_le_two_pow) hK_lo
    let sd := fun x => runFwdStep hn hK1 h (st x) x
    Build A
      ({f | ∃ u : Fin (2 * K), f = fun x => (sd x).ok u} ∪
       {f | ∃ i < sortM K, f = fun x => (sd x).isRep i} ∪
       {f | ∃ t < (sortNet K).length,
         f = (fun x => ((sd x).sw1.getD t (0, 0, false)).2.2) ∨
         f = (fun x => !(((sd x).sw1.getD t (0, 0, false)).2.2)) ∨
         f = (fun x => ((sd x).sw2.getD t (0, 0, false)).2.2) ∨
         f = (fun x => !(((sd x).sw2.getD t (0, 0, false)).2.2))} ∪
       {f | ∃ j : Fin K, f = fun x => (sd x).next.val j} ∪
       {f | ∃ (j : Fin K) (k : Fin (2 * w)), f = fun x => (sd x).next.pair j k})
      (47000 * (n + 1) ^ 3 * K) := by
  have hK1 : 1 ≤ K := le_trans Nat.one_le_two_pow hK_lo
  dsimp only
  let sd := fun x => runFwdStep hn hK1 h (st x) x
  let addr : Fin (2 * K) → Fin (w + 1) → Sig (n * 2 ^ (w + 1)) :=
    fun u bit x => extPat w ((st x).pair ⟨u.val / 2, by omega⟩) (decide (u.val % 2 = 1)) bit
  have haddr : ∀ u bit, addr u bit ∈ A := by
    intro u bit
    dsimp only [addr, extPat]
    split_ifs with hk
    · exact hPair ⟨u.val / 2, by omega⟩ ⟨w + bit.val, by omega⟩
    · cases decide (u.val % 2 = 1)
      · exact hfalse
      · exact htrue
  have Hok_raw := batchLookup hn (posOf hn h) addr haddr hinp
  have Hok_cost := lookup_cost_le hn hw hK_lo hK_hi (le_refl (2 * K))
  let Bok : Set (Sig (n * 2 ^ (w + 1))) := {f | ∃ u : Fin (2 * K), f = fun x => (sd x).ok u}
  have Hok : Build A Bok (46656 * (n + 1) ^ 3 * K) := by
    refine relax Hok_raw le_rfl ?_ Hok_cost
    rintro f ⟨u, rfl⟩
    exact ⟨u, rfl⟩
  let A1 := A ∪ Bok
  let cvalF : Fin (2 * K) → Sig (n * 2 ^ (w + 1)) := fun u x => (sd x).cval u.val
  have Hcval : Build A1 (Set.range cvalF) (2 * K) := by
    have h1 := finG (A := A1) cvalF 1 (fun u => by
      have he : cvalF u = an (fun x => (st x).val ⟨u.val / 2, by omega⟩) (fun x => (sd x).ok u) := by
        funext x; simp [cvalF, sd, runFwdStep, an]
      rw [he]
      exact andG (A := A1) (Or.inl (hVal ⟨u.val / 2, by omega⟩)) (Or.inr ⟨u, rfl⟩))
    exact relax h1 le_rfl le_rfl (by omega)
  let A2 := A1 ∪ Set.range cvalF
  let ncvalF : Fin (2 * K) → Sig (n * 2 ^ (w + 1)) := fun u x => !((sd x).cval u.val)
  have Hncval : Build A2 (Set.range ncvalF) (2 * K) := by
    have h1 := finG (A := A2) ncvalF 1 (fun u => notG (A := A2) (Or.inr ⟨u, rfl⟩))
    exact relax h1 le_rfl le_rfl (by omega)
  let A3 := A2 ∪ Set.range ncvalF
  let rec1 : (Fin (n * 2 ^ (w + 1)) → Bool) → Nat → SortRec (2 * w + 1) 0 := fun x i =>
    ⟨fun j => if hj : j < 2 * w then (sd x).cpair i ⟨j, hj⟩ else !((sd x).cval i), Fin.elim0⟩
  have hnet_mem : ∀ c ∈ sortNet K, c.1 < sortM K ∧ c.2.1 < sortM K := by
    intro c hc
    have hm := bitonicSort_mem 0 (sortDeg K) true c hc
    unfold sortM; omega
  have hK1_mem : ∀ idx < sortM K, ∀ j < 2 * w + 1, (fun x => (rec1 x idx).keyBit j) ∈ A3 := by
    intro idx _ j hj
    dsimp only [rec1]
    split_ifs with hjw
    · by_cases hi : idx < 2 * K
      · have he : (fun x => (sd x).cpair idx ⟨j, hjw⟩) =
            fun x => shiftPair w ((st x).pair ⟨idx / 2, by omega⟩) (decide (idx % 2 = 1)) ⟨j, hjw⟩ := by
          funext x; simp [sd, runFwdStep, hi]
        rw [he]
        dsimp only [shiftPair]
        split_ifs
        · exact Or.inl (Or.inl (Or.inl (hPair _ _)))
        · exact Or.inl (Or.inl (Or.inl (hPair _ _)))
        · cases decide (idx % 2 = 1)
          · exact Or.inl (Or.inl (Or.inl hfalse))
          · exact Or.inl (Or.inl (Or.inl htrue))
      · have he : (fun x => (sd x).cpair idx ⟨j, hjw⟩) = (fun _ => false) := by
          funext x; simp [sd, runFwdStep, hi]
        rw [he]; exact Or.inl (Or.inl (Or.inl hfalse))
    · by_cases hi : idx < 2 * K
      · exact Or.inr ⟨⟨idx, hi⟩, rfl⟩
      · have he : (fun x => !((sd x).cval idx)) = (fun _ => true) := by
          funext x; simp [sd, runFwdStep, hi]
        rw [he]; exact Or.inl (Or.inl (Or.inl htrue))
  have Hs1 := netCircuit (sortM K) (sortNet K) hnet_mem rec1 hK1_mem (fun _ _ j => j.elim0)
    (Or.inl (Or.inl (Or.inl hfalse)))
  let Bs1 :=
    {f | ∃ idx < sortM K, ∃ j < 2 * w + 1, f = fun x => ((sd x).s1 idx).keyBit j} ∪
    {f | ∃ idx < sortM K, ∃ j : Fin 0, f = fun x => ((sd x).s1 idx).valBit j} ∪
    {f | ∃ t < (sortNet K).length,
      f = (fun x => ((sd x).sw1.getD t (0, 0, false)).2.2) ∨
      f = (fun x => !(((sd x).sw1.getD t (0, 0, false)).2.2))}
  have Hs1' : Build A3 Bs1 ((sortNet K).length * (22 * w + 12)) :=
    relax Hs1 le_rfl le_rfl (by apply Nat.mul_le_mul_left; omega)
  let A4 := A3 ∪ Bs1
  have hs1K : ∀ idx < sortM K, ∀ j < 2 * w + 1, (fun x => ((sd x).s1 idx).keyBit j) ∈ A4 :=
    fun idx hidx j hj => Or.inr (Or.inl (Or.inl ⟨idx, hidx, j, hj, rfl⟩))
  let repF : Fin (sortM K) → Sig (n * 2 ^ (w + 1)) := fun i x => (sd x).isRep i.val
  have Hrep : Build A4 (Set.range repF) (sortM K * (12 * w + 3)) := by
    refine finG repF (12 * w + 3) (fun i => ?_)
    have hnotv : Build A4 {nt (fun x => ((sd x).s1 i.val).keyBit (2 * w))} 1 :=
      notG (hs1K i.val i.isLt (2 * w) (by omega))
    by_cases hi0 : i.val = 0
    · have he : repF i = nt (fun x => ((sd x).s1 i.val).keyBit (2 * w)) := by
        funext x; simp [repF, sd, runFwdStep, hi0, nt]
      rw [he]; exact relax hnotv le_rfl le_rfl (by omega)
    · let xors : Fin (2 * w) → Sig (n * 2 ^ (w + 1)) :=
        fun k x => xor (((sd x).s1 i.val).keyBit k.val) (((sd x).s1 (i.val - 1)).keyBit k.val)
      have Hxors : Build (A4 ∪ {nt (fun x => ((sd x).s1 i.val).keyBit (2 * w))}) (Set.range xors) (2 * w * 5) :=
        finG xors 5 (fun k =>
          xorG (Or.inl (hs1K i.val i.isLt k.val (by omega)))
               (Or.inl (hs1K (i.val - 1) (by omega) k.val (by omega))))
      let anySig : Sig (n * 2 ^ (w + 1)) :=
        fun x => ((List.finRange (2 * w)).map xors).any (fun f => f x)
      have Hany : Build (A4 ∪ ({nt (fun x => ((sd x).s1 i.val).keyBit (2 * w))} ∪ Set.range xors))
          {anySig} (2 * w) := by
        have h := orListG (A := A4 ∪ ({nt (fun x => ((sd x).s1 i.val).keyBit (2 * w))} ∪ Set.range xors))
          ((List.finRange (2 * w)).map xors)
          (fun f hf => by rcases List.mem_map.mp hf with ⟨k, _, rfl⟩; exact Or.inr (Or.inr ⟨k, rfl⟩))
          (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hfalse)))))
        exact relax h le_rfl le_rfl (by simp)
      have hcomb := seq (seq hnotv Hxors) Hany
      have Hand : Build (A4 ∪ (({nt (fun x => ((sd x).s1 i.val).keyBit (2 * w))} ∪ Set.range xors) ∪ {anySig}))
          {an (nt (fun x => ((sd x).s1 i.val).keyBit (2 * w))) anySig} 1 :=
        andG (Or.inr (Or.inl (Or.inl rfl))) (Or.inr (Or.inr rfl))
      have he : an (nt (fun x => ((sd x).s1 i.val).keyBit (2 * w))) anySig = repF i := by
        funext x
        simp only [an, nt, anySig, repF, sd, runFwdStep, hi0, decide_false, Bool.false_or, List.any_map]
        rfl
      rw [he] at Hand
      exact relax (seq hcomb Hand) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) (by omega)
  let A5 := A4 ∪ Set.range repF
  let nrepF : Fin (sortM K) → Sig (n * 2 ^ (w + 1)) := fun i x => !((sd x).isRep i.val)
  have Hnrep : Build A5 (Set.range nrepF) (sortM K) := by
    have h := finG (A := A5) nrepF 1 (fun i => notG (A := A5) (Or.inr ⟨i, rfl⟩))
    exact relax h le_rfl le_rfl (by omega)
  let A6 := A5 ∪ Set.range nrepF
  let rec2 : (Fin (n * 2 ^ (w + 1)) → Bool) → Nat → SortRec 1 (2 * w) := fun x i =>
    ⟨fun _ => !((sd x).isRep i), fun k => ((sd x).s1 i).keyBit k.val⟩
  have Hs2 := netCircuit (A := A6) (sortM K) (sortNet K) hnet_mem rec2
    (fun idx hidx j _ => Or.inr ⟨⟨idx, hidx⟩, rfl⟩)
    (fun idx hidx k => Or.inl (Or.inl (hs1K idx hidx k.val (by omega))))
    (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hfalse))))))
  let Bs2 :=
    {f | ∃ idx < sortM K, ∃ j < 1, f = fun x => ((sd x).s2 idx).keyBit j} ∪
    {f | ∃ idx < sortM K, ∃ j : Fin (2 * w), f = fun x => ((sd x).s2 idx).valBit j} ∪
    {f | ∃ t < (sortNet K).length,
      f = (fun x => ((sd x).sw2.getD t (0, 0, false)).2.2) ∨
      f = (fun x => !(((sd x).sw2.getD t (0, 0, false)).2.2))}
  have Hs2' : Build A6 Bs2 ((sortNet K).length * (12 * w + 12)) :=
    relax Hs2 le_rfl le_rfl (by apply Nat.mul_le_mul_left; omega)
  let A7 := A6 ∪ Bs2
  let nvalF : Fin K → Sig (n * 2 ^ (w + 1)) := fun j x => (sd x).next.val j
  have Hnval : Build A7 (Set.range nvalF) K := by
    have hltM : ∀ j : Fin K, j.val < sortM K := fun j =>
      lt_trans (by omega : j.val < 2 * K) (two_mul_K_lt_sortM hK1)
    have h := finG (A := A7) nvalF 1 (fun j =>
      notG (A := A7) (Or.inr (Or.inl (Or.inl ⟨j.val, hltM j, 0, Nat.zero_lt_one, rfl⟩))))
    exact relax h le_rfl le_rfl (by omega)
  have Hs01 := seq Hok Hcval
  have hsub2 : A2 ⊆ A ∪ (Bok ∪ Set.range cvalF) := stepSub le_rfl
  have Hs02 := seqS Hs01 Hncval hsub2
  have hsub3 := stepSub (B_new := Set.range ncvalF) hsub2
  have Hs03 := seqS Hs02 Hs1' hsub3
  have hsub4 := stepSub (B_new := Bs1) hsub3
  have Hs04 := seqS Hs03 Hrep hsub4
  have hsub5 := stepSub (B_new := Set.range repF) hsub4
  have Hs05 := seqS Hs04 Hnrep hsub5
  have hsub6 := stepSub (B_new := Set.range nrepF) hsub5
  have Hs06 := seqS Hs05 Hs2' hsub6
  have hsub7 := stepSub (B_new := Bs2) hsub6
  have Htot := seqS Hs06 Hnval hsub7
  refine relax Htot le_rfl ?_ ?_
  · rintro f ((((⟨u, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨t, ht, hft⟩) | ⟨j, rfl⟩) | ⟨j, k, rfl⟩)
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨u, rfl⟩))))))
    · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨i, hi⟩, rfl⟩)))
    · rcases hft with rfl | rfl | rfl | rfl
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr ⟨t, ht, Or.inl rfl⟩)))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr ⟨t, ht, Or.inr rfl⟩)))))
      · exact Or.inl (Or.inr (Or.inr ⟨t, ht, Or.inl rfl⟩))
      · exact Or.inl (Or.inr (Or.inr ⟨t, ht, Or.inr rfl⟩))
    · exact Or.inr ⟨j, rfl⟩
    · have hltM : j.val < sortM K := lt_trans (by omega : j.val < 2 * K) (two_mul_K_lt_sortM hK1)
      exact Or.inl (Or.inr (Or.inl (Or.inr ⟨j.val, hltM, k, rfl⟩)))
  · have hnl := sortNet_length_le hw hK1 hK_hi
    have hm4 := sortM_le_four_mul hK1
    have h1 : (sortNet K).length * (22 * w + 12) ≤ 6 * (n + 1) ^ 2 * K * (22 * (n + 1)) :=
      Nat.mul_le_mul hnl (by omega)
    have h2 : (sortNet K).length * (12 * w + 12) ≤ 6 * (n + 1) ^ 2 * K * (12 * (n + 1)) :=
      Nat.mul_le_mul hnl (by omega)
    have h3 : sortM K * (12 * w + 3) ≤ 4 * K * (12 * (n + 1)) := Nat.mul_le_mul hm4 (by omega)
    have h4 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow 2 (n + 1) (Nat.succ_pos n)
    have h5 : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow 3 (n + 1) (Nat.succ_pos n)
    have h3' : 4 * K * (12 * (n + 1)) ≤ 48 * (n + 1) ^ 3 * K := by
      calc 4 * K * (12 * (n + 1))
          = 48 * (n + 1) * K * 1 := by ring
        _ ≤ 48 * (n + 1) * K * (n + 1) ^ 2 := Nat.mul_le_mul_left _ h4
        _ = 48 * (n + 1) ^ 3 * K := by ring
    have hsmall : 2 * K + 2 * K + sortM K + K ≤ 9 * (n + 1) ^ 3 * K := by
      calc 2 * K + 2 * K + sortM K + K
          ≤ 9 * K := by omega
        _ = 9 * 1 * K := by ring
        _ ≤ 9 * (n + 1) ^ 3 * K := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h5)
    have h1' : 6 * (n + 1) ^ 2 * K * (22 * (n + 1)) = 132 * (n + 1) ^ 3 * K := by ring
    have h2' : 6 * (n + 1) ^ 2 * K * (12 * (n + 1)) = 72 * (n + 1) ^ 3 * K := by ring
    have hsum : 46656 * (n + 1) ^ 3 * K + 132 * (n + 1) ^ 3 * K + 72 * (n + 1) ^ 3 * K +
        48 * (n + 1) ^ 3 * K + 9 * (n + 1) ^ 3 * K ≤ 47000 * (n + 1) ^ 3 * K := by
      have heq : 46656 * (n + 1) ^ 3 * K + 132 * (n + 1) ^ 3 * K + 72 * (n + 1) ^ 3 * K +
          48 * (n + 1) ^ 3 * K + 9 * (n + 1) ^ 3 * K = 46917 * ((n + 1) ^ 3 * K) := by ring
      have hr : 47000 * (n + 1) ^ 3 * K = 47000 * ((n + 1) ^ 3 * K) := by ring
      rw [heq, hr]
      exact Nat.mul_le_mul_right _ (by omega)
    omega

theorem fwdAll_build {n w K : Nat} (hn : 0 < n) (hw : w ≤ n) (hK_lo : 2 ^ w ≤ K) (hK_hi : K ≤ 4 ^ w)
    {A : Set (Sig (n * 2 ^ (w + 1)))}
    (hinp : ∀ a : Fin (n * 2 ^ (w + 1)), (fun x => x a) ∈ A)
    (hfalse : (fun _ => false) ∈ A) (htrue : (fun _ => true) ∈ A) :
    have hK1 : 1 ≤ K := le_trans Nat.one_le_two_pow hK_lo
    ∀ m ≤ n - w,
      Build A
        ({f | ∃ h ≤ m, ∃ j : Fin K, f = fun x => (fwdState hn hK1 h x).val j} ∪
         {f | ∃ h ≤ m, ∃ (j : Fin K) (k : Fin (2 * w)), f = fun x => (fwdState hn hK1 h x).pair j k} ∪
         {f | ∃ h < m, ∃ u : Fin (2 * K), f = fun x => (stepAt hn hK1 h x).ok u} ∪
         {f | ∃ h < m, ∃ i < sortM K, f = fun x => (stepAt hn hK1 h x).isRep i} ∪
         {f | ∃ h < m, ∃ t < (sortNet K).length,
           f = (fun x => ((stepAt hn hK1 h x).sw1.getD t (0, 0, false)).2.2) ∨
           f = (fun x => !(((stepAt hn hK1 h x).sw1.getD t (0, 0, false)).2.2)) ∨
           f = (fun x => ((stepAt hn hK1 h x).sw2.getD t (0, 0, false)).2.2) ∨
           f = (fun x => !(((stepAt hn hK1 h x).sw2.getD t (0, 0, false)).2.2))})
        (m * (47000 * (n + 1) ^ 3 * K)) := by
  have hK1 : 1 ≤ K := le_trans Nat.one_le_two_pow hK_lo
  dsimp only
  intro m
  induction m with
  | zero =>
    intro _
    refine relax (idle ?_) le_rfl le_rfl (by simp)
    rintro f ((((⟨h, hh, j, rfl⟩ | ⟨h, hh, j, k, rfl⟩) | ⟨h, hh, _⟩) | ⟨h, hh, _⟩) | ⟨h, hh, _⟩)
    · have h0 : h = 0 := by omega
      subst h0
      simp only [fwdState, fwdInit]
      cases decide (j.val < 2 ^ w) <;> [exact hfalse; exact htrue]
    · have h0 : h = 0 := by omega
      subst h0
      simp only [fwdState, fwdInit]
      cases (if k.val < w then j.val.testBit k.val else j.val.testBit (k.val - w)) <;>
        [exact hfalse; exact htrue]
    · omega
    · omega
    · omega
  | succ m ih =>
    intro hm
    have Hprev := ih (by omega)
    let Bprev :=
      {f | ∃ h ≤ m, ∃ j : Fin K, f = fun x => (fwdState hn hK1 h x).val j} ∪
      {f | ∃ h ≤ m, ∃ (j : Fin K) (k : Fin (2 * w)), f = fun x => (fwdState hn hK1 h x).pair j k} ∪
      {f | ∃ h < m, ∃ u : Fin (2 * K), f = fun x => (stepAt hn hK1 h x).ok u} ∪
      {f | ∃ h < m, ∃ i < sortM K, f = fun x => (stepAt hn hK1 h x).isRep i} ∪
      {f | ∃ h < m, ∃ t < (sortNet K).length,
        f = (fun x => ((stepAt hn hK1 h x).sw1.getD t (0, 0, false)).2.2) ∨
        f = (fun x => !(((stepAt hn hK1 h x).sw1.getD t (0, 0, false)).2.2)) ∨
        f = (fun x => ((stepAt hn hK1 h x).sw2.getD t (0, 0, false)).2.2) ∨
        f = (fun x => !(((stepAt hn hK1 h x).sw2.getD t (0, 0, false)).2.2))}
    have Hstep := fwdStep_build hn hw hK_lo hK_hi (A := A ∪ Bprev) m (fwdState hn hK1 m)
      (fun j => Or.inr (Or.inl (Or.inl (Or.inl (Or.inl ⟨m, le_rfl, j, rfl⟩)))))
      (fun j k => Or.inr (Or.inl (Or.inl (Or.inl (Or.inr ⟨m, le_rfl, j, k, rfl⟩)))))
      (fun a => Or.inl (hinp a)) (Or.inl hfalse) (Or.inl htrue)
    refine relax (seq Hprev Hstep) le_rfl ?_ ?_
    · rintro f ((((⟨h, hh, j, rfl⟩ | ⟨h, hh, j, k, rfl⟩) | ⟨h, hh, u, rfl⟩) | ⟨h, hh, i, hi, rfl⟩) | ⟨h, hh, t, ht, hft⟩)
      · by_cases hhm : h ≤ m
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨h, hhm, j, rfl⟩))))
        · have heq : h = m + 1 := by omega
          subst heq; exact Or.inr (Or.inl (Or.inr ⟨j, rfl⟩))
      · by_cases hhm : h ≤ m
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨h, hhm, j, k, rfl⟩))))
        · have heq : h = m + 1 := by omega
          subst heq; exact Or.inr (Or.inr ⟨j, k, rfl⟩)
      · by_cases hhm : h < m
        · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨h, hhm, u, rfl⟩)))
        · have heq : h = m := by omega
          subst heq; exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl ⟨u, rfl⟩))))
      · by_cases hhm : h < m
        · exact Or.inl (Or.inl (Or.inr ⟨h, hhm, i, hi, rfl⟩))
        · have heq : h = m := by omega
          subst heq; exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr ⟨i, hi, rfl⟩))))
      · by_cases hhm : h < m
        · exact Or.inl (Or.inr ⟨h, hhm, t, ht, hft⟩)
        · have heq : h = m := by omega
          subst heq; exact Or.inr (Or.inl (Or.inl (Or.inr ⟨t, ht, hft⟩)))
    · rw [Nat.succ_mul m]

theorem term_build {n w K : Nat} (hn : 0 < n) (hw : w ≤ n) (hK_lo : 2 ^ w ≤ K) (hK_hi : K ≤ 4 ^ w)
    {A : Set (Sig (n * 2 ^ (w + 1)))}
    (hVal : ∀ j : Fin K, (fun x => (fwdState hn (le_trans Nat.one_le_two_pow hK_lo) (n - w) x).val j) ∈ A)
    (hPair : ∀ (j : Fin K) (k : Fin (2 * w)),
      (fun x => (fwdState hn (le_trans Nat.one_le_two_pow hK_lo) (n - w) x).pair j k) ∈ A)
    (hinp : ∀ a : Fin (n * 2 ^ (w + 1)), (fun x => x a) ∈ A)
    (hfalse : (fun _ => false) ∈ A) (htrue : (fun _ => true) ∈ A) :
    have hK1 : 1 ≤ K := le_trans Nat.one_le_two_pow hK_lo
    Build A
      ({f | ∃ j : Fin K, f = termBad hn hw hK1 j} ∪
       {f | ∃ (j : Fin K) (k : Fin (2 * w)), f = fun x => termMask hn hw hK1 j x k} ∪
       {outSig hn hw hK1})
      (w * (46656 * (n + 1) ^ 3 * K) + (2 * w ^ 2 + 4 * w + 4) * K) := by
  have hK1 : 1 ≤ K := le_trans Nat.one_le_two_pow hK_lo
  have Hwrap : Build A {f | ∃ (r : Fin w) (j : Fin K), f = wrapOk hn hw hK1 r j}
      (w * (46656 * (n + 1) ^ 3 * K)) := by
    have h1 := listBuildSet (List.finRange w)
      (fun r => {f | ∃ j : Fin K, f = wrapOk hn hw hK1 r j})
      (46656 * (n + 1) ^ 3 * K)
      (fun r _ => by
        let addr : Fin K → Fin (w + 1) → Sig (n * 2 ^ (w + 1)) := fun j bit x =>
          wrapPat n w (n - w + r.val) (by omega) (by omega) hw ((fwdState hn hK1 (n - w) x).pair j) bit
        have haddr : ∀ j bit, addr j bit ∈ A := by
          intro j bit; dsimp only [addr, wrapPat]; split_ifs <;> exact hPair j _
        have hlu := batchLookup hn (posOf hn (n - w + r.val)) addr haddr hinp
        have hcost := lookup_cost_le hn hw hK_lo hK_hi (by omega : K ≤ 2 * K)
        refine relax hlu le_rfl ?_ hcost
        rintro f ⟨j, rfl⟩; exact ⟨j, rfl⟩)
    rw [List.length_finRange] at h1
    refine relax h1 le_rfl ?_ le_rfl
    rintro f ⟨r, j, rfl⟩
    exact Set.mem_iUnion.mpr ⟨r, Set.mem_iUnion.mpr ⟨List.mem_finRange r, ⟨j, rfl⟩⟩⟩
  let A1 := A ∪ {f | ∃ (r : Fin w) (j : Fin K), f = wrapOk hn hw hK1 r j}
  have Hscan_j : ∀ j : Fin K, ∀ t ≤ w,
      Build A1
        ({fun x => (firstBadScan hn hw hK1 j x t).1} ∪
         {f | ∃ r < t, f = fun x => (firstBadScan hn hw hK1 j x t).2 r})
        (4 * t) := by
    intro j t
    induction t with
    | zero =>
      intro _
      refine relax (idle ?_) le_rfl le_rfl (by simp)
      rintro f (rfl | ⟨r, hr, _⟩)
      · exact Or.inl hfalse
      · omega
    | succ t ih =>
      intro ht
      have Hp := ih (by omega)
      let Bprev :=
        {fun x => (firstBadScan hn hw hK1 j x t).1} ∪
        {f | ∃ r < t, f = fun x => (firstBadScan hn hw hK1 j x t).2 r}
      let Ap := A1 ∪ Bprev
      have hbad : Build Ap {nt (wrapOk hn hw hK1 ⟨t, by omega⟩ j)} 1 :=
        notG (Or.inl (Or.inr ⟨⟨t, by omega⟩, j, rfl⟩))
      have hnf : Build (Ap ∪ {nt (wrapOk hn hw hK1 ⟨t, by omega⟩ j)})
          {nt (fun x => (firstBadScan hn hw hK1 j x t).1)} 1 :=
        notG (Or.inl (Or.inr (Or.inl rfl)))
      let badS := nt (wrapOk hn hw hK1 ⟨t, by omega⟩ j)
      let nfS := nt (fun x => (firstBadScan hn hw hK1 j x t).1)
      have hpick : Build (Ap ∪ ({badS} ∪ {nfS})) {an nfS badS} 1 :=
        andG (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl))
      have hfound : Build (Ap ∪ (({badS} ∪ {nfS}) ∪ {an nfS badS}))
          {or (fun x => (firstBadScan hn hw hK1 j x t).1) badS} 1 :=
        orG (Or.inl (Or.inr (Or.inl rfl))) (Or.inr (Or.inl (Or.inl rfl)))
      have hstep := seq (seq (seq hbad hnf) hpick) hfound
      refine relax (seq Hp hstep) le_rfl ?_ (by omega)
      rintro f (rfl | ⟨r, hr, rfl⟩)
      · right; right
        have he : (fun x => (firstBadScan hn hw hK1 j x (t + 1)).1) =
            Build220.or (fun x => (firstBadScan hn hw hK1 j x t).1) badS := by
          funext x; simp [firstBadScan, show t < w by omega, Build220.or, badS, nt]
        rw [he]; rfl
      · by_cases hrt : r = t
        · subst hrt
          right; left; right
          have he : (fun x => (firstBadScan hn hw hK1 j x (r + 1)).2 r) = an nfS badS := by
            funext x; simp [firstBadScan, show r < w by omega, an, nfS, badS, nt]
          rw [he]; rfl
        · left; right
          refine ⟨r, by omega, ?_⟩
          funext x; simp [firstBadScan, hrt]
  have Hscan : Build A1
      ({f | ∃ j : Fin K, f = termBad hn hw hK1 j} ∪
       {f | ∃ (j : Fin K) (r : Fin w), f = termPick hn hw hK1 j r})
      (K * (4 * w)) := by
    have h := listBuildSet (List.finRange K)
      (fun j => {fun x => (firstBadScan hn hw hK1 j x w).1} ∪
        {f | ∃ r < w, f = fun x => (firstBadScan hn hw hK1 j x w).2 r})
      (4 * w) (fun j _ => Hscan_j j w le_rfl)
    rw [List.length_finRange] at h
    refine relax h le_rfl ?_ le_rfl
    rintro f (⟨j, rfl⟩ | ⟨j, r, rfl⟩)
    · exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨List.mem_finRange j, Or.inl rfl⟩⟩
    · exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨List.mem_finRange j, Or.inr ⟨r.val, r.isLt, rfl⟩⟩⟩
  let A2 := A1 ∪ ({f | ∃ j : Fin K, f = termBad hn hw hK1 j} ∪
    {f | ∃ (j : Fin K) (r : Fin w), f = termPick hn hw hK1 j r})
  have Hmask : Build A2
      {f | ∃ (j : Fin K) (k : Fin (2 * w)), f = fun x => termMask hn hw hK1 j x k}
      (K * (2 * w * w)) := by
    have h := listBuildSet (List.finRange K)
      (fun j => {f | ∃ k : Fin (2 * w), f = fun x => termMask hn hw hK1 j x k})
      (2 * w * w)
      (fun j _ => by
        have hk := finG (A := A2) (fun k : Fin (2 * w) => fun x => termMask hn hw hK1 j x k) w (fun k => by
          let rs := (List.finRange w).filter (fun r => wrapUses n w r.val k)
          have hl := orListG (A := A2) (rs.map (fun r => termPick hn hw hK1 j r))
            (fun f hf => by rcases List.mem_map.mp hf with ⟨r, _, rfl⟩; exact Or.inr (Or.inr ⟨j, r, rfl⟩))
            (Or.inl (Or.inl hfalse))
          have hlen : (rs.map (fun r => termPick hn hw hK1 j r)).length ≤ w := by
            rw [List.length_map]
            exact (List.length_filter_le _ _).trans (by simp)
          have he : (fun x => (rs.map (fun r => termPick hn hw hK1 j r)).any (fun f => f x)) =
              (fun x => termMask hn hw hK1 j x k) := by
            funext x; simp [termMask, rs, List.any_map]
          rw [he] at hl
          exact relax hl le_rfl le_rfl hlen)
        refine relax hk le_rfl ?_ le_rfl
        rintro f ⟨k, rfl⟩; exact ⟨k, rfl⟩)
    rw [List.length_finRange] at h
    refine relax h le_rfl ?_ le_rfl
    rintro f ⟨j, k, rfl⟩
    exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨List.mem_finRange j, ⟨k, rfl⟩⟩⟩
  let A3 := A2 ∪ {f | ∃ (j : Fin K) (k : Fin (2 * w)), f = fun x => termMask hn hw hK1 j x k}
  let okJ : Fin K → Sig (n * 2 ^ (w + 1)) :=
    fun j x => !((fwdState hn hK1 (n - w) x).val j) || termBad hn hw hK1 j x
  have HokJ : Build A3 (Set.range okJ) (K * 2) := finG (A := A3) okJ 2 (fun j => by
    have h1 := notG (A := A3) (Or.inl (Or.inl (Or.inl (hVal j))))
    have h2 := orG (A := A3 ∪ {nt (fun x => (fwdState hn hK1 (n - w) x).val j)})
      (Or.inr rfl) (Or.inl (Or.inl (Or.inr (Or.inl ⟨j, rfl⟩))))
    exact relax (seq h1 h2) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl)
  have Hout : Build (A3 ∪ Set.range okJ) {outSig hn hw hK1} K := by
    have h := andListG (A := A3 ∪ Set.range okJ) ((List.finRange K).map okJ)
      (fun f hf => by rcases List.mem_map.mp hf with ⟨j, _, rfl⟩; exact Or.inr ⟨j, rfl⟩)
      (Or.inl (Or.inl (Or.inl (Or.inl htrue))))
    have he : (fun x => ((List.finRange K).map okJ).all (fun f => f x)) = outSig hn hw hK1 := by
      funext x; simp [outSig, okJ, List.all_map, Function.comp_def]
    rw [he] at h
    exact relax h le_rfl le_rfl (by simp)
  have Hws1 := seq Hwrap Hscan
  have hsub2 := stepSub (B_new := {f | ∃ j : Fin K, f = termBad hn hw hK1 j} ∪
    {f | ∃ (j : Fin K) (r : Fin w), f = termPick hn hw hK1 j r}) (le_refl A1)
  have Hws2 := seqS Hws1 Hmask hsub2
  have hsub3 := stepSub (B_new := {f | ∃ (j : Fin K) (k : Fin (2 * w)), f = fun x => termMask hn hw hK1 j x k}) hsub2
  have Hws3 := seqS Hws2 HokJ hsub3
  have hsub4 := stepSub (B_new := Set.range okJ) hsub3
  have Htot := seqS Hws3 Hout hsub4
  refine relax Htot le_rfl ?_ ?_
  · rintro f ((⟨j, rfl⟩ | ⟨j, k, rfl⟩) | rfl)
    · exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl ⟨j, rfl⟩))))
    · exact Or.inl (Or.inl (Or.inr ⟨j, k, rfl⟩))
    · exact Or.inr rfl
  · have heq : K * (4 * w) + K * (2 * w * w) + K * 2 + K ≤ (2 * w ^ 2 + 4 * w + 4) * K := by
      have h1 : K * (4 * w) + K * (2 * w * w) + K * 2 + K = (2 * w ^ 2 + 4 * w + 3) * K := by ring
      rw [h1]
      exact Nat.mul_le_mul_right K (by omega)
    omega

theorem bwdStep_build {n w K : Nat} (hn : 0 < n) (hw : w ≤ n) (hK_lo : 2 ^ w ≤ K) (hK_hi : K ≤ 4 ^ w)
    {A : Set (Sig (n * 2 ^ (w + 1)))} (h : Nat)
    (mNext : (Fin (n * 2 ^ (w + 1)) → Bool) → Fin K → Fin (2 * w) → Bool)
    (hM : ∀ (j : Fin K) (k : Fin (2 * w)), (fun x => mNext x j k) ∈ A)
    (hOk : ∀ u : Fin (2 * K), (fun x => (stepAt hn (le_trans Nat.one_le_two_pow hK_lo) h x).ok u) ∈ A)
    (hRep : ∀ i < sortM K, (fun x => (stepAt hn (le_trans Nat.one_le_two_pow hK_lo) h x).isRep i) ∈ A)
    (hSw1 : ∀ t < (sortNet K).length,
      (fun x => ((stepAt hn (le_trans Nat.one_le_two_pow hK_lo) h x).sw1.getD t (0, 0, false)).2.2) ∈ A ∧
      (fun x => !(((stepAt hn (le_trans Nat.one_le_two_pow hK_lo) h x).sw1.getD t (0, 0, false)).2.2)) ∈ A)
    (hSw2 : ∀ t < (sortNet K).length,
      (fun x => ((stepAt hn (le_trans Nat.one_le_two_pow hK_lo) h x).sw2.getD t (0, 0, false)).2.2) ∈ A ∧
      (fun x => !(((stepAt hn (le_trans Nat.one_le_two_pow hK_lo) h x).sw2.getD t (0, 0, false)).2.2)) ∈ A)
    (hfalse : (fun _ => false) ∈ A) :
    have hK1 : 1 ≤ K := le_trans Nat.one_le_two_pow hK_lo
    let bd := fun x => runBwdStep hn hK1 h (mNext x) x
    Build A
      ({f | ∃ j : Fin K, f = fun x => (bd x).hasPos j} ∪
       {f | ∃ j : Fin K, f = fun x => (bd x).hasNeg j} ∪
       {f | ∃ (j : Fin K) (k : Fin (2 * w)), f = fun x => (bd x).mask j k})
      (200 * (n + 1) ^ 3 * K) := by
  have hK1 : 1 ≤ K := le_trans Nat.one_le_two_pow hK_lo
  dsimp only
  let bd := fun x => runBwdStep hn hK1 h (mNext x) x
  let L := (sortNet K).length
  have hnet_mem : ∀ c ∈ sortNet K, c.1 < sortM K ∧ c.2.1 < sortM K := by
    intro c hc; have hm := bitonicSort_mem 0 (sortDeg K) true c hc; unfold sortM; omega
  have hrev_props : ∀ (sws : (Fin (n * 2 ^ (w + 1)) → Bool) → List (Nat × Nat × Bool)),
      (∀ x, (sws x).length = L) →
      (∀ t < L, ∀ x, ((sws x).getD t (0, 0, false)).1 = ((sortNet K).getD t (0, 0, false)).1 ∧
        ((sws x).getD t (0, 0, false)).2.1 = ((sortNet K).getD t (0, 0, false)).2.1) →
      (∀ t < L, (fun x => ((sws x).getD t (0, 0, false)).2.2) ∈ A ∧
        (fun x => !(((sws x).getD t (0, 0, false)).2.2)) ∈ A) →
      (∀ x, (sws x).reverse.length = L) ∧
      (∀ t < L, ∃ u v, u < sortM K ∧ v < sortM K ∧
        ∀ x, ((sws x).reverse.getD t (0, 0, false)).1 = u ∧
          ((sws x).reverse.getD t (0, 0, false)).2.1 = v) ∧
      (∀ t < L, (fun x => ((sws x).reverse.getD t (0, 0, false)).2.2) ∈ A ∧
        (fun x => !(((sws x).reverse.getD t (0, 0, false)).2.2)) ∈ A) := by
    intro sws hlen hidx hmem
    have hget_rev : ∀ t < L, ∀ x, (sws x).reverse.getD t (0, 0, false) = (sws x).getD (L - 1 - t) (0, 0, false) := by
      intro t ht x
      have hl : (sws x).length = L := hlen x
      rw [List.getD_eq_getElem _ _ (by simp [hl, ht]),
          List.getD_eq_getElem _ _ (by omega),
          List.getElem_reverse]
      congr 1; omega
    refine ⟨fun x => by simp [hlen x], ?_, ?_⟩
    · intro t ht
      let t' := L - 1 - t
      have ht' : t' < L := by omega
      have hc := hnet_mem ((sortNet K).getD t' (0, 0, false))
        (by rw [List.getD_eq_getElem _ _ ht']; exact List.getElem_mem _)
      refine ⟨((sortNet K).getD t' (0, 0, false)).1, ((sortNet K).getD t' (0, 0, false)).2.1,
        hc.1, hc.2, fun x => ?_⟩
      rw [hget_rev t ht x]
      exact hidx t' ht' x
    · intro t ht
      let t' := L - 1 - t
      have ht' : t' < L := by omega
      have hm := hmem t' ht'
      constructor
      · have he : (fun x => ((sws x).reverse.getD t (0, 0, false)).2.2) =
            (fun x => ((sws x).getD t' (0, 0, false)).2.2) := by funext x; rw [hget_rev t ht x]
        rw [he]; exact hm.1
      · have he : (fun x => !(((sws x).reverse.getD t (0, 0, false)).2.2)) =
            (fun x => !(((sws x).getD t' (0, 0, false)).2.2)) := by funext x; rw [hget_rev t ht x]
        rw [he]; exact hm.2
  have hp2 := hrev_props (fun x => (stepAt hn hK1 h x).sw2)
    (fun x => netSwaps_length _ _ _) (fun t ht x => netSwaps_getD_idx _ _ _ t ht) hSw2
  have hp1 := hrev_props (fun x => (stepAt hn hK1 h x).sw1)
    (fun x => netSwaps_length _ _ _) (fun t ht x => netSwaps_getD_idx _ _ _ t ht) hSw1
  let u2 : (Fin (n * 2 ^ (w + 1)) → Bool) → Nat → Fin (2 * w) → Bool :=
    fun x i => if hi : i < K then mNext x ⟨i, hi⟩ else fun _ => false
  have hu2 : ∀ idx < sortM K, ∀ k : Fin (2 * w), (fun x => u2 x idx k) ∈ A := by
    intro idx _ k; dsimp only [u2]; split_ifs with hi
    · exact hM ⟨idx, hi⟩ k
    · exact hfalse
  have Hrev2 := replayCircuit (sortM K) (fun x => (stepAt hn hK1 h x).sw2.reverse) L
    hp2.1 hp2.2.1 hp2.2.2 u2 hu2
  let A1 := A ∪ {f | ∃ idx < sortM K, ∃ k : Fin (2 * w), f = fun x => (bd x).rev2 idx k}
  have Hcopy := copyScan_circuit (A := A1) (sortM K)
    (fun x => (stepAt hn hK1 h x).isRep) (fun x => (bd x).rev2)
    (fun i hi => Or.inl (hRep i hi)) (fun i hi k => Or.inr ⟨i, hi, k, rfl⟩)
    (Or.inl hfalse) (sortM K) le_rfl
  let Bcopy :=
    {f | ∃ j : Fin (2 * w), f = fun x => (copyScan (stepAt hn hK1 h x).isRep (bd x).rev2 (sortM K)).1 j} ∪
    {f | ∃ idx < sortM K, ∃ j : Fin (2 * w), f = fun x => (bd x).copied idx j}
  let A2 := A1 ∪ Bcopy
  have Hrev1 := replayCircuit (A := A2) (sortM K) (fun x => (stepAt hn hK1 h x).sw1.reverse) L
    hp1.1 hp1.2.1
    (fun t ht => ⟨Or.inl (Or.inl (hp1.2.2 t ht).1), Or.inl (Or.inl (hp1.2.2 t ht).2)⟩)
    (fun x => (bd x).copied)
    (fun i hi k => Or.inr (Or.inr ⟨i, hi, k, rfl⟩))
  let A3 := A2 ∪ {f | ∃ idx < sortM K, ∃ k : Fin (2 * w), f = fun x => (bd x).rev1 idx k}
  have hrev1_mem : ∀ j : Fin K, ∀ b : Nat, b < 2 → ∀ k : Fin (2 * w),
      (fun x => (bd x).rev1 (2 * j.val + b) k) ∈ A3 := by
    intro j b hb k
    have hlt : 2 * j.val + b < sortM K := lt_trans (by omega : 2 * j.val + b < 2 * K) (two_mul_K_lt_sortM hK1)
    exact Or.inr ⟨2 * j.val + b, hlt, k, rfl⟩
  have Hcomb : Build A3
      ({f | ∃ j : Fin K, f = fun x => (bd x).hasPos j} ∪
       {f | ∃ j : Fin K, f = fun x => (bd x).hasNeg j} ∪
       {f | ∃ (j : Fin K) (k : Fin (2 * w)), f = fun x => (bd x).mask j k})
      (K * (10 * w + 6)) := by
    have h := listBuildSet (List.finRange K)
      (fun j => {fun x => (bd x).hasPos j} ∪ {fun x => (bd x).hasNeg j} ∪
        {f | ∃ k : Fin (2 * w), f = fun x => (bd x).mask j k})
      (10 * w + 6)
      (fun j _ => by
        let ok0 : Sig (n * 2 ^ (w + 1)) := fun x => (stepAt hn hK1 h x).ok ⟨2 * j.val, by omega⟩
        let ok1 : Sig (n * 2 ^ (w + 1)) := fun x => (stepAt hn hK1 h x).ok ⟨2 * j.val + 1, by omega⟩
        have hok0 : ok0 ∈ A3 := Or.inl (Or.inl (Or.inl (hOk ⟨2 * j.val, by omega⟩)))
        have hok1 : ok1 ∈ A3 := Or.inl (Or.inl (Or.inl (hOk ⟨2 * j.val + 1, by omega⟩)))
        have Hn0 : Build A3 {nt ok0} 1 := notG hok0
        have Hn1 : Build (A3 ∪ {nt ok0}) {nt ok1} 1 := notG (Or.inl hok1)
        let A3a := A3 ∪ ({nt ok0} ∪ {nt ok1})
        have Hhp : Build A3a {fun x => (bd x).hasPos j} 1 := by
          by_cases hw0 : 0 < w
          · have he : (fun x => (bd x).hasPos j) =
                Build220.or (nt ok0) (fun x => (bd x).rev1 (2 * j.val) ⟨2 * w - 1, by omega⟩) := by
              funext x; simp [bd, runBwdStep, hw0, Build220.or, nt, ok0]
            rw [he]
            exact orG (A := A3a) (Or.inr (Or.inl rfl)) (Or.inl (by simpa using hrev1_mem j 0 (by omega) ⟨2 * w - 1, by omega⟩))
          · have he : (fun x => (bd x).hasPos j) = nt ok0 := by
              funext x; simp [bd, runBwdStep, hw0, nt, ok0]
            rw [he]; exact relax (idle (Set.singleton_subset_iff.mpr (Or.inr (Or.inl rfl)))) le_rfl le_rfl (by omega)
        have Hhn : Build (A3a ∪ {fun x => (bd x).hasPos j}) {fun x => (bd x).hasNeg j} 1 := by
          by_cases hw0 : 0 < w
          · have he : (fun x => (bd x).hasNeg j) =
                Build220.or (nt ok1) (fun x => (bd x).rev1 (2 * j.val + 1) ⟨2 * w - 1, by omega⟩) := by
              funext x; simp [bd, runBwdStep, hw0, Build220.or, nt, ok1]
            rw [he]
            exact orG (A := A3a ∪ {fun x => (bd x).hasPos j}) (Or.inl (Or.inr (Or.inr rfl))) (Or.inl (Or.inl (hrev1_mem j 1 (by omega) ⟨2 * w - 1, by omega⟩)))
          · have he : (fun x => (bd x).hasNeg j) = nt ok1 := by
              funext x; simp [bd, runBwdStep, hw0, nt, ok1]
            rw [he]; exact relax (idle (Set.singleton_subset_iff.mpr (Or.inl (Or.inr (Or.inr rfl))))) le_rfl le_rfl (by omega)
        let A3b := A3a ∪ ({fun x => (bd x).hasPos j} ∪ {fun x => (bd x).hasNeg j})
        let nhp : Sig (n * 2 ^ (w + 1)) := nt (fun x => (bd x).hasPos j)
        have Hnhp : Build A3b {nhp} 1 := notG (A := A3b) (Or.inr (Or.inl rfl))
        let c0 : Sig (n * 2 ^ (w + 1)) := Build220.or nhp (fun x => (bd x).hasNeg j)
        have Hc0 : Build (A3b ∪ {nhp}) {c0} 1 := orG (A := A3b ∪ {nhp}) (Or.inr rfl) (Or.inl (Or.inr (Or.inr rfl)))
        let A3c := A3b ∪ ({nhp} ∪ {c0})
        have Hbm0 : Build A3c (Set.range (fun k : Fin (2 * w) => fun x => (bd x).bm0 j k)) (2 * w) := by
          have hb := finG (A := A3c) (fun k : Fin (2 * w) => fun x => (bd x).bm0 j k) 1 (fun k => by
            by_cases hk1 : k.val < w
            · have he : (fun x => (bd x).bm0 j k) = an ok0 (fun x => (bd x).rev1 (2 * j.val) k) := by
                funext x; simp [bd, runBwdStep, hk1, an, ok0]
              rw [he]
              exact andG (A := A3c) (Or.inl (Or.inl (Or.inl hok0)))
                (Or.inl (Or.inl (Or.inl (by simpa using hrev1_mem j 0 (by omega) k))))
            · by_cases hk2 : k.val = w
              · have he : (fun x => (bd x).bm0 j k) = nt ok0 := by
                  funext x; simp [bd, runBwdStep, hk1, hk2, nt, ok0]
                rw [he]
                exact relax (idle (A := A3c) (Set.singleton_subset_iff.mpr (Or.inl (Or.inl (Or.inr (Or.inl rfl)))))) le_rfl le_rfl (by omega)
              · have he : (fun x => (bd x).bm0 j k) =
                    Build220.or (nt ok0) (fun x => (bd x).rev1 (2 * j.val) ⟨k.val - 1, by omega⟩) := by
                  funext x; simp [bd, runBwdStep, hk1, hk2, Build220.or, nt, ok0]
                rw [he]
                exact orG (A := A3c) (Or.inl (Or.inl (Or.inr (Or.inl rfl))))
                  (Or.inl (Or.inl (Or.inl (by simpa using hrev1_mem j 0 (by omega) ⟨k.val - 1, by omega⟩)))))
          exact relax hb le_rfl le_rfl (by omega)
        let A3d := A3c ∪ Set.range (fun k : Fin (2 * w) => fun x => (bd x).bm0 j k)
        have Hbm1 : Build A3d (Set.range (fun k : Fin (2 * w) => fun x => (bd x).bm1 j k)) (2 * w) := by
          have hb := finG (A := A3d) (fun k : Fin (2 * w) => fun x => (bd x).bm1 j k) 1 (fun k => by
            by_cases hk1 : k.val < w
            · have he : (fun x => (bd x).bm1 j k) = an ok1 (fun x => (bd x).rev1 (2 * j.val + 1) k) := by
                funext x; simp [bd, runBwdStep, hk1, an, ok1]
              rw [he]
              exact andG (A := A3d) (Or.inl (Or.inl (Or.inl (Or.inl hok1))))
                (Or.inl (Or.inl (Or.inl (Or.inl (hrev1_mem j 1 (by omega) k)))))
            · by_cases hk2 : k.val = w
              · have he : (fun x => (bd x).bm1 j k) = nt ok1 := by
                  funext x; simp [bd, runBwdStep, hk1, hk2, nt, ok1]
                rw [he]
                exact relax (idle (A := A3d) (Set.singleton_subset_iff.mpr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr rfl))))))) le_rfl le_rfl (by omega)
              · have he : (fun x => (bd x).bm1 j k) =
                    Build220.or (nt ok1) (fun x => (bd x).rev1 (2 * j.val + 1) ⟨k.val - 1, by omega⟩) := by
                  funext x; simp [bd, runBwdStep, hk1, hk2, Build220.or, nt, ok1]
                rw [he]
                exact orG (A := A3d) (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr rfl)))))
                  (Or.inl (Or.inl (Or.inl (Or.inl (hrev1_mem j 1 (by omega) ⟨k.val - 1, by omega⟩))))))
          exact relax hb le_rfl le_rfl (by omega)
        let A3e := A3d ∪ Set.range (fun k : Fin (2 * w) => fun x => (bd x).bm1 j k)
        have Hmsk : Build A3e (Set.range (fun k : Fin (2 * w) => fun x => (bd x).mask j k)) (2 * w * 3) :=
          finG (A := A3e) (fun k : Fin (2 * w) => fun x => (bd x).mask j k) 3 (fun k =>
            combMaskG (A := A3e)
              (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl rfl)))))
              (Or.inl (Or.inl (Or.inr (Or.inr rfl))))
              (Or.inl (Or.inr ⟨k, rfl⟩))
              (Or.inr ⟨k, rfl⟩)
              (fun x => (bd x).hasNeg j) (fun _ => rfl))
        have Hpre1 := seq (seq Hn0 Hn1) (seq Hhp Hhn)
        have hsb := stepSub (B_new := {fun x => (bd x).hasPos j} ∪ {fun x => (bd x).hasNeg j}) (le_refl A3a)
        have Hpre2 := seqS Hpre1 (seq Hnhp Hc0) hsb
        have hsc := stepSub (B_new := {nhp} ∪ {c0}) hsb
        have Hpre3 := seqS Hpre2 Hbm0 hsc
        have hsd := stepSub (B_new := Set.range (fun k : Fin (2 * w) => fun x => (bd x).bm0 j k)) hsc
        have Hpre4 := seqS Hpre3 Hbm1 hsd
        have hse := stepSub (B_new := Set.range (fun k : Fin (2 * w) => fun x => (bd x).bm1 j k)) hsd
        have Htot_j := seqS Hpre4 Hmsk hse
        refine relax Htot_j le_rfl ?_ (by omega)
        rintro f ((rfl | rfl) | ⟨k, rfl⟩)
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl rfl)))))
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr rfl)))))
        · exact Or.inr ⟨k, rfl⟩)
    rw [List.length_finRange] at h
    refine relax h le_rfl ?_ le_rfl
    rintro f ((⟨j, rfl⟩ | ⟨j, rfl⟩) | ⟨j, k, rfl⟩)
    · exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨List.mem_finRange j, Or.inl (Or.inl rfl)⟩⟩
    · exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨List.mem_finRange j, Or.inl (Or.inr rfl)⟩⟩
    · exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨List.mem_finRange j, Or.inr ⟨k, rfl⟩⟩⟩
  have Hr1 := seq Hrev2 Hcopy
  have hs2 := stepSub (B_new := Bcopy) (le_refl A1)
  have Hr2 := seqS Hr1 Hrev1 hs2
  have hs3 := stepSub (B_new := {f | ∃ idx < sortM K, ∃ k : Fin (2 * w), f = fun x => (bd x).rev1 idx k}) hs2
  have Htot := seqS Hr2 Hcomb hs3
  refine relax Htot le_rfl ?_ ?_
  · exact Set.subset_union_right
  · have hnl := sortNet_length_le hw hK1 hK_hi
    have hm4 := sortM_le_four_mul hK1
    have h4 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow 2 (n + 1) (Nat.succ_pos n)
    have hL1 : L * (6 * (2 * w)) ≤ 72 * (n + 1) ^ 3 * K := by
      calc L * (6 * (2 * w))
          ≤ (6 * (n + 1) ^ 2 * K) * (12 * (n + 1)) := Nat.mul_le_mul hnl (by omega)
        _ = 72 * (n + 1) ^ 3 * K := by ring
    have hC1 : sortM K * (3 * (2 * w) + 1) ≤ 28 * (n + 1) ^ 3 * K := by
      calc sortM K * (3 * (2 * w) + 1)
          ≤ (4 * K) * (7 * (n + 1)) := Nat.mul_le_mul hm4 (by omega)
        _ = 28 * (n + 1) * K * 1 := by ring
        _ ≤ 28 * (n + 1) * K * (n + 1) ^ 2 := Nat.mul_le_mul_left _ h4
        _ = 28 * (n + 1) ^ 3 * K := by ring
    have hK2 : K * (10 * w + 6) ≤ 16 * (n + 1) ^ 3 * K := by
      calc K * (10 * w + 6)
          ≤ K * (16 * (n + 1)) := Nat.mul_le_mul_left _ (by omega)
        _ = 16 * (n + 1) * K * 1 := by ring
        _ ≤ 16 * (n + 1) * K * (n + 1) ^ 2 := Nat.mul_le_mul_left _ h4
        _ = 16 * (n + 1) ^ 3 * K := by ring
    have hsum : 72 * (n + 1) ^ 3 * K + 28 * (n + 1) ^ 3 * K + 72 * (n + 1) ^ 3 * K +
        16 * (n + 1) ^ 3 * K ≤ 200 * (n + 1) ^ 3 * K := by
      have heq : 72 * (n + 1) ^ 3 * K + 28 * (n + 1) ^ 3 * K + 72 * (n + 1) ^ 3 * K +
          16 * (n + 1) ^ 3 * K = 188 * ((n + 1) ^ 3 * K) := by ring
      have hr : 200 * (n + 1) ^ 3 * K = 200 * ((n + 1) ^ 3 * K) := by ring
      rw [heq, hr]
      exact Nat.mul_le_mul_right _ (by omega)
    omega

theorem bwdAll_build {n w K : Nat} (hn : 0 < n) (hw : w ≤ n) (hK_lo : 2 ^ w ≤ K) (hK_hi : K ≤ 4 ^ w)
    {A : Set (Sig (n * 2 ^ (w + 1)))}
    (hTerm : ∀ (j : Fin K) (k : Fin (2 * w)),
      (fun x => termMask hn hw (le_trans Nat.one_le_two_pow hK_lo) j x k) ∈ A)
    (hOk : ∀ h < n - w, ∀ u : Fin (2 * K),
      (fun x => (stepAt hn (le_trans Nat.one_le_two_pow hK_lo) h x).ok u) ∈ A)
    (hRep : ∀ h < n - w, ∀ i < sortM K,
      (fun x => (stepAt hn (le_trans Nat.one_le_two_pow hK_lo) h x).isRep i) ∈ A)
    (hSw1 : ∀ h < n - w, ∀ t < (sortNet K).length,
      (fun x => ((stepAt hn (le_trans Nat.one_le_two_pow hK_lo) h x).sw1.getD t (0, 0, false)).2.2) ∈ A ∧
      (fun x => !(((stepAt hn (le_trans Nat.one_le_two_pow hK_lo) h x).sw1.getD t (0, 0, false)).2.2)) ∈ A)
    (hSw2 : ∀ h < n - w, ∀ t < (sortNet K).length,
      (fun x => ((stepAt hn (le_trans Nat.one_le_two_pow hK_lo) h x).sw2.getD t (0, 0, false)).2.2) ∈ A ∧
      (fun x => !(((stepAt hn (le_trans Nat.one_le_two_pow hK_lo) h x).sw2.getD t (0, 0, false)).2.2)) ∈ A)
    (hfalse : (fun _ => false) ∈ A) :
    have hK1 : 1 ≤ K := le_trans Nat.one_le_two_pow hK_lo
    ∀ m ≤ n - w,
      Build A
        ({f | ∃ rem ≤ m, ∃ (j : Fin K) (k : Fin (2 * w)), f = fun x => bwdMaskRem hn hw hK1 rem x j k} ∪
         {f | ∃ rem < m, ∃ j : Fin K, f = fun x => (bwdStepAt hn hw hK1 (n - w - (rem + 1)) x).hasPos j} ∪
         {f | ∃ rem < m, ∃ j : Fin K, f = fun x => (bwdStepAt hn hw hK1 (n - w - (rem + 1)) x).hasNeg j})
        (m * (200 * (n + 1) ^ 3 * K)) := by
  have hK1 : 1 ≤ K := le_trans Nat.one_le_two_pow hK_lo
  dsimp only
  intro m
  induction m with
  | zero =>
    intro _
    refine relax (idle ?_) le_rfl le_rfl (by simp)
    rintro f ((⟨rem, hrem, j, k, rfl⟩ | ⟨rem, hrem, _⟩) | ⟨rem, hrem, _⟩)
    · have h0 : rem = 0 := by omega
      subst h0; exact hTerm j k
    · omega
    · omega
  | succ m ih =>
    intro hm
    have Hprev := ih (by omega)
    let Bprev :=
      {f | ∃ rem ≤ m, ∃ (j : Fin K) (k : Fin (2 * w)), f = fun x => bwdMaskRem hn hw hK1 rem x j k} ∪
      {f | ∃ rem < m, ∃ j : Fin K, f = fun x => (bwdStepAt hn hw hK1 (n - w - (rem + 1)) x).hasPos j} ∪
      {f | ∃ rem < m, ∃ j : Fin K, f = fun x => (bwdStepAt hn hw hK1 (n - w - (rem + 1)) x).hasNeg j}
    let h := n - w - (m + 1)
    have hh : h < n - w := by dsimp [h]; omega
    have Hstep := bwdStep_build hn hw hK_lo hK_hi (A := A ∪ Bprev) h
      (bwdMaskRem hn hw hK1 m)
      (fun j k => Or.inr (Or.inl (Or.inl ⟨m, le_rfl, j, k, rfl⟩)))
      (fun u => Or.inl (hOk h hh u))
      (fun i hi => Or.inl (hRep h hh i hi))
      (fun t ht => ⟨Or.inl (hSw1 h hh t ht).1, Or.inl (hSw1 h hh t ht).2⟩)
      (fun t ht => ⟨Or.inl (hSw2 h hh t ht).1, Or.inl (hSw2 h hh t ht).2⟩)
      (Or.inl hfalse)
    have hrem_eq : n - w - (h + 1) = m := by dsimp [h]; omega
    refine relax (seq Hprev Hstep) le_rfl ?_ ?_
    · rintro f ((⟨rem, hrem, j, k, rfl⟩ | ⟨rem, hrem, j, rfl⟩) | ⟨rem, hrem, j, rfl⟩)
      · by_cases hrm : rem ≤ m
        · exact Or.inl (Or.inl (Or.inl ⟨rem, hrm, j, k, rfl⟩))
        · have heq : rem = m + 1 := by omega
          subst heq; exact Or.inr (Or.inr ⟨j, k, rfl⟩)
      · by_cases hrm : rem < m
        · exact Or.inl (Or.inl (Or.inr ⟨rem, hrm, j, rfl⟩))
        · have heq : rem = m := by omega
          subst heq
          refine Or.inr (Or.inl (Or.inl ⟨j, ?_⟩))
          funext x; simp [bwdStepAt, h, hrem_eq]
      · by_cases hrm : rem < m
        · exact Or.inl (Or.inr ⟨rem, hrm, j, rfl⟩)
        · have heq : rem = m := by omega
          subst heq
          refine Or.inr (Or.inl (Or.inr ⟨j, ?_⟩))
          funext x; simp [bwdStepAt, h, hrem_eq]
    · rw [Nat.succ_mul m]

theorem seed_build {n w K : Nat} (hn : 0 < n) (hw : w ≤ n) (hK_lo : 2 ^ w ≤ K)
    {A : Set (Sig (n * 2 ^ (w + 1)))}
    (hB0 : ∀ (j : Fin K) (k : Fin (2 * w)),
      (fun x => bwdMaskRem hn hw (le_trans Nat.one_le_two_pow hK_lo) (n - w) x j k) ∈ A)
    (hfalse : (fun _ => false) ∈ A) :
    have hK1 : 1 ≤ K := le_trans Nat.one_le_two_pow hK_lo
    ∀ m ≤ w,
      Build A
        ({f | ∃ rem ≤ m, ∃ p < 2 ^ (w - rem), ∃ a : Fin w,
            f = fun x => seedMaskRem hn hw hK_lo hK1 rem x p a} ∪
         {f | ∃ d < w, w - m ≤ d ∧ ∃ p < 2 ^ d, ∃ hd : d < w,
            f = seedEn hn hw hK_lo hK1 d p hd})
        (w * 2 ^ w + (2 ^ w - 2 ^ (w - m)) * (3 * w + 3)) := by
  have hK1 : 1 ≤ K := le_trans Nat.one_le_two_pow hK_lo
  dsimp only
  intro m
  induction m with
  | zero =>
    intro _
    have Hbase : Build A
        {f | ∃ p < 2 ^ w, ∃ a : Fin w, f = fun x => seedMaskRem hn hw hK_lo hK1 0 x p a}
        (2 ^ w * w) := by
      have h := listBuildSet (List.finRange (2 ^ w))
        (fun p => {f | ∃ a : Fin w, f = fun x => seedMaskRem hn hw hK_lo hK1 0 x p.val a})
        w
        (fun p _ => by
          have ha := finG (fun a : Fin w => fun x => seedMaskRem hn hw hK_lo hK1 0 x p.val a) 1 (fun a => by
            have hpK : p.val < K := lt_of_lt_of_le p.isLt hK_lo
            have he : (fun x => seedMaskRem hn hw hK_lo hK1 0 x p.val a) =
                Build220.or (fun x => bwdMaskRem hn hw hK1 (n - w) x ⟨p.val, hpK⟩ ⟨a.val, by omega⟩)
                   (fun x => bwdMaskRem hn hw hK1 (n - w) x ⟨p.val, hpK⟩ ⟨w + a.val, by omega⟩) := by
              funext x; simp [seedMaskRem, hpK, Build220.or]
            rw [he]
            exact orG (hB0 ⟨p.val, hpK⟩ ⟨a.val, by omega⟩) (hB0 ⟨p.val, hpK⟩ ⟨w + a.val, by omega⟩))
          refine relax ha le_rfl ?_ (by omega)
          rintro f ⟨a, rfl⟩; exact ⟨a, rfl⟩)
      rw [List.length_finRange] at h
      refine relax h le_rfl ?_ le_rfl
      rintro f ⟨p, hp, a, rfl⟩
      exact Set.mem_iUnion.mpr ⟨⟨p, hp⟩, Set.mem_iUnion.mpr ⟨List.mem_finRange _, ⟨a, rfl⟩⟩⟩
    refine relax Hbase le_rfl ?_ (by rw [Nat.sub_zero, Nat.sub_self, Nat.zero_mul, Nat.add_zero, Nat.mul_comm])
    rintro f (⟨rem, hrem, p, hp, a, rfl⟩ | ⟨d, hd, hle, _⟩)
    · have h0 : rem = 0 := by omega
      subst h0; exact ⟨p, by simpa using hp, a, rfl⟩
    · omega
  | succ m ih =>
    intro hm
    have Hprev := ih (by omega)
    let Bprev :=
      {f | ∃ rem ≤ m, ∃ p < 2 ^ (w - rem), ∃ a : Fin w,
          f = fun x => seedMaskRem hn hw hK_lo hK1 rem x p a} ∪
      {f | ∃ d < w, w - m ≤ d ∧ ∃ p < 2 ^ d, ∃ hd : d < w,
          f = seedEn hn hw hK_lo hK1 d p hd}
    let d := w - (m + 1)
    have hd : d < w := by dsimp [d]; omega
    have hwd : w - m = d + 1 := by dsimp [d]; omega
    have Hstep : Build (A ∪ Bprev)
        ({f | ∃ p < 2 ^ d, ∃ a : Fin w, f = fun x => seedMaskRem hn hw hK_lo hK1 (m + 1) x p a} ∪
         {f | ∃ p < 2 ^ d, f = seedEn hn hw hK_lo hK1 d p hd})
        (2 ^ d * (3 * w + 3)) := by
      have h := listBuildSet (List.finRange (2 ^ d))
        (fun p => {f | ∃ a : Fin w, f = fun x => seedMaskRem hn hw hK_lo hK1 (m + 1) x p.val a} ∪
          {seedEn hn hw hK_lo hK1 d p.val hd})
        (3 * w + 3)
        (fun p _ => by
          have hp1 : p.val < 2 ^ (w - m) := by rw [hwd, Nat.pow_succ]; omega
          have hp2 : p.val + 2 ^ d < 2 ^ (w - m) := by rw [hwd, Nat.pow_succ]; omega
          let hpS : Sig (n * 2 ^ (w + 1)) := fun x => seedMaskRem hn hw hK_lo hK1 m x p.val ⟨d, hd⟩
          let hnS : Sig (n * 2 ^ (w + 1)) := fun x => seedMaskRem hn hw hK_lo hK1 m x (p.val + 2 ^ d) ⟨d, hd⟩
          have hhp : hpS ∈ A ∪ Bprev := Or.inr (Or.inl ⟨m, le_rfl, p.val, hp1, ⟨d, hd⟩, rfl⟩)
          have hhn : hnS ∈ A ∪ Bprev := Or.inr (Or.inl ⟨m, le_rfl, p.val + 2 ^ d, hp2, ⟨d, hd⟩, rfl⟩)
          have Hen : Build (A ∪ Bprev) {an hpS hnS} 1 := andG hhp hhn
          have Hnhp : Build ((A ∪ Bprev) ∪ {an hpS hnS}) {nt hpS} 1 := notG (Or.inl hhp)
          let c0 : Sig (n * 2 ^ (w + 1)) := or (nt hpS) hnS
          have Hc0 : Build ((A ∪ Bprev) ∪ ({an hpS hnS} ∪ {nt hpS})) {c0} 1 :=
            orG (Or.inr (Or.inr rfl)) (Or.inl hhn)
          let Ac := (A ∪ Bprev) ∪ (({an hpS hnS} ∪ {nt hpS}) ∪ {c0})
          have Hmsk : Build Ac
              (Set.range (fun a : Fin w => fun x => seedMaskRem hn hw hK_lo hK1 (m + 1) x p.val a)) (w * 3) :=
            finG (fun a : Fin w => fun x => seedMaskRem hn hw hK_lo hK1 (m + 1) x p.val a) 3 (fun a => by
              by_cases had : a.val < d
              · have he : (fun x => seedMaskRem hn hw hK_lo hK1 (m + 1) x p.val a) =
                    (fun x => combMask (hpS x) (hnS x) (seedMaskRem hn hw hK_lo hK1 m x p.val a)
                      (seedMaskRem hn hw hK_lo hK1 m x (p.val + 2 ^ d) a)) := by
                  funext x; simp [seedMaskRem, d, hd, had, hpS, hnS]
                rw [he]
                exact combMaskG (Or.inl hhp) (Or.inr (Or.inr rfl))
                  (Or.inl (Or.inr (Or.inl ⟨m, le_rfl, p.val, hp1, a, rfl⟩)))
                  (Or.inl (Or.inr (Or.inl ⟨m, le_rfl, p.val + 2 ^ d, hp2, a, rfl⟩)))
                  hnS (fun _ => rfl)
              · have he : (fun x => seedMaskRem hn hw hK_lo hK1 (m + 1) x p.val a) = (fun _ => false) := by
                  funext x; simp [seedMaskRem, d, hd, had]
                rw [he]
                exact relax (idle (Set.singleton_subset_iff.mpr (Or.inl (Or.inl hfalse)))) le_rfl le_rfl (by omega))
          have Hpre := seq (seq Hen Hnhp) Hc0
          refine relax (seq Hpre Hmsk) le_rfl ?_ (by omega)
          rintro f (⟨a, rfl⟩ | rfl)
          · exact Or.inr ⟨a, rfl⟩
          · have he : seedEn hn hw hK_lo hK1 d p.val hd = an hpS hnS := by
              funext x
              have heq : w - (d + 1) = m := by omega
              simp [seedEn, heq, an, hpS, hnS]
            rw [he]; exact Or.inl (Or.inl (Or.inl rfl)))
      rw [List.length_finRange] at h
      refine relax h le_rfl ?_ le_rfl
      rintro f (⟨p, hp, a, rfl⟩ | ⟨p, hp, rfl⟩)
      · exact Set.mem_iUnion.mpr ⟨⟨p, hp⟩, Set.mem_iUnion.mpr ⟨List.mem_finRange _, Or.inl ⟨a, rfl⟩⟩⟩
      · exact Set.mem_iUnion.mpr ⟨⟨p, hp⟩, Set.mem_iUnion.mpr ⟨List.mem_finRange _, Or.inr rfl⟩⟩
    refine relax (seq Hprev Hstep) le_rfl ?_ ?_
    · rintro f (⟨rem, hrem, p, hp, a, rfl⟩ | ⟨d', hd', hle, p, hp, hd'', rfl⟩)
      · by_cases hrm : rem ≤ m
        · exact Or.inl (Or.inl ⟨rem, hrm, p, hp, a, rfl⟩)
        · have heq : rem = m + 1 := by omega
          subst heq; exact Or.inr (Or.inl ⟨p, hp, a, rfl⟩)
      · by_cases hdm : w - m ≤ d'
        · exact Or.inl (Or.inr ⟨d', hd', hdm, p, hp, hd'', rfl⟩)
        · have heq : d' = d := by omega
          subst heq; exact Or.inr (Or.inr ⟨p, hp, rfl⟩)
    · have hpow : 2 ^ (w - m) = 2 ^ d + 2 ^ d := by rw [hwd, Nat.pow_succ]; omega
      have hle1 : 2 ^ (w - m) ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) (by omega)
      have hle2 : 2 ^ d ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) (by omega)
      have hdiff : (2 ^ w - 2 ^ (w - m)) + 2 ^ d = 2 ^ w - 2 ^ d := by omega
      change w * 2 ^ w + (2 ^ w - 2 ^ (w - m)) * (3 * w + 3) + 2 ^ d * (3 * w + 3) ≤
        w * 2 ^ w + (2 ^ w - 2 ^ d) * (3 * w + 3)
      calc w * 2 ^ w + (2 ^ w - 2 ^ (w - m)) * (3 * w + 3) + 2 ^ d * (3 * w + 3)
          = w * 2 ^ w + ((2 ^ w - 2 ^ (w - m)) + 2 ^ d) * (3 * w + 3) := by ring
        _ = w * 2 ^ w + (2 ^ w - 2 ^ d) * (3 * w + 3) := by rw [hdiff]
        _ ≤ _ := le_rfl

theorem slots_build {n w K : Nat} (hn : 0 < n) (hw : w ≤ n) (hK_lo : 2 ^ w ≤ K) (hK_hi : K ≤ 4 ^ w)
    {A : Set (Sig (n * 2 ^ (w + 1)))}
    (hVal : ∀ h ≤ n - w, ∀ j : Fin K,
      (fun x => (fwdState hn (le_trans Nat.one_le_two_pow hK_lo) h x).val j) ∈ A)
    (hPair : ∀ h ≤ n - w, ∀ (j : Fin K) (k : Fin (2 * w)),
      (fun x => (fwdState hn (le_trans Nat.one_le_two_pow hK_lo) h x).pair j k) ∈ A)
    (hOk : ∀ h < n - w, ∀ u : Fin (2 * K),
      (fun x => (stepAt hn (le_trans Nat.one_le_two_pow hK_lo) h x).ok u) ∈ A)
    (hTBad : ∀ j : Fin K, termBad hn hw (le_trans Nat.one_le_two_pow hK_lo) j ∈ A)
    (hTMask : ∀ (j : Fin K) (k : Fin (2 * w)),
      (fun x => termMask hn hw (le_trans Nat.one_le_two_pow hK_lo) j x k) ∈ A)
    (hBMask : ∀ rem ≤ n - w, ∀ (j : Fin K) (k : Fin (2 * w)),
      (fun x => bwdMaskRem hn hw (le_trans Nat.one_le_two_pow hK_lo) rem x j k) ∈ A)
    (hBPos : ∀ h < n - w, ∀ j : Fin K,
      (fun x => (bwdStepAt hn hw (le_trans Nat.one_le_two_pow hK_lo) h x).hasPos j) ∈ A)
    (hBNeg : ∀ h < n - w, ∀ j : Fin K,
      (fun x => (bwdStepAt hn hw (le_trans Nat.one_le_two_pow hK_lo) h x).hasNeg j) ∈ A)
    (hSMask : ∀ rem ≤ w, ∀ p < 2 ^ (w - rem), ∀ a : Fin w,
      (fun x => seedMaskRem hn hw hK_lo (le_trans Nat.one_le_two_pow hK_lo) rem x p a) ∈ A)
    (hSEn : ∀ d < w, ∀ p < 2 ^ d, ∀ hd : d < w,
      seedEn hn hw hK_lo (le_trans Nat.one_le_two_pow hK_lo) d p hd ∈ A)
    (hfalse : (fun _ => false) ∈ A) (htrue : (fun _ => true) ∈ A) :
    have hK1 : 1 ≤ K := le_trans Nat.one_le_two_pow hK_lo
    let S := (3 * (n - w) + 2) * K
    Build A
      ({f | ∃ s : Fin S, f = semEnable hn hw hK_lo hK1 s} ∪
       {f | ∃ (s : Fin S) (lit : Fin n × Bool), f = semMember hn hw hK_lo hK1 s lit})
      (S * (20 * w + 4)) := by
  have hK1 : 1 ≤ K := le_trans Nat.one_le_two_pow hK_lo
  let S := (3 * (n - w) + 2) * K
  have hpairMemB : ∀ h ≤ n - w, ∀ (pair mask : (Fin (n * 2 ^ (w + 1)) → Bool) → Fin (2 * w) → Bool),
      (∀ k : Fin (2 * w), (fun x => pair x k) ∈ A) →
      (∀ k : Fin (2 * w), (fun x => mask x k) ∈ A) →
      Build A {f | ∃ lit : Fin n × Bool, f = fun x => pairClauseMem h (pair x) (mask x) lit} (20 * w) := by
    intro h hh pair mask hp hm
    let active : List (Fin n) :=
      ((List.finRange w).map (fun a => ⟨a.val, by omega⟩)) ++
      ((List.finRange w).map (fun z => ⟨h + z.val, by omega⟩))
    have hlen : active.length = 2 * w := by simp [active, Nat.two_mul]
    have Hact : Build A
        (⋃ v ∈ active, {f | ∃ pol : Bool, f = fun x => pairClauseMem h (pair x) (mask x) (v, pol)})
        (active.length * 10) := by
      refine listBuildSet active
        (fun v => {f | ∃ pol : Bool, f = fun x => pairClauseMem h (pair x) (mask x) (v, pol)})
        10 (fun v _ => ?_)
      have hpol : ∀ pol : Bool, Build A {fun x => pairClauseMem h (pair x) (mask x) (v, pol)} 5 := by
        intro pol
        let inL : Sig (n * 2 ^ (w + 1)) := fun x =>
          if hv : v.val < w then mask x ⟨v.val, by omega⟩ && (!(pair x ⟨v.val, by omega⟩) == pol) else false
        let inR : Sig (n * 2 ^ (w + 1)) := fun x =>
          if hv : h ≤ v.val ∧ v.val < h + w then
            mask x ⟨w + (v.val - h), by omega⟩ && (!(pair x ⟨w + (v.val - h), by omega⟩) == pol)
          else false
        have HL : Build A {inL} 2 := by
          by_cases hv : v.val < w
          · cases pol
            · have he : inL = an (fun x => mask x ⟨v.val, by omega⟩) (fun x => pair x ⟨v.val, by omega⟩) := by
                funext x; simp only [inL, hv, ↓reduceDIte, an]; cases pair x ⟨v.val, by omega⟩ <;> rfl
              rw [he]; exact relax (andG (hm _) (hp _)) le_rfl le_rfl (by omega)
            · have h1 := notG (hp ⟨v.val, by omega⟩)
              have h2 := andG (A := A ∪ {nt (fun x => pair x ⟨v.val, by omega⟩)})
                (Or.inl (hm ⟨v.val, by omega⟩)) (Or.inr rfl)
              have he : an (fun x => mask x ⟨v.val, by omega⟩) (nt (fun x => pair x ⟨v.val, by omega⟩)) = inL := by
                funext x; simp only [inL, hv, ↓reduceDIte, an, nt]; cases pair x ⟨v.val, by omega⟩ <;> rfl
              rw [he] at h2
              exact relax (seq h1 h2) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl
          · have he : inL = (fun _ => false) := by funext x; simp [inL, hv]
            rw [he]; exact relax (idle (Set.singleton_subset_iff.mpr hfalse)) le_rfl le_rfl (by omega)
        have HR : Build (A ∪ {inL}) {inR} 2 := by
          by_cases hv : h ≤ v.val ∧ v.val < h + w
          · cases pol
            · have he : inR = an (fun x => mask x ⟨w + (v.val - h), by omega⟩)
                  (fun x => pair x ⟨w + (v.val - h), by omega⟩) := by
                funext x; dsimp only [inR, an]; rw [dite_pos hv]; cases pair x ⟨w + (v.val - h), by omega⟩ <;> rfl
              rw [he]; exact relax (andG (Or.inl (hm _)) (Or.inl (hp _))) le_rfl le_rfl (by omega)
            · have h1 := notG (A := A ∪ {inL}) (Or.inl (hp ⟨w + (v.val - h), by omega⟩))
              have h2 := andG (A := (A ∪ {inL}) ∪ {nt (fun x => pair x ⟨w + (v.val - h), by omega⟩)})
                (Or.inl (Or.inl (hm ⟨w + (v.val - h), by omega⟩))) (Or.inr rfl)
              have he : an (fun x => mask x ⟨w + (v.val - h), by omega⟩)
                  (nt (fun x => pair x ⟨w + (v.val - h), by omega⟩)) = inR := by
                funext x; dsimp only [inR, an, nt]; rw [dite_pos hv]; cases pair x ⟨w + (v.val - h), by omega⟩ <;> rfl
              rw [he] at h2
              exact relax (seq h1 h2) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl
          · have he : inR = (fun _ => false) := by funext x; simp [inR, hv]
            rw [he]; exact relax (idle (Set.singleton_subset_iff.mpr (Or.inl hfalse))) le_rfl le_rfl (by omega)
        have Hor : Build (A ∪ ({inL} ∪ {inR})) {or inL inR} 1 :=
          orG (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
        have he : or inL inR = (fun x => pairClauseMem h (pair x) (mask x) (v, pol)) := rfl
        rw [he] at Hor
        exact relax (seq (seq HL HR) Hor) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl
      have hF := hpol false
      have hT := relax (hpol true)
        (C := A ∪ {fun x => pairClauseMem h (pair x) (mask x) (v, false)})
        Set.subset_union_left le_rfl le_rfl
      refine relax (seq hF hT) le_rfl ?_ (by omega)
      rintro f ⟨pol, rfl⟩
      cases pol
      · exact Or.inl rfl
      · exact Or.inr rfl
    have Hwith0 := seq (idle (A := A) (B := {fun _ => false}) (Set.singleton_subset_iff.mpr hfalse))
      (relax Hact Set.subset_union_left le_rfl (by rw [hlen]))
    refine relax Hwith0 le_rfl ?_ (by omega)
    rintro f ⟨⟨v, pol⟩, rfl⟩
    by_cases hv : v.val < w ∨ (h ≤ v.val ∧ v.val < h + w)
    · have hmem : v ∈ active := by
        simp only [active, List.mem_append, List.mem_map, List.mem_finRange, true_and]
        rcases hv with h1 | ⟨h1, h2⟩
        · left; exact ⟨⟨v.val, h1⟩, by ext; rfl⟩
        · right; exact ⟨⟨v.val - h, by omega⟩, by ext; dsimp; omega⟩
      exact Or.inr (Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr ⟨hmem, ⟨pol, rfl⟩⟩⟩)
    · have h0 : (fun x => pairClauseMem h (pair x) (mask x) (v, pol)) = (fun _ => false) := by
        funext x
        have h1 : ¬ v.val < w := fun c => hv (Or.inl c)
        have h2 : ¬ (h ≤ v.val ∧ v.val < h + w) := fun c => hv (Or.inr c)
        simp [pairClauseMem, h1, h2]
      rw [h0]
      exact Or.inl rfl
  have haxMemB : ∀ h < n - w, ∀ (pair : (Fin (n * 2 ^ (w + 1)) → Bool) → Fin (2 * w) → Bool) (b : Bool),
      (∀ k : Fin (2 * w), (fun x => pair x k) ∈ A) →
      Build A {f | ∃ lit : Fin n × Bool, f = fun x => axBranchMem h (pair x) b lit} (2 * w) := by
    intro h hh pair b hp
    let active : List (Fin n) := (List.finRange w).map (fun z => ⟨h + z.val, by omega⟩)
    have hlen : active.length = w := by simp [active]
    have Hact : Build A
        (⋃ v ∈ active, {f | ∃ pol : Bool, f = fun x => axBranchMem h (pair x) b (v, pol)})
        (active.length * 2) := by
      refine listBuildSet active
        (fun v => {f | ∃ pol : Bool, f = fun x => axBranchMem h (pair x) b (v, pol)})
        2 (fun v hv => ?_)
      rcases List.mem_map.mp hv with ⟨z, _, rfl⟩
      have hz : z.val < w := z.isLt
      have hbd : h ≤ h + z.val ∧ h + z.val < h + w := ⟨by omega, by omega⟩
      let vz : Fin n := ⟨h + z.val, by omega⟩
      have hF : Build A {fun x => axBranchMem h (pair x) b (vz, false)} 1 := by
        have he : (fun x => axBranchMem h (pair x) b (vz, false)) =
            (fun x => pair x ⟨w + (h + z.val - h), by omega⟩) := by
          funext x; dsimp only [axBranchMem, vz]; rw [dite_pos hbd]
          cases pair x ⟨w + (h + z.val - h), by omega⟩ <;> rfl
        rw [he]; exact relax (idle (Set.singleton_subset_iff.mpr (hp _))) le_rfl le_rfl (by omega)
      have hT : Build (A ∪ {fun x => axBranchMem h (pair x) b (vz, false)})
          {fun x => axBranchMem h (pair x) b (vz, true)} 1 := by
        have he : (fun x => axBranchMem h (pair x) b (vz, true)) =
            nt (fun x => pair x ⟨w + (h + z.val - h), by omega⟩) := by
          funext x; dsimp only [axBranchMem, vz, nt]; rw [dite_pos hbd]
          cases pair x ⟨w + (h + z.val - h), by omega⟩ <;> rfl
        rw [he]; exact notG (Or.inl (hp _))
      refine relax (seq hF hT) le_rfl ?_ (by omega)
      rintro f ⟨pol, rfl⟩
      cases pol
      · exact Or.inl rfl
      · exact Or.inr rfl
    have Hwith01 := seq (idle (A := A) (B := {fun _ => false} ∪ {fun _ => true})
        (Set.union_subset (Set.singleton_subset_iff.mpr hfalse) (Set.singleton_subset_iff.mpr htrue)))
      (relax Hact Set.subset_union_left le_rfl (by rw [hlen]))
    refine relax Hwith01 le_rfl ?_ (by omega)
    rintro f ⟨⟨v, pol⟩, rfl⟩
    by_cases hv : h ≤ v.val ∧ v.val < h + w
    · have hmem : v ∈ active := by
        simp only [active, List.mem_map, List.mem_finRange, true_and]
        exact ⟨⟨v.val - h, by omega⟩, by ext; dsimp; omega⟩
      exact Or.inr (Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr ⟨hmem, ⟨pol, rfl⟩⟩⟩)
    · have hc : (fun x => axBranchMem h (pair x) b (v, pol)) = (fun _ => if v.val = h + w then ((!b) == pol) else false) := by
        funext x; simp [axBranchMem, hv]
      rw [hc]
      cases hval : (if v.val = h + w then ((!b) == pol) else false)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inl (Or.inr rfl)
  have hslot : ∀ s : Fin S,
      Build A
        ({semEnable hn hw hK_lo hK1 s} ∪ {f | ∃ lit : Fin n × Bool, f = semMember hn hw hK_lo hK1 s lit})
        (20 * w + 4) := by
    intro s
    by_cases hs1 : s.val < K
    · by_cases hs2 : s.val < 2 ^ w - 1
      · let d := Nat.log2 (s.val + 1)
        let p := s.val + 1 - 2 ^ d
        have hd : d < w := by
          have h1 : s.val + 1 < 2 ^ w := by omega
          exact (Nat.log2_lt (by omega)).mpr h1
        have hp : p < 2 ^ d := by
          have hlo : 2 ^ d ≤ s.val + 1 := Nat.log2_self_le (by omega)
          have hhi : s.val + 1 < 2 ^ (d + 1) := Nat.lt_log2_self
          rw [Nat.pow_succ] at hhi; omega
        refine relax (idle ?_) le_rfl le_rfl (by omega)
        rintro f (rfl | ⟨⟨v, pol⟩, rfl⟩)
        · have he : semEnable hn hw hK_lo hK1 s = seedEn hn hw hK_lo hK1 d p hd := by
            funext x; simp [semEnable, hs1, hs2, d, p, hd]
          rw [he]; exact hSEn d hd p hp hd
        · by_cases hv : v.val < d
          · by_cases hpol : !(p.testBit v.val) == pol
            · have he : semMember hn hw hK_lo hK1 s (v, pol) =
                  fun x => seedMaskRem hn hw hK_lo hK1 (w - d) x p ⟨v.val, by omega⟩ := by
                funext x; simp [semMember, hs1, hs2, d, p, hd, hv, hpol]
              rw [he]
              have hrem : w - (w - d) = d := by omega
              exact hSMask (w - d) (by omega) p (by rw [hrem]; exact hp) ⟨v.val, by omega⟩
            · have he : semMember hn hw hK_lo hK1 s (v, pol) = (fun _ => false) := by
                funext x; simp [semMember, hs1, hs2, d, p, hd, hv, hpol]
              rw [he]; exact hfalse
          · have he : semMember hn hw hK_lo hK1 s (v, pol) = (fun _ => false) := by
              funext x; simp [semMember, hs1, hs2, d, p, hd, hv]
            rw [he]; exact hfalse
      · refine relax (idle ?_) le_rfl le_rfl (by omega)
        rintro f (rfl | ⟨lit, rfl⟩)
        · have he : semEnable hn hw hK_lo hK1 s = (fun _ => false) := by
            funext x; simp [semEnable, hs1, hs2]
          rw [he]; exact hfalse
        · have he : semMember hn hw hK_lo hK1 s lit = (fun _ => false) := by
            funext x; simp [semMember, hs1, hs2]
          rw [he]; exact hfalse
    · by_cases hs3 : s.val < K + 3 * (n - w) * K
      · let off := s.val - K
        let h := off / (3 * K)
        let rem := off % (3 * K)
        let kind := rem / K
        let j : Fin K := ⟨rem % K, Nat.mod_lt _ (by omega)⟩
        have hh : h < n - w := by
          have hoff : off < (n - w) * (3 * K) := by
            have : 3 * (n - w) * K = (n - w) * (3 * K) := by ring
            dsimp [off]; omega
          exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
        by_cases hk0 : kind = 0
        · have Hen : Build A {semEnable hn hw hK_lo hK1 s} 2 := by
            let t1 := an (fun x => (fwdState hn hK1 h x).val j) (fun x => (bwdStepAt hn hw hK1 h x).hasPos j)
            have h1 : Build A {t1} 1 := andG (hVal h (by omega) j) (hBPos h hh j)
            have h2 := andG (A := A ∪ {t1}) (Or.inr rfl) (Or.inl (hBNeg h hh j))
            have he : an t1 (fun x => (bwdStepAt hn hw hK1 h x).hasNeg j) = semEnable hn hw hK_lo hK1 s := by
              funext x; simp [semEnable, hs1, hs3, off, h, rem, kind, j, hk0, t1, an]
            rw [he] at h2
            exact relax (seq h1 h2) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl
          have Hmem := hpairMemB h (by omega) (fun x => (fwdState hn hK1 h x).pair j)
            (fun x => bwdMaskAt hn hw hK1 h x j) (hPair h (by omega) j) (hBMask (n - w - h) (Nat.sub_le (n - w) h) j)
          have Hmem' := relax (C := A ∪ {semEnable hn hw hK_lo hK1 s}) Hmem Set.subset_union_left le_rfl le_rfl
          refine relax (seq Hen Hmem') le_rfl ?_ (by omega)
          rintro f (rfl | ⟨lit, rfl⟩)
          · exact Or.inl rfl
          · right; refine ⟨lit, ?_⟩; funext x; simp [semMember, hs1, hs3, off, h, rem, kind, j, hk0]
        · by_cases hk1 : kind = 1
          · have Hen : Build A {semEnable hn hw hK_lo hK1 s} 2 := by
              have h1 := notG (hOk h hh ⟨2 * j.val, by omega⟩)
              have h2 := andG (A := A ∪ {nt (fun x => (stepAt hn hK1 h x).ok ⟨2 * j.val, by omega⟩)})
                (Or.inl (hVal h (by omega) j)) (Or.inr rfl)
              have he : an (fun x => (fwdState hn hK1 h x).val j)
                  (nt (fun x => (stepAt hn hK1 h x).ok ⟨2 * j.val, by omega⟩)) = semEnable hn hw hK_lo hK1 s := by
                funext x; simp [semEnable, hs1, hs3, off, h, rem, kind, j, hk0, hk1, an, nt]
              rw [he] at h2
              exact relax (seq h1 h2) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl
            have Hmem := haxMemB h hh (fun x => (fwdState hn hK1 h x).pair j) false (hPair h (by omega) j)
            have Hmem' := relax (C := A ∪ {semEnable hn hw hK_lo hK1 s}) Hmem Set.subset_union_left le_rfl le_rfl
            refine relax (seq Hen Hmem') le_rfl ?_ (by omega)
            rintro f (rfl | ⟨lit, rfl⟩)
            · exact Or.inl rfl
            · right; refine ⟨lit, ?_⟩; funext x; simp [semMember, hs1, hs3, off, h, rem, kind, j, hk0, hk1]
          · have Hen : Build A {semEnable hn hw hK_lo hK1 s} 2 := by
              have h1 := notG (hOk h hh ⟨2 * j.val + 1, by omega⟩)
              have h2 := andG (A := A ∪ {nt (fun x => (stepAt hn hK1 h x).ok ⟨2 * j.val + 1, by omega⟩)})
                (Or.inl (hVal h (by omega) j)) (Or.inr rfl)
              have he : an (fun x => (fwdState hn hK1 h x).val j)
                  (nt (fun x => (stepAt hn hK1 h x).ok ⟨2 * j.val + 1, by omega⟩)) = semEnable hn hw hK_lo hK1 s := by
                funext x; simp [semEnable, hs1, hs3, off, h, rem, kind, j, hk0, hk1, an, nt]
              rw [he] at h2
              exact relax (seq h1 h2) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl
            have Hmem := haxMemB h hh (fun x => (fwdState hn hK1 h x).pair j) true (hPair h (by omega) j)
            have Hmem' := relax (C := A ∪ {semEnable hn hw hK_lo hK1 s}) Hmem Set.subset_union_left le_rfl le_rfl
            refine relax (seq Hen Hmem') le_rfl ?_ (by omega)
            rintro f (rfl | ⟨lit, rfl⟩)
            · exact Or.inl rfl
            · right; refine ⟨lit, ?_⟩; funext x; simp [semMember, hs1, hs3, off, h, rem, kind, j, hk0, hk1]
      · let j : Fin K := ⟨s.val - (K + 3 * (n - w) * K), by
          have hlt := s.isLt
          have heq : (3 * (n - w) + 2) * K = K + 3 * (n - w) * K + K := by ring
          omega⟩
        have Hen : Build A {semEnable hn hw hK_lo hK1 s} 1 := by
          have h1 := andG (hVal (n - w) le_rfl j) (hTBad j)
          have he : an (fun x => (fwdState hn hK1 (n - w) x).val j) (termBad hn hw hK1 j) =
              semEnable hn hw hK_lo hK1 s := by
            funext x; simp [semEnable, hs1, hs3, j, an]
          rw [he] at h1; exact h1
        have Hmem := hpairMemB (n - w) le_rfl (fun x => (fwdState hn hK1 (n - w) x).pair j)
          (fun x => termMask hn hw hK1 j x) (hPair (n - w) le_rfl j) (hTMask j)
        have Hmem' := relax (C := A ∪ {semEnable hn hw hK_lo hK1 s}) Hmem Set.subset_union_left le_rfl le_rfl
        refine relax (seq Hen Hmem') le_rfl ?_ (by omega)
        rintro f (rfl | ⟨lit, rfl⟩)
        · exact Or.inl rfl
        · right; refine ⟨lit, ?_⟩; funext x; simp [semMember, hs1, hs3, j]
  have Hall := listBuildSet (List.finRange S)
    (fun s => {semEnable hn hw hK_lo hK1 s} ∪ {f | ∃ lit : Fin n × Bool, f = semMember hn hw hK_lo hK1 s lit})
    (20 * w + 4) (fun s _ => hslot s)
  rw [List.length_finRange] at Hall
  refine relax Hall le_rfl ?_ le_rfl
  rintro f (⟨s, rfl⟩ | ⟨s, lit, rfl⟩)
  · exact Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨List.mem_finRange s, Or.inl rfl⟩⟩
  · exact Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨List.mem_finRange s, Or.inr ⟨lit, rfl⟩⟩⟩

theorem build_full_circuit (n w K : Nat) (hn : 0 < n) (hw : w ≤ n)
    (hK_lo : 2 ^ w ≤ K) (hK_hi : K ≤ 4 ^ w) :
    have hK1 : 1 ≤ K := le_trans Nat.one_le_two_pow hK_lo
    let I := n * 2 ^ (w + 1)
    let S := (3 * (n - w) + 2) * K
    ∃ (C : Circuit) (enable : Fin S → Nat) (memberWire : Fin S → Literal (Fin n) → Nat),
      FanInTwo C ∧ ReadsBack I C ∧
      C.size ≤ 262144 * (n + 1) ^ 4 * K ∧ C.output < I + C.size ∧
      (∀ slot, enable slot < I + C.size) ∧
      (∀ slot lit, memberWire slot lit < I + C.size) ∧
      ∀ x : Fin I → Bool,
        C.eval (List.ofFn x) = outSig hn hw hK1 x ∧
        (∀ slot, (C.wires (List.ofFn x)).getD (enable slot) false = semEnable hn hw hK_lo hK1 slot x) ∧
        (∀ slot lit, (C.wires (List.ofFn x)).getD (memberWire slot lit) false =
          semMember hn hw hK_lo hK1 slot lit x) := by
  have hK1 : 1 ≤ K := le_trans Nat.one_le_two_pow hK_lo
  let I := n * 2 ^ (w + 1)
  let S := (3 * (n - w) + 2) * K
  let A0 : Set (Sig I) := Set.range (fun a : Fin I => fun x : Fin I → Bool => x a)
  have Hstart : GateBridge.Scheduled I id 0 A0 :=
    GateBridge.start (F := (id : Sig I → (Fin I → Bool) → Bool)) (fun a : Fin I => fun x : Fin I → Bool => x a) (fun _ _ => rfl)
  have Hc0 : Build A0 {fun _ => false} 1 := constG false
  have Hc1 : Build (A0 ∪ {fun _ => false}) {fun _ => true} 1 := constG true
  let A1 := A0 ∪ ({fun _ => false} ∪ {fun _ => true})
  have hinp1 : ∀ a : Fin I, (fun x => x a) ∈ A1 := fun a => Or.inl ⟨a, rfl⟩
  have hf1 : (fun _ => false) ∈ A1 := Or.inr (Or.inl rfl)
  have ht1 : (fun _ => true) ∈ A1 := Or.inr (Or.inr rfl)
  have Hfwd := fwdAll_build hn hw hK_lo hK_hi (A := A1) hinp1 hf1 ht1 (n - w) le_rfl
  let Bfwd :=
    {f | ∃ h ≤ n - w, ∃ j : Fin K, f = fun x => (fwdState hn hK1 h x).val j} ∪
    {f | ∃ h ≤ n - w, ∃ (j : Fin K) (k : Fin (2 * w)), f = fun x => (fwdState hn hK1 h x).pair j k} ∪
    {f | ∃ h < n - w, ∃ u : Fin (2 * K), f = fun x => (stepAt hn hK1 h x).ok u} ∪
    {f | ∃ h < n - w, ∃ i < sortM K, f = fun x => (stepAt hn hK1 h x).isRep i} ∪
    {f | ∃ h < n - w, ∃ t < (sortNet K).length,
      f = (fun x => ((stepAt hn hK1 h x).sw1.getD t (0, 0, false)).2.2) ∨
      f = (fun x => !(((stepAt hn hK1 h x).sw1.getD t (0, 0, false)).2.2)) ∨
      f = (fun x => ((stepAt hn hK1 h x).sw2.getD t (0, 0, false)).2.2) ∨
      f = (fun x => !(((stepAt hn hK1 h x).sw2.getD t (0, 0, false)).2.2))}
  let A2 := A1 ∪ Bfwd
  have Hterm := term_build hn hw hK_lo hK_hi (A := A2)
    (fun j => Or.inr (Or.inl (Or.inl (Or.inl (Or.inl ⟨n - w, le_rfl, j, rfl⟩)))))
    (fun j k => Or.inr (Or.inl (Or.inl (Or.inl (Or.inr ⟨n - w, le_rfl, j, k, rfl⟩)))))
    (fun a => Or.inl (hinp1 a)) (Or.inl hf1) (Or.inl ht1)
  let Bterm :=
    {f | ∃ j : Fin K, f = termBad hn hw hK1 j} ∪
    {f | ∃ (j : Fin K) (k : Fin (2 * w)), f = fun x => termMask hn hw hK1 j x k} ∪
    {outSig hn hw hK1}
  let A3 := A2 ∪ Bterm
  have Hbwd := bwdAll_build hn hw hK_lo hK_hi (A := A3)
    (fun j k => Or.inr (Or.inl (Or.inr ⟨j, k, rfl⟩)))
    (fun h hh u => Or.inl (Or.inr (Or.inl (Or.inl (Or.inr ⟨h, hh, u, rfl⟩)))))
    (fun h hh i hi => Or.inl (Or.inr (Or.inl (Or.inr ⟨h, hh, i, hi, rfl⟩))))
    (fun h hh t ht => ⟨Or.inl (Or.inr (Or.inr ⟨h, hh, t, ht, Or.inl rfl⟩)),
      Or.inl (Or.inr (Or.inr ⟨h, hh, t, ht, Or.inr (Or.inl rfl)⟩))⟩)
    (fun h hh t ht => ⟨Or.inl (Or.inr (Or.inr ⟨h, hh, t, ht, Or.inr (Or.inr (Or.inl rfl))⟩)),
      Or.inl (Or.inr (Or.inr ⟨h, hh, t, ht, Or.inr (Or.inr (Or.inr rfl))⟩))⟩)
    (Or.inl (Or.inl hf1)) (n - w) le_rfl
  let Bbwd :=
    {f | ∃ rem ≤ n - w, ∃ (j : Fin K) (k : Fin (2 * w)), f = fun x => bwdMaskRem hn hw hK1 rem x j k} ∪
    {f | ∃ rem < n - w, ∃ j : Fin K, f = fun x => (bwdStepAt hn hw hK1 (n - w - (rem + 1)) x).hasPos j} ∪
    {f | ∃ rem < n - w, ∃ j : Fin K, f = fun x => (bwdStepAt hn hw hK1 (n - w - (rem + 1)) x).hasNeg j}
  let A4 := A3 ∪ Bbwd
  have Hseed := seed_build hn hw hK_lo (A := A4)
    (fun j k => Or.inr (Or.inl (Or.inl ⟨n - w, le_rfl, j, k, rfl⟩)))
    (Or.inl (Or.inl (Or.inl hf1))) w le_rfl
  let Bseed :=
    {f | ∃ rem ≤ w, ∃ p < 2 ^ (w - rem), ∃ a : Fin w,
        f = fun x => seedMaskRem hn hw hK_lo hK1 rem x p a} ∪
    {f | ∃ d < w, w - w ≤ d ∧ ∃ p < 2 ^ d, ∃ hd : d < w,
        f = seedEn hn hw hK_lo hK1 d p hd}
  let A5 := A4 ∪ Bseed
  have Hslots := slots_build hn hw hK_lo hK_hi (A := A5)
    (fun h hh j => Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl ⟨h, hh, j, rfl⟩))))))))
    (fun h hh j k => Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr ⟨h, hh, j, k, rfl⟩))))))))
    (fun h hh u => Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr ⟨h, hh, u, rfl⟩)))))))
    (fun j => Or.inl (Or.inl (Or.inr (Or.inl (Or.inl ⟨j, rfl⟩)))))
    (fun j k => Or.inl (Or.inl (Or.inr (Or.inl (Or.inr ⟨j, k, rfl⟩)))))
    (fun rem hrem j k => Or.inl (Or.inr (Or.inl (Or.inl ⟨rem, hrem, j, k, rfl⟩))))
    (fun h hh j => by
      have heq : n - w - ((n - w - (h + 1)) + 1) = h := by omega
      have hm : (fun x => (bwdStepAt hn hw hK1 (n - w - ((n - w - (h + 1)) + 1)) x).hasPos j) ∈ A5 :=
        Or.inl (Or.inr (Or.inl (Or.inr ⟨n - w - (h + 1), by omega, j, rfl⟩)))
      simpa only [heq] using hm)
    (fun h hh j => by
      have heq : n - w - ((n - w - (h + 1)) + 1) = h := by omega
      have hm : (fun x => (bwdStepAt hn hw hK1 (n - w - ((n - w - (h + 1)) + 1)) x).hasNeg j) ∈ A5 :=
        Or.inl (Or.inr (Or.inr ⟨n - w - (h + 1), by omega, j, rfl⟩))
      simpa only [heq] using hm)
    (fun rem hrem p hp a => Or.inr (Or.inl ⟨rem, hrem, p, hp, a, rfl⟩))
    (fun d hd p hp hd' => Or.inr (Or.inr ⟨d, hd, by omega, p, hp, hd', rfl⟩))
    (Or.inl (Or.inl (Or.inl (Or.inl hf1)))) (Or.inl (Or.inl (Or.inl (Or.inl ht1))))
  have Ht1 := seq Hc0 Hc1
  have hs1 : A1 ⊆ A0 ∪ ({fun _ => false} ∪ {fun _ => true}) := le_rfl
  have Ht2 := seqS Ht1 Hfwd hs1
  have hs2 := stepSub (B_new := Bfwd) hs1
  have Ht3 := seqS Ht2 Hterm hs2
  have hs3 := stepSub (B_new := Bterm) hs2
  have Ht4 := seqS Ht3 Hbwd hs3
  have hs4 := stepSub (B_new := Bbwd) hs3
  have Ht5 := seqS Ht4 Hseed hs4
  have hs5 := stepSub (B_new := Bseed) hs4
  have Htot := seqS Ht5 Hslots hs5
  obtain ⟨c, hc, Hsched⟩ := Htot.run Hstart le_rfl
  obtain ⟨gs, hgs, hread, hfan, hfind⟩ := Hsched
  have hc_le : c ≤ 262144 * (n + 1) ^ 4 * K := by
    have h1 : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow 3 (n + 1) (Nat.succ_pos n)
    have h2 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow 2 (n + 1) (Nat.succ_pos n)
    have h3 : 1 ≤ (n + 1) ^ 4 := Nat.one_le_pow 4 (n + 1) (Nat.succ_pos n)
    have ht1' : (n - w) * (47000 * (n + 1) ^ 3 * K) + w * (46656 * (n + 1) ^ 3 * K) ≤
        47000 * (n + 1) ^ 4 * K := by
      have hle : w * (46656 * (n + 1) ^ 3 * K) ≤ w * (47000 * (n + 1) ^ 3 * K) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega)))
      calc (n - w) * (47000 * (n + 1) ^ 3 * K) + w * (46656 * (n + 1) ^ 3 * K)
          ≤ (n - w) * (47000 * (n + 1) ^ 3 * K) + w * (47000 * (n + 1) ^ 3 * K) := Nat.add_le_add_left hle _
        _ = ((n - w) + w) * (47000 * (n + 1) ^ 3 * K) := by rw [← Nat.add_mul]
        _ = n * (47000 * (n + 1) ^ 3 * K) := by rw [Nat.sub_add_cancel hw]
        _ ≤ (n + 1) * (47000 * (n + 1) ^ 3 * K) := Nat.mul_le_mul_right _ (by omega)
        _ = 47000 * (n + 1) ^ 4 * K := by ring
    have ht2' : (2 * w ^ 2 + 4 * w + 4) * K ≤ 10 * (n + 1) ^ 4 * K := by
      have hsq : w ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have hlin : 2 * w ^ 2 + 4 * w + 4 ≤ 10 * (n + 1) ^ 2 := by
        have : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
        have : w ≤ n + 1 := by omega
        nlinarith
      calc (2 * w ^ 2 + 4 * w + 4) * K
          ≤ (10 * (n + 1) ^ 2) * K := Nat.mul_le_mul_right _ hlin
        _ = 10 * (n + 1) ^ 2 * 1 * K := by ring
        _ ≤ 10 * (n + 1) ^ 2 * (n + 1) ^ 2 * K := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h2)
        _ = 10 * (n + 1) ^ 4 * K := by ring
    have ht3' : (n - w) * (200 * (n + 1) ^ 3 * K) ≤ 200 * (n + 1) ^ 4 * K := by
      calc (n - w) * (200 * (n + 1) ^ 3 * K)
          ≤ (n + 1) * (200 * (n + 1) ^ 3 * K) := Nat.mul_le_mul_right _ (by omega)
        _ = 200 * (n + 1) ^ 4 * K := by ring
    have ht4' : w * 2 ^ w + (2 ^ w - 2 ^ (w - w)) * (3 * w + 3) ≤ 4 * (n + 1) ^ 4 * K := by
      have h1' : w * 2 ^ w ≤ (n + 1) * K := Nat.mul_le_mul (by omega) hK_lo
      have h2' : (2 ^ w - 2 ^ (w - w)) * (3 * w + 3) ≤ K * (3 * (n + 1)) :=
        Nat.mul_le_mul (le_trans (Nat.sub_le _ _) hK_lo) (by omega)
      calc w * 2 ^ w + (2 ^ w - 2 ^ (w - w)) * (3 * w + 3)
          ≤ (n + 1) * K + K * (3 * (n + 1)) := Nat.add_le_add h1' h2'
        _ = 4 * (n + 1) * 1 * K := by ring
        _ ≤ 4 * (n + 1) * (n + 1) ^ 3 * K := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)
        _ = 4 * (n + 1) ^ 4 * K := by ring
    have ht5' : S * (20 * w + 4) ≤ 72 * (n + 1) ^ 4 * K := by
      have hS : S ≤ 3 * (n + 1) * K := by
        dsimp [S]
        have : 3 * (n - w) + 2 ≤ 3 * (n + 1) := by omega
        exact Nat.mul_le_mul_right K this
      calc S * (20 * w + 4)
          ≤ (3 * (n + 1) * K) * (24 * (n + 1)) := Nat.mul_le_mul hS (by omega)
        _ = 72 * (n + 1) ^ 2 * 1 * K := by ring
        _ ≤ 72 * (n + 1) ^ 2 * (n + 1) ^ 2 * K := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h2)
        _ = 72 * (n + 1) ^ 4 * K := by ring
    have ht0 : 1 + 1 ≤ 2 * (n + 1) ^ 4 * K := by
      calc 1 + 1 = 2 * 1 * 1 := by ring
        _ ≤ 2 * (n + 1) ^ 4 * K := Nat.mul_le_mul (Nat.mul_le_mul_left 2 h3) hK1
    have hsum : 2 * (n + 1) ^ 4 * K + 47000 * (n + 1) ^ 4 * K + 10 * (n + 1) ^ 4 * K +
        200 * (n + 1) ^ 4 * K + 4 * (n + 1) ^ 4 * K + 72 * (n + 1) ^ 4 * K ≤
        262144 * (n + 1) ^ 4 * K := by
      have heq : 2 * (n + 1) ^ 4 * K + 47000 * (n + 1) ^ 4 * K + 10 * (n + 1) ^ 4 * K +
          200 * (n + 1) ^ 4 * K + 4 * (n + 1) ^ 4 * K + 72 * (n + 1) ^ 4 * K =
          47288 * ((n + 1) ^ 4 * K) := by ring
      have hr : 262144 * (n + 1) ^ 4 * K = 262144 * ((n + 1) ^ 4 * K) := by ring
      rw [heq, hr]
      exact Nat.mul_le_mul_right _ (by omega)
    dsimp only [S] at ht5'
    omega
  obtain ⟨outW, houtW_lt, houtW_val⟩ := hfind (outSig hn hw hK1)
    (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr rfl))))))
  have hen_ex : ∀ slot : Fin S, ∃ widx < I + c,
      ∀ x : Fin I → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD widx false = semEnable hn hw hK_lo hK1 slot x := by
    intro slot
    obtain ⟨widx, hwlt, hwval⟩ := hfind (semEnable hn hw hK_lo hK1 slot)
      (Or.inr (Or.inr (Or.inl ⟨slot, rfl⟩)))
    exact ⟨widx, by simpa using hwlt, hwval⟩
  have hmem_ex : ∀ (slot : Fin S) (lit : Literal (Fin n)), ∃ widx < I + c,
      ∀ x : Fin I → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD widx false = semMember hn hw hK_lo hK1 slot lit x := by
    intro slot lit
    obtain ⟨widx, hwlt, hwval⟩ := hfind (semMember hn hw hK_lo hK1 slot lit)
      (Or.inr (Or.inr (Or.inr ⟨slot, lit, rfl⟩)))
    exact ⟨widx, by simpa using hwlt, hwval⟩
  let enable : Fin S → Nat := fun slot => Classical.choose (hen_ex slot)
  let memberWire : Fin S → Literal (Fin n) → Nat := fun slot lit => Classical.choose (hmem_ex slot lit)
  let C : Circuit := ⟨gs, outW⟩
  refine ⟨C, enable, memberWire, hfan, hread, ?_, ?_, ?_, ?_, ?_⟩
  · change gs.length ≤ _; omega
  · change outW < I + gs.length; omega
  · intro slot; change enable slot < I + gs.length; rw [hgs, Nat.zero_add]; exact (Classical.choose_spec (hen_ex slot)).1
  · intro slot lit; change memberWire slot lit < I + gs.length; rw [hgs, Nat.zero_add]; exact (Classical.choose_spec (hmem_ex slot lit)).1
  · intro x
    refine ⟨?_, ?_, ?_⟩
    · change ((Circuit.mk gs 0).wires (List.ofFn x)).getD outW false = outSig hn hw hK1 x
      exact houtW_val x
    · intro slot; exact (Classical.choose_spec (hen_ex slot)).2 x
    · intro slot lit; exact (Classical.choose_spec (hmem_ex slot lit)).2 x

end Algo220

namespace Correct220

open Build220 Bitonic Algo220

def tableX {n w : Nat} (hn : 0 < n) (table : Fin n → (Fin (w + 1) → Bool) → Bool) :
    Fin (n * 2 ^ (w + 1)) → Bool :=
  fun a => table (posOf hn (a.val / 2 ^ (w + 1))) (fun bit => a.val.testBit bit.val)

theorem testBit_mul_two_pow_add (a b k i : Nat) (hi : i < k) :
    (a * 2 ^ k + b).testBit i = b.testBit i := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
  have hk : 2 ^ k = 2 ^ (k - i) * 2 ^ i := by
    rw [← Nat.pow_add, Nat.sub_add_cancel (Nat.le_of_lt hi)]
  have hdiv : (a * 2 ^ k + b) / 2 ^ i = a * 2 ^ (k - i) + b / 2 ^ i := by
    have hmul : a * 2 ^ k = 2 ^ i * (a * 2 ^ (k - i)) := by rw [hk]; ring
    rw [hmul, Nat.mul_add_div (Nat.pow_pos (by omega))]
  have heven : 2 ∣ 2 ^ (k - i) := by
    have h1 : k - i = (k - i - 1) + 1 := by omega
    rw [h1, Nat.pow_succ]
    exact Nat.dvd_mul_left 2 _
  rw [hdiv]
  rcases heven with ⟨q, hq⟩
  have h2 : a * 2 ^ (k - i) = 2 * (a * q) := by rw [hq]; ring
  rw [h2, Nat.mul_add_mod]

theorem readRow_tableX {n w : Nat} (hn : 0 < n) (table : Fin n → (Fin (w + 1) → Bool) → Bool)
    (r : Fin n) (pat : Fin (w + 1) → Bool) :
    readRow (tableX hn table) r pat = table r pat := by
  unfold readRow tableX
  set code := bitsVal (fun b => if h : b < w + 1 then pat ⟨b, h⟩ else false) (w + 1)
  have hcode_lt : code < 2 ^ (w + 1) := bitsVal_lt _ _
  have hdiv : (r.val * 2 ^ (w + 1) + code) / 2 ^ (w + 1) = r.val := by
    rw [Nat.mul_comm r.val (2 ^ (w + 1)), Nat.mul_add_div (Nat.pow_pos (by omega)),
        Nat.div_eq_of_lt hcode_lt, Nat.add_zero]
  have hpos : posOf hn ((r.val * 2 ^ (w + 1) + code) / 2 ^ (w + 1)) = r := by
    rw [hdiv]
    ext
    simp [posOf, Nat.mod_eq_of_lt r.isLt]
  have hpat : (fun bit : Fin (w + 1) => (r.val * 2 ^ (w + 1) + code).testBit bit.val) = pat := by
    funext bit
    rw [testBit_mul_two_pow_add r.val code (w + 1) bit.val bit.isLt, bitsVal_testBit _ (w + 1) bit.val bit.isLt]
    simp [bit.isLt]
  dsimp only
  rw [hpos, hpat]

def pairToLR {w : Nat} (p : Fin (2 * w) → Bool) : (Fin w → Bool) × (Fin w → Bool) :=
  (fun a => p ⟨a.val, by omega⟩, fun z => p ⟨w + z.val, by omega⟩)

def lrToPair {w : Nat} (q : (Fin w → Bool) × (Fin w → Bool)) : Fin (2 * w) → Bool :=
  fun k => if hk : k.val < w then q.1 ⟨k.val, hk⟩ else q.2 ⟨k.val - w, by omega⟩

theorem pairToLR_lrToPair {w : Nat} (q : (Fin w → Bool) × (Fin w → Bool)) :
    pairToLR (lrToPair q) = q := by
  rcases q with ⟨L, R⟩
  apply Prod.ext
  · funext a; simp [pairToLR, lrToPair, a.isLt]
  · funext z; simp [pairToLR, lrToPair, show ¬ w + z.val < w by omega]

theorem lrToPair_pairToLR {w : Nat} (p : Fin (2 * w) → Bool) :
    lrToPair (pairToLR p) = p := by
  funext k
  dsimp only [lrToPair, pairToLR]
  split_ifs with hk
  · rfl
  · congr 1; ext; dsimp; omega

theorem pairToLR_inj {w : Nat} {p1 p2 : Fin (2 * w) → Bool} (h : pairToLR p1 = pairToLR p2) :
    p1 = p2 := by
  rw [← lrToPair_pairToLR p1, ← lrToPair_pairToLR p2, h]

def reachedOf {n w : Nat} (hn : 0 < n) (table : Fin n → (Fin (w + 1) → Bool) → Bool) (h : Nat) :
    Finset ((Fin w → Bool) × (Fin w → Bool)) :=
  ((Finset.univ : Finset (Fin n → Bool)).filter (fun word =>
    ∀ t : Fin h, table (posOf hn t.val) (fun j => word (posOf hn (t.val + j.val))) = true)).image
    (fun x => ((fun a : Fin w => x (posOf hn a.val)), (fun z : Fin w => x (posOf hn (h + z.val)))))

theorem reached_consistent {n w : Nat} (hn : 0 < n) (hw : w ≤ n)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool) {h : Nat} (hh : h ≤ n - w)
    {p : Fin (2 * w) → Bool} (hp : pairToLR p ∈ reachedOf hn table h)
    (a z : Fin w) (heq : a.val = h + z.val) :
    p ⟨a.val, by omega⟩ = p ⟨w + z.val, by omega⟩ := by
  rcases Finset.mem_image.mp hp with ⟨word, _, hw_eq⟩
  have h1 := congrFun (congrArg Prod.fst hw_eq) a
  have h2 := congrFun (congrArg Prod.snd hw_eq) z
  dsimp only [pairToLR] at h1 h2
  rw [← h1, ← h2, heq]

theorem reached_zero_mem {n w : Nat} (hn : 0 < n) (hw : w ≤ n)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool) (q : (Fin w → Bool) × (Fin w → Bool)) :
    q ∈ reachedOf hn table 0 ↔ q.1 = q.2 := by
  constructor
  · intro hq
    rcases Finset.mem_image.mp hq with ⟨word, _, rfl⟩
    funext a; simp
  · intro heq
    apply Finset.mem_image.mpr
    let word : Fin n → Bool := fun v => if hv : v.val < w then q.1 ⟨v.val, hv⟩ else false
    refine ⟨word, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun t => t.elim0⟩, ?_⟩
    apply Prod.ext
    · funext a
      have ha : (posOf hn a.val).val = a.val := Nat.mod_eq_of_lt (by omega)
      simp [word, ha, a.isLt]
    · funext z
      have hz : (posOf hn (0 + z.val)).val = z.val := by simp [posOf, Nat.mod_eq_of_lt (by omega : z.val < n)]
      simp only [word, hz, z.isLt, ↓reduceDIte]
      exact congrFun heq z

theorem reached_succ_mem {n w : Nat} (hn : 0 < n) (hw : w ≤ n)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool) {h : Nat} (hh : h < n - w)
    (q : (Fin w → Bool) × (Fin w → Bool)) :
    q ∈ reachedOf hn table (h + 1) ↔
      ∃ p : Fin (2 * w) → Bool, pairToLR p ∈ reachedOf hn table h ∧
        ∃ b : Bool, table (posOf hn h) (extPat w p b) = true ∧ q = pairToLR (shiftPair w p b) := by
  constructor
  · intro hq
    rcases Finset.mem_image.mp hq with ⟨word, hword, rfl⟩
    have hsat := (Finset.mem_filter.mp hword).2
    let p : Fin (2 * w) → Bool := lrToPair (fun a => word (posOf hn a.val), fun z => word (posOf hn (h + z.val)))
    let b : Bool := word (posOf hn (h + w))
    refine ⟨p, ?_, b, ?_, ?_⟩
    · apply Finset.mem_image.mpr
      refine ⟨word, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun t => hsat ⟨t.val, by omega⟩⟩, ?_⟩
      exact (pairToLR_lrToPair _).symm
    · have hpat : extPat w p b = fun j : Fin (w + 1) => word (posOf hn (h + j.val)) := by
        funext j
        dsimp only [extPat, p, lrToPair]
        by_cases hj : j.val < w
        · simp only [hj, ↓reduceDIte, show ¬ w + j.val < w by omega, Nat.add_sub_cancel_left]
        · have hjw : j.val = w := by omega
          simp [hj, hjw, b]
      rw [hpat]
      exact hsat ⟨h, by omega⟩
    · apply Prod.ext
      · funext a
        simp [pairToLR, shiftPair, p, lrToPair, a.isLt]
      · funext z
        simp only [pairToLR, shiftPair, show ¬ w + z.val < w by omega, ↓reduceDIte]
        by_cases hz : w + z.val + 1 < 2 * w
        · simp only [hz, ↓reduceDIte, p, lrToPair, show ¬ w + z.val + 1 < w by omega]
          congr 2; omega
        · have hzw : z.val + 1 = w := by omega
          simp only [hz, ↓reduceDIte, b]
          congr 1; congr 1; omega
  · rintro ⟨p, hp, b, hok, rfl⟩
    rcases Finset.mem_image.mp hp with ⟨word, hword, hpeq⟩
    have hsat := (Finset.mem_filter.mp hword).2
    let word' : Fin n → Bool := fun v => if v.val = h + w then b else word v
    have hword'_lt : ∀ u < h + w, word' (posOf hn u) = word (posOf hn u) := by
      intro u hu
      have hmod : (posOf hn u).val = u := Nat.mod_eq_of_lt (by omega)
      simp [word', hmod, show u ≠ h + w by omega]
    have hword'_hw : word' (posOf hn (h + w)) = b := by
      have hmod : (posOf hn (h + w)).val = h + w := Nat.mod_eq_of_lt (by omega)
      simp [word', hmod]
    apply Finset.mem_image.mpr
    refine ⟨word', Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun t => ?_⟩, ?_⟩
    · by_cases ht : t.val < h
      · have heq : (fun j : Fin (w + 1) => word' (posOf hn (t.val + j.val))) =
            (fun j : Fin (w + 1) => word (posOf hn (t.val + j.val))) := by
          funext j; exact hword'_lt (t.val + j.val) (by omega)
        rw [heq]; exact hsat ⟨t.val, ht⟩
      · have hth : t.val = h := by omega
        rw [hth]
        have heq : (fun j : Fin (w + 1) => word' (posOf hn (h + j.val))) = extPat w p b := by
          funext j
          dsimp only [extPat]
          by_cases hj : j.val < w
          · simp only [hj, ↓reduceDIte]
            rw [hword'_lt (h + j.val) (by omega)]
            have h2 := congrFun (congrArg Prod.snd hpeq) ⟨j.val, hj⟩
            exact h2
          · have hjw : j.val = w := by omega
            rw [dite_neg hj, hjw]
            exact hword'_hw
        rw [heq]; exact hok
    · apply Prod.ext
      · funext a
        have h1 := congrFun (congrArg Prod.fst hpeq) a
        dsimp only [pairToLR, shiftPair]
        simp only [a.isLt, ↓reduceDIte]
        rw [hword'_lt a.val (by omega)]
        exact h1
      · funext z
        simp only [pairToLR, shiftPair, show ¬ w + z.val < w by omega, ↓reduceDIte]
        by_cases hz : w + z.val + 1 < 2 * w
        · simp only [hz, ↓reduceDIte]
          rw [hword'_lt (h + 1 + z.val) (by omega)]
          have h2 := congrFun (congrArg Prod.snd hpeq) ⟨z.val + 1, by omega⟩
          dsimp only [pairToLR] at h2
          have e1 : h + 1 + z.val = h + (z.val + 1) := by omega
          have e2 : (⟨w + (z.val + 1), by omega⟩ : Fin (2 * w)) = ⟨w + z.val + 1, hz⟩ := by ext; dsimp; omega
          rw [e1, h2, e2]
        · have hzw : h + 1 + z.val = h + w := by omega
          simp only [hz, ↓reduceDIte, hzw, hword'_hw]

theorem card_filter_replay (M : Nat) (sws : List (Nat × Nat × Bool))
    (hsws : ∀ c ∈ sws, c.1 < M ∧ c.2.1 < M) (f : Nat → Bool) :
    ((Finset.range M).filter (fun i => f (replaySwaps sws id i) = true)).card =
      ((Finset.range M).filter (fun i => f i = true)).card := by
  let p := replaySwaps sws id
  let pInv := replaySwaps sws.reverse id
  have hp_lt : ∀ i < M, p i < M := replaySwaps_lt M sws hsws id (fun i hi => hi)
  have hrev_sws : ∀ c ∈ sws.reverse, c.1 < M ∧ c.2.1 < M := fun c hc => hsws c (List.mem_reverse.mp hc)
  have hpInv_lt : ∀ i < M, pInv i < M := replaySwaps_lt M sws.reverse hrev_sws id (fun i hi => hi)
  have hp_pInv : ∀ i, p (pInv i) = i := by
    intro i
    have h1 := congrFun (replaySwaps_comp sws.reverse p id) i
    have h2 : replaySwaps sws.reverse (replaySwaps sws id) = id := replaySwaps_reverse_cancel sws id
    have h3 := congrFun h2 i
    dsimp [p, pInv] at h1 h3 ⊢
    rw [← h1, h3]
  have hpInv_p : ∀ i, pInv (p i) = i := by
    intro i
    have h1 := congrFun (replaySwaps_comp sws pInv id) i
    have h2 : replaySwaps sws (replaySwaps sws.reverse id) = id := by
      simpa only [List.reverse_reverse] using replaySwaps_reverse_cancel sws.reverse id
    have h3 := congrFun h2 i
    dsimp [p, pInv] at h1 h3 ⊢
    rw [← h1, h3]
  apply Finset.card_nbij p
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi ⊢
    exact ⟨hp_lt i hi.1, hi.2⟩
  · intro i1 _ i2 _ heq
    have := congrArg pInv heq
    rw [hpInv_p, hpInv_p] at this
    exact this
  · intro j hj
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hj
    refine ⟨pInv j, ?_, hp_pInv j⟩
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    refine ⟨hpInv_lt j hj.1, ?_⟩
    change f (p (pInv j)) = true
    rw [hp_pInv]; exact hj.2

theorem sortRecKey_s1_lt {w : Nat} (r1 r2 : SortRec (2 * w + 1) 0)
    (h1 : r1.keyBit (2 * w) = false) (h2 : r2.keyBit (2 * w) = true) :
    sortRecKey r1 < sortRecKey r2 := by
  unfold sortRecKey bitsVal
  rw [h1, h2]
  have hlt := bitsVal_lt r1.keyBit (2 * w)
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  omega

def FwdInv {n w K : Nat} (hn : 0 < n) (hK1 : 1 ≤ K)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool) (h : Nat) : Prop :=
  let st := fwdState hn hK1 h (tableX hn table)
  (∀ j : Fin K, st.val j = true → pairToLR (st.pair j) ∈ reachedOf hn table h) ∧
  (∀ q ∈ reachedOf hn table h, ∃ j : Fin K, st.val j = true ∧ pairToLR (st.pair j) = q) ∧
  (∀ j1 j2 : Fin K, st.val j1 = true → st.val j2 = true → st.pair j1 = st.pair j2 → j1 = j2)

theorem fwdInv_zero {n w K : Nat} (hn : 0 < n) (hw : w ≤ n) (hK_lo : 2 ^ w ≤ K) (hK1 : 1 ≤ K)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool) :
    FwdInv hn hK1 table 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    rw [reached_zero_mem hn hw table]
    funext a
    simp [fwdState, fwdInit, pairToLR, a.isLt, show ¬ w + a.val < w by omega]
  · intro q hq
    have hqeq := (reached_zero_mem hn hw table q).mp hq
    let code := bitsVal (fun a => if ha : a < w then q.1 ⟨a, ha⟩ else false) w
    have hlt : code < 2 ^ w := bitsVal_lt _ _
    refine ⟨⟨code, lt_of_lt_of_le hlt hK_lo⟩, by simp [fwdState, fwdInit, hlt], ?_⟩
    apply Prod.ext
    · funext a
      simp only [pairToLR, fwdState, fwdInit, a.isLt, ↓reduceIte]
      rw [bitsVal_testBit _ w a.val a.isLt]; simp [a.isLt]
    · funext z
      simp only [pairToLR, fwdState, fwdInit, show ¬ w + z.val < w by omega, ↓reduceIte,
        Nat.add_sub_cancel_left]
      rw [bitsVal_testBit _ w z.val z.isLt]; simp [z.isLt, hqeq]
  · intro j1 j2 hv1 hv2 hpeq
    have h1 : j1.val < 2 ^ w := by simpa [fwdState, fwdInit] using hv1
    have h2 : j2.val < 2 ^ w := by simpa [fwdState, fwdInit] using hv2
    ext
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < w
    · have hc := congrFun hpeq ⟨i, by omega⟩
      simpa [fwdState, fwdInit, hi] using hc
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega) (by omega))),
          Nat.testBit_lt_two_pow (lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by omega) (by omega)))]

theorem fwdStep_inv_and_bwd {n w K : Nat} (hn : 0 < n) (hw : w ≤ n) (hK1 : 1 ≤ K)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool) {h : Nat} (hh : h < n - w)
    (hinv : FwdInv hn hK1 table h) (hcard : (reachedOf hn table (h + 1)).card ≤ K) :
    FwdInv hn hK1 table (h + 1) ∧
    ∀ (mNext : Fin K → Fin (2 * w) → Bool) (j : Fin K) (b : Bool),
      (fwdState hn hK1 h (tableX hn table)).val j = true →
      (stepAt hn hK1 h (tableX hn table)).ok ⟨2 * j.val + b.toNat, by cases b <;> dsimp [Bool.toNat] <;> omega⟩ = true →
      ∃ j' : Fin K,
        (fwdState hn hK1 (h + 1) (tableX hn table)).val j' = true ∧
        (fwdState hn hK1 (h + 1) (tableX hn table)).pair j' =
          shiftPair w ((fwdState hn hK1 h (tableX hn table)).pair j) b ∧
        (runBwdStep hn hK1 h mNext (tableX hn table)).rev1 (2 * j.val + b.toNat) = mNext j' := by
  let x := tableX hn table
  let st := fwdState hn hK1 h x
  let sd := stepAt hn hK1 h x
  let M := sortM K
  have h2K_lt : 2 * K < M := two_mul_K_lt_sortM hK1
  have hnet_mem : ∀ c ∈ sortNet K, c.1 < M ∧ c.2.1 < M := by
    intro c hc; have hm := bitonicSort_mem 0 (sortDeg K) true c hc; dsimp [M, sortM]; omega
  let rec1 : Nat → SortRec (2 * w + 1) 0 := fun i =>
    ⟨fun j => if hj : j < 2 * w then sd.cpair i ⟨j, hj⟩ else !(sd.cval i), Fin.elim0⟩
  let rec2 : Nat → SortRec 1 (2 * w) := fun i =>
    ⟨fun _ => !(sd.isRep i), fun k => (sd.s1 i).keyBit k.val⟩
  have hsw1_mem : ∀ c ∈ sd.sw1, c.1 < M ∧ c.2.1 < M := netSwaps_mem_bound M sortRecKey (sortNet K) hnet_mem rec1
  have hsw2_mem : ∀ c ∈ sd.sw2, c.1 < M ∧ c.2.1 < M := netSwaps_mem_bound M sortRecKey (sortNet K) hnet_mem rec2
  let p1 := replaySwaps sd.sw1 id
  let p1Inv := replaySwaps sd.sw1.reverse id
  let p2 := replaySwaps sd.sw2 id
  let p2Inv := replaySwaps sd.sw2.reverse id
  have hp1_lt : ∀ i < M, p1 i < M := replaySwaps_lt M sd.sw1 hsw1_mem id (fun i hi => hi)
  have hp1Inv_lt : ∀ i < M, p1Inv i < M :=
    replaySwaps_lt M sd.sw1.reverse (fun c hc => hsw1_mem c (List.mem_reverse.mp hc)) id (fun i hi => hi)
  have hp2_lt : ∀ i < M, p2 i < M := replaySwaps_lt M sd.sw2 hsw2_mem id (fun i hi => hi)
  have hp2Inv_lt : ∀ i < M, p2Inv i < M :=
    replaySwaps_lt M sd.sw2.reverse (fun c hc => hsw2_mem c (List.mem_reverse.mp hc)) id (fun i hi => hi)
  have hp1_inv : ∀ i, p1 (p1Inv i) = i := fun i => by
    have h1 := congrFun (replaySwaps_comp sd.sw1.reverse p1 id) i
    have h2 := congrFun (replaySwaps_reverse_cancel sd.sw1 id) i
    dsimp [p1, p1Inv] at h1 h2 ⊢; rw [← h1, h2]
  have hp1Inv_inv : ∀ i, p1Inv (p1 i) = i := fun i => by
    have h1 := congrFun (replaySwaps_comp sd.sw1 p1Inv id) i
    have h2 := congrFun (by simpa only [List.reverse_reverse] using replaySwaps_reverse_cancel sd.sw1.reverse id) i
    dsimp [p1, p1Inv] at h1 h2 ⊢; rw [← h1, h2]
  have hp2_inv : ∀ i, p2 (p2Inv i) = i := fun i => by
    have h1 := congrFun (replaySwaps_comp sd.sw2.reverse p2 id) i
    have h2 := congrFun (replaySwaps_reverse_cancel sd.sw2 id) i
    dsimp [p2, p2Inv] at h1 h2 ⊢; rw [← h1, h2]
  have hp2Inv_inv : ∀ i, p2Inv (p2 i) = i := fun i => by
    have h1 := congrFun (replaySwaps_comp sd.sw2 p2Inv id) i
    have h2 := congrFun (by simpa only [List.reverse_reverse] using replaySwaps_reverse_cancel sd.sw2.reverse id) i
    dsimp [p2, p2Inv] at h1 h2 ⊢; rw [← h1, h2]
  have hs1_eq : ∀ i, sd.s1 i = rec1 (p1 i) := fun i => by
    have h1 : sd.s1 = replaySwaps sd.sw1 rec1 := runNet_eq_replay sortRecKey (sortNet K) rec1
    have h2 := congrFun (replaySwaps_comp sd.sw1 rec1 id) i
    dsimp [p1]; rw [h1]; exact h2
  have hs2_eq : ∀ i, sd.s2 i = rec2 (p2 i) := fun i => by
    have h1 : sd.s2 = replaySwaps sd.sw2 rec2 := runNet_eq_replay sortRecKey (sortNet K) rec2
    have h2 := congrFun (replaySwaps_comp sd.sw2 rec2 id) i
    dsimp [p2]; rw [h1]; exact h2
  have hs1_sorted : ∀ i j, i ≤ j → j < M → sortRecKey (sd.s1 i) ≤ sortRecKey (sd.s1 j) :=
    bitonicSort_sorted sortRecKey (sortDeg K) rec1
  have hs2_sorted : ∀ i j, i ≤ j → j < M → sortRecKey (sd.s2 i) ≤ sortRecKey (sd.s2 j) :=
    bitonicSort_sorted sortRecKey (sortDeg K) rec2
  have hok_eq : ∀ u : Fin (2 * K), sd.ok u =
      table (posOf hn h) (extPat w (st.pair ⟨u.val / 2, by omega⟩) (decide (u.val % 2 = 1))) :=
    fun u => readRow_tableX hn table _ _
  have hcval_reached : ∀ i, sd.cval i = true → pairToLR (sd.cpair i) ∈ reachedOf hn table (h + 1) := by
    intro i hi
    have hilt : i < 2 * K := by
      by_contra hge
      have : sd.cval i = false := by simp [sd, stepAt, runFwdStep, hge]
      rw [this] at hi; cases hi
    have hboth : st.val ⟨i / 2, by omega⟩ = true ∧ sd.ok ⟨i, hilt⟩ = true := by
      simpa [sd, stepAt, runFwdStep, hilt, Bool.and_eq_true] using hi
    rw [reached_succ_mem hn hw table hh]
    refine ⟨st.pair ⟨i / 2, by omega⟩, hinv.1 _ hboth.1, decide (i % 2 = 1), ?_, ?_⟩
    · rw [← hok_eq ⟨i, hilt⟩]; exact hboth.2
    · congr 1; funext k; simp [sd, stepAt, runFwdStep, hilt, st]
  have hs1_val_sound : ∀ i < M, (sd.s1 i).keyBit (2 * w) = false →
      pairToLR (fun k : Fin (2 * w) => (sd.s1 i).keyBit k.val) ∈ reachedOf hn table (h + 1) := by
    intro i _ hval
    rw [hs1_eq i] at hval ⊢
    have hc : sd.cval (p1 i) = true := by
      simp only [rec1, show ¬ 2 * w < 2 * w by omega, ↓reduceDIte, Bool.not_eq_false'] at hval
      exact hval
    have heq : (fun k : Fin (2 * w) => (rec1 (p1 i)).keyBit k.val) = sd.cpair (p1 i) := by
      funext k; simp [rec1, k.isLt]
    rw [heq]; exact hcval_reached (p1 i) hc
  have hs1_val_complete : ∀ q ∈ reachedOf hn table (h + 1),
      ∃ i < M, (sd.s1 i).keyBit (2 * w) = false ∧
        pairToLR (fun k : Fin (2 * w) => (sd.s1 i).keyBit k.val) = q := by
    intro q hq
    rcases (reached_succ_mem hn hw table hh q).mp hq with ⟨p, hp, b, hok, rfl⟩
    rcases hinv.2.1 _ hp with ⟨j, hjv, hjp⟩
    have hpeq : st.pair j = p := pairToLR_inj hjp
    let u := 2 * j.val + b.toNat
    have hu_lt : u < 2 * K := by have := j.isLt; cases b <;> dsimp [u, Bool.toNat] <;> omega
    have hu_div : u / 2 = j.val := by cases b <;> dsimp [u, Bool.toNat] <;> omega
    have hu_mod : decide (u % 2 = 1) = b := by cases b <;> simp [u]
    have hcval_u : sd.cval u = true := by
      simp only [sd, stepAt, runFwdStep, hu_lt, ↓reduceDIte, Bool.and_eq_true]
      refine ⟨by simpa [st, hu_div] using hjv, ?_⟩
      change sd.ok ⟨u, hu_lt⟩ = true
      rw [hok_eq ⟨u, hu_lt⟩]
      have hsub : (⟨u / 2, by omega⟩ : Fin K) = j := by ext; exact hu_div
      rw [hsub, hpeq, hu_mod]; exact hok
    let i := p1Inv u
    have hi_lt : i < M := hp1Inv_lt u (lt_trans hu_lt h2K_lt)
    refine ⟨i, hi_lt, ?_, ?_⟩
    · rw [hs1_eq i, hp1_inv u]; simp [rec1, hcval_u]
    · have heq : (fun k : Fin (2 * w) => (sd.s1 i).keyBit k.val) = shiftPair w p b := by
        funext k
        rw [hs1_eq i, hp1_inv u]
        simp only [rec1, k.isLt, ↓reduceDIte, sd, stepAt, runFwdStep, hu_lt]
        have hsub : (⟨u / 2, by omega⟩ : Fin K) = j := by ext; exact hu_div
        rw [hsub, hpeq, hu_mod]
      rw [heq]
  have hs1_pair_eq_iff : ∀ i1 i2,
      (List.finRange (2 * w)).any (fun k => xor ((sd.s1 i1).keyBit k.val) ((sd.s1 i2).keyBit k.val)) = false ↔
        (fun k : Fin (2 * w) => (sd.s1 i1).keyBit k.val) = (fun k : Fin (2 * w) => (sd.s1 i2).keyBit k.val) := by
    intro i1 i2
    constructor
    · intro hfalse
      funext k
      have hne := List.any_eq_false.mp hfalse k (List.mem_finRange k)
      cases h1 : (sd.s1 i1).keyBit k.val <;> cases h2 : (sd.s1 i2).keyBit k.val <;> simp [h1, h2] at hne ⊢
    · intro heq
      apply List.any_eq_false.mpr
      intro k _
      have := congrFun heq k
      rw [this]; cases (sd.s1 i2).keyBit k.val <;> decide
  have hrep_iff_min : ∀ i < M, sd.isRep i = true ↔
      (sd.s1 i).keyBit (2 * w) = false ∧
      ∀ t < i, (sd.s1 t).keyBit (2 * w) = false →
        (fun k : Fin (2 * w) => (sd.s1 t).keyBit k.val) ≠ (fun k : Fin (2 * w) => (sd.s1 i).keyBit k.val) := by
    intro i hi
    have hrep_def : sd.isRep i =
        (!((sd.s1 i).keyBit (2 * w)) &&
          (decide (i = 0) || (List.finRange (2 * w)).any (fun k => xor ((sd.s1 i).keyBit k.val) ((sd.s1 (i - 1)).keyBit k.val)))) := rfl
    rw [hrep_def]
    simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨hv, hi0 | hdiff⟩
      · refine ⟨hv, fun t ht _ => by omega⟩
      · refine ⟨hv, fun t ht htv heq => ?_⟩
        have hkey_eq : sortRecKey (sd.s1 t) = sortRecKey (sd.s1 i) := by
          dsimp only [sortRecKey]
          simp only [bitsVal, htv, hv]
          rw [bitsVal_ext (m := 2 * w) (fun k hk => congrFun heq ⟨k, hk⟩)]
        have hle1 := hs1_sorted t (i - 1) (by omega) (by omega)
        have hle2 := hs1_sorted (i - 1) i (by omega) hi
        have hmid : sortRecKey (sd.s1 (i - 1)) = sortRecKey (sd.s1 i) := by omega
        have hall := bitsVal_inj hmid
        have hp_eq : (fun k : Fin (2 * w) => (sd.s1 i).keyBit k.val) =
            (fun k : Fin (2 * w) => (sd.s1 (i - 1)).keyBit k.val) := by
          funext k; exact (hall k.val (by omega)).symm
        have hfalse := (hs1_pair_eq_iff i (i - 1)).mpr hp_eq
        rw [hfalse] at hdiff; cases hdiff
    · rintro ⟨hv, hmin⟩
      refine ⟨hv, ?_⟩
      by_cases hi0 : i = 0
      · exact Or.inl hi0
      · right
        cases hany : (List.finRange (2 * w)).any (fun k => xor ((sd.s1 i).keyBit k.val) ((sd.s1 (i - 1)).keyBit k.val))
        · exfalso
          have hpeq := (hs1_pair_eq_iff i (i - 1)).mp hany
          have hvprev : (sd.s1 (i - 1)).keyBit (2 * w) = false := by
            cases hvp : (sd.s1 (i - 1)).keyBit (2 * w)
            · rfl
            · have hlt := sortRecKey_s1_lt (sd.s1 i) (sd.s1 (i - 1)) hv hvp
              have hle := hs1_sorted (i - 1) i (by omega) hi
              omega
          exact hmin (i - 1) (by omega) hvprev hpeq.symm
        · exact rfl
  have hrep_unique_pair : ∀ i1 < M, ∀ i2 < M, sd.isRep i1 = true → sd.isRep i2 = true →
      (fun k : Fin (2 * w) => (sd.s1 i1).keyBit k.val) = (fun k : Fin (2 * w) => (sd.s1 i2).keyBit k.val) →
      i1 = i2 := by
    intro i1 h1 i2 h2 hr1 hr2 heq
    rcases (hrep_iff_min i1 h1).mp hr1 with ⟨hv1, hm1⟩
    rcases (hrep_iff_min i2 h2).mp hr2 with ⟨hv2, hm2⟩
    by_cases hlt1 : i1 < i2
    · exact False.elim (hm2 i1 hlt1 hv1 heq)
    · by_cases hlt2 : i2 < i1
      · exact False.elim (hm1 i2 hlt2 hv2 heq.symm)
      · omega
  have hrep_exists_le : ∀ i < M, (sd.s1 i).keyBit (2 * w) = false →
      ∃ i0 ≤ i, sd.isRep i0 = true ∧
        (fun k : Fin (2 * w) => (sd.s1 i0).keyBit k.val) = (fun k : Fin (2 * w) => (sd.s1 i).keyBit k.val) ∧
        ∀ t, i0 < t → t ≤ i → sd.isRep t = false := by
    intro i hi hv
    let S := (Finset.range (i + 1)).filter (fun t =>
      (sd.s1 t).keyBit (2 * w) = false ∧
      (fun k : Fin (2 * w) => (sd.s1 t).keyBit k.val) = (fun k : Fin (2 * w) => (sd.s1 i).keyBit k.val))
    have hne : S.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hv, rfl⟩⟩
    let i0 := S.min' hne
    have hi0_mem := Finset.mem_filter.mp (S.min'_mem hne)
    have hi0_le : i0 ≤ i := by have := Finset.mem_range.mp hi0_mem.1; omega
    have hi0_rep : sd.isRep i0 = true := by
      rw [hrep_iff_min i0 (by omega)]
      refine ⟨hi0_mem.2.1, fun t ht htv hteq => ?_⟩
      have ht_mem : t ∈ S := Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), htv, hteq.trans hi0_mem.2.2⟩
      have hle := S.min'_le t ht_mem
      omega
    refine ⟨i0, hi0_le, hi0_rep, hi0_mem.2.2, fun t ht1 ht2 => ?_⟩
    cases htr : sd.isRep t
    · rfl
    · exfalso
      have hkey_eq : sortRecKey (sd.s1 i0) = sortRecKey (sd.s1 i) := by
        unfold sortRecKey bitsVal
        rw [hi0_mem.2.1, hv]
        rw [bitsVal_ext (m := 2 * w) (fun k hk => congrFun hi0_mem.2.2 ⟨k, hk⟩)]
      have hle1 := hs1_sorted i0 t (by omega) (by omega)
      have hle2 := hs1_sorted t i ht2 hi
      have hmid : sortRecKey (sd.s1 t) = sortRecKey (sd.s1 i) := by omega
      have hall := bitsVal_inj hmid
      have hteq : (fun k : Fin (2 * w) => (sd.s1 t).keyBit k.val) =
          (fun k : Fin (2 * w) => (sd.s1 i).keyBit k.val) := by
        funext k; exact hall k.val (by omega)
      have := hrep_unique_pair i0 (by omega) t (by omega) hi0_rep htr (hi0_mem.2.2.trans hteq.symm)
      omega
  have hreps_card_le : ((Finset.range M).filter (fun i => sd.isRep i = true)).card ≤ K := by
    have hle_r : ((Finset.range M).filter (fun i => sd.isRep i = true)).card ≤ (reachedOf hn table (h + 1)).card := by
      apply Finset.card_le_card_of_injOn (fun i => pairToLR (fun k : Fin (2 * w) => (sd.s1 i).keyBit k.val))
      · intro i hi
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi
        have hv := ((hrep_iff_min i hi.1).mp hi.2).1
        exact Finset.mem_coe.mpr (hs1_val_sound i hi.1 hv)
      · intro i1 hi1 i2 hi2 heq
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi1 hi2
        exact hrep_unique_pair i1 hi1.1 i2 hi2.1 hi1.2 hi2.2 (pairToLR_inj heq)
    exact le_trans hle_r hcard
  have hs2_all_in_K : ∀ i < M, sd.isRep i = true → p2Inv i < K := by
    intro i hi hrep
    by_contra hge
    let idx := p2Inv i
    have hidx_lt : idx < M := hp2Inv_lt i hi
    have hidx_ge : K ≤ idx := Nat.le_of_not_lt hge
    have hs2_key0 : ∀ t ≤ idx, (sd.s2 t).keyBit 0 = false := by
      intro t ht
      have hle := hs2_sorted t idx ht hidx_lt
      have hk_idx : sortRecKey (sd.s2 idx) = 0 := by
        rw [hs2_eq idx, hp2_inv i]
        simp [rec2, hrep, sortRecKey, bitsVal]
      have hk_t : sortRecKey (sd.s2 t) = 0 := by omega
      cases hb : (sd.s2 t).keyBit 0
      · rfl
      · simp [sortRecKey, bitsVal, hb] at hk_t
    have hsub : Finset.range (K + 1) ⊆ (Finset.range M).filter (fun t => sd.isRep (p2 t) = true) := by
      intro t ht
      simp only [Finset.mem_range] at ht
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      have h0 := hs2_key0 t (by omega)
      rw [hs2_eq t] at h0
      simpa [rec2] using h0
    have hcard_ge : K + 1 ≤ ((Finset.range M).filter (fun t => sd.isRep (p2 t) = true)).card := by
      simpa using Finset.card_le_card hsub
    rw [card_filter_replay M sd.sw2 hsw2_mem sd.isRep] at hcard_ge
    omega
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro j hj
      have hj_lt : j.val < M := lt_trans (by omega : j.val < 2 * K) h2K_lt
      have hjr : sd.isRep (p2 j.val) = true := by
        have h1 : (sd.s2 j.val).keyBit 0 = false := by simpa [fwdState, sd, stepAt, runFwdStep] using hj
        rw [hs2_eq j.val] at h1; simpa [rec2] using h1
      have hp2_m : p2 j.val < M := hp2_lt j.val hj_lt
      have hv := ((hrep_iff_min (p2 j.val) hp2_m).mp hjr).1
      have hpair : (fwdState hn hK1 (h + 1) x).pair j = fun k : Fin (2 * w) => (sd.s1 (p2 j.val)).keyBit k.val := by
        change (sd.s2 j.val).valBit = _
        rw [hs2_eq j.val]
      rw [hpair]; exact hs1_val_sound (p2 j.val) hp2_m hv
    · intro q hq
      rcases hs1_val_complete q hq with ⟨i, hi, hv, hqi⟩
      rcases hrep_exists_le i hi hv with ⟨i0, hi0_le, hi0_rep, hi0_eq, _⟩
      have hj_lt : p2Inv i0 < K := hs2_all_in_K i0 (by omega) hi0_rep
      refine ⟨⟨p2Inv i0, hj_lt⟩, ?_, ?_⟩
      · change !((sd.s2 (p2Inv i0)).keyBit 0) = true
        rw [hs2_eq, hp2_inv i0]; simp [rec2, hi0_rep]
      · change pairToLR (sd.s2 (p2Inv i0)).valBit = q
        rw [hs2_eq, hp2_inv i0]
        change pairToLR (fun k : Fin (2 * w) => (sd.s1 i0).keyBit k.val) = q
        rw [hi0_eq, hqi]
    · intro j1 j2 hv1 hv2 hpeq
      have hj1_lt : j1.val < M := lt_trans (by omega : j1.val < 2 * K) h2K_lt
      have hj2_lt : j2.val < M := lt_trans (by omega : j2.val < 2 * K) h2K_lt
      have hr1 : sd.isRep (p2 j1.val) = true := by
        have h1 : (sd.s2 j1.val).keyBit 0 = false := by simpa [fwdState, sd, stepAt, runFwdStep] using hv1
        rw [hs2_eq j1.val] at h1; simpa [rec2] using h1
      have hr2 : sd.isRep (p2 j2.val) = true := by
        have h2 : (sd.s2 j2.val).keyBit 0 = false := by simpa [fwdState, sd, stepAt, runFwdStep] using hv2
        rw [hs2_eq j2.val] at h2; simpa [rec2] using h2
      have h1 : (fwdState hn hK1 (h + 1) x).pair j1 = fun k : Fin (2 * w) => (sd.s1 (p2 j1.val)).keyBit k.val := by
        change (sd.s2 j1.val).valBit = _; rw [hs2_eq j1.val]
      have h2 : (fwdState hn hK1 (h + 1) x).pair j2 = fun k : Fin (2 * w) => (sd.s1 (p2 j2.val)).keyBit k.val := by
        change (sd.s2 j2.val).valBit = _; rw [hs2_eq j2.val]
      rw [h1, h2] at hpeq
      have hp_eq := hrep_unique_pair (p2 j1.val) (hp2_lt j1.val hj1_lt) (p2 j2.val) (hp2_lt j2.val hj2_lt) hr1 hr2 hpeq
      ext
      have := congrArg p2Inv hp_eq
      rw [hp2Inv_inv, hp2Inv_inv] at this
      exact this
  · intro mNext j b hjv hokb
    let u := 2 * j.val + b.toNat
    have hu_lt : u < 2 * K := by have := j.isLt; cases b <;> dsimp [u, Bool.toNat] <;> omega
    have hu_div : u / 2 = j.val := by cases b <;> dsimp [u, Bool.toNat] <;> omega
    have hu_mod : decide (u % 2 = 1) = b := by cases b <;> simp [u]
    have hcval_u : sd.cval u = true := by
      simp only [sd, stepAt, runFwdStep, hu_lt, ↓reduceDIte, Bool.and_eq_true]
      exact ⟨by simpa [st, hu_div] using hjv, hokb⟩
    let i1 := p1Inv u
    have hi1_lt : i1 < M := hp1Inv_lt u (lt_trans hu_lt h2K_lt)
    have hi1_val : (sd.s1 i1).keyBit (2 * w) = false := by
      rw [hs1_eq i1, hp1_inv u]; simp [rec1, hcval_u]
    rcases hrep_exists_le i1 hi1_lt hi1_val with ⟨i0, hi0_le, hi0_rep, hi0_eq, hi0_mid⟩
    have hj'_lt : p2Inv i0 < K := hs2_all_in_K i0 (by omega) hi0_rep
    let j' : Fin K := ⟨p2Inv i0, hj'_lt⟩
    refine ⟨j', ?_, ?_, ?_⟩
    · change !((sd.s2 (p2Inv i0)).keyBit 0) = true
      rw [hs2_eq, hp2_inv i0]; simp [rec2, hi0_rep]
    · change (sd.s2 (p2Inv i0)).valBit = shiftPair w (st.pair j) b
      rw [hs2_eq, hp2_inv i0]
      change (fun k : Fin (2 * w) => (sd.s1 i0).keyBit k.val) = _
      rw [hi0_eq]
      funext k
      rw [hs1_eq i1, hp1_inv u]
      simp only [rec1, k.isLt, ↓reduceDIte, sd, stepAt, runFwdStep, hu_lt]
      have hsub : (⟨u / 2, by omega⟩ : Fin K) = j := by ext; exact hu_div
      rw [hsub, hu_mod]
    · let bd := runBwdStep hn hK1 h mNext x
      change bd.rev1 u = mNext j'
      have hrev1_u : bd.rev1 u = bd.copied i1 := by
        have h1 := congrFun (replaySwaps_comp sd.sw1.reverse bd.copied id) u
        exact h1
      have hcopy_i1 : bd.copied i1 = bd.rev2 i0 :=
        copyScan_spec sd.isRep bd.rev2 M i0 i1 hi0_le hi1_lt hi0_rep hi0_mid
      have hrev2_i0 : bd.rev2 i0 = mNext j' := by
        let u2 : Nat → Fin (2 * w) → Bool := fun i => if hi : i < K then mNext ⟨i, hi⟩ else fun _ => false
        have h1 := congrFun (replaySwaps_comp sd.sw2.reverse u2 id) i0
        change replaySwaps sd.sw2.reverse u2 i0 = mNext j'
        exact h1.trans (by dsimp only [u2]; exact dite_pos hj'_lt)
      rw [hrev1_u, hcopy_i1, hrev2_i0]

theorem fwdInv_all {n w K : Nat} (hn : 0 < n) (hw : w ≤ n) (hK_lo : 2 ^ w ≤ K) (hK1 : 1 ≤ K)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool)
    (hcard : ∀ h ≤ n - w, (reachedOf hn table h).card ≤ K) :
    ∀ h ≤ n - w, FwdInv hn hK1 table h := by
  intro h
  induction h with
  | zero => intro _; exact fwdInv_zero hn hw hK_lo hK1 table
  | succ h ih =>
    intro hh
    exact (fwdStep_inv_and_bwd hn hw hK1 table (by omega) (ih (by omega)) (hcard (h + 1) hh)).1

theorem firstBadScan_spec {n w K : Nat} (hn : 0 < n) (hw : w ≤ n) (hK1 : 1 ≤ K)
    (j : Fin K) (x : Fin (n * 2 ^ (w + 1)) → Bool) :
    ∀ t ≤ w,
      ((firstBadScan hn hw hK1 j x t).1 = true ↔ ∃ r : Fin w, r.val < t ∧ wrapOk hn hw hK1 r j x = false) ∧
      (∀ r : Fin w, r.val < t → (firstBadScan hn hw hK1 j x t).2 r.val = true → wrapOk hn hw hK1 r j x = false) ∧
      (∀ r1 r2 : Fin w, r1.val < t → r2.val < t →
        (firstBadScan hn hw hK1 j x t).2 r1.val = true →
        (firstBadScan hn hw hK1 j x t).2 r2.val = true → r1 = r2) ∧
      ((firstBadScan hn hw hK1 j x t).1 = true →
        ∃ r : Fin w, r.val < t ∧ (firstBadScan hn hw hK1 j x t).2 r.val = true) := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨by simp [firstBadScan], fun r hr => by omega, fun r1 _ hr1 => by omega, by simp [firstBadScan]⟩
  | succ t ih =>
    intro ht
    rcases ih (by omega) with ⟨h1, h2, h3, h4⟩
    have htw : t < w := by omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [firstBadScan, htw, ↓reduceDIte, Bool.or_eq_true, Bool.not_eq_true', h1]
      constructor
      · rintro (⟨r, hr, hbad⟩ | hbad)
        · exact ⟨r, by omega, hbad⟩
        · exact ⟨⟨t, htw⟩, Nat.lt_succ_self t, hbad⟩
      · rintro ⟨r, hr, hbad⟩
        by_cases hrt : r.val = t
        · right
          have hreq : r = ⟨t, htw⟩ := by ext; exact hrt
          rw [← hreq]; exact hbad
        · left; exact ⟨r, by omega, hbad⟩
    · intro r hr hpick
      simp only [firstBadScan, htw, ↓reduceDIte] at hpick
      by_cases hrt : r.val = t
      · simp only [hrt, ↓reduceIte, Bool.and_eq_true, Bool.not_eq_true'] at hpick
        have : r = ⟨t, htw⟩ := by ext; exact hrt
        rw [this]; exact hpick.2
      · simp only [hrt, ↓reduceIte] at hpick
        exact h2 r (by omega) hpick
    · intro r1 r2 hr1 hr2 hp1 hp2
      simp only [firstBadScan, htw, ↓reduceDIte] at hp1 hp2
      by_cases h1t : r1.val = t <;> by_cases h2t : r2.val = t
      · ext; omega
      · simp only [h1t, ↓reduceIte, Bool.and_eq_true, Bool.not_eq_true'] at hp1
        simp only [h2t, ↓reduceIte] at hp2
        have hb := h2 r2 (by omega) hp2
        have hf := h1.mpr ⟨r2, by omega, hb⟩
        rw [hf] at hp1; cases hp1.1
      · simp only [h1t, ↓reduceIte] at hp1
        simp only [h2t, ↓reduceIte, Bool.and_eq_true, Bool.not_eq_true'] at hp2
        have hb := h2 r1 (by omega) hp1
        have hf := h1.mpr ⟨r1, by omega, hb⟩
        rw [hf] at hp2; cases hp2.1
      · simp only [h1t, ↓reduceIte] at hp1
        simp only [h2t, ↓reduceIte] at hp2
        exact h3 r1 r2 (by omega) (by omega) hp1 hp2
    · intro hf
      simp only [firstBadScan, htw, ↓reduceDIte, Bool.or_eq_true, Bool.not_eq_true'] at hf
      cases hp : (firstBadScan hn hw hK1 j x t).1
      · rcases hf with hc | hbad
        · rw [hp] at hc; cases hc
        · refine ⟨⟨t, htw⟩, Nat.lt_succ_self t, ?_⟩
          simp [firstBadScan, htw, hp, hbad]
      · rcases h4 hp with ⟨r, hr, hpr⟩
        refine ⟨r, by omega, ?_⟩
        simp [firstBadScan, htw, show r.val ≠ t by omega, hpr]

def formulaOf {n w : Nat} (hn : 0 < n) (table : Fin n → (Fin (w + 1) → Bool) → Bool) :
    Set (Clause (Fin n)) :=
  {D | ∃ (i : Fin n) (p : Fin (w + 1) → Bool), table i p = false ∧
    D = Finset.univ.image (fun k : Fin (w + 1) => (posOf hn (i.val + k.val), !(p k)))}

theorem satisfiable_formulaOf_iff {n w : Nat} (hn : 0 < n)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool) :
    Satisfiable (formulaOf hn table) ↔
      ∃ word : Fin n → Bool, ∀ i : Fin n,
        table i (fun k : Fin (w + 1) => word (posOf hn (i.val + k.val))) = true := by
  constructor
  · rintro ⟨word, hsat⟩
    refine ⟨word, fun i => ?_⟩
    cases ht : table i (fun k : Fin (w + 1) => word (posOf hn (i.val + k.val)))
    · exfalso
      let D := Finset.univ.image (fun k : Fin (w + 1) =>
        (posOf hn (i.val + k.val), !(word (posOf hn (i.val + k.val)))))
      have hDF : D ∈ formulaOf hn table := ⟨i, _, ht, rfl⟩
      rcases hsat D hDF with ⟨lit, hlit, hval⟩
      rcases Finset.mem_image.mp hlit with ⟨k, _, rfl⟩
      dsimp only at hval
      cases h : word (posOf hn (i.val + k.val)) <;> rw [h] at hval <;> cases hval
    · rfl
  · rintro ⟨word, hok⟩
    refine ⟨word, fun D hDF => ?_⟩
    rcases hDF with ⟨i, p, hfalse, rfl⟩
    by_contra hall
    have hpeq : p = fun k : Fin (w + 1) => word (posOf hn (i.val + k.val)) := by
      funext k
      have hne : word (posOf hn (i.val + k.val)) ≠ !(p k) := fun heq =>
        hall ⟨(posOf hn (i.val + k.val), !(p k)), Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩, heq⟩
      cases hp : p k <;> cases hw' : word (posOf hn (i.val + k.val)) <;> simp [hp, hw'] at hne ⊢
    rw [hpeq, hok i] at hfalse; cases hfalse

theorem outSig_iff_unsat {n w K : Nat} (hn : 0 < n) (hw : w ≤ n) (hK_lo : 2 ^ w ≤ K) (hK1 : 1 ≤ K)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool)
    (hcard : ∀ h ≤ n - w, (reachedOf hn table h).card ≤ K) :
    outSig hn hw hK1 (tableX hn table) = true ↔ ¬ Satisfiable (formulaOf hn table) := by
  have hinv := fwdInv_all hn hw hK_lo hK1 table hcard (n - w) le_rfl
  rw [satisfiable_formulaOf_iff hn table]
  unfold outSig
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true, Bool.not_eq_true']
  constructor
  · rintro hall ⟨word, hword⟩
    let q : (Fin w → Bool) × (Fin w → Bool) :=
      (fun a => word (posOf hn a.val), fun z => word (posOf hn (n - w + z.val)))
    have hq : q ∈ reachedOf hn table (n - w) := by
      refine Finset.mem_image.mpr ⟨word, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun t => ?_⟩, rfl⟩
      have ht : (posOf hn t.val).val = t.val := Nat.mod_eq_of_lt (by omega)
      simpa [ht] using hword (posOf hn t.val)
    rcases hinv.2.1 q hq with ⟨j, hjv, hjp⟩
    rcases hall j with hfv | hbad
    · rw [hjv] at hfv; cases hfv
    · rcases (firstBadScan_spec hn hw hK1 j (tableX hn table) w le_rfl).1.mp hbad with ⟨r, _, hrok⟩
      have hrok' : table (posOf hn (n - w + r.val))
          (wrapPat n w (n - w + r.val) (by omega) (by omega) hw ((fwdState hn hK1 (n - w) (tableX hn table)).pair j)) = false := by
        simpa [wrapOk, readRow_tableX] using hrok
      have hpat : wrapPat n w (n - w + r.val) (by omega) (by omega) hw
          ((fwdState hn hK1 (n - w) (tableX hn table)).pair j) =
          fun k : Fin (w + 1) => word (posOf hn ((posOf hn (n - w + r.val)).val + k.val)) := by
        funext k
        have hrmod : (posOf hn (n - w + r.val)).val = n - w + r.val := Nat.mod_eq_of_lt (by omega)
        rw [hrmod]
        dsimp only [wrapPat]
        by_cases hlt : n - w + r.val + k.val < n
        · simp only [hlt, ↓reduceDIte]
          have h2 := congrFun (congrArg Prod.snd hjp) ⟨n - w + r.val + k.val - (n - w), by omega⟩
          dsimp only [pairToLR, q] at h2
          rw [h2]; congr 1; ext; dsimp [posOf]; congr 1; omega
        · simp only [hlt, ↓reduceDIte]
          have h1 := congrFun (congrArg Prod.fst hjp) ⟨n - w + r.val + k.val - n, by omega⟩
          dsimp only [pairToLR, q] at h1
          rw [h1]
          congr 1; ext; simp only [posOf]
          have hlt2 : n - w + r.val + k.val - n < n := by omega
          have hadd : n - w + r.val + k.val = (n - w + r.val + k.val - n) + n := by omega
          have hlhs : (n - w + r.val + k.val - n) % n = n - w + r.val + k.val - n := Nat.mod_eq_of_lt hlt2
          have hrhs : (n - w + r.val + k.val) % n = n - w + r.val + k.val - n :=
            (congrArg (· % n) hadd).trans ((Nat.add_mod_right _ _).trans hlhs)
          rw [hlhs, hrhs]
      rw [hpat, hword (posOf hn (n - w + r.val))] at hrok'
      cases hrok'
  · intro hunsat j
    cases hjv : (fwdState hn hK1 (n - w) (tableX hn table)).val j
    · exact Or.inl rfl
    · right
      cases htb : termBad hn hw hK1 j (tableX hn table)
      · exfalso
        have hq := hinv.1 j hjv
        rcases Finset.mem_image.mp hq with ⟨word, hword, hjp⟩
        have hsat := (Finset.mem_filter.mp hword).2
        apply hunsat
        refine ⟨word, fun i => ?_⟩
        by_cases hi : i.val < n - w
        · have hpos : posOf hn i.val = i := by ext; simp [posOf, Nat.mod_eq_of_lt i.isLt]
          have := hsat ⟨i.val, hi⟩
          simpa [hpos] using this
        · let r : Fin w := ⟨i.val - (n - w), by omega⟩
          have hr_eq : n - w + r.val = i.val := by dsimp [r]; omega
          have hpos : posOf hn (n - w + r.val) = i := by ext; simp [posOf, hr_eq, Nat.mod_eq_of_lt i.isLt]
          have hrok : wrapOk hn hw hK1 r j (tableX hn table) = true := by
            cases hok : wrapOk hn hw hK1 r j (tableX hn table)
            · have hb := (firstBadScan_spec hn hw hK1 j (tableX hn table) w le_rfl).1.mpr ⟨r, r.isLt, hok⟩
              change termBad hn hw hK1 j (tableX hn table) = true at hb
              rw [htb] at hb; cases hb
            · rfl
          have hrok' : table i
              (wrapPat n w (n - w + r.val) (by omega) (by omega) hw ((fwdState hn hK1 (n - w) (tableX hn table)).pair j)) = true := by
            simpa [wrapOk, readRow_tableX, hpos] using hrok
          have hpat : wrapPat n w (n - w + r.val) (by omega) (by omega) hw
              ((fwdState hn hK1 (n - w) (tableX hn table)).pair j) =
              fun k : Fin (w + 1) => word (posOf hn (i.val + k.val)) := by
            funext k
            dsimp only [wrapPat]
            by_cases hlt : n - w + r.val + k.val < n
            · simp only [hlt, ↓reduceDIte]
              have h2 := congrFun (congrArg Prod.snd hjp) ⟨n - w + r.val + k.val - (n - w), by omega⟩
              dsimp only [pairToLR] at h2
              rw [← h2]; congr 2; omega
            · simp only [hlt, ↓reduceDIte]
              have h1 := congrFun (congrArg Prod.fst hjp) ⟨n - w + r.val + k.val - n, by omega⟩
              dsimp only [pairToLR] at h1
              rw [← h1]
              congr 1; ext; simp only [posOf]
              have hlt2 : n - w + r.val + k.val - n < n := by omega
              have hadd : i.val + k.val = (n - w + r.val + k.val - n) + n := by omega
              rw [hadd, Nat.add_mod_right, Nat.mod_eq_of_lt hlt2]
          rw [hpat] at hrok'; exact hrok'
      · rfl

def pairClause {n w : Nat} (h : Nat) (pair mask : Fin (2 * w) → Bool) : Clause (Fin n) :=
  Finset.univ.filter (fun lit => pairClauseMem h pair mask lit = true)

def axBranchClause {n w : Nat} (h : Nat) (pair : Fin (2 * w) → Bool) (b : Bool) : Clause (Fin n) :=
  Finset.univ.filter (fun lit => axBranchMem h pair b lit = true)

def seedClause {n w : Nat} (d p : Nat) (hd : d ≤ w) (mask : Fin w → Bool) : Clause (Fin n) :=
  Finset.univ.filter (fun lit : Fin n × Bool =>
    (if hv : lit.1.val < d then
      if !(p.testBit lit.1.val) == lit.2 then mask ⟨lit.1.val, by omega⟩ else false
    else false) = true)

def semClause {n w K : Nat} (hn : 0 < n) (hw : w ≤ n) (hK_lo : 2 ^ w ≤ K) (hK1 : 1 ≤ K)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool) (s : Fin ((3 * (n - w) + 2) * K)) : Clause (Fin n) :=
  Finset.univ.filter (fun lit => semMember hn hw hK_lo hK1 s lit (tableX hn table) = true)

theorem not_beq_eq_true_iff (a b : Bool) : (!(a == b)) = true ↔ (!a) = b := by
  cases a <;> cases b <;> decide

theorem mem_pairClause {n w : Nat} {h : Nat} {pair mask : Fin (2 * w) → Bool} {lit : Literal (Fin n)} :
    lit ∈ pairClause (n := n) h pair mask ↔ pairClauseMem h pair mask lit = true := by
  rw [pairClause, Finset.mem_filter]; simp

theorem mem_axBranchClause {n w : Nat} {h : Nat} {pair : Fin (2 * w) → Bool} {b : Bool} {lit : Literal (Fin n)} :
    lit ∈ axBranchClause (n := n) h pair b ↔ axBranchMem h pair b lit = true := by
  rw [axBranchClause, Finset.mem_filter]; simp

theorem mem_seedClause {n w : Nat} {d p : Nat} {hd : d ≤ w} {mask : Fin w → Bool} {lit : Literal (Fin n)} :
    lit ∈ seedClause (n := n) d p hd mask ↔
      (if hv : lit.1.val < d then
        if !(p.testBit lit.1.val) == lit.2 then mask ⟨lit.1.val, by omega⟩ else false
      else false) = true := by
  rw [seedClause, Finset.mem_filter]; simp

theorem mem_semClause {n w K : Nat} {hn : 0 < n} {hw : w ≤ n} {hK_lo : 2 ^ w ≤ K} {hK1 : 1 ≤ K}
    {table : Fin n → (Fin (w + 1) → Bool) → Bool} {s : Fin ((3 * (n - w) + 2) * K)} {lit : Literal (Fin n)} :
    lit ∈ semClause hn hw hK_lo hK1 table s ↔ semMember hn hw hK_lo hK1 s lit (tableX hn table) = true := by
  rw [semClause, Finset.mem_filter]; simp

theorem pairClause_card_le {n w : Nat} (hw : w ≤ n) (h : Nat) (hh : h ≤ n - w)
    (pair mask : Fin (2 * w) → Bool) :
    (pairClause (n := n) h pair mask).card ≤ 2 * w := by
  let SL : Finset (Literal (Fin n)) :=
    (Finset.univ : Finset (Fin w)).image (fun a => (⟨a.val, by omega⟩, !(pair ⟨a.val, by omega⟩)))
  let SR : Finset (Literal (Fin n)) :=
    (Finset.univ : Finset (Fin w)).image (fun z => (⟨h + z.val, by omega⟩, !(pair ⟨w + z.val, by omega⟩)))
  have hsub : pairClause (n := n) h pair mask ⊆ SL ∪ SR := by
    intro ⟨v, pol⟩ hmem
    rw [mem_pairClause] at hmem
    simp only [pairClauseMem, Bool.or_eq_true] at hmem
    apply Finset.mem_union.mpr
    rcases hmem with hL | hR
    · by_cases hv : v.val < w
      · rw [dite_pos hv] at hL
        simp only [Bool.and_eq_true, not_beq_eq_true_iff] at hL
        left; apply Finset.mem_image.mpr
        refine ⟨⟨v.val, hv⟩, Finset.mem_univ _, Prod.ext (Fin.ext rfl) hL.2⟩
      · rw [dite_neg hv] at hL; cases hL
    · by_cases hv : h ≤ v.val ∧ v.val < h + w
      · rw [dite_pos hv] at hR
        simp only [Bool.and_eq_true, not_beq_eq_true_iff] at hR
        right; apply Finset.mem_image.mpr
        refine ⟨⟨v.val - h, by omega⟩, Finset.mem_univ _, Prod.ext (Fin.ext (by dsimp; omega)) hR.2⟩
      · rw [dite_neg hv] at hR; cases hR
  calc (pairClause (n := n) h pair mask).card
      ≤ (SL ∪ SR).card := Finset.card_le_card hsub
    _ ≤ SL.card + SR.card := Finset.card_union_le SL SR
    _ ≤ w + w := Nat.add_le_add (Finset.card_image_le.trans (by simp)) (Finset.card_image_le.trans (by simp))
    _ = 2 * w := by omega

theorem axBranchClause_card_le {n w : Nat} (h : Nat) (hh : h < n - w)
    (pair : Fin (2 * w) → Bool) (b : Bool) :
    (axBranchClause (n := n) h pair b).card ≤ w + 1 := by
  let S : Finset (Literal (Fin n)) :=
    (Finset.univ : Finset (Fin (w + 1))).image (fun k =>
      (⟨h + k.val, by omega⟩, !(extPat w pair b k)))
  have hsub : axBranchClause (n := n) h pair b ⊆ S := by
    intro ⟨v, pol⟩ hmem
    rw [mem_axBranchClause] at hmem
    dsimp only [axBranchMem] at hmem
    apply Finset.mem_image.mpr
    by_cases hv : h ≤ v.val ∧ v.val < h + w
    · rw [dite_pos hv, not_beq_eq_true_iff] at hmem
      refine ⟨⟨v.val - h, by omega⟩, Finset.mem_univ _, Prod.ext (Fin.ext (by dsimp; omega)) ?_⟩
      dsimp [extPat]; rw [dite_pos (show v.val - h < w by omega)]; exact hmem
    · rw [dite_neg hv] at hmem
      by_cases hvw : v.val = h + w
      · simp only [hvw, ↓reduceIte, beq_iff_eq] at hmem
        refine ⟨⟨w, by omega⟩, Finset.mem_univ _, Prod.ext (Fin.ext (by dsimp; omega)) ?_⟩
        dsimp [extPat]; rw [dite_neg (show ¬ w < w by omega)]; exact hmem
      · simp [hvw] at hmem
  calc (axBranchClause (n := n) h pair b).card
      ≤ S.card := Finset.card_le_card hsub
    _ ≤ w + 1 := Finset.card_image_le.trans (by simp)

theorem seedClause_card_le {n w : Nat} (hw : w ≤ n) (d p : Nat) (hd : d ≤ w) (mask : Fin w → Bool) :
    (seedClause (n := n) d p hd mask).card ≤ d := by
  let S : Finset (Literal (Fin n)) :=
    (Finset.univ : Finset (Fin d)).image (fun a => (⟨a.val, by omega⟩, !(p.testBit a.val)))
  have hsub : seedClause (n := n) d p hd mask ⊆ S := by
    intro ⟨v, pol⟩ hmem
    rw [mem_seedClause] at hmem
    by_cases hv : v.val < d
    · rw [dite_pos hv] at hmem
      by_cases hp : !(p.testBit v.val) == pol
      · apply Finset.mem_image.mpr
        refine ⟨⟨v.val, hv⟩, Finset.mem_univ _, Prod.ext (Fin.ext rfl) ((not_beq_eq_true_iff _ _).mp hp)⟩
      · simp [hp] at hmem
    · rw [dite_neg hv] at hmem; cases hmem
  calc (seedClause (n := n) d p hd mask).card
      ≤ S.card := Finset.card_le_card hsub
    _ ≤ d := Finset.card_image_le.trans (by simp)

theorem semClause_card_le {n w K : Nat} (hn : 0 < n) (hw : w ≤ n) (hK_lo : 2 ^ w ≤ K) (hK1 : 1 ≤ K)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool) (s : Fin ((3 * (n - w) + 2) * K)) :
    (semClause hn hw hK_lo hK1 table s).card ≤ 2 * w + 1 := by
  unfold semClause semMember
  by_cases hs1 : s.val < K
  · simp only [hs1, ↓reduceDIte]
    by_cases hs2 : s.val < 2 ^ w - 1
    · simp only [hs2, ↓reduceDIte]
      by_cases hd : Nat.log2 (s.val + 1) < w
      · simp only [hd, ↓reduceDIte]
        have := seedClause_card_le (n := n) hw (Nat.log2 (s.val + 1)) (s.val + 1 - 2 ^ Nat.log2 (s.val + 1)) (by omega)
          (seedMaskRem hn hw hK_lo hK1 (w - Nat.log2 (s.val + 1)) (tableX hn table) (s.val + 1 - 2 ^ Nat.log2 (s.val + 1)))
        exact le_trans this (by omega)
      · simp only [hd, ↓reduceDIte]
        simp
    · simp only [hs2, ↓reduceDIte]
      simp
  · simp only [hs1, ↓reduceDIte]
    by_cases hs3 : s.val < K + 3 * (n - w) * K
    · simp only [hs3, ↓reduceDIte]
      let off := s.val - K
      let h := off / (3 * K)
      have hh : h < n - w := by
        have hoff : off < (n - w) * (3 * K) := by
          have : 3 * (n - w) * K = (n - w) * (3 * K) := by ring
          dsimp [off]; omega
        exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
      by_cases hk0 : (off % (3 * K)) / K = 0
      · have h0 : (Finset.univ.filter (fun lit : Fin n × Bool =>
            (if (off % (3 * K)) / K = 0 then pairClauseMem h ((fwdState hn hK1 h (tableX hn table)).pair ⟨off % (3 * K) % K, Nat.mod_lt _ (by omega)⟩) (bwdMaskAt hn hw hK1 h (tableX hn table) ⟨off % (3 * K) % K, Nat.mod_lt _ (by omega)⟩) lit
            else if (off % (3 * K)) / K = 1 then axBranchMem h ((fwdState hn hK1 h (tableX hn table)).pair ⟨off % (3 * K) % K, Nat.mod_lt _ (by omega)⟩) false lit
            else axBranchMem h ((fwdState hn hK1 h (tableX hn table)).pair ⟨off % (3 * K) % K, Nat.mod_lt _ (by omega)⟩) true lit) = true)).card ≤ 2 * w + 1 := by
          simp only [hk0, ↓reduceIte]
          exact le_trans (pairClause_card_le hw h (by omega) _ _) (by omega)
        exact h0
      · by_cases hk1 : (off % (3 * K)) / K = 1
        · have h1 : (Finset.univ.filter (fun lit : Fin n × Bool =>
              (if (off % (3 * K)) / K = 0 then pairClauseMem h ((fwdState hn hK1 h (tableX hn table)).pair ⟨off % (3 * K) % K, Nat.mod_lt _ (by omega)⟩) (bwdMaskAt hn hw hK1 h (tableX hn table) ⟨off % (3 * K) % K, Nat.mod_lt _ (by omega)⟩) lit
              else if (off % (3 * K)) / K = 1 then axBranchMem h ((fwdState hn hK1 h (tableX hn table)).pair ⟨off % (3 * K) % K, Nat.mod_lt _ (by omega)⟩) false lit
              else axBranchMem h ((fwdState hn hK1 h (tableX hn table)).pair ⟨off % (3 * K) % K, Nat.mod_lt _ (by omega)⟩) true lit) = true)).card ≤ 2 * w + 1 := by
            simp only [hk0, hk1, ↓reduceIte]
            exact le_trans (axBranchClause_card_le h hh _ false) (by omega)
          exact h1
        · have h2 : (Finset.univ.filter (fun lit : Fin n × Bool =>
              (if (off % (3 * K)) / K = 0 then pairClauseMem h ((fwdState hn hK1 h (tableX hn table)).pair ⟨off % (3 * K) % K, Nat.mod_lt _ (by omega)⟩) (bwdMaskAt hn hw hK1 h (tableX hn table) ⟨off % (3 * K) % K, Nat.mod_lt _ (by omega)⟩) lit
              else if (off % (3 * K)) / K = 1 then axBranchMem h ((fwdState hn hK1 h (tableX hn table)).pair ⟨off % (3 * K) % K, Nat.mod_lt _ (by omega)⟩) false lit
              else axBranchMem h ((fwdState hn hK1 h (tableX hn table)).pair ⟨off % (3 * K) % K, Nat.mod_lt _ (by omega)⟩) true lit) = true)).card ≤ 2 * w + 1 := by
            simp only [hk0, hk1, ↓reduceIte]
            exact le_trans (axBranchClause_card_le h hh _ true) (by omega)
          exact h2
    · simp only [hs3, ↓reduceDIte]
      exact le_trans (pairClause_card_le hw (n - w) le_rfl _ _) (by omega)

theorem termClause_mem_F {n w K : Nat} (hn : 0 < n) (hw : w ≤ n) (hK1 : 1 ≤ K)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool) (j : Fin K)
    (hinv : FwdInv hn hK1 table (n - w))
    (hjv : (fwdState hn hK1 (n - w) (tableX hn table)).val j = true)
    (hbad : termBad hn hw hK1 j (tableX hn table) = true) :
    pairClause (n := n) (n - w)
      ((fwdState hn hK1 (n - w) (tableX hn table)).pair j)
      (termMask hn hw hK1 j (tableX hn table)) ∈ formulaOf hn table := by
  let x := tableX hn table
  let pair := (fwdState hn hK1 (n - w) x).pair j
  have hcons := reached_consistent hn hw table le_rfl (hinv.1 j hjv)
  have hspec := firstBadScan_spec hn hw hK1 j x w le_rfl
  rcases hspec.2.2.2 hbad with ⟨r, hr_lt, hpick_r⟩
  have hrok_false : wrapOk hn hw hK1 r j x = false := hspec.2.1 r hr_lt hpick_r
  have htab_false : table (posOf hn (n - w + r.val))
      (wrapPat n w (n - w + r.val) (by omega) (by omega) hw pair) = false := by
    have h1 := readRow_tableX hn table (posOf hn (n - w + r.val))
      (wrapPat n w (n - w + r.val) (by omega) (by omega) hw pair)
    rw [← h1]; exact hrok_false
  have hmask_eq : ∀ k : Fin (2 * w), termMask hn hw hK1 j x k = wrapUses n w r.val k := by
    intro k
    unfold termMask
    cases hw_use : wrapUses n w r.val k
    · apply List.any_eq_false.mpr
      intro r' hr'
      have hmem := List.mem_filter.mp hr'
      by_cases heq : r' = r
      · subst heq; rw [hw_use] at hmem; cases hmem.2
      · cases hp' : termPick hn hw hK1 j r' x
        · decide
        · exact False.elim (heq (hspec.2.2.1 r' r r'.isLt r.isLt hp' hpick_r))
    · apply List.any_eq_true.mpr
      exact ⟨r, List.mem_filter.mpr ⟨List.mem_finRange r, hw_use⟩, hpick_r⟩
  refine ⟨posOf hn (n - w + r.val), wrapPat n w (n - w + r.val) (by omega) (by omega) hw pair, htab_false, ?_⟩
  ext ⟨v, pol⟩
  rw [mem_pairClause]
  simp only [pairClauseMem, Finset.mem_image, Finset.mem_univ, true_and, Bool.or_eq_true]
  have hrmod : (posOf hn (n - w + r.val)).val = n - w + r.val := Nat.mod_eq_of_lt (by omega)
  constructor
  · rintro (hL | hR)
    · by_cases hv : v.val < w
      · rw [dite_pos hv] at hL
        simp only [Bool.and_eq_true, not_beq_eq_true_iff] at hL
        have hL1 := hL.1
        rw [show termMask hn hw hK1 j (tableX hn table) ⟨v.val, by omega⟩ = wrapUses n w r.val ⟨v.val, by omega⟩ from hmask_eq _] at hL1
        simp only [wrapUses, hv, ↓reduceIte, List.any_eq_true, List.mem_finRange, true_and,
          decide_eq_true_eq] at hL1
        rcases hL1 with ⟨o, ho1, ho2⟩
        refine ⟨o, Prod.ext (Fin.ext ?_) ?_⟩
        · rw [hrmod]; simp only [posOf]
          have hadd : n - w + r.val + o.val = v.val + n := by omega
          rw [hadd, Nat.add_mod_right, Nat.mod_eq_of_lt v.isLt]
        · dsimp only [wrapPat]
          rw [dite_neg (by omega)]
          have heq_idx : (⟨n - w + r.val + o.val - n, by omega⟩ : Fin (2 * w)) = ⟨v.val, by omega⟩ := by
            ext; dsimp; omega
          rw [heq_idx]; exact hL.2
      · rw [dite_neg hv] at hL; cases hL
    · by_cases hv : n - w ≤ v.val ∧ v.val < n - w + w
      · rw [dite_pos hv] at hR
        simp only [Bool.and_eq_true, not_beq_eq_true_iff] at hR
        have hR1 := hR.1
        rw [show termMask hn hw hK1 j (tableX hn table) ⟨w + (v.val - (n - w)), by omega⟩ = wrapUses n w r.val ⟨w + (v.val - (n - w)), by omega⟩ from hmask_eq _] at hR1
        simp only [wrapUses, show ¬ w + (v.val - (n - w)) < w by omega, ↓reduceIte,
          List.any_eq_true, List.mem_finRange, true_and, decide_eq_true_eq,
          Nat.add_sub_cancel_left] at hR1
        rcases hR1 with ⟨o, ho1, ho2⟩
        refine ⟨o, Prod.ext (Fin.ext ?_) ?_⟩
        · rw [hrmod]; simp only [posOf]
          rw [Nat.mod_eq_of_lt ho1]; omega
        · dsimp only [wrapPat]
          rw [dite_pos ho1]
          have heq_idx : (⟨w + (n - w + r.val + o.val - (n - w)), by omega⟩ : Fin (2 * w)) =
              ⟨w + (v.val - (n - w)), by omega⟩ := by ext; dsimp; omega
          rw [heq_idx]; exact hR.2
      · rw [dite_neg hv] at hR; cases hR
  · rintro ⟨o, ho⟩
    have hv_eq : (posOf hn ((posOf hn (n - w + r.val)).val + o.val)).val = v.val :=
      congrArg (fun l : Literal (Fin n) => l.1.val) ho
    have hpol_eq : (!wrapPat n w (n - w + r.val) (by omega) (by omega) hw pair o) = pol :=
      congrArg Prod.snd ho
    rw [hrmod] at hv_eq
    by_cases hlt : n - w + r.val + o.val < n
    · right
      have hv_val : v.val = n - w + r.val + o.val := by
        simpa [posOf, Nat.mod_eq_of_lt hlt] using hv_eq.symm
      have hv_bd : n - w ≤ v.val ∧ v.val < n - w + w := by omega
      rw [dite_pos hv_bd, Bool.and_eq_true, not_beq_eq_true_iff]
      refine ⟨?_, ?_⟩
      · rw [show termMask hn hw hK1 j (tableX hn table) ⟨w + (v.val - (n - w)), by omega⟩ = wrapUses n w r.val ⟨w + (v.val - (n - w)), by omega⟩ from hmask_eq _]
        simp only [wrapUses, show ¬ w + (v.val - (n - w)) < w by omega, ↓reduceIte,
          List.any_eq_true, List.mem_finRange, true_and, decide_eq_true_eq, Nat.add_sub_cancel_left]
        exact ⟨o, hlt, by omega⟩
      · dsimp only [wrapPat] at hpol_eq
        rw [dite_pos hlt] at hpol_eq
        have heq_idx : (⟨w + (v.val - (n - w)), by omega⟩ : Fin (2 * w)) =
            ⟨w + (n - w + r.val + o.val - (n - w)), by omega⟩ := by ext; dsimp; omega
        rw [heq_idx]; exact hpol_eq
    · left
      have hv_val : v.val = n - w + r.val + o.val - n := by
        have hlt2 : n - w + r.val + o.val - n < n := by omega
        have hadd : n - w + r.val + o.val = (n - w + r.val + o.val - n) + n := by omega
        simp only [posOf] at hv_eq
        rw [hadd, Nat.add_mod_right, Nat.mod_eq_of_lt hlt2] at hv_eq
        exact hv_eq.symm
      have hv_lt : v.val < w := by omega
      rw [dite_pos hv_lt, Bool.and_eq_true, not_beq_eq_true_iff]
      refine ⟨?_, ?_⟩
      · rw [show termMask hn hw hK1 j (tableX hn table) ⟨v.val, by omega⟩ = wrapUses n w r.val ⟨v.val, by omega⟩ from hmask_eq _]
        simp only [wrapUses, hv_lt, ↓reduceIte, List.any_eq_true, List.mem_finRange, true_and,
          decide_eq_true_eq]
        exact ⟨o, by omega, by omega⟩
      · dsimp only [wrapPat] at hpol_eq
        rw [dite_neg hlt] at hpol_eq
        have heq_idx : (⟨v.val, by omega⟩ : Fin (2 * w)) = ⟨n - w + r.val + o.val - n, by omega⟩ := by
          ext; dsimp; omega
        rw [heq_idx]; exact hpol_eq

theorem axBranchClause_mem_F {n w K : Nat} (hn : 0 < n) (hw : w ≤ n) (hK1 : 1 ≤ K)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool) {h : Nat} (hh : h < n - w)
    (j : Fin K) (b : Bool)
    (hok : (stepAt hn hK1 h (tableX hn table)).ok ⟨2 * j.val + b.toNat, by have := j.isLt; cases b <;> dsimp [Bool.toNat] <;> omega⟩ = false) :
    axBranchClause (n := n) h ((fwdState hn hK1 h (tableX hn table)).pair j) b ∈ formulaOf hn table := by
  let pair := (fwdState hn hK1 h (tableX hn table)).pair j
  have hu_div : (2 * j.val + b.toNat) / 2 = j.val := by cases b <;> dsimp [Bool.toNat] <;> omega
  have hu_mod : decide ((2 * j.val + b.toNat) % 2 = 1) = b := by cases b <;> simp
  have htab : table (posOf hn h) (extPat w pair b) = false := by
    have h1 := readRow_tableX hn table (posOf hn h) (extPat w pair b)
    have hsub : (⟨(2 * j.val + b.toNat) / 2, by have := j.isLt; cases b <;> dsimp [Bool.toNat] <;> omega⟩ : Fin K) = j := by ext; exact hu_div
    have hok' : readRow (tableX hn table) (posOf hn h)
        (extPat w ((fwdState hn hK1 h (tableX hn table)).pair ⟨(2 * j.val + b.toNat) / 2, by have := j.isLt; cases b <;> dsimp [Bool.toNat] <;> omega⟩)
          (decide ((2 * j.val + b.toNat) % 2 = 1))) = false := hok
    rw [hsub, hu_mod] at hok'
    rw [← h1]; exact hok'
  refine ⟨posOf hn h, extPat w pair b, htab, ?_⟩
  have hhmod : (posOf hn h).val = h := Nat.mod_eq_of_lt (by omega)
  ext ⟨v, pol⟩
  rw [mem_axBranchClause]
  simp only [axBranchMem, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hm
    by_cases hv : h ≤ v.val ∧ v.val < h + w
    · rw [dite_pos hv, not_beq_eq_true_iff] at hm
      refine ⟨⟨v.val - h, by omega⟩, Prod.ext (Fin.ext ?_) ?_⟩
      · rw [hhmod]; simp only [posOf]; rw [Nat.mod_eq_of_lt (by omega)]; omega
      · dsimp only [extPat]; rw [dite_pos (show v.val - h < w by omega)]; exact hm
    · rw [dite_neg hv] at hm
      by_cases hvw : v.val = h + w
      · simp only [hvw, ↓reduceIte, beq_iff_eq] at hm
        refine ⟨⟨w, by omega⟩, Prod.ext (Fin.ext ?_) ?_⟩
        · rw [hhmod]; simp only [posOf]; rw [Nat.mod_eq_of_lt (by omega)]; omega
        · dsimp only [extPat]; rw [dite_neg (show ¬ w < w by omega)]; exact hm
      · simp [hvw] at hm
  · rintro ⟨k, hk⟩
    have hv_eq : (posOf hn (h + k.val)).val = v.val := by
      have := congrArg (fun l : Literal (Fin n) => l.1.val) hk
      simpa [hhmod] using this
    have hv_val : v.val = h + k.val := by
      simpa [posOf, Nat.mod_eq_of_lt (by omega : h + k.val < n)] using hv_eq.symm
    have hpol_eq : (!extPat w pair b k) = pol := congrArg Prod.snd hk
    by_cases hkw : k.val < w
    · have hv : h ≤ v.val ∧ v.val < h + w := by omega
      rw [dite_pos hv, not_beq_eq_true_iff]
      dsimp only [extPat] at hpol_eq
      rw [dite_pos hkw] at hpol_eq
      have heq_idx : (⟨w + (v.val - h), by omega⟩ : Fin (2 * w)) = ⟨w + k.val, by omega⟩ := by
        ext; dsimp; omega
      rw [heq_idx]; exact hpol_eq
    · have hkw' : k.val = w := by omega
      have hv : ¬ (h ≤ v.val ∧ v.val < h + w) := by omega
      rw [dite_neg hv, if_pos (by omega), beq_iff_eq]
      dsimp only [extPat] at hpol_eq
      rw [dite_neg hkw] at hpol_eq
      exact hpol_eq

theorem branch_mem_iff {n w : Nat} (h : Nat) (hh : h < n - w)
    (pair : Fin (2 * w) → Bool) (b ok : Bool) (mChild : Fin (2 * w) → Bool)
    (lit : Fin n × Bool) :
    let bm : Fin (2 * w) → Bool := fun k =>
      if k.val < w then ok && mChild k
      else if k.val = w then !ok
      else !ok || mChild ⟨k.val - 1, by omega⟩
    let hasPiv : Bool := !ok || (if hw0 : 0 < w then mChild ⟨2 * w - 1, by omega⟩ else false)
    let Cbranch : Clause (Fin n) :=
      if ok then pairClause (n := n) (h + 1) (shiftPair w pair b) mChild
      else axBranchClause (n := n) h pair b
    (lit ∈ Cbranch ↔
      (lit.1.val ≠ h + w ∧ pairClauseMem h pair bm lit = true) ∨
      (lit.1.val = h + w ∧ hasPiv = true ∧ (!b) = lit.2)) := by
  intro bm hasPiv Cbranch
  rcases lit with ⟨v, pol⟩
  cases ok
  · simp only [Cbranch, Bool.false_eq_true, ↓reduceIte, mem_axBranchClause,
      axBranchMem, hasPiv, Bool.not_false, Bool.true_or, true_and]
    by_cases hvw : v.val = h + w
    · have hnr : ¬ (h ≤ v.val ∧ v.val < h + w) := by omega
      rw [dite_neg hnr, if_pos hvw]
      simp [hvw, beq_iff_eq]
    · by_cases hvr : h ≤ v.val ∧ v.val < h + w
      · rw [dite_pos hvr]
        simp only [hvw, ne_eq, not_false_eq_true, true_and, false_and, or_false,
          pairClauseMem, Bool.or_eq_true]
        constructor
        · intro heq
          right
          rw [dite_pos hvr, Bool.and_eq_true]
          refine ⟨?_, heq⟩
          dsimp only [bm]
          by_cases hz0 : v.val = h
          · simp [hz0]
          · simp [show ¬ w + (v.val - h) < w by omega, show w + (v.val - h) ≠ w by omega]
        · rintro (hL | hR)
          · by_cases hv : v.val < w
            · simp [hv, bm] at hL
            · simp [hv] at hL
          · rw [dite_pos hvr, Bool.and_eq_true] at hR
            exact hR.2
      · rw [dite_neg hvr, if_neg hvw]
        simp only [hvw, ne_eq, not_false_eq_true, true_and, false_and, or_false,
          pairClauseMem, Bool.or_eq_true]
        constructor
        · intro hc; cases hc
        · rintro (hL | hR)
          · by_cases hv : v.val < w
            · simp [hv, bm] at hL
            · simp [hv] at hL
          · simp [hvr] at hR
  · simp only [Cbranch, ↓reduceIte, mem_pairClause,
      pairClauseMem, Bool.or_eq_true, hasPiv, Bool.not_true, Bool.false_or]
    by_cases hvw : v.val = h + w
    · have hnl' : ¬ h + w < w := by omega
      simp only [hvw, hnl', ↓reduceDIte, Bool.false_eq_true, false_or, ne_eq, not_true_eq_false, false_and, true_and]
      by_cases hw0 : 0 < w
      · have hnr1 : h + 1 ≤ h + w ∧ h + w < h + 1 + w := by omega
        rw [dite_pos hnr1]
        simp only [hw0, ↓reduceDIte, Bool.and_eq_true, not_beq_eq_true_iff]
        have heq_idx : (⟨w + (h + w - (h + 1)), by omega⟩ : Fin (2 * w)) = ⟨2 * w - 1, by omega⟩ := by
          ext; dsimp; omega
        rw [heq_idx]
        dsimp only [shiftPair]
        simp only [show ¬ 2 * w - 1 < w by omega, show ¬ 2 * w - 1 + 1 < 2 * w by omega, ↓reduceDIte]
      · have hnr1 : ¬ (h + 1 ≤ h + w ∧ h + w < h + 1 + w) := by omega
        rw [dite_neg hnr1, dite_neg hw0]
        simp
    · simp only [hvw, ne_eq, not_false_eq_true, true_and, false_and, or_false]
      have hL_iff : (if hv : v.val < w then
            mChild ⟨v.val, by omega⟩ && (!(shiftPair w pair b ⟨v.val, by omega⟩) == pol) else false) = true ↔
          (if hv : v.val < w then bm ⟨v.val, by omega⟩ && (!(pair ⟨v.val, by omega⟩) == pol) else false) = true := by
        by_cases hv : v.val < w
        · simp [hv, shiftPair, bm]
        · simp [hv]
      have hR_iff : (if hv : h + 1 ≤ v.val ∧ v.val < h + 1 + w then
            mChild ⟨w + (v.val - (h + 1)), by omega⟩ &&
              (!(shiftPair w pair b ⟨w + (v.val - (h + 1)), by omega⟩) == pol) else false) = true ↔
          (if hv : h ≤ v.val ∧ v.val < h + w then
            bm ⟨w + (v.val - h), by omega⟩ && (!(pair ⟨w + (v.val - h), by omega⟩) == pol) else false) = true := by
        by_cases hv : h + 1 ≤ v.val ∧ v.val < h + w
        · have hv1 : h + 1 ≤ v.val ∧ v.val < h + 1 + w := by omega
          have hv0 : h ≤ v.val ∧ v.val < h + w := by omega
          rw [dite_pos hv1,
              dite_pos hv0]
          have h1 : ¬ w + (v.val - h) < w := by omega
          have h2 : w + (v.val - h) ≠ w := by omega
          have h3 : ¬ w + (v.val - (h + 1)) < w := by omega
          have h4 : w + (v.val - (h + 1)) + 1 < 2 * w := by omega
          dsimp only [bm, shiftPair]
          simp only [h1, h2, h3, h4, ↓reduceIte, ↓reduceDIte, Bool.not_true, Bool.false_or]
          have e1 : (⟨w + (v.val - h) - 1, by omega⟩ : Fin (2 * w)) = ⟨w + (v.val - (h + 1)), by omega⟩ := by
            ext; dsimp; omega
          have e2 : (⟨w + (v.val - (h + 1)) + 1, h4⟩ : Fin (2 * w)) = ⟨w + (v.val - h), by omega⟩ := by
            ext; dsimp; omega
          rw [e1, e2]
        · have hv1 : ¬ (h + 1 ≤ v.val ∧ v.val < h + 1 + w) := by omega
          rw [dite_neg hv1]
          by_cases hv0 : h ≤ v.val ∧ v.val < h + w
          · have hvh : v.val = h := by omega
            rw [dite_pos hv0]
            simp [bm, hvh]
          · rw [dite_neg hv0]
      rw [hL_iff, hR_iff]

theorem combMask_branch_step {n w : Nat} (hn : 0 < n) (hw : w ≤ n) (h : Nat) (hh : h < n - w)
    (pair m0 m1 : Fin (2 * w) → Bool) (ok0 ok1 : Bool) :
    let hasPos : Bool := !ok0 || (if hw0 : 0 < w then m0 ⟨2 * w - 1, by omega⟩ else false)
    let hasNeg : Bool := !ok1 || (if hw0 : 0 < w then m1 ⟨2 * w - 1, by omega⟩ else false)
    let bm0 : Fin (2 * w) → Bool := fun k =>
      if k.val < w then ok0 && m0 k else if k.val = w then !ok0 else !ok0 || m0 ⟨k.val - 1, by omega⟩
    let bm1 : Fin (2 * w) → Bool := fun k =>
      if k.val < w then ok1 && m1 k else if k.val = w then !ok1 else !ok1 || m1 ⟨k.val - 1, by omega⟩
    let mCur : Fin (2 * w) → Bool := fun k => combMask hasPos hasNeg (bm0 k) (bm1 k)
    let C0 : Clause (Fin n) := if ok0 then pairClause (n := n) (h + 1) (shiftPair w pair false) m0 else axBranchClause (n := n) h pair false
    let C1 : Clause (Fin n) := if ok1 then pairClause (n := n) (h + 1) (shiftPair w pair true) m1 else axBranchClause (n := n) h pair true
    let Ccur : Clause (Fin n) := pairClause (n := n) h pair mCur
    (hasPos = false → Ccur = C0) ∧
    (hasPos = true → hasNeg = false → Ccur = C1) ∧
    (hasPos = true → hasNeg = true → IsResolvent C0 C1 Ccur) := by
  intro hasPos hasNeg bm0 bm1 mCur C0 C1 Ccur
  have h0 : ∀ lit : Fin n × Bool, lit ∈ C0 ↔
      (lit.1.val ≠ h + w ∧ pairClauseMem h pair bm0 lit = true) ∨
      (lit.1.val = h + w ∧ hasPos = true ∧ (!false) = lit.2) :=
    branch_mem_iff (n := n) h hh pair false ok0 m0
  have h1 : ∀ lit : Fin n × Bool, lit ∈ C1 ↔
      (lit.1.val ≠ h + w ∧ pairClauseMem h pair bm1 lit = true) ∨
      (lit.1.val = h + w ∧ hasNeg = true ∧ (!true) = lit.2) :=
    branch_mem_iff (n := n) h hh pair true ok1 m1
  refine ⟨?_, ?_, ?_⟩
  · intro hhp
    ext ⟨v, pol⟩
    rw [mem_pairClause, h0 (v, pol)]
    simp only [hhp, Bool.false_eq_true, false_and, and_false, or_false]
    have hmeq : mCur = bm0 := by funext k; simp [mCur, combMask, hhp]
    rw [hmeq]
    constructor
    · intro hm
      have hne : v.val ≠ h + w := by
        intro heq
        simp only [pairClauseMem, Bool.or_eq_true, show ¬ v.val < w by omega,
          show ¬ (h ≤ v.val ∧ v.val < h + w) by omega, ↓reduceDIte] at hm
        cases hm <;> cases ‹false = true›
      exact ⟨hne, hm⟩
    · exact And.right
  · intro hhp hhn
    ext ⟨v, pol⟩
    rw [mem_pairClause, h1 (v, pol)]
    simp only [hhn, Bool.false_eq_true, false_and, and_false, or_false]
    have hmeq : mCur = bm1 := by funext k; simp [mCur, combMask, hhp, hhn]
    rw [hmeq]
    constructor
    · intro hm
      have hne : v.val ≠ h + w := by
        intro heq
        simp only [pairClauseMem, Bool.or_eq_true, show ¬ v.val < w by omega,
          show ¬ (h ≤ v.val ∧ v.val < h + w) by omega, ↓reduceDIte] at hm
        cases hm <;> cases ‹false = true›
      exact ⟨hne, hm⟩
    · exact And.right
  · intro hhp hhn
    let piv : Fin n := ⟨h + w, by omega⟩
    refine ⟨piv, ?_, ?_, ?_⟩
    · rw [h0 (piv, true)]; right; exact ⟨rfl, hhp, rfl⟩
    · rw [h1 (piv, false)]; right; exact ⟨rfl, hhn, rfl⟩
    · ext ⟨v, pol⟩
      rw [mem_pairClause]
      simp only [Finset.mem_union, Finset.mem_erase, ne_eq, Prod.mk.injEq]
      rw [h0 (v, pol), h1 (v, pol)]
      have hmeq : mCur = fun k => bm0 k || bm1 k := by funext k; simp [mCur, combMask, hhp, hhn]
      rw [hmeq]
      have hmem_or : pairClauseMem h pair (fun k => bm0 k || bm1 k) (v, pol) = true ↔
          pairClauseMem h pair bm0 (v, pol) = true ∨ pairClauseMem h pair bm1 (v, pol) = true := by
        simp only [pairClauseMem]
        by_cases h1' : v.val < w <;> by_cases h2' : h ≤ v.val ∧ v.val < h + w
        · simp only [h1', h2', and_self, ↓reduceDIte, Bool.or_eq_true, Bool.and_eq_true]; tauto
        · simp only [h1', h2', ↓reduceDIte, Bool.or_eq_true, Bool.and_eq_true, Bool.false_eq_true, or_false]; tauto
        · simp only [h1', h2', and_self, ↓reduceDIte, Bool.or_eq_true, Bool.and_eq_true, Bool.false_eq_true, false_or]; tauto
        · simp [h1', h2']
      rw [hmem_or]
      by_cases hvp : v.val = h + w
      · have hveq : v = piv := by ext; exact hvp
        have hnl : ¬ v.val < w := by omega
        have hnr : ¬ (h ≤ v.val ∧ v.val < h + w) := by omega
        have hf0 : pairClauseMem h pair bm0 (v, pol) = false := by simp [pairClauseMem, hnl, hnr]
        have hf1 : pairClauseMem h pair bm1 (v, pol) = false := by simp [pairClauseMem, hnl, hnr]
        rw [hf0, hf1, hveq]
        cases pol <;> simp [hvp, hhp, hhn, piv]
      · have hvne : v ≠ piv := fun hc => hvp (congrArg Fin.val hc)
        simp [hvp, hvne]

def rowSlot {n w K : Nat} (h kind : Nat) (j : Fin K) (hh : h < n - w) (hk : kind < 3) :
    Fin ((3 * (n - w) + 2) * K) :=
  ⟨K + (h * 3 + kind) * K + j.val, by
    have hK : j.val < K := j.isLt
    have h1 : h * 3 + kind + 1 ≤ 3 * (n - w) := by omega
    have h2 : (h * 3 + kind + 1) * K ≤ 3 * (n - w) * K := Nat.mul_le_mul_right K h1
    have h3 : (3 * (n - w) + 2) * K = K + 3 * (n - w) * K + K := by ring
    have h4 : (h * 3 + kind + 1) * K = (h * 3 + kind) * K + K := by ring
    omega⟩

def termSlot {n w K : Nat} (j : Fin K) : Fin ((3 * (n - w) + 2) * K) :=
  ⟨K + 3 * (n - w) * K + j.val, by
    have hK : j.val < K := j.isLt
    have h3 : (3 * (n - w) + 2) * K = K + 3 * (n - w) * K + K := by ring
    omega⟩

def seedSlot {n w K : Nat} (hK_lo : 2 ^ w ≤ K) (d p : Nat) (hd : d < w) (hp : p < 2 ^ d) :
    Fin ((3 * (n - w) + 2) * K) :=
  ⟨(2 ^ d - 1) + p, by
    have h1 : 2 ^ d + 2 ^ d = 2 ^ (d + 1) := by rw [Nat.pow_succ]; omega
    have h2 : 2 ^ (d + 1) ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : (2 ^ d - 1) + p < K := by
      have hpos : 1 ≤ 2 ^ d := Nat.one_le_two_pow
      omega
    have h4 : K ≤ (3 * (n - w) + 2) * K := by
      have : (3 * (n - w) + 2) * K = (3 * (n - w) + 1) * K + K := by ring
      omega
    omega⟩

theorem rowSlot_decode {n w K : Nat} (hK1 : 1 ≤ K) (h kind : Nat) (j : Fin K)
    (hh : h < n - w) (hk : kind < 3) :
    let s := rowSlot (n := n) (w := w) h kind j hh hk
    ¬ s.val < K ∧ s.val < K + 3 * (n - w) * K ∧
    (s.val - K) / (3 * K) = h ∧ ((s.val - K) % (3 * K)) / K = kind ∧
    ((s.val - K) % (3 * K)) % K = j.val := by
  dsimp only [rowSlot]
  have hK : j.val < K := j.isLt
  have h1 : h * 3 + kind + 1 ≤ 3 * (n - w) := by omega
  have h2 : (h * 3 + kind + 1) * K ≤ 3 * (n - w) * K := Nat.mul_le_mul_right K h1
  have h4 : (h * 3 + kind + 1) * K = (h * 3 + kind) * K + K := by ring
  have hsub : K + (h * 3 + kind) * K + j.val - K = (3 * K) * h + (K * kind + j.val) := by
    have : (h * 3 + kind) * K = (3 * K) * h + K * kind := by ring
    omega
  have hrem_lt : K * kind + j.val < 3 * K := by
    have : K * kind + K ≤ 3 * K := by
      calc K * kind + K = (kind + 1) * K := by ring
        _ ≤ 3 * K := Nat.mul_le_mul_right K (by omega)
    omega
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩
  · rw [hsub, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hrem_lt, Nat.add_zero]
  · rw [hsub, Nat.mul_add_mod, Nat.mod_eq_of_lt hrem_lt, Nat.mul_add_div (by omega),
        Nat.div_eq_of_lt hK, Nat.add_zero]
  · rw [hsub, Nat.mul_add_mod, Nat.mod_eq_of_lt hrem_lt, Nat.mul_add_mod, Nat.mod_eq_of_lt hK]

theorem seedSlot_decode {n w K : Nat} (hK_lo : 2 ^ w ≤ K) (d p : Nat) (hd : d < w) (hp : p < 2 ^ d) :
    let s := seedSlot (n := n) (w := w) hK_lo d p hd hp
    s.val < K ∧ s.val < 2 ^ w - 1 ∧
    Nat.log2 (s.val + 1) = d ∧ s.val + 1 - 2 ^ d = p := by
  dsimp only [seedSlot]
  have hpos : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  have h1 : 2 ^ d + 2 ^ d = 2 ^ (d + 1) := by rw [Nat.pow_succ]; omega
  have h2 : 2 ^ (d + 1) ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) (by omega)
  have hadd : (2 ^ d - 1) + p + 1 = 2 ^ d + p := by omega
  have hlog : Nat.log2 (2 ^ d + p) = d := by
    have hge : d ≤ Nat.log2 (2 ^ d + p) := (Nat.le_log2 (by omega)).mpr (by omega)
    have hlt : Nat.log2 (2 ^ d + p) < d + 1 := (Nat.log2_lt (by omega)).mpr (by omega)
    omega
  refine ⟨by omega, by omega, by rw [hadd, hlog], by omega⟩

theorem bwd_inv {n w K : Nat} (hn : 0 < n) (hw : w ≤ n) (hK_lo : 2 ^ w ≤ K) (hK1 : 1 ≤ K)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool)
    (hcard : ∀ h ≤ n - w, (reachedOf hn table h).card ≤ K)
    (hout : outSig hn hw hK1 (tableX hn table) = true) :
    ∀ rem ≤ n - w,
      let h := n - w - rem
      (∀ j : Fin K, (fwdState hn hK1 h (tableX hn table)).val j = true →
        ∃ s : Fin ((3 * (n - w) + 2) * K), K + 3 * h * K ≤ s.val ∧
          semEnable hn hw hK_lo hK1 s (tableX hn table) = true ∧
          semClause hn hw hK_lo hK1 table s =
            pairClause (n := n) h ((fwdState hn hK1 h (tableX hn table)).pair j)
              (bwdMaskRem hn hw hK1 rem (tableX hn table) j)) ∧
      (∀ s : Fin ((3 * (n - w) + 2) * K), K + 3 * h * K ≤ s.val →
        semEnable hn hw hK_lo hK1 s (tableX hn table) = true →
        semClause hn hw hK_lo hK1 table s ∈ formulaOf hn table ∨
        ∃ s1 s2 : Fin ((3 * (n - w) + 2) * K), s.val < s1.val ∧ s.val < s2.val ∧
          semEnable hn hw hK_lo hK1 s1 (tableX hn table) = true ∧
          semEnable hn hw hK_lo hK1 s2 (tableX hn table) = true ∧
          IsResolvent (semClause hn hw hK_lo hK1 table s1)
            (semClause hn hw hK_lo hK1 table s2) (semClause hn hw hK_lo hK1 table s)) := by
  let x := tableX hn table
  have hfwd_all := fwdInv_all hn hw hK_lo hK1 table hcard
  have hterm_all : ∀ j : Fin K, (fwdState hn hK1 (n - w) x).val j = true →
      termBad hn hw hK1 j x = true := by
    intro j hjv
    have h1 := List.all_eq_true.mp hout j (List.mem_finRange j)
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at h1
    rcases h1 with hfv | htb
    · rw [hjv] at hfv; cases hfv
    · exact htb
  intro rem
  induction rem with
  | zero =>
    intro _
    dsimp only [Nat.sub_zero]
    constructor
    · intro j hjv
      let s := termSlot (n := n) (w := w) j
      have htb := hterm_all j hjv
      refine ⟨s, by dsimp [s, termSlot]; omega, ?_, ?_⟩
      · have hs1 : ¬ s.val < K := by dsimp [s, termSlot]; omega
        have hs3 : ¬ s.val < K + 3 * (n - w) * K := by dsimp [s, termSlot]; omega
        have hj_eq : (⟨s.val - (K + 3 * (n - w) * K), by
            have hlt := s.isLt
            have heq : (3 * (n - w) + 2) * K = K + 3 * (n - w) * K + K := by ring
            omega⟩ : Fin K) = j := by ext; dsimp [s, termSlot]; omega
        simp [semEnable, hs1, hs3, hj_eq, hjv, htb, x]
      · have hs1 : ¬ s.val < K := by dsimp [s, termSlot]; omega
        have hs3 : ¬ s.val < K + 3 * (n - w) * K := by dsimp [s, termSlot]; omega
        have hj_eq : (⟨s.val - (K + 3 * (n - w) * K), by
            have hlt := s.isLt
            have heq : (3 * (n - w) + 2) * K = K + 3 * (n - w) * K + K := by ring
            omega⟩ : Fin K) = j := by ext; dsimp [s, termSlot]; omega
        ext lit
        rw [mem_semClause, mem_pairClause]
        simp [semMember, bwdMaskRem, hs1, hs3, hj_eq, x]
    · intro s hs_ge hen
      have hs1 : ¬ s.val < K := by omega
      have hs3 : ¬ s.val < K + 3 * (n - w) * K := by omega
      let j : Fin K := ⟨s.val - (K + 3 * (n - w) * K), by
        have hlt := s.isLt
        have heq : (3 * (n - w) + 2) * K = K + 3 * (n - w) * K + K := by ring
        omega⟩
      have hboth : (fwdState hn hK1 (n - w) x).val j = true ∧ termBad hn hw hK1 j x = true := by
        simpa [semEnable, hs1, hs3, j, Bool.and_eq_true, x] using hen
      left
      have hcl : semClause hn hw hK_lo hK1 table s =
          pairClause (n := n) (n - w) ((fwdState hn hK1 (n - w) x).pair j) (termMask hn hw hK1 j x) := by
        ext lit; rw [mem_semClause, mem_pairClause]; simp [semMember, hs1, hs3, j, x]
      rw [hcl]
      exact termClause_mem_F hn hw hK1 table j (hfwd_all (n - w) le_rfl) hboth.1 hboth.2
  | succ rem ih =>
    intro hrem
    rcases ih (by omega) with ⟨ih_ex, ih_just⟩
    let h := n - w - (rem + 1)
    have hh : h < n - w := by dsimp [h]; omega
    have hh1 : n - w - rem = h + 1 := by dsimp [h]; omega
    have hrem1 : n - w - (h + 1) = rem := by omega
    have hstep := fwdStep_inv_and_bwd hn hw hK1 table hh (hfwd_all h (by omega)) (hcard (h + 1) (by omega))
    have hbranch_ex : ∀ (j : Fin K) (b : Bool),
        (fwdState hn hK1 h x).val j = true →
        let ok := (stepAt hn hK1 h x).ok ⟨2 * j.val + b.toNat, by have := j.isLt; cases b <;> dsimp [Bool.toNat] <;> omega⟩
        let bd := runBwdStep hn hK1 h (bwdMaskRem hn hw hK1 rem x) x
        let Cbranch : Clause (Fin n) :=
          if ok then pairClause (n := n) (h + 1) (shiftPair w ((fwdState hn hK1 h x).pair j) b) (bd.rev1 (2 * j.val + b.toNat))
          else axBranchClause (n := n) h ((fwdState hn hK1 h x).pair j) b
        ∃ sb : Fin ((3 * (n - w) + 2) * K),
          K + 3 * h * K + K ≤ sb.val ∧
          semEnable hn hw hK_lo hK1 sb x = true ∧
          semClause hn hw hK_lo hK1 table sb = Cbranch := by
      intro j b hjv
      dsimp only
      cases hok : (stepAt hn hK1 h x).ok ⟨2 * j.val + b.toNat, by have := j.isLt; cases b <;> dsimp [Bool.toNat] <;> omega⟩
      · simp only [Bool.false_eq_true, ↓reduceIte]
        let kind := if b then 2 else 1
        have hkind : kind < 3 := by cases b <;> simp [kind]
        let sb := rowSlot (n := n) (w := w) h kind j hh hkind
        have hdec : ¬ sb.val < K ∧ sb.val < K + 3 * (n - w) * K ∧
            (sb.val - K) / (3 * K) = h ∧ ((sb.val - K) % (3 * K)) / K = kind ∧
            ((sb.val - K) % (3 * K)) % K = j.val :=
          rowSlot_decode hK1 h kind j hh hkind
        refine ⟨sb, ?_, ?_, ?_⟩
        · dsimp [sb, rowSlot]
          have : (h * 3 + kind) * K = 3 * h * K + kind * K := by ring
          have : 1 * K ≤ kind * K := Nat.mul_le_mul_right K (by cases b <;> simp [kind])
          omega
        · cases b
          · simp only [semEnable, hdec.1, hdec.2.1, hdec.2.2.1, hdec.2.2.2.1, ↓reduceDIte, kind,
              Bool.false_eq_true, ↓reduceIte, show (1 : Nat) ≠ 0 by omega]
            have hjeq : (⟨(sb.val - K) % (3 * K) % K, Nat.mod_lt _ (by omega)⟩ : Fin K) = j := by
              ext; exact hdec.2.2.2.2
            have hjeq2 : (⟨2 * ((sb.val - K) % (3 * K) % K), by
                have := Nat.mod_lt ((sb.val - K) % (3 * K)) (by omega : 0 < K); omega⟩ : Fin (2 * K)) =
                ⟨2 * j.val + false.toNat, by have := j.isLt; dsimp [Bool.toNat]; omega⟩ := by
              ext; dsimp [Bool.toNat]; rw [hdec.2.2.2.2]
            rw [hjeq, hjeq2, hjv, hok]; rfl
          · simp only [semEnable, hdec.1, hdec.2.1, hdec.2.2.1, hdec.2.2.2.1, ↓reduceDIte, kind,
              ↓reduceIte, show (2 : Nat) ≠ 0 by omega, show (2 : Nat) ≠ 1 by omega]
            have hjeq : (⟨(sb.val - K) % (3 * K) % K, Nat.mod_lt _ (by omega)⟩ : Fin K) = j := by
              ext; exact hdec.2.2.2.2
            have hjeq2 : (⟨2 * ((sb.val - K) % (3 * K) % K) + 1, by
                have := Nat.mod_lt ((sb.val - K) % (3 * K)) (by omega : 0 < K); omega⟩ : Fin (2 * K)) =
                ⟨2 * j.val + true.toNat, by have := j.isLt; dsimp [Bool.toNat]; omega⟩ := by
              ext; dsimp [Bool.toNat]; rw [hdec.2.2.2.2]
            rw [hjeq, hjeq2, hjv, hok]; rfl
        · ext lit
          rw [mem_semClause, mem_axBranchClause]
          cases b
          · simp only [semMember, hdec.1, hdec.2.1, hdec.2.2.1, hdec.2.2.2.1, ↓reduceDIte, kind,
              Bool.false_eq_true, ↓reduceIte, show (1 : Nat) ≠ 0 by omega]
            have hjeq : (⟨(sb.val - K) % (3 * K) % K, Nat.mod_lt _ (by omega)⟩ : Fin K) = j := by
              ext; exact hdec.2.2.2.2
            rw [hjeq]
          · simp only [semMember, hdec.1, hdec.2.1, hdec.2.2.1, hdec.2.2.2.1, ↓reduceDIte, kind,
              ↓reduceIte, show (2 : Nat) ≠ 0 by omega, show (2 : Nat) ≠ 1 by omega]
            have hjeq : (⟨(sb.val - K) % (3 * K) % K, Nat.mod_lt _ (by omega)⟩ : Fin K) = j := by
              ext; exact hdec.2.2.2.2
            rw [hjeq]
      · simp only [↓reduceIte]
        rcases hstep.2 (bwdMaskRem hn hw hK1 rem x) j b hjv hok with ⟨j', hj'v, hj'p, hrev⟩
        rcases ih_ex j' (by simpa [hh1] using hj'v) with ⟨sb, hsb_ge, hsb_en, hsb_cl⟩
        refine ⟨sb, ?_, hsb_en, ?_⟩
        · rw [hh1] at hsb_ge
          have : 3 * (h + 1) * K = 3 * h * K + 3 * K := by ring
          omega
        · rw [hsb_cl, hh1, hj'p, hrev]
    constructor
    · intro j hjv
      let bd := runBwdStep hn hK1 h (bwdMaskRem hn hw hK1 rem x) x
      have hcomb := combMask_branch_step hn hw h hh ((fwdState hn hK1 h x).pair j)
        (bd.rev1 (2 * j.val)) (bd.rev1 (2 * j.val + 1))
        ((stepAt hn hK1 h x).ok ⟨2 * j.val, by omega⟩)
        ((stepAt hn hK1 h x).ok ⟨2 * j.val + 1, by omega⟩)
      cases hhp : bd.hasPos j
      · have hceq := hcomb.1 hhp
        rcases hbranch_ex j false hjv with ⟨s0, hs0_ge, hs0_en, hs0_cl⟩
        refine ⟨s0, by change K + 3 * h * K ≤ s0.val; omega, hs0_en, ?_⟩
        simp only [Bool.toNat_false, Nat.add_zero] at hs0_cl
        rw [hs0_cl, ← hceq]; rfl
      · cases hhn : bd.hasNeg j
        · have hceq := hcomb.2.1 hhp hhn
          rcases hbranch_ex j true hjv with ⟨s1, hs1_ge, hs1_en, hs1_cl⟩
          refine ⟨s1, by change K + 3 * h * K ≤ s1.val; omega, hs1_en, ?_⟩
          simp only [Bool.toNat_true] at hs1_cl
          rw [hs1_cl, ← hceq]; rfl
        · let s := rowSlot (n := n) (w := w) h 0 j hh (by omega)
          have hdec : ¬ s.val < K ∧ s.val < K + 3 * (n - w) * K ∧
              (s.val - K) / (3 * K) = h ∧ ((s.val - K) % (3 * K)) / K = 0 ∧
              ((s.val - K) % (3 * K)) % K = j.val :=
            rowSlot_decode hK1 h 0 j hh (by omega)
          have hjeq : (⟨(s.val - K) % (3 * K) % K, Nat.mod_lt _ (by omega)⟩ : Fin K) = j := by
            ext; exact hdec.2.2.2.2
          refine ⟨s, ?_, ?_, ?_⟩
          · change K + 3 * h * K ≤ s.val
            change K + 3 * h * K ≤ K + (h * 3 + 0) * K + j.val
            have hmul : (h * 3 + 0) * K = 3 * h * K := by ring
            rw [hmul]; omega
          · simp only [semEnable, hdec.1, hdec.2.1, hdec.2.2.1, hdec.2.2.2.1, ↓reduceDIte, ↓reduceIte,
              hjeq, bwdStepAt, hrem1]
            change (fwdState hn hK1 h x).val j && bd.hasPos j && bd.hasNeg j = true
            rw [hjv, hhp, hhn]; rfl
          · ext lit
            rw [mem_semClause, mem_pairClause]
            simp only [semMember, hdec.1, hdec.2.1, hdec.2.2.1, hdec.2.2.2.1, ↓reduceDIte, ↓reduceIte,
              hjeq, bwdMaskAt, x]
            have hrem0 : n - w - h = rem + 1 := by omega
            rw [hrem0]
    · intro s hs_ge hen
      change K + 3 * h * K ≤ s.val at hs_ge
      by_cases hs_next : K + 3 * (h + 1) * K ≤ s.val
      · exact ih_just s (by rw [hh1]; exact hs_next) hen
      · have hs1 : ¬ s.val < K := by omega
        have hs3 : s.val < K + 3 * (n - w) * K := by
          have : 3 * (h + 1) * K ≤ 3 * (n - w) * K := Nat.mul_le_mul_right K (by omega)
          omega
        let off := s.val - K
        have hoff_lo : 3 * h * K ≤ off := by dsimp [off]; omega
        have hoff_hi : off < 3 * (h + 1) * K := by dsimp [off]; omega
        have hh_eq : off / (3 * K) = h := by
          have h1 : off = (3 * K) * h + (off - (3 * K) * h) := by
            have : (3 * K) * h = 3 * h * K := by ring
            omega
          have h2 : off - (3 * K) * h < 3 * K := by
            have : (3 * K) * h = 3 * h * K := by ring
            have : 3 * (h + 1) * K = 3 * h * K + 3 * K := by ring
            omega
          rw [h1, Nat.mul_add_div (by omega), Nat.div_eq_of_lt h2, Nat.add_zero]
        let remK := off % (3 * K)
        let kind := remK / K
        let j : Fin K := ⟨remK % K, Nat.mod_lt _ (by omega)⟩
        by_cases hk0 : kind = 0
        · have hs_lt_branch : s.val < K + 3 * h * K + K := by
            have hrem_lt_K : remK < K := by
              have hdiv := Nat.div_add_mod remK K
              dsimp [kind] at hk0; rw [hk0, Nat.mul_zero, Nat.zero_add] at hdiv
              have := Nat.mod_lt remK (by omega : 0 < K)
              omega
            have hdiv2 := Nat.div_add_mod off (3 * K)
            rw [hh_eq] at hdiv2
            have : 3 * K * h = 3 * h * K := by ring
            dsimp [off, remK] at hdiv2 hrem_lt_K ⊢; omega
          have hen' : ((fwdState hn hK1 h x).val j && (bwdStepAt hn hw hK1 h x).hasPos j &&
              (bwdStepAt hn hw hK1 h x).hasNeg j) = true := by
            simpa [semEnable, hs1, hs3, off, hh_eq, remK, kind, j, hk0, x] using hen
          simp only [Bool.and_eq_true] at hen'
          rcases hen' with ⟨⟨hjv, hhp⟩, hhn⟩
          rw [bwdStepAt, hrem1] at hhp hhn
          rcases hbranch_ex j false hjv with ⟨s0, hs0_ge, hs0_en, hs0_cl⟩
          rcases hbranch_ex j true hjv with ⟨s1, hs1_ge, hs1_en, hs1_cl⟩
          have hcomb := combMask_branch_step hn hw h hh ((fwdState hn hK1 h x).pair j)
            ((runBwdStep hn hK1 h (bwdMaskRem hn hw hK1 rem x) x).rev1 (2 * j.val))
            ((runBwdStep hn hK1 h (bwdMaskRem hn hw hK1 rem x) x).rev1 (2 * j.val + 1))
            ((stepAt hn hK1 h x).ok ⟨2 * j.val, by omega⟩)
            ((stepAt hn hK1 h x).ok ⟨2 * j.val + 1, by omega⟩)
          have hres := hcomb.2.2 hhp hhn
          have hcl_s : semClause hn hw hK_lo hK1 table s =
              pairClause (n := n) h ((fwdState hn hK1 h x).pair j)
                (bwdMaskRem hn hw hK1 (rem + 1) x j) := by
            ext lit
            rw [mem_semClause, mem_pairClause]
            simp only [semMember, hs1, hs3, off, hh_eq, remK, kind, j, hk0, ↓reduceDIte, ↓reduceIte,
              bwdMaskAt, x]
            have hrem0 : n - w - h = rem + 1 := by omega
            rw [hrem0]
          right
          refine ⟨s0, s1, by omega, by omega, hs0_en, hs1_en, ?_⟩
          simp only [Bool.toNat_false, Nat.add_zero] at hs0_cl
          simp only [Bool.toNat_true] at hs1_cl
          rw [hs0_cl, hs1_cl, hcl_s]
          exact hres
        · by_cases hk1 : kind = 1
          · left
            have hen' : (fwdState hn hK1 h x).val j = true ∧
                (stepAt hn hK1 h x).ok ⟨2 * j.val, by omega⟩ = false := by
              simpa [semEnable, hs1, hs3, off, hh_eq, remK, kind, j, hk0, hk1, Bool.and_eq_true, x] using hen
            have hcl : semClause hn hw hK_lo hK1 table s =
                axBranchClause (n := n) h ((fwdState hn hK1 h x).pair j) false := by
              ext lit
              rw [mem_semClause, mem_axBranchClause]
              simp [semMember, hs1, hs3, off, hh_eq, remK, kind, j, hk0, hk1, x]
            rw [hcl]
            exact axBranchClause_mem_F hn hw hK1 table hh j false hen'.2
          · left
            have hen' : (fwdState hn hK1 h x).val j = true ∧
                (stepAt hn hK1 h x).ok ⟨2 * j.val + 1, by omega⟩ = false := by
              simpa [semEnable, hs1, hs3, off, hh_eq, remK, kind, j, hk0, hk1, Bool.and_eq_true, x] using hen
            have hcl : semClause hn hw hK_lo hK1 table s =
                axBranchClause (n := n) h ((fwdState hn hK1 h x).pair j) true := by
              ext lit
              rw [mem_semClause, mem_axBranchClause]
              simp [semMember, hs1, hs3, off, hh_eq, remK, kind, j, hk0, hk1, x]
            rw [hcl]
            exact axBranchClause_mem_F hn hw hK1 table hh j true hen'.2

theorem seed_comb_step {n w : Nat} (hw : w ≤ n) (d p : Nat) (hd : d < w) (hp : p < 2 ^ d)
    (m0 m1 : Fin w → Bool) :
    let hasPos := m0 ⟨d, hd⟩
    let hasNeg := m1 ⟨d, hd⟩
    let mCur : Fin w → Bool := fun a => if a.val < d then combMask hasPos hasNeg (m0 a) (m1 a) else false
    let C0 := seedClause (n := n) (d + 1) p (by omega) m0
    let C1 := seedClause (n := n) (d + 1) (p + 2 ^ d) (by omega) m1
    let Ccur := seedClause (n := n) d p (by omega) mCur
    (hasPos = false → Ccur = C0) ∧
    (hasPos = true → hasNeg = false → Ccur = C1) ∧
    (hasPos = true → hasNeg = true → IsResolvent C0 C1 Ccur) := by
  intro hasPos hasNeg mCur C0 C1 Ccur
  have hbit_lt : ∀ a < d, (p + 2 ^ d).testBit a = p.testBit a := by
    intro a ha
    rw [Nat.add_comm, Nat.testBit_two_pow_add_gt ha]
  have hbit_eq0 : p.testBit d = false := Nat.testBit_lt_two_pow hp
  have hbit_eq1 : (p + 2 ^ d).testBit d = true := by
    rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hp]; rfl
  refine ⟨?_, ?_, ?_⟩
  · intro hhp
    ext ⟨v, pol⟩
    simp only [Ccur, C0, seedClause, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hv : v.val < d
    · have hv1 : v.val < d + 1 := by omega
      simp only [hv, hv1, ↓reduceDIte, mCur, combMask, hhp, Bool.not_false, ↓reduceIte]
    · by_cases hvd : v.val = d
      · have hv1 : v.val < d + 1 := by omega
        have hm0 : m0 ⟨v.val, by omega⟩ = false := by
          have : (⟨v.val, by omega⟩ : Fin w) = ⟨d, hd⟩ := by ext; exact hvd
          rw [this]; exact hhp
        simp [hv, hv1, hm0]
      · have hv1 : ¬ v.val < d + 1 := by omega
        simp [hv, hv1]
  · intro hhp hhn
    ext ⟨v, pol⟩
    simp only [Ccur, C1, seedClause, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hv : v.val < d
    · have hv1 : v.val < d + 1 := by omega
      simp only [hv, hv1, ↓reduceDIte, mCur, combMask, hhp, hhn, Bool.not_true, Bool.not_false,
        Bool.false_eq_true, ↓reduceIte, hbit_lt v.val hv]
    · by_cases hvd : v.val = d
      · have hv1 : v.val < d + 1 := by omega
        have hm1 : m1 ⟨v.val, by omega⟩ = false := by
          have : (⟨v.val, by omega⟩ : Fin w) = ⟨d, hd⟩ := by ext; exact hvd
          rw [this]; exact hhn
        simp [hv, hv1, hm1]
      · have hv1 : ¬ v.val < d + 1 := by omega
        simp [hv, hv1]
  · intro hhp hhn
    let piv : Fin n := ⟨d, by omega⟩
    refine ⟨piv, ?_, ?_, ?_⟩
    · simp only [C0, seedClause, Finset.mem_filter, Finset.mem_univ, true_and, piv,
        show d < d + 1 by omega, ↓reduceDIte, hbit_eq0, Bool.not_false, beq_self_eq_true, ↓reduceIte]
      exact hhp
    · simp only [C1, seedClause, Finset.mem_filter, Finset.mem_univ, true_and, piv,
        show d < d + 1 by omega, ↓reduceDIte, hbit_eq1, Bool.not_true, beq_self_eq_true, ↓reduceIte]
      exact hhn
    · ext ⟨v, pol⟩
      simp only [Ccur, C0, C1, seedClause, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_union, Finset.mem_erase, ne_eq, Prod.mk.injEq]
      by_cases hv : v.val < d
      · have hv1 : v.val < d + 1 := by omega
        have hvne : v ≠ piv := fun hc => by have := congrArg Fin.val hc; dsimp [piv] at this; omega
        simp only [hv, hv1, hvne, false_and, not_false_eq_true, true_and, ↓reduceDIte, mCur,
          combMask, hhp, hhn, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hbit_lt v.val hv]
        by_cases hpol : !(p.testBit v.val) == pol
        · simp [hpol, Bool.or_eq_true]
        · simp [hpol]
      · by_cases hvd : v.val = d
        · have hveq : v = piv := by ext; exact hvd
          have hv1 : v.val < d + 1 := by omega
          rw [hveq]
          simp only [show ¬ piv.val < d by dsimp [piv]; omega, ↓reduceDIte, Bool.false_eq_true,
            show piv.val < d + 1 by dsimp [piv]; omega, true_and, piv, hbit_eq0, hbit_eq1]
          cases pol <;> simp
        · have hv1 : ¬ v.val < d + 1 := by omega
          simp [hv, hv1]

theorem seedClause_congr {n w : Nat} {d1 d2 p : Nat} (h : d1 = d2) (h1 : d1 ≤ w) (h2 : d2 ≤ w)
    (mask : Fin w → Bool) :
    seedClause (n := n) d1 p h1 mask = seedClause (n := n) d2 p h2 mask := by
  subst h; rfl

theorem seed_inv {n w K : Nat} (hn : 0 < n) (hw : w ≤ n) (hK_lo : 2 ^ w ≤ K) (hK1 : 1 ≤ K)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool)
    (hcard : ∀ h ≤ n - w, (reachedOf hn table h).card ≤ K)
    (hout : outSig hn hw hK1 (tableX hn table) = true) :
    ∀ rem ≤ w,
      let d := w - rem
      (∀ p < 2 ^ d,
        ∃ s : Fin ((3 * (n - w) + 2) * K),
          (if d = w then K else 2 ^ d - 1) ≤ s.val ∧
          semEnable hn hw hK_lo hK1 s (tableX hn table) = true ∧
          semClause hn hw hK_lo hK1 table s =
            seedClause (n := n) d p (by omega) (seedMaskRem hn hw hK_lo hK1 rem (tableX hn table) p)) ∧
      (∀ s : Fin ((3 * (n - w) + 2) * K), 2 ^ d - 1 ≤ s.val → s.val < K →
        semEnable hn hw hK_lo hK1 s (tableX hn table) = true →
        ∃ s1 s2 : Fin ((3 * (n - w) + 2) * K), s.val < s1.val ∧ s.val < s2.val ∧
          semEnable hn hw hK_lo hK1 s1 (tableX hn table) = true ∧
          semEnable hn hw hK_lo hK1 s2 (tableX hn table) = true ∧
          IsResolvent (semClause hn hw hK_lo hK1 table s1)
            (semClause hn hw hK_lo hK1 table s2) (semClause hn hw hK_lo hK1 table s)) := by
  let x := tableX hn table
  have hb0 := (bwd_inv hn hw hK_lo hK1 table hcard hout (n - w) le_rfl).1
  simp only [Nat.sub_self, Nat.mul_zero, Nat.zero_mul, Nat.add_zero] at hb0
  intro rem
  induction rem with
  | zero =>
    intro _
    simp only [Nat.sub_zero, ↓reduceIte]
    constructor
    · intro p hp
      have hpK : p < K := lt_of_lt_of_le hp hK_lo
      have hjv : (fwdState hn hK1 0 x).val ⟨p, hpK⟩ = true := by simp [fwdState, fwdInit, hp]
      rcases hb0 ⟨p, hpK⟩ hjv with ⟨s, hs_ge, hs_en, hs_cl⟩
      refine ⟨s, hs_ge, hs_en, ?_⟩
      rw [hs_cl]
      ext ⟨v, pol⟩
      simp only [pairClause, seedClause, Finset.mem_filter, Finset.mem_univ, true_and, pairClauseMem,
        Bool.or_eq_true, seedMaskRem, hpK, ↓reduceDIte]
      by_cases hv : v.val < w
      · have hv0 : 0 ≤ v.val ∧ v.val < 0 + w := by omega
        rw [dite_pos hv,
            dite_pos hv0]
        simp only [fwdState, fwdInit, hv, show ¬ w + (v.val - 0) < w by omega, ↓reduceIte,
          Nat.sub_zero, Nat.add_sub_cancel_left]
        by_cases hpol : !(p.testBit v.val) == pol
        · simp [hpol, Bool.or_eq_true]
        · simp [hpol]
      · have hv0 : ¬ (0 ≤ v.val ∧ v.val < 0 + w) := by omega
        simp [hv, hv0]
    · intro s hs_ge hs_lt hen
      have hs2 : ¬ s.val < 2 ^ w - 1 := by omega
      simp [semEnable, hs_lt, hs2] at hen
  | succ rem ih =>
    intro hrem
    rcases ih (by omega) with ⟨ih_ex, ih_just⟩
    let d := w - (rem + 1)
    have hd : d < w := by dsimp [d]; omega
    have hd1 : w - rem = d + 1 := by dsimp [d]; omega
    have hrem1 : w - (d + 1) = rem := by omega
    have hpow_add : 2 ^ d + 2 ^ d = 2 ^ (d + 1) := by rw [Nat.pow_succ]; omega
    have hchild_ge : ∀ (s : Fin ((3 * (n - w) + 2) * K)),
        (if d + 1 = w then K else 2 ^ (d + 1) - 1) ≤ s.val → 2 ^ (d + 1) - 1 ≤ s.val := by
      intro s hs
      by_cases hdw : d + 1 = w
      · simp only [hdw, ↓reduceIte] at hs; rw [hdw]; omega
      · simpa [hdw] using hs
    constructor
    · intro p hp
      have hp' : p < 2 ^ d := hp
      simp only [show w - (rem + 1) ≠ w by omega, ↓reduceIte]
      have hp0 : p < 2 ^ (w - rem) := by rw [hd1, ← hpow_add]; omega
      have hp1 : p + 2 ^ d < 2 ^ (w - rem) := by rw [hd1, ← hpow_add]; omega
      rcases ih_ex p hp0 with ⟨s0, hs0_ge, hs0_en, hs0_cl⟩
      rcases ih_ex (p + 2 ^ d) hp1 with ⟨s1, hs1_ge, hs1_en, hs1_cl⟩
      have hcomb := seed_comb_step (n := n) hw d p hd hp
        (seedMaskRem hn hw hK_lo hK1 rem x p) (seedMaskRem hn hw hK_lo hK1 rem x (p + 2 ^ d))
      have hm_eq : seedMaskRem hn hw hK_lo hK1 (rem + 1) x p =
          fun a => if a.val < d then combMask
            (seedMaskRem hn hw hK_lo hK1 rem x p ⟨d, hd⟩)
            (seedMaskRem hn hw hK_lo hK1 rem x (p + 2 ^ d) ⟨d, hd⟩)
            (seedMaskRem hn hw hK_lo hK1 rem x p a)
            (seedMaskRem hn hw hK_lo hK1 rem x (p + 2 ^ d) a) else false := by
        funext a; simp [seedMaskRem, d, hd]
      cases hhp : seedMaskRem hn hw hK_lo hK1 rem x p ⟨d, hd⟩
      · have hceq := hcomb.1 hhp
        have hge0 := hchild_ge s0 (by simpa [hd1] using hs0_ge)
        refine ⟨s0, by change 2 ^ d - 1 ≤ s0.val; omega, hs0_en, ?_⟩
        rw [hs0_cl, hm_eq, seedClause_congr hd1 _ (by omega)]; exact hceq.symm
      · cases hhn : seedMaskRem hn hw hK_lo hK1 rem x (p + 2 ^ d) ⟨d, hd⟩
        · have hceq := hcomb.2.1 hhp hhn
          have hge1 := hchild_ge s1 (by simpa [hd1] using hs1_ge)
          refine ⟨s1, by change 2 ^ d - 1 ≤ s1.val; omega, hs1_en, ?_⟩
          rw [hs1_cl, hm_eq, seedClause_congr hd1 _ (by omega)]; exact hceq.symm
        · let s := seedSlot (n := n) (w := w) hK_lo d p hd hp
          have hdec : s.val < K ∧ s.val < 2 ^ w - 1 ∧
              Nat.log2 (s.val + 1) = d ∧ s.val + 1 - 2 ^ d = p :=
            seedSlot_decode hK_lo d p hd hp
          refine ⟨s, by change 2 ^ d - 1 ≤ s.val; dsimp [s, seedSlot]; omega, ?_, ?_⟩
          · simp only [semEnable, hdec.1, hdec.2.1, hdec.2.2.1, hdec.2.2.2, hd, ↓reduceDIte,
              seedEn, hrem1, x]
            rw [hhp, hhn]; rfl
          · ext ⟨v, pol⟩
            rw [mem_semClause, mem_seedClause]
            simp only [semMember, hdec.1, hdec.2.1, hdec.2.2.1, hdec.2.2.2, hd, ↓reduceDIte, x]
            have hrem0 : w - d = rem + 1 := by omega
            rw [hrem0]
    · intro s hs_ge hs_lt hen
      change 2 ^ d - 1 ≤ s.val at hs_ge
      by_cases hs_hi : 2 ^ (d + 1) - 1 ≤ s.val
      · exact ih_just s (by rw [hd1]; exact hs_hi) hs_lt hen
      · have hs2 : s.val < 2 ^ w - 1 := by
          have : 2 ^ (d + 1) ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) (by omega)
          omega
        have hpos : 1 ≤ 2 ^ d := Nat.one_le_two_pow
        have hlog : Nat.log2 (s.val + 1) = d := by
          have hge : d ≤ Nat.log2 (s.val + 1) := (Nat.le_log2 (by omega)).mpr (by omega)
          have hlt : Nat.log2 (s.val + 1) < d + 1 := (Nat.log2_lt (by omega)).mpr (by omega)
          omega
        let p := s.val + 1 - 2 ^ d
        have hp : p < 2 ^ d := by dsimp [p]; omega
        have hen' : seedMaskRem hn hw hK_lo hK1 rem x p ⟨d, hd⟩ = true ∧
            seedMaskRem hn hw hK_lo hK1 rem x (p + 2 ^ d) ⟨d, hd⟩ = true := by
          simpa [semEnable, hs_lt, hs2, hlog, p, hd, seedEn, hrem1, Bool.and_eq_true, x] using hen
        have hp0 : p < 2 ^ (w - rem) := by rw [hd1, ← hpow_add]; omega
        have hp1 : p + 2 ^ d < 2 ^ (w - rem) := by rw [hd1, ← hpow_add]; omega
        rcases ih_ex p hp0 with ⟨s0, hs0_ge, hs0_en, hs0_cl⟩
        rcases ih_ex (p + 2 ^ d) hp1 with ⟨s1, hs1_ge, hs1_en, hs1_cl⟩
        have hge0 := hchild_ge s0 (by simpa [hd1] using hs0_ge)
        have hge1 := hchild_ge s1 (by simpa [hd1] using hs1_ge)
        have hcomb := seed_comb_step (n := n) hw d p hd hp
          (seedMaskRem hn hw hK_lo hK1 rem x p) (seedMaskRem hn hw hK_lo hK1 rem x (p + 2 ^ d))
        have hres := hcomb.2.2 hen'.1 hen'.2
        have hcl_s : semClause hn hw hK_lo hK1 table s =
            seedClause (n := n) d p (by omega)
              (fun a => if a.val < d then combMask
                (seedMaskRem hn hw hK_lo hK1 rem x p ⟨d, hd⟩)
                (seedMaskRem hn hw hK_lo hK1 rem x (p + 2 ^ d) ⟨d, hd⟩)
                (seedMaskRem hn hw hK_lo hK1 rem x p a)
                (seedMaskRem hn hw hK_lo hK1 rem x (p + 2 ^ d) a) else false) := by
          ext ⟨v, pol⟩
          rw [mem_semClause, mem_seedClause]
          have hrem0 : w - d = rem + 1 := by omega
          simp only [semMember, hs_lt, hs2, hlog, p, hd, ↓reduceDIte, hrem0, seedMaskRem, x]
          have : w - (rem + 1) = d := by omega
          simp [this, hd]
        refine ⟨s0, s1, by omega, by omega, hs0_en, hs1_en, ?_⟩
        rw [hs0_cl, hs1_cl, hcl_s, seedClause_congr hd1 _ (by omega), seedClause_congr hd1 _ (by omega)]
        exact hres

theorem isDerivation_of_suffix {V : Type} [DecidableEq V] {F : Set (Clause V)}
    {α : Type} (l : List α) (f : α → Clause V) (p : α → Bool)
    (h : ∀ (a : α) (rest : List α), (a :: rest) <:+ l → p a = true →
      f a ∈ F ∨ ∃ b ∈ rest, ∃ c ∈ rest, p b = true ∧ p c = true ∧ IsResolvent (f b) (f c) (f a)) :
    IsDerivation F ((l.filter p).map f) := by
  induction l with
  | nil => exact IsDerivation.nil
  | cons a rest ih =>
    have ih' : IsDerivation F ((rest.filter p).map f) :=
      ih (fun x r hsuf hp => h x r (hsuf.trans (List.suffix_cons a rest)) hp)
    cases hpa : p a
    · simp only [List.filter_cons, hpa, Bool.false_eq_true, ↓reduceIte]
      exact ih'
    · simp only [List.filter_cons, hpa, ↓reduceIte, List.map_cons]
      rcases h a rest List.suffix_rfl hpa with hax | ⟨b, hb, c, hc, hpb, hpc, hres⟩
      · exact IsDerivation.ax ih' hax
      · have hfb : f b ∈ (rest.filter p).map f :=
          List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨hb, hpb⟩, rfl⟩
        have hfc : f c ∈ (rest.filter p).map f :=
          List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨hc, hpc⟩, rfl⟩
        exact IsDerivation.res ih' hfb hfc hres

theorem mem_suffix_finRange_of_lt {S : Nat} {s s' : Fin S} {rest : List (Fin S)}
    (hsuf : (s :: rest) <:+ List.finRange S) (hlt : s.val < s'.val) : s' ∈ rest := by
  rcases hsuf with ⟨pre, hpre⟩
  have hmem : s' ∈ List.finRange S := List.mem_finRange s'
  rw [← hpre, List.mem_append, List.mem_cons] at hmem
  rcases hmem with hInPre | rfl | hInRest
  · exfalso
    have hsorted : (List.finRange S).Pairwise (fun a b : Fin S => a.val < b.val) := by
      rw [List.finRange_eq_pmap_range]
      apply List.Pairwise.pmap (R := (· < ·))
      · exact List.pairwise_lt_range
      · intro _ _ _ _ h; exact h
    rw [← hpre, List.pairwise_append] at hsorted
    have hlt' := hsorted.2.2 s' hInPre s List.mem_cons_self
    omega
  · omega
  · exact hInRest

theorem refutation_of_outSig {n w K : Nat} (hn : 0 < n) (hw : w ≤ n) (hK_lo : 2 ^ w ≤ K) (hK1 : 1 ≤ K)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool)
    (hcard : ∀ h ≤ n - w, (reachedOf hn table h).card ≤ K)
    (hout : outSig hn hw hK1 (tableX hn table) = true) :
    let S := (3 * (n - w) + 2) * K
    let lines := ((List.finRange S).filter (fun s => semEnable hn hw hK_lo hK1 s (tableX hn table))).map
      (semClause hn hw hK_lo hK1 table)
    IsRefutation (formulaOf hn table) lines ∧ ∀ D ∈ lines, D.card ≤ 2 * w + 1 := by
  have hb := (bwd_inv hn hw hK_lo hK1 table hcard hout (n - w) le_rfl).2
  simp only [Nat.sub_self, Nat.mul_zero, Nat.zero_mul, Nat.add_zero] at hb
  have hs := seed_inv hn hw hK_lo hK1 table hcard hout w le_rfl
  simp only [Nat.sub_self, Nat.pow_zero, Nat.sub_self] at hs
  constructor
  · constructor
    · apply isDerivation_of_suffix
      intro s rest hsuf hen
      by_cases hlt : s.val < K
      · rcases hs.2 s (Nat.zero_le _) hlt hen with ⟨s1, s2, hl1, hl2, he1, he2, hres⟩
        exact Or.inr ⟨s1, mem_suffix_finRange_of_lt hsuf hl1, s2, mem_suffix_finRange_of_lt hsuf hl2, he1, he2, hres⟩
      · rcases hb s (Nat.le_of_not_lt hlt) hen with hax | ⟨s1, s2, hl1, hl2, he1, he2, hres⟩
        · exact Or.inl hax
        · exact Or.inr ⟨s1, mem_suffix_finRange_of_lt hsuf hl1, s2, mem_suffix_finRange_of_lt hsuf hl2, he1, he2, hres⟩
    · rcases hs.1 0 (by norm_num) with ⟨s0, _, hs0_en, hs0_cl⟩
      have hempty : seedClause (n := n) 0 0 (Nat.zero_le w)
          (seedMaskRem hn hw hK_lo hK1 w (tableX hn table) 0) = ∅ := by
        ext ⟨v, pol⟩; simp [seedClause]
      rw [hempty] at hs0_cl
      exact List.mem_map.mpr ⟨s0, List.mem_filter.mpr ⟨List.mem_finRange s0, hs0_en⟩, hs0_cl⟩
  · intro D hD
    rcases List.mem_map.mp hD with ⟨s, _, rfl⟩
    exact semClause_card_le hn hw hK_lo hK1 table s

theorem main_proof : ∀ (n w K : ℕ) (hn : 0 < n), w ≤ n → 2 ^ w ≤ K → K ≤ 4 ^ w →
    let I := n * 2 ^ (w + 1)
    let S := (3 * (n - w) + 2) * K
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (enable : Fin S → ℕ)
      (memberWire : Fin S → PEqualNP.ProofComplexity.Literal (Fin n) → ℕ),
      PEqualNP.MetaComplexity.FanInTwo C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack I C ∧
      C.size ≤ 262144 * (n + 1) ^ 4 * K ∧ C.output < I + C.size ∧
      (∀ slot, enable slot < I + C.size) ∧
      (∀ slot lit, memberWire slot lit < I + C.size) ∧
      ∀ table : Fin n → (Fin (w + 1) → Bool) → Bool,
        let pos := fun (v : ℕ) => (⟨v % n, Nat.mod_lt _ hn⟩ : Fin n)
        let reached := fun (h : ℕ) =>
          ((Finset.univ : Finset (Fin n → Bool)).filter (fun word =>
            ∀ t : Fin h, table (pos t.val)
              (fun j => word (pos (t.val + j.val))) = true)).image
            (fun x => ((fun a : Fin w => x (pos a.val)),
                       (fun z : Fin w => x (pos (h + z.val)))))
        (∀ h ≤ n - w, (reached h).card ≤ K) →
        let inputs := List.ofFn (fun a : Fin I =>
          table (pos (a.val / 2 ^ (w + 1))) (fun bit => a.val.testBit bit.val))
        let F : Set (PEqualNP.ProofComplexity.Clause (Fin n)) :=
          {D | ∃ (i : Fin n) (p : Fin (w + 1) → Bool), table i p = false ∧
            D = Finset.univ.image (fun k : Fin (w + 1) => (pos (i.val + k.val), !(p k)))}
        let wireVal := fun wire : ℕ => (C.wires inputs).getD wire false
        let lines := ((List.finRange S).filter (fun s => wireVal (enable s))).map
          (fun s => Finset.univ.filter (fun lit => wireVal (memberWire s lit) = true))
        (C.eval inputs = true ↔ ¬ PEqualNP.ProofComplexity.Satisfiable F) ∧
          (C.eval inputs = true → PEqualNP.ProofComplexity.IsRefutation F lines ∧
            ∀ D ∈ lines, D.card ≤ 2 * w + 1) := by
  intro n w K hn hw hK_lo hK_hi
  have hK1 : 1 ≤ K := le_trans Nat.one_le_two_pow hK_lo
  obtain ⟨C, enable, memberWire, hfan, hread, hsize, hout_lt, hen_lt, hmem_lt, hspec⟩ :=
    build_full_circuit n w K hn hw hK_lo hK_hi
  refine ⟨C, enable, memberWire, hfan, hread, hsize, hout_lt, hen_lt, hmem_lt, ?_⟩
  intro table pos reached hcard
  have hcard' : ∀ h ≤ n - w, (reachedOf hn table h).card ≤ K := hcard
  rcases hspec (tableX hn table) with ⟨heval, hen, hmem⟩
  have hlines :
      ((List.finRange ((3 * (n - w) + 2) * K)).filter
        (fun s => (C.wires (List.ofFn (tableX hn table))).getD (enable s) false)).map
        (fun s => Finset.univ.filter (fun lit => (C.wires (List.ofFn (tableX hn table))).getD (memberWire s lit) false = true)) =
      ((List.finRange ((3 * (n - w) + 2) * K)).filter
        (fun s => semEnable hn hw hK_lo hK1 s (tableX hn table))).map
        (semClause hn hw hK_lo hK1 table) := by
    have hf1 : (fun s => (C.wires (List.ofFn (tableX hn table))).getD (enable s) false) =
        (fun s => semEnable hn hw hK_lo hK1 s (tableX hn table)) := funext hen
    have hf2 : (fun s => Finset.univ.filter (fun lit =>
          (C.wires (List.ofFn (tableX hn table))).getD (memberWire s lit) false = true)) =
        semClause hn hw hK_lo hK1 table := by
      funext s; ext lit
      rw [Finset.mem_filter, mem_semClause]
      simp only [Finset.mem_univ, true_and, hmem]
    rw [hf1, hf2]
  have hiff := outSig_iff_unsat hn hw hK_lo hK1 table hcard'
  constructor
  · change C.eval (List.ofFn (tableX hn table)) = true ↔ ¬ Satisfiable (formulaOf hn table)
    rw [heval]; exact hiff
  · intro hctrue
    change C.eval (List.ofFn (tableX hn table)) = true at hctrue
    rw [heval] at hctrue
    have href := refutation_of_outSig hn hw hK_lo hK1 table hcard' hctrue
    change IsRefutation (formulaOf hn table)
        (((List.finRange ((3 * (n - w) + 2) * K)).filter
          (fun s => (C.wires (List.ofFn (tableX hn table))).getD (enable s) false)).map
          (fun s => Finset.univ.filter (fun lit =>
            (C.wires (List.ofFn (tableX hn table))).getD (memberWire s lit) false = true))) ∧
      ∀ D ∈ (((List.finRange ((3 * (n - w) + 2) * K)).filter
          (fun s => (C.wires (List.ofFn (tableX hn table))).getD (enable s) false)).map
          (fun s => Finset.univ.filter (fun lit =>
            (C.wires (List.ofFn (tableX hn table))).getD (memberWire s lit) false = true))),
        D.card ≤ 2 * w + 1
    rw [hlines]
    exact href

end Correct220

end PEqualNP.Outside.L_pcx_220_aux

theorem PEqualNP.Outside.L_pcx_220 : (∀ (n w K : ℕ) (hn : 0 < n), w ≤ n → 2 ^ w ≤ K → K ≤ 4 ^ w →
  let I := n * 2 ^ (w + 1)
  let S := (3 * (n - w) + 2) * K
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (enable : Fin S → ℕ)
    (memberWire : Fin S → PEqualNP.ProofComplexity.Literal (Fin n) → ℕ),
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack I C ∧
    C.size ≤ 262144 * (n + 1) ^ 4 * K ∧ C.output < I + C.size ∧
    (∀ slot, enable slot < I + C.size) ∧
    (∀ slot lit, memberWire slot lit < I + C.size) ∧
    ∀ table : Fin n → (Fin (w + 1) → Bool) → Bool,
      let pos := fun (v : ℕ) => (⟨v % n, Nat.mod_lt _ hn⟩ : Fin n)
      let reached := fun (h : ℕ) =>
        ((Finset.univ : Finset (Fin n → Bool)).filter (fun word =>
          ∀ t : Fin h, table (pos t.val)
            (fun j => word (pos (t.val + j.val))) = true)).image
          (fun x => ((fun a : Fin w => x (pos a.val)),
                     (fun z : Fin w => x (pos (h + z.val)))))
      (∀ h ≤ n - w, (reached h).card ≤ K) →
      let inputs := List.ofFn (fun a : Fin I =>
        table (pos (a.val / 2 ^ (w + 1))) (fun bit => a.val.testBit bit.val))
      let F : Set (PEqualNP.ProofComplexity.Clause (Fin n)) :=
        {D | ∃ (i : Fin n) (p : Fin (w + 1) → Bool), table i p = false ∧
          D = Finset.univ.image (fun k : Fin (w + 1) => (pos (i.val + k.val), !(p k)))}
      let wireVal := fun wire : ℕ => (C.wires inputs).getD wire false
      let lines := ((List.finRange S).filter (fun s => wireVal (enable s))).map
        (fun s => Finset.univ.filter (fun lit => wireVal (memberWire s lit) = true))
      (C.eval inputs = true ↔ ¬ PEqualNP.ProofComplexity.Satisfiable F) ∧
        (C.eval inputs = true → PEqualNP.ProofComplexity.IsRefutation F lines ∧
          ∀ D ∈ lines, D.card ≤ 2 * w + 1)) :=
  PEqualNP.Outside.L_pcx_220_aux.Correct220.main_proof
