import PEqualNP.Defs

namespace PEqualNP.Outside.L_clb_100_aux

namespace GateBridge

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)

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

namespace Build049

open PEqualNP.CircuitLowerBounds

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

theorem finG {k : Nat} {A : Set (Sig n)} (F : Fin k → Sig n) (c : Nat)
    (H : ∀ i, Build A {F i} c) : Build A (Set.range F) (k * c) := by
  have h := listBuild (List.finRange k) F c (fun i _ => H i)
  rw [List.length_finRange] at h
  refine relax h le_rfl ?_ le_rfl
  rintro _ ⟨i, rfl⟩
  exact ⟨i, List.mem_finRange i, rfl⟩

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

end Build049

namespace Bitonic

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
    · dsimp only
      rw [Nat.pow_succ]
      omega
    · have h := bitonicMerge_mem off k asc c hc
      rw [Nat.pow_succ]
      omega
    · have h := bitonicMerge_mem (off + 2 ^ k) k asc c hc
      rw [Nat.pow_succ]
      omega

theorem bitonicSort_mem (off : Nat) : ∀ k asc c,
    c ∈ bitonicSort off k asc → off ≤ c.1 ∧ c.1 < c.2.1 ∧ c.2.1 < off + 2 ^ k
  | 0, _, c, hc => by simp [bitonicSort] at hc
  | k + 1, asc, c, hc => by
    simp only [bitonicSort, List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · have h := bitonicSort_mem off k true c hc
      rw [Nat.pow_succ]
      omega
    · have h := bitonicSort_mem (off + 2 ^ k) k false c hc
      rw [Nat.pow_succ]
      omega
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
      · simp [huv, Ne.symm huv]
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
            simp only [c1, c2, c1', c2', and_self, ↓reduceIte]
          · have c1' : ¬ (off ≤ idx ∧ idx < off + (m + 1)) := by omega
            have c2' : ¬ (off + h ≤ idx ∧ idx < off + h + (m + 1)) := by omega
            simp only [c1, c2, c1', c2', and_self, ↓reduceIte]

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
        · left
          intro i hi_lt
          rw [hg1_L i hi_lt]
          exact h3 i hi_lt
        · right
          intro i hi_lt
          rw [hg1_L i hi_lt]
          exact h3 i hi_lt
      | false =>
        rcases hsp.2.1 with ⟨s, e, h1, h2', h3⟩
        refine ⟨s, e, h1, h2', ?_⟩
        rcases h3 with h3 | h3
        · left
          intro i hi_lt
          have e1 : off + h + i - h = off + i := by omega
          have e2 : off + h + i = off + i + h := by omega
          have h3' := h3 i hi_lt
          dsimp only at h3'
          rw [e1, e2] at h3'
          rw [hg1_L i hi_lt]
          exact h3'
        · right
          intro i hi_lt
          have e1 : off + h + i - h = off + i := by omega
          have e2 : off + h + i = off + i + h := by omega
          have h3' := h3 i hi_lt
          dsimp only at h3'
          rw [e1, e2] at h3'
          rw [hg1_L i hi_lt]
          exact h3'
    have hright_bit : IsBitonic (off + h) h g2 := by
      have hg2_eq : ∀ i < h, g2 (off + h + i) = g1 (off + h + i) := by
        intro i hi_lt
        apply runNet_unchanged
        intro c hc
        have hm := bitonicMerge_mem off k asc c hc
        dsimp only [h] at hi_lt ⊢
        omega
      cases asc with
      | true =>
        rcases hsp.2.1 with ⟨s, e, h1, h2', h3⟩
        refine ⟨s, e, h1, h2', ?_⟩
        rcases h3 with h3 | h3
        · left
          intro i hi_lt
          rw [hg2_eq i hi_lt, hg1_R i hi_lt]
          exact h3 i hi_lt
        · right
          intro i hi_lt
          rw [hg2_eq i hi_lt, hg1_R i hi_lt]
          exact h3 i hi_lt
      | false =>
        rcases hsp.1 with ⟨s, e, h1, h2', h3⟩
        refine ⟨s, e, h1, h2', ?_⟩
        rcases h3 with h3 | h3
        · left
          intro i hi_lt
          have e1 : off + h + i - h = off + i := by omega
          have e2 : off + h + i = off + i + h := by omega
          rw [hg2_eq i hi_lt, hg1_R i hi_lt]
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [e1, e2]
          exact h3 i hi_lt
        · right
          intro i hi_lt
          have e1 : off + h + i - h = off + i := by omega
          have e2 : off + h + i = off + i + h := by omega
          rw [hg2_eq i hi_lt, hg1_R i hi_lt]
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [e1, e2]
          exact h3 i hi_lt
    have hsL : IsSortedBool off h asc g2 := bitonicMerge_sorted off k asc g1 hleft_bit
    have hsR : IsSortedBool (off + h) h asc g3 := bitonicMerge_sorted (off + h) k asc g2 hright_bit
    have hg3_left : ∀ i < h, g3 (off + i) = g2 (off + i) := by
      intro i hi_lt
      apply runNet_unchanged
      intro c hc
      have hm := bitonicMerge_mem (off + h) k asc c hc
      dsimp only [h] at hi_lt ⊢
      omega
    have hnetL : ∀ c ∈ bitonicMerge off k asc, off ≤ c.1 ∧ c.1 < off + h ∧ off ≤ c.2.1 ∧ c.2.1 < off + h := by
      intro c hc; have hm := bitonicMerge_mem off k asc c hc; dsimp [h]; omega
    have hnetR : ∀ c ∈ bitonicMerge (off + h) k asc,
        off + h ≤ c.1 ∧ c.1 < off + h + h ∧ off + h ≤ c.2.1 ∧ c.2.1 < off + h + h := by
      intro c hc; have hm := bitonicMerge_mem (off + h) k asc c hc; dsimp [h]; omega
    intro i j hij hj
    by_cases hjh : j < h
    · rw [hg3_left i (by omega), hg3_left j hjh]
      exact hsL i j hij hjh
    · by_cases hih : h ≤ i
      · have ei : off + i = off + h + (i - h) := by omega
        have ej : off + j = off + h + (j - h) := by omega
        rw [ei, ej]
        exact hsR (i - h) (j - h) (by omega) (by omega)
      · have hi_lt : i < h := by omega
        have hj_lt : j - h < h := by omega
        have ej : off + j = off + h + (j - h) := by omega
        rw [hg3_left i hi_lt, ej]
        cases asc with
        | true =>
          simp only [↓reduceIte]
          rcases hsp.2.2 with hlo | hhi
          · have hg1L : ∀ x < h, g1 (off + x) = false := by
              intro x hx
              rw [hg1_L x hx]
              exact hlo x hx
            have hg2i : g2 (off + i) = false :=
              runNet_bool_const (bitonicMerge off k true) off h false g1 hnetL hg1L i hi_lt
            intro ht; rw [hg2i] at ht; cases ht
          · have hg2R : ∀ x < h, g2 (off + h + x) = true := by
              intro x hx
              have heq : g2 (off + h + x) = g1 (off + h + x) := by
                apply runNet_unchanged; intro c hc; have hm := bitonicMerge_mem off k true c hc; dsimp [h] at hx ⊢; omega
              rw [heq, hg1_R x hx]
              exact hhi x hx
            intro _
            exact runNet_bool_const (bitonicMerge (off + h) k true) (off + h) h true g2 hnetR hg2R (j - h) hj_lt
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          rcases hsp.2.2 with hlo | hhi
          · have hg2R : ∀ x < h, g2 (off + h + x) = false := by
              intro x hx
              have heq : g2 (off + h + x) = g1 (off + h + x) := by
                apply runNet_unchanged; intro c hc; have hm := bitonicMerge_mem off k false c hc; dsimp [h] at hx ⊢; omega
              rw [heq, hg1_R x hx]
              simp only [Bool.false_eq_true, ↓reduceIte]
              have e1 : off + h + x - h = off + x := by omega
              have e2 : off + h + x = off + x + h := by omega
              rw [e1, e2]
              exact hlo x hx
            have hg3j : g3 (off + h + (j - h)) = false :=
              runNet_bool_const (bitonicMerge (off + h) k false) (off + h) h false g2 hnetR hg2R (j - h) hj_lt
            intro ht; rw [hg3j] at ht; cases ht
          · have hg1L : ∀ x < h, g1 (off + x) = true := by
              intro x hx
              rw [hg1_L x hx]
              simp only [Bool.false_eq_true, ↓reduceIte]
              have e1 : off + h + x - h = off + x := by omega
              have e2 : off + h + x = off + x + h := by omega
              have hhi' := hhi x hx
              dsimp only at hhi'
              rw [e1, e2] at hhi'
              exact hhi'
            intro _
            exact runNet_bool_const (bitonicMerge off k false) off h true g1 hnetL hg1L i hi_lt

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
            · have hgt := hLm i m (by omega) (by omega)
              simp only [↓reduceIte] at hgt
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
      intro i j hij hj
      simpa only [Nat.zero_add] using hR i j hij hj
    exact hgen h (fun i => g (off + h + i)) hR'
  rcases hexL with ⟨s, hsh, hs⟩
  rcases hexR with ⟨e, heh, he⟩
  refine ⟨s, h + e, by omega, by omega, Or.inl (fun i hi => ?_)⟩
  by_cases hih : i < h
  · rw [hs i hih]
    omega
  · have e1 : off + i = off + h + (i - h) := by omega
    rw [e1, he (i - h) (by omega)]
    omega

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
      rw [e1, e2]
      exact hsL i j hij hj
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
    intro x y hxy hx
    simp only [f, decide_eq_true_eq] at hx ⊢
    omega
  have hs := bitonicSort_sorted_bool 0 p true (fun idx => f (key (st idx))) i j hij hj
  simp only [Nat.zero_add, ↓reduceIte] at hs
  rw [← runNet_mono_map key f hf] at hs
  have hiT : f (key (runNet key (bitonicSort 0 p true) st i)) = true := by
    simp [f, T]
  have hjT := hs hiT
  simp only [f, decide_eq_true_eq] at hjT
  exact hjT

end Bitonic

namespace Lookup049

open Build049 Bitonic
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

structure Rec (a b : Nat) where
  keyBit : Nat → Bool
  valBit : Fin b → Bool

def recKey {a b : Nat} (r : Rec a b) : Nat :=
  bitsVal r.keyBit (a + 2)

def netCircuit {n a b : Nat} {A : Set (Sig n)} (N : Nat)
    (net : List (Nat × Nat × Bool))
    (hnet : ∀ c ∈ net, c.1 < N ∧ c.2.1 < N)
    (st0 : (Fin n → Bool) → Nat → Rec a b)
    (hK : ∀ idx < N, ∀ j < a + 2, (fun v => (st0 v idx).keyBit j) ∈ A)
    (hV : ∀ idx < N, ∀ j : Fin b, (fun v => (st0 v idx).valBit j) ∈ A)
    (hfalse : (fun _ => false) ∈ A) :
    Build A
      ({f | ∃ idx < N, ∃ j < a + 2, f = fun v => (runNet recKey net (st0 v) idx).keyBit j} ∪
       {f | ∃ idx < N, ∃ j : Fin b, f = fun v => (runNet recKey net (st0 v) idx).valBit j} ∪
       {f | ∃ t < net.length,
         f = (fun v => ((netSwaps recKey net (st0 v)).getD t (0, 0, false)).2.2) ∨
         f = (fun v => !(((netSwaps recKey net (st0 v)).getD t (0, 0, false)).2.2))})
      (net.length * (11 * a + 6 * b + 23)) := by
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
    let swSig : Sig n := fun x =>
      swapBit (recKey (st0 x u)) (recKey (st0 x v)) asc
    have Hsw : Build A {swSig} (5 * (a + 2)) := by
      cases asc with
      | true =>
        exact ltWordG (fun j x => (st0 x v).keyBit j) (fun j x => (st0 x u).keyBit j) (a + 2)
          (fun j hj => hK v hc.2 j hj) (fun j hj => hK u hc.1 j hj) hfalse
      | false =>
        exact ltWordG (fun j x => (st0 x u).keyBit j) (fun j x => (st0 x v).keyBit j) (a + 2)
          (fun j hj => hK u hc.1 j hj) (fun j hj => hK v hc.2 j hj) hfalse
    let nswSig : Sig n := nt swSig
    have Hnsw : Build (A ∪ {swSig}) {nswSig} 1 := notG (Or.inr rfl)
    let st1 : (Fin n → Bool) → Nat → Rec a b := fun x => applySwap u v (swSig x) (st0 x)
    let A1 := A ∪ ({swSig} ∪ {nswSig})
    have hsw1 : swSig ∈ A1 := Or.inr (Or.inl rfl)
    have hnsw1 : nswSig ∈ A1 := Or.inr (Or.inr rfl)
    let K1 : Fin (a + 2) → Sig n := fun j x => (st1 x u).keyBit j.val
    let K2 : Fin (a + 2) → Sig n := fun j x => (st1 x v).keyBit j.val
    let V1 : Fin b → Sig n := fun j x => (st1 x u).valBit j
    let V2 : Fin b → Sig n := fun j x => (st1 x v).valBit j
    have HK1 : Build A1 (Set.range K1) ((a + 2) * 3) := finG K1 3 fun j => by
      have he : K1 j = fun x => if swSig x then (st0 x v).keyBit j.val else (st0 x u).keyBit j.val := by
        funext x
        simp only [K1, st1, applySwap]
        cases swSig x <;> simp
      rw [he]
      exact muxG hsw1 hnsw1 (Or.inl (hK v hc.2 j.val j.isLt)) (Or.inl (hK u hc.1 j.val j.isLt)) (fun _ => rfl)
    have HK2 : Build (A1 ∪ Set.range K1) (Set.range K2) ((a + 2) * 3) := finG K2 3 fun j => by
      have he : K2 j = fun x => if swSig x then (st0 x u).keyBit j.val else (st0 x v).keyBit j.val := by
        funext x
        simp only [K2, st1, applySwap]
        by_cases huv : v = u
        · subst huv; cases swSig x <;> simp
        · cases swSig x <;> simp [huv]
      rw [he]
      exact muxG (Or.inl hsw1) (Or.inl hnsw1) (Or.inl (Or.inl (hK u hc.1 j.val j.isLt)))
        (Or.inl (Or.inl (hK v hc.2 j.val j.isLt))) (fun _ => rfl)
    have HV1 : Build (A1 ∪ (Set.range K1 ∪ Set.range K2)) (Set.range V1) (b * 3) := finG V1 3 fun j => by
      have he : V1 j = fun x => if swSig x then (st0 x v).valBit j else (st0 x u).valBit j := by
        funext x
        simp only [V1, st1, applySwap]
        cases swSig x <;> simp
      rw [he]
      exact muxG (Or.inl hsw1) (Or.inl hnsw1) (Or.inl (Or.inl (hV v hc.2 j)))
        (Or.inl (Or.inl (hV u hc.1 j))) (fun _ => rfl)
    have HV2 : Build (A1 ∪ ((Set.range K1 ∪ Set.range K2) ∪ Set.range V1)) (Set.range V2) (b * 3) := finG V2 3 fun j => by
      have he : V2 j = fun x => if swSig x then (st0 x u).valBit j else (st0 x v).valBit j := by
        funext x
        simp only [V2, st1, applySwap]
        by_cases huv : v = u
        · subst huv; cases swSig x <;> simp
        · cases swSig x <;> simp [huv]
      rw [he]
      exact muxG (Or.inl hsw1) (Or.inl hnsw1) (Or.inl (Or.inl (hV u hc.1 j)))
        (Or.inl (Or.inl (hV v hc.2 j))) (fun _ => rfl)
    let B1 := ({swSig} ∪ {nswSig}) ∪ (((Set.range K1 ∪ Set.range K2) ∪ Set.range V1) ∪ Set.range V2)
    have Hstep : Build A B1 (11 * a + 6 * b + 23) := by
      have H0 := seq Hsw Hnsw
      have H1 := seq (seq (seq HK1 HK2) HV1) HV2
      have H01 := seq H0 H1
      exact relax H01 le_rfl le_rfl (by omega)
    have hK1 : ∀ idx < N, ∀ j < a + 2, (fun x => (st1 x idx).keyBit j) ∈ A ∪ B1 := by
      intro idx hidx j hj
      by_cases hu : idx = u
      · subst hu; exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl ⟨⟨j, hj⟩, rfl⟩))))
      · by_cases hv : idx = v
        · subst hv; exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr ⟨⟨j, hj⟩, rfl⟩))))
        · have he : (fun x => (st1 x idx).keyBit j) = (fun x => (st0 x idx).keyBit j) := by
            funext x; simp only [st1, applySwap]; cases swSig x <;> simp [hu, hv]
          rw [he]; exact Or.inl (hK idx hidx j hj)
    have hV1 : ∀ idx < N, ∀ j : Fin b, (fun x => (st1 x idx).valBit j) ∈ A ∪ B1 := by
      intro idx hidx j
      by_cases hu : idx = u
      · subst hu; exact Or.inr (Or.inr (Or.inl (Or.inr ⟨j, rfl⟩)))
      · by_cases hv : idx = v
        · subst hv; exact Or.inr (Or.inr (Or.inr ⟨j, rfl⟩))
        · have he : (fun x => (st1 x idx).valBit j) = (fun x => (st0 x idx).valBit j) := by
            funext x; simp only [st1, applySwap]; cases swSig x <;> simp [hu, hv]
          rw [he]; exact Or.inl (hV idx hidx j)
    have Hrest := ih (fun c' hc' => hnet c' (List.mem_cons_of_mem _ hc')) st1 hK1 hV1 (Or.inl hfalse)
    have Htot := seq Hstep Hrest
    refine relax Htot le_rfl ?_ ?_
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

def scanStep {n b : Nat} (N : Nat)
    (st : (Fin n → Bool) → Nat → Rec a b) : Nat → (Fin n → Bool) → (Fin b → Bool) × (Nat → Fin b → Bool)
  | 0, _ => (fun _ => false, fun _ _ => false)
  | t + 1, x =>
    let prev := scanStep N st t x
    let isTab := !((st x t).keyBit (a + 1)) && !((st x t).keyBit 0)
    let cur' := fun j => if isTab then (st x t).valBit j else prev.1 j
    (cur', fun idx => if idx = t then cur' else prev.2 idx)

theorem scanCircuit {n a b : Nat} {A : Set (Sig n)} (N : Nat)
    (st : (Fin n → Bool) → Nat → Rec a b)
    (hK : ∀ idx < N, ∀ j < a + 2, (fun v => (st v idx).keyBit j) ∈ A)
    (hV : ∀ idx < N, ∀ j : Fin b, (fun v => (st v idx).valBit j) ∈ A)
    (hfalse : (fun _ => false) ∈ A) :
    ∀ m ≤ N,
      Build A
        ({f | ∃ j : Fin b, f = fun v => (scanStep N st m v).1 j} ∪
         {f | ∃ idx < m, ∃ j : Fin b, f = fun v => (scanStep N st m v).2 idx j})
        (m * (3 * b + 4)) := by
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
      {f | ∃ j : Fin b, f = fun v => (scanStep N st m v).1 j} ∪
      {f | ∃ idx < m, ∃ j : Fin b, f = fun v => (scanStep N st m v).2 idx j}
    let A1 := A ∪ Bprev
    let dSig : Sig n := fun v => (st v m).keyBit (a + 1)
    let tSig : Sig n := fun v => (st v m).keyBit 0
    have hd : dSig ∈ A1 := Or.inl (hK m (by omega) (a + 1) (by omega))
    have ht : tSig ∈ A1 := Or.inl (hK m (by omega) 0 (by omega))
    have Hnd : Build A1 {nt dSig} 1 := notG hd
    have Hnt : Build (A1 ∪ {nt dSig}) {nt tSig} 1 := notG (Or.inl ht)
    let isTab : Sig n := an (nt dSig) (nt tSig)
    have HisTab : Build (A1 ∪ ({nt dSig} ∪ {nt tSig})) {isTab} 1 :=
      andG (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
    let nisTab : Sig n := nt isTab
    have HnisTab : Build (A1 ∪ (({nt dSig} ∪ {nt tSig}) ∪ {isTab})) {nisTab} 1 :=
      notG (Or.inr (Or.inr rfl))
    let curF : Fin b → Sig n := fun j v => (scanStep N st (m + 1) v).1 j
    let A2 := A1 ∪ ((({nt dSig} ∪ {nt tSig}) ∪ {isTab}) ∪ {nisTab})
    have Hcur : Build A2 (Set.range curF) (b * 3) := finG curF 3 fun j => by
      have he : curF j = fun v => if isTab v then (st v m).valBit j else (scanStep N st m v).1 j := rfl
      rw [he]
      exact muxG (Or.inr (Or.inl (Or.inr rfl))) (Or.inr (Or.inr rfl))
        (Or.inl (Or.inl (hV m (by omega) j)))
        (Or.inl (Or.inr (Or.inl ⟨j, rfl⟩)))
        (fun _ => rfl)
    have Hstep := seq (seq (seq (seq Hnd Hnt) HisTab) HnisTab) Hcur
    have Htot := seq Hprev Hstep
    refine relax Htot le_rfl ?_ ?_
    · rintro f (⟨j, rfl⟩ | ⟨idx, hidx, j, rfl⟩)
      · exact Or.inr (Or.inr ⟨j, rfl⟩)
      · by_cases hjm : idx = m
        · subst hjm
          exact Or.inr (Or.inr ⟨j, by funext v; simp [curF, scanStep]⟩)
        · exact Or.inl (Or.inr ⟨idx, by omega, j, by funext v; simp [scanStep, hjm]⟩)
    · rw [Nat.succ_mul m]
      omega

theorem replayCircuit {n b : Nat} {A : Set (Sig n)} (N : Nat)
    (sws : (Fin n → Bool) → List (Nat × Nat × Bool))
    (L : Nat) (hL : ∀ v, (sws v).length = L)
    (hidx_fixed : ∀ t < L, ∃ u v, u < N ∧ v < N ∧
      ∀ x, ((sws x).getD t (0, 0, false)).1 = u ∧ ((sws x).getD t (0, 0, false)).2.1 = v)
    (hsw_mem : ∀ t < L,
      (fun x => ((sws x).getD t (0, 0, false)).2.2) ∈ A ∧
      (fun x => !(((sws x).getD t (0, 0, false)).2.2)) ∈ A)
    (ans0 : (Fin n → Bool) → Nat → Fin b → Bool)
    (hA0 : ∀ idx < N, ∀ j : Fin b, (fun x => ans0 x idx j) ∈ A) :
    Build A {f | ∃ idx < N, ∃ j : Fin b, f = fun x => replaySwaps (sws x) (ans0 x) idx j} (L * (6 * b)) := by
  induction L generalizing sws ans0 A with
  | zero =>
    refine relax (idle ?_) le_rfl le_rfl (by simp)
    rintro f ⟨idx, hidx, j, rfl⟩
    have he : (fun x => replaySwaps (sws x) (ans0 x) idx j) = (fun x => ans0 x idx j) := by
      funext x
      have hnil : sws x = [] := List.eq_nil_of_length_eq_zero (hL x)
      rw [hnil]
      rfl
    rw [he]
    exact hA0 idx hidx j
  | succ L ih =>
    rcases hidx_fixed 0 (Nat.zero_lt_succ L) with ⟨u, v, hu, hv, huv⟩
    let swSig : Sig n := fun x => ((sws x).getD 0 (0, 0, false)).2.2
    let nswSig : Sig n := fun x => !(((sws x).getD 0 (0, 0, false)).2.2)
    have hsw0 := hsw_mem 0 (Nat.zero_lt_succ L)
    let ans1 : (Fin n → Bool) → Nat → Fin b → Bool := fun x => applySwap u v (swSig x) (ans0 x)
    let V1 : Fin b → Sig n := fun j x => ans1 x u j
    let V2 : Fin b → Sig n := fun j x => ans1 x v j
    have HV1 : Build A (Set.range V1) (b * 3) := finG V1 3 fun j => by
      have he : V1 j = fun x => if swSig x then ans0 x v j else ans0 x u j := by
        funext x; simp only [V1, ans1, applySwap]; cases swSig x <;> simp
      rw [he]
      exact muxG hsw0.1 hsw0.2 (hA0 v hv j) (hA0 u hu j) (fun _ => rfl)
    have HV2 : Build (A ∪ Set.range V1) (Set.range V2) (b * 3) := finG V2 3 fun j => by
      have he : V2 j = fun x => if swSig x then ans0 x u j else ans0 x v j := by
        funext x
        simp only [V2, ans1, applySwap]
        by_cases hvu : v = u
        · subst hvu; cases swSig x <;> simp
        · cases swSig x <;> simp [hvu]
      rw [he]
      exact muxG (Or.inl hsw0.1) (Or.inl hsw0.2) (Or.inl (hA0 u hu j)) (Or.inl (hA0 v hv j)) (fun _ => rfl)
    have Hstep := seq HV1 HV2
    let sws' : (Fin n → Bool) → List (Nat × Nat × Bool) := fun x => (sws x).tail
    have hL' : ∀ x, (sws' x).length = L := by
      intro x; simp [sws', List.length_tail, hL x]
    have hget_tail : ∀ t < L, ∀ x, (sws' x).getD t (0, 0, false) = (sws x).getD (t + 1) (0, 0, false) := by
      intro t ht x
      cases hs : sws x with
      | nil => have := hL x; rw [hs] at this; simp at this
      | cons c cs => simp [sws', hs]
    have hidx' : ∀ t < L, ∃ u' v', u' < N ∧ v' < N ∧
        ∀ x, ((sws' x).getD t (0, 0, false)).1 = u' ∧ ((sws' x).getD t (0, 0, false)).2.1 = v' := by
      intro t ht
      rcases hidx_fixed (t + 1) (by omega) with ⟨u', v', hu', hv', hEq⟩
      refine ⟨u', v', hu', hv', fun x => ?_⟩
      rw [hget_tail t ht x]
      exact hEq x
    have hsw' : ∀ t < L,
        (fun x => ((sws' x).getD t (0, 0, false)).2.2) ∈ A ∪ (Set.range V1 ∪ Set.range V2) ∧
        (fun x => !(((sws' x).getD t (0, 0, false)).2.2)) ∈ A ∪ (Set.range V1 ∪ Set.range V2) := by
      intro t ht
      have h1 := hsw_mem (t + 1) (by omega)
      have e1 : (fun x => ((sws' x).getD t (0, 0, false)).2.2) = (fun x => ((sws x).getD (t + 1) (0, 0, false)).2.2) := by
        funext x; rw [hget_tail t ht x]
      have e2 : (fun x => !(((sws' x).getD t (0, 0, false)).2.2)) = (fun x => !(((sws x).getD (t + 1) (0, 0, false)).2.2)) := by
        funext x; rw [hget_tail t ht x]
      rw [e1, e2]
      exact ⟨Or.inl h1.1, Or.inl h1.2⟩
    have hA1 : ∀ idx < N, ∀ j : Fin b, (fun x => ans1 x idx j) ∈ A ∪ (Set.range V1 ∪ Set.range V2) := by
      intro idx hidx j
      by_cases h1 : idx = u
      · subst h1; exact Or.inr (Or.inl ⟨j, rfl⟩)
      · by_cases h2 : idx = v
        · subst h2; exact Or.inr (Or.inr ⟨j, rfl⟩)
        · have he : (fun x => ans1 x idx j) = (fun x => ans0 x idx j) := by
            funext x; simp only [ans1, applySwap]; cases swSig x <;> simp [h1, h2]
          rw [he]; exact Or.inl (hA0 idx hidx j)
    have Hrest := ih sws' hL' hidx' hsw' ans1 hA1
    refine relax (seq Hstep Hrest) le_rfl ?_ ?_
    · rintro f ⟨idx, hidx, j, rfl⟩
      right
      refine ⟨idx, hidx, j, ?_⟩
      funext x
      cases hs : sws x with
      | nil => have := hL x; rw [hs] at this; simp at this
      | cons c cs =>
        have h0 := huv x
        rw [hs] at h0
        simp only [List.getD_cons_zero] at h0
        rcases c with ⟨cu, cv, csw⟩
        dsimp only at h0
        rcases h0 with ⟨rfl, rfl⟩
        have he_sw : swSig x = csw := by simp [swSig, hs]
        simp only [replaySwaps, sws', hs, List.tail_cons, ans1, he_sw]
    · rw [Nat.succ_mul L]
      omega

theorem log2_bound (a q : Nat) :
    let M := 2 ^ a + q
    let p := if M ≤ 1 then 0 else Nat.log2 (M - 1) + 1
    M ≤ 2 ^ p ∧ 2 ^ p ≤ 2 * M ∧ p ≤ a + Nat.log2 (q + 1) + 1 := by
  intro M p
  have hMpos : 1 ≤ M := by
    have := Nat.two_pow_pos a
    dsimp [M]
    omega
  by_cases hM1 : M ≤ 1
  · have hp : p = 0 := by simp [p, hM1]
    rw [hp]
    simp only [Nat.pow_zero]
    omega
  · have hp : p = Nat.log2 (M - 1) + 1 := by simp [p, hM1]
    rw [hp]
    have hm_ne : M - 1 ≠ 0 := by omega
    have hlt := Nat.lt_log2_self (n := M - 1)
    have hle := Nat.log2_self_le hm_ne
    have h1 : M ≤ 2 ^ (Nat.log2 (M - 1) + 1) := by omega
    have h2 : 2 ^ (Nat.log2 (M - 1) + 1) ≤ 2 * M := by
      rw [Nat.pow_succ, Nat.mul_comm]
      omega
    have h3 : Nat.log2 (M - 1) ≤ a + Nat.log2 (q + 1) := by
      have hqlt : q + 1 < 2 ^ (Nat.log2 (q + 1) + 1) := Nat.lt_log2_self
      have hMlt : M - 1 < 2 ^ (a + Nat.log2 (q + 1) + 1) := by
        have hmul : 2 ^ a * (q + 1) ≤ 2 ^ a * (2 ^ (Nat.log2 (q + 1) + 1)) :=
          Nat.mul_le_mul_left _ (Nat.le_of_lt hqlt)
        have hpow : 2 ^ a * 2 ^ (Nat.log2 (q + 1) + 1) = 2 ^ (a + Nat.log2 (q + 1) + 1) := by
          rw [← Nat.pow_add, Nat.add_assoc]
        have h2p : 1 ≤ 2 ^ a := Nat.two_pow_pos a
        have hqle : q ≤ 2 ^ a * q := Nat.le_mul_of_pos_left q h2p
        have hsum : M - 1 < 2 ^ a * (q + 1) := by
          dsimp [M]
          rw [Nat.mul_add, Nat.mul_one]
          omega
        have hstep : 2 ^ a * (q + 1) < 2 ^ a * 2 ^ (Nat.log2 (q + 1) + 1) :=
          Nat.mul_lt_mul_of_pos_left hqlt (Nat.two_pow_pos a)
        omega
      by_contra hgt
      have hge : a + Nat.log2 (q + 1) + 1 ≤ Nat.log2 (M - 1) := by omega
      have hpow_le := Nat.pow_le_pow_right Nat.zero_lt_two hge
      omega
    exact ⟨h1, h2, by omega⟩

theorem netSwaps_length {α : Type*} (key : α → Nat) (net : List (Nat × Nat × Bool)) (st : Nat → α) :
    (netSwaps key net st).length = net.length := by
  induction net generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, asc⟩
    simp [netSwaps, ih]

theorem netSwaps_getD_uv {α : Type*} (key : α → Nat) (net : List (Nat × Nat × Bool)) (st : Nat → α) :
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
      simpa [netSwaps] using ih _ t (by omega)

theorem scanStep_answer {a b : Nat} (N : Nat) (st : Nat → Rec a b)
    (table : Fin (2 ^ a) → Fin b → Bool)
    (hsorted : ∀ i j, i ≤ j → j < N → recKey (st i) ≤ recKey (st j))
    (htab_real : ∀ i < N, (st i).keyBit (a + 1) = false → (st i).keyBit 0 = false →
      ∃ addr : Fin (2 ^ a), recKey (st i) = 2 * addr.val ∧ (st i).valBit = table addr)
    (htab_exists : ∀ addr : Fin (2 ^ a), ∃ i < N,
      (st i).keyBit (a + 1) = false ∧ (st i).keyBit 0 = false ∧ recKey (st i) = 2 * addr.val) :
    ∀ m ≤ N,
      (∀ t < m, (st t).keyBit (a + 1) = false → (st t).keyBit 0 = true →
        ∀ addr : Fin (2 ^ a), recKey (st t) = 2 * addr.val + 1 →
          (scanStep N (fun _ : Fin 0 → Bool => st) m (fun i => i.elim0)).2 t = table addr) ∧
      (∀ t < m, (st t).keyBit (a + 1) = false → (st t).keyBit 0 = false →
        ∃ addr : Fin (2 ^ a),
          (∀ j < m, (st j).keyBit (a + 1) = false → (st j).keyBit 0 = false → recKey (st j) ≤ 2 * addr.val) ∧
          (∃ j < m, (st j).keyBit (a + 1) = false ∧ (st j).keyBit 0 = false ∧ recKey (st j) = 2 * addr.val) ∧
          (scanStep N (fun _ : Fin 0 → Bool => st) m (fun i => i.elim0)).1 = table addr) := by
  intro m
  induction m with
  | zero =>
    intro _
    exact ⟨fun t ht => by omega, fun t ht => by omega⟩
  | succ m ih =>
    intro hm
    rcases ih (by omega) with ⟨ih_ans, ih_cur⟩
    constructor
    · intro t ht hd0 ht1 addr hkey
      simp only [scanStep]
      by_cases htm : t = m
      · subst t
        simp only [↓reduceIte, ht1, Bool.not_true, Bool.and_false, Bool.false_eq_true]
        rcases htab_exists addr with ⟨i0, hi0N, hi0d, hi0t, hi0k⟩
        have hi0_lt : i0 < m := by
          by_contra hge
          have hle := hsorted m i0 (by omega) hi0N
          omega
        rcases ih_cur i0 hi0_lt hi0d hi0t with ⟨addr', hmax, ⟨j0, hj0m, _, _, hj0k⟩, hcur_eq⟩
        have hle1 : 2 * addr.val ≤ 2 * addr'.val := by
          have := hmax i0 hi0_lt hi0d hi0t
          omega
        have hle2 : 2 * addr'.val ≤ 2 * addr.val + 1 := by
          have := hsorted j0 m (by omega) (by omega)
          omega
        have haddr_eq : addr' = addr := Fin.ext (by omega)
        rw [hcur_eq, haddr_eq]
      · simp only [htm, ↓reduceIte]
        exact ih_ans t (by omega) hd0 ht1 addr hkey
    · intro t ht hd0 ht0
      simp only [scanStep]
      by_cases hmtab : (st m).keyBit (a + 1) = false ∧ (st m).keyBit 0 = false
      · simp only [hmtab.1, hmtab.2, Bool.not_false, Bool.and_self, ↓reduceIte]
        rcases htab_real m (by omega) hmtab.1 hmtab.2 with ⟨addr, hkey, hval⟩
        refine ⟨addr, ?_, ⟨m, by omega, hmtab.1, hmtab.2, hkey⟩, hval⟩
        intro j hj _ _
        have hle := hsorted j m (by omega) (by omega)
        omega
      · have hnot : (!((st m).keyBit (a + 1)) && !((st m).keyBit 0)) = false := by
          cases h1 : (st m).keyBit (a + 1) <;> cases h2 : (st m).keyBit 0
          · exact absurd ⟨h1, h2⟩ hmtab
          · rfl
          · rfl
          · rfl
        simp only [hnot, Bool.false_eq_true, ↓reduceIte]
        have htm : t < m := by
          by_contra hge
          have hteq : t = m := by omega
          subst hteq
          exact hmtab ⟨hd0, ht0⟩
        rcases ih_cur t htm hd0 ht0 with ⟨addr, hmax, ⟨j0, hj0, hj0d, hj0t, hj0k⟩, hcur_eq⟩
        refine ⟨addr, ?_, ⟨j0, by omega, hj0d, hj0t, hj0k⟩, hcur_eq⟩
        intro j hj hjd hjt
        by_cases hjm : j = m
        · subst hjm; exact absurd ⟨hjd, hjt⟩ hmtab
        · exact hmax j (by omega) hjd hjt

theorem keyBits_val (a : Nat) (dummy tag : Bool) (addr : Nat) (haddr : addr < 2 ^ a) :
    let kb : Nat → Bool := fun j =>
      if j = 0 then tag else if j = a + 1 then dummy else addr.testBit (j - 1)
    bitsVal kb (a + 2) = (if dummy then 2 ^ (a + 1) else 0) + 2 * addr + (if tag then 1 else 0) := by
  intro kb
  have hmid : ∀ m ≤ a, bitsVal kb (m + 1) = (if tag then 1 else 0) + 2 * (addr % 2 ^ m) := by
    intro m
    induction m with
    | zero =>
      intro _
      simp [bitsVal, kb, Nat.mod_one]
    | succ m ih =>
      intro hm
      have hih := ih (by omega)
      change (bitsVal kb (m + 1) + if kb (m + 1) then 2 ^ (m + 1) else 0) = _
      have hbit : kb (m + 1) = addr.testBit m := by
        simp only [kb, show m + 1 ≠ 0 by omega, show m + 1 ≠ a + 1 by omega, ↓reduceIte, Nat.add_sub_cancel]
      rw [hih, hbit]
      have hmod : addr % 2 ^ (m + 1) = addr % 2 ^ m + if addr.testBit m then 2 ^ m else 0 := by
        apply Nat.eq_of_testBit_eq
        intro j
        rw [Nat.testBit_mod_two_pow]
        have hltm : addr % 2 ^ m < 2 ^ m := Nat.mod_lt _ (Nat.two_pow_pos m)
        by_cases hj : j < m
        · have hj1 : j < m + 1 := by omega
          simp only [hj1, decide_true, Bool.true_and]
          cases addr.testBit m with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.testBit_mod_two_pow, hj, decide_true, Bool.true_and]
          | true =>
            simp only [↓reduceIte]
            rw [Nat.add_comm, Nat.testBit_two_pow_add_gt hj, Nat.testBit_mod_two_pow]
            simp [hj]
        · by_cases hjm : j = m
          · subst hjm
            simp only [Nat.lt_succ_self, decide_true, Bool.true_and]
            cases hbm : addr.testBit j with
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
              exact (Nat.testBit_lt_two_pow hltm).symm
            | true =>
              simp only [↓reduceIte]
              rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hltm]
              rfl
          · have hge : m + 1 ≤ j := by omega
            have hnf : ¬ j < m + 1 := by omega
            simp only [hnf, decide_false, Bool.false_and]
            have hlt2 : addr % 2 ^ m + (if addr.testBit m then 2 ^ m else 0) < 2 ^ (m + 1) := by
              rw [Nat.pow_succ]; cases addr.testBit m <;> simp <;> omega
            exact (Nat.testBit_lt_two_pow (hlt2.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two hge))).symm
      rw [hmod, Nat.mul_add]
      have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [hpow]
      cases addr.testBit m <;> simp <;> omega
  change (bitsVal kb (a + 1) + if kb (a + 1) then 2 ^ (a + 1) else 0) = _
  have h1 := hmid a (Nat.le_refl a)
  rw [Nat.mod_eq_of_lt haddr] at h1
  rw [h1]
  have htop : kb (a + 1) = dummy := by simp [kb]
  rw [htop]
  omega

theorem list_ofFn_flatten_getD {m k : Nat} (f : Fin m → Fin k → Bool)
    (j : Fin m) (i : Fin k) :
    ((List.ofFn (fun r : Fin m => List.ofFn (f r))).flatten).getD (j.val * k + i.val) false = f j i := by
  have hgen : ∀ (l : List (List Bool)), (∀ s ∈ l, s.length = k) →
      ∀ (r : Nat) (hr : r < l.length) (c : Nat) (hc : c < k),
        l.flatten.getD (r * k + c) false = (l[r]'hr).getD c false := by
    intro l
    induction l with
    | nil => intro _ r hr; simp at hr
    | cons hd tl ih =>
      intro hlen r hr c hc
      have hhd : hd.length = k := hlen hd List.mem_cons_self
      cases r with
      | zero =>
        simp only [Nat.zero_mul, Nat.zero_add, List.flatten_cons, List.getElem_cons_zero]
        rw [List.getD_append _ _ _ _ (by omega)]
      | succ r =>
        simp only [List.length_cons] at hr
        simp only [List.flatten_cons, List.getElem_cons_succ]
        have hge : hd.length ≤ (r + 1) * k + c := by rw [hhd, Nat.succ_mul]; omega
        rw [List.getD_append_right _ _ _ _ hge]
        have hsub : (r + 1) * k + c - hd.length = r * k + c := by rw [hhd, Nat.succ_mul]; omega
        rw [hsub]
        exact ih (fun s hs => hlen s (List.mem_cons_of_mem hd hs)) r (by omega) c hc
  have hlen : ∀ s ∈ List.ofFn (fun r : Fin m => List.ofFn (f r)), s.length = k := by
    intro s hs
    rw [List.mem_ofFn] at hs
    rcases hs with ⟨r, rfl⟩
    simp
  have h1 := hgen (List.ofFn (fun r : Fin m => List.ofFn (f r))) hlen j.val (by simp) i.val i.isLt
  rw [h1, List.getElem_ofFn, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

theorem list_ofFn_flatten_length {m k : Nat} (f : Fin m → Fin k → Bool) :
    ((List.ofFn (fun r : Fin m => List.ofFn (f r))).flatten).length = m * k := by
  have hgen : ∀ (l : List (List Bool)), (∀ s ∈ l, s.length = k) → l.flatten.length = l.length * k := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons hd tl ih =>
      intro hlen
      simp only [List.flatten_cons, List.length_append, List.length_cons,
        hlen hd List.mem_cons_self, ih (fun s hs => hlen s (List.mem_cons_of_mem hd hs)), Nat.succ_mul]
      omega
  have h1 := hgen (List.ofFn (fun r : Fin m => List.ofFn (f r))) (by
    intro s hs; rw [List.mem_ofFn] at hs; rcases hs with ⟨r, rfl⟩; simp)
  simpa using h1

theorem solve_049 (a b q : Nat) :
    let words := 2 ^ a
    let I := words * b + q * a
    ∃ (C : Circuit) (outBit : Fin q → Fin b → Fin (I + C.size)),
      FanInTwo C ∧ ReadsBack I C ∧ C.output < I + C.size ∧
      C.size ≤ 128 * (words + q) * (a + b + Nat.log2 (q + 1) + 3) ^ 3 ∧
      ∀ (table : Fin words → Fin b → Bool) (address : Fin q → Fin words),
        let x := (List.ofFn (fun j : Fin words => List.ofFn (table j))).flatten ++
          (List.ofFn (fun j : Fin q =>
            List.ofFn (fun i : Fin a => (address j).val.testBit i.val))).flatten
        ∀ (j : Fin q) (i : Fin b),
          (C.wires x).getD (outBit j i).val false = table (address j) i := by
  intro words I
  let M := words + q
  let p := if M ≤ 1 then 0 else Nat.log2 (M - 1) + 1
  have hp_bd := log2_bound a q
  have hMN : M ≤ 2 ^ p := hp_bd.1
  have hN2M : 2 ^ p ≤ 2 * M := hp_bd.2.1
  have hp_le : p ≤ a + Nat.log2 (q + 1) + 1 := hp_bd.2.2
  let N := 2 ^ p
  let net := bitonicSort 0 p true
  have hnet_mem : ∀ c ∈ net, c.1 < N ∧ c.2.1 < N := by
    intro c hc
    have hm := bitonicSort_mem 0 p true c hc
    omega
  let inputs : Set (Sig I) := Set.range (fun idx : Fin I => fun v => v idx)
  let base : Set (Sig I) := inputs ∪ {fun _ => false, fun _ => true}
  have Hconst : Build inputs {fun _ => false, fun _ => true} 2 := by
    simpa only [Set.singleton_union] using
      (seq (constG (A := inputs) false) (constG (A := inputs ∪ {fun _ => false}) true))
  have hbase_c : ∀ c : Bool, (fun _ : Fin I → Bool => c) ∈ base := by
    intro c; cases c <;> exact Or.inr (by simp)
  let st0 (v : Fin I → Bool) (idx : Nat) : Rec a b :=
    if h1 : idx < words then
      { keyBit := fun j => if j = 0 then false else if j = a + 1 then false else idx.testBit (j - 1)
        valBit := fun j => v ⟨idx * b + j.val, by
          have hmul : idx * b + b ≤ words * b := by
            have := Nat.mul_le_mul_right b (show idx + 1 ≤ words by omega)
            rw [Nat.succ_mul] at this
            exact this
          omega⟩ }
    else if h2 : idx < M then
      let qIdx := idx - words
      { keyBit := fun j =>
          if j = 0 then true
          else if j = a + 1 then false
          else if hj : j - 1 < a then
            v ⟨words * b + qIdx * a + (j - 1), by
              have hmul : qIdx * a + a ≤ q * a := by
                have := Nat.mul_le_mul_right a (show qIdx + 1 ≤ q by dsimp [qIdx, M] at *; omega)
                rw [Nat.succ_mul] at this
                exact this
              omega⟩
          else false
        valBit := fun _ => false }
    else
      { keyBit := fun j => if j = 0 then true else if j = a + 1 then true else false
        valBit := fun _ => false }
  have hK0 : ∀ idx < N, ∀ j < a + 2, (fun v => (st0 v idx).keyBit j) ∈ base := by
    intro idx _ j _
    by_cases h1 : idx < words
    · simp only [st0, h1, ↓reduceDIte]
      exact hbase_c _
    · by_cases h2 : idx < M
      · simp only [st0, h1, h2, ↓reduceDIte]
        by_cases hj0 : j = 0
        · simp only [hj0, ↓reduceIte]; exact hbase_c true
        · by_cases hja : j = a + 1
          · simp only [hj0, hja, ↓reduceIte]; exact hbase_c false
          · by_cases hja' : j - 1 < a
            · simp only [hj0, hja, hja', ↓reduceIte, ↓reduceDIte]
              exact Or.inl ⟨_, rfl⟩
            · simp only [hj0, hja, hja', ↓reduceIte, ↓reduceDIte]
              exact hbase_c false
      · simp only [st0, h1, h2, ↓reduceDIte]
        exact hbase_c _
  have hV0 : ∀ idx < N, ∀ j : Fin b, (fun v => (st0 v idx).valBit j) ∈ base := by
    intro idx _ j
    by_cases h1 : idx < words
    · simp only [st0, h1, ↓reduceDIte]
      exact Or.inl ⟨_, rfl⟩
    · by_cases h2 : idx < M
      · simp only [st0, h1, h2, ↓reduceDIte]; exact hbase_c false
      · simp only [st0, h1, h2, ↓reduceDIte]; exact hbase_c false
  have Hnet := netCircuit (A := base) N net hnet_mem st0 hK0 hV0 (hbase_c false)
  let Bnet :=
    {f | ∃ idx < N, ∃ j < a + 2, f = fun v => (runNet recKey net (st0 v) idx).keyBit j} ∪
    {f | ∃ idx < N, ∃ j : Fin b, f = fun v => (runNet recKey net (st0 v) idx).valBit j} ∪
    {f | ∃ t < net.length,
      f = (fun v => ((netSwaps recKey net (st0 v)).getD t (0, 0, false)).2.2) ∨
      f = (fun v => !(((netSwaps recKey net (st0 v)).getD t (0, 0, false)).2.2))}
  have Hscan := scanCircuit (A := base ∪ Bnet) N (fun v => runNet recKey net (st0 v))
    (fun idx hidx j hj => Or.inr (Or.inl (Or.inl ⟨idx, hidx, j, hj, rfl⟩)))
    (fun idx hidx j => Or.inr (Or.inl (Or.inr ⟨idx, hidx, j, rfl⟩)))
    (Or.inl (hbase_c false)) N (Nat.le_refl N)
  let Bscan :=
    {f | ∃ j : Fin b, f = fun v => (scanStep N (fun x => runNet recKey net (st0 x)) N v).1 j} ∪
    {f | ∃ idx < N, ∃ j : Fin b, f = fun v => (scanStep N (fun x => runNet recKey net (st0 x)) N v).2 idx j}
  let swsRev : (Fin I → Bool) → List (Nat × Nat × Bool) :=
    fun v => (netSwaps recKey net (st0 v)).reverse
  have hL_rev : ∀ v, (swsRev v).length = net.length := by
    intro v; simp [swsRev, netSwaps_length]
  have hget_rev : ∀ t < net.length, ∀ v,
      (swsRev v).getD t (0, 0, false) = (netSwaps recKey net (st0 v)).getD (net.length - 1 - t) (0, 0, false) := by
    intro t ht v
    have hlen : (netSwaps recKey net (st0 v)).length = net.length := netSwaps_length _ _ _
    dsimp only [swsRev]
    rw [List.getD_eq_getElem _ _ (by simp [hlen]; omega),
        List.getD_eq_getElem _ _ (by omega),
        List.getElem_reverse]
    congr 1
    omega
  have hidx_rev : ∀ t < net.length, ∃ u' v', u' < N ∧ v' < N ∧
      ∀ x, ((swsRev x).getD t (0, 0, false)).1 = u' ∧ ((swsRev x).getD t (0, 0, false)).2.1 = v' := by
    intro t ht
    let t' := net.length - 1 - t
    have ht' : t' < net.length := by omega
    have hmem : net[t']'ht' ∈ net := List.getElem_mem ht'
    have hbd := hnet_mem _ hmem
    have hget : net.getD t' (0, 0, false) = net[t']'ht' := by simp [List.getD_eq_getElem?_getD, ht']
    refine ⟨(net[t']'ht').1, (net[t']'ht').2.1, hbd.1, hbd.2, fun x => ?_⟩
    rw [hget_rev t ht x]
    have huv := netSwaps_getD_uv recKey net (st0 x) t' ht'
    rw [hget] at huv
    exact huv
  have hsw_rev : ∀ t < net.length,
      (fun x => ((swsRev x).getD t (0, 0, false)).2.2) ∈ base ∪ (Bnet ∪ Bscan) ∧
      (fun x => !(((swsRev x).getD t (0, 0, false)).2.2)) ∈ base ∪ (Bnet ∪ Bscan) := by
    intro t ht
    let t' := net.length - 1 - t
    have e1 : (fun x => ((swsRev x).getD t (0, 0, false)).2.2) =
        (fun x => ((netSwaps recKey net (st0 x)).getD t' (0, 0, false)).2.2) := by
      funext x; rw [hget_rev t ht x]
    have e2 : (fun x => !(((swsRev x).getD t (0, 0, false)).2.2)) =
        (fun x => !(((netSwaps recKey net (st0 x)).getD t' (0, 0, false)).2.2)) := by
      funext x; rw [hget_rev t ht x]
    rw [e1, e2]
    exact ⟨Or.inr (Or.inl (Or.inr ⟨t', by omega, Or.inl rfl⟩)),
           Or.inr (Or.inl (Or.inr ⟨t', by omega, Or.inr rfl⟩))⟩
  let ansScan (v : Fin I → Bool) : Nat → Fin b → Bool :=
    (scanStep N (fun x => runNet recKey net (st0 x)) N v).2
  have Hrev := replayCircuit (A := base ∪ (Bnet ∪ Bscan)) N swsRev net.length hL_rev hidx_rev hsw_rev ansScan
    (fun idx hidx j => Or.inr (Or.inr (Or.inr ⟨idx, hidx, j, rfl⟩)))
  let Bout := {f | ∃ idx < N, ∃ j : Fin b, f = fun x => replaySwaps (swsRev x) (ansScan x) idx j}
  have Htot : Build inputs ({fun _ => false} ∪ Bout)
      (2 + (net.length * (11 * a + 6 * b + 23) + (N * (3 * b + 4) + net.length * (6 * b)))) := by
    have H12 := seq Hnet Hscan
    have H123 := seq H12 Hrev
    have H0123 := seq Hconst H123
    refine relax H0123 le_rfl ?_ (by omega)
    rintro f (rfl | hf)
    · exact Or.inl (Or.inl rfl)
    · exact Or.inr (Or.inr hf)
  obtain ⟨c, hc, HS⟩ := Htot.run (GateBridge.start (F := id) (fun i : Fin I => fun v => v i) (by intros; rfl)) le_rfl
  clear Htot
  rcases HS with ⟨gs, hgs, hread, hfan, hwire⟩
  have hpos : 0 < I + c := by
    have hcf : (fun _ : Fin I → Bool => false) ∈ (Set.range (fun i : Fin I => fun v => v i)) ∪ ({fun _ => false} ∪ Bout) :=
      Or.inr (Or.inl rfl)
    obtain ⟨idx0, hidx0, _⟩ := hwire _ hcf
    omega
  let C : Circuit := ⟨gs, 0⟩
  have hCsize : C.size = c := by simp [C, Circuit.size, hgs]
  have hout_ex : ∀ (j : Fin q) (i : Fin b), ∃ idx < I + C.size,
      ∀ v : Fin I → Bool, (C.wires (List.ofFn v)).getD idx false =
        replaySwaps (swsRev v) (ansScan v) (words + j.val) i := by
    intro j i
    have hmem : (fun x : Fin I → Bool => replaySwaps (swsRev x) (ansScan x) (words + j.val) i) ∈
        (Set.range (fun idx : Fin I => fun v => v idx)) ∪ ({fun _ => false} ∪ Bout) :=
      Or.inr (Or.inr ⟨words + j.val, by dsimp [N, M] at *; omega, i, rfl⟩)
    obtain ⟨idx, hidx, hval⟩ := hwire _ hmem
    exact ⟨idx, by rw [hCsize]; omega, hval⟩
  let outBit : Fin q → Fin b → Fin (I + C.size) :=
    fun j i => ⟨Classical.choose (hout_ex j i), (Classical.choose_spec (hout_ex j i)).1⟩
  refine ⟨C, outBit, hfan, hread, ?_, ?_, ?_⟩
  · simp only [C]; rw [hCsize]; omega
  · rw [hCsize]
    let L := a + b + Nat.log2 (q + 1) + 3
    have hL3 : 3 ≤ L := by dsimp [L]; omega
    have hMpos : 1 ≤ M := by have := Nat.two_pow_pos a; dsimp [M, words]; omega
    have h4net : 4 * net.length = p * (p + 1) * N := bitonicSort_length 0 p true
    have hnet_cost : net.length * (11 * a + 12 * b + 23) ≤ 6 * (M * L ^ 3) := by
      have h1 : 11 * a + 12 * b + 23 ≤ 12 * L := by dsimp [L]; omega
      have h2 : p ≤ L := by dsimp [L]; omega
      have h3 : p + 1 ≤ L := by dsimp [L]; omega
      have h4 : 4 * (net.length * (11 * a + 12 * b + 23)) ≤ 24 * (M * L ^ 3) := by
        have e1 : 4 * (net.length * (11 * a + 12 * b + 23)) =
            (p * (p + 1) * N) * (11 * a + 12 * b + 23) := by
          rw [← Nat.mul_assoc, h4net]
        have hpp : p * (p + 1) ≤ L * L := Nat.mul_le_mul h2 h3
        have hppN : p * (p + 1) * N ≤ (L * L) * (2 * M) := Nat.mul_le_mul hpp hN2M
        have hprod := Nat.mul_le_mul hppN h1
        have e2 : (L * L) * (2 * M) * (12 * L) = 24 * (M * L ^ 3) := by
          have eL3 : L ^ 3 = L * L * L := by rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_one]
          rw [eL3]
          calc
            (L * L) * (2 * M) * (12 * L) = (2 * 12) * (M * (L * L * L)) := by
              simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
            _ = 24 * (M * (L * L * L)) := rfl
        rw [e1, ← e2]
        exact hprod
      omega
    have hscan_cost : N * (3 * b + 4) ≤ 6 * (M * L ^ 3) := by
      have h1 : 3 * b + 4 ≤ 3 * L := by dsimp [L]; omega
      have h2 : N * (3 * b + 4) ≤ (2 * M) * (3 * L) := Nat.mul_le_mul hN2M h1
      have hL1 : L ≤ L ^ 3 := by
        have hLL : L ≤ L * L := Nat.le_mul_of_pos_right L (by omega)
        have hLLL : L * L ≤ L * L * L := Nat.le_mul_of_pos_right (L * L) (by omega)
        have eL3 : L ^ 3 = L * L * L := by rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_one]
        omega
      have h3 : (2 * M) * (3 * L) = 6 * (M * L) := by
        calc
          (2 * M) * (3 * L) = (2 * 3) * (M * L) := by
            simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
          _ = 6 * (M * L) := rfl
      have h4 : 6 * (M * L) ≤ 6 * (M * L ^ 3) :=
        Nat.mul_le_mul_left 6 (Nat.mul_le_mul_left M hL1)
      omega
    have h2le : 2 ≤ M * L ^ 3 := by
      have h27 : 27 ≤ L ^ 3 := by
        have eL3 : L ^ 3 = L * L * L := by rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_one]
        have hLL : 9 ≤ L * L := Nat.mul_le_mul hL3 hL3
        have hLLL : 27 ≤ L * L * L := Nat.mul_le_mul hLL hL3
        omega
      have hm := Nat.mul_le_mul hMpos h27
      omega
    have hcomb : net.length * (11 * a + 6 * b + 23) + net.length * (6 * b) =
        net.length * (11 * a + 12 * b + 23) := by
      rw [← Nat.mul_add]
      congr 1
      omega
    have hrhs : 128 * (words + q) * (a + b + Nat.log2 (q + 1) + 3) ^ 3 = 128 * (M * L ^ 3) := by
      exact Nat.mul_assoc 128 M (L ^ 3)
    rw [hrhs]
    omega
  · intro table address x j i
    have hx_len : x.length = I := by
      dsimp only [x, I]
      rw [List.length_append, list_ofFn_flatten_length, list_ofFn_flatten_length]
    let v : Fin I → Bool := fun idx => x.getD idx.val false
    have hv_eq : List.ofFn v = x := by
      apply List.ext_getElem (by simp [hx_len])
      intro idx h1 h2
      rw [List.getElem_ofFn]
      simp only [v, List.getD_eq_getElem _ _ h2]
    have hwire_j := (Classical.choose_spec (hout_ex j i)).2 v
    rw [hv_eq] at hwire_j
    change (C.wires x).getD (Classical.choose (hout_ex j i)) false = table (address j) i
    rw [hwire_j]
    have hv_tab : ∀ (r : Fin words) (c : Fin b),
        v ⟨r.val * b + c.val, by
          have := Nat.mul_le_mul_right b (show r.val + 1 ≤ words by omega)
          rw [Nat.succ_mul] at this; omega⟩ = table r c := by
      intro r c
      dsimp only [v, x]
      have hlt : r.val * b + c.val < ((List.ofFn (fun r' : Fin words => List.ofFn (table r'))).flatten).length := by
        rw [list_ofFn_flatten_length]
        have := Nat.mul_le_mul_right b (show r.val + 1 ≤ words by omega)
        rw [Nat.succ_mul] at this; omega
      rw [List.getD_append _ _ _ _ hlt]
      exact list_ofFn_flatten_getD table r c
    have hv_addr : ∀ (r : Fin q) (c : Fin a),
        v ⟨words * b + r.val * a + c.val, by
          have := Nat.mul_le_mul_right a (show r.val + 1 ≤ q by omega)
          rw [Nat.succ_mul] at this; omega⟩ = (address r).val.testBit c.val := by
      intro r c
      dsimp only [v, x]
      have hlen1 : ((List.ofFn (fun r' : Fin words => List.ofFn (table r'))).flatten).length = words * b :=
        list_ofFn_flatten_length table
      rw [List.getD_append_right _ _ _ _ (by omega)]
      have hsub : words * b + r.val * a + c.val - words * b = r.val * a + c.val := by omega
      rw [hlen1, hsub]
      exact list_ofFn_flatten_getD (fun r' c' => (address r').val.testBit c'.val) r c
    let sws := netSwaps recKey net (st0 v)
    let pFwd : Nat → Nat := replaySwaps sws id
    let pInv : Nat → Nat := replaySwaps sws.reverse id
    have hinv_fwd : ∀ idx, pFwd (pInv idx) = idx := by
      intro idx
      have h1 : replaySwaps sws pInv idx = idx := by
        have h := congrFun (replaySwaps_reverse_cancel sws.reverse id) idx
        rw [List.reverse_reverse] at h
        exact h
      have h2 : replaySwaps sws pInv idx = pInv (pFwd idx) :=
        congrFun (replaySwaps_comp sws pInv id) idx
      have h3 : replaySwaps sws.reverse pFwd idx = idx :=
        congrFun (replaySwaps_reverse_cancel sws id) idx
      have h4 : replaySwaps sws.reverse pFwd idx = pFwd (pInv idx) :=
        congrFun (replaySwaps_comp sws.reverse pFwd id) idx
      rw [← h4]
      exact h3
    have hpInv_lt : ∀ idx < N, pInv idx < N := by
      have hgen : ∀ (l : List (Nat × Nat × Bool)), (∀ c ∈ l, c.1 < N ∧ c.2.1 < N) →
          ∀ (f : Nat → Nat), (∀ k < N, f k < N) → ∀ k < N, replaySwaps l f k < N := by
        intro l
        induction l with
        | nil => intro _ f hf k hk; exact hf k hk
        | cons c rest ih =>
          rcases c with ⟨u', v', sw'⟩
          intro hl f hf k hk
          have hc := hl (u', v', sw') List.mem_cons_self
          apply ih (fun c' hc' => hl c' (List.mem_cons_of_mem _ hc')) _ _ k hk
          intro m hm
          simp only [applySwap]
          cases sw'
          · exact hf m hm
          · simp only [↓reduceIte]
            by_cases h1 : m = u'
            · simp [h1, hf v' hc.2]
            · by_cases h2 : m = v'
              · simp only [h1, ↓reduceIte]; simp only [h2, ↓reduceIte]; exact hf u' hc.1
              · simp [h1, h2, hf m hm]
      have hsws_lt : ∀ c ∈ sws.reverse, c.1 < N ∧ c.2.1 < N := by
        intro c hc
        rcases List.getElem_of_mem hc with ⟨t, ht, rfl⟩
        have ht' : t < net.length := by
          have : sws.reverse.length = net.length := by simp [sws, netSwaps_length]
          omega
        rcases hidx_rev t ht' with ⟨u', v', hu', hv', hEq⟩
        have hget : (swsRev v).getD t (0, 0, false) = sws.reverse[t]'ht :=
          List.getD_eq_getElem _ _ ht
        have hv0 := hEq v
        rw [hget] at hv0
        rw [hv0.1, hv0.2]
        exact ⟨hu', hv'⟩
      exact hgen sws.reverse hsws_lt id (fun k hk => hk)
    have hst_inv : ∀ idx, runNet recKey net (st0 v) (pInv idx) = st0 v idx := by
      intro idx
      rw [runNet_eq_replay]
      have h1 : replaySwaps sws (st0 v) (pInv idx) = st0 v (pFwd (pInv idx)) :=
        congrFun (replaySwaps_comp sws (st0 v) id) (pInv idx)
      rw [h1, hinv_fwd]
    have hst0_tab : ∀ idx (hidx : idx < words),
        (st0 v idx).keyBit (a + 1) = false ∧ (st0 v idx).keyBit 0 = false ∧
        recKey (st0 v idx) = 2 * idx ∧ (st0 v idx).valBit = table ⟨idx, hidx⟩ := by
      intro idx hidx
      have h1 : (st0 v idx).keyBit (a + 1) = false := by simp [st0, hidx]
      have h2 : (st0 v idx).keyBit 0 = false := by simp [st0, hidx]
      have h3 : recKey (st0 v idx) = 2 * idx := by
        have hk := keyBits_val a false false idx hidx
        simpa [recKey, st0, hidx] using hk
      have h4 : (st0 v idx).valBit = table ⟨idx, hidx⟩ := by
        funext c
        simp only [st0, hidx, ↓reduceDIte]
        exact hv_tab ⟨idx, hidx⟩ c
      exact ⟨h1, h2, h3, h4⟩
    have hst0_q : ∀ r : Fin q,
        (st0 v (words + r.val)).keyBit (a + 1) = false ∧
        (st0 v (words + r.val)).keyBit 0 = true ∧
        recKey (st0 v (words + r.val)) = 2 * (address r).val + 1 := by
      intro r
      have hnot : ¬ words + r.val < words := by omega
      have hltM : words + r.val < M := by dsimp [M]; omega
      have h1 : (st0 v (words + r.val)).keyBit (a + 1) = false := by simp [st0, hnot, hltM]
      have h2 : (st0 v (words + r.val)).keyBit 0 = true := by simp [st0, hnot, hltM]
      have h3 : recKey (st0 v (words + r.val)) = 2 * (address r).val + 1 := by
        have hk := keyBits_val a false true (address r).val (address r).isLt
        have hkb : (st0 v (words + r.val)).keyBit =
            (fun j => if j = 0 then true else if j = a + 1 then false else (address r).val.testBit (j - 1)) := by
          funext t
          simp only [st0, hnot, hltM, ↓reduceDIte]
          by_cases ht0 : t = 0
          · simp [ht0]
          · by_cases hta : t = a + 1
            · simp [ht0, hta]
            · by_cases hta' : t - 1 < a
              · simp only [ht0, hta, hta', ↓reduceIte, ↓reduceDIte]
                have e1 : words + r.val - words = r.val := by omega
                have hA := hv_addr r ⟨t - 1, hta'⟩
                simpa only [e1] using hA
              · simp only [ht0, hta, hta', ↓reduceIte, ↓reduceDIte]
                exact (Nat.testBit_lt_two_pow ((address r).isLt.trans_le
                  (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))).symm
        change bitsVal (st0 v (words + r.val)).keyBit (a + 2) = _
        rw [hkb]
        simpa using hk
      exact ⟨h1, h2, h3⟩
    have hsorted := bitonicSort_sorted recKey p (st0 v)
    have htab_real : ∀ t < N, (runNet recKey net (st0 v) t).keyBit (a + 1) = false →
        (runNet recKey net (st0 v) t).keyBit 0 = false →
        ∃ addr : Fin words, recKey (runNet recKey net (st0 v) t) = 2 * addr.val ∧
          (runNet recKey net (st0 v) t).valBit = table addr := by
      intro t ht hd0 ht0
      have hrun_eq : runNet recKey net (st0 v) t = st0 v (pFwd t) := by
        rw [runNet_eq_replay]
        exact congrFun (replaySwaps_comp sws (st0 v) id) t
      rw [hrun_eq] at hd0 ht0 ⊢
      let orig := pFwd t
      by_cases h1 : orig < words
      · rcases hst0_tab orig h1 with ⟨_, _, hk, hv⟩
        exact ⟨⟨orig, h1⟩, hk, hv⟩
      · by_cases h2 : orig < M
        · have hnot : (st0 v orig).keyBit 0 = true := by simp [st0, h1, h2]
          rw [hnot] at ht0; cases ht0
        · have hnot : (st0 v orig).keyBit 0 = true := by simp [st0, h1, h2]
          rw [hnot] at ht0; cases ht0
    have htab_exists : ∀ addr : Fin words, ∃ t < N,
        (runNet recKey net (st0 v) t).keyBit (a + 1) = false ∧
        (runNet recKey net (st0 v) t).keyBit 0 = false ∧
        recKey (runNet recKey net (st0 v) t) = 2 * addr.val := by
      intro addr
      refine ⟨pInv addr.val, hpInv_lt addr.val (by dsimp [N, M] at *; omega), ?_⟩
      rw [hst_inv addr.val]
      rcases hst0_tab addr.val addr.isLt with ⟨h1, h2, h3, _⟩
      exact ⟨h1, h2, h3⟩
    have hscan_ok := (scanStep_answer N (runNet recKey net (st0 v)) table hsorted htab_real htab_exists N (Nat.le_refl N)).1
    have hscan_indep : ∀ m, (scanStep N (fun x => runNet recKey net (st0 x)) m v).2 =
        (scanStep N (fun _ : Fin 0 → Bool => runNet recKey net (st0 v)) m (fun z => z.elim0)).2 := by
      have hboth : ∀ m, scanStep N (fun x => runNet recKey net (st0 x)) m v =
          scanStep N (fun _ : Fin 0 → Bool => runNet recKey net (st0 v)) m (fun z => z.elim0) := by
        intro m
        induction m with
        | zero => rfl
        | succ m ih =>
          simp only [scanStep, ih]
      intro m
      rw [hboth m]
    change replaySwaps sws.reverse (ansScan v) (words + j.val) i = table (address j) i
    have hrev_app : replaySwaps sws.reverse (ansScan v) (words + j.val) = ansScan v (pInv (words + j.val)) :=
      congrFun (replaySwaps_comp sws.reverse (ansScan v) id) (words + j.val)
    rw [hrev_app]
    dsimp only [ansScan]
    rw [hscan_indep N]
    have hlt_q : words + j.val < N := by dsimp [N, M] at *; omega
    have hinv_q := hpInv_lt (words + j.val) hlt_q
    have hq_rec := hst0_q j
    have hEq_ans := hscan_ok (pInv (words + j.val)) hinv_q
      (by rw [hst_inv]; exact hq_rec.1)
      (by rw [hst_inv]; exact hq_rec.2.1)
      (address j)
      (by rw [hst_inv]; exact hq_rec.2.2)
    exact congrFun hEq_ans i

end Lookup049

end PEqualNP.Outside.L_clb_100_aux

namespace PEqualNP.Outside.L_clb_100_aux
namespace Sem

theorem len_filter_range (m : Nat) (p : Nat → Bool) :
    ((List.range m).filter p).length = ((Finset.range m).filter (fun x => p x = true)).card := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih, Finset.range_add_one,
      Finset.filter_insert]
    by_cases h : p m = true
    · simp [h]
    · simp [h]

def cnt (T : Nat → Nat → Bool) (w h s c : Nat) : Nat :=
  ((List.range (2 ^ (w + h))).filter (fun bits =>
    bits % 2 ^ w == s && (bits >>> h) % 2 ^ w == c &&
    (List.range h).all (fun site => T site ((bits >>> site) % 2 ^ (w + 1))))).length

def SP (T : Nat → Nat → Bool) (w h s c : Nat) : Finset Nat :=
  (Finset.range (2 ^ (w + h))).filter (fun bits =>
    bits % 2 ^ w = s ∧ (bits >>> h) % 2 ^ w = c ∧
    ∀ site < h, T site ((bits >>> site) % 2 ^ (w + 1)) = true)

theorem cnt_eq (T : Nat → Nat → Bool) (w h s c : Nat) : cnt T w h s c = (SP T w h s c).card := by
  unfold cnt SP
  rw [len_filter_range]
  congr 1
  apply Finset.filter_congr
  intro x _
  simp [List.all_eq_true, and_assoc]

theorem win_mod (b' w h site : Nat) (hs : site < h) :
    ((b' % 2 ^ (w + h)) >>> site) % 2 ^ (w + 1) = (b' >>> site) % 2 ^ (w + 1) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases hi : i < w + 1
  · have : site + i < w + h := by omega
    simp [hi, this]
  · simp [hi]

theorem cur_mod (b' w h : Nat) :
    ((b' % 2 ^ (w + h)) >>> h) % 2 ^ w = ((b' >>> h) % 2 ^ (w + 1)) % 2 ^ w := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases hi : i < w
  · have h1 : h + i < w + h := by omega
    have h2 : i < w + 1 := by omega
    simp [hi, h1, h2]
  · simp [hi]

theorem half_win (b' w h : Nat) :
    ((b' >>> h) % 2 ^ (w + 1)) / 2 = (b' >>> (h + 1)) % 2 ^ w := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [← Nat.shiftRight_one, Nat.testBit_shiftRight]
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases hi : i < w
  · have h2 : 1 + i < w + 1 := by omega
    have e : h + (1 + i) = h + 1 + i := by omega
    simp [hi, h2, e]
  · have h2 : ¬ (1 + i < w + 1) := by omega
    simp [hi, h2]

theorem seed_mod (b' w h : Nat) : (b' % 2 ^ (w + h)) % 2 ^ w = b' % 2 ^ w :=
  Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (Nat.le_add_right w h))

theorem recon (w h u b : Nat) (hb : b < 2 ^ (w + h)) (hu : u < 2 ^ (w + 1))
    (hcur : (b >>> h) % 2 ^ w = u % 2 ^ w) :
    ((2 ^ (w + h) * (u / 2 ^ w) + b) >>> h) % 2 ^ (w + 1) = u := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.testBit_two_pow_mul_add _ hb]
  by_cases hi : i < w
  · have h1 : h + i < w + h := by omega
    have h2 : i < w + 1 := by omega
    have hc := congrArg (fun z => z.testBit i) hcur
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, hi, decide_true, Bool.true_and] at hc
    simp [h1, h2, hc]
  · by_cases hiw : i = w
    · subst hiw
      have h1 : ¬ (h + i < i + h) := by omega
      have h3 : h + i - (i + h) = 0 := by omega
      rw [if_neg h1, h3, Nat.testBit_div_two_pow]
      simp
    · have h2 : ¬ (i < w + 1) := by omega
      have hlt : u < 2 ^ i := lt_of_lt_of_le hu (Nat.pow_le_pow_right (by omega) (by omega))
      simp [h2, Nat.testBit_lt_two_pow hlt]

theorem top_eq (w h b' : Nat) (hb : b' < 2 ^ (w + (h + 1))) :
    ((b' >>> h) % 2 ^ (w + 1)) / 2 ^ w = b' / 2 ^ (w + h) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_div_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases hi : i = 0
  · subst hi
    simp [Nat.add_comm h w]
  · have h2 : ¬ (i + w < w + 1) := by omega
    have hlt : b' < 2 ^ (i + (w + h)) := lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) (by omega))
    simp [h2, Nat.testBit_lt_two_pow hlt]

theorem rec_card (T : Nat → Nat → Bool) (w h s c' : Nat) :
    (SP T w (h + 1) s c').card =
      ∑ u ∈ (Finset.range (2 ^ (w + 1))).filter (fun u => u / 2 = c' ∧ T h u = true),
        (SP T w h s (u % 2 ^ w)).card := by
  classical
  have hmaps : ((SP T w (h + 1) s c' : Finset Nat) : Set Nat).MapsTo
      (fun b' => (b' >>> h) % 2 ^ (w + 1)) (Finset.range (2 ^ (w + 1))) := by
    intro b' _
    exact Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.mod_lt _ (Nat.two_pow_pos _)))
  rw [Finset.card_eq_sum_card_fiberwise hmaps, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  have hu' : u < 2 ^ (w + 1) := Finset.mem_range.mp hu
  split_ifs with hc
  · apply Finset.card_nbij' (fun b' => b' % 2 ^ (w + h)) (fun b => 2 ^ (w + h) * (u / 2 ^ w) + b)
    · intro b' hb'
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, SP, Finset.mem_filter, Finset.mem_range,
        Finset.mem_coe] at hb' ⊢
      obtain ⟨⟨hlt, hseed, hcur, hsites⟩, hfu⟩ := hb'
      refine ⟨Nat.mod_lt _ (Nat.two_pow_pos _), ?_, ?_, ?_⟩
      · rw [seed_mod]; exact hseed
      · rw [cur_mod, hfu]
      · intro site hs
        rw [win_mod _ _ _ _ hs]
        exact hsites site (by omega)
    · intro b hb
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, SP, Finset.mem_filter, Finset.mem_range,
        Finset.mem_coe] at hb ⊢
      obtain ⟨hlt, hseed, hcur, hsites⟩ := hb
      have hkey := recon w h u b hlt hu' hcur
      have ht : u / 2 ^ w ≤ 1 := by
        have : u / 2 ^ w < 2 := by
          rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
          rw [Nat.pow_succ] at hu'; omega
        omega
      have hmod : (2 ^ (w + h) * (u / 2 ^ w) + b) % 2 ^ (w + h) = b := by
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
      refine ⟨⟨?_, ?_, ?_, ?_⟩, hkey⟩
      · have h1 : 2 ^ (w + h) * (u / 2 ^ w) ≤ 2 ^ (w + h) * 1 := Nat.mul_le_mul_left _ ht
        have h2 : 2 ^ (w + (h + 1)) = 2 * 2 ^ (w + h) := by rw [← Nat.add_assoc, Nat.pow_succ]; omega
        omega
      · rw [← seed_mod _ w h, hmod]; exact hseed
      · rw [← half_win, hkey]; exact hc.1
      · intro site hs
        by_cases hsh : site = h
        · subst hsh; rw [hkey]; exact hc.2
        · have hs' : site < h := by omega
          rw [← win_mod _ w h site hs', hmod]
          exact hsites site hs'
    · intro b' hb'
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, SP, Finset.mem_filter, Finset.mem_range] at hb'
      obtain ⟨⟨hlt, -, -, -⟩, hfu⟩ := hb'
      show 2 ^ (w + h) * (u / 2 ^ w) + b' % 2 ^ (w + h) = b'
      rw [← hfu, top_eq w h b' hlt]
      exact Nat.div_add_mod b' (2 ^ (w + h))
    · intro b hb
      simp only [SP, Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_range] at hb
      show (2 ^ (w + h) * (u / 2 ^ w) + b) % 2 ^ (w + h) = b
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hb.1]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro b' hb' hfu
    apply hc
    simp only [SP, Finset.mem_filter, Finset.mem_range] at hb'
    obtain ⟨hlt, hseed, hcur, hsites⟩ := hb'
    refine ⟨?_, ?_⟩
    · rw [← hfu, half_win]; exact hcur
    · rw [← hfu]; exact hsites h (by omega)

end Sem
end PEqualNP.Outside.L_clb_100_aux

namespace PEqualNP.Outside.L_clb_100_aux
namespace Sem

theorem sum_parity (U : Finset Nat) (f : Nat → Nat) :
    (∑ u ∈ U, f u) % 2 = (U.filter (fun u => f u % 2 = 1)).card % 2 := by
  classical
  induction U using Finset.induction_on with
  | empty => simp
  | insert a U ha ih =>
    rw [Finset.sum_insert ha, Finset.filter_insert]
    by_cases h : f a % 2 = 1
    · rw [if_pos h, Finset.card_insert_of_notMem (by simp [ha])]
      omega
    · rw [if_neg h]
      omega

def Par (T : Nat → Nat → Bool) (w h s c : Nat) : Bool := (cnt T w h s c).testBit 0

theorem par_iff (T : Nat → Nat → Bool) (w h s c : Nat) :
    Par T w h s c = true ↔ (SP T w h s c).card % 2 = 1 := by
  unfold Par
  rw [Nat.testBit_zero, cnt_eq]
  simp

theorem par_zero (T : Nat → Nat → Bool) (w s c : Nat) (hs : s < 2 ^ w) :
    Par T w 0 s c = decide (s = c) := by
  have hcard : (SP T w 0 s c).card = if s = c then 1 else 0 := by
    split_ifs with h
    · subst h
      have : SP T w 0 s s = {s} := by
        ext x
        simp only [SP, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, Nat.add_zero,
          Nat.shiftRight_zero, Nat.not_lt_zero, false_imp_iff, implies_true, and_true]
        constructor
        · rintro ⟨hx, h1, -⟩
          rw [Nat.mod_eq_of_lt hx] at h1; exact h1
        · rintro rfl
          exact ⟨hs, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hs⟩
      rw [this, Finset.card_singleton]
    · rw [Finset.card_eq_zero, SP, Finset.filter_eq_empty_iff]
      rintro x - ⟨h1, h2, -⟩
      simp only [Nat.shiftRight_zero] at h2
      exact h (h1.symm.trans h2)
  apply Bool.eq_iff_iff.mpr
  rw [par_iff, hcard]
  by_cases h : s = c <;> simp [h]

def parents (T : Nat → Nat → Bool) (w h s c' : Nat) : Finset Nat :=
  (Finset.range (2 ^ (w + 1))).filter
    (fun u => u / 2 = c' ∧ T h u = true ∧ Par T w h s (u % 2 ^ w) = true)

theorem par_succ (T : Nat → Nat → Bool) (w h s c' : Nat) :
    Par T w (h + 1) s c' = true ↔ (parents T w h s c').card % 2 = 1 := by
  rw [par_iff, rec_card, sum_parity]
  have : ((Finset.range (2 ^ (w + 1))).filter (fun u => u / 2 = c' ∧ T h u = true)).filter
      (fun u => (SP T w h s (u % 2 ^ w)).card % 2 = 1) = parents T w h s c' := by
    unfold parents
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro u _
    rw [par_iff, and_assoc]
  rw [this]

theorem parents_card_le (T : Nat → Nat → Bool) (w h s c' : Nat) : (parents T w h s c').card ≤ 2 := by
  have hsub : parents T w h s c' ⊆ {2 * c', 2 * c' + 1} := by
    intro u hu
    simp only [parents, Finset.mem_filter] at hu
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  exact (Finset.card_le_card hsub).trans (Finset.card_le_two)

def patOf (w : Nat) (bit : Nat → Bool) : Nat :=
  (List.range (w + 1)).foldl (fun (acc j : Nat) => acc ||| ((bit j).toNat <<< j)) 0

theorem foldl_testBit (bit : Nat → Bool) : ∀ m i,
    ((List.range m).foldl (fun (acc j : Nat) => acc ||| ((bit j).toNat <<< j)) 0).testBit i =
      (decide (i < m) && bit i)
  | 0, i => by simp
  | m + 1, i => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.testBit_or,
      foldl_testBit bit m i, Nat.testBit_shiftLeft]
    by_cases him : i = m
    · subst him
      cases bit i <;> simp
    · by_cases hlt : i < m
      · have h1 : ¬ (i ≥ m) := by omega
        have h2 : i < m + 1 := by omega
        simp [hlt, h1, h2]
      · have h1 : i ≥ m := by omega
        have h2 : ¬ (i < m + 1) := by omega
        have h3 : i - m ≠ 0 := by omega
        have h4 : Nat.testBit 1 (i - m) = false := Nat.testBit_lt_two_pow (Nat.one_lt_two_pow h3)
        cases bit m <;> simp [hlt, h1, h2, h4]

theorem patOf_testBit (w : Nat) (bit : Nat → Bool) (i : Nat) :
    (patOf w bit).testBit i = (decide (i < w + 1) && bit i) := foldl_testBit bit (w + 1) i

theorem patOf_congr (w : Nat) (b1 b2 : Nat → Bool) (h : ∀ j, j ≤ w → b1 j = b2 j) :
    patOf w b1 = patOf w b2 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [patOf_testBit, patOf_testBit]
  by_cases hi : i < w + 1
  · simp [hi, h i (by omega)]
  · simp [hi]

theorem patOf_lt (w : Nat) (bit : Nat → Bool) : patOf w bit < 2 ^ (w + 1) := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [patOf_testBit]
  have : ¬ (i < w + 1) := by omega
  simp [this]

theorem pat_window (n w x i : Nat) (h : i + w < n) :
    patOf w (fun j => x.testBit ((i + j) % n)) = (x >>> i) % 2 ^ (w + 1) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [patOf_testBit, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases hk : k < w + 1
  · have : (i + k) % n = i + k := Nat.mod_eq_of_lt (by omega)
    simp [hk, this]
  · simp [hk]

end Sem
end PEqualNP.Outside.L_clb_100_aux

namespace PEqualNP.Outside.L_clb_100_aux
namespace Sem

def closeBit (n w s c p : Nat) : Bool :=
  if n - w ≤ p then c.testBit (p - (n - w)) else s.testBit p

def closePat (n w i s c : Nat) : Nat := patOf w (fun j => closeBit n w s c ((i + j) % n))

def G (T : Nat → Nat → Bool) (sm em : Nat → Bool) (n w s c : Nat) : Bool :=
  sm s && em c && (List.range w).all (fun r => T (n - w + r) (closePat n w (n - w + r) s c))

theorem close_bit (n w x i j : Nat) (hn : 0 < n) (hw : w ≤ n)
    (hi : n - w ≤ i) (hin : i < n) (hj : j ≤ w) :
    x.testBit ((i + j) % n) =
      closeBit n w (x % 2 ^ w) ((x >>> (n - w)) % 2 ^ w) ((i + j) % n) := by
  have hp : (i + j) % n = i + j ∨ ((i + j) % n = i + j - n ∧ n ≤ i + j) := by
    by_cases hlt : i + j < n
    · exact Or.inl (Nat.mod_eq_of_lt hlt)
    · right
      refine ⟨?_, by omega⟩
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  have hpn : (i + j) % n < n := Nat.mod_lt _ hn
  generalize (i + j) % n = p at hp hpn ⊢
  unfold closeBit
  split_ifs with hL
  · rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
    have h1 : p - (n - w) < w := by omega
    have h2 : n - w + (p - (n - w)) = p := by omega
    simp [h1, h2]
  · rw [Nat.testBit_mod_two_pow]
    have h1 : p < w := by omega
    simp [h1]

theorem count_split (T : Nat → Nat → Bool) (sm em : Nat → Bool) (n w : Nat) (hn : 0 < n) (hw : w ≤ n) :
    ((List.range (2 ^ n)).filter (fun x => sm (x % 2 ^ w) && em ((x >>> (n - w)) % 2 ^ w) &&
        (List.range n).all (fun i => T i (patOf w (fun j => x.testBit ((i + j) % n)))))).length =
      ∑ e ∈ Finset.range (2 ^ w * 2 ^ w),
        if G T sm em n w (e % 2 ^ w) (e / 2 ^ w) = true then cnt T w (n - w) (e % 2 ^ w) (e / 2 ^ w) else 0 := by
  classical
  rw [len_filter_range]
  have hD : 0 < 2 ^ w := Nat.two_pow_pos w
  have hmaps : (((Finset.range (2 ^ n)).filter (fun x => (sm (x % 2 ^ w) && em ((x >>> (n - w)) % 2 ^ w) &&
        (List.range n).all (fun i => T i (patOf w (fun j => x.testBit ((i + j) % n))))) = true) :
          Finset Nat) : Set Nat).MapsTo
      (fun x => 2 ^ w * ((x >>> (n - w)) % 2 ^ w) + x % 2 ^ w) (Finset.range (2 ^ w * 2 ^ w)) := by
    intro x _
    refine Finset.mem_coe.mpr (Finset.mem_range.mpr ?_)
    have h1 : (x >>> (n - w)) % 2 ^ w < 2 ^ w := Nat.mod_lt _ hD
    have h2 : x % 2 ^ w < 2 ^ w := Nat.mod_lt _ hD
    calc 2 ^ w * ((x >>> (n - w)) % 2 ^ w) + x % 2 ^ w
        < 2 ^ w * ((x >>> (n - w)) % 2 ^ w) + 2 ^ w := by omega
      _ = 2 ^ w * ((x >>> (n - w)) % 2 ^ w + 1) := by rw [Nat.mul_succ]
      _ ≤ 2 ^ w * 2 ^ w := Nat.mul_le_mul_left _ h1
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro e he
  have hpow : 2 ^ (w + (n - w)) = 2 ^ n := by rw [Nat.add_sub_cancel' hw]
  have hsite : ∀ x i, i < n - w → patOf w (fun j => x.testBit ((i + j) % n)) = (x >>> i) % 2 ^ (w + 1) :=
    fun x i hi => pat_window n w x i (by omega)
  have hclose : ∀ x r, r < w → patOf w (fun j => x.testBit ((n - w + r + j) % n)) =
      closePat n w (n - w + r) (x % 2 ^ w) ((x >>> (n - w)) % 2 ^ w) := by
    intro x r hr
    unfold closePat
    apply patOf_congr
    intro j hj
    exact close_bit n w x (n - w + r) j hn hw (by omega) (by omega) hj
  have hfib : ∀ x, 2 ^ w * ((x >>> (n - w)) % 2 ^ w) + x % 2 ^ w = e ↔
      (x % 2 ^ w = e % 2 ^ w ∧ (x >>> (n - w)) % 2 ^ w = e / 2 ^ w) := by
    intro x
    constructor
    · intro h
      subst h
      refine ⟨?_, ?_⟩
      · rw [Nat.mul_add_mod, Nat.mod_mod]
      · rw [Nat.mul_add_div hD, Nat.div_eq_of_lt (Nat.mod_lt _ hD), Nat.add_zero]
    · rintro ⟨h1, h2⟩
      rw [h1, h2]
      exact Nat.div_add_mod e (2 ^ w)
  split_ifs with hG
  · rw [cnt_eq]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, SP, hfib, hpow, Bool.and_eq_true,
      List.all_eq_true, List.mem_range]
    simp only [G, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hG
    constructor
    · rintro ⟨⟨hx, ⟨hsm, hem⟩, hall⟩, hs, hc⟩
      refine ⟨hx, hs, hc, fun site hsite' => ?_⟩
      rw [← hsite x site hsite']
      exact hall site (by omega)
    · rintro ⟨hx, hs, hc, hall⟩
      refine ⟨⟨hx, ⟨by rw [hs]; exact hG.1.1, by rw [hc]; exact hG.1.2⟩, fun i hi => ?_⟩, hs, hc⟩
      by_cases hiL : i < n - w
      · rw [hsite x i hiL]; exact hall i hiL
      · have hr : i - (n - w) < w := by omega
        have hi' : n - w + (i - (n - w)) = i := by omega
        have := hclose x (i - (n - w)) hr
        rw [hi'] at this
        rw [this, hs, hc]
        have h2 := hG.2 (i - (n - w)) hr
        rw [hi'] at h2
        exact h2
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x hx hfx
    apply hG
    simp only [Finset.mem_filter, Finset.mem_range, Bool.and_eq_true, List.all_eq_true,
      List.mem_range] at hx
    obtain ⟨hxlt, ⟨hsm, hem⟩, hall⟩ := hx
    obtain ⟨hs, hc⟩ := (hfib x).mp hfx
    simp only [G, Bool.and_eq_true, List.all_eq_true, List.mem_range]
    refine ⟨⟨by rw [← hs]; exact hsm, by rw [← hc]; exact hem⟩, fun r hr => ?_⟩
    rw [← hs, ← hc, ← hclose x r hr]
    exact hall (n - w + r) (by omega)

theorem count_parity (T : Nat → Nat → Bool) (sm em : Nat → Bool) (n w : Nat) (hn : 0 < n) (hw : w ≤ n) :
    (((List.range (2 ^ n)).filter (fun x => sm (x % 2 ^ w) && em ((x >>> (n - w)) % 2 ^ w) &&
        (List.range n).all (fun i => T i (patOf w (fun j => x.testBit ((i + j) % n)))))).length.testBit 0 = true) ↔
      ((Finset.range (2 ^ w * 2 ^ w)).filter (fun e => G T sm em n w (e % 2 ^ w) (e / 2 ^ w) = true ∧
        Par T w (n - w) (e % 2 ^ w) (e / 2 ^ w) = true)).card % 2 = 1 := by
  rw [count_split T sm em n w hn hw, Nat.testBit_zero, decide_eq_true_eq, sum_parity]
  have : (Finset.range (2 ^ w * 2 ^ w)).filter (fun e =>
      (if G T sm em n w (e % 2 ^ w) (e / 2 ^ w) = true then cnt T w (n - w) (e % 2 ^ w) (e / 2 ^ w) else 0) % 2 = 1) =
      (Finset.range (2 ^ w * 2 ^ w)).filter (fun e => G T sm em n w (e % 2 ^ w) (e / 2 ^ w) = true ∧
        Par T w (n - w) (e % 2 ^ w) (e / 2 ^ w) = true) := by
    apply Finset.filter_congr
    intro e _
    unfold Par
    rw [Nat.testBit_zero, decide_eq_true_eq]
    split_ifs with h
    · simp [h]
    · simp [h]
  rw [this]

end Sem
end PEqualNP.Outside.L_clb_100_aux

namespace PEqualNP.Outside.L_clb_100_aux
namespace Arr

open Bitonic

theorem count_applySwap {α : Type*} (N u v : Nat) (hu : u < N) (hv : v < N) (sw : Bool)
    (st : Nat → α) (P : α → Prop) [DecidablePred P] :
    ((Finset.range N).filter (fun i => P (applySwap u v sw st i))).card =
      ((Finset.range N).filter (fun i => P (st i))).card := by
  cases sw with
  | false => rfl
  | true =>
    apply Finset.card_nbij' (fun i => if i = u then v else if i = v then u else i)
      (fun i => if i = u then v else if i = v then u else i)
    · intro i hi
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq, applySwap, if_true] at hi ⊢
      by_cases h1 : i = u
      · subst h1
        by_cases h2 : i = v
        · subst h2; simpa using hi
        · simp only [if_true] at hi ⊢; exact ⟨hv, hi.2⟩
      · by_cases h2 : i = v
        · subst h2; simp only [h1, if_false, if_true] at hi ⊢; exact ⟨hu, hi.2⟩
        · simp only [h1, h2, if_false] at hi ⊢; exact hi
    · intro i hi
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq, applySwap, if_true] at hi ⊢
      by_cases h1 : i = u
      · subst h1
        by_cases h2 : v = i
        · subst h2; simpa using hi
        · simp only [if_true, h2, if_false] at hi ⊢; exact ⟨hv, hi.2⟩
      · by_cases h2 : i = v
        · subst h2
          simp only [h1, if_false, if_true] at hi ⊢; exact ⟨hu, hi.2⟩
        · have h3 : ¬ (i = u) := h1
          simp only [h1, h2, if_false] at hi ⊢; exact hi
    · intro i _
      show (if (if i = u then v else if i = v then u else i) = u then v
        else if (if i = u then v else if i = v then u else i) = v then u
        else (if i = u then v else if i = v then u else i)) = i
      by_cases h1 : i = u
      · subst h1; by_cases h2 : v = i
        · subst h2; simp
        · simp [h2]
      · by_cases h2 : i = v
        · subst h2; simp [h1]
        · simp [h1, h2]
    · intro i _
      show (if (if i = u then v else if i = v then u else i) = u then v
        else if (if i = u then v else if i = v then u else i) = v then u
        else (if i = u then v else if i = v then u else i)) = i
      by_cases h1 : i = u
      · subst h1; by_cases h2 : v = i
        · subst h2; simp
        · simp [h2]
      · by_cases h2 : i = v
        · subst h2; simp [h1]
        · simp [h1, h2]

theorem count_runNet {α : Type*} (key : α → Nat) (N : Nat) (net : List (Nat × Nat × Bool))
    (hnet : ∀ c ∈ net, c.1 < N ∧ c.2.1 < N) (st : Nat → α) (P : α → Prop) [DecidablePred P] :
    ((Finset.range N).filter (fun i => P (runNet key net st i))).card =
      ((Finset.range N).filter (fun i => P (st i))).card := by
  induction net generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, asc⟩
    have hc := hnet (u, v, asc) List.mem_cons_self
    have h1 := ih (fun c' hc' => hnet c' (List.mem_cons_of_mem _ hc'))
      (applySwap u v (swapBit (key (st u)) (key (st v)) asc) st)
    have h2 := count_applySwap N u v hc.1 hc.2 (swapBit (key (st u)) (key (st v)) asc) st P
    exact h1.trans h2

theorem all_runNet {α : Type*} (key : α → Nat) (N : Nat) (net : List (Nat × Nat × Bool))
    (hnet : ∀ c ∈ net, c.1 < N ∧ c.2.1 < N) (st : Nat → α) (P : α → Prop)
    (h : ∀ i < N, P (st i)) : ∀ i < N, P (runNet key net st i) := by
  classical
  intro i hi
  by_contra hne
  have hc := count_runNet key N net hnet st (fun a => ¬ P a)
  have h0 : ((Finset.range N).filter (fun i => ¬ P (st i))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro j hj; simpa using h j (Finset.mem_range.mp hj)
  rw [h0, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hc
  exact hc (Finset.mem_range.mpr hi) hne

theorem unique_of_neighbours (N : Nat) (a : Nat → Nat)
    (hmono : ∀ i j, i ≤ j → j < N → a i ≤ a j) (j : Nat) (hj : j < N)
    (hl : ¬ (0 < j ∧ a (j - 1) = a j)) (hr : ¬ (j + 1 < N ∧ a (j + 1) = a j)) :
    ∀ j' < N, a j' = a j → j' = j := by
  intro j' hj' heq
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  ·
    apply hl
    refine ⟨by omega, ?_⟩
    have h1 := hmono j' (j - 1) (by omega) (by omega)
    have h2 := hmono (j - 1) j (by omega) hj
    omega
  · apply hr
    refine ⟨by omega, ?_⟩
    have h1 := hmono j (j + 1) (by omega) (by omega)
    have h2 := hmono (j + 1) j' (by omega) hj'
    omega

theorem filter_down_eq_range (N : Nat) (P : Nat → Prop) [DecidablePred P]
    (hdown : ∀ i j, i ≤ j → j < N → P j → P i) :
    (Finset.range N).filter P = Finset.range (((Finset.range N).filter P).card) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have ih' := ih (fun i j hij hjN => hdown i j hij (by omega))
    by_cases hP : P N
    · have hall : (Finset.range (N + 1)).filter P = Finset.range (N + 1) := by
        apply Finset.filter_true_of_mem
        intro i hi
        exact hdown i N (by have := Finset.mem_range.mp hi; omega) (by omega) hP
      rw [hall, Finset.card_range]
    · have : (Finset.range (N + 1)).filter P = (Finset.range N).filter P := by
        rw [Finset.range_add_one, Finset.filter_insert, ite_eq_right (by simp [hP])]
      rw [this]
      exact ih'

theorem prefix_of_down (N : Nat) (P : Nat → Prop) [DecidablePred P]
    (hdown : ∀ i j, i ≤ j → j < N → P j → P i) (j : Nat) (hj : j < N) :
    P j ↔ j < ((Finset.range N).filter P).card := by
  have hset := filter_down_eq_range N P hdown
  constructor
  · intro h
    have : j ∈ (Finset.range N).filter P := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, h⟩
    rw [hset] at this
    exact Finset.mem_range.mp this
  · intro h
    have : j ∈ Finset.range (((Finset.range N).filter P).card) := Finset.mem_range.mpr h
    rw [← hset] at this
    exact (Finset.mem_filter.mp this).2

end Arr
end PEqualNP.Outside.L_clb_100_aux

namespace PEqualNP.Outside.L_clb_100_aux
namespace Step

open Bitonic Build049 Lookup049 Sem Arr

theorem bitsVal_congr (f g : Nat → Bool) : ∀ m, (∀ i < m, f i = g i) → bitsVal f m = bitsVal g m
  | 0, _ => rfl
  | m + 1, h => by
    simp only [bitsVal]
    rw [bitsVal_congr f g m (fun i hi => h i (by omega)), h m (by omega)]

theorem bitsVal_add (f : Nat → Bool) (m : Nat) : ∀ k,
    bitsVal f (m + k) = bitsVal f m + 2 ^ m * bitsVal (fun j => f (m + j)) k
  | 0 => by simp [bitsVal]
  | k + 1 => by
    rw [← Nat.add_assoc]
    simp only [bitsVal]
    rw [bitsVal_add f m k]
    by_cases hf : f (m + k) = true <;> simp [hf, Nat.pow_add, Nat.mul_add, Nat.add_assoc]

theorem bitsVal_inj (f g : Nat → Bool) (m : Nat) (h : bitsVal f m = bitsVal g m) :
    ∀ i < m, f i = g i := by
  intro i hi
  rw [← bitsVal_testBit f m i hi, ← bitsVal_testBit g m i hi, h]

abbrev R1 (w : Nat) := Rec (2 * w) 0
abbrev R2 (w : Nat) := Rec 0 (2 * w)

def vld {w : Nat} (r : R1 w) : Bool := !(r.keyBit (2 * w + 1))
def ek {w : Nat} (r : R1 w) : Nat := bitsVal r.keyBit (2 * w)
def sd {w : Nat} (r : R1 w) : Nat := bitsVal r.keyBit w
def cu {w : Nat} (r : R1 w) : Nat := bitsVal (fun j => r.keyBit (w + j)) w

theorem sd_lt {w : Nat} (r : R1 w) : sd r < 2 ^ w := bitsVal_lt _ _
theorem cu_lt {w : Nat} (r : R1 w) : cu r < 2 ^ w := bitsVal_lt _ _

theorem ek_eq {w : Nat} (r : R1 w) : ek r = sd r + 2 ^ w * cu r := by
  unfold ek sd cu
  exact (congrArg (bitsVal r.keyBit) (show 2 * w = w + w by omega)).trans (bitsVal_add _ w w)

theorem ek_lt {w : Nat} (r : R1 w) : ek r < 2 ^ w * 2 ^ w := by
  have := bitsVal_lt r.keyBit (2 * w)
  have e : 2 ^ (2 * w) = 2 ^ w * 2 ^ w := by rw [two_mul, Nat.pow_add]
  rw [e] at this
  exact this

theorem ek_mod {w : Nat} (r : R1 w) : ek r % 2 ^ w = sd r := by
  rw [ek_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (sd_lt r)]

theorem ek_div {w : Nat} (r : R1 w) : ek r / 2 ^ w = cu r := by
  rw [ek_eq, Nat.add_mul_div_left _ _ (Nat.two_pow_pos w), Nat.div_eq_of_lt (sd_lt r), Nat.zero_add]

theorem recKey_eq {w : Nat} (r : R1 w) (h0 : r.keyBit (2 * w) = false) :
    recKey r = ek r + (if vld r = true then 0 else 2 ^ (2 * w + 1)) := by
  unfold recKey ek vld
  simp only [bitsVal, h0]
  cases r.keyBit (2 * w + 1) <;> simp

theorem recKey_eq_iff {w : Nat} (r1 r2 : R1 w) (h1 : r1.keyBit (2 * w) = false)
    (h2 : r2.keyBit (2 * w) = false) :
    recKey r1 = recKey r2 ↔ (vld r1 = vld r2 ∧ ek r1 = ek r2) := by
  rw [recKey_eq r1 h1, recKey_eq r2 h2]
  have e1 := bitsVal_lt r1.keyBit (2 * w)
  have e2 := bitsVal_lt r2.keyBit (2 * w)
  have hp : 2 ^ (2 * w + 1) = 2 * 2 ^ (2 * w) := by rw [Nat.pow_succ]; omega
  unfold ek at *
  cases vld r1 <;> cases vld r2 <;> simp <;> omega

def child (w : Nat) (r : R1 w) (t look : Bool) : R1 w :=
  { keyBit := fun j =>
      if j < w then r.keyBit j
      else if j < 2 * w then (if j + 1 < 2 * w then r.keyBit (j + 1) else t)
      else if j = 2 * w then false
      else !(vld r && look)
    valBit := fun i => i.elim0 }

def dummy (w : Nat) : R1 w :=
  { keyBit := fun j => decide (j = 2 * w + 1), valBit := fun i => i.elim0 }

def addr {w : Nat} (r : R1 w) (t : Bool) : Nat := 2 ^ w * t.toNat + cu r

theorem addr_lt {w : Nat} (r : R1 w) (t : Bool) : addr r t < 2 ^ (w + 1) := by
  have := cu_lt r
  unfold addr
  rw [Nat.pow_succ]
  cases t <;> simp <;> omega

theorem addr_mod {w : Nat} (r : R1 w) (t : Bool) : addr r t % 2 ^ w = cu r := by
  unfold addr
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (cu_lt r)]

theorem addr_div {w : Nat} (r : R1 w) (t : Bool) : addr r t / 2 ^ w = t.toNat := by
  unfold addr
  rw [Nat.mul_add_div (Nat.two_pow_pos w), Nat.div_eq_of_lt (cu_lt r), Nat.add_zero]

theorem child_vld (w : Nat) (r : R1 w) (t look : Bool) : vld (child w r t look) = (vld r && look) := by
  have h1 : ¬ (2 * w + 1 < w) := by omega
  have h2 : ¬ (2 * w + 1 < 2 * w) := by omega
  have h3 : ¬ (2 * w + 1 = 2 * w) := by omega
  simp [vld, child, h1, h2, h3]

theorem child_bit0 (w : Nat) (r : R1 w) (t look : Bool) : (child w r t look).keyBit (2 * w) = false := by
  have h1 : ¬ (2 * w < w) ∨ w = 0 := by omega
  by_cases hw : w = 0
  · subst hw; simp [child]
  · have h1 : ¬ (2 * w < w) := by omega
    simp [child, h1]

theorem child_sd (w : Nat) (r : R1 w) (t look : Bool) : sd (child w r t look) = sd r := by
  unfold sd
  apply bitsVal_congr
  intro i hi
  simp [child, hi]

theorem child_cu (w : Nat) (r : R1 w) (t look : Bool) : cu (child w r t look) = addr r t / 2 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_div_two]
  unfold addr
  rw [Nat.testBit_two_pow_mul_add _ (cu_lt r)]
  by_cases hi : i < w
  · unfold cu
    rw [bitsVal_testBit _ _ _ hi]
    have h1 : ¬ (w + i < w) := by omega
    have h2 : w + i < 2 * w := by omega
    by_cases hi1 : i + 1 < w
    · have h3 : w + (i + 1) < 2 * w := by omega
      rw [if_pos hi1, bitsVal_testBit _ _ _ hi1]
      simp [child, h1, h2, h3, Nat.add_assoc]
    · have h3 : ¬ (w + i + 1 < 2 * w) := by omega
      have h4 : i + 1 - w = 0 := by omega
      rw [if_neg hi1, h4]
      cases t <;> simp [child, h1, h2, h3]
  · have hlt : cu (child w r t look) < 2 ^ i :=
      lt_of_lt_of_le (cu_lt _) (Nat.pow_le_pow_right (by omega) (by omega))
    rw [Nat.testBit_lt_two_pow hlt]
    have h1 : ¬ (i + 1 < w) := by omega
    rw [if_neg h1]
    have h5 : i + 1 - w ≠ 0 := by omega
    cases t
    · simp
    · exact (Nat.testBit_lt_two_pow (Nat.one_lt_two_pow h5)).symm

theorem child_ek (w : Nat) (r : R1 w) (t look : Bool) :
    ek (child w r t look) = sd r + 2 ^ w * (addr r t / 2) := by
  rw [ek_eq, child_sd, child_cu]

theorem dummy_vld (w : Nat) : vld (dummy w) = false := by simp [vld, dummy]
theorem dummy_bit0 (w : Nat) : (dummy w).keyBit (2 * w) = false := by simp [dummy]

end Step
end PEqualNP.Outside.L_clb_100_aux

namespace PEqualNP.Outside.L_clb_100_aux
namespace Step

open Bitonic Build049 Lookup049 Sem Arr

def mult {w : Nat} (A : Nat → R1 w) (M e : Nat) : Nat :=
  ((Finset.range M).filter (fun i => vld (A i) = true ∧ ek (A i) = e)).card

def isOdd (T : Nat → Nat → Bool) (w h e : Nat) : Bool :=
  decide (e < 2 ^ w * 2 ^ w) && Par T w h (e % 2 ^ w) (e / 2 ^ w)

def Inv (T : Nat → Nat → Bool) (w K h : Nat) (st : Nat → R1 w) : Prop :=
  ∀ e, mult st K e = if isOdd T w h e = true then 1 else 0

def oddCard (T : Nat → Nat → Bool) (w h : Nat) : Nat :=
  ((Finset.range (2 ^ w * 2 ^ w)).filter (fun e => Par T w h (e % 2 ^ w) (e / 2 ^ w) = true)).card

def children (w K : Nat) (row : Nat → Bool) (st : Nat → R1 w) : Nat → R1 w := fun idx =>
  if idx < 2 * K then
    child w (st (idx / 2)) (decide (idx % 2 = 1)) (row (addr (st (idx / 2)) (decide (idx % 2 = 1))))
  else dummy w

theorem inv_card {T : Nat → Nat → Bool} {w K h : Nat} {st : Nat → R1 w} (hInv : Inv T w K h st) :
    ((Finset.range K).filter (fun i => vld (st i) = true)).card = oddCard T w h := by
  classical
  have hmaps : (((Finset.range K).filter (fun i => vld (st i) = true) : Finset Nat) : Set Nat).MapsTo
      (fun i => ek (st i)) (Finset.range (2 ^ w * 2 ^ w)) := by
    intro i _
    exact Finset.mem_coe.mpr (Finset.mem_range.mpr (ek_lt _))
  rw [Finset.card_eq_sum_card_fiberwise hmaps, oddCard, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.filter_filter]
  have := hInv e
  unfold mult at this
  rw [this]
  have he' : e < 2 ^ w * 2 ^ w := Finset.mem_range.mp he
  simp [isOdd, he']

theorem inv_unique {T : Nat → Nat → Bool} {w K h : Nat} {st : Nat → R1 w} (hInv : Inv T w K h st)
    {i j : Nat} (hi : i < K) (hj : j < K) (vi : vld (st i) = true) (vj : vld (st j) = true)
    (hek : ek (st i) = ek (st j)) : i = j := by
  have h1 := hInv (ek (st i))
  have hle : mult st K (ek (st i)) ≤ 1 := by rw [h1]; split_ifs <;> omega
  unfold mult at hle
  rw [Finset.card_le_one] at hle
  exact hle i (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, vi, rfl⟩)
    j (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, vj, hek.symm⟩)

theorem inv_odd {T : Nat → Nat → Bool} {w K h : Nat} {st : Nat → R1 w} (hInv : Inv T w K h st)
    {i : Nat} (hi : i < K) (vi : vld (st i) = true) : Par T w h (sd (st i)) (cu (st i)) = true := by
  have h1 := hInv (ek (st i))
  have hpos : 0 < mult st K (ek (st i)) := by
    unfold mult
    exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, vi, rfl⟩⟩
  rw [h1] at hpos
  split_ifs at hpos with ho
  · simp only [isOdd, Bool.and_eq_true, decide_eq_true_eq] at ho
    rw [ek_mod, ek_div] at ho
    exact ho.2
  · omega

theorem inv_exists {T : Nat → Nat → Bool} {w K h : Nat} {st : Nat → R1 w} (hInv : Inv T w K h st)
    {e : Nat} (ho : isOdd T w h e = true) : ∃ i < K, vld (st i) = true ∧ ek (st i) = e := by
  have h1 := hInv e
  rw [if_pos ho] at h1
  have hpos : 0 < mult st K e := by omega
  unfold mult at hpos
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter, Finset.mem_range] at hi
  exact ⟨i, hi.1, hi.2.1, hi.2.2⟩

theorem mult_children {T : Nat → Nat → Bool} {w K h : Nat} {st : Nat → R1 w} (hInv : Inv T w K h st)
    (N : Nat) (hN : 2 * K ≤ N) (row : Nat → Bool) (hrow : ∀ u < 2 ^ (w + 1), row u = T h u)
    (e' : Nat) (he' : e' < 2 ^ w * 2 ^ w) :
    mult (children w K row st) N e' = (parents T w h (e' % 2 ^ w) (e' / 2 ^ w)).card := by
  have hD : 0 < 2 ^ w := Nat.two_pow_pos w
  unfold mult
  apply Finset.card_bij (fun idx _ => addr (st (idx / 2)) (decide (idx % 2 = 1)))
  · intro idx hidx
    rw [Finset.mem_filter, Finset.mem_range] at hidx
    obtain ⟨hlt, hv, hk⟩ := hidx
    by_cases h2K : idx < 2 * K
    · simp only [children, if_pos h2K] at hv hk
      rw [child_vld, Bool.and_eq_true] at hv
      rw [child_ek] at hk
      have hal := addr_lt (st (idx / 2)) (decide (idx % 2 = 1))
      have hhalf : addr (st (idx / 2)) (decide (idx % 2 = 1)) / 2 < 2 ^ w := by
        rw [Nat.pow_succ] at hal; omega
      have hsd := sd_lt (st (idx / 2))
      have hmod : e' % 2 ^ w = sd (st (idx / 2)) := by
        rw [← hk, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hsd]
      have hdiv : e' / 2 ^ w = addr (st (idx / 2)) (decide (idx % 2 = 1)) / 2 := by
        rw [← hk, Nat.add_mul_div_left _ _ hD, Nat.div_eq_of_lt hsd, Nat.zero_add]
      simp only [parents, Finset.mem_filter, Finset.mem_range]
      refine ⟨hal, hdiv.symm, ?_, ?_⟩
      · rw [← hrow _ hal]; exact hv.2
      · rw [addr_mod, hmod]
        exact inv_odd hInv (by omega) hv.1
    · simp only [children, if_neg h2K, dummy_vld] at hv
      exact absurd hv (by simp)
  · intro i1 h1 i2 h2 heq
    rw [Finset.mem_filter, Finset.mem_range] at h1 h2
    obtain ⟨-, hv1, hk1⟩ := h1
    obtain ⟨-, hv2, hk2⟩ := h2
    by_cases a1 : i1 < 2 * K
    · by_cases a2 : i2 < 2 * K
      · simp only [children, if_pos a1] at hv1 hk1
        simp only [children, if_pos a2] at hv2 hk2
        rw [child_vld, Bool.and_eq_true] at hv1 hv2
        rw [child_ek] at hk1 hk2
        have hsd1 := sd_lt (st (i1 / 2))
        have hsd2 := sd_lt (st (i2 / 2))
        have hs : sd (st (i1 / 2)) = sd (st (i2 / 2)) := by
          have e1 : e' % 2 ^ w = sd (st (i1 / 2)) := by
            rw [← hk1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hsd1]
          have e2 : e' % 2 ^ w = sd (st (i2 / 2)) := by
            rw [← hk2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hsd2]
          rw [← e1, ← e2]
        have hc : cu (st (i1 / 2)) = cu (st (i2 / 2)) := by
          have := congrArg (· % 2 ^ w) heq
          simpa only [addr_mod] using this
        have ht : (decide (i1 % 2 = 1)).toNat = (decide (i2 % 2 = 1)).toNat := by
          have := congrArg (· / 2 ^ w) heq
          simpa only [addr_div] using this
        have hi : i1 / 2 = i2 / 2 :=
          inv_unique hInv (by omega) (by omega) hv1.1 hv2.1 (by rw [ek_eq, ek_eq, hs, hc])
        have hb : i1 % 2 = i2 % 2 := by
          by_cases b1 : i1 % 2 = 1 <;> by_cases b2 : i2 % 2 = 1 <;> simp [b1, b2] at ht <;> omega
        omega
      · simp only [children, if_neg a2, dummy_vld] at hv2
        exact absurd hv2 (by simp)
    · simp only [children, if_neg a1, dummy_vld] at hv1
      exact absurd hv1 (by simp)
  · intro u hu
    simp only [parents, Finset.mem_filter, Finset.mem_range] at hu
    obtain ⟨hu2, hhalf, hT, hpar⟩ := hu
    have hmodlt : u % 2 ^ w < 2 ^ w := Nat.mod_lt _ hD
    have hodd : isOdd T w h (e' % 2 ^ w + 2 ^ w * (u % 2 ^ w)) = true := by
      have hs : e' % 2 ^ w < 2 ^ w := Nat.mod_lt _ hD
      simp only [isOdd, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨?_, ?_⟩
      · calc e' % 2 ^ w + 2 ^ w * (u % 2 ^ w) < 2 ^ w + 2 ^ w * (u % 2 ^ w) := by omega
          _ = 2 ^ w * (u % 2 ^ w + 1) := by rw [Nat.mul_succ]; omega
          _ ≤ 2 ^ w * 2 ^ w := Nat.mul_le_mul_left _ hmodlt
      · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs, Nat.add_mul_div_left _ _ hD,
          Nat.div_eq_of_lt hs, Nat.zero_add]
        exact hpar
    obtain ⟨i, hiK, hvi, hki⟩ := inv_exists hInv hodd
    have hudiv : u / 2 ^ w ≤ 1 := by
      have : u / 2 ^ w < 2 := by
        rw [Nat.div_lt_iff_lt_mul hD]; rw [Nat.pow_succ] at hu2; omega
      omega
    have hsdi : sd (st i) = e' % 2 ^ w := by
      rw [← ek_mod, hki, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Nat.mod_lt _ hD)]
    have hcui : cu (st i) = u % 2 ^ w := by
      rw [← ek_div, hki, Nat.add_mul_div_left _ _ hD, Nat.div_eq_of_lt (Nat.mod_lt _ hD), Nat.zero_add]
    have hq : ∀ q, q ≤ 1 → (2 * i + q) / 2 = i ∧ (2 * i + q) % 2 = q := by
      intro q hq; omega
    obtain ⟨hidx2, hidxm⟩ := hq _ hudiv
    have haddr : addr (st i) (decide (u / 2 ^ w = 1)) = u := by
      unfold addr
      rw [hcui]
      have : (decide (u / 2 ^ w = 1)).toNat = u / 2 ^ w := by
        by_cases hb : u / 2 ^ w = 1
        · simp [hb]
        · have : u / 2 ^ w = 0 := by omega
          simp [this]
      rw [this]
      exact Nat.div_add_mod u (2 ^ w)
    refine ⟨2 * i + u / 2 ^ w, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_range]
      have hq2 : ∀ q, q ≤ 1 → 2 * i + q < 2 * K := by intro q hq; omega
      have h2K : 2 * i + u / 2 ^ w < 2 * K := hq2 _ hudiv
      refine ⟨lt_of_lt_of_le h2K hN, ?_, ?_⟩
      · simp only [children, if_pos h2K, hidx2, hidxm]
        rw [child_vld, haddr, hrow u hu2, hvi, hT]; rfl
      · simp only [children, if_pos h2K, hidx2, hidxm]
        rw [child_ek, haddr, hsdi, hhalf]
        exact Nat.mod_add_div e' (2 ^ w)
    · simp only [hidx2, hidxm]
      exact haddr

end Step
end PEqualNP.Outside.L_clb_100_aux

namespace PEqualNP.Outside.L_clb_100_aux
namespace Step

open Bitonic Build049 Lookup049 Sem Arr

def eqAdj {w : Nat} (A : Nat → R1 w) (j : Nat) : Bool := decide (recKey (A j) = recKey (A (j + 1)))

def surv {w : Nat} (N : Nat) (A : Nat → R1 w) (j : Nat) : Bool :=
  vld (A j) && !(decide (0 < j) && eqAdj A (j - 1)) && !(decide (j + 1 < N) && eqAdj A j)

def rec2 {w : Nat} (N : Nat) (A : Nat → R1 w) : Nat → R2 w := fun j =>
  { keyBit := fun b => if b = 1 then !(surv N A j) else false
    valBit := fun i => (A j).keyBit i.val }

def vld2 {w : Nat} (r : R2 w) : Bool := !(r.keyBit 1)

def back {w : Nat} (r : R2 w) : R1 w :=
  { keyBit := fun j => if h : j < 2 * w then r.valBit ⟨j, h⟩ else if j = 2 * w then false else r.keyBit 1
    valBit := fun i => i.elim0 }

def stepSt (w K p : Nat) (row : Nat → Bool) (st : Nat → R1 w) : (Nat → R1 w) × Bool :=
  let s1 := runNet recKey (bitonicSort 0 p true) (children w K row st)
  let s2 := runNet recKey (bitonicSort 0 p true) (rec2 (2 ^ p) s1)
  (fun i => back (s2 i), vld2 (s2 K))

theorem surv_iff {w : Nat} (N : Nat) (A : Nat → R1 w) (j : Nat) :
    surv N A j = true ↔ (vld (A j) = true ∧ ¬ (0 < j ∧ recKey (A (j - 1)) = recKey (A (j - 1 + 1))) ∧
      ¬ (j + 1 < N ∧ recKey (A j) = recKey (A (j + 1)))) := by
  unfold surv eqAdj
  by_cases a1 : 0 < j <;> by_cases a2 : recKey (A (j - 1)) = recKey (A (j - 1 + 1)) <;>
    by_cases a3 : j + 1 < N <;> by_cases a4 : recKey (A j) = recKey (A (j + 1)) <;>
    simp [a1, a2, a3, a4]

theorem back_vld {w : Nat} (r : R2 w) : vld (back r) = vld2 r := by
  have h1 : ¬ (2 * w + 1 < 2 * w) := by omega
  have h2 : ¬ (2 * w + 1 = 2 * w) := by omega
  simp [vld, vld2, back, h1, h2]

theorem back_rec2_ek {w : Nat} (N : Nat) (A : Nat → R1 w) (j : Nat) : ek (back (rec2 N A j)) = ek (A j) := by
  unfold ek
  apply bitsVal_congr
  intro i hi
  simp [back, rec2, hi]

theorem recKey2 {w : Nat} (r : R2 w) (h0 : r.keyBit 0 = false) :
    recKey r = if vld2 r = true then 0 else 2 := by
  unfold recKey vld2
  simp only [Nat.zero_add, bitsVal, h0]
  cases r.keyBit 1 <;> simp

theorem step_spec (T : Nat → Nat → Bool) (w K p h : Nat) (st : Nat → R1 w) (row : Nat → Bool)
    (hK : 1 ≤ K) (hN : 2 * K ≤ 2 ^ p) (hInv : Inv T w K h st)
    (hrow : ∀ u < 2 ^ (w + 1), row u = T h u) :
    ((stepSt w K p row st).2 = true ↔ K < oddCard T w (h + 1)) ∧
    ((stepSt w K p row st).2 = false → Inv T w K (h + 1) (stepSt w K p row st).1) := by
  classical
  have hnet : ∀ c ∈ bitonicSort 0 p true, c.1 < 2 ^ p ∧ c.2.1 < 2 ^ p := by
    intro c hc
    have := bitonicSort_mem 0 p true c hc
    omega
  have hs1def : ∀ j, runNet recKey (bitonicSort 0 p true) (children w K row st) j =
      runNet recKey (bitonicSort 0 p true) (children w K row st) j := fun _ => rfl
  generalize hs1 : runNet recKey (bitonicSort 0 p true) (children w K row st) = s1 at *
  have hb0 : ∀ j < 2 ^ p, (s1 j).keyBit (2 * w) = false := by
    rw [← hs1]
    apply all_runNet recKey (2 ^ p) _ hnet (children w K row st) (fun r => r.keyBit (2 * w) = false)
    intro i _
    unfold children
    split_ifs
    · exact child_bit0 _ _ _ _
    · exact dummy_bit0 w
  have hsorted : ∀ i j, i ≤ j → j < 2 ^ p → recKey (s1 i) ≤ recKey (s1 j) := by
    rw [← hs1]; exact bitonicSort_sorted recKey p _
  have hmult1 : ∀ e', mult s1 (2 ^ p) e' = mult (children w K row st) (2 ^ p) e' := by
    intro e'
    rw [← hs1]
    exact count_runNet recKey (2 ^ p) _ hnet (children w K row st) (fun r => vld r = true ∧ ek r = e')
  have hkeyiff : ∀ i j, i < 2 ^ p → j < 2 ^ p →
      (recKey (s1 i) = recKey (s1 j) ↔ (vld (s1 i) = vld (s1 j) ∧ ek (s1 i) = ek (s1 j))) :=
    fun i j hi hj => recKey_eq_iff _ _ (hb0 i hi) (hb0 j hj)
  have hsurv : ∀ j < 2 ^ p, (surv (2 ^ p) s1 j = true ↔
      (vld (s1 j) = true ∧ ∀ j' < 2 ^ p, recKey (s1 j') = recKey (s1 j) → j' = j)) := by
    intro j hj
    rw [surv_iff]
    constructor
    · rintro ⟨hv, hl, hr⟩
      refine ⟨hv, unique_of_neighbours (2 ^ p) (fun j => recKey (s1 j)) hsorted j hj ?_ ?_⟩
      · rintro ⟨h0, he⟩
        apply hl
        refine ⟨h0, ?_⟩
        rw [Nat.sub_add_cancel h0]; exact he
      · rintro ⟨h1, he⟩
        exact hr ⟨h1, he.symm⟩
    · rintro ⟨hv, huniq⟩
      refine ⟨hv, ?_, ?_⟩
      · rintro ⟨h0, he⟩
        rw [Nat.sub_add_cancel h0] at he
        have := huniq (j - 1) (by omega) he
        omega
      · rintro ⟨h1, he⟩
        have := huniq (j + 1) h1 he.symm
        omega
  have msurv : ∀ e', ((Finset.range (2 ^ p)).filter (fun j => surv (2 ^ p) s1 j = true ∧ ek (s1 j) = e')).card =
      if mult s1 (2 ^ p) e' = 1 then 1 else 0 := by
    intro e'
    split_ifs with h1
    · unfold mult at h1
      obtain ⟨j0, hj0⟩ := Finset.card_eq_one.mp h1
      have hmem : j0 ∈ (Finset.range (2 ^ p)).filter (fun i => vld (s1 i) = true ∧ ek (s1 i) = e') := by
        rw [hj0]; exact Finset.mem_singleton_self _
      rw [Finset.mem_filter, Finset.mem_range] at hmem
      obtain ⟨hj0N, hv0, hk0⟩ := hmem
      rw [Finset.card_eq_one]
      refine ⟨j0, ?_⟩
      ext j
      rw [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨hjN, hs, hk⟩
        have hvj := ((hsurv j hjN).mp hs).1
        have : j ∈ ({j0} : Finset Nat) := by
          rw [← hj0]; exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjN, hvj, hk⟩
        exact Finset.mem_singleton.mp this
      · intro hjj
        subst hjj
        refine ⟨hj0N, (hsurv j hj0N).mpr ⟨hv0, ?_⟩, hk0⟩
        intro j' hj' he
        have hh := (hkeyiff j' j hj' hj0N).mp he
        have hv' : vld (s1 j') = true := by rw [hh.1]; exact hv0
        have : j' ∈ ({j} : Finset Nat) := by
          rw [← hj0]; exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj', hv', hh.2.trans hk0⟩
        exact Finset.mem_singleton.mp this
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro j hj ⟨hs, hk⟩
      have hjN := Finset.mem_range.mp hj
      obtain ⟨hvj, huniq⟩ := (hsurv j hjN).mp hs
      apply h1
      unfold mult
      rw [Finset.card_eq_one]
      refine ⟨j, ?_⟩
      ext j'
      rw [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨hj'N, hv', hk'⟩
        exact huniq j' hj'N ((hkeyiff j' j hj'N hjN).mpr ⟨hv'.trans hvj.symm, hk'.trans hk.symm⟩)
      · intro hjj
        subst hjj
        exact ⟨hjN, hvj, hk⟩
  have hone : ∀ e', e' < 2 ^ w * 2 ^ w →
      (mult s1 (2 ^ p) e' = 1 ↔ Par T w (h + 1) (e' % 2 ^ w) (e' / 2 ^ w) = true) := by
    intro e' he'
    rw [hmult1, mult_children hInv (2 ^ p) hN row hrow e' he', par_succ]
    have := parents_card_le T w h (e' % 2 ^ w) (e' / 2 ^ w)
    omega
  have hzero : ∀ e', ¬ (e' < 2 ^ w * 2 ^ w) → mult s1 (2 ^ p) e' ≠ 1 := by
    intro e' he' h1
    unfold mult at h1
    obtain ⟨j0, hj0⟩ := Finset.card_eq_one.mp h1
    have hmem : j0 ∈ (Finset.range (2 ^ p)).filter (fun i => vld (s1 i) = true ∧ ek (s1 i) = e') := by
      rw [hj0]; exact Finset.mem_singleton_self _
    rw [Finset.mem_filter] at hmem
    have := ek_lt (s1 j0)
    omega

  have hr2v : ∀ j, vld2 (rec2 (2 ^ p) s1 j) = surv (2 ^ p) s1 j := by
    intro j; simp [vld2, rec2]
  have hs2def : (stepSt w K p row st) =
      ((fun i => back (runNet recKey (bitonicSort 0 p true) (rec2 (2 ^ p) s1) i)),
        vld2 (runNet recKey (bitonicSort 0 p true) (rec2 (2 ^ p) s1) K)) := by
    unfold stepSt; rw [hs1]
  rw [hs2def]
  have hcount2 : ∀ (P : R2 w → Prop) [DecidablePred P],
      ((Finset.range (2 ^ p)).filter (fun j => P (runNet recKey (bitonicSort 0 p true) (rec2 (2 ^ p) s1) j))).card =
      ((Finset.range (2 ^ p)).filter (fun j => P (rec2 (2 ^ p) s1 j))).card :=
    fun P _ => count_runNet recKey (2 ^ p) _ hnet (rec2 (2 ^ p) s1) P
  have hb20 : ∀ j < 2 ^ p, (runNet recKey (bitonicSort 0 p true) (rec2 (2 ^ p) s1) j).keyBit 0 = false := by
    apply all_runNet recKey (2 ^ p) _ hnet (rec2 (2 ^ p) s1) (fun r => r.keyBit 0 = false)
    intro i _; simp [rec2]
  have hsorted2 := bitonicSort_sorted (recKey (a := 0) (b := 2 * w)) p (rec2 (2 ^ p) s1)
  generalize runNet recKey (bitonicSort 0 p true) (rec2 (2 ^ p) s1) = s2 at *
  have hdown : ∀ i j, i ≤ j → j < 2 ^ p → vld2 (s2 j) = true → vld2 (s2 i) = true := by
    intro i j hij hj hvj
    have hs := hsorted2 i j hij hj
    rw [recKey2 _ (hb20 i (by omega)), recKey2 _ (hb20 j hj), if_pos hvj] at hs
    by_contra hvi
    rw [if_neg hvi] at hs
    omega
  have hKN : K < 2 ^ p := by omega
  have hpre := fun j hj => prefix_of_down (2 ^ p) (fun j => vld2 (s2 j) = true) hdown j hj
  have hm : ((Finset.range (2 ^ p)).filter (fun j => vld2 (s2 j) = true)).card = oddCard T w (h + 1) := by
    rw [hcount2 (fun r => vld2 r = true)]
    have e1 : (Finset.range (2 ^ p)).filter (fun j => vld2 (rec2 (2 ^ p) s1 j) = true) =
        (Finset.range (2 ^ p)).filter (fun j => surv (2 ^ p) s1 j = true) := by
      apply Finset.filter_congr; intro j _; rw [hr2v]
    rw [e1]
    have hmaps : (((Finset.range (2 ^ p)).filter (fun j => surv (2 ^ p) s1 j = true) : Finset Nat) : Set Nat).MapsTo
        (fun j => ek (s1 j)) (Finset.range (2 ^ w * 2 ^ w)) := by
      intro j _
      exact Finset.mem_coe.mpr (Finset.mem_range.mpr (ek_lt _))
    rw [Finset.card_eq_sum_card_fiberwise hmaps, oddCard, Finset.card_filter]
    apply Finset.sum_congr rfl
    intro e' he'
    rw [Finset.filter_filter, msurv e']
    have := hone e' (Finset.mem_range.mp he')
    by_cases hp : Par T w (h + 1) (e' % 2 ^ w) (e' / 2 ^ w) = true
    · rw [if_pos (this.mpr hp), if_pos hp]
    · rw [if_neg (fun hh => hp (this.mp hh)), if_neg hp]
  refine ⟨?_, ?_⟩
  · show vld2 (s2 K) = true ↔ K < oddCard T w (h + 1)
    rw [← hm]
    exact hpre K hKN
  · intro hov
    have hov' : vld2 (s2 K) = false := hov
    have hmK : ((Finset.range (2 ^ p)).filter (fun j => vld2 (s2 j) = true)).card ≤ K := by
      by_contra hlt
      have := (hpre K hKN).mpr (by omega)
      rw [hov'] at this
      exact absurd this (by simp)
    intro e'
    show mult (fun i => back (s2 i)) K e' = _
    have e1 : mult (fun i => back (s2 i)) K e' =
        ((Finset.range (2 ^ p)).filter (fun j => vld2 (s2 j) = true ∧ ek (back (s2 j)) = e')).card := by
      unfold mult
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, back_vld]
      constructor
      · rintro ⟨hi, hv, hk⟩
        exact ⟨by omega, hv, hk⟩
      · rintro ⟨hi, hv, hk⟩
        have := (hpre i hi).mp hv
        exact ⟨by omega, hv, hk⟩
    rw [e1, hcount2 (fun r => vld2 r = true ∧ ek (back r) = e')]
    have e2 : (Finset.range (2 ^ p)).filter (fun j => vld2 (rec2 (2 ^ p) s1 j) = true ∧ ek (back (rec2 (2 ^ p) s1 j)) = e') =
        (Finset.range (2 ^ p)).filter (fun j => surv (2 ^ p) s1 j = true ∧ ek (s1 j) = e') := by
      apply Finset.filter_congr; intro j _; rw [hr2v, back_rec2_ek]
    rw [e2, msurv e']
    by_cases hlt : e' < 2 ^ w * 2 ^ w
    · have := hone e' hlt
      by_cases hp : Par T w (h + 1) (e' % 2 ^ w) (e' / 2 ^ w) = true
      · rw [if_pos (this.mpr hp), if_pos (by simp [isOdd, hlt, hp])]
      · rw [if_neg (fun hh => hp (this.mp hh)), if_neg (by simp [isOdd, hp])]
    · rw [if_neg (hzero e' hlt), if_neg (by simp [isOdd, hlt])]

end Step
end PEqualNP.Outside.L_clb_100_aux

namespace PEqualNP.Outside.L_clb_100_aux
namespace Emb

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open Build049 Lookup049

def wsig {n : Nat} (I' : Nat) (inp : Fin I' → Sig n) (gs : List Gate) (k : Nat) : Sig n :=
  fun v => ((Circuit.mk gs 0).wires (List.ofFn fun i => inp i v)).getD k false

theorem wires_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    (Circuit.mk (gs ++ [g]) 0).wires x =
      (Circuit.mk gs 0).wires x ++
        [g.op.eval (g.inputs.map fun i => ((Circuit.mk gs 0).wires x).getD i false)] := by
  simp only [Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem embed {n : Nat} {A : Set (Sig n)} (I' : Nat) (inp : Fin I' → Sig n) (hin : ∀ i, inp i ∈ A)
    (gs : List Gate) (hr : ReadsBack I' ⟨gs, 0⟩) (hf : FanInTwo ⟨gs, 0⟩) :
    Build A {f | ∃ k < I' + gs.length, f = wsig I' inp gs k} gs.length := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine relax (idle (A := A) (B := {f | ∃ k < I' + ([] : List Gate).length, f = wsig I' inp [] k}) ?_)
      le_rfl le_rfl le_rfl
    rintro f ⟨k, hk, rfl⟩
    have hk' : k < I' := by simpa using hk
    have : wsig I' inp [] k = inp ⟨k, hk'⟩ := by
      funext v
      simp only [wsig, Circuit.wires, List.foldl_nil]
      rw [List.getD_eq_getElem _ _ (by simpa using hk'), List.getElem_ofFn]
    rw [this]; exact hin _
  | append_singleton gs g ih =>
    have hr' : ReadsBack I' ⟨gs, 0⟩ := by
      intro j hj i hi
      have hj' : j < gs.length := hj
      apply hr j (by show j < (gs ++ [g]).length; simp; omega) i
      show i ∈ ((gs ++ [g]).getD j ⟨GateOp.or, []⟩).inputs
      rw [List.getD_append _ _ _ _ hj']
      exact hi
    have hf' : FanInTwo ⟨gs, 0⟩ := fun g' hg' =>
      hf g' (by show g' ∈ gs ++ [g]; exact List.mem_append_left _ hg')
    have ih' := ih hr' hf'
    have hg := hf g (by show g ∈ gs ++ [g]; simp)
    have hdeps : ∀ i ∈ g.inputs, i < I' + gs.length := by
      intro i hi
      apply hr gs.length (by show gs.length < (gs ++ [g]).length; simp) i
      show i ∈ ((gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩).inputs
      rw [List.getD_append_right _ _ _ _ le_rfl]
      simpa using hi
    have hlen : ∀ v, ((Circuit.mk gs 0).wires (List.ofFn fun i => inp i v)).length = I' + gs.length := by
      intro v; rw [GateBridge.wireLength]; simp
    have hone : Build (A ∪ {f | ∃ k < I' + gs.length, f = wsig I' inp gs k})
        {wsig I' inp (gs ++ [g]) (I' + gs.length)} 1 := by
      apply one g.op (g.inputs.map (fun i => wsig I' inp gs i)) hg.1 (by simpa using hg.2)
      · intro d hd
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hd
        exact Or.inr ⟨i, hdeps i hi, rfl⟩
      · intro v
        simp only [wsig]
        rw [wires_snoc, List.getD_append_right _ _ _ _ (by rw [hlen v]), hlen v, Nat.sub_self]
        simp [List.map_map, wsig, Function.comp_def]
    refine relax (seq ih' hone) le_rfl ?_ (by simp)
    rintro f ⟨k, hk, rfl⟩
    by_cases hk' : k < I' + gs.length
    · left
      refine ⟨k, hk', ?_⟩
      funext v
      simp only [wsig]
      rw [wires_snoc, List.getD_append _ _ _ _ (by rw [hlen v]; exact hk')]
    · right
      have : k = I' + gs.length := by
        simp only [List.length_append, List.length_singleton] at hk; omega
      subst this
      rfl

theorem ofFn_getD (l : List Bool) (m : Nat) (h : l.length = m) :
    (List.ofFn fun k : Fin m => l.getD k.val false) = l := by
  subst h
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.getElem_ofFn, List.getD_eq_getElem _ _ h2]

theorem lookupG {n : Nat} {A : Set (Sig n)} (a q : Nat) (tab : Fin (2 ^ a) → Sig n)
    (adr : Fin q → Fin a → Sig n) (htab : ∀ j, tab j ∈ A) (hadr : ∀ j i, adr j i ∈ A) :
    ∃ c, c ≤ 128 * (2 ^ a + q) * (a + 1 + Nat.log2 (q + 1) + 3) ^ 3 ∧
      Build A {f | ∃ j : Fin q, f = fun v =>
        tab ⟨bitsVal (fun i => if h : i < a then adr j ⟨i, h⟩ v else false) a, bitsVal_lt _ _⟩ v} c := by
  obtain ⟨C, outBit, hfan, hread, -, hsize, hspec⟩ := solve_049 a 1 q
  let xl : (Fin n → Bool) → List Bool := fun v =>
    (List.ofFn (fun j : Fin (2 ^ a) => List.ofFn (fun _ : Fin 1 => tab j v))).flatten ++
      (List.ofFn (fun j : Fin q => List.ofFn (fun i : Fin a => adr j i v))).flatten
  have hl1 : ∀ v, ((List.ofFn (fun j : Fin (2 ^ a) => List.ofFn (fun _ : Fin 1 => tab j v))).flatten).length = 2 ^ a * 1 :=
    fun v => list_ofFn_flatten_length _
  have hl2 : ∀ v, ((List.ofFn (fun j : Fin q => List.ofFn (fun i : Fin a => adr j i v))).flatten).length = q * a :=
    fun v => list_ofFn_flatten_length _
  have hxl : ∀ v, (xl v).length = 2 ^ a * 1 + q * a := by
    intro v; simp only [xl, List.length_append, hl1 v, hl2 v]
  let inp : Fin (2 ^ a * 1 + q * a) → Sig n := fun k v => (xl v).getD k.val false
  have hin : ∀ k, inp k ∈ A := by
    intro k
    by_cases hk : k.val < 2 ^ a * 1
    · have hk' : k.val < 2 ^ a := by omega
      have : inp k = tab ⟨k.val, hk'⟩ := by
        funext v
        simp only [inp, xl]
        rw [List.getD_append _ _ _ _ (by rw [hl1 v]; exact hk)]
        have := list_ofFn_flatten_getD (fun (j : Fin (2 ^ a)) (_ : Fin 1) => tab j v) ⟨k.val, hk'⟩ ⟨0, by omega⟩
        simpa using this
      rw [this]; exact htab _
    · have hk2 : k.val - 2 ^ a * 1 < q * a := by have := k.isLt; omega
      have ha : 0 < a := by
        rcases Nat.eq_zero_or_pos a with h0 | h0
        · subst h0; simp at hk2
        · exact h0
      have hj : (k.val - 2 ^ a * 1) / a < q := by
        rw [Nat.div_lt_iff_lt_mul ha]; exact hk2
      have hi : (k.val - 2 ^ a * 1) % a < a := Nat.mod_lt _ ha
      have : inp k = adr ⟨(k.val - 2 ^ a * 1) / a, hj⟩ ⟨(k.val - 2 ^ a * 1) % a, hi⟩ := by
        funext v
        simp only [inp, xl]
        rw [List.getD_append_right _ _ _ _ (by rw [hl1 v]; omega), hl1 v]
        have := list_ofFn_flatten_getD (fun (j : Fin q) (i : Fin a) => adr j i v)
          ⟨(k.val - 2 ^ a * 1) / a, hj⟩ ⟨(k.val - 2 ^ a * 1) % a, hi⟩
        simp only at this
        rw [Nat.div_add_mod'] at this
        exact this
      rw [this]; exact hadr _ _
  have hemb := embed (A := A) (2 ^ a * 1 + q * a) inp hin C.gates hread hfan
  refine ⟨C.gates.length, hsize, relax hemb le_rfl ?_ le_rfl⟩
  rintro f ⟨j, rfl⟩
  refine ⟨(outBit j ⟨0, by omega⟩).val, (outBit j ⟨0, by omega⟩).isLt, ?_⟩
  funext v
  simp only [wsig]
  have hx : (List.ofFn fun i => inp i v) = xl v := ofFn_getD (xl v) _ (hxl v)
  rw [hx]
  have hs := hspec (fun j' _ => tab j' v)
    (fun j' => ⟨bitsVal (fun i => if h : i < a then adr j' ⟨i, h⟩ v else false) a, bitsVal_lt _ _⟩) j ⟨0, by omega⟩
  simp only at hs
  have hadr2 : (List.ofFn fun j' : Fin q => List.ofFn fun i : Fin a =>
      (bitsVal (fun i => if h : i < a then adr j' ⟨i, h⟩ v else false) a).testBit i.val) =
      (List.ofFn fun j' : Fin q => List.ofFn fun i : Fin a => adr j' i v) := by
    congr 1; funext j'; congr 1; funext i
    rw [bitsVal_testBit _ _ _ i.isLt, dif_pos i.isLt]
  rw [hadr2] at hs
  exact hs.symm

theorem xorG {n : Nat} {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {fun v => xor (f v) (g v)} 4 := by
  have he : (fun v => xor (f v) (g v)) = an (Build049.or f g) (nt (an f g)) := by
    funext v
    cases hfv : f v <;> cases hgv : g v <;> simp [an, Build049.or, nt, hfv, hgv]
  rw [he]
  have h1 := orG hf hg
  have h2 := andG (A := A ∪ {Build049.or f g}) (Or.inl hf) (Or.inl hg)
  have h3 := notG (A := A ∪ ({Build049.or f g} ∪ {an f g})) (f := an f g) (Or.inr (Or.inr rfl))
  have h4 := andG (A := A ∪ (({Build049.or f g} ∪ {an f g}) ∪ {nt (an f g)}))
    (f := Build049.or f g) (g := nt (an f g)) (Or.inr (Or.inl (Or.inl rfl))) (Or.inr (Or.inr rfl))
  exact relax (seq (seq (seq h1 h2) h3) h4) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl

theorem eqWordG {n : Nat} {A : Set (Sig n)} (f g : Nat → Sig n) (m : Nat)
    (hf : ∀ i < m, f i ∈ A) (hg : ∀ i < m, g i ∈ A) (hfalse : (fun _ => false) ∈ A) :
    Build A {fun v => decide (bitsVal (fun i => f i v) m = bitsVal (fun i => g i v) m)} (10 * m + 3) := by
  let L1 : Sig n := fun v => decide (bitsVal (fun i => f i v) m < bitsVal (fun i => g i v) m)
  let L2 : Sig n := fun v => decide (bitsVal (fun i => g i v) m < bitsVal (fun i => f i v) m)
  have he : (fun v => decide (bitsVal (fun i => f i v) m = bitsVal (fun i => g i v) m)) = an (nt L1) (nt L2) := by
    funext v
    simp only [an, nt, L1, L2]
    rcases Nat.lt_trichotomy (bitsVal (fun i => f i v) m) (bitsVal (fun i => g i v) m) with h | h | h
    · have h1 : ¬ (bitsVal (fun i => f i v) m = bitsVal (fun i => g i v) m) := by omega
      have h2 : ¬ (bitsVal (fun i => g i v) m < bitsVal (fun i => f i v) m) := by omega
      simp [h, h1]
    · simp [h]
    · have h1 : ¬ (bitsVal (fun i => f i v) m = bitsVal (fun i => g i v) m) := by omega
      have h2 : ¬ (bitsVal (fun i => f i v) m < bitsVal (fun i => g i v) m) := by omega
      simp [h, h1, h2]
  rw [he]
  have h1 : Build A {L1} (5 * m) := ltWordG f g m hf hg hfalse
  have h2 : Build (A ∪ {L1}) {L2} (5 * m) :=
    ltWordG g f m (fun i hi => Or.inl (hg i hi)) (fun i hi => Or.inl (hf i hi)) (Or.inl hfalse)
  have h3 := notG (A := A ∪ ({L1} ∪ {L2})) (f := L1) (Or.inr (Or.inl rfl))
  have h4 := notG (A := A ∪ (({L1} ∪ {L2}) ∪ {nt L1})) (f := L2) (Or.inr (Or.inl (Or.inr rfl)))
  have h5 := andG (A := A ∪ ((({L1} ∪ {L2}) ∪ {nt L1}) ∪ {nt L2})) (f := nt L1) (g := nt L2)
    (Or.inr (Or.inl (Or.inr rfl))) (Or.inr (Or.inr rfl))
  exact relax (seq (seq (seq (seq h1 h2) h3) h4) h5) le_rfl
    (Set.singleton_subset_iff.mpr (Or.inr rfl)) (by omega)

end Emb
end PEqualNP.Outside.L_clb_100_aux

namespace PEqualNP.Outside.L_clb_100_aux
namespace Circ

open PEqualNP.CircuitLowerBounds Build049 Bitonic Lookup049 Step Emb

theorem addr_bits {w : Nat} (r : R1 w) (t : Bool) :
    bitsVal (fun i => if i < w then r.keyBit (w + i) else t) (w + 1) = addr r t := by
  have h1 : bitsVal (fun i => if i < w then r.keyBit (w + i) else t) w = cu r := by
    unfold cu
    apply bitsVal_congr
    intro i hi
    simp [hi]
  simp only [bitsVal, h1, Nat.lt_irrefl, if_false]
  unfold addr
  cases t <;> simp <;> omega

theorem nsurvG {n : Nat} {A : Set (Sig n)} {k g1 g2 : Sig n} (hk : k ∈ A) (h1 : g1 ∈ A) (h2 : g2 ∈ A) :
    Build A {fun v => !((!(k v) && !(g1 v)) && !(g2 v))} 6 := by
  show Build A {nt (an (an (nt k) (nt g1)) (nt g2))} 6
  have a1 := notG hk
  have a2 := notG (A := A ∪ {nt k}) (Or.inl h1)
  have a3 := notG (A := A ∪ ({nt k} ∪ {nt g1})) (Or.inl h2)
  have a4 := andG (A := A ∪ (({nt k} ∪ {nt g1}) ∪ {nt g2})) (f := nt k) (g := nt g1)
    (Or.inr (Or.inl (Or.inl rfl))) (Or.inr (Or.inl (Or.inr rfl)))
  have a5 := andG (A := A ∪ ((({nt k} ∪ {nt g1}) ∪ {nt g2}) ∪ {an (nt k) (nt g1)}))
    (f := an (nt k) (nt g1)) (g := nt g2) (Or.inr (Or.inr rfl)) (Or.inr (Or.inl (Or.inr rfl)))
  have a6 := notG (A := A ∪ (((({nt k} ∪ {nt g1}) ∪ {nt g2}) ∪ {an (nt k) (nt g1)}) ∪
    {an (an (nt k) (nt g1)) (nt g2)})) (f := an (an (nt k) (nt g1)) (nt g2)) (Or.inr (Or.inr rfl))
  exact relax (seq (seq (seq (seq (seq a1 a2) a3) a4) a5) a6) le_rfl
    (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl

def stepCost (w K p : Nat) : Nat :=
  128 * (2 ^ (w + 1) + 2 * K) * (w + 1 + 1 + Nat.log2 (2 * K + 1) + 3) ^ 3 + K * 1 + 2 * K * 1 + 2 * K * 1 +
    (bitonicSort 0 p true).length * (11 * (2 * w) + 6 * 0 + 23) +
    (2 ^ p - 1) * (10 * (2 * w + 2) + 3) + 2 ^ p * 6 +
    (bitonicSort 0 p true).length * (11 * 0 + 6 * (2 * w) + 23)

theorem stepG {n : Nat} {A : Set (Sig n)} (w K p : Nat) (hN : 2 * K ≤ 2 ^ p)
    (st : (Fin n → Bool) → Nat → R1 w) (row : (Fin n → Bool) → Nat → Bool)
    (hS : ∀ i < K, ∀ j < 2 * w + 2, (fun v => (st v i).keyBit j) ∈ A)
    (hT : ∀ u < 2 ^ (w + 1), (fun v => row v u) ∈ A)
    (hc : ∀ b : Bool, (fun _ => b) ∈ A) :
    ∃ (c : Nat) (Bout : Set (Sig n)), c ≤ stepCost w K p ∧ Build A Bout c ∧
      (∀ i < K, ∀ j < 2 * w + 2,
        (fun v => ((stepSt w K p (row v) (st v)).1 i).keyBit j) ∈ A ∪ Bout) ∧
      (fun v => !(stepSt w K p (row v) (st v)).2) ∈ A ∪ Bout := by
  have hnet : ∀ c ∈ bitonicSort 0 p true, c.1 < 2 ^ p ∧ c.2.1 < 2 ^ p := by
    intro c hc'
    have := bitonicSort_mem 0 p true c hc'
    omega

  let tab : Fin (2 ^ (w + 1)) → Sig n := fun u v => row v u.val
  let adr : Fin (2 * K) → Fin (w + 1) → Sig n := fun j i =>
    if i.val < w then (fun v => (st v (j.val / 2)).keyBit (w + i.val)) else (fun _ => decide (j.val % 2 = 1))
  have hadr : ∀ j i, adr j i ∈ A := by
    intro j i
    simp only [adr]
    split_ifs with h
    · exact hS _ (by have := j.isLt; omega) _ (by omega)
    · exact hc _
  obtain ⟨cL, hcL, HL⟩ := lookupG (A := A) (w + 1) (2 * K) tab adr (fun u => hT u.val u.isLt) hadr
  let look : Nat → Sig n := fun idx v => row v (addr (st v (idx / 2)) (decide (idx % 2 = 1)))
  have hlook : ∀ idx (hidx : idx < 2 * K), look idx ∈
      {f | ∃ j : Fin (2 * K), f = fun v => tab ⟨bitsVal (fun i => if h : i < w + 1 then adr j ⟨i, h⟩ v else false) (w + 1),
        bitsVal_lt _ _⟩ v} := by
    intro idx hidx
    refine ⟨⟨idx, hidx⟩, ?_⟩
    funext v
    simp only [look, tab]
    congr 1
    rw [← addr_bits]
    apply bitsVal_congr
    intro i hi
    simp only [adr, dif_pos hi]
    split_ifs <;> rfl
  let nv : Fin K → Sig n := fun i => nt (fun v => (st v i.val).keyBit (2 * w + 1))
  have H2 := finG (A := A ∪ {f | ∃ j : Fin (2 * K), f = fun v => tab ⟨bitsVal (fun i => if h : i < w + 1 then adr j ⟨i, h⟩ v else false) (w + 1),
        bitsVal_lt _ _⟩ v}) nv 1 (fun i => notG (Or.inl (hS i.val i.isLt _ (by omega))))
  let cv : Fin (2 * K) → Sig n := fun j => an (nv ⟨j.val / 2, by have := j.isLt; omega⟩) (look j.val)
  have H3 := finG (A := A ∪ ({f | ∃ j : Fin (2 * K), f = fun v => tab ⟨bitsVal (fun i => if h : i < w + 1 then adr j ⟨i, h⟩ v else false) (w + 1),
        bitsVal_lt _ _⟩ v} ∪ Set.range nv)) cv 1
    (fun j => andG (Or.inr (Or.inr ⟨_, rfl⟩)) (Or.inr (Or.inl (hlook j.val j.isLt))))
  let ncv : Fin (2 * K) → Sig n := fun j => nt (cv j)
  have H4 := finG (A := A ∪ (({f | ∃ j : Fin (2 * K), f = fun v => tab ⟨bitsVal (fun i => if h : i < w + 1 then adr j ⟨i, h⟩ v else false) (w + 1),
        bitsVal_lt _ _⟩ v} ∪ Set.range nv) ∪ Set.range cv)) ncv 1
    (fun j => notG (Or.inr (Or.inr ⟨j, rfl⟩)))
  have H1234 := seq (seq (seq HL H2) H3) H4
  generalize hX : ((({f | ∃ j : Fin (2 * K), f = fun v => tab ⟨bitsVal (fun i => if h : i < w + 1 then adr j ⟨i, h⟩ v else false) (w + 1),
        bitsVal_lt _ _⟩ v} ∪ Set.range nv) ∪ Set.range cv) ∪ Set.range ncv : Set (Sig n)) = X at H1234
  have hncvX : ∀ j, ncv j ∈ X := by intro j; rw [← hX]; exact Or.inr ⟨j, rfl⟩

  let ch : (Fin n → Bool) → Nat → R1 w := fun v => children w K (row v) (st v)
  have hchK : ∀ idx < 2 ^ p, ∀ j < 2 * w + 2, (fun v => (ch v idx).keyBit j) ∈ A ∪ X := by
    intro idx _ j hj
    by_cases h2K : idx < 2 * K
    · have e : (fun v => (ch v idx).keyBit j) =
          fun v => (child w (st v (idx / 2)) (decide (idx % 2 = 1)) (look idx v)).keyBit j := by
        funext v; simp only [ch, children, if_pos h2K, look]
      rw [e]
      by_cases j1 : j < w
      · have e2 : (fun v => (child w (st v (idx / 2)) (decide (idx % 2 = 1)) (look idx v)).keyBit j) =
            fun v => (st v (idx / 2)).keyBit j := by
          funext v; simp [child, j1]
        rw [e2]; exact Or.inl (hS _ (by omega) _ (by omega))
      · by_cases j2 : j < 2 * w
        · by_cases j3 : j + 1 < 2 * w
          · have e2 : (fun v => (child w (st v (idx / 2)) (decide (idx % 2 = 1)) (look idx v)).keyBit j) =
                fun v => (st v (idx / 2)).keyBit (j + 1) := by
              funext v; simp [child, j1, j2, j3]
            rw [e2]; exact Or.inl (hS _ (by omega) _ (by omega))
          · have e2 : (fun v => (child w (st v (idx / 2)) (decide (idx % 2 = 1)) (look idx v)).keyBit j) =
                fun _ => decide (idx % 2 = 1) := by
              funext v; simp [child, j1, j2, j3]
            rw [e2]; exact Or.inl (hc _)
        · by_cases j4 : j = 2 * w
          · have e2 : (fun v => (child w (st v (idx / 2)) (decide (idx % 2 = 1)) (look idx v)).keyBit j) =
                fun _ => false := by
              funext v; rw [j4]; exact child_bit0 _ _ _ _
            rw [e2]; exact Or.inl (hc false)
          · have e2 : (fun v => (child w (st v (idx / 2)) (decide (idx % 2 = 1)) (look idx v)).keyBit j) =
                ncv ⟨idx, h2K⟩ := by
              funext v; simp [child, j1, j2, j4, ncv, cv, nv, nt, an, vld]
            rw [e2]; exact Or.inr (hncvX _)
    · have e : (fun v => (ch v idx).keyBit j) = fun _ => decide (j = 2 * w + 1) := by
        funext v; simp only [ch, children, if_neg h2K, dummy]
      rw [e]; exact Or.inl (hc _)
  have H5 := netCircuit (A := A ∪ X) (a := 2 * w) (b := 0) (2 ^ p) (bitonicSort 0 p true) hnet ch hchK
    (fun _ _ j => j.elim0) (Or.inl (hc false))
  let s1 : (Fin n → Bool) → Nat → R1 w := fun v => runNet recKey (bitonicSort 0 p true) (ch v)
  have H15 := seq H1234 H5
  generalize hY : (X ∪ (({f | ∃ idx < 2 ^ p, ∃ j < 2 * w + 2, f = fun v => (runNet recKey (bitonicSort 0 p true) (ch v) idx).keyBit j} ∪
       {f | ∃ idx < 2 ^ p, ∃ j : Fin 0, f = fun v => (runNet recKey (bitonicSort 0 p true) (ch v) idx).valBit j}) ∪
       {f | ∃ t < (bitonicSort 0 p true).length,
         f = (fun v => ((netSwaps recKey (bitonicSort 0 p true) (ch v)).getD t (0, 0, false)).2.2) ∨
         f = (fun v => !(((netSwaps recKey (bitonicSort 0 p true) (ch v)).getD t (0, 0, false)).2.2))}) : Set (Sig n)) = Y at H15
  have hs1K : ∀ idx < 2 ^ p, ∀ j < 2 * w + 2, (fun v => (s1 v idx).keyBit j) ∈ Y := by
    intro idx hidx j hj
    rw [← hY]
    exact Or.inr (Or.inl (Or.inl ⟨idx, hidx, j, hj, rfl⟩))

  let eqs : Fin (2 ^ p - 1) → Sig n := fun j v => eqAdj (s1 v) j.val
  have H6 : Build (A ∪ Y) (Set.range eqs) ((2 ^ p - 1) * (10 * (2 * w + 2) + 3)) :=
    finG eqs _ (fun j => by
      have hj : j.val + 1 < 2 ^ p := by have := j.isLt; omega
      exact eqWordG (fun i v => (s1 v j.val).keyBit i) (fun i v => (s1 v (j.val + 1)).keyBit i) (2 * w + 2)
        (fun i hi => Or.inr (hs1K _ (by omega) i hi)) (fun i hi => Or.inr (hs1K _ hj i hi)) (Or.inl (hc false)))
  let nsv : Fin (2 ^ p) → Sig n := fun j v => !(surv (2 ^ p) (s1 v) j.val)
  have H7 : Build (A ∪ (Y ∪ Set.range eqs)) (Set.range nsv) (2 ^ p * 6) :=
    finG nsv 6 (fun j => by
      have hk : (fun v => (s1 v j.val).keyBit (2 * w + 1)) ∈ A ∪ (Y ∪ Set.range eqs) :=
        Or.inr (Or.inl (hs1K _ j.isLt _ (by omega)))
      have hg1 : (fun v => decide (0 < j.val) && eqAdj (s1 v) (j.val - 1)) ∈ A ∪ (Y ∪ Set.range eqs) := by
        by_cases h0 : 0 < j.val
        · have e : (fun v => decide (0 < j.val) && eqAdj (s1 v) (j.val - 1)) =
              eqs ⟨j.val - 1, by have := j.isLt; omega⟩ := by
            funext v; simp [h0, eqs]
          rw [e]; exact Or.inr (Or.inr ⟨_, rfl⟩)
        · have e : (fun v => decide (0 < j.val) && eqAdj (s1 v) (j.val - 1)) = fun _ => false := by
            funext v; simp [h0]
          rw [e]; exact Or.inl (hc false)
      have hg2 : (fun v => decide (j.val + 1 < 2 ^ p) && eqAdj (s1 v) j.val) ∈ A ∪ (Y ∪ Set.range eqs) := by
        by_cases h0 : j.val + 1 < 2 ^ p
        · have e : (fun v => decide (j.val + 1 < 2 ^ p) && eqAdj (s1 v) j.val) = eqs ⟨j.val, by omega⟩ := by
            funext v; simp [h0, eqs]
          rw [e]; exact Or.inr (Or.inr ⟨_, rfl⟩)
        · have e : (fun v => decide (j.val + 1 < 2 ^ p) && eqAdj (s1 v) j.val) = fun _ => false := by
            funext v; simp [h0]
          rw [e]; exact Or.inl (hc false)
      exact nsurvG hk hg1 hg2)
  let r2 : (Fin n → Bool) → Nat → R2 w := fun v => rec2 (2 ^ p) (s1 v)
  have hr2K : ∀ idx < 2 ^ p, ∀ j < 0 + 2, (fun v => (r2 v idx).keyBit j) ∈ A ∪ ((Y ∪ Set.range eqs) ∪ Set.range nsv) := by
    intro idx hidx j hj
    by_cases j1 : j = 1
    · subst j1
      have e : (fun v => (r2 v idx).keyBit 1) = nsv ⟨idx, hidx⟩ := by
        funext v; simp [r2, rec2, nsv]
      rw [e]; exact Or.inr (Or.inr ⟨_, rfl⟩)
    · have e : (fun v => (r2 v idx).keyBit j) = fun _ => false := by
        funext v; simp [r2, rec2, j1]
      rw [e]; exact Or.inl (hc false)
  have hr2V : ∀ idx < 2 ^ p, ∀ j : Fin (2 * w), (fun v => (r2 v idx).valBit j) ∈ A ∪ ((Y ∪ Set.range eqs) ∪ Set.range nsv) :=
    fun idx hidx j => Or.inr (Or.inl (Or.inl (hs1K idx hidx j.val (by have := j.isLt; omega))))
  have H8 := netCircuit (A := A ∪ ((Y ∪ Set.range eqs) ∪ Set.range nsv)) (a := 0) (b := 2 * w) (2 ^ p)
    (bitonicSort 0 p true) hnet r2 hr2K hr2V (Or.inl (hc false))
  have Hall := seq (seq (seq H15 H6) H7) H8
  refine ⟨_, _, ?_, Hall, ?_, ?_⟩
  · unfold stepCost
    have := hcL
    omega
  · intro i hi j hj
    have hiN : i < 2 ^ p := by omega
    by_cases j1 : j < 2 * w
    · have e : (fun v => ((stepSt w K p (row v) (st v)).1 i).keyBit j) =
          fun v => (runNet recKey (bitonicSort 0 p true) (r2 v) i).valBit ⟨j, j1⟩ := by
        funext v; simp [stepSt, back, j1, r2, s1, ch]
      rw [e]
      exact Or.inr (Or.inr (Or.inl (Or.inr ⟨i, hiN, ⟨j, j1⟩, rfl⟩)))
    · by_cases j2 : j = 2 * w
      · have e : (fun v => ((stepSt w K p (row v) (st v)).1 i).keyBit j) = fun _ => false := by
          funext v; simp [stepSt, back, j2]
        rw [e]; exact Or.inl (hc false)
      · have e : (fun v => ((stepSt w K p (row v) (st v)).1 i).keyBit j) =
            fun v => (runNet recKey (bitonicSort 0 p true) (r2 v) i).keyBit 1 := by
          funext v; simp [stepSt, back, j1, j2, r2, s1, ch]
        rw [e]
        exact Or.inr (Or.inr (Or.inl (Or.inl ⟨i, hiN, 1, by omega, rfl⟩)))
  · have hKN : K < 2 ^ p ∨ K = 0 := by omega
    have e : (fun v => !(stepSt w K p (row v) (st v)).2) =
        fun v => (runNet recKey (bitonicSort 0 p true) (r2 v) K).keyBit 1 := by
      funext v; simp [stepSt, vld2, r2, s1, ch]
    rw [e]
    by_cases hK0 : K < 2 ^ p
    · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨K, hK0, 1, by omega, rfl⟩)))
    · exfalso; have : 0 < 2 ^ p := Nat.two_pow_pos p; omega

end Circ
end PEqualNP.Outside.L_clb_100_aux

namespace PEqualNP.Outside.L_clb_100_aux
namespace Glob

open PEqualNP.CircuitLowerBounds Build049 Bitonic Lookup049 Step Emb Sem

def xin {I : Nat} (v : Fin I → Bool) (k : Nat) : Bool := if h : k < I then v ⟨k, h⟩ else false

def st0 (w : Nat) : Nat → R1 w := fun i =>
  if i < 2 ^ w then
    { keyBit := fun j => if j < w then i.testBit j else if j < 2 * w then i.testBit (j - w) else false
      valBit := fun k => k.elim0 }
  else dummy w

theorem bitsVal_self (i w : Nat) (hi : i < 2 ^ w) : bitsVal (fun j => i.testBit j) w = i := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < w
  · rw [bitsVal_testBit _ _ _ hk]
  · have h1 : bitsVal (fun j => i.testBit j) w < 2 ^ k :=
      lt_of_lt_of_le (bitsVal_lt _ _) (Nat.pow_le_pow_right (by omega) (by omega))
    have h2 : i < 2 ^ k := lt_of_lt_of_le hi (Nat.pow_le_pow_right (by omega) (by omega))
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]

theorem st0_vld (w i : Nat) : vld (st0 w i) = decide (i < 2 ^ w) := by
  unfold st0
  split_ifs with h
  · have h1 : ¬ (2 * w + 1 < w) := by omega
    have h2 : ¬ (2 * w + 1 < 2 * w) := by omega
    simp [vld, h, h1, h2]
  · simp [dummy_vld, h]

theorem st0_ek (w i : Nat) (hi : i < 2 ^ w) : ek (st0 w i) = i + 2 ^ w * i := by
  rw [ek_eq]
  have h1 : sd (st0 w i) = i := by
    unfold sd st0
    rw [if_pos hi]
    rw [← bitsVal_self i w hi]
    apply bitsVal_congr
    intro j hj
    simp [hj, bitsVal_self i w hi]
  have h2 : cu (st0 w i) = i := by
    unfold cu st0
    rw [if_pos hi]
    rw [← bitsVal_self i w hi]
    apply bitsVal_congr
    intro j hj
    have a1 : ¬ (w + j < w) := by omega
    have a2 : w + j < 2 * w := by omega
    simp [a1, a2, bitsVal_self i w hi]
  rw [h1, h2]

theorem inv0 (T : Nat → Nat → Bool) (w K : Nat) (hK : 2 ^ w ≤ K) : Inv T w K 0 (st0 w) := by
  intro e
  have hD : 0 < 2 ^ w := Nat.two_pow_pos w
  unfold mult
  by_cases ho : isOdd T w 0 e = true
  · rw [if_pos ho]
    simp only [isOdd, Bool.and_eq_true, decide_eq_true_eq] at ho
    obtain ⟨hlt, hpar⟩ := ho
    have hs : e % 2 ^ w < 2 ^ w := Nat.mod_lt _ hD
    rw [par_zero T w _ _ hs, decide_eq_true_eq] at hpar
    rw [Finset.card_eq_one]
    refine ⟨e % 2 ^ w, ?_⟩
    ext i
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, st0_vld, decide_eq_true_eq]
    constructor
    · rintro ⟨-, hi, hk⟩
      rw [st0_ek w i hi] at hk
      rw [← hk, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
    · intro hi
      subst hi
      refine ⟨by omega, hs, ?_⟩
      rw [st0_ek w _ hs]
      conv_lhs => rw [hpar]
      rw [Nat.add_comm]; nth_rewrite 2 [← hpar]
      exact Nat.div_add_mod e (2 ^ w)
  · rw [if_neg ho]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro i - ⟨hv, hk⟩
    rw [st0_vld, decide_eq_true_eq] at hv
    rw [st0_ek w i hv] at hk
    apply ho
    simp only [isOdd, Bool.and_eq_true, decide_eq_true_eq]
    have hmod : e % 2 ^ w = i := by rw [← hk, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hv]
    have hdiv : e / 2 ^ w = i := by
      rw [← hk, Nat.add_mul_div_left _ _ hD, Nat.div_eq_of_lt hv, Nat.zero_add]
    refine ⟨?_, ?_⟩
    · calc e = i + 2 ^ w * i := hk.symm
        _ < 2 ^ w + 2 ^ w * i := by omega
        _ = 2 ^ w * (i + 1) := by rw [Nat.mul_succ]; omega
        _ ≤ 2 ^ w * 2 ^ w := Nat.mul_le_mul_left _ hv
    · rw [par_zero T w _ _ (Nat.mod_lt _ hD), hmod, hdiv]
      simp

def St (w K p : Nat) {I : Nat} (v : Fin I → Bool) : Nat → (Nat → R1 w) × Bool
  | 0 => (st0 w, true)
  | h + 1 =>
    ((stepSt w K p (fun u => xin v (h * 2 ^ (w + 1) + u)) (St w K p v h).1).1,
      (St w K p v h).2 && !(stepSt w K p (fun u => xin v (h * 2 ^ (w + 1) + u)) (St w K p v h).1).2)

def good (T : Nat → Nat → Bool) (w K h : Nat) : Prop := ∀ t ≤ h, oddCard T w t ≤ K

theorem main_sem (T : Nat → Nat → Bool) (w K p L : Nat) {I : Nat} (v : Fin I → Bool)
    (hK : 2 ^ w ≤ K) (hN : 2 * K ≤ 2 ^ p)
    (hrow : ∀ h < L, ∀ u < 2 ^ (w + 1), xin v (h * 2 ^ (w + 1) + u) = T h u) :
    ∀ h ≤ L, ((St w K p v h).2 = true ↔ good T w K h) ∧ (good T w K h → Inv T w K h (St w K p v h).1) := by
  have hK1 : 1 ≤ K := le_trans (Nat.one_le_two_pow) hK
  intro h
  induction h with
  | zero =>
    intro _
    have hinv := inv0 T w K hK
    have hgood : good T w K 0 := by
      intro t ht
      have ht0 : t = 0 := by omega
      subst ht0
      rw [← inv_card hinv]
      exact (Finset.card_filter_le _ _).trans (by simp)
    exact ⟨⟨fun _ => hgood, fun _ => rfl⟩, fun _ => hinv⟩
  | succ h ih =>
    intro hh
    obtain ⟨ihc, ihi⟩ := ih (by omega)
    have hsucc : good T w K (h + 1) ↔ (good T w K h ∧ oddCard T w (h + 1) ≤ K) := by
      constructor
      · intro hg
        exact ⟨fun t ht => hg t (by omega), hg (h + 1) le_rfl⟩
      · rintro ⟨hg, hl⟩ t ht
        by_cases hth : t = h + 1
        · subst hth; exact hl
        · exact hg t (by omega)
    by_cases hg : good T w K h
    · have hspec := step_spec T w K p h (St w K p v h).1 (fun u => xin v (h * 2 ^ (w + 1) + u)) hK1 hN
        (ihi hg) (fun u hu => hrow h (by omega) u hu)
      have hcap : (St w K p v h).2 = true := ihc.mpr hg
      refine ⟨?_, ?_⟩
      · show ((St w K p v h).2 && !(stepSt w K p (fun u => xin v (h * 2 ^ (w + 1) + u)) (St w K p v h).1).2) = true ↔ _
        rw [hsucc, hcap, Bool.true_and, Bool.not_eq_true']
        constructor
        · intro hov
          refine ⟨hg, ?_⟩
          by_contra hlt
          have := hspec.1.mpr (by omega)
          rw [hov] at this
          exact absurd this (by simp)
        · rintro ⟨-, hl⟩
          by_contra hov
          have hov' : (stepSt w K p (fun u => xin v (h * 2 ^ (w + 1) + u)) (St w K p v h).1).2 = true := by
            simpa using hov
          have := hspec.1.mp hov'
          omega
      · intro hg1
        have hl := (hsucc.mp hg1).2
        apply hspec.2
        by_contra hov
        have hov' : (stepSt w K p (fun u => xin v (h * 2 ^ (w + 1) + u)) (St w K p v h).1).2 = true := by
          simpa using hov
        have := hspec.1.mp hov'
        omega
    · have hcap : (St w K p v h).2 = false := by
        by_contra hc
        exact hg (ihc.mp (by simpa using hc))
      refine ⟨?_, ?_⟩
      · show ((St w K p v h).2 && !(stepSt w K p (fun u => xin v (h * 2 ^ (w + 1) + u)) (St w K p v h).1).2) = true ↔ _
        rw [hcap, hsucc]
        simp [hg]
      · intro hg1
        exact absurd (hsucc.mp hg1).1 hg

theorem xor_fold (f : Nat → Bool) : ∀ K,
    ((List.range K).foldl (fun acc i => xor acc (f i)) false = true) ↔
      ((Finset.range K).filter (fun i => f i = true)).card % 2 = 1
  | 0 => by simp
  | K + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Finset.range_add_one,
      Finset.filter_insert]
    have ih := xor_fold f K
    by_cases hf : f K = true
    · rw [if_pos hf, Finset.card_insert_of_notMem (by simp), hf]
      cases hx : (List.range K).foldl (fun acc i => xor acc (f i)) false
      · rw [hx] at ih
        simp only [Bool.false_eq_true, false_iff] at ih
        simp only [Bool.xor_true, Bool.not_false, true_iff]
        omega
      · rw [hx] at ih
        simp only [true_iff] at ih
        simp only [Bool.xor_true, Bool.not_true, Bool.false_eq_true, false_iff]
        omega
    · rw [if_neg hf]
      have hf' : f K = false := by simpa using hf
      rw [hf', Bool.xor_false]
      exact ih

theorem final_parity {T : Nat → Nat → Bool} {w K h : Nat} {st : Nat → R1 w} (hInv : Inv T w K h st)
    (G : Nat → Nat → Bool) :
    ((Finset.range K).filter (fun i => (vld (st i) && G (sd (st i)) (cu (st i))) = true)).card =
      ((Finset.range (2 ^ w * 2 ^ w)).filter (fun e => G (e % 2 ^ w) (e / 2 ^ w) = true ∧
        Par T w h (e % 2 ^ w) (e / 2 ^ w) = true)).card := by
  classical
  have hmaps : (((Finset.range K).filter (fun i => (vld (st i) && G (sd (st i)) (cu (st i))) = true) : Finset Nat) : Set Nat).MapsTo
      (fun i => ek (st i)) (Finset.range (2 ^ w * 2 ^ w)) := by
    intro i _
    exact Finset.mem_coe.mpr (Finset.mem_range.mpr (ek_lt _))
  rw [Finset.card_eq_sum_card_fiberwise hmaps, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro e he
  have he' : e < 2 ^ w * 2 ^ w := Finset.mem_range.mp he
  rw [Finset.filter_filter]
  have hm := hInv e
  unfold mult at hm
  by_cases hG : G (e % 2 ^ w) (e / 2 ^ w) = true
  · have e1 : (Finset.range K).filter (fun i => (vld (st i) && G (sd (st i)) (cu (st i))) = true ∧ ek (st i) = e) =
        (Finset.range K).filter (fun i => vld (st i) = true ∧ ek (st i) = e) := by
      apply Finset.filter_congr
      intro i _
      constructor
      · rintro ⟨h1, h2⟩
        rw [Bool.and_eq_true] at h1
        exact ⟨h1.1, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        rw [Bool.and_eq_true]
        refine ⟨h1, ?_⟩
        rw [← ek_mod, ← ek_div, h2]; exact hG
    rw [e1, hm]
    simp [isOdd, he', hG]
  · have e1 : (Finset.range K).filter (fun i => (vld (st i) && G (sd (st i)) (cu (st i))) = true ∧ ek (st i) = e) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      rintro i - ⟨h1, h2⟩
      rw [Bool.and_eq_true] at h1
      apply hG
      rw [← h2, ek_mod, ek_div]; exact h1.2
    rw [e1]
    simp [hG]

end Glob
end PEqualNP.Outside.L_clb_100_aux

namespace PEqualNP.Outside.L_clb_100_aux
namespace Fin1

open PEqualNP.CircuitLowerBounds Build049 Bitonic Lookup049 Step Emb Sem Glob Circ

theorem sd_testBit {w : Nat} (r : R1 w) (k : Nat) : (sd r).testBit k = (decide (k < w) && r.keyBit k) := by
  by_cases hk : k < w
  · unfold sd; rw [bitsVal_testBit _ _ _ hk]; simp [hk]
  · have h1 : sd r < 2 ^ k := lt_of_lt_of_le (sd_lt r) (Nat.pow_le_pow_right (by omega) (by omega))
    rw [Nat.testBit_lt_two_pow h1]; simp [hk]

theorem cu_testBit {w : Nat} (r : R1 w) (k : Nat) : (cu r).testBit k = (decide (k < w) && r.keyBit (w + k)) := by
  by_cases hk : k < w
  · unfold cu; rw [bitsVal_testBit _ _ _ hk]; simp [hk]
  · have h1 : cu r < 2 ^ k := lt_of_lt_of_le (cu_lt r) (Nat.pow_le_pow_right (by omega) (by omega))
    rw [Nat.testBit_lt_two_pow h1]; simp [hk]

theorem patOf_eq_bitsVal (w : Nat) (bit : Nat → Bool) :
    patOf w bit = bitsVal (fun b => if b < w + 1 then bit b else false) (w + 1) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [patOf_testBit]
  by_cases hi : i < w + 1
  · rw [bitsVal_testBit _ _ _ hi]; simp [hi]
  · have h1 : bitsVal (fun b => if b < w + 1 then bit b else false) (w + 1) < 2 ^ i :=
      lt_of_lt_of_le (bitsVal_lt _ _) (Nat.pow_le_pow_right (by omega) (by omega))
    rw [Nat.testBit_lt_two_pow h1]; simp [hi]

theorem famBuild {n : Nat} {A : Set (Sig n)} (B : Nat → Set (Sig n)) (c : Nat) :
    ∀ m, (∀ r < m, Build A (B r) c) → Build A {f | ∃ r < m, f ∈ B r} (m * c)
  | 0, _ => relax (idle (A := A) (B := ∅) (by simp)) le_rfl (by rintro f ⟨r, hr, -⟩; omega) (by simp)
  | m + 1, H => by
    have h1 := famBuild B c m (fun r hr => H r (by omega))
    have h2 := relax (H m (by omega)) (C := A ∪ {f | ∃ r < m, f ∈ B r}) Set.subset_union_left le_rfl le_rfl
    refine relax (seq h1 h2) le_rfl ?_ (by rw [Nat.succ_mul])
    rintro f ⟨r, hr, hf⟩
    by_cases hrm : r = m
    · subst hrm; exact Or.inr hf
    · exact Or.inl ⟨r, by omega, hf⟩

theorem chainAnd {n : Nat} {A : Set (Sig n)} (f : Nat → Sig n) (htrue : (fun _ => true) ∈ A) :
    ∀ m, (∀ r < m, f r ∈ A) → Build A {fun v => (List.range m).all (fun r => f r v)} m
  | 0, _ => by
    have e : (fun v : Fin n → Bool => (List.range 0).all (fun r => f r v)) = fun _ => true := by
      funext v; simp
    rw [e]
    exact idle (Set.singleton_subset_iff.mpr htrue)
  | m + 1, H => by
    have h1 := chainAnd f htrue m (fun r hr => H r (by omega))
    have h2 := andG (A := A ∪ {fun v => (List.range m).all (fun r => f r v)})
      (f := fun v => (List.range m).all (fun r => f r v)) (g := f m) (Or.inr rfl) (Or.inl (H m (by omega)))
    have e : (fun v => (List.range (m + 1)).all (fun r => f r v)) =
        an (fun v => (List.range m).all (fun r => f r v)) (f m) := by
      funext v
      simp [List.range_succ, an]
    rw [e]
    exact relax (seq h1 h2) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl

theorem chainXor {n : Nat} {A : Set (Sig n)} (f : Nat → Sig n) (hfalse : (fun _ => false) ∈ A) :
    ∀ m, (∀ r < m, f r ∈ A) →
      Build A {fun v => (List.range m).foldl (fun acc i => xor acc (f i v)) false} (m * 4)
  | 0, _ => by
    have e : (fun v : Fin n → Bool => (List.range 0).foldl (fun acc i => xor acc (f i v)) false) = fun _ => false := by
      funext v; simp
    rw [e]
    exact relax (idle (Set.singleton_subset_iff.mpr hfalse)) le_rfl le_rfl (by simp)
  | m + 1, H => by
    have h1 := chainXor f hfalse m (fun r hr => H r (by omega))
    have h2 := xorG (A := A ∪ {fun v => (List.range m).foldl (fun acc i => xor acc (f i v)) false})
      (f := fun v => (List.range m).foldl (fun acc i => xor acc (f i v)) false) (g := f m)
      (Or.inr rfl) (Or.inl (H m (by omega)))
    have e : (fun v => (List.range (m + 1)).foldl (fun acc i => xor acc (f i v)) false) =
        fun v => xor ((List.range m).foldl (fun acc i => xor acc (f i v)) false) (f m v) := by
      funext v
      simp [List.range_succ]
    rw [e]
    exact relax (seq h1 h2) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) (by rw [Nat.succ_mul])

end Fin1
end PEqualNP.Outside.L_clb_100_aux

namespace PEqualNP.Outside.L_clb_100_aux
namespace Top

open PEqualNP.CircuitLowerBounds Build049 Bitonic Lookup049 Step Emb Sem Glob Circ Fin1

def A0 (I : Nat) : Set (Sig I) :=
  Set.range (fun idx : Fin I => fun v : Fin I → Bool => v idx) ∪ {fun _ => false, fun _ => true}

theorem xin_mem (I k : Nat) : (fun v : Fin I → Bool => xin v k) ∈ A0 I := by
  by_cases hk : k < I
  · have e : (fun v : Fin I → Bool => xin v k) = fun v => v ⟨k, hk⟩ := by
      funext v; simp [xin, hk]
    rw [e]; exact Or.inl ⟨⟨k, hk⟩, rfl⟩
  · have e : (fun v : Fin I → Bool => xin v k) = fun _ => false := by
      funext v; simp [xin, hk]
    rw [e]; exact Or.inr (by simp)

theorem const_mem (I : Nat) (b : Bool) : (fun _ : Fin I → Bool => b) ∈ A0 I := by
  cases b <;> exact Or.inr (by simp)

theorem chainG (I w K p : Nat) (hN : 2 * K ≤ 2 ^ p) : ∀ h,
    ∃ (c : Nat) (B : Set (Sig I)), c ≤ h * (stepCost w K p + 1) ∧ Build (A0 I) B c ∧
      (∀ i < K, ∀ j < 2 * w + 2, (fun v => ((St w K p v h).1 i).keyBit j) ∈ A0 I ∪ B) ∧
      (∀ t ≤ h, (fun v => (St w K p v t).2) ∈ A0 I ∪ B)
  | 0 => by
    refine ⟨0, ∅, by simp, idle (by simp), ?_, ?_⟩
    · intro i _ j _
      exact Or.inl (const_mem I ((st0 w i).keyBit j))
    · intro t ht
      have : t = 0 := by omega
      subst this
      exact Or.inl (const_mem I true)
  | h + 1 => by
    obtain ⟨c, B, hc, HB, hbits, hcaps⟩ := chainG I w K p hN h
    obtain ⟨c', Bout, hc', HS, hnew, hnov⟩ := stepG (A := A0 I ∪ B) w K p hN
      (fun v => (St w K p v h).1) (fun v u => xin v (h * 2 ^ (w + 1) + u)) hbits
      (fun u _ => Or.inl (xin_mem I _)) (fun b => Or.inl (const_mem I b))
    have Hc : Build ((A0 I ∪ B) ∪ Bout) {fun v => (St w K p v (h + 1)).2} 1 :=
      andG (A := (A0 I ∪ B) ∪ Bout) (f := fun v => (St w K p v h).2)
        (g := fun v => !(stepSt w K p (fun u => xin v (h * 2 ^ (w + 1) + u)) (St w K p v h).1).2)
        (Or.inl (hcaps h le_rfl)) hnov
    have Hall := seq HB (seq HS Hc)
    refine ⟨c + (c' + 1), B ∪ (Bout ∪ {fun v => (St w K p v (h + 1)).2}), ?_, Hall, ?_, ?_⟩
    · rw [Nat.succ_mul]; omega
    · intro i hi j hj
      rcases hnew i hi j hj with (h1 | h1) | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr (Or.inl h1))
    · intro t ht
      by_cases hth : t = h + 1
      · subst hth; exact Or.inr (Or.inr (Or.inr rfl))
      · rcases hcaps t (by omega) with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (Or.inl h1)

theorem closeBit_mem {I : Nat} {A : Set (Sig I)} (n w K : Nat) (st : (Fin I → Bool) → Nat → R1 w)
    (hS : ∀ i < K, ∀ j < 2 * w + 2, (fun v => (st v i).keyBit j) ∈ A) (hc : ∀ b : Bool, (fun _ => b) ∈ A)
    (i : Nat) (hi : i < K) (q : Nat) :
    (fun v => closeBit n w (sd (st v i)) (cu (st v i)) q) ∈ A := by
  by_cases h1 : n - w ≤ q
  · by_cases h2 : q - (n - w) < w
    · have e : (fun v => closeBit n w (sd (st v i)) (cu (st v i)) q) =
          fun v => (st v i).keyBit (w + (q - (n - w))) := by
        funext v; simp [closeBit, h1, cu_testBit, h2]
      rw [e]; exact hS i hi _ (by omega)
    · have e : (fun v => closeBit n w (sd (st v i)) (cu (st v i)) q) = fun _ => false := by
        funext v; simp [closeBit, h1, cu_testBit, h2]
      rw [e]; exact hc false
  · by_cases h2 : q < w
    · have e : (fun v => closeBit n w (sd (st v i)) (cu (st v i)) q) = fun v => (st v i).keyBit q := by
        funext v; simp [closeBit, h1, sd_testBit, h2]
      rw [e]; exact hS i hi _ (by omega)
    · have e : (fun v => closeBit n w (sd (st v i)) (cu (st v i)) q) = fun _ => false := by
        funext v; simp [closeBit, h1, sd_testBit, h2]
      rw [e]; exact hc false

theorem fG {n : Nat} {A : Set (Sig n)} {k a b c : Sig n} (hk : k ∈ A) (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) :
    Build A {fun v => !(k v) && ((a v && b v) && c v)} 4 := by
  show Build A {an (nt k) (an (an a b) c)} 4
  have h1 := andG ha hb
  have h2 := andG (A := A ∪ {an a b}) (f := an a b) (g := c) (Or.inr rfl) (Or.inl hc)
  have h3 := notG (A := A ∪ ({an a b} ∪ {an (an a b) c})) (Or.inl hk)
  have h4 := andG (A := A ∪ (({an a b} ∪ {an (an a b) c}) ∪ {nt k})) (f := nt k) (g := an (an a b) c)
    (Or.inr (Or.inr rfl)) (Or.inr (Or.inl (Or.inr rfl)))
  exact relax (seq (seq (seq h1 h2) h3) h4) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl

def finalCost (w K : Nat) : Nat :=
  128 * (2 ^ w + K) * (w + 1 + Nat.log2 (K + 1) + 3) ^ 3 +
    128 * (2 ^ w + K) * (w + 1 + Nat.log2 (K + 1) + 3) ^ 3 +
    w * (128 * (2 ^ (w + 1) + K) * (w + 1 + 1 + Nat.log2 (K + 1) + 3) ^ 3) + K * w + K * 4 + K * 4 + 1

theorem finalG {I : Nat} {A : Set (Sig I)} (n w K : Nat) (st : (Fin I → Bool) → Nat → R1 w) (cap : Sig I)
    (hS : ∀ i < K, ∀ j < 2 * w + 2, (fun v => (st v i).keyBit j) ∈ A) (hcap : cap ∈ A)
    (hx : ∀ k, (fun v : Fin I → Bool => xin v k) ∈ A) (hc : ∀ b : Bool, (fun _ => b) ∈ A) :
    ∃ (c : Nat) (B : Set (Sig I)), c ≤ finalCost w K ∧ Build A B c ∧
      (fun v => cap v && (List.range K).foldl (fun acc i => xor acc
        (vld (st v i) && G (fun site pat => xin v (site * 2 ^ (w + 1) + pat))
          (fun u => xin v (n * 2 ^ (w + 1) + u)) (fun u => xin v (n * 2 ^ (w + 1) + 2 ^ w + u))
          n w (sd (st v i)) (cu (st v i)))) false) ∈ A ∪ B := by

  obtain ⟨c1, hc1, H1⟩ := lookupG (A := A) w K (fun u v => xin v (n * 2 ^ (w + 1) + u.val))
    (fun i b v => (st v i.val).keyBit b.val) (fun u => hx _) (fun i b => hS i.val i.isLt b.val (by have := b.isLt; omega))
  have hsm : ∀ i (hi : i < K), (fun v => xin v (n * 2 ^ (w + 1) + sd (st v i))) ∈
      {f | ∃ j : Fin K, f = fun v => (fun (u : Fin (2 ^ w)) v => xin v (n * 2 ^ (w + 1) + u.val))
        ⟨bitsVal (fun b => if h : b < w then (fun (i : Fin K) (b : Fin w) v => (st v i.val).keyBit b.val) j ⟨b, h⟩ v else false) w,
          bitsVal_lt _ _⟩ v} := by
    intro i hi
    refine ⟨⟨i, hi⟩, ?_⟩
    funext v
    simp only
    congr 2
    unfold sd
    apply bitsVal_congr
    intro b hb
    simp [hb]

  obtain ⟨c2, hc2, H2⟩ := lookupG (A := A) w K (fun u v => xin v (n * 2 ^ (w + 1) + 2 ^ w + u.val))
    (fun i b v => (st v i.val).keyBit (w + b.val)) (fun u => hx _)
    (fun i b => hS i.val i.isLt (w + b.val) (by have := b.isLt; omega))
  have hem : ∀ i (hi : i < K), (fun v => xin v (n * 2 ^ (w + 1) + 2 ^ w + cu (st v i))) ∈
      {f | ∃ j : Fin K, f = fun v => (fun (u : Fin (2 ^ w)) v => xin v (n * 2 ^ (w + 1) + 2 ^ w + u.val))
        ⟨bitsVal (fun b => if h : b < w then (fun (i : Fin K) (b : Fin w) v => (st v i.val).keyBit (w + b.val)) j ⟨b, h⟩ v else false) w,
          bitsVal_lt _ _⟩ v} := by
    intro i hi
    refine ⟨⟨i, hi⟩, ?_⟩
    funext v
    simp only
    congr 2
    unfold cu
    apply bitsVal_congr
    intro b hb
    simp [hb]

  let BC : Nat → Set (Sig I) := fun r =>
    {f | ∃ j : Fin K, f = fun v => (fun (u : Fin (2 ^ (w + 1))) v => xin v ((n - w + r) * 2 ^ (w + 1) + u.val))
      ⟨bitsVal (fun b => if h : b < w + 1 then
          (fun (i : Fin K) (b : Fin (w + 1)) v => closeBit n w (sd (st v i.val)) (cu (st v i.val)) ((n - w + r + b.val) % n)) j ⟨b, h⟩ v
          else false) (w + 1), bitsVal_lt _ _⟩ v}
  have HCr : ∀ r < w, Build A (BC r) (128 * (2 ^ (w + 1) + K) * (w + 1 + 1 + Nat.log2 (K + 1) + 3) ^ 3) := by
    intro r _
    obtain ⟨c3, hc3, H3⟩ := lookupG (A := A) (w + 1) K (fun u v => xin v ((n - w + r) * 2 ^ (w + 1) + u.val))
      (fun i b v => closeBit n w (sd (st v i.val)) (cu (st v i.val)) ((n - w + r + b.val) % n)) (fun u => hx _)
      (fun i b => closeBit_mem n w K st hS hc i.val i.isLt _)
    exact relax H3 le_rfl le_rfl hc3
  have HC := famBuild BC _ w HCr
  have hcl : ∀ r i (hi : i < K), (fun v => xin v ((n - w + r) * 2 ^ (w + 1) +
      closePat n w (n - w + r) (sd (st v i)) (cu (st v i)))) ∈ BC r := by
    intro r i hi
    refine ⟨⟨i, hi⟩, ?_⟩
    funext v
    simp only
    congr 2
    unfold closePat
    rw [patOf_eq_bitsVal]
    apply bitsVal_congr
    intro b hb
    simp [hb]

  let allS : Nat → Sig I := fun i v => (List.range w).all (fun r =>
    xin v ((n - w + r) * 2 ^ (w + 1) + closePat n w (n - w + r) (sd (st v i)) (cu (st v i))))
  generalize hB1 : ({f | ∃ j : Fin K, f = fun v => (fun (u : Fin (2 ^ w)) v => xin v (n * 2 ^ (w + 1) + u.val))
        ⟨bitsVal (fun b => if h : b < w then (fun (i : Fin K) (b : Fin w) v => (st v i.val).keyBit b.val) j ⟨b, h⟩ v else false) w,
          bitsVal_lt _ _⟩ v} : Set (Sig I)) = B1 at H1 hsm
  generalize hB2 : ({f | ∃ j : Fin K, f = fun v => (fun (u : Fin (2 ^ w)) v => xin v (n * 2 ^ (w + 1) + 2 ^ w + u.val))
        ⟨bitsVal (fun b => if h : b < w then (fun (i : Fin K) (b : Fin w) v => (st v i.val).keyBit (w + b.val)) j ⟨b, h⟩ v else false) w,
          bitsVal_lt _ _⟩ v} : Set (Sig I)) = B2 at H2 hem
  generalize hBCs : ({f | ∃ r < w, f ∈ BC r} : Set (Sig I)) = BCs at HC
  have hclS : ∀ r < w, ∀ i (hi : i < K), (fun v => xin v ((n - w + r) * 2 ^ (w + 1) +
      closePat n w (n - w + r) (sd (st v i)) (cu (st v i)))) ∈ BCs := by
    intro r hr i hi; rw [← hBCs]; exact ⟨r, hr, hcl r i hi⟩
  have Hb := relax H2 (C := A ∪ B1) Set.subset_union_left le_rfl le_rfl
  have Hc := relax HC (C := A ∪ (B1 ∪ B2)) Set.subset_union_left le_rfl le_rfl
  have Hd : Build (A ∪ ((B1 ∪ B2) ∪ BCs)) (Set.range fun i : Fin K => allS i.val) (K * w) :=
    finG (fun i : Fin K => allS i.val) w (fun i =>
      chainAnd (fun r v => xin v ((n - w + r) * 2 ^ (w + 1) + closePat n w (n - w + r) (sd (st v i.val)) (cu (st v i.val))))
        (Or.inl (hc true)) w (fun r hr => Or.inr (Or.inr (hclS r hr i.val i.isLt))))
  let F : Nat → Sig I := fun i v => vld (st v i) && G (fun site pat => xin v (site * 2 ^ (w + 1) + pat))
          (fun u => xin v (n * 2 ^ (w + 1) + u)) (fun u => xin v (n * 2 ^ (w + 1) + 2 ^ w + u))
          n w (sd (st v i)) (cu (st v i))
  have He : Build (A ∪ (((B1 ∪ B2) ∪ BCs) ∪ (Set.range fun i : Fin K => allS i.val)))
      (Set.range fun i : Fin K => F i.val) (K * 4) :=
    finG (fun i : Fin K => F i.val) 4 (fun i =>
      fG (k := fun v => (st v i.val).keyBit (2 * w + 1))
        (a := fun v => xin v (n * 2 ^ (w + 1) + sd (st v i.val)))
        (b := fun v => xin v (n * 2 ^ (w + 1) + 2 ^ w + cu (st v i.val))) (c := allS i.val)
        (Or.inl (hS i.val i.isLt _ (by omega)))
        (Or.inr (Or.inl (Or.inl (Or.inl (hsm i.val i.isLt)))))
        (Or.inr (Or.inl (Or.inl (Or.inr (hem i.val i.isLt)))))
        (Or.inr (Or.inr ⟨i, rfl⟩)))
  have Hf := chainXor (A := A ∪ ((((B1 ∪ B2) ∪ BCs) ∪ (Set.range fun i : Fin K => allS i.val)) ∪
      (Set.range fun i : Fin K => F i.val))) F (Or.inl (hc false)) K
    (fun r hr => Or.inr (Or.inr ⟨⟨r, hr⟩, rfl⟩))
  have Hg := andG (A := A ∪ (((((B1 ∪ B2) ∪ BCs) ∪ (Set.range fun i : Fin K => allS i.val)) ∪
      (Set.range fun i : Fin K => F i.val)) ∪ {fun v => (List.range K).foldl (fun acc i => xor acc (F i v)) false}))
    (f := cap) (g := fun v => (List.range K).foldl (fun acc i => xor acc (F i v)) false)
    (Or.inl hcap) (Or.inr (Or.inr rfl))
  have Hall := seq (seq (seq (seq (seq (seq H1 Hb) Hc) Hd) He) Hf) Hg
  refine ⟨_, _, ?_, Hall, Or.inr (Or.inr rfl)⟩
  unfold finalCost
  omega

end Top
end PEqualNP.Outside.L_clb_100_aux

namespace PEqualNP.Outside.L_clb_100_aux
namespace Top

open Bitonic Circ

theorem size_bound (n w K : Nat) (hw : w ≤ n) (hK1 : 2 ^ w ≤ K) (hK2 : K ≤ 4 ^ w) :
    2 + ((n - w) * (stepCost w K (Nat.clog 2 (2 * K)) + 1) + finalCost w K) ≤
      1048576 * (n + 1) * K * (w + 1) ^ 3 := by
  have hKpos : 1 ≤ K := le_trans Nat.one_le_two_pow hK1
  have h4 : (4 : Nat) ^ w = 2 ^ (2 * w) := by rw [show (4 : Nat) = 2 ^ 2 from rfl, ← pow_mul]
  have hK2' : K ≤ 2 ^ (2 * w) := h4 ▸ hK2
  have hpos : 0 < Nat.clog 2 (2 * K) := Nat.clog_pos (by omega) (by omega)
  have hpred : 2 ^ (Nat.clog 2 (2 * K) - 1) < 2 * K := by
    have := Nat.pow_pred_clog_lt_self 2 (show 1 < 2 * K by omega)
    simpa [Nat.pred_eq_sub_one] using this
  generalize Nat.clog 2 (2 * K) = p at hpos hpred ⊢
  have hNp : 2 ^ p = 2 * 2 ^ (p - 1) := by
    conv_lhs => rw [show p = (p - 1) + 1 by omega]
    rw [Nat.pow_succ]; omega
  have hN : 2 ^ p ≤ 4 * K := by omega
  have hp2 : p ≤ 2 * w + 1 := by
    have h1 : 2 ^ (p - 1) < 2 ^ (2 * w + 1) := by
      have : 2 * K ≤ 2 ^ (2 * w + 1) := by rw [Nat.pow_succ]; omega
      omega
    have := (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp h1
    omega
  have ha : 2 ^ (w + 1) ≤ 2 * K := by rw [Nat.pow_succ]; omega
  have hl1 : Nat.log2 (2 * K + 1) ≤ 2 * w + 1 := by
    have : Nat.log2 (2 * K + 1) < 2 * w + 2 := by
      rw [Nat.log2_lt (by omega), Nat.pow_succ, Nat.pow_succ]
      have := Nat.two_pow_pos (2 * w)
      omega
    omega
  have hl2 : Nat.log2 (K + 1) ≤ 2 * w + 1 := by
    have : Nat.log2 (K + 1) < 2 * w + 2 := by
      rw [Nat.log2_lt (by omega), Nat.pow_succ, Nat.pow_succ]
      have := Nat.two_pow_pos (2 * w)
      omega
    omega
  have hlen4 := bitonicSort_length 0 p true
  have hlen' : (bitonicSort 0 p true).length ≤ 4 * (w + 1) ^ 2 * K := by
    have h1 : p * (p + 1) ≤ (2 * w + 1) * (2 * w + 2) := Nat.mul_le_mul hp2 (by omega)
    have h2 : p * (p + 1) * 2 ^ p ≤ (2 * w + 1) * (2 * w + 2) * (4 * K) := Nat.mul_le_mul h1 hN
    have h3 : (2 * w + 1) * (2 * w + 2) * (4 * K) ≤ 4 * (4 * (w + 1) ^ 2 * K) := by nlinarith
    omega
  have hW3 : 1 ≤ (w + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hKX : K ≤ K * (w + 1) ^ 3 := Nat.le_mul_of_pos_right K (by omega)
  have hX1 : 1 ≤ K * (w + 1) ^ 3 := le_trans hKpos hKX
  have hs : stepCost w K p + 1 ≤ 110898 * (K * (w + 1) ^ 3) := by
    unfold stepCost
    have t1 : 128 * (2 ^ (w + 1) + 2 * K) * (w + 1 + 1 + Nat.log2 (2 * K + 1) + 3) ^ 3 ≤
        110592 * (K * (w + 1) ^ 3) := by
      calc 128 * (2 ^ (w + 1) + 2 * K) * (w + 1 + 1 + Nat.log2 (2 * K + 1) + 3) ^ 3
          ≤ 128 * (4 * K) * (6 * (w + 1)) ^ 3 :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (Nat.pow_le_pow_left (by omega) 3)
        _ = 110592 * (K * (w + 1) ^ 3) := by ring
    have t3 : (bitonicSort 0 p true).length * (11 * (2 * w) + 6 * 0 + 23) ≤ 92 * (K * (w + 1) ^ 3) := by
      calc (bitonicSort 0 p true).length * (11 * (2 * w) + 6 * 0 + 23)
          ≤ (4 * (w + 1) ^ 2 * K) * (23 * (w + 1)) := Nat.mul_le_mul hlen' (by omega)
        _ = 92 * (K * (w + 1) ^ 3) := by ring
    have t4 : (2 ^ p - 1) * (10 * (2 * w + 2) + 3) ≤ 92 * (K * (w + 1) ^ 3) := by
      calc (2 ^ p - 1) * (10 * (2 * w + 2) + 3) ≤ (4 * K) * (23 * (w + 1)) :=
            Nat.mul_le_mul (by omega) (by omega)
        _ = 92 * (K * (w + 1)) := by ring
        _ ≤ 92 * (K * (w + 1) ^ 3) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.le_self_pow (by omega) _))
    have t6 : (bitonicSort 0 p true).length * (11 * 0 + 6 * (2 * w) + 23) ≤ 92 * (K * (w + 1) ^ 3) := by
      calc (bitonicSort 0 p true).length * (11 * 0 + 6 * (2 * w) + 23)
          ≤ (4 * (w + 1) ^ 2 * K) * (23 * (w + 1)) := Nat.mul_le_mul hlen' (by omega)
        _ = 92 * (K * (w + 1) ^ 3) := by ring
    omega
  have hf : finalCost w K ≤ 64012 * (K * (w + 1) ^ 3) + 82944 * (w * (K * (w + 1) ^ 3)) := by
    unfold finalCost
    have u1 : 128 * (2 ^ w + K) * (w + 1 + Nat.log2 (K + 1) + 3) ^ 3 ≤ 32000 * (K * (w + 1) ^ 3) := by
      calc 128 * (2 ^ w + K) * (w + 1 + Nat.log2 (K + 1) + 3) ^ 3
          ≤ 128 * (2 * K) * (5 * (w + 1)) ^ 3 :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (Nat.pow_le_pow_left (by omega) 3)
        _ = 32000 * (K * (w + 1) ^ 3) := by ring
    have u2 : w * (128 * (2 ^ (w + 1) + K) * (w + 1 + 1 + Nat.log2 (K + 1) + 3) ^ 3) ≤
        82944 * (w * (K * (w + 1) ^ 3)) := by
      calc w * (128 * (2 ^ (w + 1) + K) * (w + 1 + 1 + Nat.log2 (K + 1) + 3) ^ 3)
          ≤ w * (128 * (3 * K) * (6 * (w + 1)) ^ 3) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega))
              (Nat.pow_le_pow_left (by omega) 3))
        _ = 82944 * (w * (K * (w + 1) ^ 3)) := by ring
    have u3 : K * w ≤ K * (w + 1) ^ 3 :=
      Nat.mul_le_mul_left _ (le_trans (by omega : w ≤ w + 1) (Nat.le_self_pow (by omega) _))
    omega
  have hsum : (n - w) * (stepCost w K p + 1) ≤ 110898 * ((n - w) * (K * (w + 1) ^ 3)) := by
    calc (n - w) * (stepCost w K p + 1) ≤ (n - w) * (110898 * (K * (w + 1) ^ 3)) := Nat.mul_le_mul_left _ hs
      _ = 110898 * ((n - w) * (K * (w + 1) ^ 3)) := by ring
  have hnX : (n - w) * (K * (w + 1) ^ 3) + w * (K * (w + 1) ^ 3) = n * (K * (w + 1) ^ 3) := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hw]
  have htarget : 1048576 * (n + 1) * K * (w + 1) ^ 3 =
      1048576 * (n * (K * (w + 1) ^ 3) + K * (w + 1) ^ 3) := by ring
  rw [htarget]
  omega

end Top
end PEqualNP.Outside.L_clb_100_aux

namespace PEqualNP.Outside.L_clb_100_aux
namespace Top

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open Build049 Bitonic Lookup049 Step Emb Sem Glob Circ Fin1

theorem three_a {m k : Nat} (f : Nat → Bool) (l2 l3 : List Bool) (hk : k < m) :
    ((List.range m).map f ++ l2 ++ l3).getD k false = f k := by
  rw [List.append_assoc, List.getD_append _ _ _ _ (by simpa using hk)]
  simp [List.getD_eq_getElem?_getD, hk]

theorem three_b {m d k : Nat} (f g : Nat → Bool) (l3 : List Bool) (hk : k < d) :
    ((List.range m).map f ++ (List.range d).map g ++ l3).getD (m + k) false = g k := by
  rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD, hk]

theorem three_c {m d k : Nat} (f g h : Nat → Bool) (hk : k < d) :
    ((List.range m).map f ++ (List.range d).map g ++ (List.range d).map h).getD (m + d + k) false = h k := by
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD, hk]

theorem G_eq (T : Nat → Nat → Bool) (sm em : Nat → Bool) (n w : Nat) {I : Nat} (v : Fin I → Bool)
    (hrowT : ∀ h < n, ∀ u < 2 ^ (w + 1), xin v (h * 2 ^ (w + 1) + u) = T h u)
    (hsm : ∀ u < 2 ^ w, xin v (n * 2 ^ (w + 1) + u) = sm u)
    (hem : ∀ u < 2 ^ w, xin v (n * 2 ^ (w + 1) + 2 ^ w + u) = em u)
    (hw : w ≤ n) (s c : Nat) (hs : s < 2 ^ w) (hc : c < 2 ^ w) :
    G (fun site pat => xin v (site * 2 ^ (w + 1) + pat)) (fun u => xin v (n * 2 ^ (w + 1) + u))
      (fun u => xin v (n * 2 ^ (w + 1) + 2 ^ w + u)) n w s c = G T sm em n w s c := by
  apply Bool.eq_iff_iff.mpr
  simp only [G, Bool.and_eq_true, List.all_eq_true, List.mem_range]
  rw [hsm s hs, hem c hc]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun r hr => ?_⟩
    have hlt : closePat n w (n - w + r) s c < 2 ^ (w + 1) := patOf_lt _ _
    rw [← hrowT (n - w + r) (by omega) _ hlt]
    exact h2 r hr
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun r hr => ?_⟩
    have hlt : closePat n w (n - w + r) s c < 2 ^ (w + 1) := patOf_lt _ _
    rw [hrowT (n - w + r) (by omega) _ hlt]
    exact h2 r hr

theorem main : (∀ (n w K : Nat) (hn : 0 < n), w ≤ n → 2^w ≤ K → K ≤ 4^w →
  let D := 2^w
  let stride := 2^(w+1)
  let L := n-w
  let I := n*stride + 2*D
  let pos := fun (offset : Nat) => (⟨offset % n, Nat.mod_lt _ hn⟩ : Fin n)
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (capWire : Fin (L+1) → Fin (I+C.size)),
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack I C ∧ C.output < I+C.size ∧
    C.size ≤ 1048576*(n+1)*K*(w+1)^3 ∧
    ∀ (table : Fin n → Nat → Bool) (seedMask endMask : Nat → Bool),
      let inputs := (List.range (n*stride)).map (fun a => table (pos (a/stride)) (a % stride)) ++
        (List.range D).map seedMask ++ (List.range D).map endMask
      let oddPairs := fun (h : Nat) =>
        ((List.range (D*D)).filter (fun edge =>
          (((List.range (2^(w+h))).filter (fun bits =>
            bits % D == edge % D && (bits >>> h) % D == edge / D &&
            (List.range h).all (fun site => table (pos site) ((bits >>> site) % stride)))).length.testBit 0))).length
      let good := fun (h : Nat) => ∀ t ≤ h, oddPairs t ≤ K
      let cyclicPattern := fun (word start : Nat) =>
        (List.range (w+1)).foldl (fun (acc j : Nat) =>
          acc ||| ((word.testBit ((start+j) % n)).toNat <<< j)) 0
      let count := ((List.range (2^n)).filter (fun x =>
        seedMask (x % D) && endMask ((x >>> L) % D) &&
        (List.range n).all (fun i => table (pos i) (cyclicPattern x i)))).length
      (∀ j : Fin (L+1), (C.wires inputs).getD (capWire j).val false = true ↔ good j.val) ∧
      (C.eval inputs = true ↔ good L ∧ count.testBit 0 = true)) := by
  intro n w K hn hw hK1 hK2 D stride L I pos
  have hsz := size_bound n w K hw hK1 hK2
  have hN : 2 * K ≤ 2 ^ Nat.clog 2 (2 * K) := Nat.le_pow_clog (by omega) _
  generalize Nat.clog 2 (2 * K) = p at hsz hN
  have Hconst : Build (Set.range (fun idx : Fin I => fun v : Fin I → Bool => v idx))
      {fun _ => false, fun _ => true} 2 := by
    simpa only [Set.singleton_union] using
      (seq (constG (A := Set.range (fun idx : Fin I => fun v : Fin I → Bool => v idx)) false)
        (constG (A := Set.range (fun idx : Fin I => fun v : Fin I → Bool => v idx) ∪ {fun _ => false}) true))
  obtain ⟨c1, B1, hc1, HB1, hbits, hcaps⟩ := chainG I w K p hN L
  obtain ⟨c2, B2, hc2, HB2, hout⟩ := finalG (A := A0 I ∪ B1) n w K (fun v => (St w K p v L).1)
    (fun v => (St w K p v L).2) hbits (hcaps L le_rfl) (fun k => Or.inl (xin_mem I k))
    (fun b => Or.inl (const_mem I b))
  have Htot : Build (Set.range (fun idx : Fin I => fun v : Fin I → Bool => v idx))
      ({fun _ => false, fun _ => true} ∪ (B1 ∪ B2)) (2 + (c1 + c2)) := seq Hconst (seq HB1 HB2)
  obtain ⟨c, hc, HS⟩ := Htot.run
    (GateBridge.start (F := id) (fun i : Fin I => fun v : Fin I → Bool => v i) (by intros; rfl)) le_rfl
  rcases HS with ⟨gs, hgs, hread, hfan, hwire⟩
  have hsubA : ∀ f : Sig I, f ∈ A0 I ∪ B1 →
      f ∈ Set.range (fun idx : Fin I => fun v : Fin I → Bool => v idx) ∪
        ({fun _ => false, fun _ => true} ∪ (B1 ∪ B2)) := by
    intro f hf
    rcases hf with hf | hf
    · rcases (show f ∈ Set.range (fun idx : Fin I => fun v : Fin I → Bool => v idx) ∪
          {fun _ => false, fun _ => true} from hf) with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl hf))
  have hsubB : ∀ f : Sig I, f ∈ (A0 I ∪ B1) ∪ B2 →
      f ∈ Set.range (fun idx : Fin I => fun v : Fin I → Bool => v idx) ∪
        ({fun _ => false, fun _ => true} ∪ (B1 ∪ B2)) := by
    intro f hf
    rcases hf with hf | hf
    · exact hsubA f hf
    · exact Or.inr (Or.inr (Or.inr hf))
  have hcapEx : ∀ j : Fin (L + 1), ∃ idx, idx < I + (0 + c) ∧ ∀ x : Fin I → Bool,
      ((Circuit.mk gs 0).wires (List.ofFn x)).getD idx false = (St w K p x j.val).2 :=
    fun j => hwire _ (hsubA _ (hcaps j.val (by have := j.isLt; omega)))
  obtain ⟨io, hio, hvo⟩ := hwire _ (hsubB _ hout)
  have hsize : (Circuit.mk gs io).size = 0 + c := hgs
  refine ⟨⟨gs, io⟩, fun j => ⟨Classical.choose (hcapEx j), by
    rw [hsize]; exact (Classical.choose_spec (hcapEx j)).1⟩, hfan, hread, ?_, ?_, ?_⟩
  · rw [hsize]; exact hio
  · rw [hsize]
    have hc1' : c1 ≤ (n - w) * (stepCost w K p + 1) := hc1
    omega
  · intro table seedMask endMask inputs oddPairs good cyclicPattern count
    have hlen : inputs.length = I := by
      simp only [inputs, List.length_append, List.length_map, List.length_range, I]
      omega
    have hv : List.ofFn (fun k : Fin I => inputs.getD k.val false) = inputs := ofFn_getD inputs I hlen
    generalize hvdef : (fun k : Fin I => inputs.getD k.val false) = v at hv
    have hxin : ∀ k, xin v k = inputs.getD k false := by
      intro k
      unfold xin
      split_ifs with hk
      · rw [← hvdef]
      · rw [List.getD_eq_default _ _ (by omega)]
    have hsp : 0 < stride := Nat.two_pow_pos _
    have hrowT : ∀ h < n, ∀ u < stride, xin v (h * stride + u) = table (pos h) u := by
      intro h hh u hu
      rw [hxin]
      have hk : h * stride + u < n * stride := by
        calc h * stride + u < h * stride + stride := by omega
          _ = (h + 1) * stride := by rw [Nat.succ_mul]
          _ ≤ n * stride := Nat.mul_le_mul_right _ (by omega)
      have h3 := three_a (fun a => table (pos (a / stride)) (a % stride))
        ((List.range D).map seedMask) ((List.range D).map endMask) hk
      have e1 : (h * stride + u) / stride = h := by
        rw [Nat.mul_comm, Nat.mul_add_div hsp, Nat.div_eq_of_lt hu, Nat.add_zero]
      have e2 : (h * stride + u) % stride = u := by
        rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hu]
      simp only [e1, e2] at h3
      exact h3
    have hsm : ∀ u < D, xin v (n * stride + u) = seedMask u := by
      intro u hu
      rw [hxin]
      exact three_b (fun a => table (pos (a / stride)) (a % stride)) seedMask ((List.range D).map endMask) hu
    have hem : ∀ u < D, xin v (n * stride + D + u) = endMask u := by
      intro u hu
      rw [hxin]
      exact three_c (fun a => table (pos (a / stride)) (a % stride)) seedMask endMask hu
    have hms := main_sem (fun site pat => table (pos site) pat) w K p L v hK1 hN
      (fun h hh u hu => hrowT h (by omega) u hu)
    have hodd : ∀ t, oddPairs t = oddCard (fun site pat => table (pos site) pat) w t := by
      intro t
      show ((List.range (D * D)).filter _).length = _
      rw [len_filter_range]
      rfl
    have hgood : ∀ j, good j ↔ Glob.good (fun site pat => table (pos site) pat) w K j := by
      intro j
      constructor
      · intro hg t ht; rw [← hodd]; exact hg t ht
      · intro hg t ht; rw [hodd]; exact hg t ht
    have hwires : (Circuit.mk gs io).wires inputs = (Circuit.mk gs 0).wires (List.ofFn v) := by
      rw [hv]; rfl
    refine ⟨?_, ?_⟩
    · intro j
      show ((Circuit.mk gs io).wires inputs).getD (Classical.choose (hcapEx j)) false = true ↔ good j.val
      rw [hwires, (Classical.choose_spec (hcapEx j)).2 v, hgood]
      exact (hms j.val (by have := j.isLt; omega)).1
    · show ((Circuit.mk gs io).wires inputs).getD io false = true ↔ _
      rw [hwires, hvo v]
      simp only [id, Bool.and_eq_true]
      rw [(hms L le_rfl).1, hgood L]
      apply and_congr_right
      intro hg
      have hInv := (hms L le_rfl).2 hg
      rw [xor_fold, final_parity hInv]
      have hcp := count_parity (fun site pat => table (pos site) pat) seedMask endMask n w hn hw
      have hfilt : (Finset.range (2 ^ w * 2 ^ w)).filter (fun e =>
          G (fun site pat => xin v (site * 2 ^ (w + 1) + pat)) (fun u => xin v (n * 2 ^ (w + 1) + u))
            (fun u => xin v (n * 2 ^ (w + 1) + 2 ^ w + u)) n w (e % 2 ^ w) (e / 2 ^ w) = true ∧
          Par (fun site pat => table (pos site) pat) w L (e % 2 ^ w) (e / 2 ^ w) = true) =
        (Finset.range (2 ^ w * 2 ^ w)).filter (fun e =>
          G (fun site pat => table (pos site) pat) seedMask endMask n w (e % 2 ^ w) (e / 2 ^ w) = true ∧
          Par (fun site pat => table (pos site) pat) w (n - w) (e % 2 ^ w) (e / 2 ^ w) = true) := by
        apply Finset.filter_congr
        intro e he
        have he' := Finset.mem_range.mp he
        rw [G_eq (fun site pat => table (pos site) pat) seedMask endMask n w v hrowT hsm hem hw _ _
          (Nat.mod_lt _ (Nat.two_pow_pos w)) (Nat.div_lt_of_lt_mul he')]
      rw [hfilt]
      exact hcp.symm

end Top
end PEqualNP.Outside.L_clb_100_aux

theorem PEqualNP.Outside.L_clb_100 : (∀ (n w K : Nat) (hn : 0 < n), w ≤ n → 2^w ≤ K → K ≤ 4^w →
  let D := 2^w
  let stride := 2^(w+1)
  let L := n-w
  let I := n*stride + 2*D
  let pos := fun (offset : Nat) => (⟨offset % n, Nat.mod_lt _ hn⟩ : Fin n)
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (capWire : Fin (L+1) → Fin (I+C.size)),
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack I C ∧ C.output < I+C.size ∧
    C.size ≤ 1048576*(n+1)*K*(w+1)^3 ∧
    ∀ (table : Fin n → Nat → Bool) (seedMask endMask : Nat → Bool),
      let inputs := (List.range (n*stride)).map (fun a => table (pos (a/stride)) (a % stride)) ++
        (List.range D).map seedMask ++ (List.range D).map endMask
      let oddPairs := fun (h : Nat) =>
        ((List.range (D*D)).filter (fun edge =>
          (((List.range (2^(w+h))).filter (fun bits =>
            bits % D == edge % D && (bits >>> h) % D == edge / D &&
            (List.range h).all (fun site => table (pos site) ((bits >>> site) % stride)))).length.testBit 0))).length
      let good := fun (h : Nat) => ∀ t ≤ h, oddPairs t ≤ K
      let cyclicPattern := fun (word start : Nat) =>
        (List.range (w+1)).foldl (fun (acc j : Nat) =>
          acc ||| ((word.testBit ((start+j) % n)).toNat <<< j)) 0
      let count := ((List.range (2^n)).filter (fun x =>
        seedMask (x % D) && endMask ((x >>> L) % D) &&
        (List.range n).all (fun i => table (pos i) (cyclicPattern x i)))).length
      (∀ j : Fin (L+1), (C.wires inputs).getD (capWire j).val false = true ↔ good j.val) ∧
      (C.eval inputs = true ↔ good L ∧ count.testBit 0 = true)) :=
  PEqualNP.Outside.L_clb_100_aux.Top.main
