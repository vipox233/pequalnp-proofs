import PEqualNP.Defs

namespace PEqualNP.Outside.L_clb_049_aux

namespace GateBridge

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)

variable {α : Type*}

private def Scheduled (n : Nat) (F : α → (Fin n → Bool) → Bool) (k : Nat) (S : Set α) : Prop :=
  ∃ gs : List Gate, gs.length = k ∧ ReadsBack n ⟨gs, 0⟩ ∧ FanInTwo ⟨gs, 0⟩ ∧
    ∀ a ∈ S, ∃ i : Nat, i < n + k ∧
      ∀ x : Fin n → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = F a x

private theorem wireLength (C : Circuit) (w : List Bool) :
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

private theorem start {n : Nat} {F : α → (Fin n → Bool) → Bool}
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

private theorem restrict {n k : Nat} {F : α → (Fin n → Bool) → Bool} {S T : Set α}
    (h : Scheduled n F k S) (hsub : T ⊆ S) : Scheduled n F k T := by
  obtain ⟨gs, hs, hr, hf, hw⟩ := h
  exact ⟨gs, hs, hr, hf, fun a ha => hw a (hsub ha)⟩

private theorem realizeDeps {n k : Nat} {F : α → (Fin n → Bool) → Bool} {S : Set α}
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

private theorem push {n k : Nat} {F : α → (Fin n → Bool) → Bool} {S : Set α}
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
private abbrev Sig (n : Nat) := (Fin n → Bool) → Bool

private def Build (A B : Set (Sig n)) (b : Nat) : Prop :=
  True ∧ (∀ {m S}, GateBridge.Scheduled n id m S → A ⊆ S →
    ∃ c ≤ b, GateBridge.Scheduled n id (m + c) (S ∪ B))

private theorem Build.run {A B : Set (Sig n)} {b m S} (H : Build A B b)
    (HS : GateBridge.Scheduled n id m S) (hA : A ⊆ S) :
    ∃ c ≤ b, GateBridge.Scheduled n id (m + c) (S ∪ B) := H.2 HS hA

private theorem idle {A B : Set (Sig n)} (h : B ⊆ A) : Build A B 0 := by
  refine ⟨trivial, ?_⟩
  intro m S HS hA
  refine ⟨0, Nat.le_refl _, ?_⟩
  simpa [Set.union_eq_left.mpr (h.trans hA)] using HS

private theorem relax {A B C D : Set (Sig n)} {b d : Nat}
    (H : Build A B b) (hA : A ⊆ C) (hB : D ⊆ B) (h : b ≤ d) : Build C D d := by
  refine ⟨trivial, ?_⟩
  intro m S HS hC
  obtain ⟨c, hc, HS'⟩ := H.run HS (hA.trans hC)
  exact ⟨c, hc.trans h, GateBridge.restrict HS' (Set.union_subset_union le_rfl hB)⟩

private theorem seq {A B C : Set (Sig n)} {b c : Nat}
    (H : Build A B b) (J : Build (A ∪ B) C c) : Build A (B ∪ C) (b + c) := by
  refine ⟨trivial, ?_⟩
  intro m S HS hA
  obtain ⟨d, hd, K⟩ := H.run HS hA
  obtain ⟨e, he, K'⟩ := J.run K (Set.union_subset_union hA le_rfl)
  exact ⟨d + e, Nat.add_le_add hd he, by simpa [Nat.add_assoc, Set.union_assoc] using K'⟩

private theorem one {A : Set (Sig n)} (op : GateOp) (deps : List (Sig n))
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (hlen : deps.length ≤ 2)
    (hd : ∀ g ∈ deps, g ∈ A) (f : Sig n)
    (hv : ∀ x, f x = op.eval (deps.map fun g => g x)) : Build A {f} 1 := by
  refine ⟨trivial, ?_⟩
  intro m S HS hA
  refine ⟨1, le_rfl, ?_⟩
  have h := GateBridge.push HS op deps f hop hlen (fun g hg => hA (hd g hg)) hv
  rw [Set.insert_eq] at h
  exact GateBridge.restrict h (by intro g hg; exact hg.elim Or.inr Or.inl)

private def an (f g : Sig n) : Sig n := fun x => f x && g x
private def or (f g : Sig n) : Sig n := fun x => f x || g x
private def nt (f : Sig n) : Sig n := fun x => !f x

private theorem andG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {an f g} 1 :=
  one .and [f, g] (by simp) (by simp) (by simpa using And.intro hf hg) _ (by simp [GateOp.eval, an])

private theorem orG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {or f g} 1 :=
  one .or [f, g] (by simp) (by simp) (by simpa using And.intro hf hg) _ (by simp [GateOp.eval, or])

private theorem notG {A : Set (Sig n)} {f : Sig n} (hf : f ∈ A) : Build A {nt f} 1 :=
  one .not [f] (by simp) (by simp) (by simpa using hf) _ (by simp [GateOp.eval, nt])

private theorem constG {A : Set (Sig n)} (b : Bool) : Build A {fun _ => b} 1 := by
  cases b
  · exact one .or [] (by simp) (by simp) (by simp) _ (by intro; rfl)
  · exact one .and [] (by simp) (by simp) (by simp) _ (by intro; rfl)

private theorem muxG {A : Set (Sig n)} {sw nsw t f : Sig n}
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

private theorem listBuild {α : Type*} {A : Set (Sig n)} (xs : List α)
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

private theorem finG {k : Nat} {A : Set (Sig n)} (F : Fin k → Sig n) (c : Nat)
    (H : ∀ i, Build A {F i} c) : Build A (Set.range F) (k * c) := by
  have h := listBuild (List.finRange k) F c (fun i _ => H i)
  rw [List.length_finRange] at h
  refine relax h le_rfl ?_ le_rfl
  rintro _ ⟨i, rfl⟩
  exact ⟨i, List.mem_finRange i, rfl⟩

private theorem ltStepG {A : Set (Sig n)} {xm ym prev : Sig n}
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

private def bitsVal (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | m + 1 => bitsVal f m + if f m then 2 ^ m else 0

private theorem bitsVal_lt (f : Nat → Bool) : ∀ m, bitsVal f m < 2 ^ m
  | 0 => by simp [bitsVal]
  | m + 1 => by
    have ih := bitsVal_lt f m
    simp only [bitsVal, Nat.pow_succ]
    cases f m <;> simp <;> omega

private theorem bitsVal_testBit (f : Nat → Bool) : ∀ m i, i < m → (bitsVal f m).testBit i = f i
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

private theorem bitsVal_lt_step (f g : Nat → Bool) (m : Nat) :
    decide (bitsVal f (m + 1) < bitsVal g (m + 1)) =
      ((!(f m) && g m) || ((!(f m) || g m) && decide (bitsVal f m < bitsVal g m))) := by
  have hf := bitsVal_lt f m
  have hg := bitsVal_lt g m
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  simp only [bitsVal, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
  cases f m <;> cases g m <;> simp <;> omega

private theorem ltWordG {A : Set (Sig n)} (f g : Nat → Sig n) (m : Nat)
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

private def bitonicMerge (off : Nat) : Nat → Bool → List (Nat × Nat × Bool)
  | 0, _ => []
  | k + 1, asc =>
    let h := 2 ^ k
    let stage := (List.range h).map (fun i => (off + i, off + h + i, asc))
    stage ++ bitonicMerge off k asc ++ bitonicMerge (off + h) k asc

private def bitonicSort (off : Nat) : Nat → Bool → List (Nat × Nat × Bool)
  | 0, _ => []
  | k + 1, asc =>
    let h := 2 ^ k
    bitonicSort off k true ++ bitonicSort (off + h) k false ++ bitonicMerge off (k + 1) asc

private theorem bitonicMerge_length (off : Nat) : ∀ k asc,
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

private theorem bitonicSort_length (off : Nat) : ∀ k asc,
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

private theorem bitonicMerge_mem (off : Nat) : ∀ k asc c,
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

private theorem bitonicSort_mem (off : Nat) : ∀ k asc c,
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

private def swapBit (k1 k2 : Nat) (asc : Bool) : Bool :=
  if asc then decide (k2 < k1) else decide (k1 < k2)

private def applySwap {α : Type*} (u v : Nat) (sw : Bool) (st : Nat → α) : Nat → α :=
  fun idx =>
    if sw then
      if idx = u then st v else if idx = v then st u else st idx
    else st idx

private theorem applySwap_invol {α : Type*} (u v : Nat) (sw : Bool) (st : Nat → α) :
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

private theorem applySwap_comp {α β : Type*} (u v : Nat) (sw : Bool) (f : α → β) (st : Nat → α) :
    applySwap u v sw (fun idx => f (st idx)) = fun idx => f (applySwap u v sw st idx) := by
  funext idx
  simp only [applySwap]
  cases sw <;> simp only [Bool.false_eq_true, ↓reduceIte]
  by_cases h1 : idx = u
  · simp [h1]
  · by_cases h2 : idx = v
    · subst h2; simp [h1]
    · simp [h1, h2]

private def runNet {α : Type*} (key : α → Nat) : List (Nat × Nat × Bool) → (Nat → α) → (Nat → α)
  | [], st => st
  | (u, v, asc) :: rest, st =>
    let sw := swapBit (key (st u)) (key (st v)) asc
    runNet key rest (applySwap u v sw st)

private theorem runNet_append {α : Type*} (key : α → Nat) (n1 n2 : List (Nat × Nat × Bool)) (st : Nat → α) :
    runNet key (n1 ++ n2) st = runNet key n2 (runNet key n1 st) := by
  induction n1 generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, asc⟩
    simp only [List.cons_append, runNet]
    exact ih _

private def netSwaps {α : Type*} (key : α → Nat) : List (Nat × Nat × Bool) → (Nat → α) → List (Nat × Nat × Bool)
  | [], _ => []
  | (u, v, asc) :: rest, st =>
    let sw := swapBit (key (st u)) (key (st v)) asc
    (u, v, sw) :: netSwaps key rest (applySwap u v sw st)

private def replaySwaps {β : Type*} : List (Nat × Nat × Bool) → (Nat → β) → (Nat → β)
  | [], st => st
  | (u, v, sw) :: rest, st => replaySwaps rest (applySwap u v sw st)

private theorem replaySwaps_append {β : Type*} (s1 s2 : List (Nat × Nat × Bool)) (st : Nat → β) :
    replaySwaps (s1 ++ s2) st = replaySwaps s2 (replaySwaps s1 st) := by
  induction s1 generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, sw⟩
    simp only [List.cons_append, replaySwaps]
    exact ih _

private theorem replaySwaps_comp {α β : Type*} (sws : List (Nat × Nat × Bool)) (f : α → β) (st : Nat → α) :
    replaySwaps sws (fun idx => f (st idx)) = fun idx => f (replaySwaps sws st idx) := by
  induction sws generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, sw⟩
    simp only [replaySwaps]
    rw [applySwap_comp]
    exact ih _

private theorem replaySwaps_reverse_cancel {β : Type*} (sws : List (Nat × Nat × Bool)) (st : Nat → β) :
    replaySwaps sws.reverse (replaySwaps sws st) = st := by
  induction sws generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, sw⟩
    simp only [List.reverse_cons, replaySwaps, replaySwaps_append]
    rw [ih, applySwap_invol]

private theorem runNet_eq_replay {α : Type*} (key : α → Nat) (net : List (Nat × Nat × Bool)) (st : Nat → α) :
    runNet key net st = replaySwaps (netSwaps key net st) st := by
  induction net generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, asc⟩
    simp only [runNet, netSwaps, replaySwaps]
    exact ih _

private theorem runNet_unchanged {α : Type*} (key : α → Nat) (net : List (Nat × Nat × Bool))
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

private theorem runNet_mono_map {α : Type*} (key : α → Nat) (f : Nat → Bool)
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

private def IsBitonic (off len : Nat) (g : Nat → Bool) : Prop :=
  ∃ s e, s ≤ e ∧ e ≤ len ∧
    ((∀ i < len, g (off + i) = true ↔ s ≤ i ∧ i < e) ∨
     (∀ i < len, g (off + i) = false ↔ s ≤ i ∧ i < e))

private def IsSortedBool (off len : Nat) (asc : Bool) (g : Nat → Bool) : Prop :=
  ∀ i j, i ≤ j → j < len →
    if asc then (g (off + i) = true → g (off + j) = true)
    else (g (off + j) = true → g (off + i) = true)

private theorem runNet_bool_const (net : List (Nat × Nat × Bool)) (off len : Nat) (v : Bool)
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

private theorem stage_eval (off h : Nat) (asc : Bool) (g : Nat → Bool) :
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

private theorem bitonic_split_true (off h : Nat) (g : Nat → Bool) (hb : IsBitonic off (2 * h) g) :
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

private theorem bitonicMerge_sorted (off : Nat) : ∀ k asc (g : Nat → Bool),
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

private theorem sorted_asc_desc_bitonic (off h : Nat) (g : Nat → Bool)
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

private theorem bitonicSort_sorted_bool (off : Nat) : ∀ k asc (g : Nat → Bool),
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

private theorem bitonicSort_sorted {α : Type*} (key : α → Nat) (p : Nat) (st : Nat → α) :
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

private structure Rec (a b : Nat) where
  keyBit : Nat → Bool
  valBit : Fin b → Bool

private def recKey {a b : Nat} (r : Rec a b) : Nat :=
  bitsVal r.keyBit (a + 2)

private def netCircuit {n a b : Nat} {A : Set (Sig n)} (N : Nat)
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

private def scanStep {n b : Nat} (N : Nat)
    (st : (Fin n → Bool) → Nat → Rec a b) : Nat → (Fin n → Bool) → (Fin b → Bool) × (Nat → Fin b → Bool)
  | 0, _ => (fun _ => false, fun _ _ => false)
  | t + 1, x =>
    let prev := scanStep N st t x
    let isTab := !((st x t).keyBit (a + 1)) && !((st x t).keyBit 0)
    let cur' := fun j => if isTab then (st x t).valBit j else prev.1 j
    (cur', fun idx => if idx = t then cur' else prev.2 idx)

private theorem scanCircuit {n a b : Nat} {A : Set (Sig n)} (N : Nat)
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

private theorem replayCircuit {n b : Nat} {A : Set (Sig n)} (N : Nat)
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

private theorem log2_bound (a q : Nat) :
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

private theorem netSwaps_length {α : Type*} (key : α → Nat) (net : List (Nat × Nat × Bool)) (st : Nat → α) :
    (netSwaps key net st).length = net.length := by
  induction net generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, asc⟩
    simp [netSwaps, ih]

private theorem netSwaps_getD_uv {α : Type*} (key : α → Nat) (net : List (Nat × Nat × Bool)) (st : Nat → α) :
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

private theorem scanStep_answer {a b : Nat} (N : Nat) (st : Nat → Rec a b)
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

private theorem keyBits_val (a : Nat) (dummy tag : Bool) (addr : Nat) (haddr : addr < 2 ^ a) :
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

private theorem list_ofFn_flatten_getD {m k : Nat} (f : Fin m → Fin k → Bool)
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

private theorem list_ofFn_flatten_length {m k : Nat} (f : Fin m → Fin k → Bool) :
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

private theorem solve_049 (a b q : Nat) :
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

end PEqualNP.Outside.L_clb_049_aux

theorem PEqualNP.Outside.L_clb_049 : ∀ (a b q : ℕ),
  let words := 2 ^ a
  let I := words * b + q * a
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit)
    (outBit : Fin q → Fin b → Fin (I + C.size)),
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack I C ∧ C.output < I + C.size ∧
    C.size ≤ 128 * (words + q) * (a + b + Nat.log2 (q + 1) + 3) ^ 3 ∧
    ∀ (table : Fin words → Fin b → Bool) (address : Fin q → Fin words),
      let x := (List.ofFn (fun j : Fin words => List.ofFn (table j))).flatten ++
        (List.ofFn (fun j : Fin q =>
          List.ofFn (fun i : Fin a => (address j).val.testBit i.val))).flatten
      ∀ (j : Fin q) (i : Fin b),
        (C.wires x).getD (outBit j i).val false = table (address j) i := by
  intro a b q
  exact PEqualNP.Outside.L_clb_049_aux.Lookup049.solve_049 a b q
