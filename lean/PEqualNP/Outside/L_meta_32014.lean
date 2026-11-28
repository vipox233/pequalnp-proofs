import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_32014_aux
namespace GB

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)

abbrev Sig (n : Nat) := (Fin n → Bool) → Bool

def Shape (g : Gate) : Prop :=
  g.inputs.length ≤ 2 ∧ (g.op = .and ∨ g.op = .or ∨ (g.op = .not ∧ g.inputs.length = 1))

def Sched (n : Nat) (J : Set Nat) (k : Nat) (S : Set (Sig n)) : Prop :=
  ∃ gs : List Gate, gs.length = k ∧ ReadsBack n ⟨gs, 0⟩ ∧ (∀ g ∈ gs, Shape g) ∧
    (∀ g ∈ gs, ∀ i ∈ g.inputs, i < n → i ∈ J) ∧
    ∀ a ∈ S, ∃ i : Nat, i < n + k ∧ (i < n → i ∈ J) ∧
      ∀ x : Fin n → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = a x

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

theorem start (n : Nat) (J : Set Nat) :
    Sched n J 0 {f | ∃ i : Fin n, i.val ∈ J ∧ f = fun v => v i} := by
  refine ⟨[], rfl, ?_, ?_, ?_, ?_⟩
  · simp [ReadsBack]
  · simp
  · simp
  · rintro a ⟨i, hi, rfl⟩
    refine ⟨i.val, by simp, fun _ => hi, fun x => ?_⟩
    change (List.ofFn x).getD i.val false = x i
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

theorem restrict {n k : Nat} {J : Set Nat} {S T : Set (Sig n)}
    (h : Sched n J k S) (hsub : T ⊆ S) : Sched n J k T := by
  obtain ⟨gs, hs, hr, hf, hj, hw⟩ := h
  exact ⟨gs, hs, hr, hf, hj, fun a ha => hw a (hsub ha)⟩

theorem realizeDeps {n k : Nat} {J : Set Nat} {S : Set (Sig n)} {gs : List Gate}
    (hw : ∀ a ∈ S, ∃ i : Nat, i < n + k ∧ (i < n → i ∈ J) ∧
      ∀ x : Fin n → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = a x)
    (deps : List (Sig n)) (hdeps : ∀ a ∈ deps, a ∈ S) :
    ∃ is : List Nat, is.length = deps.length ∧ (∀ i ∈ is, i < n + k ∧ (i < n → i ∈ J)) ∧
      ∀ x : Fin n → Bool,
        is.map (fun i => ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false) =
          deps.map (fun a => a x) := by
  induction deps with
  | nil => exact ⟨[], rfl, by simp, by simp⟩
  | cons a deps ih =>
    obtain ⟨i, hi, hiJ, hval⟩ := hw a (hdeps a List.mem_cons_self)
    obtain ⟨is, hlen, hbound, hvals⟩ := ih (fun b hb => hdeps b (List.mem_cons_of_mem a hb))
    refine ⟨i :: is, by simp [hlen], ?_, fun x => ?_⟩
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact ⟨hi, hiJ⟩
      · exact hbound j hj
    · simp only [List.map_cons, hval x, hvals x]

theorem push {n k : Nat} {J : Set Nat} {S : Set (Sig n)}
    (h : Sched n J k S) (op : GateOp) (deps : List (Sig n)) (out : Sig n)
    (hop : op = .and ∨ op = .or ∨ (op = .not ∧ deps.length = 1))
    (hlen : deps.length ≤ 2) (hdeps : ∀ a ∈ deps, a ∈ S)
    (hval : ∀ x, out x = op.eval (deps.map fun a => a x)) :
    Sched n J (k + 1) (insert out S) := by
  obtain ⟨gs, hgs, hr, hf, hj, hw⟩ := h
  obtain ⟨is, his, hbound, hvalues⟩ := realizeDeps hw deps hdeps
  have hlength (x : Fin n → Bool) :
      ((Circuit.mk gs 0).wires (List.ofFn x)).length = n + k := by
    rw [wireLength]
    simpa using congrArg (n + ·) hgs
  have hsnoc (x : Fin n → Bool) :
      (Circuit.mk (gs ++ [(Gate.mk op is)]) 0).wires (List.ofFn x) =
        (Circuit.mk gs 0).wires (List.ofFn x) ++ [out x] := by
    simp only [Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (Circuit.mk gs 0).wires (List.ofFn x) ++
      [op.eval (is.map fun i => ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false)] =
        (Circuit.mk gs 0).wires (List.ofFn x) ++ [out x]
    rw [hvalues x, hval x]
  refine ⟨gs ++ [(Gate.mk op is)], by simp [hgs], ?_, ?_, ?_, ?_⟩
  · intro j hj i hi
    change j < (gs ++ [(Gate.mk op is)]).length at hj
    change i ∈ ((gs ++ [(Gate.mk op is)]).getD j ⟨GateOp.or, []⟩).inputs at hi
    by_cases hj' : j < gs.length
    · rw [List.getD_append _ _ _ _ hj'] at hi
      exact hr j hj' i hi
    · have heq : j = gs.length := by
        simp only [List.length_append, List.length_singleton] at hj
        omega
      subst j
      rw [List.getD_append_right _ _ _ _ le_rfl] at hi
      have hi' : i ∈ is := by simpa using hi
      simpa [hgs] using (hbound i hi').1
  · intro g' hg'
    rcases List.mem_append.mp hg' with hg' | hg'
    · exact hf g' hg'
    · have heq : g' = (Gate.mk op is) := List.mem_singleton.mp hg'
      subst heq
      refine ⟨by show is.length ≤ 2; rw [his]; exact hlen, ?_⟩
      rcases hop with h1 | h1 | ⟨h1, h2⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr ⟨h1, by show is.length = 1; rw [his]; exact h2⟩)
  · intro g' hg' i hi hin
    rcases List.mem_append.mp hg' with hg' | hg'
    · exact hj g' hg' i hi hin
    · have heq : g' = (Gate.mk op is) := List.mem_singleton.mp hg'
      subst heq
      exact (hbound i hi).2 hin
  · intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · refine ⟨n + k, by omega, fun h => by omega, fun x => ?_⟩
      rw [hsnoc x, List.getD_append_right _ _ _ _ (by simp [hlength x])]
      simp [hlength x]
    · obtain ⟨i, hi, hiJ, hval'⟩ := hw a ha
      refine ⟨i, by omega, hiJ, fun x => ?_⟩
      rw [hsnoc x, List.getD_append _ _ _ _ (by simpa [hlength x] using hi), hval' x]

def Build {n : Nat} (J : Set Nat) (A B : Set (Sig n)) (b : Nat) : Prop :=
  ∀ (m : Nat) (S : Set (Sig n)), Sched n J m S → A ⊆ S → ∃ c ≤ b, Sched n J (m + c) (S ∪ B)

variable {n : Nat} {J : Set Nat}

theorem idle {A B : Set (Sig n)} (h : B ⊆ A) : Build J A B 0 := by
  intro m S HS hA
  refine ⟨0, Nat.le_refl _, ?_⟩
  simpa [Set.union_eq_left.mpr (h.trans hA)] using HS

theorem relax {A B C D : Set (Sig n)} {b d : Nat}
    (H : Build J A B b) (hA : A ⊆ C) (hB : D ⊆ B) (h : b ≤ d) : Build J C D d := by
  intro m S HS hC
  obtain ⟨c, hc, HS'⟩ := H _ _ HS (hA.trans hC)
  exact ⟨c, hc.trans h, restrict HS' (Set.union_subset_union le_rfl hB)⟩

theorem seq {A B C : Set (Sig n)} {b c : Nat}
    (H : Build J A B b) (K : Build J (A ∪ B) C c) : Build J A (B ∪ C) (b + c) := by
  intro m S HS hA
  obtain ⟨d, hd, K1⟩ := H _ _ HS hA
  obtain ⟨e, he, K2⟩ := K _ _ K1 (Set.union_subset_union hA le_rfl)
  exact ⟨d + e, Nat.add_le_add hd he, by simpa [Nat.add_assoc, Set.union_assoc] using K2⟩

theorem one {A : Set (Sig n)} (op : GateOp) (deps : List (Sig n))
    (hop : op = .and ∨ op = .or ∨ (op = .not ∧ deps.length = 1)) (hlen : deps.length ≤ 2)
    (hd : ∀ g ∈ deps, g ∈ A) (f : Sig n)
    (hv : ∀ x, f x = op.eval (deps.map fun g => g x)) : Build J A {f} 1 := by
  intro m S HS hA
  refine ⟨1, le_rfl, ?_⟩
  have h := push HS op deps f hop hlen (fun g hg => hA (hd g hg)) hv
  rw [Set.insert_eq] at h
  exact restrict h (by intro g hg; exact hg.elim Or.inr Or.inl)

def an (f g : Sig n) : Sig n := fun x => f x && g x
def orr (f g : Sig n) : Sig n := fun x => f x || g x
def nt (f : Sig n) : Sig n := fun x => !f x

theorem andG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) : Build J A {an f g} 1 :=
  one .and [f, g] (Or.inl rfl) (by simp) (by simpa using And.intro hf hg) _ (by simp [GateOp.eval, an])

theorem orG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) : Build J A {orr f g} 1 :=
  one .or [f, g] (Or.inr (Or.inl rfl)) (by simp) (by simpa using And.intro hf hg) _ (by simp [GateOp.eval, orr])

theorem notG {A : Set (Sig n)} {f : Sig n} (hf : f ∈ A) : Build J A {nt f} 1 :=
  one .not [f] (Or.inr (Or.inr ⟨rfl, rfl⟩)) (by simp) (by simpa using hf) _ (by simp [GateOp.eval, nt])

theorem constG {A : Set (Sig n)} (b : Bool) : Build J A {fun _ => b} 1 := by
  cases b
  · exact one .or [] (Or.inr (Or.inl rfl)) (by simp) (by simp) _ (by intro; rfl)
  · exact one .and [] (Or.inl rfl) (by simp) (by simp) _ (by intro; rfl)

theorem muxG {A : Set (Sig n)} {sw nsw t f : Sig n}
    (hsw : sw ∈ A) (hnsw : nsw ∈ A) (ht : t ∈ A) (hf : f ∈ A)
    (hneg : ∀ x, nsw x = !(sw x)) :
    Build J A {fun x => if sw x then t x else f x} 3 := by
  have he : (fun x => if sw x then t x else f x) = orr (an sw t) (an nsw f) := by
    funext x
    simp only [orr, an, hneg x]
    cases sw x <;> cases t x <;> cases f x <;> rfl
  rw [he]
  have h1 := andG (J := J) hsw ht
  have h2 := andG (J := J) (A := A ∪ {an sw t}) (Or.inl hnsw) (Or.inl hf)
  have h3 := orG (J := J) (A := A ∪ ({an sw t} ∪ {an nsw f}))
    (f := an sw t) (g := an nsw f) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
  exact relax (seq (seq h1 h2) h3) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl

theorem famBuild {A : Set (Sig n)} (B : Nat → Set (Sig n)) (c : Nat) :
    ∀ m, (∀ r < m, Build J A (B r) c) → Build J A {f | ∃ r < m, f ∈ B r} (m * c)
  | 0, _ => relax (idle (A := A) (B := ∅) (by simp)) le_rfl (by rintro f ⟨r, hr, -⟩; omega) (by simp)
  | m + 1, H => by
    have h1 := famBuild B c m (fun r hr => H r (by omega))
    have h2 := relax (H m (by omega)) (C := A ∪ {f | ∃ r < m, f ∈ B r}) Set.subset_union_left le_rfl le_rfl
    refine relax (seq h1 h2) le_rfl ?_ (by rw [Nat.succ_mul])
    rintro f ⟨r, hr, hf⟩
    by_cases hrm : r = m
    · subst hrm; exact Or.inr hf
    · exact Or.inl ⟨r, by omega, hf⟩

end GB
end PEqualNP.Outside.L_meta_32014_aux

namespace PEqualNP.Outside.L_meta_32014_aux
namespace Loss

variable {N : Nat} [NeZero N]

def lossF (H : Fin N → Fin N → Bool) (U : Finset (Fin N)) : Nat :=
  ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => H z.1 z.2 ≠ decide (z.2 - z.1 ∈ U))).card

theorem shift_count (U : Finset (Fin N)) :
    ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => z.2 - z.1 ∈ U)).card = N * U.card := by
  have h : ((Finset.univ : Finset (Fin N)) ×ˢ U).card = N * U.card := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
  rw [← h]
  symm
  apply Finset.card_nbij' (fun p : Fin N × Fin N => (p.1, p.1 + p.2)) (fun z : Fin N × Fin N => (z.1, z.2 - z.1))
  · intro p hp
    simp only [Finset.coe_product, Finset.coe_univ, Set.mem_prod, Set.mem_univ, true_and, Finset.mem_coe] at hp
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, add_sub_cancel_left]
    exact hp
  · intro z hz
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hz
    simp only [Finset.coe_product, Finset.coe_univ, Set.mem_prod, Set.mem_univ, true_and, Finset.mem_coe]
    exact hz
  · intro p _
    simp
  · intro z _
    simp

theorem loss_zero (H : Fin N → Fin N → Bool) (U : Finset (Fin N)) (h : ∀ x y, H x y = false) :
    lossF H U = N * U.card := by
  rw [← shift_count U]
  unfold lossF
  congr 1
  apply Finset.filter_congr
  intro z _
  rw [h]
  simp

theorem loss_one (H : Fin N → Fin N → Bool) (U : Finset (Fin N)) (c : Fin N × Fin N)
    (h : ∀ x y, H x y = true ↔ (x, y) = c) :
    (c.2 - c.1 ∈ U → lossF H U + 1 = N * U.card) ∧ (c.2 - c.1 ∉ U → lossF H U = N * U.card + 1) := by
  classical
  have hmis : ∀ z : Fin N × Fin N, (H z.1 z.2 ≠ decide (z.2 - z.1 ∈ U)) ↔
      ((z = c ∧ z.2 - z.1 ∉ U) ∨ (z ≠ c ∧ z.2 - z.1 ∈ U)) := by
    intro z
    by_cases hz : z = c
    · have : H z.1 z.2 = true := (h z.1 z.2).mpr hz
      rw [this]
      by_cases hu : z.2 - z.1 ∈ U <;> simp [hz]
    · have : H z.1 z.2 = false := by
        by_contra hne
        exact hz ((h z.1 z.2).mp (by simpa using hne))
      rw [this]
      by_cases hu : z.2 - z.1 ∈ U <;> simp [hz, hu]
  constructor
  · intro hc
    have hset : (Finset.univ : Finset (Fin N × Fin N)).filter (fun z => H z.1 z.2 ≠ decide (z.2 - z.1 ∈ U)) =
        ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => z.2 - z.1 ∈ U)).erase c := by
      ext z
      rw [Finset.mem_filter, Finset.mem_erase, Finset.mem_filter, hmis]
      constructor
      · rintro ⟨-, (⟨hz, hn⟩ | ⟨hz, hu⟩)⟩
        · exact absurd (hz ▸ hc) hn
        · exact ⟨hz, Finset.mem_univ _, hu⟩
      · rintro ⟨hz, -, hu⟩
        exact ⟨Finset.mem_univ _, Or.inr ⟨hz, hu⟩⟩
    unfold lossF
    rw [hset, Finset.card_erase_of_mem (by simp [hc]), shift_count]
    have hpos : 0 < ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => z.2 - z.1 ∈ U)).card :=
      Finset.card_pos.mpr ⟨c, by simp [hc]⟩
    rw [shift_count] at hpos
    omega
  · intro hc
    have hset : (Finset.univ : Finset (Fin N × Fin N)).filter (fun z => H z.1 z.2 ≠ decide (z.2 - z.1 ∈ U)) =
        insert c ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => z.2 - z.1 ∈ U)) := by
      ext z
      rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_filter, hmis]
      constructor
      · rintro ⟨-, (⟨hz, hn⟩ | ⟨hz, hu⟩)⟩
        · exact Or.inl hz
        · exact Or.inr ⟨Finset.mem_univ _, hu⟩
      · rintro (hz | ⟨-, hu⟩)
        · exact ⟨Finset.mem_univ _, Or.inl ⟨hz, hz ▸ hc⟩⟩
        · refine ⟨Finset.mem_univ _, Or.inr ⟨?_, hu⟩⟩
          intro hz; exact hc (hz ▸ hu)
    unfold lossF
    rw [hset, Finset.card_insert_of_notMem (by simp [hc]), shift_count]

theorem at_most_one (H : Fin N → Fin N → Bool) (h : lossF H ∅ ≤ 1) :
    (∀ x y, H x y = false) ∨ ∃ c : Fin N × Fin N, ∀ x y, H x y = true ↔ (x, y) = c := by
  have hset : lossF H ∅ = ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => H z.1 z.2 = true)).card := by
    unfold lossF
    congr 1
    apply Finset.filter_congr
    intro z _
    simp
  rw [hset, Finset.card_le_one] at h
  by_cases hall : ∀ x y, H x y = false
  · exact Or.inl hall
  · right
    obtain ⟨x0, hx0⟩ := not_forall.mp hall
    obtain ⟨y0, h0⟩ := not_forall.mp hx0
    have h0' : H x0 y0 = true := by simpa using h0
    refine ⟨(x0, y0), fun x y => ⟨fun hxy => ?_, fun hxy => ?_⟩⟩
    · exact h (x, y) (by simp [hxy]) (x0, y0) (by simp [h0'])
    · rw [Prod.mk.injEq] at hxy
      rw [hxy.1, hxy.2]; exact h0'

end Loss
end PEqualNP.Outside.L_meta_32014_aux

namespace PEqualNP.Outside.L_meta_32014_aux
namespace Ext

open PEqualNP.CircuitLowerBounds GB
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)

def inp {N h : Nat} (x y : Fin N) (w : Fin h → Bool) : Fin (N + N + h) → Bool :=
  fun k => (PEqualNP.Represents.oneEach x y ++ List.ofFn w).getD k.val false

theorem inp_len {N h : Nat} (x y : Fin N) (w : Fin h → Bool) :
    (PEqualNP.Represents.oneEach x y ++ List.ofFn w).length = N + N + h := by
  simp [PEqualNP.Represents.oneEach]; omega

theorem ofFn_inp {N h : Nat} (x y : Fin N) (w : Fin h → Bool) :
    List.ofFn (inp x y w) = PEqualNP.Represents.oneEach x y ++ List.ofFn w := by
  apply List.ext_getElem
  · rw [inp_len]; simp
  · intro i h1 h2
    rw [List.getElem_ofFn]
    simp only [inp]
    rw [List.getD_eq_getElem _ _ h2]

theorem inp_row {N h : Nat} (x y : Fin N) (w : Fin h → Bool) (x' : Fin N) (hk : x'.val < N + N + h) :
    inp x y w ⟨x'.val, hk⟩ = decide (x' = x) := by
  simp only [inp, PEqualNP.Represents.oneEach]
  rw [List.append_assoc, List.getD_append _ _ _ _ (by simp)]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

theorem inp_col {N h : Nat} (x y : Fin N) (w : Fin h → Bool) (y' : Fin N) (hk : N + y'.val < N + N + h) :
    inp x y w ⟨N + y'.val, hk⟩ = decide (y' = y) := by
  simp only [inp, PEqualNP.Represents.oneEach]
  rw [List.getD_append _ _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp)]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  simp

theorem inp_seed {N h : Nat} (x y : Fin N) (w : Fin h → Bool) (i : Fin h) (hk : N + N + i.val < N + N + h) :
    inp x y w ⟨N + N + i.val, hk⟩ = w i := by
  simp only [inp, PEqualNP.Represents.oneEach]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  simp

def JJ {N : Nat} (R S : Finset (Fin N)) : Set Nat :=
  {j | (∀ x : Fin N, j = x.val → x ∈ R) ∧ (∀ y : Fin N, j = N + y.val → y ∈ S)}

def A0 {N : Nat} (h : Nat) (R S : Finset (Fin N)) : Set (Sig (N + N + h)) :=
  {f | ∃ i : Fin (N + N + h), i.val ∈ JJ R S ∧ f = fun v => v i}

theorem row_mem {N : Nat} (h : Nat) (R S : Finset (Fin N)) (x : Fin N) (hx : x ∈ R) :
    (fun v : Fin (N + N + h) → Bool => v ⟨x.val, by omega⟩) ∈ A0 h R S := by
  refine ⟨⟨x.val, by omega⟩, ⟨fun x' hx' => ?_, fun y hy => ?_⟩, rfl⟩
  · have : x = x' := Fin.ext hx'
    rw [← this]; exact hx
  · simp only at hy; omega

theorem col_mem {N : Nat} (h : Nat) (R S : Finset (Fin N)) (y : Fin N) (hy : y ∈ S) :
    (fun v : Fin (N + N + h) → Bool => v ⟨N + y.val, by omega⟩) ∈ A0 h R S := by
  refine ⟨⟨N + y.val, by omega⟩, ⟨fun x' hx' => ?_, fun y' hy' => ?_⟩, rfl⟩
  · simp only at hx'; omega
  · have : y = y' := Fin.ext (by simp only at hy'; omega)
    rw [← this]; exact hy

theorem seed_mem {N : Nat} (h : Nat) (R S : Finset (Fin N)) (i : Fin h) :
    (fun v : Fin (N + N + h) → Bool => v ⟨N + N + i.val, by omega⟩) ∈ A0 h R S := by
  refine ⟨⟨N + N + i.val, by omega⟩, ⟨fun x' hx' => ?_, fun y' hy' => ?_⟩, rfl⟩
  · simp only at hx'; omega
  · simp only at hy'; omega

theorem extract {N h : Nat} (R S : Finset (Fin N)) (B : Set (Sig (N + N + h))) (b : Nat)
    (out : Sig (N + N + h)) (HB : Build (JJ R S) (A0 h R S) B b) (hout : out ∈ A0 h R S ∪ B) :
    ∃ C : Circuit, (ReadsBack (N + N + h) C ∧ C.output < N + N + h + C.size ∧
        ∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
          (g.op = .and ∨ g.op = .or ∨ (g.op = .not ∧ g.inputs.length = 1))) ∧
      ((∀ x : Fin N, (C.output = x.val ∨ ∃ g ∈ C.gates, x.val ∈ g.inputs) → x ∈ R) ∧
        (∀ y : Fin N, (C.output = N + y.val ∨ ∃ g ∈ C.gates, N + y.val ∈ g.inputs) → y ∈ S)) ∧
      C.size ≤ b ∧
      ∀ (w : Fin h → Bool) (x y : Fin N),
        C.eval (PEqualNP.Represents.oneEach x y ++ List.ofFn w) = out (inp x y w) := by
  obtain ⟨c, hc, gs, hgs, hr, hf, hj, hw⟩ := HB 0 (A0 h R S) (start (N + N + h) (JJ R S)) le_rfl
  obtain ⟨io, hio, hioJ, hval⟩ := hw out hout
  have hsize : (Circuit.mk gs io).size = 0 + c := hgs
  refine ⟨⟨gs, io⟩, ⟨hr, by rw [hsize]; exact hio, fun g hg => hf g hg⟩, ⟨?_, ?_⟩, by rw [hsize]; omega, ?_⟩
  · rintro x (hx | ⟨g, hg, hx⟩)
    · have hx' : io = x.val := hx
      exact (hioJ (by omega)).1 x hx'
    · exact (hj g hg _ hx (by omega)).1 x rfl
  · rintro y (hy | ⟨g, hg, hy⟩)
    · have hy' : io = N + y.val := hy
      exact (hioJ (by omega)).2 y hy'
    · exact (hj g hg _ hy (by omega)).2 y rfl
  · intro w x y
    show ((Circuit.mk gs io).wires (PEqualNP.Represents.oneEach x y ++ List.ofFn w)).getD io false = _
    rw [← ofFn_inp x y w]
    exact hval (inp x y w)

end Ext
end PEqualNP.Outside.L_meta_32014_aux

namespace PEqualNP.Outside.L_meta_32014_aux
namespace Mux

open PEqualNP.CircuitLowerBounds GB Ext

def bitsVal (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | m + 1 => bitsVal f m + if f m then 2 ^ m else 0

theorem bitsVal_lt (f : Nat → Bool) : ∀ m, bitsVal f m < 2 ^ m
  | 0 => by simp [bitsVal]
  | m + 1 => by
    have ih := bitsVal_lt f m
    simp only [bitsVal, Nat.pow_succ]
    by_cases h : f m = true <;> simp [h] <;> omega

theorem bitsVal_testBit (f : Nat → Bool) : ∀ m i, i < m → (bitsVal f m).testBit i = f i
  | 0, _, hi => by omega
  | m + 1, i, hi => by
    simp only [bitsVal]
    have hlt := bitsVal_lt f m
    by_cases him : i = m
    · subst him
      by_cases hfm : f i = true
      · simp only [hfm, if_true]
        rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]
        rfl
      · have hfm' : f i = false := by simpa using hfm
        simp only [hfm', Bool.false_eq_true, if_false, Nat.add_zero]
        exact Nat.testBit_lt_two_pow hlt
    · have him' : i < m := by omega
      by_cases hfm : f m = true
      · simp only [hfm, if_true]
        rw [Nat.add_comm, Nat.testBit_two_pow_add_gt him']
        exact bitsVal_testBit f m i him'
      · have hfm' : f m = false := by simpa using hfm
        simp only [hfm', Bool.false_eq_true, if_false, Nat.add_zero]
        exact bitsVal_testBit f m i him'

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

theorem muxTree {n : Nat} {J : Set Nat} {A : Set (Sig n)} (sel : Nat → Sig n) :
    ∀ (a : Nat) (leaf : Nat → Sig n), (∀ i < a, sel i ∈ A) → (∀ i < a, nt (sel i) ∈ A) →
      (∀ m < 2 ^ a, leaf m ∈ A) →
      Build J A {fun v => leaf (bitsVal (fun i => sel i v) a) v} (3 * (2 ^ a - 1))
  | 0, leaf, _, _, hl =>
    relax (idle (J := J) (A := A) (B := {fun v => leaf (bitsVal (fun i => sel i v) 0) v})
      (Set.singleton_subset_iff.mpr (hl 0 (by simp)))) le_rfl le_rfl (by simp)
  | a + 1, leaf, hs, hn, hl => by
    have hp := Nat.two_pow_pos a
    have h1 := muxTree (J := J) (A := A) sel a leaf (fun i hi => hs i (by omega)) (fun i hi => hn i (by omega))
      (fun m hm => hl m (by rw [Nat.pow_succ]; omega))
    have h2 := muxTree (J := J) (A := A) sel a (fun m => leaf (m + 2 ^ a)) (fun i hi => hs i (by omega))
      (fun i hi => hn i (by omega)) (fun m hm => hl (m + 2 ^ a) (by rw [Nat.pow_succ]; omega))
    have h2' := relax h2 (C := A ∪ {fun v => leaf (bitsVal (fun i => sel i v) a) v})
      Set.subset_union_left le_rfl le_rfl
    have h3 := muxG (J := J)
      (A := A ∪ ({fun v => leaf (bitsVal (fun i => sel i v) a) v} ∪
        {fun v => leaf (bitsVal (fun i => sel i v) a + 2 ^ a) v}))
      (sw := sel a) (nsw := nt (sel a)) (t := fun v => leaf (bitsVal (fun i => sel i v) a + 2 ^ a) v)
      (f := fun v => leaf (bitsVal (fun i => sel i v) a) v)
      (Or.inl (hs a (by omega))) (Or.inl (hn a (by omega))) (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl))
      (fun _ => rfl)
    have e : (fun v => leaf (bitsVal (fun i => sel i v) (a + 1)) v) =
        fun v => if sel a v then leaf (bitsVal (fun i => sel i v) a + 2 ^ a) v
          else leaf (bitsVal (fun i => sel i v) a) v := by
      funext v
      simp only [bitsVal]
      by_cases hsv : sel a v = true <;> simp [hsv]
    rw [e]
    refine relax (seq (seq h1 h2') h3) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) ?_
    rw [Nat.pow_succ]; omega

end Mux
end PEqualNP.Outside.L_meta_32014_aux

namespace PEqualNP.Outside.L_meta_32014_aux
namespace Sq

open PEqualNP.CircuitLowerBounds GB Ext Mux
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)

def rowOf {N : Nat} [NeZero N] (m : Nat) : Fin N := -(Fin.ofNat N m)
def colOf {N : Nat} [NeZero N] (r m : Nat) : Fin N := Fin.ofNat N (m * r)
def wbit {h : Nat} (w : Fin h → Bool) (i : Nat) : Bool := if hi : i < h then w ⟨i, hi⟩ else false
def sdS (N h : Nat) (i : Nat) : Sig (N + N + h) :=
  fun v => if hi : i < h then v ⟨N + N + i, by omega⟩ else false

theorem sdS_inp {N h : Nat} (x y : Fin N) (w : Fin h → Bool) (i : Nat) :
    sdS N h i (inp x y w) = wbit w i := by
  unfold sdS wbit
  split_ifs with hi
  · exact inp_seed x y w ⟨i, hi⟩ (by omega)
  · rfl

theorem sdS_mem {N : Nat} (h : Nat) (R S : Finset (Fin N)) (i : Nat) (hi : i < h) :
    sdS N h i ∈ A0 h R S := by
  have e : sdS N h i = fun v : Fin (N + N + h) → Bool => v ⟨N + N + (⟨i, hi⟩ : Fin h).val, by omega⟩ := by
    funext v; simp [sdS, hi]
  rw [e]; exact seed_mem h R S ⟨i, hi⟩

theorem build3b (N a : Nat) [NeZero N] :
    ∃ C : Circuit, (ReadsBack (N + N + 2 * a) C ∧ C.output < N + N + 2 * a + C.size ∧
        ∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
          (g.op = .and ∨ g.op = .or ∨ (g.op = .not ∧ g.inputs.length = 1))) ∧
      ((∀ x : Fin N, (C.output = x.val ∨ ∃ g ∈ C.gates, x.val ∈ g.inputs) →
          x ∈ (Finset.range (2 ^ a)).image (rowOf (N := N))) ∧
        (∀ y : Fin N, (C.output = N + y.val ∨ ∃ g ∈ C.gates, N + y.val ∈ g.inputs) →
          y ∈ (Finset.range (2 ^ a)).image (colOf (N := N) (2 ^ a)))) ∧
      C.size ≤ 6 * (2 ^ a - 1) + 2 * a + 1 ∧
      ∀ (w : Fin (2 * a) → Bool) (x y : Fin N),
        C.eval (PEqualNP.Represents.oneEach x y ++ List.ofFn w) =
          (decide (rowOf (bitsVal (wbit w) a) = x) &&
            decide (colOf (2 ^ a) (bitsVal (fun i => wbit w (a + i)) a) = y)) := by
  generalize hR : (Finset.range (2 ^ a)).image (rowOf (N := N)) = R
  generalize hS : (Finset.range (2 ^ a)).image (colOf (N := N) (2 ^ a)) = S
  have HN : Build (JJ R S) (A0 (2 * a) R S)
      {f | ∃ i < 2 * a, f ∈ ({nt (sdS N (2 * a) i)} : Set (Sig (N + N + 2 * a)))} (2 * a * 1) :=
    famBuild (fun i => {nt (sdS N (2 * a) i)}) 1 (2 * a) (fun i hi => notG (sdS_mem (2 * a) R S i hi))
  have hleafR : ∀ m < 2 ^ a, (fun v : Fin (N + N + 2 * a) → Bool => v ⟨(rowOf (N := N) m).val, by omega⟩) ∈
      A0 (2 * a) R S := by
    intro m hm
    exact row_mem (2 * a) R S _ (by rw [← hR]; exact Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr hm, rfl⟩)
  have hleafC : ∀ m < 2 ^ a, (fun v : Fin (N + N + 2 * a) → Bool => v ⟨N + (colOf (N := N) (2 ^ a) m).val, by omega⟩) ∈
      A0 (2 * a) R S := by
    intro m hm
    exact col_mem (2 * a) R S _ (by rw [← hS]; exact Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr hm, rfl⟩)
  have HR := muxTree (J := JJ R S)
    (A := A0 (2 * a) R S ∪ {f | ∃ i < 2 * a, f ∈ ({nt (sdS N (2 * a) i)} : Set (Sig (N + N + 2 * a)))})
    (sdS N (2 * a)) a (fun m v => v ⟨(rowOf (N := N) m).val, by omega⟩)
    (fun i hi => Or.inl (sdS_mem (2 * a) R S i (by omega))) (fun i hi => Or.inr ⟨i, by omega, rfl⟩)
    (fun m hm => Or.inl (hleafR m hm))
  have HC := muxTree (J := JJ R S)
    (A := A0 (2 * a) R S ∪ ({f | ∃ i < 2 * a, f ∈ ({nt (sdS N (2 * a) i)} : Set (Sig (N + N + 2 * a)))} ∪
      {fun v => (fun (m : Nat) (v : Fin (N + N + 2 * a) → Bool) => v ⟨(rowOf (N := N) m).val, by omega⟩)
        (bitsVal (fun i => sdS N (2 * a) i v) a) v}))
    (fun i => sdS N (2 * a) (a + i)) a (fun m v => v ⟨N + (colOf (N := N) (2 ^ a) m).val, by omega⟩)
    (fun i hi => Or.inl (sdS_mem (2 * a) R S (a + i) (by omega)))
    (fun i hi => Or.inr (Or.inl ⟨a + i, by omega, rfl⟩))
    (fun m hm => Or.inl (hleafC m hm))
  have HA := andG (J := JJ R S)
    (A := A0 (2 * a) R S ∪ (({f | ∃ i < 2 * a, f ∈ ({nt (sdS N (2 * a) i)} : Set (Sig (N + N + 2 * a)))} ∪
      {fun v => (fun (m : Nat) (v : Fin (N + N + 2 * a) → Bool) => v ⟨(rowOf (N := N) m).val, by omega⟩)
        (bitsVal (fun i => sdS N (2 * a) i v) a) v}) ∪
      {fun v => (fun (m : Nat) (v : Fin (N + N + 2 * a) → Bool) => v ⟨N + (colOf (N := N) (2 ^ a) m).val, by omega⟩)
        (bitsVal (fun i => sdS N (2 * a) (a + i) v) a) v}))
    (f := fun v => (fun (m : Nat) (v : Fin (N + N + 2 * a) → Bool) => v ⟨(rowOf (N := N) m).val, by omega⟩)
        (bitsVal (fun i => sdS N (2 * a) i v) a) v)
    (g := fun v => (fun (m : Nat) (v : Fin (N + N + 2 * a) → Bool) => v ⟨N + (colOf (N := N) (2 ^ a) m).val, by omega⟩)
        (bitsVal (fun i => sdS N (2 * a) (a + i) v) a) v)
    (Or.inr (Or.inl (Or.inr rfl))) (Or.inr (Or.inr rfl))
  have Hall := seq (seq (seq HN HR) HC) HA
  obtain ⟨C, hlegal, hnamed, hsize, heval⟩ := extract R S _ _ _ Hall (Or.inr (Or.inr rfl))
  refine ⟨C, hlegal, hnamed, by omega, fun w x y => ?_⟩
  rw [heval]
  simp only [an]
  have e1 : bitsVal (fun i => sdS N (2 * a) i (inp x y w)) a = bitsVal (wbit w) a :=
    bitsVal_congr _ _ a (fun i _ => sdS_inp x y w i)
  have e2 : bitsVal (fun i => sdS N (2 * a) (a + i) (inp x y w)) a = bitsVal (fun i => wbit w (a + i)) a :=
    bitsVal_congr _ _ a (fun i _ => sdS_inp x y w (a + i))
  rw [e1, e2, inp_row, inp_col]

end Sq
end PEqualNP.Outside.L_meta_32014_aux

namespace PEqualNP.Outside.L_meta_32014_aux
namespace Dec

open PEqualNP.CircuitLowerBounds GB Ext Mux Sq
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)

theorem chainOr {n : Nat} {J : Set Nat} {A : Set (Sig n)} (f : Nat → Sig n) (hfalse : (fun _ => false) ∈ A) :
    ∀ m, (∀ r < m, f r ∈ A) → Build J A {fun v => (List.range m).any (fun r => f r v)} m
  | 0, _ => by
    have e : (fun v : Fin n → Bool => (List.range 0).any (fun r => f r v)) = fun _ => false := by
      funext v; simp
    rw [e]
    exact idle (Set.singleton_subset_iff.mpr hfalse)
  | m + 1, H => by
    have h1 := chainOr (J := J) f hfalse m (fun r hr => H r (by omega))
    have h2 := orG (J := J) (A := A ∪ {fun v => (List.range m).any (fun r => f r v)})
      (f := fun v => (List.range m).any (fun r => f r v)) (g := f m) (Or.inr rfl) (Or.inl (H m (by omega)))
    have e : (fun v => (List.range (m + 1)).any (fun r => f r v)) =
        orr (fun v => (List.range m).any (fun r => f r v)) (f m) := by
      funext v
      simp [List.range_succ, orr]
    rw [e]
    exact relax (seq h1 h2) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl

theorem dec_step (P bv r : Nat) (b : Bool) (hbv : bv < P) (hr : r < 2 * P) :
    decide (bv + (if b = true then P else 0) = r) = (decide (bv = r % P) && (b == decide (r / P = 1))) := by
  have hP : 0 < P := by omega
  have h1 := Nat.div_add_mod r P
  have h2 := Nat.mod_lt r hP
  have h3 : r / P < 2 := by rw [Nat.div_lt_iff_lt_mul hP]; omega
  generalize r / P = q at h1 h3 ⊢
  generalize r % P = ρ at h1 h2 ⊢
  have hq : q = 0 ∨ q = 1 := by omega
  rcases hq with rfl | rfl
  · simp only [Nat.mul_zero, Nat.zero_add] at h1
    subst h1
    cases b
    · simp
    · have : ¬ (bv + P = ρ) := by omega
      simp [this]
  · simp only [Nat.mul_one] at h1
    cases b
    · have : ¬ (bv = r) := by omega
      simp [this]
    · have : (bv + P = r) ↔ (bv = ρ) := by omega
      simp [this]

theorem decG {n : Nat} {J : Set Nat} {A : Set (Sig n)} (sd : Nat → Sig n) (htrue : (fun _ => true) ∈ A) :
    ∀ i, (∀ k < i, sd k ∈ A) → (∀ k < i, nt (sd k) ∈ A) →
      ∃ (c : Nat) (B : Set (Sig n)), c ≤ 2 ^ (i + 1) ∧ Build J A B c ∧
        ∀ m < 2 ^ i, (fun v => decide (bitsVal (fun k => sd k v) i = m)) ∈ A ∪ B
  | 0, _, _ => by
    refine ⟨0, ∅, by simp, idle (by simp), ?_⟩
    intro m hm
    have hm0 : m = 0 := by simpa using hm
    subst hm0
    have e : (fun v : Fin n → Bool => decide (bitsVal (fun k => sd k v) 0 = 0)) = fun _ => true := by
      funext v; simp [bitsVal]
    rw [e]; exact Or.inl htrue
  | i + 1, hs, hn => by
    obtain ⟨c, B, hc, HB, hD⟩ := decG (J := J) sd htrue i (fun k hk => hs k (by omega)) (fun k hk => hn k (by omega))
    have hpos : 0 < 2 ^ i := Nat.two_pow_pos i
    have H' : Build J (A ∪ B) {f | ∃ r < 2 ^ (i + 1),
        f ∈ ({fun v => decide (bitsVal (fun k => sd k v) (i + 1) = r)} : Set (Sig n))} (2 ^ (i + 1) * 1) :=
      famBuild (fun r => {fun v => decide (bitsVal (fun k => sd k v) (i + 1) = r)}) 1 (2 ^ (i + 1))
        (fun r hr => by
          have hr2 : r < 2 * 2 ^ i := by rw [Nat.pow_succ] at hr; omega
          by_cases hb : r / 2 ^ i = 1
          · have hand := andG (J := J) (A := A ∪ B)
              (f := fun v => decide (bitsVal (fun k => sd k v) i = r % 2 ^ i)) (g := sd i)
              (hD _ (Nat.mod_lt _ hpos)) (Or.inl (hs i (by omega)))
            have e : (fun v => decide (bitsVal (fun k => sd k v) (i + 1) = r)) =
                an (fun v => decide (bitsVal (fun k => sd k v) i = r % 2 ^ i)) (sd i) := by
              funext v
              have hb' : bitsVal (fun k => sd k v) (i + 1) =
                  bitsVal (fun k => sd k v) i + (if sd i v = true then 2 ^ i else 0) := rfl
              show decide (bitsVal (fun k => sd k v) (i + 1) = r) =
                (decide (bitsVal (fun k => sd k v) i = r % 2 ^ i) && sd i v)
              rw [hb', dec_step (2 ^ i) _ r (sd i v) (bitsVal_lt _ _) hr2]
              simp [hb]
            rw [e]; exact hand
          · have hand := andG (J := J) (A := A ∪ B)
              (f := fun v => decide (bitsVal (fun k => sd k v) i = r % 2 ^ i)) (g := nt (sd i))
              (hD _ (Nat.mod_lt _ hpos)) (Or.inl (hn i (by omega)))
            have e : (fun v => decide (bitsVal (fun k => sd k v) (i + 1) = r)) =
                an (fun v => decide (bitsVal (fun k => sd k v) i = r % 2 ^ i)) (nt (sd i)) := by
              funext v
              have hb' : bitsVal (fun k => sd k v) (i + 1) =
                  bitsVal (fun k => sd k v) i + (if sd i v = true then 2 ^ i else 0) := rfl
              show decide (bitsVal (fun k => sd k v) (i + 1) = r) =
                (decide (bitsVal (fun k => sd k v) i = r % 2 ^ i) && !(sd i v))
              rw [hb', dec_step (2 ^ i) _ r (sd i v) (bitsVal_lt _ _) hr2]
              simp [hb]
            rw [e]; exact hand)
    refine ⟨c + 2 ^ (i + 1) * 1, _, ?_, seq HB H', ?_⟩
    · have : 2 ^ (i + 1 + 1) = 2 * 2 ^ (i + 1) := by rw [Nat.pow_succ]; omega
      omega
    · intro m hm
      exact Or.inr (Or.inr ⟨m, hm, rfl⟩)

theorem any_decide (p j0 : Nat) (g : Nat → Bool) :
    (List.range p).any (fun j => decide (j0 = j) && g j) = (decide (j0 < p) && g j0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨j, hj, hjj, hg⟩
    subst hjj
    exact ⟨hj, hg⟩
  · rintro ⟨hj, hg⟩
    exact ⟨j0, hj, rfl, hg⟩

theorem buildCells (N h p : Nat) [NeZero N] (cx cy : Nat → Fin N) (R S : Finset (Fin N))
    (hR : ∀ j < p, cx j ∈ R) (hS : ∀ j < p, cy j ∈ S) :
    ∃ C : Circuit, (ReadsBack (N + N + h) C ∧ C.output < N + N + h + C.size ∧
        ∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
          (g.op = .and ∨ g.op = .or ∨ (g.op = .not ∧ g.inputs.length = 1))) ∧
      ((∀ x : Fin N, (C.output = x.val ∨ ∃ g ∈ C.gates, x.val ∈ g.inputs) → x ∈ R) ∧
        (∀ y : Fin N, (C.output = N + y.val ∨ ∃ g ∈ C.gates, N + y.val ∈ g.inputs) → y ∈ S)) ∧
      C.size ≤ 2 + h + 2 ^ (h + 1) + 3 * p ∧
      ∀ (w : Fin h → Bool) (x y : Fin N),
        C.eval (PEqualNP.Represents.oneEach x y ++ List.ofFn w) =
          (decide (bitsVal (wbit w) h < p) && (decide (cx (bitsVal (wbit w) h) = x) &&
            decide (cy (bitsVal (wbit w) h) = y))) := by
  have Hconst : Build (JJ R S) (A0 h R S) ({fun _ => false} ∪ {fun _ => true}) (1 + 1) :=
    seq (constG false) (constG true)
  have hfalse : (fun _ : Fin (N + N + h) → Bool => false) ∈
      A0 h R S ∪ ({fun _ => false} ∪ {fun _ => true}) := Or.inr (Or.inl rfl)
  have htrue : (fun _ : Fin (N + N + h) → Bool => true) ∈
      A0 h R S ∪ ({fun _ => false} ∪ {fun _ => true}) := Or.inr (Or.inr rfl)
  have HN : Build (JJ R S) (A0 h R S ∪ ({fun _ => false} ∪ {fun _ => true}))
      {f | ∃ i < h, f ∈ ({nt (sdS N h i)} : Set (Sig (N + N + h)))} (h * 1) :=
    famBuild (fun i => {nt (sdS N h i)}) 1 h (fun i hi => notG (Or.inl (sdS_mem h R S i hi)))
  have H12 := seq Hconst HN
  generalize hA1 : (({fun _ => false} ∪ {fun _ => true}) ∪
      {f | ∃ i < h, f ∈ ({nt (sdS N h i)} : Set (Sig (N + N + h)))} : Set (Sig (N + N + h))) = A1 at H12
  have hfalse1 : (fun _ : Fin (N + N + h) → Bool => false) ∈ A0 h R S ∪ A1 := by
    rw [← hA1]; exact Or.inr (Or.inl (Or.inl rfl))
  have htrue1 : (fun _ : Fin (N + N + h) → Bool => true) ∈ A0 h R S ∪ A1 := by
    rw [← hA1]; exact Or.inr (Or.inl (Or.inr rfl))
  obtain ⟨cD, BD, hcD, HD, hDm⟩ := decG (J := JJ R S) (A := A0 h R S ∪ A1) (sdS N h) htrue1 h
    (fun k hk => Or.inl (sdS_mem h R S k hk))
    (fun k hk => by rw [← hA1]; exact Or.inr (Or.inr ⟨k, hk, rfl⟩))
  have H123 := seq H12 HD
  let cell : Nat → Sig (N + N + h) := fun j =>
    an (an (fun v => decide (bitsVal (fun k => sdS N h k v) h = j))
      (fun v => v ⟨(cx j).val, by omega⟩)) (fun v => v ⟨N + (cy j).val, by omega⟩)
  have HCell : Build (JJ R S) (A0 h R S ∪ (A1 ∪ BD)) {f | ∃ j < p, f ∈ ({cell j} : Set (Sig (N + N + h)))} (p * 2) :=
    famBuild (fun j => {cell j}) 2 p (fun j hj => by
      have hj2 : j < 2 ^ h ∨ ¬ j < 2 ^ h := em _
      have hdec : (fun v => decide (bitsVal (fun k => sdS N h k v) h = j)) ∈ A0 h R S ∪ (A1 ∪ BD) := by
        by_cases hjh : j < 2 ^ h
        · rcases hDm j hjh with (h1 | h1) | h1
          · exact Or.inl h1
          · exact Or.inr (Or.inl h1)
          · exact Or.inr (Or.inr h1)
        · have e : (fun v : Fin (N + N + h) → Bool => decide (bitsVal (fun k => sdS N h k v) h = j)) = fun _ => false := by
            funext v
            have := bitsVal_lt (fun k => sdS N h k v) h
            simp; omega
          rw [e]
          rcases hfalse1 with h1 | h1
          · exact Or.inl h1
          · exact Or.inr (Or.inl h1)
      have a1 := andG (J := JJ R S) (A := A0 h R S ∪ (A1 ∪ BD))
        (f := fun v => decide (bitsVal (fun k => sdS N h k v) h = j)) (g := fun v => v ⟨(cx j).val, by omega⟩)
        hdec (Or.inl (row_mem h R S (cx j) (hR j hj)))
      have a2 := andG (J := JJ R S) (A := (A0 h R S ∪ (A1 ∪ BD)) ∪
          {an (fun v => decide (bitsVal (fun k => sdS N h k v) h = j)) (fun v => v ⟨(cx j).val, by omega⟩)})
        (f := an (fun v => decide (bitsVal (fun k => sdS N h k v) h = j)) (fun v => v ⟨(cx j).val, by omega⟩))
        (g := fun v => v ⟨N + (cy j).val, by omega⟩) (Or.inr rfl) (Or.inl (Or.inl (col_mem h R S (cy j) (hS j hj))))
      exact relax (seq a1 a2) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl)
  have H1234 := seq H123 HCell
  have HOr := chainOr (J := JJ R S)
    (A := A0 h R S ∪ ((A1 ∪ BD) ∪ {f | ∃ j < p, f ∈ ({cell j} : Set (Sig (N + N + h)))})) cell
    (by rcases hfalse1 with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (Or.inl (Or.inl h1))) p
    (fun j hj => Or.inr (Or.inr ⟨j, hj, rfl⟩))
  have Hall := seq H1234 HOr
  obtain ⟨C, hlegal, hnamed, hsize, heval⟩ := extract R S _ _ _ Hall (Or.inr (Or.inr rfl))
  refine ⟨C, hlegal, hnamed, by omega, fun w x y => ?_⟩
  rw [heval]
  have e1 : bitsVal (fun k => sdS N h k (inp x y w)) h = bitsVal (wbit w) h :=
    bitsVal_congr _ _ h (fun i _ => sdS_inp x y w i)
  simp only [cell, an, e1, inp_row, inp_col]
  have := any_decide p (bitsVal (wbit w) h) (fun j => decide (cx j = x) && decide (cy j = y))
  simp only [Bool.and_assoc] at this ⊢
  exact this

end Dec
end PEqualNP.Outside.L_meta_32014_aux

namespace PEqualNP.Outside.L_meta_32014_aux
namespace Sp

open PEqualNP.CircuitLowerBounds GB Ext Mux Sq Dec Loss
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)

def legal (N h : Nat) (C : Circuit) : Prop :=
  ReadsBack (N + N + h) C ∧ C.output < N + N + h + C.size ∧
    ∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ (g.op = .not ∧ g.inputs.length = 1))

def uses (C : Circuit) (j : Nat) : Prop := C.output = j ∨ ∃ g ∈ C.gates, j ∈ g.inputs

def named (N : Nat) (C : Circuit) (R S : Finset (Fin N)) : Prop :=
  (∀ x : Fin N, uses C x.val → x ∈ R) ∧ (∀ y : Fin N, uses C (N + y.val) → y ∈ S)

def table (N h : Nat) (C : Circuit) (w : Fin h → Bool) (x y : Fin N) : Bool :=
  C.eval (PEqualNP.Represents.oneEach x y ++ List.ofFn w)

def code (h j : Nat) (i : Fin h) : Bool := j.testBit i.val

def fits (N h : Nat) (C : Circuit) (budget : Nat) : Prop :=
  legal N h C ∧ (∃ R S : Finset (Fin N), named N C R S ∧ R.card + S.card ≤ budget) ∧
    ∀ w : Fin h → Bool, lossF (table N h C w) ∅ ≤ 1

variable {N : Nat} [NeZero N]

theorem cell_loss (H : Fin N → Fin N → Bool) (cx cy : Fin N)
    (h : ∀ x y, H x y = (decide (cx = x) && decide (cy = y))) (U : Finset (Fin N)) :
    lossF H ∅ ≤ 1 ∧ (lossF H U : ℝ) = (N * U.card : ℕ) + (if cy - cx ∈ U then (-1 : ℝ) else 1) := by
  have hc : ∀ x y, H x y = true ↔ (x, y) = (cx, cy) := by
    intro x y
    rw [h, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq, Prod.mk.injEq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1.symm, h2.symm⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1.symm, h2.symm⟩
  refine ⟨?_, ?_⟩
  · have := (loss_one H ∅ (cx, cy) hc).2 (by simp)
    rw [this]; simp
  · by_cases hu : cy - cx ∈ U
    · have h1 := (loss_one H U (cx, cy) hc).1 hu
      rw [if_pos hu]
      have : (lossF H U : ℝ) + 1 = ((N * U.card : ℕ) : ℝ) := by exact_mod_cast h1
      linarith
    · have h1 := (loss_one H U (cx, cy) hc).2 hu
      rw [if_neg hu, h1]
      push_cast; ring

theorem zero_loss (H : Fin N → Fin N → Bool) (h : ∀ x y, H x y = false) (U : Finset (Fin N)) :
    lossF H ∅ ≤ 1 ∧ lossF H U = N * U.card := by
  refine ⟨?_, loss_zero H U h⟩
  rw [loss_zero H ∅ h]; simp

theorem ofNat_add (u v : Nat) : Fin.ofNat N u + Fin.ofNat N v = Fin.ofNat N (u + v) := by
  apply Fin.ext
  simp [Fin.val_add, Nat.add_mod]

theorem shift_cell (r q ρ : Nat) : colOf (N := N) r q - rowOf ρ = Fin.ofNat N (q * r + ρ) := by
  unfold colOf rowOf
  rw [sub_neg_eq_add, ofNat_add]

theorem ofNat_inj {j j' : Nat} (hj : j < N) (hj' : j' < N) (h : Fin.ofNat N j = Fin.ofNat N j') : j = j' := by
  have := congrArg Fin.val h
  simp only [Fin.val_ofNat] at this
  rwa [Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hj'] at this

theorem bitsVal_self (i w : Nat) (hi : i < 2 ^ w) : bitsVal (fun j => i.testBit j) w = i := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < w
  · rw [bitsVal_testBit _ _ _ hk]
  · have h1 : bitsVal (fun j => i.testBit j) w < 2 ^ k :=
      lt_of_lt_of_le (bitsVal_lt _ _) (Nat.pow_le_pow_right (by omega) (by omega))
    have h2 : i < 2 ^ k := lt_of_lt_of_le hi (Nat.pow_le_pow_right (by omega) (by omega))
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]

theorem code_val (h j : Nat) (hj : j < 2 ^ h) : bitsVal (wbit (code h j)) h = j := by
  rw [← bitsVal_self j h hj]
  apply bitsVal_congr
  intro i hi
  simp [wbit, code, hi, bitsVal_self j h hj]

end Sp
end PEqualNP.Outside.L_meta_32014_aux

namespace PEqualNP.Outside.L_meta_32014_aux
namespace Sp

open PEqualNP.CircuitLowerBounds GB Ext Mux Sq Dec Loss
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)

variable {N : Nat} [NeZero N]

theorem sum_delta (U : Finset (Fin N)) :
    (∑ s : Fin N, (if s ∈ U then (-1 : ℝ) else 1)) = (N : ℝ) - 2 * (U.card : ℝ) := by
  have h1 : ∀ s : Fin N, (if s ∈ U then (-1 : ℝ) else 1) = 1 - 2 * (if s ∈ U then (1 : ℝ) else 0) := by
    intro s; split_ifs <;> norm_num
  simp_rw [h1]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole]
  simp

theorem part3b (a t : Nat) (hN : N = 2 ^ (2 * a)) (h2t : N < 2 * t) :
    ∃ C : Circuit, fits N (2 * a) C (2 * 2 ^ a) ∧ C.size ≤ 6 * (2 ^ a - 1) + 2 * a + 1 ∧
      ∀ U : Finset (Fin N), U.card = t →
        (∑ w : Fin (2 * a) → Bool, (lossF (table N (2 * a) C w) U : ℝ)) / (N : ℝ) =
          ((N * t : ℕ) : ℝ) - ((2 * t - N : ℕ) : ℝ) / (N : ℝ) := by
  obtain ⟨C, hlegal, hnamed, hsize, heval⟩ := build3b N a
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hval : ∀ w : Fin (2 * a) → Bool, bitsVal (wbit w) (2 * a) =
      bitsVal (wbit w) a + 2 ^ a * bitsVal (fun i => wbit w (a + i)) a := fun w =>
    (congrArg (bitsVal (wbit w)) (show 2 * a = a + a by omega)).trans (bitsVal_add _ a a)
  have hshift : ∀ w : Fin (2 * a) → Bool,
      colOf (N := N) (2 ^ a) (bitsVal (fun i => wbit w (a + i)) a) - rowOf (bitsVal (wbit w) a) =
        Fin.ofNat N (bitsVal (wbit w) (2 * a)) := by
    intro w
    rw [shift_cell, hval w]
    congr 1
    rw [Nat.mul_comm]; omega
  have hcell : ∀ (w : Fin (2 * a) → Bool) (U : Finset (Fin N)),
      lossF (table N (2 * a) C w) ∅ ≤ 1 ∧
      (lossF (table N (2 * a) C w) U : ℝ) = (N * U.card : ℕ) +
        (if Fin.ofNat N (bitsVal (wbit w) (2 * a)) ∈ U then (-1 : ℝ) else 1) := by
    intro w U
    have := cell_loss (table N (2 * a) C w) _ _ (fun x y => heval w x y) U
    rw [hshift w] at this
    exact this
  have hinj : Function.Injective (fun w : Fin (2 * a) → Bool => Fin.ofNat N (bitsVal (wbit w) (2 * a))) := by
    intro w w' hww
    have hlt : ∀ u : Fin (2 * a) → Bool, bitsVal (wbit u) (2 * a) < N := fun u => by
      rw [hN]; exact bitsVal_lt _ _
    have hv := ofNat_inj (hlt w) (hlt w') hww
    funext i
    have := bitsVal_inj _ _ _ hv i.val i.isLt
    simpa [wbit] using this
  have hbij : Function.Bijective (fun w : Fin (2 * a) → Bool => Fin.ofNat N (bitsVal (wbit w) (2 * a))) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    simp [hN]
  refine ⟨C, ⟨hlegal, ⟨_, _, hnamed, ?_⟩, fun w => (hcell w ∅).1⟩, hsize, ?_⟩
  · have h1 := Finset.card_image_le (s := Finset.range (2 ^ a)) (f := rowOf (N := N))
    have h2 := Finset.card_image_le (s := Finset.range (2 ^ a)) (f := colOf (N := N) (2 ^ a))
    rw [Finset.card_range] at h1 h2
    omega
  · intro U hU
    have hsum : (∑ w : Fin (2 * a) → Bool, (lossF (table N (2 * a) C w) U : ℝ)) =
        (N : ℝ) * ((N * t : ℕ) : ℝ) + ((N : ℝ) - 2 * (t : ℝ)) := by
      have h1 : ∀ w : Fin (2 * a) → Bool, (lossF (table N (2 * a) C w) U : ℝ) =
          ((N * t : ℕ) : ℝ) + (fun s : Fin N => if s ∈ U then (-1 : ℝ) else 1)
            ((fun w : Fin (2 * a) → Bool => Fin.ofNat N (bitsVal (wbit w) (2 * a))) w) := by
        intro w
        rw [(hcell w U).2, hU]
      simp_rw [h1]
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        hbij.sum_comp (fun s : Fin N => if s ∈ U then (-1 : ℝ) else 1), sum_delta, hU]
      have hc : Fintype.card (Fin (2 * a) → Bool) = N := by simp [hN]
      rw [hc]
      simp
    rw [hsum]
    have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
    rw [Nat.cast_sub (by omega : N ≤ 2 * t)]
    push_cast
    field_simp
    ring

end Sp
end PEqualNP.Outside.L_meta_32014_aux

namespace PEqualNP.Outside.L_meta_32014_aux
namespace Sp

open PEqualNP.CircuitLowerBounds GB Ext Mux Sq Dec Loss
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)

variable {N : Nat} [NeZero N]

theorem half_bound (B K : Nat) (hK : K ≤ B ^ 2 / 4) : K ≤ (B / 2) * (B - B / 2) := by
  have h1 : 4 * K ≤ B ^ 2 := by
    have := Nat.div_mul_le_self (B ^ 2) 4
    omega
  have h2 := Nat.div_add_mod B 2
  have h3 := Nat.mod_lt B (by omega : 0 < 2)
  generalize B / 2 = a at *
  generalize B % 2 = e at *
  have hB : B = 2 * a + e := by omega
  subst hB
  have h4 : 2 * a + e - a = a + e := by omega
  rw [h4]
  have he : e = 0 ∨ e = 1 := by omega
  rcases he with rfl | rfl
  · nlinarith
  · nlinarith

theorem part2 (t B : Nat) (ht : t ≤ N) :
    ∃ (p h : Nat) (C : Circuit), 0 < p ∧ p ≤ N ∧ p ≤ 2 ^ h ∧ 2 ^ h ≤ 2 * p ∧
      fits N h C B ∧ C.size ≤ 10 * p + h + 2 ∧
      ∀ U : Finset (Fin N), U.card = t →
        (∑ j : Fin p, (lossF (table N h C (code h j.val)) U : ℝ)) / (p : ℝ) ≤
          ((N * t : ℕ) : ℝ) - ((min N (B ^ 2 / 4) - 2 * (N - t) : ℕ) : ℝ) / ((min N (B ^ 2 / 4) : ℕ) : ℝ) := by
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  by_cases hcase : min N (B ^ 2 / 4) ≤ 2 * (N - t)
  · obtain ⟨C, hlegal, hnamed, hsize, heval⟩ := buildCells N 0 0 (fun _ => (0 : Fin N)) (fun _ => (0 : Fin N))
      ∅ ∅ (fun j hj => absurd hj (by omega)) (fun j hj => absurd hj (by omega))
    have hz : ∀ (w : Fin 0 → Bool) (x y : Fin N), table N 0 C w x y = false := by
      intro w x y
      show C.eval _ = false
      rw [heval]; simp
    refine ⟨1, 0, C, by omega, hNpos, by simp, by simp, ⟨hlegal, ⟨∅, ∅, hnamed, by simp⟩,
      fun w => (zero_loss _ (hz w) ∅).1⟩, by simp at hsize ⊢; omega, ?_⟩
    intro U hU
    rw [Nat.sub_eq_zero_of_le hcase]
    simp only [Fin.sum_univ_one, Nat.cast_one, div_one, Nat.cast_zero, zero_div, sub_zero]
    rw [(zero_loss _ (hz _) U).2, hU]
  · have hK1 : 1 ≤ min N (B ^ 2 / 4) := by omega
    have hKN : min N (B ^ 2 / 4) ≤ N := Nat.min_le_left _ _
    have hKB : min N (B ^ 2 / 4) ≤ B ^ 2 / 4 := Nat.min_le_right _ _
    generalize min N (B ^ 2 / 4) = K at *
    have hab := half_bound B K hKB
    have ha : 1 ≤ B / 2 := by
      by_contra h0
      have : B / 2 = 0 := by omega
      rw [this] at hab; omega
    generalize B / 2 = a at *
    have haB : a ≤ B := by
      by_contra hlt
      have : B - a = 0 := by omega
      rw [this] at hab; omega

    have hh : K ≤ 2 ^ Nat.clog 2 K ∧ 2 ^ Nat.clog 2 K ≤ 2 * K := by
      refine ⟨Nat.le_pow_clog (by omega) _, ?_⟩
      by_cases hK2 : K = 1
      · subst hK2; simp
      · have hpos : 0 < Nat.clog 2 K := Nat.clog_pos (by omega) (by omega)
        have hpred := Nat.pow_pred_clog_lt_self 2 (show 1 < K by omega)
        rw [Nat.pred_eq_sub_one] at hpred
        have : 2 ^ Nat.clog 2 K = 2 * 2 ^ (Nat.clog 2 K - 1) := by
          conv_lhs => rw [show Nat.clog 2 K = (Nat.clog 2 K - 1) + 1 by omega]
          rw [Nat.pow_succ]; omega
        omega
    generalize Nat.clog 2 K = h at hh
    obtain ⟨hKh, hh2⟩ := hh
    obtain ⟨C, hlegal, hnamed, hsize, heval⟩ := buildCells N h K
      (fun j => rowOf (N := N) (j % a)) (fun j => colOf (N := N) a (j / a))
      ((Finset.range a).image (rowOf (N := N))) ((Finset.range ((K - 1) / a + 1)).image (colOf (N := N) a))
      (fun j hj => Finset.mem_image.mpr ⟨j % a, Finset.mem_range.mpr (Nat.mod_lt _ (by omega)), rfl⟩)
      (fun j hj => Finset.mem_image.mpr ⟨j / a, Finset.mem_range.mpr (by
        have := Nat.div_le_div_right (c := a) (show j ≤ K - 1 by omega); omega), rfl⟩)
    have hcellshift : ∀ j : Nat, colOf (N := N) a (j / a) - rowOf (j % a) = Fin.ofNat N j := by
      intro j
      rw [shift_cell, Nat.div_add_mod']
    have htab : ∀ (w : Fin h → Bool) (x y : Fin N), table N h C w x y =
        (decide (bitsVal (wbit w) h < K) && (decide (rowOf (N := N) (bitsVal (wbit w) h % a) = x) &&
          decide (colOf (N := N) a (bitsVal (wbit w) h / a) = y))) := fun w x y => heval w x y
    have hfit : ∀ w : Fin h → Bool, lossF (table N h C w) ∅ ≤ 1 := by
      intro w
      by_cases hlt : bitsVal (wbit w) h < K
      · exact (cell_loss (table N h C w) (rowOf (N := N) (bitsVal (wbit w) h % a))
          (colOf (N := N) a (bitsVal (wbit w) h / a)) (fun x y => by rw [htab]; simp [hlt]) ∅).1
      · exact (zero_loss (table N h C w) (fun x y => by rw [htab]; simp [hlt]) ∅).1
    refine ⟨K, h, C, by omega, hKN, hKh, hh2, ⟨hlegal, ⟨_, _, hnamed, ?_⟩, hfit⟩, ?_, ?_⟩
    · have h1 := Finset.card_image_le (s := Finset.range a) (f := rowOf (N := N))
      have h2 := Finset.card_image_le (s := Finset.range ((K - 1) / a + 1)) (f := colOf (N := N) a)
      rw [Finset.card_range] at h1 h2
      have h3 : (K - 1) / a < B - a := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        rw [Nat.mul_comm] at hab; omega
      omega
    · have : 2 ^ (h + 1) = 2 * 2 ^ h := by rw [Nat.pow_succ]; omega
      omega
    · intro U hU
      have hloss : ∀ j : Fin K, (lossF (table N h C (code h j.val)) U : ℝ) =
          ((N * t : ℕ) : ℝ) + (if Fin.ofNat N j.val ∈ U then (-1 : ℝ) else 1) := by
        intro j
        have hjv : bitsVal (wbit (code h j.val)) h = j.val := code_val h j.val (by have := j.isLt; omega)
        have := (cell_loss (table N h C (code h j.val)) (rowOf (N := N) (j.val % a)) (colOf (N := N) a (j.val / a))
          (fun x y => by rw [htab, hjv]; simp) U).2
        rw [hcellshift, hU] at this
        exact this
      simp_rw [hloss]
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]

      have hm : t + K ≤ N + ((Finset.univ : Finset (Fin K)).filter (fun j => Fin.ofNat N j.val ∈ U)).card := by
        classical
        have hinj : Function.Injective (fun j : Fin K => Fin.ofNat N j.val) := by
          intro j j' hjj
          exact Fin.ext (ofNat_inj (by have := j.isLt; omega) (by have := j'.isLt; omega) hjj)
        have hV : ((Finset.univ : Finset (Fin K)).image (fun j : Fin K => Fin.ofNat N j.val)).card = K := by
          rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
        have hfil : ((Finset.univ : Finset (Fin K)).filter (fun j => Fin.ofNat N j.val ∈ U)).card =
            (U ∩ (Finset.univ : Finset (Fin K)).image (fun j : Fin K => Fin.ofNat N j.val)).card := by
          rw [← Finset.card_image_of_injective _ hinj]
          congr 1
          ext s
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
          constructor
          · rintro ⟨j, hj, rfl⟩; exact ⟨hj, j, rfl⟩
          · rintro ⟨hs, j, rfl⟩; exact ⟨j, hs, rfl⟩
        have hun := Finset.card_union_add_card_inter U
          ((Finset.univ : Finset (Fin K)).image (fun j : Fin K => Fin.ofNat N j.val))
        have hle : (U ∪ (Finset.univ : Finset (Fin K)).image (fun j : Fin K => Fin.ofNat N j.val)).card ≤ N := by
          have := Finset.card_le_univ (U ∪ (Finset.univ : Finset (Fin K)).image (fun j : Fin K => Fin.ofNat N j.val))
          simpa using this
        rw [hfil]; omega
      have hd : (∑ j : Fin K, (if Fin.ofNat N j.val ∈ U then (-1 : ℝ) else 1)) =
          (K : ℝ) - 2 * (((Finset.univ : Finset (Fin K)).filter (fun j => Fin.ofNat N j.val ∈ U)).card : ℝ) := by
        have h1 : ∀ j : Fin K, (if Fin.ofNat N j.val ∈ U then (-1 : ℝ) else 1) =
            1 - 2 * (if Fin.ofNat N j.val ∈ U then (1 : ℝ) else 0) := by
          intro j; split_ifs <;> norm_num
        simp_rw [h1]
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole]
        simp
      rw [hd]
      have hKr : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK1
      have hmr : (t : ℝ) + (K : ℝ) ≤ (N : ℝ) +
          (((Finset.univ : Finset (Fin K)).filter (fun j => Fin.ofNat N j.val ∈ U)).card : ℝ) := by
        exact_mod_cast hm
      have hc1 : ((K - 2 * (N - t) : ℕ) : ℝ) = (K : ℝ) - 2 * ((N : ℝ) - (t : ℝ)) := by
        rw [Nat.cast_sub (by omega : 2 * (N - t) ≤ K)]
        push_cast [Nat.cast_sub ht]
        ring
      rw [hc1, div_le_iff₀ hKr, sub_mul, div_mul_cancel₀ _ (ne_of_gt hKr)]
      simp only [nsmul_eq_mul]
      push_cast
      nlinarith [hmr]

end Sp
end PEqualNP.Outside.L_meta_32014_aux

namespace PEqualNP.Outside.L_meta_32014_aux
namespace Cone

open PEqualNP.CircuitLowerBounds GB
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)

def pullR (n : Nat) : List Gate → Finset Nat → Finset Nat
  | [], F => F
  | g :: rs, F =>
    pullR n rs (if n + rs.length ∈ F then (F.erase (n + rs.length)) ∪ g.inputs.toFinset else F)

theorem pullR_card (n : Nat) : ∀ (rs : List Gate) (F : Finset Nat),
    (∀ g ∈ rs, g.inputs.length ≤ 2) → (pullR n rs F).card ≤ F.card + rs.length
  | [], F, _ => by simp [pullR]
  | g :: rs, F, h => by
    have ih := pullR_card n rs (if n + rs.length ∈ F then (F.erase (n + rs.length)) ∪ g.inputs.toFinset else F)
      (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))
    have hg := h g List.mem_cons_self
    have hstep : (if n + rs.length ∈ F then (F.erase (n + rs.length)) ∪ g.inputs.toFinset else F).card ≤ F.card + 1 := by
      split_ifs with hm
      · have h1 := Finset.card_union_le (F.erase (n + rs.length)) g.inputs.toFinset
        have h2 := Finset.card_erase_of_mem hm
        have h3 : g.inputs.toFinset.card ≤ g.inputs.length := List.toFinset_card_le _
        have h4 : 0 < F.card := Finset.card_pos.mpr ⟨_, hm⟩
        omega
      · omega
    simp only [pullR, List.length_cons]
    omega

theorem pullR_sub (n : Nat) : ∀ (rs : List Gate) (F : Finset Nat) (j : Nat),
    j ∈ pullR n rs F → j ∈ F ∨ ∃ g ∈ rs, j ∈ g.inputs
  | [], F, j, h => Or.inl h
  | g :: rs, F, j, h => by
    simp only [pullR] at h
    rcases pullR_sub n rs _ j h with h1 | ⟨g', hg', hj⟩
    · split_ifs at h1 with hm
      · rcases Finset.mem_union.mp h1 with h2 | h2
        · exact Or.inl (Finset.mem_of_mem_erase h2)
        · exact Or.inr ⟨g, List.mem_cons_self, List.mem_toFinset.mp h2⟩
      · exact Or.inl h1
    · exact Or.inr ⟨g', List.mem_cons_of_mem _ hg', hj⟩

theorem wires_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    (Circuit.mk (gs ++ [g]) 0).wires x =
      (Circuit.mk gs 0).wires x ++
        [g.op.eval (g.inputs.map fun i => ((Circuit.mk gs 0).wires x).getD i false)] := by
  simp only [Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem pullR_sem (n : Nat) : ∀ (rs : List Gate) (F : Finset Nat) (x x' : List Bool),
    x.length = n → x'.length = n →
    (∀ k, ∀ g, rs.reverse.getD k ⟨GateOp.or, []⟩ = g → k < rs.length → ∀ i ∈ g.inputs, i < n + k) →
    (∀ j ∈ pullR n rs F, j < n → x.getD j false = x'.getD j false) →
    ∀ j ∈ F, j < n + rs.length →
      ((Circuit.mk rs.reverse 0).wires x).getD j false = ((Circuit.mk rs.reverse 0).wires x').getD j false
  | [], F, x, x', _, _, _, hag => by
    intro j hj hlt
    simp only [List.reverse_nil, Circuit.wires, List.foldl_nil]
    exact hag j hj (by simpa using hlt)
  | g :: rs, F, x, x', hx, hx', hrb, hag => by
    intro j hj hlt
    have hrb' : ∀ k, ∀ g', rs.reverse.getD k ⟨GateOp.or, []⟩ = g' → k < rs.length → ∀ i ∈ g'.inputs, i < n + k := by
      intro k g' hk hkl i hi
      apply hrb k g' ?_ (by simp; omega) i hi
      rw [List.reverse_cons, List.getD_append _ _ _ _ (by simpa using hkl)]
      exact hk
    have hgin : ∀ i ∈ g.inputs, i < n + rs.length := by
      intro i hi
      apply hrb rs.length g ?_ (by simp) i hi
      rw [List.reverse_cons, List.getD_append_right _ _ _ _ (by simp)]
      simp
    have ih := pullR_sem n rs (if n + rs.length ∈ F then (F.erase (n + rs.length)) ∪ g.inputs.toFinset else F)
      x x' hx hx' hrb' (by simpa only [pullR] using hag)
    have hlen : ∀ y : List Bool, y.length = n → ((Circuit.mk rs.reverse 0).wires y).length = n + rs.length := by
      intro y hy
      rw [wireLength]; simp [hy]
    rw [List.reverse_cons, wires_snoc, wires_snoc]
    by_cases hjl : j < n + rs.length
    · rw [List.getD_append _ _ _ _ (by rw [hlen x hx]; exact hjl),
        List.getD_append _ _ _ _ (by rw [hlen x' hx']; exact hjl)]
      apply ih j ?_ hjl
      split_ifs with hm
      · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by omega, hj⟩)
      · exact hj
    · have hje : j = n + rs.length := by simp only [List.length_cons] at hlt; omega
      subst hje
      rw [List.getD_append_right _ _ _ _ (by rw [hlen x hx]),
        List.getD_append_right _ _ _ _ (by rw [hlen x' hx']), hlen x hx, hlen x' hx']
      simp only [Nat.sub_self, List.getD_cons_zero]
      congr 1
      apply List.map_congr_left
      intro i hi
      apply ih i ?_ (hgin i hi)
      rw [if_pos hj]
      exact Finset.mem_union_right _ (List.mem_toFinset.mpr hi)

def needSet (n : Nat) (C : Circuit) : Finset Nat := pullR n C.gates.reverse {C.output}

theorem need_card (n : Nat) (C : Circuit) (h : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    (needSet n C).card ≤ C.size + 1 := by
  have := pullR_card n C.gates.reverse {C.output} (fun g hg => h g (List.mem_reverse.mp hg))
  simp only [Finset.card_singleton, List.length_reverse] at this
  unfold needSet Circuit.size
  omega

theorem need_uses (n : Nat) (C : Circuit) (j : Nat) (hj : j ∈ needSet n C) :
    C.output = j ∨ ∃ g ∈ C.gates, j ∈ g.inputs := by
  rcases pullR_sub n C.gates.reverse {C.output} j hj with h1 | ⟨g, hg, hjg⟩
  · exact Or.inl (Finset.mem_singleton.mp h1).symm
  · exact Or.inr ⟨g, List.mem_reverse.mp hg, hjg⟩

theorem need_sem (n : Nat) (C : Circuit) (hrb : ReadsBack n C) (x x' : List Bool)
    (hx : x.length = n) (hx' : x'.length = n)
    (hag : ∀ j ∈ needSet n C, j < n → x.getD j false = x'.getD j false) :
    C.eval x = C.eval x' := by
  have hmain := pullR_sem n C.gates.reverse {C.output} x x' hx hx'
    (by
      intro k g hk hkl i hi
      rw [List.reverse_reverse] at hk
      rw [List.length_reverse] at hkl
      exact hrb k hkl i (by show i ∈ (C.gates.getD k ⟨GateOp.or, []⟩).inputs; rw [hk]; exact hi))
    hag C.output (Finset.mem_singleton_self _)
  rw [List.reverse_reverse, List.length_reverse] at hmain
  show (C.wires x).getD C.output false = (C.wires x').getD C.output false
  by_cases hlt : C.output < n + C.gates.length
  · exact hmain hlt
  · have h1 : (C.wires x).length = n + C.gates.length := by rw [wireLength, hx]
    have h2 : (C.wires x').length = n + C.gates.length := by rw [wireLength, hx']
    rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

end Cone
end PEqualNP.Outside.L_meta_32014_aux

namespace PEqualNP.Outside.L_meta_32014_aux
namespace Low

open PEqualNP.CircuitLowerBounds GB Ext Mux Sq Dec Loss Sp Cone
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)

theorem small_step (c μ S qx Tot : ℝ) (hc : 0 ≤ c) (hμ : 0 ≤ μ)
    (hM : c * S ≤ (μ + 1) * Tot) (hle : S ≤ (μ + 1) * qx) : c * (S - qx) ≤ μ * Tot := by
  have h1 : (μ + 1) * (c * (S - qx)) ≤ (μ + 1) * (μ * Tot) := by
    nlinarith [mul_le_mul_of_nonneg_left hle hc, mul_le_mul_of_nonneg_left hM hμ]
  exact le_of_mul_le_mul_left h1 (by linarith)

theorem small {α : Type} [DecidableEq α] (T : Finset α) (q : α → ℝ) :
    ∀ j ≤ T.card, ∃ M ⊆ T, M.card = T.card - j ∧
      (T.card : ℝ) * ∑ x ∈ M, q x ≤ ((T.card - j : ℕ) : ℝ) * ∑ x ∈ T, q x
  | 0, _ => ⟨T, Finset.Subset.refl _, rfl, le_rfl⟩
  | j + 1, hj => by
    obtain ⟨M, hMT, hMc, hM⟩ := small T q j (by omega)
    have hne : M.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨x, hxM, hmax⟩ := Finset.exists_max_image M q hne
    refine ⟨M.erase x, (Finset.erase_subset _ _).trans hMT, by rw [Finset.card_erase_of_mem hxM]; omega, ?_⟩
    have hsum : ∑ y ∈ M.erase x, q y = ∑ y ∈ M, q y - q x := by
      rw [← Finset.sum_erase_add _ _ hxM]; ring
    have hle : ∑ y ∈ M, q y ≤ (M.card : ℝ) * q x := by
      have := Finset.sum_le_card_nsmul M q (q x) hmax
      simpa [nsmul_eq_mul] using this
    rw [hsum]
    have hμ : ((T.card - j : ℕ) : ℝ) = ((T.card - (j + 1) : ℕ) : ℝ) + 1 := by
      have : T.card - j = T.card - (j + 1) + 1 := by omega
      rw [this]; push_cast; ring
    rw [hMc] at hle
    rw [hμ] at hM hle
    exact small_step _ _ _ _ _ (Nat.cast_nonneg _) (Nat.cast_nonneg _) hM hle

variable {N : Nat} [NeZero N]

def dl (o : Option (Fin N)) (U : Finset (Fin N)) : ℝ :=
  match o with
  | none => 0
  | some s => if s ∈ U then -1 else 1

theorem classify (H : Fin N → Fin N → Bool) (h : lossF H ∅ ≤ 1) :
    ∃ o : Option (Fin N × Fin N),
      (∀ U : Finset (Fin N), (lossF H U : ℝ) =
        ((N * U.card : ℕ) : ℝ) + dl (o.map (fun c => c.2 - c.1)) U) ∧
      (∀ c, o = some c → ∀ x y, H x y = true ↔ (x, y) = c) ∧ (o = none → ∀ x y, H x y = false) := by
  rcases at_most_one H h with h0 | ⟨c, hc⟩
  · refine ⟨none, fun U => ?_, fun c hc => (by cases hc), fun _ => h0⟩
    rw [loss_zero H U h0]; simp [dl]
  · refine ⟨some c, fun U => ?_, fun c' hc' => (by cases hc'; exact hc), fun hn => (by cases hn)⟩
    have hH : ∀ x y, H x y = (decide (c.1 = x) && decide (c.2 = y)) := by
      intro x y
      apply Bool.eq_iff_iff.mpr
      rw [hc x y, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      constructor
      · intro e; rw [← e]; exact ⟨rfl, rfl⟩
      · rintro ⟨h1, h2⟩; exact Prod.ext h1.symm h2.symm
    have := (cell_loss H c.1 c.2 hH U).2
    rw [this]; simp [dl]

def qw {W : Type} [Fintype W] (σ : W → Option (Fin N)) (P : W → ℝ) (s : Fin N) : ℝ :=
  ∑ w, if σ w = some s then P w else 0

theorem dl_sum {W : Type} [Fintype W] (σ : W → Option (Fin N)) (P : W → ℝ) (U : Finset (Fin N)) :
    ∑ w, P w * dl (σ w) U = ∑ s, qw σ P s - 2 * ∑ s ∈ U, qw σ P s := by
  have h1 : ∀ w, P w * dl (σ w) U =
      ∑ s, (if σ w = some s then P w else 0) * (if s ∈ U then (-1 : ℝ) else 1) := by
    intro w
    cases hσ : σ w with
    | none => simp [dl]
    | some s0 =>
      simp only [dl, Option.some.injEq]
      rw [Finset.sum_eq_single s0]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · intro hn; exact absurd (Finset.mem_univ _) hn
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ s : Fin N, ∑ w, (if σ w = some s then P w else 0) * (if s ∈ U then (-1 : ℝ) else 1) =
      qw σ P s - 2 * (if s ∈ U then qw σ P s else 0) := by
    intro s
    rw [← Finset.sum_mul]
    change qw σ P s * _ = _
    split_ifs <;> ring
  simp_rw [h2]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_mem, Finset.univ_inter]

theorem qw_nonneg {W : Type} [Fintype W] (σ : W → Option (Fin N)) (P : W → ℝ) (hP : ∀ w, 0 ≤ P w)
    (s : Fin N) : 0 ≤ qw σ P s :=
  Finset.sum_nonneg (fun w _ => by split_ifs; exact hP w; exact le_rfl)

theorem qw_total {W : Type} [Fintype W] (σ : W → Option (Fin N)) (P : W → ℝ) (hP : ∀ w, 0 ≤ P w) :
    ∑ s, qw σ P s ≤ ∑ w, P w := by
  unfold qw
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro w _
  cases hσ : σ w with
  | none => simp [hP w]
  | some s0 => simp

theorem qw_zero {W : Type} [Fintype W] (σ : W → Option (Fin N)) (P : W → ℝ) (s : Fin N)
    (h : ∀ w, σ w ≠ some s) : qw σ P s = 0 :=
  Finset.sum_eq_zero (fun w _ => if_neg (h w))

theorem indep {h : Nat} (C : Circuit) (hrb : ReadsBack (N + N + h) C) (x x' y y' : Fin N)
    (w w' : Fin h → Bool)
    (hx : x = x' ∨ (x.val ∉ needSet (N + N + h) C ∧ x'.val ∉ needSet (N + N + h) C))
    (hy : y = y' ∨ (N + y.val ∉ needSet (N + N + h) C ∧ N + y'.val ∉ needSet (N + N + h) C))
    (hw : ∀ i : Fin h, w i = w' i ∨ N + N + i.val ∉ needSet (N + N + h) C) :
    C.eval (PEqualNP.Represents.oneEach x y ++ List.ofFn w) =
      C.eval (PEqualNP.Represents.oneEach x' y' ++ List.ofFn w') := by
  apply need_sem (N + N + h) C hrb _ _ (inp_len x y w) (inp_len x' y' w')
  intro j hj hjn
  show inp x y w ⟨j, hjn⟩ = inp x' y' w' ⟨j, hjn⟩
  by_cases h1 : j < N
  · have e1 : inp x y w ⟨j, hjn⟩ = decide ((⟨j, h1⟩ : Fin N) = x) := inp_row x y w ⟨j, h1⟩ hjn
    have e2 : inp x' y' w' ⟨j, hjn⟩ = decide ((⟨j, h1⟩ : Fin N) = x') := inp_row x' y' w' ⟨j, h1⟩ hjn
    rw [e1, e2]
    rcases hx with rfl | ⟨hx1, hx2⟩
    · rfl
    · have n1 : ¬ ((⟨j, h1⟩ : Fin N) = x) := fun e => hx1 (by rw [← e]; exact hj)
      have n2 : ¬ ((⟨j, h1⟩ : Fin N) = x') := fun e => hx2 (by rw [← e]; exact hj)
      simp [n1, n2]
  · by_cases h2 : j < N + N
    · have hj' : j = N + (j - N) := by omega
      have e1 : inp x y w ⟨N + (j - N), by omega⟩ = decide ((⟨j - N, by omega⟩ : Fin N) = y) :=
        inp_col x y w ⟨j - N, by omega⟩ (by omega)
      have e2 : inp x' y' w' ⟨N + (j - N), by omega⟩ = decide ((⟨j - N, by omega⟩ : Fin N) = y') :=
        inp_col x' y' w' ⟨j - N, by omega⟩ (by omega)
      have f1 : inp x y w ⟨j, hjn⟩ = inp x y w ⟨N + (j - N), by omega⟩ := congrArg _ (Fin.ext hj')
      have f2 : inp x' y' w' ⟨j, hjn⟩ = inp x' y' w' ⟨N + (j - N), by omega⟩ := congrArg _ (Fin.ext hj')
      rw [f1, f2, e1, e2]
      rcases hy with rfl | ⟨hy1, hy2⟩
      · rfl
      · have n1 : ¬ ((⟨j - N, by omega⟩ : Fin N) = y) := fun e => hy1 (by rw [← e]; simpa [← hj'] using hj)
        have n2 : ¬ ((⟨j - N, by omega⟩ : Fin N) = y') := fun e => hy2 (by rw [← e]; simpa [← hj'] using hj)
        simp [n1, n2]
    · have hj' : j = N + N + (j - (N + N)) := by omega
      have e1 : inp x y w ⟨N + N + (j - (N + N)), by omega⟩ = w ⟨j - (N + N), by omega⟩ :=
        inp_seed x y w ⟨j - (N + N), by omega⟩ (by omega)
      have e2 : inp x' y' w' ⟨N + N + (j - (N + N)), by omega⟩ = w' ⟨j - (N + N), by omega⟩ :=
        inp_seed x' y' w' ⟨j - (N + N), by omega⟩ (by omega)
      have f1 : inp x y w ⟨j, hjn⟩ = inp x y w ⟨N + N + (j - (N + N)), by omega⟩ := congrArg _ (Fin.ext hj')
      have f2 : inp x' y' w' ⟨j, hjn⟩ = inp x' y' w' ⟨N + N + (j - (N + N)), by omega⟩ :=
        congrArg _ (Fin.ext hj')
      rw [f1, f2, e1, e2]
      rcases hw ⟨j - (N + N), by omega⟩ with hw1 | hw1
      · exact hw1
      · exact absurd (by simpa [← hj'] using hj) hw1

def Rn (N h : Nat) (C : Circuit) : Finset (Fin N) :=
  Finset.univ.filter (fun x : Fin N => x.val ∈ needSet (N + N + h) C)

def Sn (N h : Nat) (C : Circuit) : Finset (Fin N) :=
  Finset.univ.filter (fun y : Fin N => N + y.val ∈ needSet (N + N + h) C)

theorem row_alt {h : Nat} (C : Circuit) (hrb : ReadsBack (N + N + h) C) (w : Fin h → Bool)
    (c : Fin N × Fin N) (hc : ∀ x y, table N h C w x y = true ↔ (x, y) = c) :
    c.1 ∈ Rn N h C ∨ N ≤ (Rn N h C).card + 1 := by
  by_cases h1 : c.1 ∈ Rn N h C
  · exact Or.inl h1
  · right
    have hsub : Finset.univ.erase c.1 ⊆ Rn N h C := by
      intro x' hx'
      by_contra h2
      have hne : x' ≠ c.1 := Finset.ne_of_mem_erase hx'
      have e := indep C hrb x' c.1 c.2 c.2 w w
        (Or.inr ⟨fun hm => h2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩),
          fun hm => h1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩)⟩) (Or.inl rfl) (fun i => Or.inl rfl)
      have t1 : table N h C w c.1 c.2 = true := (hc c.1 c.2).mpr rfl
      have t2 : table N h C w x' c.2 = true := by
        show C.eval _ = true
        rw [e]; exact t1
      exact hne (congrArg Prod.fst ((hc x' c.2).mp t2))
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at this
    omega

theorem col_alt {h : Nat} (C : Circuit) (hrb : ReadsBack (N + N + h) C) (w : Fin h → Bool)
    (c : Fin N × Fin N) (hc : ∀ x y, table N h C w x y = true ↔ (x, y) = c) :
    c.2 ∈ Sn N h C ∨ N ≤ (Sn N h C).card + 1 := by
  by_cases h1 : c.2 ∈ Sn N h C
  · exact Or.inl h1
  · right
    have hsub : Finset.univ.erase c.2 ⊆ Sn N h C := by
      intro y' hy'
      by_contra h2
      have hne : y' ≠ c.2 := Finset.ne_of_mem_erase hy'
      have e := indep C hrb c.1 c.1 y' c.2 w w (Or.inl rfl)
        (Or.inr ⟨fun hm => h2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩),
          fun hm => h1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩)⟩) (fun i => Or.inl rfl)
      have t1 : table N h C w c.1 c.2 = true := (hc c.1 c.2).mpr rfl
      have t2 : table N h C w c.1 y' = true := by
        show C.eval _ = true
        rw [e]; exact t1
      exact hne (congrArg Prod.snd ((hc c.1 y').mp t2))
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at this
    omega

end Low
end PEqualNP.Outside.L_meta_32014_aux

namespace PEqualNP.Outside.L_meta_32014_aux
namespace Low

open PEqualNP.CircuitLowerBounds GB Ext Mux Sq Dec Loss Sp Cone
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)

variable {N : Nat} [NeZero N]

theorem final_ineq (K Nn tt m : ℕ) (e qM : ℝ) (hK : 0 < K) (ht : tt ≤ Nn) (hKN : K ≤ Nn)
    (hm : m = tt - (Nn - K)) (he0 : 0 ≤ e) (he1 : e ≤ 1) (hq0 : 0 ≤ qM)
    (hM : (K : ℝ) * qM ≤ (m : ℝ) * e) :
    -(((K - 2 * (Nn - tt) : ℕ) : ℝ) / (K : ℝ)) ≤ e - 2 * qM := by
  have hKr : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  rw [neg_le, le_div_iff₀ hKr]
  by_cases hc : K ≤ 2 * (Nn - tt)
  · rw [Nat.sub_eq_zero_of_le hc]
    have h2m : 2 * m ≤ K := by omega
    have h2mr : 2 * (m : ℝ) ≤ (K : ℝ) := by exact_mod_cast h2m
    simp only [Nat.cast_zero]
    nlinarith [mul_nonneg he0 (sub_nonneg.mpr h2mr)]
  · have hmK : m + Nn = tt + K := by omega
    have hmr : (m : ℝ) + (Nn : ℝ) = (tt : ℝ) + (K : ℝ) := by exact_mod_cast hmK
    have hcast : ((K - 2 * (Nn - tt) : ℕ) : ℝ) = (K : ℝ) - 2 * ((Nn : ℝ) - (tt : ℝ)) := by
      rw [Nat.cast_sub (by omega)]
      push_cast [Nat.cast_sub ht]
      ring
    rw [hcast]
    have hneg : (K : ℝ) - 2 * ((Nn : ℝ) - (tt : ℝ)) ≥ 0 := by
      have : 2 * (Nn - tt) ≤ K := by omega
      have h' : ((2 * (Nn - tt) : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast this
      push_cast [Nat.cast_sub ht] at h'
      linarith
    have hm2 : (m : ℝ) = (tt : ℝ) + (K : ℝ) - (Nn : ℝ) := by linarith
    rw [hm2] at hM
    nlinarith [mul_le_mul_of_nonneg_left he1 hneg]

theorem part1 (t B : Nat) (hN : 8 ≤ N) (ht : t ≤ N) (h : Nat) (C : Circuit)
    (P : (Fin h → Bool) → ℝ) (hfit : fits N h C B) (hP : ∀ w, 0 ≤ P w) (hsum : ∑ w, P w = 1) :
    ∃ U : Finset (Fin N), U.card = t ∧
      ((N * t : ℕ) : ℝ) - ((min N (B ^ 2 / 4) - 2 * (N - t) : ℕ) : ℝ) / ((min N (B ^ 2 / 4) : ℕ) : ℝ) ≤
        ∑ w, P w * (lossF (table N h C w) U : ℝ) := by
  classical
  obtain ⟨hlegal, ⟨R, S, hnamed, hRS⟩, hone⟩ := hfit
  choose o ho1 ho2 ho3 using fun w => classify (table N h C w) (hone w)
  have hT : ∃ T : Finset (Fin N), T.card = min N (B ^ 2 / 4) ∧
      ∀ w s, (o w).map (fun c => c.2 - c.1) = some s → s ∈ T := by
    by_cases hB : B + 2 ≤ N
    · have hRsub : Rn N h C ⊆ R := fun x hx =>
        hnamed.1 x (need_uses _ C _ (Finset.mem_filter.mp hx).2)
      have hSsub : Sn N h C ⊆ S := fun y hy =>
        hnamed.2 y (need_uses _ C _ (Finset.mem_filter.mp hy).2)
      have hRc := Finset.card_le_card hRsub
      have hSc := Finset.card_le_card hSsub
      have hD0 : ((Rn N h C ×ˢ Sn N h C).image (fun c : Fin N × Fin N => c.2 - c.1)).card ≤
          min N (B ^ 2 / 4) := by
        apply Nat.le_min.mpr
        constructor
        · have := Finset.card_le_univ ((Rn N h C ×ˢ Sn N h C).image (fun c : Fin N × Fin N => c.2 - c.1))
          simpa using this
        · refine le_trans Finset.card_image_le ?_
          rw [Finset.card_product, Nat.le_div_iff_mul_le (by omega)]
          have hab : (Rn N h C).card + (Sn N h C).card ≤ B := by omega
          nlinarith [sq_nonneg ((Rn N h C).card - (Sn N h C).card : ℤ), hab]
      obtain ⟨T, hDT, _, hTc⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ _) hD0
        (by rw [Finset.card_univ, Fintype.card_fin]; exact Nat.min_le_left _ _)
      refine ⟨T, hTc, fun w s hs => hDT ?_⟩
      cases how : o w with
      | none => rw [how] at hs; cases hs
      | some c =>
        rw [how] at hs
        simp only [Option.map_some, Option.some.injEq] at hs
        have hc := ho2 w c how
        have h1 : c.1 ∈ Rn N h C := by
          rcases row_alt C hlegal.1 w c hc with h1 | h1
          · exact h1
          · omega
        have h2 : c.2 ∈ Sn N h C := by
          rcases col_alt C hlegal.1 w c hc with h2 | h2
          · exact h2
          · omega
        exact Finset.mem_image.mpr ⟨c, Finset.mem_product.mpr ⟨h1, h2⟩, hs⟩
    · have hK : min N (B ^ 2 / 4) = N := by
        apply Nat.min_eq_left
        rw [Nat.le_div_iff_mul_le (by omega)]
        have hBN : N ≤ B + 1 := by omega
        nlinarith
      exact ⟨Finset.univ, by rw [hK, Finset.card_univ, Fintype.card_fin], fun _ _ _ => Finset.mem_univ _⟩
  obtain ⟨T, hTc, hTσ⟩ := hT
  have hKN : min N (B ^ 2 / 4) ≤ N := Nat.min_le_left _ _
  generalize min N (B ^ 2 / 4) = K at hTc hKN ⊢
  have hq0 : ∀ s ∉ T, qw (fun w => (o w).map (fun c => c.2 - c.1)) P s = 0 := fun s hs =>
    qw_zero _ P s (fun w hw => hs (hTσ w s hw))
  obtain ⟨M, hMT, hMc, hM⟩ := small T (qw (fun w => (o w).map (fun c => c.2 - c.1)) P)
    (K - (t - (N - K))) (by omega)
  have hm : T.card - (K - (t - (N - K))) = t - (N - K) := by omega
  rw [hm] at hMc hM
  have hdisj : Disjoint M Tᶜ := by
    rw [Finset.disjoint_left]
    intro s hs hs'
    exact (Finset.mem_compl.mp hs') (hMT hs)
  have hcard : (M ∪ Tᶜ).card = M.card + (N - K) := by
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_compl, Fintype.card_fin, hTc]
  obtain ⟨U, hMU, hUsub, hUc⟩ := Finset.exists_subsuperset_card_eq (s := M) (t := M ∪ Tᶜ)
    Finset.subset_union_left (n := t) (by omega) (by omega)
  refine ⟨U, hUc, ?_⟩
  have hUq : ∑ s ∈ U, qw (fun w => (o w).map (fun c => c.2 - c.1)) P s =
      ∑ s ∈ M, qw (fun w => (o w).map (fun c => c.2 - c.1)) P s := by
    symm
    apply Finset.sum_subset hMU
    intro s hsU hsM
    apply hq0
    intro hsT
    rcases Finset.mem_union.mp (hUsub hsU) with h1 | h1
    · exact hsM h1
    · exact (Finset.mem_compl.mp h1) hsT
  have hTq : ∑ s, qw (fun w => (o w).map (fun c => c.2 - c.1)) P s =
      ∑ s ∈ T, qw (fun w => (o w).map (fun c => c.2 - c.1)) P s := by
    symm
    apply Finset.sum_subset (Finset.subset_univ T)
    intro s _ hs
    exact hq0 s hs
  have hloss : ∑ w, P w * (lossF (table N h C w) U : ℝ) = ((N * t : ℕ) : ℝ) +
      (∑ s, qw (fun w => (o w).map (fun c => c.2 - c.1)) P s -
        2 * ∑ s ∈ U, qw (fun w => (o w).map (fun c => c.2 - c.1)) P s) := by
    have h1 : ∀ w, P w * (lossF (table N h C w) U : ℝ) =
        ((N * t : ℕ) : ℝ) * P w + P w * dl ((o w).map (fun c => c.2 - c.1)) U := by
      intro w; rw [ho1 w U, hUc]; ring
    simp_rw [h1]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, mul_one, dl_sum]
  rw [hloss, hUq, hTq]
  have he0 : 0 ≤ ∑ s ∈ T, qw (fun w => (o w).map (fun c => c.2 - c.1)) P s :=
    Finset.sum_nonneg (fun s _ => qw_nonneg _ P hP s)
  have he1 : ∑ s ∈ T, qw (fun w => (o w).map (fun c => c.2 - c.1)) P s ≤ 1 := by
    rw [← hTq, ← hsum]; exact qw_total _ P hP
  have hqM0 : 0 ≤ ∑ s ∈ M, qw (fun w => (o w).map (fun c => c.2 - c.1)) P s :=
    Finset.sum_nonneg (fun s _ => qw_nonneg _ P hP s)
  rw [hTc] at hM
  by_cases hK0 : K = 0
  · subst hK0
    have hT0 : T = ∅ := Finset.card_eq_zero.mp hTc
    have hM0 : M = ∅ := by rw [hT0] at hMT; exact Finset.subset_empty.mp hMT
    rw [hT0, hM0]
    simp
  · have := final_ineq K N t (t - (N - K)) _ _ (by omega) ht hKN rfl he0 he1 hqM0 hM
    linarith

end Low
end PEqualNP.Outside.L_meta_32014_aux

namespace PEqualNP.Outside.L_meta_32014_aux
namespace Low

open PEqualNP.CircuitLowerBounds GB Ext Mux Sq Dec Loss Sp Cone
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)

variable {N : Nat} [NeZero N]

theorem contra (Nn tt e qM : ℝ) (h1 : e - 2 * qM ≤ -(2 * tt - Nn)) (h2 : (Nn - 1) * qM ≤ (tt - 1) * e)
    (heN : e ≤ Nn) (h2t : Nn + 1 ≤ 2 * tt) (htN : tt + 1 ≤ Nn) (hN : 1 ≤ Nn) : False := by
  have hA := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ Nn - 1)
  have hB := mul_le_mul_of_nonneg_right heN (by linarith : (0 : ℝ) ≤ 2 * tt - Nn - 1)
  nlinarith

theorem prod_bound (r a b : ℕ) (h : r * r ≤ a * b) : 2 * r ≤ a + b := by
  by_contra hlt
  have h1 : a + b + 1 ≤ 2 * r := by omega
  nlinarith [sq_nonneg ((a : ℤ) - b)]

theorem part3a (a t : Nat) (hN8 : 8 ≤ N) (hN : N = 2 ^ (2 * a)) (h2t : N < 2 * t) (htN : t < N)
    (C : Circuit) (hlegal : legal N (2 * a) C)
    (hone : ∀ w : Fin (2 * a) → Bool, lossF (table N (2 * a) C w) ∅ ≤ 1)
    (hrisk : ∀ U : Finset (Fin N), U.card = t →
      (∑ w : Fin (2 * a) → Bool, (lossF (table N (2 * a) C w) U : ℝ)) / (N : ℝ) ≤
        ((N * t : ℕ) : ℝ) - ((2 * t - N : ℕ) : ℝ) / (N : ℝ)) :
    2 * 2 ^ a + 2 * a ≤ C.size + 1 := by
  classical
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hcW : Fintype.card (Fin (2 * a) → Bool) = N := by simp [hN]
  choose o ho1 ho2 ho3 using fun w => classify (table N (2 * a) C w) (hone w)
  have hq : ∀ U : Finset (Fin N), U.card = t →
      (∑ s, qw (fun w => (o w).map (fun c => c.2 - c.1)) (fun _ => (1 : ℝ)) s) -
        2 * ∑ s ∈ U, qw (fun w => (o w).map (fun c => c.2 - c.1)) (fun _ => (1 : ℝ)) s ≤
          -(2 * (t : ℝ) - (N : ℝ)) := by
    intro U hU
    have h0 := hrisk U hU
    rw [div_le_iff₀ hNr, sub_mul, div_mul_cancel₀ _ (ne_of_gt hNr)] at h0
    have h1 : ∀ w, (lossF (table N (2 * a) C w) U : ℝ) =
        ((N * t : ℕ) : ℝ) + (fun _ => (1 : ℝ)) w * dl ((o w).map (fun c => c.2 - c.1)) U := by
      intro w; rw [ho1 w U, hU]; simp
    simp_rw [h1] at h0
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hcW,
      dl_sum (fun w => (o w).map (fun c => c.2 - c.1)) (fun _ => (1 : ℝ)) U] at h0
    rw [Nat.cast_sub (by omega : N ≤ 2 * t)] at h0
    simp only [nsmul_eq_mul] at h0
    push_cast at h0
    nlinarith
  have hetot : ∑ s, qw (fun w => (o w).map (fun c => c.2 - c.1)) (fun _ => (1 : ℝ)) s ≤ (N : ℝ) := by
    have := qw_total (fun w => (o w).map (fun c => c.2 - c.1)) (fun _ : Fin (2 * a) → Bool => (1 : ℝ))
      (fun _ => zero_le_one)
    simpa [hcW] using this

  have hsurj : ∀ s0 : Fin N, ∃ w, (o w).map (fun c => c.2 - c.1) = some s0 := by
    intro s0
    by_contra hne
    have hne' : ∀ w, (o w).map (fun c => c.2 - c.1) ≠ some s0 := fun w hw => hne ⟨w, hw⟩
    have hq0 := qw_zero (fun w => (o w).map (fun c => c.2 - c.1)) (fun _ => (1 : ℝ)) s0 hne'
    have hTc : (Finset.univ.erase s0).card = N - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    obtain ⟨M, hMT, hMc, hM⟩ := small (Finset.univ.erase s0)
      (qw (fun w => (o w).map (fun c => c.2 - c.1)) (fun _ => (1 : ℝ))) (N - t) (by omega)
    rw [hTc] at hMc hM
    have hs0M : s0 ∉ M := fun hm => (Finset.notMem_erase s0 _) (hMT hm)
    have hUc : (insert s0 M).card = t := by rw [Finset.card_insert_of_notMem hs0M]; omega
    have h1 := hq (insert s0 M) hUc
    rw [Finset.sum_insert hs0M, hq0, zero_add] at h1
    rw [Finset.sum_erase _ hq0] at hM
    have e1 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
    have e2 : ((N - 1 - (N - t) : ℕ) : ℝ) = (t : ℝ) - 1 := by
      have : N - 1 - (N - t) = t - 1 := by omega
      rw [this, Nat.cast_sub (by omega)]; simp
    rw [e1, e2] at hM
    have h2tr : (N : ℝ) + 1 ≤ 2 * (t : ℝ) := by exact_mod_cast h2t
    have htNr : (t : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast htN
    exact contra (N : ℝ) (t : ℝ) _ _ h1 hM hetot h2tr htNr (by exact_mod_cast hNpos)
  choose g hg using hsurj
  have hginj : Function.Injective g := by
    intro s s' hss
    have h1 := hg s
    rw [hss, hg s'] at h1
    exact (Option.some.inj h1).symm
  have hgbij : Function.Bijective g := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hginj, by rw [Fintype.card_fin, hcW]⟩
  have hsome : ∀ w, ∃ c, o w = some c := by
    intro w
    obtain ⟨s, rfl⟩ := hgbij.2 w
    have h1 := hg s
    cases hog : o (g s) with
    | none => rw [hog] at h1; cases h1
    | some c => exact ⟨c, rfl⟩
  have hcellinj : ∀ w w' c, o w = some c → o w' = some c → w = w' := by
    intro w w' c hw hw'
    obtain ⟨s, rfl⟩ := hgbij.2 w
    obtain ⟨s', rfl⟩ := hgbij.2 w'
    have h1 := hg s
    have h2 := hg s'
    rw [hw] at h1
    rw [hw'] at h2
    rw [h1] at h2
    rw [Option.some.inj h2]

  have hseed : ∀ i : Fin (2 * a), N + N + i.val ∈ needSet (N + N + 2 * a) C := by
    intro i
    by_contra hi
    obtain ⟨c, hc⟩ := hsome (fun _ => false)
    obtain ⟨c', hc'⟩ := hsome (Function.update (fun _ => false) i true)
    have heq : ∀ x y, table N (2 * a) C (Function.update (fun _ => false) i true) x y =
        table N (2 * a) C (fun _ => false) x y := by
      intro x y
      apply indep C hlegal.1 x x y y _ _ (Or.inl rfl) (Or.inl rfl)
      intro k
      by_cases hk : k = i
      · right; rw [hk]; exact hi
      · left; rw [Function.update_of_ne hk]
    have t1 : table N (2 * a) C (Function.update (fun _ => false) i true) c'.1 c'.2 = true :=
      (ho2 _ c' hc' c'.1 c'.2).mpr rfl
    rw [heq] at t1
    have hcc : c' = c := (ho2 _ c hc c'.1 c'.2).mp t1
    rw [hcc] at hc'
    have := congrFun (hcellinj _ _ c hc hc') i
    simp at this

  have hRS : 2 * 2 ^ a ≤ (Rn N (2 * a) C).card + (Sn N (2 * a) C).card := by
    have hr : N = 2 ^ a * 2 ^ a := by rw [hN, ← Nat.pow_add]; congr 1; omega
    have hr3 : 3 ≤ 2 ^ a := by
      by_contra hlt
      have h2 : 2 ^ a ≤ 2 := by omega
      have h4 := Nat.mul_le_mul h2 h2
      rw [← hr] at h4
      omega
    have hbig : 2 * 2 ^ a + 1 ≤ N := by
      have h3 := Nat.mul_le_mul_right (2 ^ a) hr3
      rw [← hr] at h3
      omega
    by_cases hA : ∀ w c, o w = some c → c.1 ∈ Rn N (2 * a) C ∧ c.2 ∈ Sn N (2 * a) C
    · choose cell hcell using hsome
      have hle := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin (2 * a) → Bool)))
        (t := Rn N (2 * a) C ×ˢ Sn N (2 * a) C) cell
        (fun w _ => Finset.mem_product.mpr (hA w (cell w) (hcell w)))
        (fun w _ w' _ hww => hcellinj w w' (cell w) (hcell w) (by rw [hww]; exact hcell w'))
      rw [Finset.card_univ, hcW, Finset.card_product] at hle
      exact prod_bound _ _ _ (le_of_eq_of_le hr.symm hle)
    · rw [not_forall] at hA
      obtain ⟨w, hA⟩ := hA
      rw [not_forall] at hA
      obtain ⟨c, hA⟩ := hA
      rw [Classical.not_imp] at hA
      obtain ⟨hwc, hA⟩ := hA
      have hc := ho2 w c hwc
      by_cases h1 : c.1 ∈ Rn N (2 * a) C
      · have h2 : c.2 ∉ Sn N (2 * a) C := fun h2 => hA ⟨h1, h2⟩
        rcases col_alt C hlegal.1 w c hc with h3 | h3
        · exact absurd h3 h2
        · omega
      · rcases row_alt C hlegal.1 w c hc with h3 | h3
        · exact absurd h3 h1
        · omega
  have hneed := need_card (N + N + 2 * a) C (fun g hg => (hlegal.2.2 g hg).1)
  have hinj2 : Function.Injective (fun y : Fin N => N + y.val) := by
    intro y y' e
    apply Fin.ext
    simp only at e
    omega
  have hinj3 : Function.Injective (fun i : Fin (2 * a) => N + N + i.val) := by
    intro y y' e
    apply Fin.ext
    simp only at e
    omega
  have hsub : ((Rn N (2 * a) C).image (fun x : Fin N => x.val) ∪
      (Sn N (2 * a) C).image (fun y : Fin N => N + y.val)) ∪
      (Finset.univ : Finset (Fin (2 * a))).image (fun i : Fin (2 * a) => N + N + i.val) ⊆
        needSet (N + N + 2 * a) C := by
    intro j hj
    rcases Finset.mem_union.mp hj with hj | hj
    · rcases Finset.mem_union.mp hj with hj | hj
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hj
        exact (Finset.mem_filter.mp hx).2
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hj
        exact (Finset.mem_filter.mp hy).2
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
      exact hseed i
  have hd1 : Disjoint ((Rn N (2 * a) C).image (fun x : Fin N => x.val))
      ((Sn N (2 * a) C).image (fun y : Fin N => N + y.val)) := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨y, _, hy⟩ := Finset.mem_image.mp h2
    have := x.isLt
    omega
  have hd2 : Disjoint ((Rn N (2 * a) C).image (fun x : Fin N => x.val) ∪
      (Sn N (2 * a) C).image (fun y : Fin N => N + y.val))
      ((Finset.univ : Finset (Fin (2 * a))).image (fun i : Fin (2 * a) => N + N + i.val)) := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h2
    rcases Finset.mem_union.mp h1 with h1 | h1
    · obtain ⟨x, _, hx⟩ := Finset.mem_image.mp h1
      have := x.isLt
      omega
    · obtain ⟨y, _, hy⟩ := Finset.mem_image.mp h1
      have := y.isLt
      omega
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1,
    Finset.card_image_of_injective _ Fin.val_injective, Finset.card_image_of_injective _ hinj2,
    Finset.card_image_of_injective _ hinj3, Finset.card_univ, Fintype.card_fin] at hcard
  omega

end Low
end PEqualNP.Outside.L_meta_32014_aux

namespace PEqualNP.Outside.L_meta_32014_aux
namespace Fin0

open Loss Sp Low

theorem main : (∀ (N t B : ℕ), 8 ≤ N → t ≤ N →
  let X := Fin N
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let legal := fun (h : ℕ) (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N+h) C ∧ C.output < N+N+h+C.size ∧
    ∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ (g.op = .not ∧ g.inputs.length = 1))
  let uses := fun (C : Circ) (j : ℕ) => C.output = j ∨ ∃ g ∈ C.gates, j ∈ g.inputs
  let named := fun (C : Circ) (R S : Finset X) =>
    (∀ x : X, uses C x.val → x ∈ R) ∧ (∀ y : X, uses C (N+y.val) → y ∈ S)
  let table := fun (h : ℕ) (C : Circ) (w : Fin h → Bool) (x y : X) =>
    C.eval (PEqualNP.Represents.oneEach x y ++ List.ofFn w)
  let code := fun (h j : ℕ) (i : Fin h) => j.testBit i.val
  let loss := fun (H : X → X → Bool) (U : Finset X) =>
    ((Finset.univ : Finset (X × X)).filter (fun z =>
      H z.1 z.2 ≠ decide (z.2-z.1 ∈ U))).card
  let fits := fun (h : ℕ) (C : Circ) (budget : ℕ) =>
    legal h C ∧ (∃ R S : Finset X, named C R S ∧ R.card+S.card ≤ budget) ∧
    ∀ w : Fin h → Bool, loss (table h C w) ∅ ≤ 1
  let K := min N (B^2/4)
  let value := ((N*t : ℕ) : ℝ) - ((K-2*(N-t) : ℕ) : ℝ)/(K : ℝ)
  (∀ (h : ℕ) (C : Circ) (P : (Fin h → Bool) → ℝ),
    fits h C B → (∀ w, 0 ≤ P w) → (∑ w, P w) = 1 →
    ∃ U : Finset X, U.card = t ∧ value ≤ ∑ w, P w * (loss (table h C w) U : ℝ)) ∧
  (∃ (p h : ℕ) (C : Circ), 0 < p ∧ p ≤ N ∧ p ≤ 2^h ∧ 2^h ≤ 2*p ∧
    fits h C B ∧ C.size ≤ 10*p+h+2 ∧
    ∀ U : Finset X, U.card = t →
      (∑ j : Fin p, (loss (table h C (code h j.val)) U : ℝ))/(p : ℝ) ≤ value) ∧
  ∀ a : ℕ, N = 2^(2*a) → N < 2*t → t < N →
    let r := 2^a
    let h := 2*a
    let ideal := ((N*t : ℕ) : ℝ) - ((2*t-N : ℕ) : ℝ)/(N : ℝ)
    let risk := fun (C : Circ) (U : Finset X) =>
      (∑ w : Fin h → Bool, (loss (table h C w) U : ℝ))/(N : ℝ)
    (∀ C : Circ, legal h C → (∀ w : Fin h → Bool, loss (table h C w) ∅ ≤ 1) →
      (∀ U : Finset X, U.card = t → risk C U ≤ ideal) → 2*r+h ≤ C.size+1) ∧
    ∃ C : Circ, fits h C (2*r) ∧ C.size ≤ 6*(r-1)+h+1 ∧
      ∀ U : Finset X, U.card = t → risk C U = ideal) := by
  intro N t B hN8 ht
  haveI : NeZero N := ⟨by omega⟩
  intro X Circ legal uses named table code loss fits K value
  refine ⟨?_, ?_, ?_⟩
  · intro h C P hfit hP hsum
    exact part1 t B hN8 ht h C P hfit hP hsum
  · exact part2 t B ht
  · intro a hN h2t htN r h ideal risk
    refine ⟨fun C hl h1 hr => ?_, ?_⟩
    · exact part3a a t hN8 hN h2t htN C hl h1 hr
    · exact part3b a t hN h2t

end Fin0
end PEqualNP.Outside.L_meta_32014_aux

theorem PEqualNP.Outside.L_meta_32014 : (∀ (N t B : ℕ), 8 ≤ N → t ≤ N →
  let X := Fin N
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let legal := fun (h : ℕ) (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N+h) C ∧ C.output < N+N+h+C.size ∧
    ∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ (g.op = .not ∧ g.inputs.length = 1))
  let uses := fun (C : Circ) (j : ℕ) => C.output = j ∨ ∃ g ∈ C.gates, j ∈ g.inputs
  let named := fun (C : Circ) (R S : Finset X) =>
    (∀ x : X, uses C x.val → x ∈ R) ∧ (∀ y : X, uses C (N+y.val) → y ∈ S)
  let table := fun (h : ℕ) (C : Circ) (w : Fin h → Bool) (x y : X) =>
    C.eval (PEqualNP.Represents.oneEach x y ++ List.ofFn w)
  let code := fun (h j : ℕ) (i : Fin h) => j.testBit i.val
  let loss := fun (H : X → X → Bool) (U : Finset X) =>
    ((Finset.univ : Finset (X × X)).filter (fun z =>
      H z.1 z.2 ≠ decide (z.2-z.1 ∈ U))).card
  let fits := fun (h : ℕ) (C : Circ) (budget : ℕ) =>
    legal h C ∧ (∃ R S : Finset X, named C R S ∧ R.card+S.card ≤ budget) ∧
    ∀ w : Fin h → Bool, loss (table h C w) ∅ ≤ 1
  let K := min N (B^2/4)
  let value := ((N*t : ℕ) : ℝ) - ((K-2*(N-t) : ℕ) : ℝ)/(K : ℝ)
  (∀ (h : ℕ) (C : Circ) (P : (Fin h → Bool) → ℝ),
    fits h C B → (∀ w, 0 ≤ P w) → (∑ w, P w) = 1 →
    ∃ U : Finset X, U.card = t ∧ value ≤ ∑ w, P w * (loss (table h C w) U : ℝ)) ∧
  (∃ (p h : ℕ) (C : Circ), 0 < p ∧ p ≤ N ∧ p ≤ 2^h ∧ 2^h ≤ 2*p ∧
    fits h C B ∧ C.size ≤ 10*p+h+2 ∧
    ∀ U : Finset X, U.card = t →
      (∑ j : Fin p, (loss (table h C (code h j.val)) U : ℝ))/(p : ℝ) ≤ value) ∧
  ∀ a : ℕ, N = 2^(2*a) → N < 2*t → t < N →
    let r := 2^a
    let h := 2*a
    let ideal := ((N*t : ℕ) : ℝ) - ((2*t-N : ℕ) : ℝ)/(N : ℝ)
    let risk := fun (C : Circ) (U : Finset X) =>
      (∑ w : Fin h → Bool, (loss (table h C w) U : ℝ))/(N : ℝ)
    (∀ C : Circ, legal h C → (∀ w : Fin h → Bool, loss (table h C w) ∅ ≤ 1) →
      (∀ U : Finset X, U.card = t → risk C U ≤ ideal) → 2*r+h ≤ C.size+1) ∧
    ∃ C : Circ, fits h C (2*r) ∧ C.size ≤ 6*(r-1)+h+1 ∧
      ∀ U : Finset X, U.card = t → risk C U = ideal) :=
  PEqualNP.Outside.L_meta_32014_aux.Fin0.main
