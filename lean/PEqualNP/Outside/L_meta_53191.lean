import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_53191
open PEqualNP.CircuitLowerBounds
def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def W (gs : List Gate) (x : List Bool) : List Bool := gs.foldl stp x
theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) : W (gs ++ [g]) x = stp (W gs x) g := by
  simp [W, List.foldl_append]
theorem W_len (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [stp, ih]; omega
theorem getD_app_l (l l' : List Bool) (i : ℕ) (h : i < l.length) : (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
theorem getD_app_m (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD_eq_getElem?_getD]
theorem getD_big (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
theorem W_lt (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (W gs x).getD i false = x.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih =>
    rw [W_snoc, stp, getD_app_l _ _ _ (by rw [W_len]; omega)]; exact ih
theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = W C.gates x := rfl
theorem W_stable (gs : List Gate) (g : Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (W (gs ++ [g]) x).getD i false = (W gs x).getD i false := by
  rw [W_snoc, stp, getD_app_l _ _ _ (by rw [W_len]; omega)]
theorem W_take (gs : List Gate) (x : List Bool) (k i : ℕ) (hi : i < x.length + k) :
    (W gs x).getD i false = (W (gs.take k) x).getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih =>
    by_cases hk : k ≤ gs.length
    · rw [List.take_append_of_le_length hk, W_stable _ _ _ _ (by omega)]; exact ih
    · rw [List.take_of_length_le (by simp; omega)]
theorem eval_mono (g : Gate) (h : g.op = GateOp.and ∨ g.op = GateOp.or) (w w' : List Bool)
    (hle : ∀ i ∈ g.inputs, w.getD i false = true → w'.getD i false = true)
    (hv : g.op.eval (g.inputs.map fun i => w.getD i false) = true) :
    g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  rcases h with h | h <;> rw [h] at hv ⊢
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, id] at hv ⊢
    intro i hi; exact hle i hi (hv i hi)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id] at hv ⊢
    obtain ⟨v, ⟨i, hi, rfl⟩, hv⟩ := hv
    exact ⟨true, ⟨i, hi, hle i hi hv⟩, rfl⟩
theorem W_mono (gs : List Gate) (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) (X Y : List Bool)
    (hl : X.length = Y.length)
    (hle : ∀ i, X.getD i false = true → Y.getD i false = true) :
    ∀ i, (W gs X).getD i false = true → (W gs Y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => simpa [W] using hle
  | append_singleton gs g ih =>
    have ih' := ih (fun g' hg' => hm g' (by simp [hg']))
    intro i
    rw [W_snoc, W_snoc]
    unfold stp
    have e1 : (W gs X).length = X.length + gs.length := W_len _ _
    have e2 : (W gs Y).length = X.length + gs.length := by rw [W_len, hl]
    rcases lt_trichotomy i (X.length + gs.length) with h | h | h
    · rw [getD_app_l _ _ _ (by omega), getD_app_l _ _ _ (by omega)]; exact ih' i
    · subst h
      have a1 := getD_app_m (W gs X) (g.op.eval (g.inputs.map fun i => (W gs X).getD i false))
      have a2 := getD_app_m (W gs Y) (g.op.eval (g.inputs.map fun i => (W gs Y).getD i false))
      rw [e1] at a1
      rw [e2] at a2
      rw [a1, a2]
      exact eval_mono g (hm g (by simp)) _ _ (fun k _ => ih' k)
    · rw [getD_big _ _ (by simp [e1]; omega)]
      intro hf
      exact absurd hf (by decide)
def Good (N : ℕ) (gs : List Gate) : Prop := ∀ j (hj : j < gs.length),
  ((gs[j]).op = GateOp.and ∨ (gs[j]).op = GateOp.or) ∧ (gs[j]).inputs.length ≤ 2 ∧
    ∀ i ∈ (gs[j]).inputs, i < N + j
theorem good_snoc (N : ℕ) (gs : List Gate) (g : Gate) (hg : Good N gs)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hl : g.inputs.length ≤ 2)
    (hi : ∀ i ∈ g.inputs, i < N + gs.length) : Good N (gs ++ [g]) := by
  intro j hj
  simp only [List.length_append, List.length_singleton] at hj
  rcases Nat.lt_or_ge j gs.length with h | h
  · rw [List.getElem_append_left h]; exact hg j h
  · have : j = gs.length := by omega
    subst this
    simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_singleton]
    exact ⟨hop, hl, hi⟩
theorem W_ext (gs gs' : List Gate) (h : ∃ t, gs' = gs ++ t) (x : List Bool) (i : ℕ)
    (hi : i < x.length + gs.length) : (W gs' x).getD i false = (W gs x).getD i false := by
  rw [W_take gs' x gs.length i hi]
  obtain ⟨t, rfl⟩ := h
  simp
theorem W_last (gs : List Gate) (g : Gate) (x : List Bool) :
    (W (gs ++ [g]) x).getD (x.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (W gs x).getD i false) := by
  rw [W_snoc, stp]
  have := getD_app_m (W gs x) (g.op.eval (g.inputs.map fun i => (W gs x).getD i false))
  rw [W_len] at this
  exact this
def Has {α : Type} (L : List (α → Bool)) (A : Finset α) (gs : List Gate) (f : α → Bool) : Prop :=
  ∃ j < L.length + gs.length, ∀ x ∈ A, (W gs (L.map fun g => g x)).getD j false = f x
theorem map_getD {α : Type} (L : List (α → Bool)) (x : α) (j : ℕ) (hj : j < L.length) :
    (L.map fun g => g x).getD j false = L[j] x := by
  simp [List.getD_eq_getElem?_getD, hj]
theorem has_inp {α : Type} (L : List (α → Bool)) (A : Finset α) (gs : List Gate) (g : α → Bool)
    (hg : g ∈ L) : Has L A gs g := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  refine ⟨j, by omega, fun x _ => ?_⟩
  rw [W_lt _ _ _ (by simpa using hj)]
  exact map_getD L x j hj
theorem has_ext {α : Type} (L : List (α → Bool)) (A : Finset α) (gs u : List Gate) (f : α → Bool)
    (h : Has L A gs f) : Has L A (gs ++ u) f := by
  obtain ⟨j, hj, hv⟩ := h
  refine ⟨j, by simp; omega, fun x hx => ?_⟩
  rw [W_ext gs (gs ++ u) ⟨u, rfl⟩ _ _ (by simpa using hj)]
  exact hv x hx
theorem has_congr {α : Type} (L : List (α → Bool)) (A : Finset α) (gs : List Gate) (f f' : α → Bool)
    (h : Has L A gs f) (he : ∀ x ∈ A, f x = f' x) : Has L A gs f' := by
  obtain ⟨j, hj, hv⟩ := h
  exact ⟨j, hj, fun x hx => (hv x hx).trans (he x hx)⟩
theorem has_gate {α : Type} (L : List (α → Bool)) (A : Finset α) (gs : List Gate) (f1 f2 : α → Bool)
    (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (hg : Good L.length gs)
    (h1 : Has L A gs f1) (h2 : Has L A gs f2) :
    ∃ g : Gate, Good L.length (gs ++ [g]) ∧ Has L A (gs ++ [g]) (fun x => op.eval [f1 x, f2 x]) := by
  obtain ⟨j1, hj1, v1⟩ := h1
  obtain ⟨j2, hj2, v2⟩ := h2
  refine ⟨⟨op, [j1, j2]⟩, good_snoc _ _ _ hg hop (by simp) (by intro i hi; simp at hi; omega),
    L.length + gs.length, by simp, fun x hx => ?_⟩
  have := W_last gs ⟨op, [j1, j2]⟩ (L.map fun g => g x)
  rw [List.length_map] at this
  rw [this]
  show op.eval [(W gs (L.map fun g => g x)).getD j1 false, (W gs (L.map fun g => g x)).getD j2 false] = _
  rw [v1 x hx, v2 x hx]
theorem has_const {α : Type} (L : List (α → Bool)) (A : Finset α) (gs : List Gate) (v : Bool)
    (hg : Good L.length gs) :
    ∃ g : Gate, Good L.length (gs ++ [g]) ∧ Has L A (gs ++ [g]) (fun _ => v) := by
  refine ⟨⟨if v then GateOp.and else GateOp.or, []⟩,
    good_snoc _ _ _ hg (by cases v <;> simp) (by simp) (by simp), L.length + gs.length, by simp,
    fun x _ => ?_⟩
  have := W_last gs ⟨if v then GateOp.and else GateOp.or, []⟩ (L.map fun g => g x)
  rw [List.length_map] at this
  rw [this]
  cases v <;> simp [GateOp.eval]
theorem level {α ι : Type} [DecidableEq ι] (L : List (α → Bool)) (A : Finset α) (φ : ι → α → Bool)
    (gs0 : List Gate) (T : Finset ι)
    (hT : ∀ t ∈ T, ∃ op : GateOp, ∃ f1 f2 : α → Bool, (op = GateOp.and ∨ op = GateOp.or) ∧
      Has L A gs0 f1 ∧ Has L A gs0 f2 ∧ ∀ x ∈ A, φ t x = op.eval [f1 x, f2 x]) :
    ∀ gs, Good L.length gs → (∃ u, gs = gs0 ++ u) → ∃ gs', Good L.length gs' ∧ (∃ u, gs' = gs ++ u) ∧
      gs'.length ≤ gs.length + T.card ∧ ∀ t ∈ T, Has L A gs' (φ t) := by
  induction T using Finset.induction_on with
  | empty => intro gs hg _; exact ⟨gs, hg, ⟨[], by simp⟩, by simp, by simp⟩
  | @insert t0 T ht0 ih =>
    intro gs hg hgs
    obtain ⟨gs1, hg1, ⟨u1, rfl⟩, hl1, hh1⟩ :=
      ih (fun t ht => hT t (Finset.mem_insert_of_mem ht)) gs hg hgs
    obtain ⟨op, f1, f2, hop, h1, h2, he⟩ := hT t0 (Finset.mem_insert_self _ _)
    obtain ⟨u0, rfl⟩ := hgs
    have h1' : Has L A (gs0 ++ u0 ++ u1) f1 := by
      rw [List.append_assoc]; exact has_ext L A gs0 (u0 ++ u1) f1 h1
    have h2' : Has L A (gs0 ++ u0 ++ u1) f2 := by
      rw [List.append_assoc]; exact has_ext L A gs0 (u0 ++ u1) f2 h2
    obtain ⟨g, hg2, hh2⟩ := has_gate L A _ f1 f2 op hop hg1 h1' h2'
    refine ⟨_, hg2, ⟨u1 ++ [g], by simp⟩, ?_, ?_⟩
    · simp only [List.length_append, List.length_singleton] at hl1 ⊢
      rw [Finset.card_insert_of_notMem ht0]; omega
    · intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact has_congr L A _ _ _ hh2 (fun x hx => (he x hx).symm)
      · exact has_ext L A _ [g] _ (hh1 t ht)
def Bld {α : Type} (L : List (α → Bool)) (A : Finset α) (f : α → Bool) : Prop :=
  ∀ gs, Good L.length gs → ∃ gs', Good L.length gs' ∧ (∃ u, gs' = gs ++ u) ∧ Has L A gs' f
theorem bld_inp {α : Type} (L : List (α → Bool)) (A : Finset α) (g : α → Bool) (hg : g ∈ L) :
    Bld L A g := fun gs hgs => ⟨gs, hgs, ⟨[], by simp⟩, has_inp L A gs g hg⟩
theorem bld_bin {α : Type} (L : List (α → Bool)) (A : Finset α) (f1 f2 : α → Bool) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or) (h1 : Bld L A f1) (h2 : Bld L A f2) :
    Bld L A (fun x => op.eval [f1 x, f2 x]) := by
  intro gs hgs
  obtain ⟨gs1, hg1, ⟨u1, rfl⟩, hh1⟩ := h1 gs hgs
  obtain ⟨gs2, hg2, ⟨u2, rfl⟩, hh2⟩ := h2 _ hg1
  obtain ⟨g, hg3, hh3⟩ := has_gate L A _ f1 f2 op hop hg2 (has_ext L A _ u2 f1 hh1) hh2
  exact ⟨_, hg3, ⟨u1 ++ u2 ++ [g], by simp⟩, hh3⟩
theorem bld_const {α : Type} (L : List (α → Bool)) (A : Finset α) (v : Bool) :
    Bld L A (fun _ => v) := by
  intro gs hgs
  obtain ⟨g, hg, hh⟩ := has_const L A gs v hgs
  exact ⟨_, hg, ⟨[g], rfl⟩, hh⟩
theorem bld_congr {α : Type} (L : List (α → Bool)) (A : Finset α) (f f' : α → Bool) (h : Bld L A f)
    (he : ∀ x ∈ A, f x = f' x) : Bld L A f' := by
  intro gs hgs
  obtain ⟨gs', h1, h2, h3⟩ := h gs hgs
  exact ⟨gs', h1, h2, has_congr L A _ _ _ h3 he⟩
theorem bld_andL {α : Type} (L : List (α → Bool)) (A : Finset α) (l : List (α → Bool))
    (hl : ∀ g ∈ l, Bld L A g) : Bld L A (fun x => l.all (fun g => g x)) := by
  induction l with
  | nil => exact bld_congr L A _ _ (bld_const L A true) (fun x _ => by simp)
  | cons g0 l ih =>
    have := bld_bin L A _ _ GateOp.and (Or.inl rfl) (hl g0 (by simp))
      (ih (fun g hg => hl g (by simp [hg])))
    exact bld_congr L A _ _ this (fun x _ => by simp [GateOp.eval])
theorem bld_orL {α : Type} (L : List (α → Bool)) (A : Finset α) (l : List (α → Bool))
    (hl : ∀ g ∈ l, Bld L A g) : Bld L A (fun x => l.any (fun g => g x)) := by
  induction l with
  | nil => exact bld_congr L A _ _ (bld_const L A false) (fun x _ => by simp)
  | cons g0 l ih =>
    have := bld_bin L A _ _ GateOp.or (Or.inr rfl) (hl g0 (by simp))
      (ih (fun g hg => hl g (by simp [hg])))
    exact bld_congr L A _ _ this (fun x _ => by simp [GateOp.eval])
theorem bld_all {α : Type} (L : List (α → Bool)) (A : Finset α) (l : List (α → Bool))
    (hl : ∀ g ∈ l, Bld L A g) : ∀ gs, Good L.length gs →
    ∃ gs', Good L.length gs' ∧ (∃ u, gs' = gs ++ u) ∧ ∀ g ∈ l, Has L A gs' g := by
  induction l with
  | nil => intro gs hgs; exact ⟨gs, hgs, ⟨[], by simp⟩, by simp⟩
  | cons g0 l ih =>
    intro gs hgs
    obtain ⟨gs1, hg1, ⟨u1, rfl⟩, hh1⟩ := ih (fun g hg => hl g (by simp [hg])) gs hgs
    obtain ⟨gs2, hg2, ⟨u2, rfl⟩, hh2⟩ := hl g0 (by simp) _ hg1
    refine ⟨_, hg2, ⟨u1 ++ u2, by simp⟩, fun g hg => ?_⟩
    rcases List.mem_cons.mp hg with rfl | hg
    · exact hh2
    · exact has_ext L A _ u2 g (hh1 g hg)
theorem bld_sep {α : Type} (L : List (α → Bool)) (A : Finset α)
    (hsep : ∀ y ∈ A, ∀ x ∈ A, (∀ g ∈ L, g y = true → g x = true) → y = x) (f : α → Bool) :
    Bld L A f := by
  have ho := bld_orL L A ((A.toList.filter (fun y => f y)).map
    (fun y => fun x => (L.filter (fun g => g y)).all (fun g => g x)))
    (fun h hh => by
      simp only [List.mem_map] at hh
      obtain ⟨y, _, rfl⟩ := hh
      exact bld_andL L A _ (fun g hg => bld_inp L A g (List.mem_filter.mp hg).1))
  refine bld_congr L A _ _ ho (fun x hx => ?_)
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true, List.mem_map, List.mem_filter, Finset.mem_toList]
  constructor
  · rintro ⟨h, ⟨y, ⟨hy, hfy⟩, rfl⟩, hyx⟩
    simp only [List.all_eq_true, List.mem_filter] at hyx
    have := hsep y hy x hx (fun g hg hgy => hyx g ⟨hg, hgy⟩)
    subst this; exact hfy
  · intro hfx
    refine ⟨_, ⟨x, ⟨hx, hfx⟩, rfl⟩, ?_⟩
    simp only [List.all_eq_true, List.mem_filter]
    exact fun g hg => hg.2
theorem pack {α : Type} (L : List (α → Bool)) (A : Finset α) (need : Finset (α → Bool)) (gs : List Gate)
    (hg : Good L.length gs) (hL0 : 0 < L.length) (hh : ∀ f ∈ need, Has L A gs f) :
    ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack L.length C ∧
      C.output < L.length + C.size ∧ C.size = gs.length ∧ ∀ f ∈ need, ∃ j < L.length + C.size,
        ∀ x ∈ A, (C.wires (L.map (fun g => g x))).getD j false = f x := by
  refine ⟨⟨gs, 0⟩, ?_, ?_, ?_, rfl, ?_⟩
  · intro g hgm
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hgm
    obtain ⟨h1, h2, _⟩ := hg j hj
    exact ⟨by rcases h1 with h | h <;> simp [h], h2⟩
  · intro j hj i hi
    have e : PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs, 0⟩ j = gs[j] := by
      simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hj]
    rw [e] at hi
    exact (hg j hj).2.2 i hi
  · simp only [Circuit.size]; omega
  · intro f hf
    exact hh f hf
theorem lower {α ι : Type} (L : List (α → Bool)) (A : Finset α) (C : Circuit) (Sl : Finset ι)
    (σ : ι → α → Bool)
    (hC : ∀ s ∈ Sl, ∃ j < L.length + C.size, ∀ x ∈ A, (C.wires (L.map (fun g => g x))).getD j false = σ s x)
    (hinj : ∀ s ∈ Sl, ∀ s' ∈ Sl, (∀ x ∈ A, σ s x = σ s' x) → s = s')
    (hnot : ∀ s ∈ Sl, ∀ g ∈ L, ¬ ∀ x ∈ A, σ s x = g x) : Sl.card ≤ C.size := by
  classical
  have key : ∀ s, ∃ j, s ∈ Sl → (L.length ≤ j ∧ j < L.length + C.size ∧
      ∀ x ∈ A, (C.wires (L.map (fun g => g x))).getD j false = σ s x) := by
    intro s
    by_cases hs : s ∈ Sl
    · obtain ⟨j, hj, hv⟩ := hC s hs
      refine ⟨j, fun _ => ⟨?_, hj, hv⟩⟩
      by_contra hlt
      have hlt' : j < L.length := by omega
      apply hnot s hs L[j] (List.getElem_mem _)
      intro x hx
      rw [← hv x hx, wires_eq, W_lt C.gates (L.map fun g => g x) j (by simpa using hlt'),
        map_getD L x j hlt']
    · exact ⟨0, fun h => absurd h hs⟩
  choose j hj using key
  have hmaps : ∀ s ∈ Sl, j s ∈ Finset.Ico L.length (L.length + C.size) := fun s hs => by
    simp only [Finset.mem_Ico]; exact ⟨(hj s hs).1, (hj s hs).2.1⟩
  have hinj' : Set.InjOn j Sl := by
    intro s hs s' hs' he
    apply hinj s hs s' hs'
    intro x hx
    rw [← (hj s hs).2.2 x hx, ← (hj s' hs').2.2 x hx, he]
  have := Finset.card_le_card_of_injOn j (fun s hs => hmaps s hs) hinj'
  simpa using this
def aa (m : ℕ) (i : Fin m) : Fin (m+m) := Fin.castAdd m i
def bb (m : ℕ) (i : Fin m) : Fin (m+m) := Fin.natAdd m i
def nf (m : ℕ) (v : Fin (m+m)) : Finset (Fin (m+m)) → Bool := fun x => !decide (v ∈ x)
def atom (m : ℕ) (i : Fin m) : Option Bool → Finset (Fin (m+m)) → Bool
  | none => fun x => !decide (aa m i ∈ x) && !decide (bb m i ∈ x)
  | some false => fun x => decide (aa m i ∈ x) && !decide (bb m i ∈ x)
  | some true => fun x => !decide (aa m i ∈ x) && decide (bb m i ∈ x)
def sameF (m : ℕ) (i : Fin m) : Finset (Fin (m+m)) → Bool :=
  fun x => !(xor (decide (aa m i ∈ x)) (decide (bb m i ∈ x)))
def nsameF (m : ℕ) (i : Fin m) : Finset (Fin (m+m)) → Bool :=
  fun x => xor (decide (aa m i ∈ x)) (decide (bb m i ∈ x))
def IsRaw (m : ℕ) (g : Finset (Fin (m+m)) → Bool) : Prop :=
  g = (fun _ => false) ∨ g = (fun _ => true) ∨ (∃ v : Fin (m+m), g = fun x => decide (v ∈ x)) ∨
  (∃ i : Fin m, g = sameF m i) ∨ (∃ i : Fin m, g = nsameF m i)
def Keeps (m : ℕ) (L : Finset (Fin (m+m)) → List (Finset (Fin (m+m)) → Bool))
    (need : Finset (Finset (Fin (m+m)) → Bool)) (A : Finset (Finset (Fin (m+m)))) : Prop :=
  ∀ (S : Finset (Fin (m+m))) (p : ℕ),
    (∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (L S).length C ∧
      C.output < (L S).length + C.size ∧ C.size ≤ p ∧ ∀ f ∈ need, ∃ j < (L S).length + C.size,
        ∀ x ∈ A, (C.wires ((L S).map (fun g => g x))).getD j false = f x) ↔
    ((∀ i : Fin m, aa m i ∈ S ∨ bb m i ∈ S) ∧ m+m+3*m-S.card ≤ p)
def GoodF (m t : ℕ) (dq : DecidableEq (Fin t)) (f : Fin m × Bool → Finset (Fin t)) : Prop :=
  Function.Injective f ∧ (∀ k, (f k).Nonempty) ∧
    (∀ i, Disjoint (f (i,false)) (f (i,true)) ∧ f (i,false) ∪ f (i,true) ≠ Finset.univ) ∧
    ∀ k i, f k ≠ f (i,false) ∪ f (i,true) ∧ f k ≠ Finset.univ \ (f (i,false) ∪ f (i,true))
theorem ca_ne_na {m : ℕ} (i j : Fin m) : aa m i ≠ bb m j := by
  intro h; have h1 := congrArg Fin.val h
  simp only [aa, bb, Fin.val_castAdd, Fin.val_natAdd] at h1; have := i.isLt; omega
theorem na_ne_ca {m : ℕ} (i j : Fin m) : bb m j ≠ aa m i :=
  fun h => ca_ne_na i j h.symm
theorem ca_inj {m : ℕ} (i j : Fin m) : aa m i = aa m j ↔ i = j := by
  constructor
  · intro h; ext; have h1 := congrArg Fin.val h; simpa [aa] using h1
  · rintro rfl; rfl
theorem na_inj {m : ℕ} (i j : Fin m) : bb m i = bb m j ↔ i = j := by
  constructor
  · intro h; ext; have h1 := congrArg Fin.val h; simp only [bb, Fin.val_natAdd] at h1; omega
  · rintro rfl; rfl
theorem sx (p q : Prop) [Decidable p] [Decidable q] : xor (decide p) (decide q) = true ↔ ¬(p ↔ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]
theorem snx (p q : Prop) [Decidable p] [Decidable q] : (!xor (decide p) (decide q)) = true ↔ (p ↔ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]
theorem raw0 (m : ℕ) : IsRaw m (fun _ => false) := Or.inl rfl
theorem raw1 (m : ℕ) : IsRaw m (fun _ => true) := Or.inr (Or.inl rfl)
theorem rawb (m : ℕ) (v : Fin (m+m)) : IsRaw m (fun x => decide (v ∈ x)) := Or.inr (Or.inr (Or.inl ⟨v, rfl⟩))
theorem raws (m : ℕ) (i : Fin m) : IsRaw m (sameF m i) := Or.inr (Or.inr (Or.inr (Or.inl ⟨i, rfl⟩)))
theorem rawn (m : ℕ) (i : Fin m) : IsRaw m (nsameF m i) := Or.inr (Or.inr (Or.inr (Or.inr ⟨i, rfl⟩)))
def PP (m : ℕ) (A : Finset (Finset (Fin (m+m)))) (i : Fin m) : Prop :=
  ∃ z ∈ A, aa m i ∉ z ∧ bb m i ∉ z ∧
    insert (aa m i) (insert (bb m i) z) ∈ A
def prof (m : ℕ) (x : Finset (Fin (m+m))) : Fin m × Bool → Bool := fun k => atom m k.1 (some k.2) x
theorem cheap (m : ℕ) (hm : 0 < m) (L : Finset (Fin (m+m)) → List (Finset (Fin (m+m)) → Bool))
    (need : Finset (Finset (Fin (m+m)) → Bool))
    (hL : ∀ S g, g ∈ L S ↔ IsRaw m g ∨ ∃ v ∈ S, g = nf m v)
    (hN : ∀ f, f ∈ need ↔ (∃ v, f = nf m v) ∨ ∃ i o, f = atom m i o)
    (A : Finset (Finset (Fin (m+m)))) (hk : Keeps m L need A)
    (k0 : Fin m × Option Bool) (g : Finset (Fin (m+m)) → Bool)
    (hg : g ∈ L Finset.univ ∨ ∃ k', k' ≠ k0 ∧ g = atom m k'.1 k'.2)
    (heq : ∀ x ∈ A, atom m k0.1 k0.2 x = g x) : False := by
  have hinp : ∀ g, IsRaw m g → g ∈ L Finset.univ := fun g h => (hL _ g).mpr (Or.inl h)
  have hneg : ∀ v, nf m v ∈ L Finset.univ := fun v => (hL _ _).mpr (Or.inr ⟨v, Finset.mem_univ _, rfl⟩)
  have hbit : ∀ v, (fun x => decide (v ∈ x)) ∈ L Finset.univ := fun v => hinp _ (rawb m v)
  have hT : ∀ k ∈ Finset.univ.erase k0, ∃ op : GateOp, ∃ f1 f2 : Finset (Fin (m+m)) → Bool,
      (op = GateOp.and ∨ op = GateOp.or) ∧ Has (L Finset.univ) A [] f1 ∧ Has (L Finset.univ) A [] f2 ∧
      ∀ x ∈ A, (fun k : Fin m × Option Bool => atom m k.1 k.2) k x = op.eval [f1 x, f2 x] := by
    rintro ⟨i, o⟩ _
    rcases o with _ | ⟨_ | _⟩
    · exact ⟨GateOp.and, nf m (aa m i), nf m (bb m i), Or.inl rfl,
        has_inp _ _ _ _ (hneg _), has_inp _ _ _ _ (hneg _), fun x _ => by simp [atom, nf, GateOp.eval]⟩
    · exact ⟨GateOp.and, (fun x => decide (aa m i ∈ x)), nf m (bb m i), Or.inl rfl,
        has_inp _ _ _ _ (hbit _), has_inp _ _ _ _ (hneg _), fun x _ => by simp [atom, nf, GateOp.eval]⟩
    · exact ⟨GateOp.and, nf m (aa m i), (fun x => decide (bb m i ∈ x)), Or.inl rfl,
        has_inp _ _ _ _ (hneg _), has_inp _ _ _ _ (hbit _), fun x _ => by simp [atom, nf, GateOp.eval]⟩
  obtain ⟨gs, hgs, _, hlen, hh⟩ := level (L Finset.univ) A (fun k : Fin m × Option Bool => atom m k.1 k.2)
    [] _ hT [] (fun j hj => absurd hj (by simp)) ⟨[], rfl⟩
  have hk0 : Has (L Finset.univ) A gs (atom m k0.1 k0.2) := by
    rcases hg with hg | ⟨k', hk', rfl⟩
    · exact has_congr _ _ _ _ _ (has_inp _ _ _ _ hg) (fun x hx => (heq x hx).symm)
    · exact has_congr _ _ _ _ _ (hh k' (Finset.mem_erase.mpr ⟨hk', Finset.mem_univ _⟩))
        (fun x hx => (heq x hx).symm)
  have hall : ∀ f ∈ need, Has (L Finset.univ) A gs f := by
    intro f hf
    rcases (hN f).mp hf with ⟨v, rfl⟩ | ⟨i, o, rfl⟩
    · exact has_inp _ _ _ _ (hneg v)
    · by_cases hio : (i, o) = k0
      · subst hio; exact hk0
      · exact hh (i, o) (Finset.mem_erase.mpr ⟨hio, Finset.mem_univ _⟩)
  have hL0 : 0 < (L Finset.univ).length := List.length_pos_of_mem (hinp _ (raw0 m))
  obtain ⟨C, h1, h2, h3, h4, h5⟩ := pack (L Finset.univ) A need gs hgs hL0 hall
  have hc2 : (Finset.univ.erase k0).card = m * 3 - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; simp
  simp only [List.length_nil, zero_add, hc2] at hlen
  have := (hk Finset.univ (3*m-1)).mp ⟨C, h1, h2, h3, by rw [h4]; omega, h5⟩
  obtain ⟨_, hp⟩ := this
  rw [Finset.card_univ, Fintype.card_fin] at hp
  omega
theorem fwd_a (m : ℕ) (hm : 0 < m) (L : Finset (Fin (m+m)) → List (Finset (Fin (m+m)) → Bool))
    (need : Finset (Finset (Fin (m+m)) → Bool))
    (hL : ∀ S g, g ∈ L S ↔ IsRaw m g ∨ ∃ v ∈ S, g = nf m v)
    (hN : ∀ f, f ∈ need ↔ (∃ v, f = nf m v) ∨ ∃ i o, f = atom m i o)
    (A : Finset (Finset (Fin (m+m)))) (hk : Keeps m L need A) :
    (∀ k k' : Fin m × Bool, (∀ x ∈ A, prof m x k = prof m x k') → k = k') ∧
    (∀ k, ∃ x ∈ A, prof m x k = true) ∧
    (∀ k i, ¬ ∀ x ∈ A, prof m x k = sameF m i x) ∧
    (∀ k i, ¬ ∀ x ∈ A, prof m x k = nsameF m i x) := by
  have hinp : ∀ g, IsRaw m g → g ∈ L Finset.univ := fun g h => (hL _ g).mpr (Or.inl h)
  refine ⟨fun k k' h => ?_, fun k => ?_, fun k i h => ?_, fun k i h => ?_⟩
  · by_contra hne
    refine cheap m hm L need hL hN A hk (k.1, some k.2) (atom m k'.1 (some k'.2))
      (Or.inr ⟨(k'.1, some k'.2), fun he => hne ?_, rfl⟩) (fun x hx => h x hx)
    obtain ⟨k1, k2⟩ := k
    obtain ⟨k1', k2'⟩ := k'
    simp only [Prod.mk.injEq, Option.some.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    rfl
  · by_contra hne
    simp only [not_exists, not_and, Bool.not_eq_true] at hne
    exact cheap m hm L need hL hN A hk (k.1, some k.2) (fun _ => false) (Or.inl (hinp _ (raw0 m)))
      (fun x hx => hne x hx)
  · exact cheap m hm L need hL hN A hk (k.1, some k.2) (sameF m i) (Or.inl (hinp _ (raws m i)))
      (fun x hx => h x hx)
  · exact cheap m hm L need hL hN A hk (k.1, some k.2) (nsameF m i) (Or.inl (hinp _ (rawn m i)))
      (fun x hx => h x hx)
theorem fwd_b (m : ℕ) (L : Finset (Fin (m+m)) → List (Finset (Fin (m+m)) → Bool))
    (need : Finset (Finset (Fin (m+m)) → Bool))
    (hL : ∀ S g, g ∈ L S ↔ IsRaw m g ∨ ∃ v ∈ S, g = nf m v)
    (A : Finset (Finset (Fin (m+m)))) (hk : Keeps m L need A) (i : Fin m) : PP m A i := by
  by_contra hpp
  have hmemS : ∀ v, v ∈ Finset.univ.filter (fun v => v ≠ aa m i ∧ v ≠ bb m i) ↔
      v ≠ aa m i ∧ v ≠ bb m i := by intro v; simp
  generalize Finset.univ.filter (fun v => v ≠ aa m i ∧ v ≠ bb m i) = S at hmemS
  have hsep : ∀ y ∈ A, ∀ x ∈ A, (∀ g ∈ L S, g y = true → g x = true) → y = x := by
    intro y hy x hx hyx
    have hbit : ∀ v, v ∈ y → v ∈ x := fun v hv => by
      have := hyx _ ((hL S _).mpr (Or.inl (rawb m v))) (by simpa using hv)
      simpa using this
    have hnegv : ∀ v ∈ S, v ∉ y → v ∉ x := fun v hv hvy => by
      have := hyx _ ((hL S _).mpr (Or.inr ⟨v, hv, rfl⟩)) (by simpa [nf] using hvy)
      simpa [nf] using this
    have hs : (aa m i ∈ y ↔ bb m i ∈ y) → (aa m i ∈ x ↔ bb m i ∈ x) :=
      fun h => by
        have := hyx _ ((hL S _).mpr (Or.inl (raws m i))) (by simp only [sameF, snx]; exact h)
        simp only [sameF, snx] at this; exact this
    have hns : ¬(aa m i ∈ y ↔ bb m i ∈ y) → ¬(aa m i ∈ x ↔ bb m i ∈ x) :=
      fun h => by
        have := hyx _ ((hL S _).mpr (Or.inl (rawn m i))) (by simp only [nsameF, sx]; exact h)
        simp only [nsameF, sx] at this; exact this
    have hother : ∀ v, v ≠ aa m i → v ≠ bb m i → (v ∈ y ↔ v ∈ x) := fun v h1 h2 =>
      ⟨hbit v, fun hvx => by by_contra hvy; exact hnegv v ((hmemS v).mpr ⟨h1, h2⟩) hvy hvx⟩
    have hnot : ¬(aa m i ∉ y ∧ bb m i ∉ y ∧ aa m i ∈ x ∧ bb m i ∈ x) := by
      rintro ⟨h1, h2, h3, h4⟩
      apply hpp
      refine ⟨y, hy, h1, h2, ?_⟩
      convert hx using 1
      ext v
      simp only [Finset.mem_insert]
      by_cases e1 : v = aa m i
      · subst e1; simp [h3]
      · by_cases e2 : v = bb m i
        · subst e2; simp [h4]
        · simp [e1, e2, hother v e1 e2]
    have ha := hbit (aa m i)
    have hb' := hbit (bb m i)
    ext v
    by_cases e1 : v = aa m i
    · subst e1; tauto
    · by_cases e2 : v = bb m i
      · subst e2; tauto
      · exact hother v e1 e2
  have hb_all : ∀ f ∈ need.toList, Bld (L S) A f := fun f _ => bld_sep (L S) A hsep f
  obtain ⟨gs, hgs, _, hh⟩ := bld_all (L S) A need.toList hb_all [] (fun j hj => absurd hj (by simp))
  have hL0 : 0 < (L S).length := List.length_pos_of_mem ((hL S _).mpr (Or.inl (raw0 m)))
  obtain ⟨C, h1, h2, h3, h4, h5⟩ := pack (L S) A need gs hgs hL0 (fun f hf => hh f (Finset.mem_toList.mpr hf))
  have := ((hk S C.size).mp ⟨C, h1, h2, h3, le_refl _, h5⟩).1 i
  rcases this with h | h <;> simp [hmemS] at h
def phi (m : ℕ) (i0 : Fin m) (z : Finset (Fin (m+m))) : Finset (Fin (m+m)) :=
  if aa m i0 ∈ z ∧ bb m i0 ∈ z then (z.erase (aa m i0)).erase (bb m i0)
  else z
theorem mem_phi (m : ℕ) (i0 : Fin m) (z : Finset (Fin (m+m))) (v : Fin (m+m)) :
    v ∈ phi m i0 z ↔ v ∈ z ∧ ¬((aa m i0 ∈ z ∧ bb m i0 ∈ z) ∧
      (v = aa m i0 ∨ v = bb m i0)) := by
  unfold phi; split_ifs with h <;> simp [Finset.mem_erase, h] <;> tauto
theorem prof_phi (m : ℕ) (i0 : Fin m) (z : Finset (Fin (m+m))) : prof m (phi m i0 z) = prof m z := by
  funext ⟨i, b⟩
  simp only [prof]
  have ha : aa m i ∈ phi m i0 z ↔ aa m i ∈ z ∧
      ¬((aa m i0 ∈ z ∧ bb m i0 ∈ z) ∧ i = i0) := by
    rw [mem_phi]; simp [ca_inj, ca_ne_na]
  have hb : bb m i ∈ phi m i0 z ↔ bb m i ∈ z ∧
      ¬((aa m i0 ∈ z ∧ bb m i0 ∈ z) ∧ i = i0) := by
    rw [mem_phi]; simp [na_inj, na_ne_ca]
  by_cases hi : i = i0
  · subst hi
    by_cases h1 : aa m i ∈ z <;> by_cases h2 : bb m i ∈ z <;> cases b <;>
      simp_all [atom]
  · cases b <;> simp [atom, ha, hb, hi]
theorem pp_phi (m : ℕ) (P : Finset (Finset (Fin (m+m)))) (i i0 : Fin m) (hne : i ≠ i0) (h : PP m P i) :
    PP m (P.image (phi m i0)) i := by
  obtain ⟨z, hz, h1, h2, h3⟩ := h
  refine ⟨phi m i0 z, Finset.mem_image_of_mem _ hz, ?_, ?_, ?_⟩
  · rw [mem_phi]; tauto
  · rw [mem_phi]; tauto
  · have e : insert (aa m i) (insert (bb m i) (phi m i0 z)) =
        phi m i0 (insert (aa m i) (insert (bb m i) z)) := by
      ext v
      simp only [Finset.mem_insert, mem_phi]
      by_cases hv1 : v = aa m i
      · subst hv1; simp [ca_inj, na_inj, hne, ca_ne_na, na_ne_ca]
      · by_cases hv2 : v = bb m i
        · subst hv2; simp [ca_inj, na_inj, hne, ca_ne_na, na_ne_ca]
        · have e1 : aa m i0 ≠ aa m i := fun h => hne ((ca_inj _ _).mp h).symm
          have e4 : bb m i0 ≠ bb m i := fun h => hne ((na_inj _ _).mp h).symm
          simp [hv1, hv2, e1, e4, ca_ne_na, na_ne_ca]
    rw [e]; exact Finset.mem_image_of_mem _ h3
theorem card_phi_lt (m : ℕ) (P : Finset (Finset (Fin (m+m)))) (i0 : Fin m) (h : PP m P i0) :
    (P.image (phi m i0)).card < P.card := by
  obtain ⟨z, hz, h1, h2, h3⟩ := h
  have e1 : phi m i0 z = z := by
    unfold phi; split_ifs with hc
    · exact absurd hc.1 h1
    · rfl
  have e2 : phi m i0 (insert (aa m i0) (insert (bb m i0) z)) = z := by
    ext v; rw [mem_phi]; simp only [Finset.mem_insert]
    by_cases hv1 : v = aa m i0
    · subst hv1; simp [h1]
    · by_cases hv2 : v = bb m i0
      · subst hv2; simp [h2]
      · simp [hv1, hv2]
  have hne : z ≠ insert (aa m i0) (insert (bb m i0) z) := by
    intro h; apply h1; rw [h]; exact Finset.mem_insert_self _ _
  have hle := Finset.card_image_le (s := P) (f := phi m i0)
  have hneq : (P.image (phi m i0)).card ≠ P.card := by
    intro hc
    have hinj := Finset.card_image_iff.mp hc
    exact hne (hinj hz h3 (by rw [e1, e2]))
  omega
theorem forest (m : ℕ) (I : Finset (Fin m)) : ∀ P : Finset (Finset (Fin (m+m))),
    (∀ i ∈ I, PP m P i) → (P.image (prof m)).card + I.card ≤ P.card := by
  induction I using Finset.induction_on with
  | empty => intro P _; simpa using Finset.card_image_le
  | @insert i0 I hi0 ih =>
    intro P hP
    have h1 := ih (P.image (phi m i0)) (fun i hi => pp_phi m P i i0 (fun he => hi0 (he ▸ hi))
      (hP i (Finset.mem_insert_of_mem hi)))
    have e : (P.image (phi m i0)).image (prof m) = P.image (prof m) := by
      rw [Finset.image_image]; congr 1; funext z; exact prof_phi m i0 z
    rw [e] at h1
    have h2 := card_phi_lt m P i0 (hP i0 (Finset.mem_insert_self _ _))
    rw [Finset.card_insert_of_notMem hi0]; omega
theorem fwd (m t : ℕ) (hm : 0 < m) (L : Finset (Fin (m+m)) → List (Finset (Fin (m+m)) → Bool))
    (need : Finset (Finset (Fin (m+m)) → Bool))
    (hL : ∀ S g, g ∈ L S ↔ IsRaw m g ∨ ∃ v ∈ S, g = nf m v)
    (hN : ∀ f, f ∈ need ↔ (∃ v, f = nf m v) ∨ ∃ i o, f = atom m i o) (dq : DecidableEq (Fin t))
    (A : Finset (Finset (Fin (m+m)))) (hk : Keeps m L need A) (hc : A.card ≤ m + t) :
    ∃ f, GoodF m t dq f := by
  obtain ⟨hinj, hnz, hsm, hnsm⟩ := fwd_a m hm L need hL hN A hk
  have hpp : ∀ i, PP m A i := fun i => fwd_b m L need hL A hk i
  have hfor := forest m Finset.univ A (fun i _ => hpp i)
  simp only [Finset.card_univ, Fintype.card_fin] at hfor
  have hRt : (A.image (prof m)).card ≤ t := by omega
  obtain ⟨z0, hz0, -⟩ := hpp ⟨0, hm⟩
  have hlen : (A.image (prof m)).toList.length = (A.image (prof m)).card := Finset.length_toList _
  obtain ⟨ρ, hρd⟩ : ∃ ρ : Fin t → Fin m × Bool → Bool,
      ∀ r, ρ r = (A.image (prof m)).toList.getD r.val (prof m z0) := ⟨_, fun r => rfl⟩
  have hρR : ∀ r, ∃ x ∈ A, ρ r = prof m x := by
    intro r
    have : ρ r ∈ A.image (prof m) := by
      rw [hρd]
      rcases Nat.lt_or_ge r.val (A.image (prof m)).toList.length with h | h
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
        exact Finset.mem_toList.mp (List.getElem_mem h)
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h, Option.getD_none]
        exact Finset.mem_image_of_mem _ hz0
    obtain ⟨x, hx, e⟩ := Finset.mem_image.mp this
    exact ⟨x, hx, e.symm⟩
  have hRρ : ∀ x ∈ A, ∃ r, ρ r = prof m x := by
    intro x hx
    have hm' : prof m x ∈ (A.image (prof m)).toList :=
      Finset.mem_toList.mpr (Finset.mem_image_of_mem _ hx)
    obtain ⟨j, hj, e⟩ := List.getElem_of_mem hm'
    refine ⟨⟨j, by omega⟩, ?_⟩
    rw [hρd, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some, e]
  have mf : ∀ k r, r ∈ (Finset.univ.filter (fun r => ρ r k = true)) ↔ ρ r k = true := by
    intro k r; simp
  refine ⟨fun k => Finset.univ.filter (fun r => ρ r k = true), ?_⟩
  unfold GoodF
  refine ⟨fun k k' he => ?_, fun k => ?_, fun i => ⟨?_, ?_⟩, fun k i => ⟨?_, ?_⟩⟩
  · apply hinj k k'
    intro x hx
    obtain ⟨r, hr⟩ := hRρ x hx
    have := congrArg (fun s => r ∈ s) he
    simp only [mf, hr] at this
    exact Bool.eq_iff_iff.mpr (Iff.of_eq this)
  · obtain ⟨x, hx, hv⟩ := hnz k
    obtain ⟨r, hr⟩ := hRρ x hx
    exact ⟨r, by rw [mf, hr]; exact hv⟩
  · rw [Finset.disjoint_left]
    intro r h1 h2
    rw [mf] at h1 h2
    obtain ⟨x, _, hx⟩ := hρR r
    rw [hx] at h1 h2
    simp only [prof, atom, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
      decide_eq_false_iff_not] at h1 h2
    exact h2.1 h1.1
  · intro hu
    obtain ⟨z, hz, h1, h2, _⟩ := hpp i
    obtain ⟨r, hr⟩ := hRρ z hz
    have : r ∈ (Finset.univ.filter (fun r => ρ r (i,false) = true)) ∪
        (Finset.univ.filter (fun r => ρ r (i,true) = true)) := by rw [hu]; exact Finset.mem_univ r
    rw [Finset.mem_union, mf, mf, hr] at this
    simp [prof, atom, h1, h2] at this
  · intro he
    apply hnsm k i
    intro x hx
    obtain ⟨r, hr⟩ := hRρ x hx
    have := congrArg (fun s => r ∈ s) he
    simp only [Finset.mem_union, mf, hr] at this
    rw [Bool.eq_iff_iff, this]
    by_cases ha : aa m i ∈ x <;> by_cases hb : bb m i ∈ x <;> simp [prof, atom, nsameF, ha, hb]
  · intro he
    apply hsm k i
    intro x hx
    obtain ⟨r, hr⟩ := hRρ x hx
    have := congrArg (fun s => r ∈ s) he
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union, mf, hr] at this
    rw [Bool.eq_iff_iff, this]
    by_cases ha : aa m i ∈ x <;> by_cases hb : bb m i ∈ x <;> simp [prof, atom, sameF, ha, hb]
def Pp (m t : ℕ) (dq : DecidableEq (Fin t)) (f : Fin m × Bool → Finset (Fin t)) (r : Fin t) :
    Finset (Fin (m+m)) :=
  (Finset.univ.filter (fun i => r ∈ f (i,false))).image (aa m) ∪
    (Finset.univ.filter (fun i => r ∈ f (i,true))).image (bb m)
def Qp (m t : ℕ) (dq : DecidableEq (Fin t)) (f : Fin m × Bool → Finset (Fin t)) (ρ : Fin m → Fin t)
    (i : Fin m) : Finset (Fin (m+m)) :=
  insert (aa m i) (insert (bb m i) (Pp m t dq f (ρ i)))
def Ap (m t : ℕ) (dq : DecidableEq (Fin t)) (f : Fin m × Bool → Finset (Fin t)) (ρ : Fin m → Fin t) :
    Finset (Finset (Fin (m+m))) :=
  Finset.univ.image (Pp m t dq f) ∪ Finset.univ.image (Qp m t dq f ρ)
theorem memPa (m t : ℕ) (dq : DecidableEq (Fin t)) (f : Fin m × Bool → Finset (Fin t)) (r : Fin t)
    (k : Fin m) : aa m k ∈ Pp m t dq f r ↔ r ∈ f (k,false) := by
  simp [Pp, ca_inj, na_ne_ca]
theorem memPb (m t : ℕ) (dq : DecidableEq (Fin t)) (f : Fin m × Bool → Finset (Fin t)) (r : Fin t)
    (k : Fin m) : bb m k ∈ Pp m t dq f r ↔ r ∈ f (k,true) := by
  simp [Pp, na_inj, ca_ne_na]
theorem memQa (m t : ℕ) (dq : DecidableEq (Fin t)) (f : Fin m × Bool → Finset (Fin t))
    (ρ : Fin m → Fin t) (i k : Fin m) : aa m k ∈ Qp m t dq f ρ i ↔ k = i ∨ ρ i ∈ f (k,false) := by
  simp [Qp, memPa, ca_inj, ca_ne_na]
theorem memQb (m t : ℕ) (dq : DecidableEq (Fin t)) (f : Fin m × Bool → Finset (Fin t))
    (ρ : Fin m → Fin t) (i k : Fin m) : bb m k ∈ Qp m t dq f ρ i ↔ k = i ∨ ρ i ∈ f (k,true) := by
  simp [Qp, memPb, na_inj, na_ne_ca]
def Rep (m t : ℕ) (dq : DecidableEq (Fin t)) (f : Fin m × Bool → Finset (Fin t)) (ρ : Fin m → Fin t)
    (c : Finset (Fin (m+m)) → Bool) (B : Fin t → Bool) (E : Option (Fin m)) (q : Bool) : Prop :=
  (∀ r, c (Pp m t dq f r) = B r) ∧ (∀ i, c (Qp m t dq f ρ i) = if E = some i then q else B (ρ i)) ∧
    (∀ k, E = some k → q ≠ B (ρ k))
theorem rep_eq (m t : ℕ) (dq : DecidableEq (Fin t)) (f : Fin m × Bool → Finset (Fin t))
    (ρ : Fin m → Fin t) (c c' : Finset (Fin (m+m)) → Bool) (B B' : Fin t → Bool) (E E' : Option (Fin m))
    (q q' : Bool) (h : Rep m t dq f ρ c B E q) (h' : Rep m t dq f ρ c' B' E' q')
    (he : ∀ x ∈ Ap m t dq f ρ, c x = c' x) : B = B' ∧ E = E' ∧ (∀ k, E = some k → q = q') := by
  obtain ⟨hP, hQ, hV⟩ := h
  obtain ⟨hP', hQ', hV'⟩ := h'
  have hB : B = B' := funext fun r => by
    rw [← hP r, ← hP' r]
    exact he _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ r)))
  have hQe : ∀ i, c (Qp m t dq f ρ i) = c' (Qp m t dq f ρ i) := fun i =>
    he _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  subst hB
  refine ⟨rfl, ?_, ?_⟩
  · rcases E with _ | k <;> rcases E' with _ | k'
    · rfl
    · exfalso; have := hQe k'; rw [hQ k', hQ' k'] at this; simp at this; exact hV' k' rfl this.symm
    · exfalso; have := hQe k; rw [hQ k, hQ' k] at this; simp at this; exact hV k rfl this
    · by_cases hkk : k' = k
      · rw [hkk]
      · exfalso
        have := hQe k; rw [hQ k, hQ' k] at this; simp [hkk] at this; exact hV k rfl this
  · intro k hk; subst hk
    have := hQe k; rw [hQ k, hQ' k] at this
    rcases E' with _ | k'
    · simp at this; exact absurd this (hV k rfl)
    · by_cases hkk : k' = k
      · subst hkk; simpa using this
      · simp [hkk] at this; exact absurd this (hV k rfl)
theorem rep_edge (m t : ℕ) (dq : DecidableEq (Fin t)) (f : Fin m × Bool → Finset (Fin t))
    (ρ : Fin m → Fin t) (hρ : ∀ i, ρ i ∉ f (i,false) ∪ f (i,true)) (k : Fin m) (h : Bool → Bool → Bool)
    (B : Fin t → Bool) (hB : ∀ r, h (decide (r ∈ f (k,false))) (decide (r ∈ f (k,true))) = B r) :
    (∀ r, h (decide (aa m k ∈ Pp m t dq f r)) (decide (bb m k ∈ Pp m t dq f r)) = B r) ∧
    (∀ i, h (decide (aa m k ∈ Qp m t dq f ρ i)) (decide (bb m k ∈ Qp m t dq f ρ i)) =
      if k = i then h true true else B (ρ i)) ∧ B (ρ k) = h false false := by
  refine ⟨fun r => by simp only [memPa, memPb]; exact hB r, fun i => ?_, ?_⟩
  · simp only [memQa, memQb]
    by_cases hki : k = i
    · subst hki; simp
    · simp only [hki, false_or, ite_false]; exact hB (ρ i)
  · rw [← hB]
    have := hρ k
    simp only [Finset.mem_union, not_or] at this
    simp [this.1, this.2]
theorem rep_inv (m t : ℕ) (dq : DecidableEq (Fin t)) (f : Fin m × Bool → Finset (Fin t))
    (ρ : Fin m → Fin t) (hρ : ∀ i, ρ i ∉ f (i,false) ∪ f (i,true)) (k : Fin m) (h : Bool → Bool → Bool)
    (B : Fin t → Bool) (hB : ∀ r, h (decide (r ∈ f (k,false))) (decide (r ∈ f (k,true))) = B r)
    (hh : h true true = h false false) (q : Bool) :
    Rep m t dq f ρ (fun x => h (decide (aa m k ∈ x)) (decide (bb m k ∈ x))) B none q := by
  obtain ⟨h1, h2, h3⟩ := rep_edge m t dq f ρ hρ k h B hB
  refine ⟨h1, fun i => ?_, fun k' hk' => by simp at hk'⟩
  show h (decide (aa m k ∈ Qp m t dq f ρ i)) (decide (bb m k ∈ Qp m t dq f ρ i)) = _
  rw [h2 i]
  by_cases hki : k = i
  · subst hki; simp [hh, h3]
  · simp [hki]
theorem rep_vis (m t : ℕ) (dq : DecidableEq (Fin t)) (f : Fin m × Bool → Finset (Fin t))
    (ρ : Fin m → Fin t) (hρ : ∀ i, ρ i ∉ f (i,false) ∪ f (i,true)) (k : Fin m) (h : Bool → Bool → Bool)
    (B : Fin t → Bool) (hB : ∀ r, h (decide (r ∈ f (k,false))) (decide (r ∈ f (k,true))) = B r)
    (hh : h true true ≠ h false false) :
    Rep m t dq f ρ (fun x => h (decide (aa m k ∈ x)) (decide (bb m k ∈ x))) B (some k) (h true true) := by
  obtain ⟨h1, h2, h3⟩ := rep_edge m t dq f ρ hρ k h B hB
  refine ⟨h1, fun i => ?_, fun k' hk' => ?_⟩
  · show h (decide (aa m k ∈ Qp m t dq f ρ i)) (decide (bb m k ∈ Qp m t dq f ρ i)) = _
    rw [h2 i]; simp
  · simp at hk'; subst hk'; rw [h3]; exact hh
theorem disj_of (m t : ℕ) (dq : DecidableEq (Fin t)) (f : Fin m × Bool → Finset (Fin t))
    (hG : GoodF m t dq f) (k : Fin m) (r : Fin t) (h : r ∈ f (k,false)) : r ∉ f (k,true) := by
  obtain ⟨_, _, hdu, _⟩ := hG
  exact Finset.disjoint_left.mp (hdu k).1 h
theorem reps (m t : ℕ) (dq : DecidableEq (Fin t)) (f : Fin m × Bool → Finset (Fin t))
    (hG : GoodF m t dq f) (ρ : Fin m → Fin t) (hρ : ∀ i, ρ i ∉ f (i,false) ∪ f (i,true)) (k : Fin m) :
    Rep m t dq f ρ (nf m (aa m k)) (fun r => !decide (r ∈ f (k,false))) (some k) false ∧
    Rep m t dq f ρ (nf m (bb m k)) (fun r => !decide (r ∈ f (k,true))) (some k) false ∧
    Rep m t dq f ρ (atom m k none) (fun r => decide (r ∈ Finset.univ \ (f (k,false) ∪ f (k,true))))
      (some k) false ∧
    (∀ b, Rep m t dq f ρ (atom m k (some b)) (fun r => decide (r ∈ f (k,b))) none false) ∧
    Rep m t dq f ρ (fun x => decide (aa m k ∈ x)) (fun r => decide (r ∈ f (k,false))) (some k) true ∧
    Rep m t dq f ρ (fun x => decide (bb m k ∈ x)) (fun r => decide (r ∈ f (k,true))) (some k) true ∧
    Rep m t dq f ρ (sameF m k) (fun r => decide (r ∈ Finset.univ \ (f (k,false) ∪ f (k,true)))) none false ∧
    Rep m t dq f ρ (nsameF m k) (fun r => decide (r ∈ f (k,false) ∪ f (k,true))) none false := by
  have hd := disj_of m t dq f hG k
  refine ⟨rep_vis m t dq f ρ hρ k (fun p _ => !p) _ (fun r => rfl) (by decide),
    rep_vis m t dq f ρ hρ k (fun _ q => !q) _ (fun r => rfl) (by decide),
    rep_vis m t dq f ρ hρ k (fun p q => !p && !q) _ (fun r => by simp) (by decide),
    fun b => ?_,
    rep_vis m t dq f ρ hρ k (fun p _ => p) _ (fun r => rfl) (by decide),
    rep_vis m t dq f ρ hρ k (fun _ q => q) _ (fun r => rfl) (by decide),
    rep_inv m t dq f ρ hρ k (fun p q => !(xor p q)) _ (fun r => ?_) (by decide) false,
    rep_inv m t dq f ρ hρ k (fun p q => xor p q) _ (fun r => ?_) (by decide) false⟩
  · cases b
    · refine rep_inv m t dq f ρ hρ k (fun p q => p && !q) _ (fun r => ?_) (by decide) false
      by_cases h1 : r ∈ f (k,false)
      · simp [h1, hd r h1]
      · simp [h1]
    · refine rep_inv m t dq f ρ hρ k (fun p q => !p && q) _ (fun r => ?_) (by decide) false
      by_cases h1 : r ∈ f (k,false)
      · simp [h1, hd r h1]
      · simp [h1]
  · by_cases h1 : r ∈ f (k,false)
    · simp [h1, hd r h1]
    · by_cases h2 : r ∈ f (k,true) <;> simp [h1, h2]
  · by_cases h1 : r ∈ f (k,false)
    · simp [h1, hd r h1]
    · by_cases h2 : r ∈ f (k,true) <;> simp [h1, h2]
theorem rC0 (m t : ℕ) (dq : DecidableEq (Fin t)) (f : Fin m × Bool → Finset (Fin t)) (ρ : Fin m → Fin t) :
    Rep m t dq f ρ (fun _ => false) (fun _ => false) none false :=
  ⟨fun r => rfl, fun i => by simp, fun k h => by simp at h⟩
theorem rC1 (m t : ℕ) (dq : DecidableEq (Fin t)) (f : Fin m × Bool → Finset (Fin t)) (ρ : Fin m → Fin t) :
    Rep m t dq f ρ (fun _ => true) (fun _ => true) none false :=
  ⟨fun r => rfl, fun i => by simp, fun k h => by simp at h⟩
theorem bset {t : ℕ} [DecidableEq (Fin t)] (X Y : Finset (Fin t))
    (h : (fun r => decide (r ∈ X)) = (fun r => decide (r ∈ Y))) : X = Y := by
  ext r; have := congrFun h r; simpa using this
theorem bnset {t : ℕ} [DecidableEq (Fin t)] (X Y : Finset (Fin t))
    (h : (fun r => !decide (r ∈ X)) = (fun r => !decide (r ∈ Y))) : X = Y := by
  ext r; have := congrFun h r; simpa using this
theorem bmix {t : ℕ} [DecidableEq (Fin t)] (X Y : Finset (Fin t))
    (h : (fun r => !decide (r ∈ X)) = (fun r => decide (r ∈ Finset.univ \ Y))) : X = Y := by
  ext r; have := congrFun h r; simp at this; tauto
def sig (m : ℕ) : Fin (m+m) ⊕ (Fin m × Option Bool) → Finset (Fin (m+m)) → Bool :=
  Sum.elim (nf m) (fun k => atom m k.1 k.2)
theorem q1 (m t : ℕ) (dq : DecidableEq (Fin t)) (f : Fin m × Bool → Finset (Fin t))
    (hG : GoodF m t dq f) (ρ : Fin m → Fin t) (hρ : ∀ i, ρ i ∉ f (i,false) ∪ f (i,true))
    (s s' : Fin (m+m) ⊕ (Fin m × Option Bool)) (h : ∀ x ∈ Ap m t dq f ρ, sig m s x = sig m s' x) :
    s = s' := by
  obtain ⟨hinj, hne, hdu, hfu⟩ := id hG
  have R := reps m t dq f hG ρ hρ
  have key : ∀ (c c' : Finset (Fin (m+m)) → Bool) B B' E E' q q', Rep m t dq f ρ c B E q →
      Rep m t dq f ρ c' B' E' q' → (∀ x ∈ Ap m t dq f ρ, c x = c' x) →
      B = B' ∧ E = E' ∧ (∀ k, E = some k → q = q') :=
    fun c c' B B' E E' q q' h1 h2 h3 => rep_eq m t dq f ρ c c' B B' E E' q q' h1 h2 h3
  rcases s with v | ⟨k, o⟩ <;> rcases s' with v' | ⟨k', o'⟩
  · induction v using Fin.addCases with
    | left k =>
      induction v' using Fin.addCases with
      | left k' =>
        obtain ⟨_, hE, _⟩ := key _ _ _ _ _ _ _ _ (R k).1 (R k').1 h
        simp at hE; subst hE; rfl
      | right k' =>
        obtain ⟨hB, hE, _⟩ := key _ _ _ _ _ _ _ _ (R k).1 (R k').2.1 h
        simp at hE; subst hE
        have := hinj (bnset _ _ hB); simp at this
    | right k =>
      induction v' using Fin.addCases with
      | left k' =>
        obtain ⟨hB, hE, _⟩ := key _ _ _ _ _ _ _ _ (R k).2.1 (R k').1 h
        simp at hE; subst hE
        have := hinj (bnset _ _ hB); simp at this
      | right k' =>
        obtain ⟨_, hE, _⟩ := key _ _ _ _ _ _ _ _ (R k).2.1 (R k').2.1 h
        simp at hE; subst hE; rfl
  · induction v using Fin.addCases with
    | left k =>
      rcases o' with _ | b'
      · obtain ⟨hB, hE, _⟩ := key _ _ _ _ _ _ _ _ (R k).1 (R k').2.2.1 h
        simp at hE; subst hE
        exact absurd (bmix _ _ hB) (hfu (k,false) k).1
      · obtain ⟨_, hE, _⟩ := key _ _ _ _ _ _ _ _ (R k).1 ((R k').2.2.2.1 b') h
        simp at hE
    | right k =>
      rcases o' with _ | b'
      · obtain ⟨hB, hE, _⟩ := key _ _ _ _ _ _ _ _ (R k).2.1 (R k').2.2.1 h
        simp at hE; subst hE
        exact absurd (bmix _ _ hB) (hfu (k,true) k).1
      · obtain ⟨_, hE, _⟩ := key _ _ _ _ _ _ _ _ (R k).2.1 ((R k').2.2.2.1 b') h
        simp at hE
  · have h' : ∀ x ∈ Ap m t dq f ρ, sig m (Sum.inl v') x = sig m (Sum.inr (k, o)) x :=
      fun x hx => (h x hx).symm
    induction v' using Fin.addCases with
    | left k' =>
      rcases o with _ | b
      · obtain ⟨hB, hE, _⟩ := key _ _ _ _ _ _ _ _ (R k').1 (R k).2.2.1 h'
        simp at hE; subst hE
        exact absurd (bmix _ _ hB) (hfu (k',false) k').1
      · obtain ⟨_, hE, _⟩ := key _ _ _ _ _ _ _ _ (R k').1 ((R k).2.2.2.1 b) h'
        simp at hE
    | right k' =>
      rcases o with _ | b
      · obtain ⟨hB, hE, _⟩ := key _ _ _ _ _ _ _ _ (R k').2.1 (R k).2.2.1 h'
        simp at hE; subst hE
        exact absurd (bmix _ _ hB) (hfu (k',true) k').1
      · obtain ⟨_, hE, _⟩ := key _ _ _ _ _ _ _ _ (R k').2.1 ((R k).2.2.2.1 b) h'
        simp at hE
  · rcases o with _ | b <;> rcases o' with _ | b'
    · obtain ⟨_, hE, _⟩ := key _ _ _ _ _ _ _ _ (R k).2.2.1 (R k').2.2.1 h
      simp at hE; subst hE; rfl
    · obtain ⟨_, hE, _⟩ := key _ _ _ _ _ _ _ _ (R k).2.2.1 ((R k').2.2.2.1 b') h
      simp at hE
    · obtain ⟨_, hE, _⟩ := key _ _ _ _ _ _ _ _ ((R k).2.2.2.1 b) (R k').2.2.1 h
      simp at hE
    · obtain ⟨hB, _, _⟩ := key _ _ _ _ _ _ _ _ ((R k).2.2.2.1 b) ((R k').2.2.2.1 b') h
      have := hinj (bset _ _ hB)
      simp only [Prod.mk.injEq] at this
      obtain ⟨rfl, rfl⟩ := this
      rfl
theorem q2 (m t : ℕ) (dq : DecidableEq (Fin t)) (f : Fin m × Bool → Finset (Fin t))
    (hG : GoodF m t dq f) (ρ : Fin m → Fin t) (hρ : ∀ i, ρ i ∉ f (i,false) ∪ f (i,true))
    (s : Fin (m+m) ⊕ (Fin m × Option Bool)) (g : Finset (Fin (m+m)) → Bool) (hg : IsRaw m g)
    (h : ∀ x ∈ Ap m t dq f ρ, sig m s x = g x) : False := by
  obtain ⟨hinj, hne, hdu, hfu⟩ := id hG
  have R := reps m t dq f hG ρ hρ
  have key : ∀ (c c' : Finset (Fin (m+m)) → Bool) B B' E E' q q', Rep m t dq f ρ c B E q →
      Rep m t dq f ρ c' B' E' q' → (∀ x ∈ Ap m t dq f ρ, c x = c' x) →
      B = B' ∧ E = E' ∧ (∀ k, E = some k → q = q') :=
    fun c c' B B' E E' q q' h1 h2 h3 => rep_eq m t dq f ρ c c' B B' E E' q q' h1 h2 h3
  have hvis : ∀ c B k, Rep m t dq f ρ c B (some k) false → (∀ x ∈ Ap m t dq f ρ, c x = g x) → False := by
    intro c B k hc hcg
    rcases hg with rfl | rfl | ⟨v, rfl⟩ | ⟨k', rfl⟩ | ⟨k', rfl⟩
    · obtain ⟨_, hE, _⟩ := key _ _ _ _ _ _ _ _ hc (rC0 m t dq f ρ) hcg; simp at hE
    · obtain ⟨_, hE, _⟩ := key _ _ _ _ _ _ _ _ hc (rC1 m t dq f ρ) hcg; simp at hE
    · induction v using Fin.addCases with
      | left k' =>
        obtain ⟨_, _, hq⟩ := key _ _ _ _ _ _ _ _ hc (R k').2.2.2.2.1 hcg; simp at hq
      | right k' =>
        obtain ⟨_, _, hq⟩ := key _ _ _ _ _ _ _ _ hc (R k').2.2.2.2.2.1 hcg; simp at hq
    · obtain ⟨_, hE, _⟩ := key _ _ _ _ _ _ _ _ hc (R k').2.2.2.2.2.2.1 hcg; simp at hE
    · obtain ⟨_, hE, _⟩ := key _ _ _ _ _ _ _ _ hc (R k').2.2.2.2.2.2.2 hcg; simp at hE
  rcases s with v | ⟨k, o⟩
  · induction v using Fin.addCases with
    | left k => exact hvis _ _ k (R k).1 h
    | right k => exact hvis _ _ k (R k).2.1 h
  · rcases o with _ | b
    · exact hvis _ _ k (R k).2.2.1 h
    · have hc := (R k).2.2.2.1 b
      have hsub : f (k,b) ⊆ f (k,false) ∪ f (k,true) := by
        cases b
        · exact Finset.subset_union_left
        · exact Finset.subset_union_right
      rcases hg with rfl | rfl | ⟨v, rfl⟩ | ⟨k', rfl⟩ | ⟨k', rfl⟩
      · obtain ⟨hB, _, _⟩ := key _ _ _ _ _ _ _ _ hc (rC0 m t dq f ρ) h
        obtain ⟨r, hr⟩ := hne (k,b)
        have := congrFun hB r; simp [hr] at this
      · obtain ⟨hB, _, _⟩ := key _ _ _ _ _ _ _ _ hc (rC1 m t dq f ρ) h
        apply (hdu k).2
        apply Finset.eq_univ_iff_forall.mpr
        intro r; have := congrFun hB r; simp at this; exact hsub this
      · induction v using Fin.addCases with
        | left k' =>
          obtain ⟨_, hE, _⟩ := key _ _ _ _ _ _ _ _ hc (R k').2.2.2.2.1 h; simp at hE
        | right k' =>
          obtain ⟨_, hE, _⟩ := key _ _ _ _ _ _ _ _ hc (R k').2.2.2.2.2.1 h; simp at hE
      · obtain ⟨hB, _, _⟩ := key _ _ _ _ _ _ _ _ hc (R k').2.2.2.2.2.2.1 h
        exact (hfu (k,b) k').2 (bset _ _ hB)
      · obtain ⟨hB, _, _⟩ := key _ _ _ _ _ _ _ _ hc (R k').2.2.2.2.2.2.2 h
        exact (hfu (k,b) k').1 (bset _ _ hB)
theorem fcases (m : ℕ) (v : Fin (m+m)) : (∃ i, v = aa m i) ∨ (∃ i, v = bb m i) := by
  induction v using Fin.addCases with
  | left i => exact Or.inl ⟨i, rfl⟩
  | right i => exact Or.inr ⟨i, rfl⟩
theorem build_cover (m : ℕ) (L : Finset (Fin (m+m)) → List (Finset (Fin (m+m)) → Bool))
    (need : Finset (Finset (Fin (m+m)) → Bool))
    (hL : ∀ S g, g ∈ L S ↔ IsRaw m g ∨ ∃ v ∈ S, g = nf m v)
    (hN : ∀ f, f ∈ need ↔ (∃ v, f = nf m v) ∨ ∃ i o, f = atom m i o)
    (A : Finset (Finset (Fin (m+m)))) (S : Finset (Fin (m+m))) (hcov : ∀ i, aa m i ∈ S ∨ bb m i ∈ S) :
    ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (L S).length C ∧
      C.output < (L S).length + C.size ∧ C.size ≤ m * 3 + (m + m - S.card) ∧
      ∀ f ∈ need, ∃ j < (L S).length + C.size,
        ∀ x ∈ A, (C.wires ((L S).map (fun g => g x))).getD j false = f x := by
  have hinp : ∀ g, IsRaw m g → g ∈ L S := fun g h => (hL S g).mpr (Or.inl h)
  have hneg : ∀ v ∈ S, nf m v ∈ L S := fun v hv => (hL S _).mpr (Or.inr ⟨v, hv, rfl⟩)
  have hT1 : ∀ k ∈ (Finset.univ : Finset (Fin m × Option Bool)), ∃ op : GateOp,
      ∃ f1 f2 : Finset (Fin (m+m)) → Bool,
      (op = GateOp.and ∨ op = GateOp.or) ∧ Has (L S) A [] f1 ∧ Has (L S) A [] f2 ∧
      ∀ x ∈ A, (fun k : Fin m × Option Bool => atom m k.1 k.2) k x = op.eval [f1 x, f2 x] := by
    rintro ⟨i, o⟩ _
    rcases o with _ | ⟨_ | _⟩
    · rcases hcov i with hi | hi
      · refine ⟨GateOp.and, nf m (aa m i), sameF m i, Or.inl rfl, has_inp _ _ _ _ (hneg _ hi),
          has_inp _ _ _ _ (hinp _ (raws m i)), fun x _ => ?_⟩
        by_cases h1 : aa m i ∈ x <;> by_cases h2 : bb m i ∈ x <;> simp [atom, nf, sameF, GateOp.eval, h1, h2]
      · refine ⟨GateOp.and, nf m (bb m i), sameF m i, Or.inl rfl, has_inp _ _ _ _ (hneg _ hi),
          has_inp _ _ _ _ (hinp _ (raws m i)), fun x _ => ?_⟩
        by_cases h1 : aa m i ∈ x <;> by_cases h2 : bb m i ∈ x <;> simp [atom, nf, sameF, GateOp.eval, h1, h2]
    · refine ⟨GateOp.and, (fun x => decide (aa m i ∈ x)), nsameF m i, Or.inl rfl,
        has_inp _ _ _ _ (hinp _ (rawb m _)), has_inp _ _ _ _ (hinp _ (rawn m i)), fun x _ => ?_⟩
      by_cases h1 : aa m i ∈ x <;> by_cases h2 : bb m i ∈ x <;> simp [atom, nsameF, GateOp.eval, h1, h2]
    · refine ⟨GateOp.and, (fun x => decide (bb m i ∈ x)), nsameF m i, Or.inl rfl,
        has_inp _ _ _ _ (hinp _ (rawb m _)), has_inp _ _ _ _ (hinp _ (rawn m i)), fun x _ => ?_⟩
      by_cases h1 : aa m i ∈ x <;> by_cases h2 : bb m i ∈ x <;> simp [atom, nsameF, GateOp.eval, h1, h2]
  obtain ⟨gs1, hg1, _, hl1, hh1⟩ := level (L S) A (fun k : Fin m × Option Bool => atom m k.1 k.2)
    [] Finset.univ hT1 [] (fun j hj => absurd hj (by simp)) ⟨[], rfl⟩
  have hT2 : ∀ v ∈ Finset.univ \ S, ∃ op : GateOp, ∃ f1 f2 : Finset (Fin (m+m)) → Bool,
      (op = GateOp.and ∨ op = GateOp.or) ∧ Has (L S) A gs1 f1 ∧ Has (L S) A gs1 f2 ∧
      ∀ x ∈ A, nf m v x = op.eval [f1 x, f2 x] := by
    intro v _
    rcases fcases m v with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · refine ⟨GateOp.or, atom m i none, atom m i (some true), Or.inr rfl,
        hh1 (i, none) (Finset.mem_univ _), hh1 (i, some true) (Finset.mem_univ _), fun x _ => ?_⟩
      by_cases h1 : aa m i ∈ x <;> by_cases h2 : bb m i ∈ x <;> simp [atom, nf, GateOp.eval, h1, h2]
    · refine ⟨GateOp.or, atom m i none, atom m i (some false), Or.inr rfl,
        hh1 (i, none) (Finset.mem_univ _), hh1 (i, some false) (Finset.mem_univ _), fun x _ => ?_⟩
      by_cases h1 : aa m i ∈ x <;> by_cases h2 : bb m i ∈ x <;> simp [atom, nf, GateOp.eval, h1, h2]
  obtain ⟨gs2, hg2, ⟨u2, hu2⟩, hl2, hh2⟩ := level (L S) A (nf m) gs1 (Finset.univ \ S) hT2 gs1 hg1 ⟨[], by simp⟩
  have hall : ∀ f ∈ need, Has (L S) A gs2 f := by
    intro f hf
    rcases (hN f).mp hf with ⟨v, rfl⟩ | ⟨i, o, rfl⟩
    · by_cases hv : v ∈ S
      · exact has_inp _ _ _ _ (hneg v hv)
      · exact hh2 v (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv⟩)
    · rw [hu2]; exact has_ext _ _ _ _ _ (hh1 (i, o) (Finset.mem_univ _))
  have hL0 : 0 < (L S).length := List.length_pos_of_mem (hinp _ (raw0 m))
  obtain ⟨C, h1, h2, h3, h4, h5⟩ := pack (L S) A need gs2 hg2 hL0 hall
  refine ⟨C, h1, h2, h3, ?_, h5⟩
  rw [h4]
  have c1 : (Finset.univ : Finset (Fin m × Option Bool)).card = m * 3 := by simp
  have c2 : (Finset.univ \ S).card = m + m - S.card := by
    rw [Finset.card_univ_diff, Fintype.card_fin]
  simp only [List.length_nil, zero_add, c1] at hl1
  rw [c2] at hl2
  omega
theorem bwd_keeps (m t : ℕ) (L : Finset (Fin (m+m)) → List (Finset (Fin (m+m)) → Bool))
    (need : Finset (Finset (Fin (m+m)) → Bool))
    (hL : ∀ S g, g ∈ L S ↔ IsRaw m g ∨ ∃ v ∈ S, g = nf m v)
    (hN : ∀ f, f ∈ need ↔ (∃ v, f = nf m v) ∨ ∃ i o, f = atom m i o) (dq : DecidableEq (Fin t))
    (f : Fin m × Bool → Finset (Fin t)) (hG : GoodF m t dq f) (ρ : Fin m → Fin t)
    (hρ : ∀ i, ρ i ∉ f (i,false) ∪ f (i,true)) : Keeps m L need (Ap m t dq f ρ) := by
  intro S p
  have hS2 : S.card ≤ m + m := by have := S.card_le_univ; simpa using this
  have hPA : ∀ r, Pp m t dq f r ∈ Ap m t dq f ρ := fun r =>
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ r))
  have hQA : ∀ i, Qp m t dq f ρ i ∈ Ap m t dq f ρ := fun i =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  constructor
  · rintro ⟨C, h1, h2, h3, h4, h5⟩
    have hops : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => by
      have := (h1 g hg).1; simpa using this
    have hcov : ∀ i, aa m i ∈ S ∨ bb m i ∈ S := by
      by_contra hc
      simp only [not_forall, not_or] at hc
      obtain ⟨i, hai, hbi⟩ := hc
      have hρi := hρ i
      simp only [Finset.mem_union, not_or] at hρi
      have hin : ∀ g ∈ L S, g (Pp m t dq f (ρ i)) = true → g (Qp m t dq f ρ i) = true := by
        intro g hg
        rcases (hL S g).mp hg with hr | ⟨v, hv, rfl⟩
        · rcases hr with rfl | rfl | ⟨v, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
          · simp
          · simp
          · intro h; simp only [decide_eq_true_eq] at h ⊢
            exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)
          · by_cases hki : k = i
            · subst hki; intro _; simp [sameF, memQa, memQb]
            · intro h; simpa [sameF, memQa, memQb, memPa, memPb, hki] using h
          · by_cases hki : k = i
            · subst hki; intro h; simp [nsameF, memPa, memPb, hρi.1, hρi.2] at h
            · intro h; simpa [nsameF, memQa, memQb, memPa, memPb, hki] using h
        · have hv1 : v ≠ aa m i := fun e => hai (e ▸ hv)
          have hv2 : v ≠ bb m i := fun e => hbi (e ▸ hv)
          intro h; simpa [nf, Qp, hv1, hv2] using h
      obtain ⟨j, _, hv⟩ := h5 (nf m (aa m i)) ((hN _).mpr (Or.inl ⟨_, rfl⟩))
      have e1 := hv _ (hPA (ρ i))
      have e2 := hv _ (hQA i)
      rw [wires_eq] at e1 e2
      have hmono := W_mono C.gates hops ((L S).map (fun g => g (Pp m t dq f (ρ i))))
        ((L S).map (fun g => g (Qp m t dq f ρ i))) (by simp) (by
          intro idx
          rcases Nat.lt_or_ge idx (L S).length with hi | hi
          · rw [map_getD _ _ _ hi, map_getD _ _ _ hi]
            exact hin _ (List.getElem_mem hi)
          · rw [getD_big _ _ (by simpa using hi)]; simp) j
      rw [e1, e2] at hmono
      simp [nf, memPa, memQa, hρi.1] at hmono
    refine ⟨hcov, ?_⟩
    have hcard := lower (L S) (Ap m t dq f ρ) C ((Finset.univ \ S).disjSum Finset.univ) (sig m)
      (fun s hs => by
        rcases s with v | k
        · exact h5 _ ((hN _).mpr (Or.inl ⟨v, rfl⟩))
        · exact h5 _ ((hN _).mpr (Or.inr ⟨k.1, k.2, rfl⟩)))
      (fun s _ s' _ he => q1 m t dq f hG ρ hρ s s' he)
      (fun s hs g hg he => by
        rcases (hL S g).mp hg with hr | ⟨v, hv, rfl⟩
        · exact q2 m t dq f hG ρ hρ s g hr he
        · have := q1 m t dq f hG ρ hρ s (Sum.inl v) he
          subst this
          simp at hs
          exact hs hv)
    have c1 : ((Finset.univ \ S).disjSum (Finset.univ : Finset (Fin m × Option Bool))).card =
        (m + m - S.card) + m * 3 := by
      rw [Finset.card_disjSum, Finset.card_univ_diff, Fintype.card_fin]; simp
    rw [c1] at hcard
    omega
  · rintro ⟨hcov, hp⟩
    obtain ⟨C, h1, h2, h3, h4, h5⟩ := build_cover m L need hL hN (Ap m t dq f ρ) S hcov
    exact ⟨C, h1, h2, h3, by omega, h5⟩
theorem main (m t : ℕ) (hm : 0 < m)
    (L : Finset (Fin (m+m)) → List (Finset (Fin (m+m)) → Bool))
    (need : Finset (Finset (Fin (m+m)) → Bool))
    (hL : ∀ S g, g ∈ L S ↔ IsRaw m g ∨ ∃ v ∈ S, g = nf m v)
    (hN : ∀ f, f ∈ need ↔ (∃ v, f = nf m v) ∨ ∃ i o, f = atom m i o) (dq : DecidableEq (Fin t)) :
    (∃ A, Keeps m L need A ∧ A.card ≤ m + t) ↔ ∃ f, GoodF m t dq f := by
  constructor
  · rintro ⟨A, hk, hc⟩
    exact fwd m t hm L need hL hN dq A hk hc
  · rintro ⟨f, hG⟩
    have hρ : ∀ i, ∃ r, r ∉ f (i,false) ∪ f (i,true) := fun i => by
      obtain ⟨_, _, hdu, _⟩ := id hG
      by_contra h
      simp only [not_exists, not_not] at h
      exact (hdu i).2 (Finset.eq_univ_iff_forall.mpr h)
    choose ρ hρ using hρ
    refine ⟨Ap m t dq f ρ, bwd_keeps m t L need hL hN dq f hG ρ hρ, ?_⟩
    have e1 := Finset.card_union_le (Finset.univ.image (Pp m t dq f)) (Finset.univ.image (Qp m t dq f ρ))
    have e2 : (Finset.univ.image (Pp m t dq f)).card ≤ t := by
      have := Finset.card_image_le (s := (Finset.univ : Finset (Fin t))) (f := Pp m t dq f); simpa using this
    have e3 : (Finset.univ.image (Qp m t dq f ρ)).card ≤ m := by
      have := Finset.card_image_le (s := (Finset.univ : Finset (Fin m))) (f := Qp m t dq f ρ); simpa using this
    unfold Ap
    omega
end PEqualNP.Outside.L_meta_53191
theorem PEqualNP.Outside.L_meta_53191 : ∀ (m t : Nat), 0 < m →
  let n := m+m
  let E : Finset (Fin n × Fin n) := Finset.univ.image
    (fun i : Fin m => (Fin.castAdd m i, Fin.natAdd m i))
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  let W := Finset (Fin n)
  let bit := fun (i : Fin n) (x : W) => decide (i ∈ x)
  let neg := fun (i : Fin n) (x : W) => !(bit i x)
  let same := fun (e : Fin n × Fin n) (x : W) => bit e.1 x == bit e.2 x
  let raw : Finset (W → Bool) := {fun _ => false,fun _ => true} ∪ Finset.univ.image bit ∪
    E.image same ∪ E.image (fun e x => !(same e x))
  let need := Finset.univ.image neg ∪ E.image (fun e x => neg e.1 x && neg e.2 x) ∪
    E.image (fun e x => bit e.1 x && neg e.2 x) ∪ E.image (fun e x => neg e.1 x && bit e.2 x)
  let keeps := fun A : Finset W => ∀ (S : W) (p : Nat),
    let L := (raw ∪ S.image neg).toList
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack L.length C ∧
      C.output < L.length+C.size ∧ C.size ≤ p ∧ ∀ f ∈ need, ∃ j < L.length+C.size,
        ∀ x ∈ A, (C.wires (L.map (fun g => g x))).getD j false = f x) ↔
    (∀ i : Fin m, Fin.castAdd m i ∈ S ∨ Fin.natAdd m i ∈ S) ∧ n+3*m-S.card ≤ p
  (∃ A : Finset W, keeps A ∧ A.card ≤ m+t) ↔
  ∃ f : Fin m × Bool → Finset (Fin t),
    Function.Injective f ∧ (∀ k, (f k).Nonempty) ∧
    (∀ i, Disjoint (f (i,false)) (f (i,true)) ∧
      f (i,false) ∪ f (i,true) ≠ Finset.univ) ∧
    ∀ k i, let u := f (i,false) ∪ f (i,true)
      f k ≠ u ∧ f k ≠ Finset.univ \ u := by
  intro m t hm n E W bit neg same raw need keeps
  have hb : bit = fun v x => decide (v ∈ x) := by
    funext v x; exact Bool.eq_iff_iff.mpr (by simp [bit])
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  have hq : ∀ a b : Bool, (a == b) = !(xor a b) := by
    intro a b; rw [Bool.eq_iff_iff, beq_iff_eq]; cases a <;> cases b <;> simp
  have hL : ∀ (S : Finset (Fin (m+m))) (g : Finset (Fin (m+m)) → Bool),
      g ∈ (raw ∪ S.image neg).toList ↔ PEqualNP.Outside.L_meta_53191.IsRaw m g ∨
        ∃ v ∈ S, g = PEqualNP.Outside.L_meta_53191.nf m v := by
    intro S g
    simp only [Finset.mem_toList, Finset.mem_union, Finset.mem_image, Finset.mem_insert,
      Finset.mem_singleton, Finset.mem_univ, true_and, raw, E, neg, same, hb, exists_exists_eq_and,
      @eq_comm _ _ g, PEqualNP.Outside.L_meta_53191.IsRaw, hq, Bool.not_not, or_assoc]
    exact Iff.rfl
  have hN : ∀ f, f ∈ need ↔ (∃ v, f = PEqualNP.Outside.L_meta_53191.nf m v) ∨
      ∃ i o, f = PEqualNP.Outside.L_meta_53191.atom m i o := by
    intro f
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, need, E, neg, hb,
      exists_exists_eq_and, @eq_comm _ _ f, PEqualNP.Outside.L_meta_53191.nf, Option.exists,
      Bool.exists_bool, PEqualNP.Outside.L_meta_53191.atom, exists_or, or_assoc]
    exact Iff.rfl
  exact PEqualNP.Outside.L_meta_53191.main m t hm (fun S => (raw ∪ S.image neg).toList) need hL hN
    (fun a b => Classical.propDecidable (a = b))
