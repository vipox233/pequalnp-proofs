import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27809_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def isNotOp : GateOp → Bool
  | .not => true
  | _ => false

lemma eval_eq (C : Circuit) (x : List Bool) :
    C.eval x = (C.gates.foldl stp x).getD C.output false := rfl

lemma getD_snoc (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false =
      if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

lemma getD_stp_eq (w : List Bool) (g : Gate) :
    (stp w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  rw [stp, getD_snoc]; simp

lemma getD_stp_ne (w : List Bool) (g : Gate) {i : ℕ} (h1 : i ≠ w.length) :
    (stp w g).getD i false = w.getD i false := by
  rw [stp, getD_snoc]
  by_cases hlt : i < w.length
  · simp [hlt]
  · simp only [hlt, ite_false, h1]
    exact (List.getD_eq_default _ _ (by omega)).symm

lemma getD_stp_eq_of {w : List Bool} {g : Gate} {N : ℕ} (h : w.length = N) :
    (stp w g).getD N false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  rw [← h, getD_stp_eq]

lemma getD_stp_ne_of {w : List Bool} {g : Gate} {i N : ℕ} (h : w.length = N) (hne : i ≠ N) :
    (stp w g).getD i false = w.getD i false :=
  getD_stp_ne w g (h.symm ▸ hne)

lemma oneEach_len {n m : ℕ} (u : Fin n) (v : Fin m) : (oneEach u v).length = n + m := by
  simp [oneEach]

lemma oneEach_getD_left {n m : ℕ} (u : Fin n) (v : Fin m) {k : ℕ} (hk : k < n) :
    (oneEach u v).getD k false = decide (u.val = k) := by
  unfold oneEach
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hk]), List.getElem?_ofFn]
  simp [hk, Fin.ext_iff, eq_comm]

lemma oneEach_getD_right {n m : ℕ} (u : Fin n) (v : Fin m) {k : ℕ} (hk : k < m) :
    (oneEach u v).getD (n + k) false = decide (v.val = k) := by
  unfold oneEach
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp), List.length_ofFn,
    Nat.add_sub_cancel_left, List.getElem?_ofFn]
  simp [hk, Fin.ext_iff, eq_comm]

inductive MTree (α : Type) where
  | leaf (a : α)
  | and (l r : MTree α)
  | or (l r : MTree α)

def MTree.leaves {α : Type} [DecidableEq α] : MTree α → Finset α
  | .leaf a => {a}
  | .and l r => l.leaves ∪ r.leaves
  | .or l r => l.leaves ∪ r.leaves

def MTree.ReadOnce {α : Type} [DecidableEq α] : MTree α → Prop
  | .leaf _ => True
  | .and l r => Disjoint l.leaves r.leaves ∧ l.ReadOnce ∧ r.ReadOnce
  | .or l r => Disjoint l.leaves r.leaves ∧ l.ReadOnce ∧ r.ReadOnce

def MTree.eval {α : Type} (env : α → Bool) : MTree α → Bool
  | .leaf a => env a
  | .and l r => l.eval env && r.eval env
  | .or l r => l.eval env || r.eval env

def MTree.map {α β : Type} (f : α → β) : MTree α → MTree β
  | .leaf a => .leaf (f a)
  | .and l r => .and (l.map f) (r.map f)
  | .or l r => .or (l.map f) (r.map f)

def MTree.subst {α : Type} [DecidableEq α] : MTree α → α → MTree α → MTree α
  | .leaf b, a, s => if b = a then s else .leaf b
  | .and l r, a, s => .and (l.subst a s) (r.subst a s)
  | .or l r, a, s => .or (l.subst a s) (r.subst a s)

lemma MTree.leaves_nonempty {α : Type} [DecidableEq α] (t : MTree α) : t.leaves.Nonempty := by
  induction t with
  | leaf a => exact ⟨a, Finset.mem_singleton_self a⟩
  | and l r ihl _ => obtain ⟨x, hx⟩ := ihl; exact ⟨x, Finset.mem_union_left _ hx⟩
  | or l r ihl _ => obtain ⟨x, hx⟩ := ihl; exact ⟨x, Finset.mem_union_left _ hx⟩

lemma MTree.eval_false {α : Type} (t : MTree α) : t.eval (fun _ => false) = false := by
  induction t with
  | leaf _ => rfl
  | and l r ihl ihr => simp [MTree.eval, ihl, ihr]
  | or l r ihl ihr => simp [MTree.eval, ihl, ihr]

lemma MTree.eval_congr {α : Type} [DecidableEq α] (t : MTree α) {f g : α → Bool}
    (h : ∀ a ∈ t.leaves, f a = g a) : t.eval f = t.eval g := by
  induction t with
  | leaf a => exact h a (Finset.mem_singleton_self a)
  | and l r ihl ihr =>
    simp only [MTree.eval]
    rw [ihl (fun a ha => h a (Finset.mem_union_left _ ha)),
        ihr (fun a ha => h a (Finset.mem_union_right _ ha))]
  | or l r ihl ihr =>
    simp only [MTree.eval]
    rw [ihl (fun a ha => h a (Finset.mem_union_left _ ha)),
        ihr (fun a ha => h a (Finset.mem_union_right _ ha))]

lemma MTree.eval_mono {α : Type} [DecidableEq α] (t : MTree α) {f g : α → Bool}
    (h : ∀ a ∈ t.leaves, f a = true → g a = true) : t.eval f = true → t.eval g = true := by
  induction t with
  | leaf a => exact h a (Finset.mem_singleton_self a)
  | and l r ihl ihr =>
    simp only [MTree.eval, Bool.and_eq_true]
    rintro ⟨hl, hr⟩
    exact ⟨ihl (fun a ha => h a (Finset.mem_union_left _ ha)) hl,
           ihr (fun a ha => h a (Finset.mem_union_right _ ha)) hr⟩
  | or l r ihl ihr =>
    simp only [MTree.eval, Bool.or_eq_true]
    rintro (hl | hr)
    · exact Or.inl (ihl (fun a ha => h a (Finset.mem_union_left _ ha)) hl)
    · exact Or.inr (ihr (fun a ha => h a (Finset.mem_union_right _ ha)) hr)

lemma MTree.eval_map {α β : Type} (f : α → β) (env : β → Bool) (t : MTree α) :
    (t.map f).eval env = t.eval (env ∘ f) := by
  induction t with
  | leaf _ => rfl
  | and l r ihl ihr => simp [MTree.map, MTree.eval, ihl, ihr]
  | or l r ihl ihr => simp [MTree.map, MTree.eval, ihl, ihr]

lemma MTree.leaves_map {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → β) (t : MTree α) :
    (t.map f).leaves = t.leaves.image f := by
  induction t with
  | leaf a => simp [MTree.map, MTree.leaves]
  | and l r ihl ihr => simp [MTree.map, MTree.leaves, ihl, ihr, Finset.image_union]
  | or l r ihl ihr => simp [MTree.map, MTree.leaves, ihl, ihr, Finset.image_union]

lemma MTree.readOnce_map {α β : Type} [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) {t : MTree α} (ht : t.ReadOnce) : (t.map f).ReadOnce := by
  induction t with
  | leaf _ => trivial
  | and l r ihl ihr =>
    refine ⟨?_, ihl ht.2.1, ihr ht.2.2⟩
    rw [MTree.leaves_map, MTree.leaves_map, Finset.disjoint_left]
    intro y hy1 hy2
    rcases Finset.mem_image.mp hy1 with ⟨a1, ha1, rfl⟩
    rcases Finset.mem_image.mp hy2 with ⟨a2, ha2, heq⟩
    have := hf heq
    subst this
    exact Finset.disjoint_left.mp ht.1 ha1 ha2
  | or l r ihl ihr =>
    refine ⟨?_, ihl ht.2.1, ihr ht.2.2⟩
    rw [MTree.leaves_map, MTree.leaves_map, Finset.disjoint_left]
    intro y hy1 hy2
    rcases Finset.mem_image.mp hy1 with ⟨a1, ha1, rfl⟩
    rcases Finset.mem_image.mp hy2 with ⟨a2, ha2, heq⟩
    have := hf heq
    subst this
    exact Finset.disjoint_left.mp ht.1 ha1 ha2

lemma MTree.subst_notMem {α : Type} [DecidableEq α] (a : α) (s t : MTree α) (ha : a ∉ t.leaves) :
    t.subst a s = t := by
  induction t with
  | leaf b =>
    simp only [MTree.leaves, Finset.mem_singleton] at ha
    simp [MTree.subst, Ne.symm ha]
  | and l r ihl ihr =>
    simp only [MTree.leaves, Finset.mem_union, not_or] at ha
    simp [MTree.subst, ihl ha.1, ihr ha.2]
  | or l r ihl ihr =>
    simp only [MTree.leaves, Finset.mem_union, not_or] at ha
    simp [MTree.subst, ihl ha.1, ihr ha.2]

lemma MTree.eval_subst {α : Type} [DecidableEq α] (a : α) (s t : MTree α) (env : α → Bool) :
    (t.subst a s).eval env = t.eval (Function.update env a (s.eval env)) := by
  induction t with
  | leaf b =>
    simp only [MTree.subst]
    split_ifs with h
    · subst h; simp [MTree.eval]
    · simp [MTree.eval, Function.update_of_ne h]
  | and l r ihl ihr => simp [MTree.subst, MTree.eval, ihl, ihr]
  | or l r ihl ihr => simp [MTree.subst, MTree.eval, ihl, ihr]

lemma MTree.leaves_subst {α : Type} [DecidableEq α] (a : α) (s t : MTree α)
    (ht : t.ReadOnce) (ha : a ∈ t.leaves) :
    (t.subst a s).leaves = t.leaves.erase a ∪ s.leaves := by
  induction t with
  | leaf b =>
    simp only [MTree.leaves, Finset.mem_singleton] at ha
    subst ha
    simp [MTree.subst, MTree.leaves]
  | and l r ihl ihr =>
    simp only [MTree.leaves, Finset.mem_union] at ha
    rcases ha with hl | hr
    · have hnr : a ∉ r.leaves := Finset.disjoint_left.mp ht.1 hl
      rw [MTree.subst, MTree.leaves, MTree.subst_notMem a s r hnr, ihl ht.2.1 hl]
      ext x
      simp only [Finset.mem_union, Finset.mem_erase, MTree.leaves]
      constructor
      · rintro ((⟨hxa, hxl⟩ | hxs) | hxr)
        · exact Or.inl ⟨hxa, Or.inl hxl⟩
        · exact Or.inr hxs
        · exact Or.inl ⟨fun e => hnr (e ▸ hxr), Or.inr hxr⟩
      · rintro (⟨hxa, hxl | hxr⟩ | hxs)
        · exact Or.inl (Or.inl ⟨hxa, hxl⟩)
        · exact Or.inr hxr
        · exact Or.inl (Or.inr hxs)
    · have hnl : a ∉ l.leaves := Finset.disjoint_right.mp ht.1 hr
      rw [MTree.subst, MTree.leaves, MTree.subst_notMem a s l hnl, ihr ht.2.2 hr]
      ext x
      simp only [Finset.mem_union, Finset.mem_erase, MTree.leaves]
      constructor
      · rintro (hxl | (⟨hxa, hxr⟩ | hxs))
        · exact Or.inl ⟨fun e => hnl (e ▸ hxl), Or.inl hxl⟩
        · exact Or.inl ⟨hxa, Or.inr hxr⟩
        · exact Or.inr hxs
      · rintro (⟨hxa, hxl | hxr⟩ | hxs)
        · exact Or.inl hxl
        · exact Or.inr (Or.inl ⟨hxa, hxr⟩)
        · exact Or.inr (Or.inr hxs)
  | or l r ihl ihr =>
    simp only [MTree.leaves, Finset.mem_union] at ha
    rcases ha with hl | hr
    · have hnr : a ∉ r.leaves := Finset.disjoint_left.mp ht.1 hl
      rw [MTree.subst, MTree.leaves, MTree.subst_notMem a s r hnr, ihl ht.2.1 hl]
      ext x
      simp only [Finset.mem_union, Finset.mem_erase, MTree.leaves]
      constructor
      · rintro ((⟨hxa, hxl⟩ | hxs) | hxr)
        · exact Or.inl ⟨hxa, Or.inl hxl⟩
        · exact Or.inr hxs
        · exact Or.inl ⟨fun e => hnr (e ▸ hxr), Or.inr hxr⟩
      · rintro (⟨hxa, hxl | hxr⟩ | hxs)
        · exact Or.inl (Or.inl ⟨hxa, hxl⟩)
        · exact Or.inr hxr
        · exact Or.inl (Or.inr hxs)
    · have hnl : a ∉ l.leaves := Finset.disjoint_right.mp ht.1 hr
      rw [MTree.subst, MTree.leaves, MTree.subst_notMem a s l hnl, ihr ht.2.2 hr]
      ext x
      simp only [Finset.mem_union, Finset.mem_erase, MTree.leaves]
      constructor
      · rintro (hxl | (⟨hxa, hxr⟩ | hxs))
        · exact Or.inl ⟨fun e => hnl (e ▸ hxl), Or.inl hxl⟩
        · exact Or.inl ⟨hxa, Or.inr hxr⟩
        · exact Or.inr hxs
      · rintro (⟨hxa, hxl | hxr⟩ | hxs)
        · exact Or.inl hxl
        · exact Or.inr (Or.inl ⟨hxa, hxr⟩)
        · exact Or.inr (Or.inr hxs)

lemma MTree.readOnce_subst {α : Type} [DecidableEq α] (a : α) (s t : MTree α)
    (ht : t.ReadOnce) (hs : s.ReadOnce) (hdisj : Disjoint (t.leaves.erase a) s.leaves) :
    (t.subst a s).ReadOnce := by
  induction t with
  | leaf b =>
    simp only [MTree.subst]
    split_ifs
    · exact hs
    · trivial
  | and l r ihl ihr =>
    by_cases hl : a ∈ l.leaves
    · have hnr : a ∉ r.leaves := Finset.disjoint_left.mp ht.1 hl
      have hd_l : Disjoint (l.leaves.erase a) s.leaves := by
        rw [Finset.disjoint_left] at hdisj ⊢
        intro x hx
        have hx' := Finset.mem_erase.mp hx
        exact hdisj (Finset.mem_erase.mpr ⟨hx'.1, Finset.mem_union_left _ hx'.2⟩)
      have hd_r : Disjoint r.leaves s.leaves := by
        rw [Finset.disjoint_left] at hdisj ⊢
        intro x hx
        exact hdisj (Finset.mem_erase.mpr ⟨fun e => hnr (e ▸ hx), Finset.mem_union_right _ hx⟩)
      rw [MTree.subst, MTree.subst_notMem a s r hnr]
      refine ⟨?_, ihl ht.2.1 hd_l, ht.2.2⟩
      rw [MTree.leaves_subst a s l ht.2.1 hl, Finset.disjoint_union_left]
      exact ⟨Finset.disjoint_of_subset_left (Finset.erase_subset a l.leaves) ht.1, hd_r.symm⟩
    · rw [MTree.subst, MTree.subst_notMem a s l hl]
      by_cases hr : a ∈ r.leaves
      · have hd_r : Disjoint (r.leaves.erase a) s.leaves := by
          rw [Finset.disjoint_left] at hdisj ⊢
          intro x hx
          have hx' := Finset.mem_erase.mp hx
          exact hdisj (Finset.mem_erase.mpr ⟨hx'.1, Finset.mem_union_right _ hx'.2⟩)
        have hd_l : Disjoint l.leaves s.leaves := by
          rw [Finset.disjoint_left] at hdisj ⊢
          intro x hx
          exact hdisj (Finset.mem_erase.mpr ⟨fun e => hl (e ▸ hx), Finset.mem_union_left _ hx⟩)
        refine ⟨?_, ht.2.1, ihr ht.2.2 hd_r⟩
        rw [MTree.leaves_subst a s r ht.2.2 hr, Finset.disjoint_union_right]
        exact ⟨Finset.disjoint_of_subset_right (Finset.erase_subset a r.leaves) ht.1, hd_l⟩
      · rw [MTree.subst_notMem a s r hr]; exact ht
  | or l r ihl ihr =>
    by_cases hl : a ∈ l.leaves
    · have hnr : a ∉ r.leaves := Finset.disjoint_left.mp ht.1 hl
      have hd_l : Disjoint (l.leaves.erase a) s.leaves := by
        rw [Finset.disjoint_left] at hdisj ⊢
        intro x hx
        have hx' := Finset.mem_erase.mp hx
        exact hdisj (Finset.mem_erase.mpr ⟨hx'.1, Finset.mem_union_left _ hx'.2⟩)
      have hd_r : Disjoint r.leaves s.leaves := by
        rw [Finset.disjoint_left] at hdisj ⊢
        intro x hx
        exact hdisj (Finset.mem_erase.mpr ⟨fun e => hnr (e ▸ hx), Finset.mem_union_right _ hx⟩)
      rw [MTree.subst, MTree.subst_notMem a s r hnr]
      refine ⟨?_, ihl ht.2.1 hd_l, ht.2.2⟩
      rw [MTree.leaves_subst a s l ht.2.1 hl, Finset.disjoint_union_left]
      exact ⟨Finset.disjoint_of_subset_left (Finset.erase_subset a l.leaves) ht.1, hd_r.symm⟩
    · rw [MTree.subst, MTree.subst_notMem a s l hl]
      by_cases hr : a ∈ r.leaves
      · have hd_r : Disjoint (r.leaves.erase a) s.leaves := by
          rw [Finset.disjoint_left] at hdisj ⊢
          intro x hx
          have hx' := Finset.mem_erase.mp hx
          exact hdisj (Finset.mem_erase.mpr ⟨hx'.1, Finset.mem_union_right _ hx'.2⟩)
        have hd_l : Disjoint l.leaves s.leaves := by
          rw [Finset.disjoint_left] at hdisj ⊢
          intro x hx
          exact hdisj (Finset.mem_erase.mpr ⟨fun e => hl (e ▸ hx), Finset.mem_union_left _ hx⟩)
        refine ⟨?_, ht.2.1, ihr ht.2.2 hd_r⟩
        rw [MTree.leaves_subst a s r ht.2.2 hr, Finset.disjoint_union_right]
        exact ⟨Finset.disjoint_of_subset_right (Finset.erase_subset a r.leaves) ht.1, hd_l⟩
      · rw [MTree.subst_notMem a s r hr]; exact ht

lemma MTree.eval_singleton_eq {α : Type} [DecidableEq α] (t : MTree α) (ht : t.ReadOnce)
    (a : α) (hsub : t.leaves = {a}) (env : α → Bool) :
    t.eval env = env a := by
  induction t with
  | leaf b =>
    simp only [MTree.leaves, Finset.singleton_inj] at hsub
    subst hsub; rfl
  | and l r =>
    exfalso
    obtain ⟨x, hx⟩ := l.leaves_nonempty
    obtain ⟨y, hy⟩ := r.leaves_nonempty
    have hx' : x = a := by
      have : x ∈ (MTree.and l r).leaves := Finset.mem_union_left _ hx
      rw [hsub, Finset.mem_singleton] at this; exact this
    have hy' : y = a := by
      have : y ∈ (MTree.and l r).leaves := Finset.mem_union_right _ hy
      rw [hsub, Finset.mem_singleton] at this; exact this
    subst hx'; subst hy'
    exact Finset.disjoint_left.mp ht.1 hx hy
  | or l r =>
    exfalso
    obtain ⟨x, hx⟩ := l.leaves_nonempty
    obtain ⟨y, hy⟩ := r.leaves_nonempty
    have hx' : x = a := by
      have : x ∈ (MTree.or l r).leaves := Finset.mem_union_left _ hx
      rw [hsub, Finset.mem_singleton] at this; exact this
    have hy' : y = a := by
      have : y ∈ (MTree.or l r).leaves := Finset.mem_union_right _ hy
      rw [hsub, Finset.mem_singleton] at this; exact this
    subst hx'; subst hy'
    exact Finset.disjoint_left.mp ht.1 hx hy

lemma MTree.min_pair_equiv {α : Type} [DecidableEq α] (t : MTree α) (ht : t.ReadOnce)
    (z a b : α) (hza : z ≠ a) (hzb : z ≠ b) (hab : a ≠ b)
    (ha_t : t.eval (fun w => decide (w = z ∨ w = a)) = true)
    (hb_t : t.eval (fun w => decide (w = z ∨ w = b)) = true)
    (hz_f : t.eval (fun w => decide (w = z)) = false)
    (ha_f : t.eval (fun w => decide (w = a)) = false)
    (hb_f : t.eval (fun w => decide (w = b)) = false) :
    ∀ env : α → Bool, env a = false → env b = false →
      t.eval (Function.update env a true) = t.eval (Function.update env b true) := by
  induction t with
  | leaf w =>
    exfalso
    simp only [MTree.eval, decide_eq_true_eq, decide_eq_false_iff_not] at ha_t hz_f ha_f
    rcases ha_t with rfl | rfl
    · exact hz_f rfl
    · exact ha_f rfl
  | and l r ihl ihr =>
    simp only [MTree.eval, Bool.and_eq_true] at ha_t hb_t
    have hz_in : z ∈ l.leaves ∨ z ∈ r.leaves := by
      by_contra h
      push Not at h
      have hl : l.eval (fun w => decide (w = z ∨ w = a)) = l.eval (fun w => decide (w = a)) :=
        l.eval_congr (fun w hw => by simp [show w ≠ z from fun e => h.1 (e ▸ hw)])
      have hr : r.eval (fun w => decide (w = z ∨ w = a)) = r.eval (fun w => decide (w = a)) :=
        r.eval_congr (fun w hw => by simp [show w ≠ z from fun e => h.2 (e ▸ hw)])
      have : (MTree.and l r).eval (fun w => decide (w = a)) = true := by
        rw [MTree.eval, ← hl, ← hr, ha_t.1, ha_t.2]; rfl
      rw [ha_f] at this; cases this
    rcases hz_in with hzl | hzr
    · have hznr : z ∉ r.leaves := Finset.disjoint_left.mp ht.1 hzl
      have hra : r.eval (fun w => decide (w = a)) = true := by
        have hc : r.eval (fun w => decide (w = z ∨ w = a)) = r.eval (fun w => decide (w = a)) :=
          r.eval_congr (fun w hw => by have hne : w ≠ z := fun e => hznr (e ▸ hw); simp [hne])
        rw [← hc]; exact ha_t.2
      have hrb : r.eval (fun w => decide (w = b)) = true := by
        have hc : r.eval (fun w => decide (w = z ∨ w = b)) = r.eval (fun w => decide (w = b)) :=
          r.eval_congr (fun w hw => by have hne : w ≠ z := fun e => hznr (e ▸ hw); simp [hne])
        rw [← hc]; exact hb_t.2
      have har : a ∈ r.leaves := by
        by_contra hna
        have : r.eval (fun w => decide (w = a)) = r.eval (fun _ => false) :=
          r.eval_congr (fun w hw => by have hne : w ≠ a := fun e => hna (e ▸ hw); simp [hne])
        rw [MTree.eval_false] at this
        rw [hra] at this; cases this
      have hbr : b ∈ r.leaves := by
        by_contra hnb
        have : r.eval (fun w => decide (w = b)) = r.eval (fun _ => false) :=
          r.eval_congr (fun w hw => by have hne : w ≠ b := fun e => hnb (e ▸ hw); simp [hne])
        rw [MTree.eval_false] at this
        rw [hrb] at this; cases this
      have hanl : a ∉ l.leaves := Finset.disjoint_right.mp ht.1 har
      have hbnl : b ∉ l.leaves := Finset.disjoint_right.mp ht.1 hbr
      intro env _ _
      simp only [MTree.eval]
      have hl_eq : l.eval (Function.update env a true) = l.eval (Function.update env b true) :=
        l.eval_congr (fun w hw => by
          have hwa : w ≠ a := fun e => hanl (e ▸ hw)
          have hwb : w ≠ b := fun e => hbnl (e ▸ hw)
          rw [Function.update_of_ne hwa, Function.update_of_ne hwb])
      have hra' : r.eval (Function.update env a true) = true :=
        r.eval_mono (fun w _ hw => by
          have : w = a := of_decide_eq_true hw
          subst this; simp) hra
      have hrb' : r.eval (Function.update env b true) = true :=
        r.eval_mono (fun w _ hw => by
          have : w = b := of_decide_eq_true hw
          subst this; simp) hrb
      rw [hl_eq, hra', hrb']
    · have hznl : z ∉ l.leaves := Finset.disjoint_right.mp ht.1 hzr
      have hla : l.eval (fun w => decide (w = a)) = true := by
        have hc : l.eval (fun w => decide (w = z ∨ w = a)) = l.eval (fun w => decide (w = a)) :=
          l.eval_congr (fun w hw => by have hne : w ≠ z := fun e => hznl (e ▸ hw); simp [hne])
        rw [← hc]; exact ha_t.1
      have hlb : l.eval (fun w => decide (w = b)) = true := by
        have hc : l.eval (fun w => decide (w = z ∨ w = b)) = l.eval (fun w => decide (w = b)) :=
          l.eval_congr (fun w hw => by have hne : w ≠ z := fun e => hznl (e ▸ hw); simp [hne])
        rw [← hc]; exact hb_t.1
      have hal : a ∈ l.leaves := by
        by_contra hna
        have : l.eval (fun w => decide (w = a)) = l.eval (fun _ => false) :=
          l.eval_congr (fun w hw => by have hne : w ≠ a := fun e => hna (e ▸ hw); simp [hne])
        rw [MTree.eval_false] at this
        rw [hla] at this; cases this
      have hbl : b ∈ l.leaves := by
        by_contra hnb
        have : l.eval (fun w => decide (w = b)) = l.eval (fun _ => false) :=
          l.eval_congr (fun w hw => by have hne : w ≠ b := fun e => hnb (e ▸ hw); simp [hne])
        rw [MTree.eval_false] at this
        rw [hlb] at this; cases this
      have hanr : a ∉ r.leaves := Finset.disjoint_left.mp ht.1 hal
      have hbnr : b ∉ r.leaves := Finset.disjoint_left.mp ht.1 hbl
      intro env _ _
      simp only [MTree.eval]
      have hr_eq : r.eval (Function.update env a true) = r.eval (Function.update env b true) :=
        r.eval_congr (fun w hw => by
          have hwa : w ≠ a := fun e => hanr (e ▸ hw)
          have hwb : w ≠ b := fun e => hbnr (e ▸ hw)
          rw [Function.update_of_ne hwa, Function.update_of_ne hwb])
      have hla' : l.eval (Function.update env a true) = true :=
        l.eval_mono (fun w _ hw => by
          have : w = a := of_decide_eq_true hw
          subst this; simp) hla
      have hlb' : l.eval (Function.update env b true) = true :=
        l.eval_mono (fun w _ hw => by
          have : w = b := of_decide_eq_true hw
          subst this; simp) hlb
      rw [hr_eq, hla', hlb']
  | or l r ihl ihr =>
    simp only [MTree.eval, Bool.or_eq_false_iff] at hz_f ha_f hb_f
    simp only [MTree.eval, Bool.or_eq_true] at ha_t hb_t
    have hz_side : ∀ (t1 t2 : MTree α), Disjoint t1.leaves t2.leaves →
        t1.eval (fun w => decide (w = z)) = false →
        t1.eval (fun w => decide (w = a)) = false →
        t1.eval (fun w => decide (w = z ∨ w = a)) = true →
        z ∈ t1.leaves ∧ a ∈ t1.leaves := by
      intro t1 t2 _ h1z h1a h1za
      constructor
      · by_contra hnz
        have : t1.eval (fun w => decide (w = z ∨ w = a)) = t1.eval (fun w => decide (w = a)) :=
          t1.eval_congr (fun w hw => by have hne : w ≠ z := fun e => hnz (e ▸ hw); simp [hne])
        rw [h1a] at this; rw [h1za] at this; cases this
      · by_contra hna
        have : t1.eval (fun w => decide (w = z ∨ w = a)) = t1.eval (fun w => decide (w = z)) :=
          t1.eval_congr (fun w hw => by have hne : w ≠ a := fun e => hna (e ▸ hw); simp [hne])
        rw [h1z] at this; rw [h1za] at this; cases this
    have hz_side_b : ∀ (t1 t2 : MTree α), Disjoint t1.leaves t2.leaves →
        t1.eval (fun w => decide (w = z)) = false →
        t1.eval (fun w => decide (w = b)) = false →
        t1.eval (fun w => decide (w = z ∨ w = b)) = true →
        z ∈ t1.leaves ∧ b ∈ t1.leaves := by
      intro t1 t2 _ h1z h1b h1zb
      constructor
      · by_contra hnz
        have : t1.eval (fun w => decide (w = z ∨ w = b)) = t1.eval (fun w => decide (w = b)) :=
          t1.eval_congr (fun w hw => by have hne : w ≠ z := fun e => hnz (e ▸ hw); simp [hne])
        rw [h1b] at this; rw [h1zb] at this; cases this
      · by_contra hnb
        have : t1.eval (fun w => decide (w = z ∨ w = b)) = t1.eval (fun w => decide (w = z)) :=
          t1.eval_congr (fun w hw => by have hne : w ≠ b := fun e => hnb (e ▸ hw); simp [hne])
        rw [h1z] at this; rw [h1zb] at this; cases this
    rcases ha_t with hal | har
    · have ⟨hzl, ha_in_l⟩ := hz_side l r ht.1 hz_f.1 ha_f.1 hal
      have hbl : l.eval (fun w => decide (w = z ∨ w = b)) = true := by
        rcases hb_t with hbl | hbr
        · exact hbl
        · exfalso
          have ⟨hzr, _⟩ := hz_side_b r l ht.1.symm hz_f.2 hb_f.2 hbr
          exact Finset.disjoint_left.mp ht.1 hzl hzr
      have ⟨_, hb_in_l⟩ := hz_side_b l r ht.1 hz_f.1 hb_f.1 hbl
      have hanr : a ∉ r.leaves := Finset.disjoint_left.mp ht.1 ha_in_l
      have hbnr : b ∉ r.leaves := Finset.disjoint_left.mp ht.1 hb_in_l
      intro env hea heb
      simp only [MTree.eval]
      have hr_eq : r.eval (Function.update env a true) = r.eval (Function.update env b true) :=
        r.eval_congr (fun w hw => by
          have hwa : w ≠ a := fun e => hanr (e ▸ hw)
          have hwb : w ≠ b := fun e => hbnr (e ▸ hw)
          rw [Function.update_of_ne hwa, Function.update_of_ne hwb])
      rw [ihl ht.2.1 hal hbl hz_f.1 ha_f.1 hb_f.1 env hea heb, hr_eq]
    · have ⟨hzr, ha_in_r⟩ := hz_side r l ht.1.symm hz_f.2 ha_f.2 har
      have hbr : r.eval (fun w => decide (w = z ∨ w = b)) = true := by
        rcases hb_t with hbl | hbr
        · exfalso
          have ⟨hzl, _⟩ := hz_side_b l r ht.1 hz_f.1 hb_f.1 hbl
          exact Finset.disjoint_left.mp ht.1 hzl hzr
        · exact hbr
      have ⟨_, hb_in_r⟩ := hz_side_b r l ht.1.symm hz_f.2 hb_f.2 hbr
      have hanl : a ∉ l.leaves := Finset.disjoint_right.mp ht.1 ha_in_r
      have hbnl : b ∉ l.leaves := Finset.disjoint_right.mp ht.1 hb_in_r
      intro env hea heb
      simp only [MTree.eval]
      have hl_eq : l.eval (Function.update env a true) = l.eval (Function.update env b true) :=
        l.eval_congr (fun w hw => by
          have hwa : w ≠ a := fun e => hanl (e ▸ hw)
          have hwb : w ≠ b := fun e => hbnl (e ▸ hw)
          rw [Function.update_of_ne hwa, Function.update_of_ne hwb])
      rw [ihr ht.2.2 har hbr hz_f.2 ha_f.2 hb_f.2 env hea heb, hl_eq]

inductive Slot where
  | sh
  | neg
  | wire (w : ℕ)
  deriving DecidableEq

def slotWires (s : Finset Slot) : Finset ℕ :=
  s.biUnion (fun x => match x with | .wire w => {w} | _ => ∅)

lemma mem_slotWires {s : Finset Slot} {w : ℕ} : w ∈ slotWires s ↔ Slot.wire w ∈ s := by
  simp only [slotWires, Finset.mem_biUnion]
  constructor
  · rintro ⟨a, ha, hw⟩
    cases a with
    | wire u => simp at hw; subst hw; exact ha
    | sh => simp at hw
    | neg => simp at hw
  · intro h; exact ⟨.wire w, h, by simp⟩

def optWires (s : Finset (Option ℕ)) : Finset ℕ :=
  s.biUnion (fun x => match x with | some w => {w} | none => ∅)

lemma mem_optWires {s : Finset (Option ℕ)} {w : ℕ} : w ∈ optWires s ↔ some w ∈ s := by
  simp only [optWires, Finset.mem_biUnion]
  constructor
  · rintro ⟨a, ha, hw⟩
    cases a with
    | some u => simp at hw; subst hw; exact ha
    | none => simp at hw
  · intro h; exact ⟨some w, h, by simp⟩

def DependsOn (N : ℕ) (f : List Bool → Bool) (R : Finset ℕ) : Prop :=
  ∀ x y : List Bool, x.length = N → y.length = N →
    (∀ i ∈ R, x.getD i false = y.getD i false) → f x = f y

def UnateOn (N : ℕ) (f : List Bool → Bool) (R : Finset ℕ) (sgn : ℕ → Bool) : Prop :=
  ∀ x y : List Bool, x.length = N → y.length = N →
    (∀ i ∈ R, if sgn i then (x.getD i false = true → y.getD i false = true)
              else (y.getD i false = true → x.getD i false = true)) →
    f x = true → f y = true

def effInputs (g : Gate) : List ℕ :=
  match g.op with
  | .not => match g.inputs with | [] => [] | a :: _ => [a]
  | _ => g.inputs

lemma effInputs_eval (g : Gate) (w1 w2 : List Bool)
    (h : ∀ i ∈ effInputs g, w1.getD i false = w2.getD i false) :
    g.op.eval (g.inputs.map fun i => w1.getD i false) =
      g.op.eval (g.inputs.map fun i => w2.getD i false) := by
  cases hop : g.op with
  | not =>
    cases hin : g.inputs with
    | nil => rfl
    | cons a tl =>
      simp only [GateOp.eval, List.map_cons, List.headD_cons]
      congr 1
      exact h a (by simp [effInputs, hop, hin])
  | and =>
    congr 1; apply List.map_congr_left; intro i hi; exact h i (by simp [effInputs, hop, hi])
  | or =>
    congr 1; apply List.map_congr_left; intro i hi; exact h i (by simp [effInputs, hop, hi])
  | mod _ =>
    congr 1; apply List.map_congr_left; intro i hi; exact h i (by simp [effInputs, hop, hi])
  | maj =>
    congr 1; apply List.map_congr_left; intro i hi; exact h i (by simp [effInputs, hop, hi])

lemma mono_step_andOr (g : Gate) (hop : g.op = .and ∨ g.op = .or) (x y : List Bool) (s : Bool)
    (h : ∀ i ∈ g.inputs, if s then (x.getD i false = true → y.getD i false = true)
                         else (y.getD i false = true → x.getD i false = true)) :
    if s then
      (g.op.eval (g.inputs.map fun i => x.getD i false) = true →
       g.op.eval (g.inputs.map fun i => y.getD i false) = true)
    else
      (g.op.eval (g.inputs.map fun i => y.getD i false) = true →
       g.op.eval (g.inputs.map fun i => x.getD i false) = true) := by
  cases s with
  | true =>
    simp only [ite_true] at h ⊢
    rcases hop with h1 | h1 <;> rw [h1]
    · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
      intro hx b hb; rcases hb with ⟨i, hi, rfl⟩; exact h i hi (hx _ ⟨i, hi, rfl⟩)
    · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
      rintro ⟨_, ⟨i, hi, rfl⟩, hxi⟩; exact ⟨_, ⟨i, hi, rfl⟩, h i hi hxi⟩
  | false =>
    simp only [Bool.false_eq_true, ite_false] at h ⊢
    rcases hop with h1 | h1 <;> rw [h1]
    · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
      intro hy b hb; rcases hb with ⟨i, hi, rfl⟩; exact h i hi (hy _ ⟨i, hi, rfl⟩)
    · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
      rintro ⟨_, ⟨i, hi, rfl⟩, hyi⟩; exact ⟨_, ⟨i, hi, rfl⟩, h i hi hyi⟩

structure Decomp (N : ℕ) (f : List Bool → Bool) where
  tPos : MTree Slot
  tNeg : MTree (Option ℕ)
  sSh : MTree ℕ
  roPos : tPos.ReadOnce
  roNeg : tNeg.ReadOnce
  roSh : sSh.ReadOnce
  sh_in_pos : Slot.sh ∈ tPos.leaves
  neg_in_pos : Slot.neg ∈ tPos.leaves
  sh_in_neg : none ∈ tNeg.leaves
  disj_PH : Disjoint (slotWires tPos.leaves) (optWires tNeg.leaves)
  disj_PU : Disjoint (slotWires tPos.leaves) sSh.leaves
  disj_HU : Disjoint (optWires tNeg.leaves) sSh.leaves
  eval_eq : ∀ x : List Bool, x.length = N →
    let sh := sSh.eval (fun w => x.getD w false)
    let neg := !tNeg.eval (fun o => match o with | none => sh | some w => x.getD w false)
    f x = tPos.eval (fun s => match s with | .sh => sh | .neg => neg | .wire w => x.getD w false)

def Decomp.wires {N : ℕ} {f : List Bool → Bool} (D : Decomp N f) : Finset ℕ :=
  slotWires D.tPos.leaves ∪ optWires D.tNeg.leaves ∪ D.sSh.leaves

lemma Decomp.dependsOn {N : ℕ} {f : List Bool → Bool} (D : Decomp N f) :
    DependsOn N f D.wires := by
  intro x y hx hy hxy
  rw [D.eval_eq x hx, D.eval_eq y hy]
  have hsh : D.sSh.eval (fun w => x.getD w false) = D.sSh.eval (fun w => y.getD w false) :=
    D.sSh.eval_congr (fun w hw => hxy w (Finset.mem_union_right _ hw))
  have hneg : D.tNeg.eval (fun o => match o with | none => D.sSh.eval (fun w => x.getD w false) | some w => x.getD w false) =
      D.tNeg.eval (fun o => match o with | none => D.sSh.eval (fun w => y.getD w false) | some w => y.getD w false) := by
    apply D.tNeg.eval_congr
    intro o ho
    cases o with
    | none => exact hsh
    | some w => exact hxy w (Finset.mem_union_left _ (Finset.mem_union_right _ (mem_optWires.mpr ho)))
  apply D.tPos.eval_congr
  intro s hs
  cases s with
  | sh => exact hsh
  | neg => dsimp only; rw [hneg]
  | wire w => exact hxy w (Finset.mem_union_left _ (Finset.mem_union_left _ (mem_slotWires.mpr hs)))

structure NegTree (N : ℕ) (f : List Bool → Bool) where
  tPos : MTree (Option ℕ)
  tNeg : MTree ℕ
  roPos : tPos.ReadOnce
  roNeg : tNeg.ReadOnce
  neg_in_pos : none ∈ tPos.leaves
  disj_PH : Disjoint (optWires tPos.leaves) tNeg.leaves
  eval_eq : ∀ x : List Bool, x.length = N →
    let neg := !tNeg.eval (fun w => x.getD w false)
    f x = tPos.eval (fun o => match o with | none => neg | some w => x.getD w false)

def NegTree.wires {N : ℕ} {f : List Bool → Bool} (T : NegTree N f) : Finset ℕ :=
  optWires T.tPos.leaves ∪ T.tNeg.leaves

lemma NegTree.unateOn {N : ℕ} {f : List Bool → Bool} (T : NegTree N f) :
    UnateOn N f T.wires (fun w => decide (w ∈ optWires T.tPos.leaves)) := by
  intro x y hx hy hxy hfx
  rw [T.eval_eq x hx] at hfx
  rw [T.eval_eq y hy]
  have hneg : (!T.tNeg.eval (fun w => x.getD w false)) = true → (!T.tNeg.eval (fun w => y.getD w false)) = true := by
    simp only [Bool.not_eq_true']
    intro hx0
    by_contra hy1
    have hyt : T.tNeg.eval (fun w => y.getD w false) = true := Bool.eq_true_of_not_eq_false hy1
    have hxt : T.tNeg.eval (fun w => x.getD w false) = true := by
      apply T.tNeg.eval_mono _ hyt
      intro w hw
      have hnp : w ∉ optWires T.tPos.leaves := Finset.disjoint_right.mp T.disj_PH hw
      have h1 := hxy w (Finset.mem_union_right _ hw)
      simpa [hnp] using h1
    rw [hx0] at hxt; cases hxt
  apply T.tPos.eval_mono _ hfx
  intro o ho
  cases o with
  | none => exact hneg
  | some w =>
    have hw : w ∈ optWires T.tPos.leaves := mem_optWires.mpr ho
    have h1 := hxy w (Finset.mem_union_left _ hw)
    simpa [hw] using h1

def TightInv (N s : ℕ) (hasNot : Bool) (f : List Bool → Bool) : Prop :=
  (hasNot = false ∧ ∃ t : MTree ℕ, t.ReadOnce ∧ t.leaves.card ≤ s + 1 ∧
    ∀ x : List Bool, x.length = N → f x = t.eval (fun w => x.getD w false)) ∨
  (∃ R : Finset ℕ, R.card ≤ s ∧ UnateOn N f R (fun _ => true)) ∨
  (∃ T : NegTree N f, T.wires.card ≤ s) ∨
  (∃ (R : Finset ℕ) (sgn : ℕ → Bool), R.card + 1 ≤ s ∧ UnateOn N f R sgn) ∨
  (∃ D : Decomp N f, D.wires.card + 1 ≤ s) ∨
  (∃ R : Finset ℕ, R.card + 2 ≤ s ∧ DependsOn N f R)

lemma unate_to_dep {N : ℕ} {f : List Bool → Bool} {R : Finset ℕ} {sgn : ℕ → Bool}
    (hUn : UnateOn N f R sgn) : DependsOn N f R := by
  intro x y hx hy heq
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact hUn x y hx hy (fun i hi => by split_ifs <;> intro h <;> first | rwa [← heq i hi] | rwa [heq i hi])
  · exact hUn y x hy hx (fun i hi => by split_ifs <;> intro h <;> first | rwa [heq i hi] | rwa [← heq i hi])

lemma dep_step_aux {N : ℕ} {f : List Bool → Bool} {R : Finset ℕ} (hDep : DependsOn (N + 1) f R)
    (g : Gate) :
    DependsOn N (fun x => f (stp x g)) (if N ∈ R then R.erase N ∪ (effInputs g).toFinset else R) := by
  split_ifs with ht
  · intro x y hx hy hxy
    apply hDep (stp x g) (stp y g) (by simp [stp, hx]) (by simp [stp, hy])
    intro i hi
    by_cases hiN : i = N
    · subst hiN
      rw [← hx, getD_stp_eq, hx, ← hy, getD_stp_eq]
      exact effInputs_eval g x y (fun a ha => hxy a (Finset.mem_union_right _ (List.mem_toFinset.mpr ha)))
    · rw [getD_stp_ne x g (by omega), getD_stp_ne y g (by omega)]
      exact hxy i (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hiN, hi⟩))
  · intro x y hx hy hxy
    apply hDep (stp x g) (stp y g) (by simp [stp, hx]) (by simp [stp, hy])
    intro i hi
    have hiN : i ≠ N := fun e => ht (e ▸ hi)
    rw [getD_stp_ne x g (by omega), getD_stp_ne y g (by omega)]
    exact hxy i hi

lemma effInputs_len_le2 (g : Gate) (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (effInputs g).length ≤ 2 := by
  have hop : g.op = .and ∨ g.op = .or ∨ g.op = .not := by
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hg.1
  rcases hop with h | h | h
  · simpa [effInputs, h] using hg.2
  · simpa [effInputs, h] using hg.2
  · cases hin : g.inputs <;> simp [effInputs, h, hin]

lemma unate_step_unate_or_dep {N s : ℕ} {f : List Bool → Bool} {R : Finset ℕ} {sgn : ℕ → Bool}
    (hUn : UnateOn (N + 1) f R sgn) (hRc : R.card + 1 ≤ s)
    (g : Gate) (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (∃ (R' : Finset ℕ) (sgn' : ℕ → Bool), R'.card + 1 ≤ s + 1 ∧ UnateOn N (fun x => f (stp x g)) R' sgn') ∨
    (∃ R' : Finset ℕ, R'.card + 2 ≤ s + 1 ∧ DependsOn N (fun x => f (stp x g)) R') := by
  have hop : g.op = .and ∨ g.op = .or ∨ g.op = .not := by
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hg.1
  by_cases ht : N ∈ R
  · let R' := R.erase N ∪ (effInputs g).toFinset
    by_cases hbig : R'.card ≤ R.card
    · refine Or.inr ⟨R', by omega, ?_⟩
      simpa [ht, R'] using dep_step_aux (unate_to_dep hUn) g
    · have hpos : 0 < R.card := Finset.card_pos.mpr ⟨N, ht⟩
      have herase : (R.erase N).card = R.card - 1 := Finset.card_erase_of_mem ht
      have h1 : R'.card ≤ (R.erase N).card + (effInputs g).toFinset.card :=
        Finset.card_union_le (R.erase N) (effInputs g).toFinset
      have h2 := List.toFinset_card_le (effInputs g)
      have h3 := effInputs_len_le2 g hg
      have heff2 : (effInputs g).length = 2 := by omega
      have hop_ao : g.op = .and ∨ g.op = .or := by
        rcases hop with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exfalso; cases hin : g.inputs <;> simp [effInputs, h, hin] at heff2
      have heff_eq : effInputs g = g.inputs := by rcases hop_ao with h | h <;> simp [effInputs, h]
      rw [heff_eq] at heff2
      rcases hgin : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> simp [hgin] at heff2
      have hR'eq : R' = insert a (insert b (R.erase N)) := by ext v; simp [R', heff_eq, hgin]
      have ha_not : a ∉ R.erase N := by
        intro ha
        have : R' = insert b (R.erase N) := by rw [hR'eq]; ext v; simp; grind
        have hc := Finset.card_insert_le b (R.erase N)
        rw [← this] at hc; omega
      have hb_not : b ∉ R.erase N := by
        intro hb
        have : R' = insert a (R.erase N) := by rw [hR'eq]; ext v; simp; grind
        have hc := Finset.card_insert_le a (R.erase N)
        rw [← this] at hc; omega
      have hR'card : R'.card + 1 ≤ s + 1 := by
        rw [hR'eq]
        have hc1 := Finset.card_insert_le a (insert b (R.erase N))
        have hc2 := Finset.card_insert_le b (R.erase N)
        omega
      let sgn' := Function.update (Function.update sgn a (sgn N)) b (sgn N)
      refine Or.inl ⟨R', sgn', hR'card, ?_⟩
      intro x y hx hy hxy
      apply hUn (stp x g) (stp y g) (by simp [stp, hx]) (by simp [stp, hy])
      intro i hi
      by_cases hiN : i = N
      · subst hiN
        have hm := mono_step_andOr g hop_ao x y (sgn i) (fun u hu => by
          rw [hgin] at hu
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
          rcases hu with rfl | rfl
          · have h1 := hxy u (by rw [hR'eq]; simp)
            by_cases hub : u = b
            · subst hub; simpa [sgn'] using h1
            · simpa [sgn', Function.update_of_ne hub] using h1
          · have h1 := hxy u (by rw [hR'eq]; simp)
            simpa [sgn'] using h1)
        simp only [show (stp x g).getD i false = g.op.eval (g.inputs.map fun a => x.getD a false) by rw [← hx, getD_stp_eq],
          show (stp y g).getD i false = g.op.eval (g.inputs.map fun a => y.getD a false) by rw [← hy, getD_stp_eq]]
        exact hm
      · have hi' : i ∈ R.erase N := Finset.mem_erase.mpr ⟨hiN, hi⟩
        have hia : i ≠ a := fun e => ha_not (e ▸ hi')
        have hib : i ≠ b := fun e => hb_not (e ▸ hi')
        have hdir := hxy i (by rw [hR'eq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hi'))
        simp only [sgn', Function.update_of_ne hib, Function.update_of_ne hia] at hdir
        rw [getD_stp_ne x g (by omega), getD_stp_ne y g (by omega)]
        exact hdir
  · refine Or.inr ⟨R, by omega, ?_⟩
    simpa [ht] using dep_step_aux (unate_to_dep hUn) g

lemma slot_wire_inj {a b : ℕ} : Slot.wire a = Slot.wire b ↔ a = b :=
  ⟨fun h => by cases h; rfl, fun h => by rw [h]⟩

def mkBinTree {α : Type} (op : GateOp) (a b : α) : MTree α :=
  match op with
  | .and => MTree.and (.leaf a) (.leaf b)
  | _ => MTree.or (.leaf a) (.leaf b)

lemma mkBinTree_leaves {α : Type} [DecidableEq α] (op : GateOp) (a b : α) :
    (mkBinTree op a b).leaves = {a, b} := by
  cases op <;> simp [mkBinTree, MTree.leaves]

lemma mkBinTree_ro {α : Type} [DecidableEq α] (op : GateOp) (a b : α) (hab : a ≠ b) :
    (mkBinTree op a b).ReadOnce := by
  cases op <;> simp [mkBinTree, MTree.ReadOnce, MTree.leaves, hab]

lemma mkBinTree_eval (g : Gate) (hop : g.op = .and ∨ g.op = .or) (a b : ℕ) (hin : g.inputs = [a, b])
    (x : List Bool) :
    g.op.eval (g.inputs.map fun i => x.getD i false) =
      (mkBinTree g.op a b).eval (fun i => x.getD i false) := by
  rcases hop with h | h <;> simp [h, hin, mkBinTree, GateOp.eval, MTree.eval]

lemma mkBinTree_eval_comm {α : Type} (op : GateOp) (a b : α) (env : α → Bool) :
    (mkBinTree op a b).eval env = (mkBinTree op b a).eval env := by
  cases op <;> simp [mkBinTree, MTree.eval, Bool.and_comm, Bool.or_comm]

lemma mkBinTree_eval_map {α β : Type} (op : GateOp) (f : α → β) (a b : α) (env : β → Bool) :
    (mkBinTree op (f a) (f b)).eval env = (mkBinTree op a b).eval (env ∘ f) := by
  cases op <;> simp [mkBinTree, MTree.eval]

lemma tightInv_step_treePos (N s : ℕ) (hasNot : Bool) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (f : List Bool → Bool) (hfn : hasNot = false)
    (t : MTree ℕ) (hro : t.ReadOnce) (htc : t.leaves.card ≤ s + 1)
    (hte : ∀ x : List Bool, x.length = N + 1 → f x = t.eval (fun w => x.getD w false)) :
    TightInv N (s + 1) (hasNot || isNotOp g.op) (fun x => f (stp x g)) := by
  have hop : g.op = .and ∨ g.op = .or ∨ g.op = .not := by
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hg.1
  have hMono : UnateOn (N + 1) f t.leaves (fun _ => true) := by
    intro x y hx hy hxy hfx
    rw [hte x hx] at hfx; rw [hte y hy]
    exact t.eval_mono (fun a ha => by simpa using hxy a ha) hfx
  by_cases ht : N ∈ t.leaves
  · rcases hop with h | h | h
    · have hop_ao : g.op = .and ∨ g.op = .or := Or.inl h
      have hnotf : (hasNot || isNotOp g.op) = false := by simp [hfn, h, isNotOp]
      rcases hgin : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩
      · refine Or.inr (Or.inl ⟨t.leaves.erase N, by have := Finset.card_erase_of_mem ht; omega, ?_⟩)
        intro x y hx hy hxy
        apply hMono (stp x g) (stp y g) (by simp [stp, hx]) (by simp [stp, hy])
        intro i hi; simp only [ite_true]
        by_cases hiN : i = N
        · subst hiN; rw [getD_stp_eq_of hx, getD_stp_eq_of hy, h, hgin]; intro z; exact z
        · rw [getD_stp_ne_of hx hiN, getD_stp_ne_of hy hiN]
          exact hxy i (Finset.mem_erase.mpr ⟨hiN, hi⟩)
      · refine Or.inr (Or.inl ⟨insert a (t.leaves.erase N), ?_, ?_⟩)
        · have h1 := Finset.card_insert_le a (t.leaves.erase N)
          have h2 := Finset.card_erase_of_mem ht
          have hpos : 0 < t.leaves.card := Finset.card_pos.mpr ⟨N, ht⟩
          omega
        · intro x y hx hy hxy
          apply hMono (stp x g) (stp y g) (by simp [stp, hx]) (by simp [stp, hy])
          intro i hi; simp only [ite_true]
          by_cases hiN : i = N
          · subst hiN; rw [getD_stp_eq_of hx, getD_stp_eq_of hy]
            exact mono_step_andOr g hop_ao x y true (fun u hu => by
              rw [hgin] at hu; simp at hu; subst hu; exact hxy u (Finset.mem_insert_self u _))
          · rw [getD_stp_ne_of hx hiN, getD_stp_ne_of hy hiN]
            exact hxy i (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hiN, hi⟩))
      · by_cases hfresh : a ≠ b ∧ a ∉ t.leaves.erase N ∧ b ∉ t.leaves.erase N
        · let sTree : MTree ℕ := mkBinTree g.op a b
          have hsro : sTree.ReadOnce := mkBinTree_ro g.op a b hfresh.1
          have hsl : sTree.leaves = {a, b} := mkBinTree_leaves g.op a b
          have hdisj : Disjoint (t.leaves.erase N) sTree.leaves := by
            rw [hsl, Finset.disjoint_right]
            intro w hw
            simp only [Finset.mem_insert, Finset.mem_singleton] at hw
            rcases hw with rfl | rfl; exact hfresh.2.1; exact hfresh.2.2
          refine Or.inl ⟨hnotf, t.subst N sTree, MTree.readOnce_subst N sTree t hro hsro hdisj, ?_, ?_⟩
          · rw [MTree.leaves_subst N sTree t hro ht, hsl]
            have h1 := Finset.card_union_le (t.leaves.erase N) {a, b}
            have h2 := Finset.card_erase_of_mem ht
            have h3 : ({a, b} : Finset ℕ).card ≤ 2 := Finset.card_insert_le _ _
            have hpos : 0 < t.leaves.card := Finset.card_pos.mpr ⟨N, ht⟩
            omega
          · intro x hx
            dsimp only
            rw [hte (stp x g) (by simp [stp, hx]), MTree.eval_subst]
            apply t.eval_congr
            intro w _
            by_cases hwN : w = N
            · subst hwN
              rw [Function.update_self, getD_stp_eq_of hx, mkBinTree_eval g hop_ao a b hgin x]
            · rw [Function.update_of_ne hwN, getD_stp_ne_of hx hwN]
        · refine Or.inr (Or.inl ⟨t.leaves.erase N ∪ {a, b}, ?_, ?_⟩)
          · have h2 := Finset.card_erase_of_mem ht
            have hpos : 0 < t.leaves.card := Finset.card_pos.mpr ⟨N, ht⟩
            by_cases hab : a = b
            · subst hab
              have : t.leaves.erase N ∪ {a, a} = insert a (t.leaves.erase N) := by ext v; simp
              rw [this]; have := Finset.card_insert_le a (t.leaves.erase N); omega
            · have hmem : a ∈ t.leaves.erase N ∨ b ∈ t.leaves.erase N := by tauto
              rcases hmem with ha | hb
              · have : t.leaves.erase N ∪ {a, b} = insert b (t.leaves.erase N) := by
                  ext v; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
                  constructor; · rintro (hv | rfl | rfl); exact Or.inr hv; exact Or.inr ha; exact Or.inl rfl
                  · rintro (rfl | hv); exact Or.inr (Or.inr rfl); exact Or.inl hv
                rw [this]; have := Finset.card_insert_le b (t.leaves.erase N); omega
              · have : t.leaves.erase N ∪ {a, b} = insert a (t.leaves.erase N) := by
                  ext v; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
                  constructor; · rintro (hv | rfl | rfl); exact Or.inr hv; exact Or.inl rfl; exact Or.inr hb
                  · rintro (rfl | hv); exact Or.inr (Or.inl rfl); exact Or.inl hv
                rw [this]; have := Finset.card_insert_le a (t.leaves.erase N); omega
          · intro x y hx hy hxy
            apply hMono (stp x g) (stp y g) (by simp [stp, hx]) (by simp [stp, hy])
            intro i hi; simp only [ite_true]
            by_cases hiN : i = N
            · subst hiN; rw [getD_stp_eq_of hx, getD_stp_eq_of hy]
              exact mono_step_andOr g hop_ao x y true (fun u hu => by
                rw [hgin] at hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
                rcases hu with rfl | rfl
                · exact hxy u (Finset.mem_union_right _ (by simp))
                · exact hxy u (Finset.mem_union_right _ (by simp)))
            · rw [getD_stp_ne_of hx hiN, getD_stp_ne_of hy hiN]
              exact hxy i (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hiN, hi⟩))
      · simp [hgin] at hg
    · have hop_ao : g.op = .and ∨ g.op = .or := Or.inr h
      have hnotf : (hasNot || isNotOp g.op) = false := by simp [hfn, h, isNotOp]
      rcases hgin : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩
      · refine Or.inr (Or.inl ⟨t.leaves.erase N, by have := Finset.card_erase_of_mem ht; omega, ?_⟩)
        intro x y hx hy hxy
        apply hMono (stp x g) (stp y g) (by simp [stp, hx]) (by simp [stp, hy])
        intro i hi; simp only [ite_true]
        by_cases hiN : i = N
        · subst hiN; rw [getD_stp_eq_of hx, getD_stp_eq_of hy, h, hgin]; intro z; exact z
        · rw [getD_stp_ne_of hx hiN, getD_stp_ne_of hy hiN]
          exact hxy i (Finset.mem_erase.mpr ⟨hiN, hi⟩)
      · refine Or.inr (Or.inl ⟨insert a (t.leaves.erase N), ?_, ?_⟩)
        · have h1 := Finset.card_insert_le a (t.leaves.erase N)
          have h2 := Finset.card_erase_of_mem ht
          have hpos : 0 < t.leaves.card := Finset.card_pos.mpr ⟨N, ht⟩
          omega
        · intro x y hx hy hxy
          apply hMono (stp x g) (stp y g) (by simp [stp, hx]) (by simp [stp, hy])
          intro i hi; simp only [ite_true]
          by_cases hiN : i = N
          · subst hiN; rw [getD_stp_eq_of hx, getD_stp_eq_of hy]
            exact mono_step_andOr g hop_ao x y true (fun u hu => by
              rw [hgin] at hu; simp at hu; subst hu; exact hxy u (Finset.mem_insert_self u _))
          · rw [getD_stp_ne_of hx hiN, getD_stp_ne_of hy hiN]
            exact hxy i (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hiN, hi⟩))
      · by_cases hfresh : a ≠ b ∧ a ∉ t.leaves.erase N ∧ b ∉ t.leaves.erase N
        · let sTree : MTree ℕ := mkBinTree g.op a b
          have hsro : sTree.ReadOnce := mkBinTree_ro g.op a b hfresh.1
          have hsl : sTree.leaves = {a, b} := mkBinTree_leaves g.op a b
          have hdisj : Disjoint (t.leaves.erase N) sTree.leaves := by
            rw [hsl, Finset.disjoint_right]
            intro w hw
            simp only [Finset.mem_insert, Finset.mem_singleton] at hw
            rcases hw with rfl | rfl; exact hfresh.2.1; exact hfresh.2.2
          refine Or.inl ⟨hnotf, t.subst N sTree, MTree.readOnce_subst N sTree t hro hsro hdisj, ?_, ?_⟩
          · rw [MTree.leaves_subst N sTree t hro ht, hsl]
            have h1 := Finset.card_union_le (t.leaves.erase N) {a, b}
            have h2 := Finset.card_erase_of_mem ht
            have h3 : ({a, b} : Finset ℕ).card ≤ 2 := Finset.card_insert_le _ _
            have hpos : 0 < t.leaves.card := Finset.card_pos.mpr ⟨N, ht⟩
            omega
          · intro x hx
            dsimp only
            rw [hte (stp x g) (by simp [stp, hx]), MTree.eval_subst]
            apply t.eval_congr
            intro w _
            by_cases hwN : w = N
            · subst hwN
              rw [Function.update_self, getD_stp_eq_of hx, mkBinTree_eval g hop_ao a b hgin x]
            · rw [Function.update_of_ne hwN, getD_stp_ne_of hx hwN]
        · refine Or.inr (Or.inl ⟨t.leaves.erase N ∪ {a, b}, ?_, ?_⟩)
          · have h2 := Finset.card_erase_of_mem ht
            have hpos : 0 < t.leaves.card := Finset.card_pos.mpr ⟨N, ht⟩
            by_cases hab : a = b
            · subst hab
              have : t.leaves.erase N ∪ {a, a} = insert a (t.leaves.erase N) := by ext v; simp
              rw [this]; have := Finset.card_insert_le a (t.leaves.erase N); omega
            · have hmem : a ∈ t.leaves.erase N ∨ b ∈ t.leaves.erase N := by tauto
              rcases hmem with ha | hb
              · have : t.leaves.erase N ∪ {a, b} = insert b (t.leaves.erase N) := by
                  ext v; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
                  constructor; · rintro (hv | rfl | rfl); exact Or.inr hv; exact Or.inr ha; exact Or.inl rfl
                  · rintro (rfl | hv); exact Or.inr (Or.inr rfl); exact Or.inl hv
                rw [this]; have := Finset.card_insert_le b (t.leaves.erase N); omega
              · have : t.leaves.erase N ∪ {a, b} = insert a (t.leaves.erase N) := by
                  ext v; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
                  constructor; · rintro (hv | rfl | rfl); exact Or.inr hv; exact Or.inl rfl; exact Or.inr hb
                  · rintro (rfl | hv); exact Or.inr (Or.inl rfl); exact Or.inl hv
                rw [this]; have := Finset.card_insert_le a (t.leaves.erase N); omega
          · intro x y hx hy hxy
            apply hMono (stp x g) (stp y g) (by simp [stp, hx]) (by simp [stp, hy])
            intro i hi; simp only [ite_true]
            by_cases hiN : i = N
            · subst hiN; rw [getD_stp_eq_of hx, getD_stp_eq_of hy]
              exact mono_step_andOr g hop_ao x y true (fun u hu => by
                rw [hgin] at hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
                rcases hu with rfl | rfl
                · exact hxy u (Finset.mem_union_right _ (by simp))
                · exact hxy u (Finset.mem_union_right _ (by simp)))
            · rw [getD_stp_ne_of hx hiN, getD_stp_ne_of hy hiN]
              exact hxy i (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hiN, hi⟩))
      · simp [hgin] at hg
    · cases hgin : g.inputs with
      | nil =>
        refine Or.inr (Or.inr (Or.inr (Or.inl ⟨t.leaves.erase N, fun _ => true, ?_, ?_⟩)))
        · have h2 := Finset.card_erase_of_mem ht
          have hpos : 0 < t.leaves.card := Finset.card_pos.mpr ⟨N, ht⟩
          omega
        · intro x y hx hy hxy
          apply hMono (stp x g) (stp y g) (by simp [stp, hx]) (by simp [stp, hy])
          intro i hi; simp only [ite_true]
          by_cases hiN : i = N
          · subst hiN; rw [getD_stp_eq_of hx, getD_stp_eq_of hy, h, hgin]; intro z; exact z
          · rw [getD_stp_ne_of hx hiN, getD_stp_ne_of hy hiN]
            exact hxy i (Finset.mem_erase.mpr ⟨hiN, hi⟩)
      | cons a tl =>
        by_cases ha : a ∈ t.leaves.erase N
        · let t1 : MTree Slot := (t.map Slot.wire).subst (Slot.wire N) (.leaf .neg)
          let tPos' : MTree Slot := t1.subst (Slot.wire a) (.leaf .sh)
          have hro0 : (t.map Slot.wire).ReadOnce :=
            MTree.readOnce_map (fun _ _ e => by cases e; rfl) hro
          have hN_in : Slot.wire N ∈ (t.map Slot.wire).leaves := by
            rw [MTree.leaves_map]; exact Finset.mem_image_of_mem _ ht
          have hdisj1 : Disjoint ((t.map Slot.wire).leaves.erase (Slot.wire N)) (MTree.leaf Slot.neg).leaves := by
            rw [Finset.disjoint_right]; intro s hs
            simp only [MTree.leaves, Finset.mem_singleton] at hs; subst hs
            simp [MTree.leaves_map]
          have hro1 : t1.ReadOnce := MTree.readOnce_subst _ _ _ hro0 trivial hdisj1
          have ht1_leaves : t1.leaves = (t.map Slot.wire).leaves.erase (Slot.wire N) ∪ {Slot.neg} :=
            MTree.leaves_subst _ _ _ hro0 hN_in
          have ha_in1 : Slot.wire a ∈ t1.leaves := by
            rw [ht1_leaves, Finset.mem_union]; left
            have ha' := Finset.mem_erase.mp ha
            refine Finset.mem_erase.mpr ⟨fun e => ha'.1 (by cases e; rfl), ?_⟩
            rw [MTree.leaves_map]; exact Finset.mem_image_of_mem _ ha'.2
          have hdisj2 : Disjoint (t1.leaves.erase (Slot.wire a)) (MTree.leaf Slot.sh).leaves := by
            rw [Finset.disjoint_right]; intro s hs
            simp only [MTree.leaves, Finset.mem_singleton] at hs; subst hs
            rw [Finset.mem_erase, ht1_leaves]; simp [MTree.leaves_map]
          have hro2 : tPos'.ReadOnce := MTree.readOnce_subst _ _ _ hro1 trivial hdisj2
          have htPos'_leaves : tPos'.leaves = t1.leaves.erase (Slot.wire a) ∪ {Slot.sh} :=
            MTree.leaves_subst _ _ _ hro1 ha_in1
          have hsw : slotWires tPos'.leaves = (t.leaves.erase N).erase a := by
            ext w
            rw [mem_slotWires, htPos'_leaves, Finset.mem_union, Finset.mem_erase, ht1_leaves,
                Finset.mem_union, Finset.mem_erase, MTree.leaves_map]
            simp
          have hopt_none : optWires ({none} : Finset (Option ℕ)) = ∅ := by
            ext w; simp [mem_optWires]
          let D : Decomp N (fun x => f (stp x g)) := {
            tPos := tPos'
            tNeg := MTree.leaf none
            sSh := MTree.leaf a
            roPos := hro2
            roNeg := trivial
            roSh := trivial
            sh_in_pos := by rw [htPos'_leaves]; simp
            neg_in_pos := by
              rw [htPos'_leaves, Finset.mem_union]; left
              refine Finset.mem_erase.mpr ⟨(by intro e; cases e), ?_⟩
              rw [ht1_leaves]; simp
            sh_in_neg := by simp [MTree.leaves]
            disj_PH := by simp [MTree.leaves, hopt_none]
            disj_PU := by rw [hsw]; simp [MTree.leaves]
            disj_HU := by simp [MTree.leaves, hopt_none]
            eval_eq := fun x hx => by
              dsimp only [tPos', t1]
              rw [hte (stp x g) (by simp [stp, hx]), MTree.eval_subst, MTree.eval_subst, MTree.eval_map]
              apply t.eval_congr
              intro w _
              simp only [Function.comp_apply, MTree.eval]
              by_cases hwN : w = N
              · subst hwN
                rw [Function.update_self, getD_stp_eq_of hx, h, hgin]
                simp [GateOp.eval]
              · rw [Function.update_of_ne (fun e => hwN (by cases e; rfl))]
                by_cases hwa : w = a
                · subst hwa
                  rw [Function.update_self, getD_stp_ne_of hx hwN]
                · rw [Function.update_of_ne (fun e => hwa (by cases e; rfl)), getD_stp_ne_of hx hwN]
          }
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨D, ?_⟩))))
          have hwires : D.wires = t.leaves.erase N := by
            simp only [Decomp.wires, D, hsw, MTree.leaves, hopt_none, Finset.union_empty]
            ext w
            simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton]
            constructor
            · rintro (⟨_, hw⟩ | rfl)
              · exact hw
              · exact Finset.mem_erase.mp ha
            · intro hw
              by_cases hwa : w = a
              · exact Or.inr hwa
              · exact Or.inl ⟨hwa, hw⟩
          rw [hwires]
          have h2 := Finset.card_erase_of_mem ht
          have hpos : 0 < t.leaves.card := Finset.card_pos.mpr ⟨N, ht⟩
          omega
        · let tPos' : MTree (Option ℕ) := (t.map some).subst (some N) (.leaf none)
          have hro0 : (t.map some).ReadOnce :=
            MTree.readOnce_map (fun _ _ e => by cases e; rfl) hro
          have hN_in : some N ∈ (t.map some).leaves := by
            rw [MTree.leaves_map]; exact Finset.mem_image_of_mem _ ht
          have hdisj1 : Disjoint ((t.map some).leaves.erase (some N)) (MTree.leaf (none : Option ℕ)).leaves := by
            rw [Finset.disjoint_right]; intro s hs
            simp only [MTree.leaves, Finset.mem_singleton] at hs; subst hs
            simp [MTree.leaves_map]
          have hro1 : tPos'.ReadOnce := MTree.readOnce_subst _ _ _ hro0 trivial hdisj1
          have htPos'_leaves : tPos'.leaves = (t.map some).leaves.erase (some N) ∪ {none} :=
            MTree.leaves_subst _ _ _ hro0 hN_in
          have how : optWires tPos'.leaves = t.leaves.erase N := by
            ext w; rw [mem_optWires, htPos'_leaves, Finset.mem_union, Finset.mem_erase, MTree.leaves_map]
            simp
          let T : NegTree N (fun x => f (stp x g)) := {
            tPos := tPos'
            tNeg := MTree.leaf a
            roPos := hro1
            roNeg := trivial
            neg_in_pos := by rw [htPos'_leaves]; simp
            disj_PH := by rw [how]; simp [MTree.leaves, ha]
            eval_eq := fun x hx => by
              dsimp only [tPos']
              rw [hte (stp x g) (by simp [stp, hx]), MTree.eval_subst, MTree.eval_map]
              apply t.eval_congr
              intro w _
              simp only [Function.comp_apply, MTree.eval]
              by_cases hwN : w = N
              · subst hwN
                rw [Function.update_self, getD_stp_eq_of hx, h, hgin]
                simp [GateOp.eval]
              · rw [Function.update_of_ne (fun e => hwN (by cases e; rfl)), getD_stp_ne_of hx hwN]
          }
          refine Or.inr (Or.inr (Or.inl ⟨T, ?_⟩))
          have hwires : T.wires = insert a (t.leaves.erase N) := by
            simp only [NegTree.wires, T, how, MTree.leaves]; ext w; simp
          rw [hwires]
          have h1 := Finset.card_insert_le a (t.leaves.erase N)
          have h2 := Finset.card_erase_of_mem ht
          have hpos : 0 < t.leaves.card := Finset.card_pos.mpr ⟨N, ht⟩
          omega
  · refine Or.inr (Or.inl ⟨t.leaves, htc, ?_⟩)
    intro x y hx hy hxy
    apply hMono (stp x g) (stp y g) (by simp [stp, hx]) (by simp [stp, hy])
    intro i hi
    have hiN : i ≠ N := fun e => ht (e ▸ hi)
    rw [getD_stp_ne_of hx hiN, getD_stp_ne_of hy hiN]
    exact hxy i hi

lemma tightInv_step_monoSlack (N s : ℕ) (hasNot : Bool) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (f : List Bool → Bool) (R : Finset ℕ) (hRc : R.card ≤ s)
    (hMono : UnateOn (N + 1) f R (fun _ => true)) :
    TightInv N (s + 1) (hasNot || isNotOp g.op) (fun x => f (stp x g)) := by
  have hop : g.op = .and ∨ g.op = .or ∨ g.op = .not := by
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hg.1
  by_cases ht : N ∈ R
  · rcases hop with h | h | h
    · refine Or.inr (Or.inl ⟨R.erase N ∪ g.inputs.toFinset, ?_, ?_⟩)
      · have h1 := Finset.card_union_le (R.erase N) g.inputs.toFinset
        have h2 := Finset.card_erase_of_mem ht
        have h3 := List.toFinset_card_le g.inputs
        have hpos : 0 < R.card := Finset.card_pos.mpr ⟨N, ht⟩
        omega
      · intro x y hx hy hxy
        apply hMono (stp x g) (stp y g) (by simp [stp, hx]) (by simp [stp, hy])
        intro i hi; simp only [ite_true]
        by_cases hiN : i = N
        · subst hiN; rw [getD_stp_eq_of hx, getD_stp_eq_of hy]
          exact mono_step_andOr g (Or.inl h) x y true (fun u hu =>
            hxy u (Finset.mem_union_right _ (List.mem_toFinset.mpr hu)))
        · rw [getD_stp_ne_of hx hiN, getD_stp_ne_of hy hiN]
          exact hxy i (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hiN, hi⟩))
    · refine Or.inr (Or.inl ⟨R.erase N ∪ g.inputs.toFinset, ?_, ?_⟩)
      · have h1 := Finset.card_union_le (R.erase N) g.inputs.toFinset
        have h2 := Finset.card_erase_of_mem ht
        have h3 := List.toFinset_card_le g.inputs
        have hpos : 0 < R.card := Finset.card_pos.mpr ⟨N, ht⟩
        omega
      · intro x y hx hy hxy
        apply hMono (stp x g) (stp y g) (by simp [stp, hx]) (by simp [stp, hy])
        intro i hi; simp only [ite_true]
        by_cases hiN : i = N
        · subst hiN; rw [getD_stp_eq_of hx, getD_stp_eq_of hy]
          exact mono_step_andOr g (Or.inr h) x y true (fun u hu =>
            hxy u (Finset.mem_union_right _ (List.mem_toFinset.mpr hu)))
        · rw [getD_stp_ne_of hx hiN, getD_stp_ne_of hy hiN]
          exact hxy i (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hiN, hi⟩))
    · cases hgin : g.inputs with
      | nil =>
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨R.erase N, ?_, ?_⟩))))
        · have h2 := Finset.card_erase_of_mem ht
          have hpos : 0 < R.card := Finset.card_pos.mpr ⟨N, ht⟩
          omega
        · simpa [ht, effInputs, h, hgin] using dep_step_aux (unate_to_dep hMono) g
      | cons a tl =>
        by_cases ha : a ∈ R.erase N
        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨R.erase N, ?_, ?_⟩))))
          · have h2 := Finset.card_erase_of_mem ht
            have hpos : 0 < R.card := Finset.card_pos.mpr ⟨N, ht⟩
            omega
          · have heq : R.erase N ∪ (effInputs g).toFinset = R.erase N := by
              ext w
              simp only [Finset.mem_union, List.mem_toFinset, effInputs, h, hgin, List.mem_singleton,
                or_iff_left_iff_imp]
              rintro rfl; exact ha
            simpa [ht, heq] using dep_step_aux (unate_to_dep hMono) g
        · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨insert a (R.erase N), Function.update (fun _ => true) a false, ?_, ?_⟩)))
          · have h1 := Finset.card_insert_le a (R.erase N)
            have h2 := Finset.card_erase_of_mem ht
            have hpos : 0 < R.card := Finset.card_pos.mpr ⟨N, ht⟩
            omega
          · intro x y hx hy hxy
            apply hMono (stp x g) (stp y g) (by simp [stp, hx]) (by simp [stp, hy])
            intro i hi; simp only [ite_true]
            by_cases hiN : i = N
            · subst hiN; rw [getD_stp_eq_of hx, getD_stp_eq_of hy, h, hgin]
              simp only [GateOp.eval, List.map_cons, List.headD_cons]
              have ha_dir := hxy a (Finset.mem_insert_self a _)
              simp only [Function.update_self, Bool.false_eq_true, ite_false] at ha_dir
              cases hxa : x.getD a false <;> cases hya : y.getD a false <;> simp_all
            · have hi' : i ∈ R.erase N := Finset.mem_erase.mpr ⟨hiN, hi⟩
              have hia : i ≠ a := fun e => ha (e ▸ hi')
              have hidir := hxy i (Finset.mem_insert_of_mem hi')
              simp only [Function.update_of_ne hia, ite_true] at hidir
              rw [getD_stp_ne_of hx hiN, getD_stp_ne_of hy hiN]
              exact hidir
  · refine Or.inr (Or.inl ⟨R, by omega, ?_⟩)
    intro x y hx hy hxy
    apply hMono (stp x g) (stp y g) (by simp [stp, hx]) (by simp [stp, hy])
    intro i hi; have hiN : i ≠ N := fun e => ht (e ▸ hi)
    rw [getD_stp_ne_of hx hiN, getD_stp_ne_of hy hiN]; exact hxy i hi

lemma tightInv_step_negTree_ao (N s : ℕ) (hasNot : Bool) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hop_ao : g.op = .and ∨ g.op = .or)
    (f : List Bool → Bool) (T : NegTree (N + 1) f) (hTc : T.wires.card ≤ s)
    (ht : N ∈ T.wires) :
    TightInv N (s + 1) (hasNot || isNotOp g.op) (fun x => f (stp x g)) := by
  let P := optWires T.tPos.leaves
  let H := T.tNeg.leaves
  have hUn : UnateOn (N + 1) f T.wires (fun w => decide (w ∈ P)) := T.unateOn
  have heff_eq : effInputs g = g.inputs := by rcases hop_ao with h | h <;> simp [effInputs, h]
  rcases hgin : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨T.wires.erase N, ?_, ?_⟩))))
    · have h2 := Finset.card_erase_of_mem ht
      have hpos : 0 < T.wires.card := Finset.card_pos.mpr ⟨N, ht⟩
      omega
    · simpa [ht, heff_eq, hgin] using dep_step_aux (unate_to_dep hUn) g
  · by_cases ha : a ∈ T.wires.erase N
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨T.wires.erase N, ?_, ?_⟩))))
      · have h2 := Finset.card_erase_of_mem ht
        have hpos : 0 < T.wires.card := Finset.card_pos.mpr ⟨N, ht⟩
        omega
      · have heq : T.wires.erase N ∪ (effInputs g).toFinset = T.wires.erase N := by
          ext w
          simp only [Finset.mem_union, List.mem_toFinset, heff_eq, hgin, List.mem_singleton,
            or_iff_left_iff_imp]
          rintro rfl; exact ha
        simpa [ht, heq] using dep_step_aux (unate_to_dep hUn) g
    · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨insert a (T.wires.erase N),
          Function.update (fun w => decide (w ∈ P)) a (decide (N ∈ P)), ?_, ?_⟩)))
      · have h1 := Finset.card_insert_le a (T.wires.erase N)
        have h2 := Finset.card_erase_of_mem ht
        have hpos : 0 < T.wires.card := Finset.card_pos.mpr ⟨N, ht⟩
        omega
      · intro x y hx hy hxy
        apply hUn (stp x g) (stp y g) (by simp [stp, hx]) (by simp [stp, hy])
        intro i hi
        by_cases hiN : i = N
        · subst hiN
          have hm := mono_step_andOr g hop_ao x y (decide (i ∈ P)) (fun u hu => by
            rw [hgin] at hu; simp at hu; subst hu
            simpa using hxy u (Finset.mem_insert_self u _))
          rw [getD_stp_eq_of hx, getD_stp_eq_of hy]
          exact hm
        · have hi' : i ∈ T.wires.erase N := Finset.mem_erase.mpr ⟨hiN, hi⟩
          have hia : i ≠ a := fun e => ha (e ▸ hi')
          have hidir := hxy i (Finset.mem_insert_of_mem hi')
          simp only [Function.update_of_ne hia] at hidir
          rw [getD_stp_ne_of hx hiN, getD_stp_ne_of hy hiN]
          exact hidir
  · by_cases hfresh : a ≠ b ∧ a ∉ T.wires.erase N ∧ b ∉ T.wires.erase N
    · rcases Finset.mem_union.mp ht with hNP | hNH
      · let sTree : MTree (Option ℕ) := mkBinTree g.op (some a) (some b)
        have hsro : sTree.ReadOnce := mkBinTree_ro g.op (some a) (some b) (fun e => hfresh.1 (by cases e; rfl))
        have hsl : sTree.leaves = {some a, some b} := mkBinTree_leaves g.op _ _
        have hN_in : some N ∈ T.tPos.leaves := mem_optWires.mp hNP
        have hdisj : Disjoint (T.tPos.leaves.erase (some N)) sTree.leaves := by
          rw [hsl, Finset.disjoint_right]; intro o ho
          simp only [Finset.mem_insert, Finset.mem_singleton] at ho
          rcases ho with rfl | rfl
          · intro hmem; have := Finset.mem_erase.mp hmem
            exact hfresh.2.1 (Finset.mem_erase.mpr ⟨fun e => this.1 (by rw [e]),
              Finset.mem_union_left _ (mem_optWires.mpr this.2)⟩)
          · intro hmem; have := Finset.mem_erase.mp hmem
            exact hfresh.2.2 (Finset.mem_erase.mpr ⟨fun e => this.1 (by rw [e]),
              Finset.mem_union_left _ (mem_optWires.mpr this.2)⟩)
        let tPos' := T.tPos.subst (some N) sTree
        have htPos'_leaves : tPos'.leaves = T.tPos.leaves.erase (some N) ∪ {some a, some b} := by
          rw [MTree.leaves_subst _ _ _ T.roPos hN_in, hsl]
        have how : optWires tPos'.leaves = P.erase N ∪ {a, b} := by
          ext w
          rw [mem_optWires, htPos'_leaves]
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton,
            P, mem_optWires, Option.some.injEq, ne_eq]
        have hdisj_PH' : Disjoint (optWires tPos'.leaves) H := by
          rw [how, Finset.disjoint_union_left]
          refine ⟨Finset.disjoint_of_subset_left (Finset.erase_subset N P) T.disj_PH, ?_⟩
          rw [Finset.disjoint_left]; intro w hw hwH
          have hwN : w ≠ N := fun e => Finset.disjoint_left.mp T.disj_PH hNP (by rw [e] at hwH; exact hwH)
          simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl
          · exact hfresh.2.1 (Finset.mem_erase.mpr ⟨hwN, Finset.mem_union_right _ hwH⟩)
          · exact hfresh.2.2 (Finset.mem_erase.mpr ⟨hwN, Finset.mem_union_right _ hwH⟩)
        let T' : NegTree N (fun x => f (stp x g)) := {
          tPos := tPos'
          tNeg := T.tNeg
          roPos := MTree.readOnce_subst _ _ _ T.roPos hsro hdisj
          roNeg := T.roNeg
          neg_in_pos := by
            rw [htPos'_leaves, Finset.mem_union]; left
            exact Finset.mem_erase.mpr ⟨(by intro e; cases e), T.neg_in_pos⟩
          disj_PH := hdisj_PH'
          eval_eq := fun x hx => by
            dsimp only [tPos']
            rw [T.eval_eq (stp x g) (by simp [stp, hx]), MTree.eval_subst]
            have hneg_eq : T.tNeg.eval (fun w => (stp x g).getD w false) = T.tNeg.eval (fun w => x.getD w false) :=
              T.tNeg.eval_congr (fun w hw => getD_stp_ne_of hx (fun e => Finset.disjoint_left.mp T.disj_PH hNP (by rw [e] at hw; exact hw)))
            apply T.tPos.eval_congr
            intro o _
            cases o with
            | none =>
              dsimp only
              rw [Function.update_of_ne (by intro e; cases e)]
              dsimp only
              rw [hneg_eq]
            | some w =>
              dsimp only
              by_cases hwN : w = N
              · rw [hwN, Function.update_self, getD_stp_eq_of hx, mkBinTree_eval g hop_ao a b hgin x]
                dsimp only [sTree]
                rw [mkBinTree_eval_map]
                rfl
              · rw [Function.update_of_ne (fun e => hwN (by cases e; rfl)), getD_stp_ne_of hx hwN]
        }
        refine Or.inr (Or.inr (Or.inl ⟨T', ?_⟩))
        have hw : T'.wires = T.wires.erase N ∪ {a, b} := by
          simp only [NegTree.wires, T', how]
          ext w
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, P]
          have hNnotH : N ∉ H := Finset.disjoint_left.mp T.disj_PH hNP
          constructor
          · rintro ((⟨h1, h2⟩ | h3) | h4)
            · exact Or.inl ⟨h1, Or.inl h2⟩
            · exact Or.inr h3
            · exact Or.inl ⟨fun e => hNnotH (by rw [e] at h4; exact h4), Or.inr h4⟩
          · rintro (⟨h1, h2 | h3⟩ | h4)
            · exact Or.inl (Or.inl ⟨h1, h2⟩)
            · exact Or.inr h3
            · exact Or.inl (Or.inr h4)
        rw [hw]
        have h1 := Finset.card_union_le (T.wires.erase N) {a, b}
        have h2 := Finset.card_erase_of_mem ht
        have h3 : ({a, b} : Finset ℕ).card ≤ 2 := Finset.card_insert_le _ _
        have hpos : 0 < T.wires.card := Finset.card_pos.mpr ⟨N, ht⟩
        omega
      · let sTree : MTree ℕ := mkBinTree g.op a b
        have hsro : sTree.ReadOnce := mkBinTree_ro g.op a b hfresh.1
        have hsl : sTree.leaves = {a, b} := mkBinTree_leaves g.op a b
        have hdisj : Disjoint (H.erase N) sTree.leaves := by
          rw [hsl, Finset.disjoint_right]; intro w hw
          simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl
          · intro hm; have := Finset.mem_erase.mp hm
            exact hfresh.2.1 (Finset.mem_erase.mpr ⟨this.1, Finset.mem_union_right _ this.2⟩)
          · intro hm; have := Finset.mem_erase.mp hm
            exact hfresh.2.2 (Finset.mem_erase.mpr ⟨this.1, Finset.mem_union_right _ this.2⟩)
        let tNeg' := T.tNeg.subst N sTree
        have htNeg'_leaves : tNeg'.leaves = H.erase N ∪ {a, b} := by
          rw [MTree.leaves_subst N sTree T.tNeg T.roNeg hNH, hsl]
        have hdisj_PH' : Disjoint P tNeg'.leaves := by
          rw [htNeg'_leaves, Finset.disjoint_union_right]
          refine ⟨Finset.disjoint_of_subset_right (Finset.erase_subset N H) T.disj_PH, ?_⟩
          rw [Finset.disjoint_right]; intro w hw hwP
          have hwN : w ≠ N := fun e => Finset.disjoint_right.mp T.disj_PH hNH (by rw [e] at hwP; exact hwP)
          simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl
          · exact hfresh.2.1 (Finset.mem_erase.mpr ⟨hwN, Finset.mem_union_left _ hwP⟩)
          · exact hfresh.2.2 (Finset.mem_erase.mpr ⟨hwN, Finset.mem_union_left _ hwP⟩)
        let T' : NegTree N (fun x => f (stp x g)) := {
          tPos := T.tPos
          tNeg := tNeg'
          roPos := T.roPos
          roNeg := MTree.readOnce_subst N sTree T.tNeg T.roNeg hsro hdisj
          neg_in_pos := T.neg_in_pos
          disj_PH := hdisj_PH'
          eval_eq := fun x hx => by
            dsimp only [tNeg']
            rw [T.eval_eq (stp x g) (by simp [stp, hx])]
            have hneg_eq : T.tNeg.eval (fun w => (stp x g).getD w false) =
                (T.tNeg.subst N sTree).eval (fun w => x.getD w false) := by
              rw [MTree.eval_subst]
              apply T.tNeg.eval_congr
              intro w _
              by_cases hwN : w = N
              · rw [hwN, Function.update_self, getD_stp_eq_of hx, mkBinTree_eval g hop_ao a b hgin x]
              · rw [Function.update_of_ne hwN, getD_stp_ne_of hx hwN]
            apply T.tPos.eval_congr
            intro o ho
            cases o with
            | none => dsimp only; rw [hneg_eq]
            | some w =>
              dsimp only
              exact getD_stp_ne_of hx (fun e => Finset.disjoint_right.mp T.disj_PH hNH (by have h := mem_optWires.mpr ho; rw [e] at h; exact h))
        }
        refine Or.inr (Or.inr (Or.inl ⟨T', ?_⟩))
        have hw : T'.wires = T.wires.erase N ∪ {a, b} := by
          simp only [NegTree.wires, T', htNeg'_leaves]
          ext w
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, H]
          have hNnotP : N ∉ P := Finset.disjoint_right.mp T.disj_PH hNH
          constructor
          · rintro (h1 | (⟨h2, h3⟩ | h4))
            · exact Or.inl ⟨fun e => hNnotP (by rw [e] at h1; exact h1), Or.inl h1⟩
            · exact Or.inl ⟨h2, Or.inr h3⟩
            · exact Or.inr h4
          · rintro (⟨h1, h2 | h3⟩ | h4)
            · exact Or.inl h2
            · exact Or.inr (Or.inl ⟨h1, h3⟩)
            · exact Or.inr (Or.inr h4)
        rw [hw]
        have h1 := Finset.card_union_le (T.wires.erase N) {a, b}
        have h2 := Finset.card_erase_of_mem ht
        have h3 : ({a, b} : Finset ℕ).card ≤ 2 := Finset.card_insert_le _ _
        have hpos : 0 < T.wires.card := Finset.card_pos.mpr ⟨N, ht⟩
        omega
    · by_cases hcard_le : (T.wires.erase N ∪ {a, b}).card + 1 ≤ T.wires.card
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨T.wires.erase N ∪ {a, b}, by omega, ?_⟩))))
        have heff : (effInputs g).toFinset = {a, b} := by ext w; simp [heff_eq, hgin]
        simpa [ht, heff] using dep_step_aux (unate_to_dep hUn) g
      · by_cases hab : a = b
        · subst hab
          have hna : a ∉ T.wires.erase N := by
            intro ha
            have : T.wires.erase N ∪ {a, a} = T.wires.erase N := by
              ext w; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, or_iff_left_iff_imp]
              rintro (rfl | rfl); exact ha; exact ha
            rw [this] at hcard_le
            have := Finset.card_erase_of_mem ht
            have hpos : 0 < T.wires.card := Finset.card_pos.mpr ⟨N, ht⟩
            omega
          refine Or.inr (Or.inr (Or.inr (Or.inl ⟨insert a (T.wires.erase N),
            Function.update (fun w => decide (w ∈ P)) a (decide (N ∈ P)), ?_, ?_⟩)))
          · have h1 := Finset.card_insert_le a (T.wires.erase N)
            have h2 := Finset.card_erase_of_mem ht
            have hpos : 0 < T.wires.card := Finset.card_pos.mpr ⟨N, ht⟩
            omega
          · intro x y hx hy hxy
            apply hUn (stp x g) (stp y g) (by simp [stp, hx]) (by simp [stp, hy])
            intro i hi
            by_cases hiN : i = N
            · subst hiN
              have hm := mono_step_andOr g hop_ao x y (decide (i ∈ P)) (fun u hu => by
                rw [hgin] at hu; simp at hu; subst hu
                simpa using hxy u (Finset.mem_insert_self u _))
              rw [getD_stp_eq_of hx, getD_stp_eq_of hy]
              exact hm
            · have hi' : i ∈ T.wires.erase N := Finset.mem_erase.mpr ⟨hiN, hi⟩
              have hia : i ≠ a := fun e => hna (e ▸ hi')
              have hidir := hxy i (Finset.mem_insert_of_mem hi')
              simp only [Function.update_of_ne hia] at hidir
              rw [getD_stp_ne_of hx hiN, getD_stp_ne_of hy hiN]
              exact hidir
        · have hsplit : ∃ sh fr : ℕ, ({a, b} : Finset ℕ) = {sh, fr} ∧
              sh ∈ T.wires.erase N ∧ fr ∉ T.wires.erase N ∧
              (∀ x : List Bool, g.op.eval (g.inputs.map fun i => x.getD i false) =
                (mkBinTree g.op sh fr).eval (fun i => x.getD i false)) := by
            by_cases ha : a ∈ T.wires.erase N
            · have hnb : b ∉ T.wires.erase N := by
                intro hb
                have : T.wires.erase N ∪ {a, b} = T.wires.erase N := by
                  ext w
                  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, or_iff_left_iff_imp]
                  rintro (rfl | rfl); exact ha; exact hb
                rw [this] at hcard_le
                have := Finset.card_erase_of_mem ht
                have hpos : 0 < T.wires.card := Finset.card_pos.mpr ⟨N, ht⟩
                omega
              exact ⟨a, b, rfl, ha, hnb, fun x => mkBinTree_eval g hop_ao a b hgin x⟩
            · have hb : b ∈ T.wires.erase N := by tauto
              exact ⟨b, a, Finset.pair_comm a b, hb, ha, fun x => by
                rw [mkBinTree_eval g hop_ao a b hgin x, mkBinTree_eval_comm]⟩
          obtain ⟨sh, fr, hpair, hsh_in, hfr_not, hgeval⟩ := hsplit
          have hsh_ne_fr : sh ≠ fr := fun e => hfr_not (e ▸ hsh_in)
          by_cases hsame : (N ∈ P ↔ sh ∈ P)
          · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨insert fr (T.wires.erase N),
              Function.update (fun w => decide (w ∈ P)) fr (decide (N ∈ P)), ?_, ?_⟩)))
            · have h1 := Finset.card_insert_le fr (T.wires.erase N)
              have h2 := Finset.card_erase_of_mem ht
              have hpos : 0 < T.wires.card := Finset.card_pos.mpr ⟨N, ht⟩
              omega
            · intro x y hx hy hxy
              apply hUn (stp x g) (stp y g) (by simp [stp, hx]) (by simp [stp, hy])
              intro i hi
              by_cases hiN : i = N
              · subst hiN
                have hdir_sh : if decide (i ∈ P) then (x.getD sh false = true → y.getD sh false = true)
                    else (y.getD sh false = true → x.getD sh false = true) := by
                  have h1 := hxy sh (Finset.mem_insert_of_mem hsh_in)
                  simp only [Function.update_of_ne hsh_ne_fr] at h1
                  simpa [hsame] using h1
                have hdir_fr : if decide (i ∈ P) then (x.getD fr false = true → y.getD fr false = true)
                    else (y.getD fr false = true → x.getD fr false = true) := by
                  simpa using hxy fr (Finset.mem_insert_self fr _)
                rw [getD_stp_eq_of hx, getD_stp_eq_of hy, hgeval x, hgeval y]
                cases hc : decide (i ∈ P) <;> simp only [hc, ite_true, ite_false, Bool.false_eq_true] at hdir_sh hdir_fr ⊢
                · exact (mkBinTree g.op sh fr).eval_mono (fun w hw => by
                    rw [mkBinTree_leaves] at hw
                    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
                    rcases hw with rfl | rfl; exact hdir_sh; exact hdir_fr)
                · exact (mkBinTree g.op sh fr).eval_mono (fun w hw => by
                    rw [mkBinTree_leaves] at hw
                    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
                    rcases hw with rfl | rfl; exact hdir_sh; exact hdir_fr)
              · have hi' : i ∈ T.wires.erase N := Finset.mem_erase.mpr ⟨hiN, hi⟩
                have hifr : i ≠ fr := fun e => hfr_not (e ▸ hi')
                have hidir := hxy i (Finset.mem_insert_of_mem hi')
                simp only [Function.update_of_ne hifr] at hidir
                rw [getD_stp_ne_of hx hiN, getD_stp_ne_of hy hiN]
                exact hidir
          · have hsh_mem : sh ∈ T.wires := (Finset.mem_erase.mp hsh_in).2
            rcases Finset.mem_union.mp ht with hNP | hNH
            · have hsh_H : sh ∈ H := by
                rcases Finset.mem_union.mp hsh_mem with h1 | h2
                · exfalso; exact hsame (iff_of_true hNP h1)
                · exact h2
              let liftPos : Option ℕ → Slot := fun o => match o with | none => .neg | some w => .wire w
              have hlift_inj : Function.Injective liftPos := by
                intro o1 o2 he; cases o1 <;> cases o2 <;> simp [liftPos] at he ⊢; exact he
              let t0 := T.tPos.map liftPos
              let sTree : MTree Slot := mkBinTree g.op .sh (.wire fr)
              have hsro : sTree.ReadOnce := mkBinTree_ro g.op _ _ (by intro e; cases e)
              have hsl : sTree.leaves = {.sh, .wire fr} := mkBinTree_leaves g.op _ _
              have hro0 : t0.ReadOnce := MTree.readOnce_map hlift_inj T.roPos
              have hN_in0 : Slot.wire N ∈ t0.leaves := by
                rw [MTree.leaves_map]; exact Finset.mem_image.mpr ⟨some N, mem_optWires.mp hNP, rfl⟩
              have hdisj0 : Disjoint (t0.leaves.erase (Slot.wire N)) sTree.leaves := by
                rw [hsl, Finset.disjoint_right]; intro s hs
                simp only [Finset.mem_insert, Finset.mem_singleton] at hs
                rcases hs with rfl | rfl
                · intro hm; rw [Finset.mem_erase, MTree.leaves_map] at hm
                  rcases Finset.mem_image.mp hm.2 with ⟨o, _, ho⟩; cases o <;> cases ho
                · intro hm; rw [Finset.mem_erase, MTree.leaves_map] at hm
                  rcases Finset.mem_image.mp hm.2 with ⟨o, ho, he⟩
                  cases o with
                  | none => cases he
                  | some w =>
                    have hwf : w = fr := by cases he; rfl
                    subst hwf
                    exact hfr_not (Finset.mem_erase.mpr ⟨fun e => hm.1 (by rw [e]),
                      Finset.mem_union_left _ (mem_optWires.mpr ho)⟩)
              let tPos' := t0.subst (Slot.wire N) sTree
              have htPos'_l : tPos'.leaves = t0.leaves.erase (Slot.wire N) ∪ {.sh, .wire fr} := by
                rw [MTree.leaves_subst _ _ _ hro0 hN_in0, hsl]
              have hsw : slotWires tPos'.leaves = insert fr (P.erase N) := by
                ext w
                rw [mem_slotWires, htPos'_l]
                simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton,
                  t0, MTree.leaves_map, Finset.mem_image, P, mem_optWires, slot_wire_inj, ne_eq]
                constructor
                · rintro (⟨h1, o, ho, he⟩ | h2 | h3)
                  · cases o with
                    | none => cases he
                    | some u =>
                      have huw : u = w := by cases he; rfl
                      subst huw; exact Or.inr ⟨h1, ho⟩
                  · cases h2
                  · exact Or.inl h3
                · rintro (rfl | ⟨h1, h2⟩)
                  · exact Or.inr (Or.inr rfl)
                  · exact Or.inl ⟨h1, some w, h2, rfl⟩
              let tNeg' := (T.tNeg.map some).subst (some sh) (.leaf none)
              have hroN0 : (T.tNeg.map some).ReadOnce :=
                MTree.readOnce_map (fun _ _ e => by cases e; rfl) T.roNeg
              have hsh_inN : some sh ∈ (T.tNeg.map some).leaves := by
                rw [MTree.leaves_map]; exact Finset.mem_image_of_mem _ hsh_H
              have hdisjN : Disjoint ((T.tNeg.map some).leaves.erase (some sh)) (MTree.leaf (none : Option ℕ)).leaves := by
                rw [Finset.disjoint_right]; intro o ho; simp [MTree.leaves] at ho; subst ho
                simp [MTree.leaves_map]
              have htNeg'_l : tNeg'.leaves = (T.tNeg.map some).leaves.erase (some sh) ∪ {none} :=
                MTree.leaves_subst _ _ _ hroN0 hsh_inN
              have how : optWires tNeg'.leaves = H.erase sh := by
                ext w; rw [mem_optWires, htNeg'_l, Finset.mem_union, Finset.mem_erase, MTree.leaves_map]
                simp [H]
              have hfr_notH : fr ∉ H := fun hmem =>
                hfr_not (Finset.mem_erase.mpr ⟨fun e => Finset.disjoint_left.mp T.disj_PH hNP (by rw [e] at hmem; exact hmem),
                  Finset.mem_union_right _ hmem⟩)
              let D : Decomp N (fun x => f (stp x g)) := {
                tPos := tPos'
                tNeg := tNeg'
                sSh := MTree.leaf sh
                roPos := MTree.readOnce_subst _ _ _ hro0 hsro hdisj0
                roNeg := MTree.readOnce_subst _ _ _ hroN0 trivial hdisjN
                roSh := trivial
                sh_in_pos := by rw [htPos'_l]; simp
                neg_in_pos := by
                  rw [htPos'_l, Finset.mem_union]; left
                  refine Finset.mem_erase.mpr ⟨(by intro e; cases e), ?_⟩
                  rw [MTree.leaves_map]; exact Finset.mem_image.mpr ⟨none, T.neg_in_pos, rfl⟩
                sh_in_neg := by rw [htNeg'_l]; simp
                disj_PH := by
                  rw [hsw, how, Finset.disjoint_insert_left]
                  exact ⟨fun hm => hfr_notH (Finset.mem_of_mem_erase hm),
                    T.disj_PH.mono (Finset.erase_subset _ _) (Finset.erase_subset _ _)⟩
                disj_PU := by
                  rw [hsw, MTree.leaves, Finset.disjoint_singleton_right, Finset.mem_insert, not_or]
                  exact ⟨hsh_ne_fr, fun hm => Finset.disjoint_right.mp T.disj_PH hsh_H (Finset.mem_of_mem_erase hm)⟩
                disj_HU := by rw [how, MTree.leaves]; simp
                eval_eq := fun x hx => by
                  dsimp only [tPos', t0, tNeg']
                  rw [T.eval_eq (stp x g) (by simp [stp, hx]), MTree.eval_subst, MTree.eval_map,
                      MTree.eval_subst, MTree.eval_map]
                  have hneg_eq : T.tNeg.eval (fun w => (stp x g).getD w false) =
                      T.tNeg.eval (Function.update (fun w => x.getD w false) sh (x.getD sh false)) := by
                    apply T.tNeg.eval_congr
                    intro w hw
                    have hwN : w ≠ N := fun e => Finset.disjoint_left.mp T.disj_PH hNP (by rw [e] at hw; exact hw)
                    rw [getD_stp_ne_of hx hwN]
                    by_cases hws : w = sh
                    · subst hws; simp
                    · rw [Function.update_of_ne hws]
                  have hneg_eq' : T.tNeg.eval ((Function.update (fun o => match o with | none => (MTree.leaf sh).eval (fun w => x.getD w false) | some w => x.getD w false) (some sh) ((MTree.leaf none).eval (fun o => match o with | none => (MTree.leaf sh).eval (fun w => x.getD w false) | some w => x.getD w false))) ∘ some) =
                      T.tNeg.eval (fun w => (stp x g).getD w false) := by
                    rw [hneg_eq]; apply T.tNeg.eval_congr; intro w _
                    simp only [Function.comp_apply, MTree.eval]
                    by_cases hws : w = sh
                    · subst hws; simp
                    · rw [Function.update_of_ne hws, Function.update_of_ne (fun e => hws (by cases e; rfl))]
                  rw [hneg_eq']
                  apply T.tPos.eval_congr
                  intro o _
                  cases o with
                  | none =>
                    dsimp only [Function.comp_apply, liftPos]
                    rw [Function.update_of_ne (by intro e; cases e)]
                  | some w =>
                    dsimp only [Function.comp_apply, liftPos]
                    by_cases hwN : w = N
                    · rw [hwN, Function.update_self, getD_stp_eq_of hx, hgeval x]
                      rcases hop_ao with h1 | h1 <;> simp [sTree, mkBinTree, h1, MTree.eval]
                    · rw [Function.update_of_ne (fun e => hwN (by cases e; rfl)), getD_stp_ne_of hx hwN]
              }
              refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨D, ?_⟩))))
              have hDw : D.wires = insert fr (T.wires.erase N) := by
                simp only [Decomp.wires, NegTree.wires, D, hsw, how, MTree.leaves]
                ext w
                simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton, P, H]
                have hNnotH : N ∉ H := Finset.disjoint_left.mp T.disj_PH hNP
                have hsh_in' : sh ≠ N ∧ (sh ∈ optWires T.tPos.leaves ∨ sh ∈ T.tNeg.leaves) := by
                  simpa [NegTree.wires] using Finset.mem_erase.mp hsh_in
                constructor
                · rintro (((rfl | ⟨h1, h2⟩) | ⟨_, h3⟩) | rfl)
                  · exact Or.inl rfl
                  · exact Or.inr ⟨h1, Or.inl h2⟩
                  · exact Or.inr ⟨fun e => hNnotH (by rw [e] at h3; exact h3), Or.inr h3⟩
                  · exact Or.inr hsh_in'
                · rintro (rfl | ⟨h1, h2 | h3⟩)
                  · exact Or.inl (Or.inl (Or.inl rfl))
                  · exact Or.inl (Or.inl (Or.inr ⟨h1, h2⟩))
                  · by_cases hws : w = sh
                    · exact Or.inr hws
                    · exact Or.inl (Or.inr ⟨hws, h3⟩)
              rw [hDw]
              have h1 := Finset.card_insert_le fr (T.wires.erase N)
              have h2 := Finset.card_erase_of_mem ht
              have hpos : 0 < T.wires.card := Finset.card_pos.mpr ⟨N, ht⟩
              omega
            · have hN_notP : N ∉ P := Finset.disjoint_right.mp T.disj_PH hNH
              have hsh_P : sh ∈ P := by
                by_contra hnp
                exact hsame (iff_of_false hN_notP hnp)
              let liftPos : Option ℕ → Slot := fun o => match o with | none => .neg | some w => .wire w
              have hlift_inj : Function.Injective liftPos := by
                intro o1 o2 he; cases o1 <;> cases o2 <;> simp [liftPos] at he ⊢; exact he
              let t0 := T.tPos.map liftPos
              have hro0 : t0.ReadOnce := MTree.readOnce_map hlift_inj T.roPos
              have hsh_in0 : Slot.wire sh ∈ t0.leaves := by
                rw [MTree.leaves_map]; exact Finset.mem_image.mpr ⟨some sh, mem_optWires.mp hsh_P, rfl⟩
              have hdisj0 : Disjoint (t0.leaves.erase (Slot.wire sh)) (MTree.leaf Slot.sh).leaves := by
                rw [Finset.disjoint_right]; intro s hs; simp [MTree.leaves] at hs; subst hs
                rw [Finset.mem_erase, MTree.leaves_map]
                intro hm; rcases Finset.mem_image.mp hm.2 with ⟨o, _, ho⟩; cases o <;> cases ho
              let tPos' := t0.subst (Slot.wire sh) (.leaf .sh)
              have htPos'_l : tPos'.leaves = t0.leaves.erase (Slot.wire sh) ∪ {Slot.sh} :=
                MTree.leaves_subst _ _ _ hro0 hsh_in0
              have hsw : slotWires tPos'.leaves = P.erase sh := by
                ext w
                rw [mem_slotWires, htPos'_l]
                simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton,
                  t0, MTree.leaves_map, Finset.mem_image, P, mem_optWires, slot_wire_inj, ne_eq]
                constructor
                · rintro (⟨h1, o, ho, he⟩ | h2)
                  · cases o with
                    | none => cases he
                    | some u =>
                      have huw : u = w := by cases he; rfl
                      subst huw; exact ⟨h1, ho⟩
                  · cases h2
                · rintro ⟨h1, h2⟩; exact Or.inl ⟨h1, some w, h2, rfl⟩
              let sTreeN : MTree (Option ℕ) := mkBinTree g.op none (some fr)
              have hsroN : sTreeN.ReadOnce := mkBinTree_ro g.op _ _ (by intro e; cases e)
              have hslN : sTreeN.leaves = {none, some fr} := mkBinTree_leaves g.op _ _
              have hroN0 : (T.tNeg.map some).ReadOnce :=
                MTree.readOnce_map (fun _ _ e => by cases e; rfl) T.roNeg
              have hN_inN : some N ∈ (T.tNeg.map some).leaves := by
                rw [MTree.leaves_map]; exact Finset.mem_image_of_mem _ hNH
              have hdisjN : Disjoint ((T.tNeg.map some).leaves.erase (some N)) sTreeN.leaves := by
                rw [hslN, Finset.disjoint_right]; intro o ho
                simp only [Finset.mem_insert, Finset.mem_singleton] at ho
                rcases ho with rfl | rfl
                · simp [MTree.leaves_map]
                · intro hm; rw [Finset.mem_erase, MTree.leaves_map] at hm
                  rcases Finset.mem_image.mp hm.2 with ⟨w, hw, he⟩
                  have : w = fr := by cases he; rfl
                  subst this
                  exact hfr_not (Finset.mem_erase.mpr ⟨fun e => hm.1 (by rw [e]),
                    Finset.mem_union_right _ hw⟩)
              let tNeg' := (T.tNeg.map some).subst (some N) sTreeN
              have htNeg'_l : tNeg'.leaves = (T.tNeg.map some).leaves.erase (some N) ∪ {none, some fr} := by
                rw [MTree.leaves_subst _ _ _ hroN0 hN_inN, hslN]
              have how : optWires tNeg'.leaves = insert fr (H.erase N) := by
                ext w
                rw [mem_optWires, htNeg'_l]
                simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton,
                  MTree.leaves_map, Finset.mem_image, H, Option.some.injEq, ne_eq]
                constructor
                · rintro (⟨h1, u, hu, rfl⟩ | h2 | h3)
                  · exact Or.inr ⟨h1, hu⟩
                  · cases h2
                  · exact Or.inl h3
                · rintro (rfl | ⟨h1, h2⟩)
                  · exact Or.inr (Or.inr rfl)
                  · exact Or.inl ⟨h1, w, h2, rfl⟩
              have hfr_notP : fr ∉ P := fun hmem =>
                hfr_not (Finset.mem_erase.mpr ⟨fun e => hN_notP (by rw [e] at hmem; exact hmem), Finset.mem_union_left _ hmem⟩)
              let D : Decomp N (fun x => f (stp x g)) := {
                tPos := tPos'
                tNeg := tNeg'
                sSh := MTree.leaf sh
                roPos := MTree.readOnce_subst _ _ _ hro0 trivial hdisj0
                roNeg := MTree.readOnce_subst _ _ _ hroN0 hsroN hdisjN
                roSh := trivial
                sh_in_pos := by rw [htPos'_l]; simp
                neg_in_pos := by
                  rw [htPos'_l, Finset.mem_union]; left
                  refine Finset.mem_erase.mpr ⟨(by intro e; cases e), ?_⟩
                  rw [MTree.leaves_map]; exact Finset.mem_image.mpr ⟨none, T.neg_in_pos, rfl⟩
                sh_in_neg := by rw [htNeg'_l]; simp
                disj_PH := by
                  rw [hsw, how, Finset.disjoint_insert_right]
                  exact ⟨fun hm => hfr_notP (Finset.mem_of_mem_erase hm),
                    T.disj_PH.mono (Finset.erase_subset _ _) (Finset.erase_subset _ _)⟩
                disj_PU := by rw [hsw, MTree.leaves]; simp
                disj_HU := by
                  rw [how, MTree.leaves, Finset.disjoint_singleton_right, Finset.mem_insert, not_or]
                  exact ⟨hsh_ne_fr, fun hm => Finset.disjoint_left.mp T.disj_PH hsh_P (Finset.mem_of_mem_erase hm)⟩
                eval_eq := fun x hx => by
                  dsimp only [tPos', t0, tNeg']
                  rw [T.eval_eq (stp x g) (by simp [stp, hx]), MTree.eval_subst, MTree.eval_map,
                      MTree.eval_subst, MTree.eval_map]
                  have hneg_eq : T.tNeg.eval (fun w => (stp x g).getD w false) =
                      T.tNeg.eval ((Function.update (fun o => match o with | none => (MTree.leaf sh).eval (fun w => x.getD w false) | some w => x.getD w false) (some N) (sTreeN.eval (fun o => match o with | none => (MTree.leaf sh).eval (fun w => x.getD w false) | some w => x.getD w false))) ∘ some) := by
                    apply T.tNeg.eval_congr
                    intro w _
                    dsimp only [Function.comp_apply]
                    by_cases hwN : w = N
                    · rw [hwN, Function.update_self, getD_stp_eq_of hx, hgeval x]
                      rcases hop_ao with h1 | h1 <;> simp [sTreeN, mkBinTree, h1, MTree.eval]
                    · rw [Function.update_of_ne (fun e => hwN (by cases e; rfl)), getD_stp_ne_of hx hwN]
                  rw [hneg_eq]
                  apply T.tPos.eval_congr
                  intro o ho
                  cases o with
                  | none =>
                    dsimp only [Function.comp_apply, liftPos]
                    rw [Function.update_of_ne (by intro e; cases e)]
                  | some w =>
                    dsimp only [Function.comp_apply, liftPos, MTree.eval]
                    have hwN : w ≠ N := fun e => hN_notP (by have h := mem_optWires.mpr ho; rw [e] at h; exact h)
                    rw [getD_stp_ne_of hx hwN]
                    by_cases hws : w = sh
                    · subst hws; simp
                    · rw [Function.update_of_ne (fun e => hws (by cases e; rfl))]
              }
              refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨D, ?_⟩))))
              have hDw : D.wires = insert fr (T.wires.erase N) := by
                simp only [Decomp.wires, NegTree.wires, D, hsw, how, MTree.leaves]
                ext w
                simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton, P, H]
                have hsh_in' : sh ≠ N ∧ (sh ∈ optWires T.tPos.leaves ∨ sh ∈ T.tNeg.leaves) := by
                  simpa [NegTree.wires] using Finset.mem_erase.mp hsh_in
                constructor
                · rintro ((⟨_, h1⟩ | (rfl | ⟨h2, h3⟩)) | rfl)
                  · exact Or.inr ⟨fun e => hN_notP (by rw [e] at h1; exact h1), Or.inl h1⟩
                  · exact Or.inl rfl
                  · exact Or.inr ⟨h2, Or.inr h3⟩
                  · exact Or.inr hsh_in'
                · rintro (rfl | ⟨h1, h2 | h3⟩)
                  · exact Or.inl (Or.inr (Or.inl rfl))
                  · by_cases hws : w = sh
                    · exact Or.inr hws
                    · exact Or.inl (Or.inl ⟨hws, h2⟩)
                  · exact Or.inl (Or.inr (Or.inr ⟨h1, h3⟩))
              rw [hDw]
              have h1 := Finset.card_insert_le fr (T.wires.erase N)
              have h2 := Finset.card_erase_of_mem ht
              have hpos : 0 < T.wires.card := Finset.card_pos.mpr ⟨N, ht⟩
              omega
  · simp [hgin] at hg

lemma tightInv_step_negTree (N s : ℕ) (hasNot : Bool) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (f : List Bool → Bool) (T : NegTree (N + 1) f) (hTc : T.wires.card ≤ s) :
    TightInv N (s + 1) (hasNot || isNotOp g.op) (fun x => f (stp x g)) := by
  have hop : g.op = .and ∨ g.op = .or ∨ g.op = .not := by
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hg.1
  let P := optWires T.tPos.leaves
  have hUn : UnateOn (N + 1) f T.wires (fun w => decide (w ∈ P)) := T.unateOn
  by_cases ht : N ∈ T.wires
  · rcases hop with h | h | h
    · exact tightInv_step_negTree_ao N s hasNot g hg (Or.inl h) f T hTc ht
    · exact tightInv_step_negTree_ao N s hasNot g hg (Or.inr h) f T hTc ht
    · cases hgin : g.inputs with
      | nil =>
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨T.wires.erase N, ?_, ?_⟩))))
        · have h2 := Finset.card_erase_of_mem ht
          have hpos : 0 < T.wires.card := Finset.card_pos.mpr ⟨N, ht⟩
          omega
        · simpa [ht, effInputs, h, hgin] using dep_step_aux (unate_to_dep hUn) g
      | cons a tl =>
        by_cases ha : a ∈ T.wires.erase N
        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨T.wires.erase N, ?_, ?_⟩))))
          · have h2 := Finset.card_erase_of_mem ht
            have hpos : 0 < T.wires.card := Finset.card_pos.mpr ⟨N, ht⟩
            omega
          · have heq : T.wires.erase N ∪ (effInputs g).toFinset = T.wires.erase N := by
              ext w
              simp only [Finset.mem_union, List.mem_toFinset, effInputs, h, hgin, List.mem_singleton,
                or_iff_left_iff_imp]
              rintro rfl; exact ha
            simpa [ht, heq] using dep_step_aux (unate_to_dep hUn) g
        · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨insert a (T.wires.erase N),
              Function.update (fun w => decide (w ∈ P)) a (!decide (N ∈ P)), ?_, ?_⟩)))
          · have h1 := Finset.card_insert_le a (T.wires.erase N)
            have h2 := Finset.card_erase_of_mem ht
            have hpos : 0 < T.wires.card := Finset.card_pos.mpr ⟨N, ht⟩
            omega
          · intro x y hx hy hxy
            apply hUn (stp x g) (stp y g) (by simp [stp, hx]) (by simp [stp, hy])
            intro i hi
            by_cases hiN : i = N
            · subst hiN
              have ha_dir := hxy a (Finset.mem_insert_self a _)
              simp only [Function.update_self] at ha_dir
              rw [getD_stp_eq_of hx, getD_stp_eq_of hy, h, hgin]
              simp only [GateOp.eval, List.map_cons, List.headD_cons]
              cases hc : decide (i ∈ P) <;> cases hxa : x.getD a false <;> cases hya : y.getD a false <;> simp_all
            · have hi' : i ∈ T.wires.erase N := Finset.mem_erase.mpr ⟨hiN, hi⟩
              have hia : i ≠ a := fun e => ha (e ▸ hi')
              have hidir := hxy i (Finset.mem_insert_of_mem hi')
              simp only [Function.update_of_ne hia] at hidir
              rw [getD_stp_ne_of hx hiN, getD_stp_ne_of hy hiN]
              exact hidir
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨T.wires, fun w => decide (w ∈ P), by omega, ?_⟩)))
    intro x y hx hy hxy
    apply hUn (stp x g) (stp y g) (by simp [stp, hx]) (by simp [stp, hy])
    intro i hi; have hiN : i ≠ N := fun e => ht (e ▸ hi)
    rw [getD_stp_ne_of hx hiN, getD_stp_ne_of hy hiN]; exact hxy i hi

lemma tightInv_step_decomp (N s : ℕ) (hasNot : Bool) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (f : List Bool → Bool) (D : Decomp (N + 1) f) (hDc : D.wires.card + 1 ≤ s) :
    TightInv N (s + 1) (hasNot || isNotOp g.op) (fun x => f (stp x g)) := by
  have hop : g.op = .and ∨ g.op = .or ∨ g.op = .not := by
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hg.1
  let P := slotWires D.tPos.leaves
  let H := optWires D.tNeg.leaves
  let U := D.sSh.leaves
  by_cases ht : N ∈ D.wires
  · by_cases hbin : (g.op = .and ∨ g.op = .or) ∧ ∃ a b, g.inputs = [a, b] ∧ a ≠ b ∧
        a ∉ D.wires.erase N ∧ b ∉ D.wires.erase N
    · obtain ⟨hop_ao, a, b, hgin, hab, ha_not, hb_not⟩ := hbin
      have hgeval : ∀ x : List Bool, g.op.eval (g.inputs.map fun w => x.getD w false) =
          (mkBinTree g.op a b).eval (fun w => x.getD w false) :=
        fun x => mkBinTree_eval g hop_ao a b hgin x
      have hPU : P ⊆ D.wires := fun w hw => Finset.mem_union_left _ (Finset.mem_union_left _ hw)
      have hHU : H ⊆ D.wires := fun w hw => Finset.mem_union_left _ (Finset.mem_union_right _ hw)
      have hUU : U ⊆ D.wires := fun w hw => Finset.mem_union_right _ hw
      rcases Finset.mem_union.mp ht with hPH | hNU
      · rcases Finset.mem_union.mp hPH with hNP | hNH
        · have hN_notH : N ∉ H := Finset.disjoint_left.mp D.disj_PH hNP
          have hN_notU : N ∉ U := Finset.disjoint_left.mp D.disj_PU hNP
          let sTree : MTree Slot := mkBinTree g.op (Slot.wire a) (Slot.wire b)
          have hsro : sTree.ReadOnce := mkBinTree_ro g.op (Slot.wire a) (Slot.wire b) (fun e => hab (by cases e; rfl))
          have hsl : sTree.leaves = {Slot.wire a, Slot.wire b} := mkBinTree_leaves g.op _ _
          have hN_in : Slot.wire N ∈ D.tPos.leaves := mem_slotWires.mp hNP
          have hdisj : Disjoint (D.tPos.leaves.erase (Slot.wire N)) sTree.leaves := by
            rw [hsl, Finset.disjoint_right]; intro s hs
            simp only [Finset.mem_insert, Finset.mem_singleton] at hs
            rcases hs with rfl | rfl
            · intro hm; have := Finset.mem_erase.mp hm
              exact ha_not (Finset.mem_erase.mpr ⟨fun e => this.1 (by rw [e]), hPU (mem_slotWires.mpr this.2)⟩)
            · intro hm; have := Finset.mem_erase.mp hm
              exact hb_not (Finset.mem_erase.mpr ⟨fun e => this.1 (by rw [e]), hPU (mem_slotWires.mpr this.2)⟩)
          let tPos' := D.tPos.subst (Slot.wire N) sTree
          have htPos'_l : tPos'.leaves = D.tPos.leaves.erase (Slot.wire N) ∪ {Slot.wire a, Slot.wire b} := by
            rw [MTree.leaves_subst _ _ _ D.roPos hN_in, hsl]
          have hsw : slotWires tPos'.leaves = P.erase N ∪ {a, b} := by
            ext w; rw [mem_slotWires, htPos'_l]
            simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton,
              P, mem_slotWires, slot_wire_inj, ne_eq]
          have ha_notH : a ∉ H := fun hm => ha_not (Finset.mem_erase.mpr ⟨fun e => hN_notH (e ▸ hm), hHU hm⟩)
          have hb_notH : b ∉ H := fun hm => hb_not (Finset.mem_erase.mpr ⟨fun e => hN_notH (e ▸ hm), hHU hm⟩)
          have ha_notU : a ∉ U := fun hm => ha_not (Finset.mem_erase.mpr ⟨fun e => hN_notU (e ▸ hm), hUU hm⟩)
          have hb_notU : b ∉ U := fun hm => hb_not (Finset.mem_erase.mpr ⟨fun e => hN_notU (e ▸ hm), hUU hm⟩)
          let D' : Decomp N (fun x => f (stp x g)) := {
            tPos := tPos'
            tNeg := D.tNeg
            sSh := D.sSh
            roPos := MTree.readOnce_subst _ _ _ D.roPos hsro hdisj
            roNeg := D.roNeg
            roSh := D.roSh
            sh_in_pos := by rw [htPos'_l, Finset.mem_union]; left; exact Finset.mem_erase.mpr ⟨(by intro e; cases e), D.sh_in_pos⟩
            neg_in_pos := by rw [htPos'_l, Finset.mem_union]; left; exact Finset.mem_erase.mpr ⟨(by intro e; cases e), D.neg_in_pos⟩
            sh_in_neg := D.sh_in_neg
            disj_PH := by
              rw [hsw, Finset.disjoint_union_left]
              refine ⟨Finset.disjoint_of_subset_left (Finset.erase_subset _ _) D.disj_PH, ?_⟩
              rw [Finset.disjoint_left]; intro w hw; simp at hw; rcases hw with rfl | rfl; exact ha_notH; exact hb_notH
            disj_PU := by
              rw [hsw, Finset.disjoint_union_left]
              refine ⟨Finset.disjoint_of_subset_left (Finset.erase_subset _ _) D.disj_PU, ?_⟩
              rw [Finset.disjoint_left]; intro w hw; simp at hw; rcases hw with rfl | rfl; exact ha_notU; exact hb_notU
            disj_HU := D.disj_HU
            eval_eq := fun x hx => by
              dsimp only [tPos']
              rw [D.eval_eq (stp x g) (by simp [stp, hx]), MTree.eval_subst]
              have hsh_eq : D.sSh.eval (fun w => (stp x g).getD w false) = D.sSh.eval (fun w => x.getD w false) :=
                D.sSh.eval_congr (fun w hw => getD_stp_ne_of hx (fun e => hN_notU (e ▸ hw)))
              have hneg_eq : D.tNeg.eval (fun o => match o with | none => D.sSh.eval (fun w => (stp x g).getD w false) | some w => (stp x g).getD w false) =
                  D.tNeg.eval (fun o => match o with | none => D.sSh.eval (fun w => x.getD w false) | some w => x.getD w false) := by
                apply D.tNeg.eval_congr; intro o ho; cases o with
                | none => exact hsh_eq
                | some w => exact getD_stp_ne_of hx (fun e => hN_notH (e ▸ mem_optWires.mpr ho))
              apply D.tPos.eval_congr; intro s _
              cases s with
              | sh =>
                dsimp only
                rw [Function.update_of_ne (by intro e; cases e)]
                exact hsh_eq
              | neg =>
                dsimp only
                rw [Function.update_of_ne (by intro e; cases e)]
                dsimp only
                rw [hneg_eq]
              | wire w =>
                dsimp only
                by_cases hwN : w = N
                · subst hwN
                  rw [Function.update_self, getD_stp_eq_of hx, hgeval x]
                  rcases hop_ao with h1 | h1 <;> simp [sTree, mkBinTree, h1, MTree.eval]
                · rw [Function.update_of_ne (fun e => hwN (by cases e; rfl)), getD_stp_ne_of hx hwN]
          }
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨D', ?_⟩))))
          have hDw : D'.wires = D.wires.erase N ∪ {a, b} := by
            simp only [Decomp.wires, D', hsw]
            ext w; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, P]
            constructor
            · rintro (((⟨h1, h2⟩ | h3) | h4) | h5)
              · exact Or.inl ⟨h1, Or.inl (Or.inl h2)⟩
              · exact Or.inr h3
              · exact Or.inl ⟨fun e => hN_notH (e ▸ h4), Or.inl (Or.inr h4)⟩
              · exact Or.inl ⟨fun e => hN_notU (e ▸ h5), Or.inr h5⟩
            · rintro (⟨h1, (h2 | h3) | h4⟩ | h5)
              · exact Or.inl (Or.inl (Or.inl ⟨h1, h2⟩))
              · exact Or.inl (Or.inr h3)
              · exact Or.inr h4
              · exact Or.inl (Or.inl (Or.inr h5))
          rw [hDw]
          have h1 := Finset.card_union_le (D.wires.erase N) {a, b}
          have h2 := Finset.card_erase_of_mem ht
          have h3 : ({a, b} : Finset ℕ).card ≤ 2 := Finset.card_insert_le _ _
          have hpos : 0 < D.wires.card := Finset.card_pos.mpr ⟨N, ht⟩
          omega
        · have hN_notP : N ∉ P := Finset.disjoint_right.mp D.disj_PH hNH
          have hN_notU : N ∉ U := Finset.disjoint_left.mp D.disj_HU hNH
          let sTree : MTree (Option ℕ) := mkBinTree g.op (some a) (some b)
          have hsro : sTree.ReadOnce := mkBinTree_ro g.op (some a) (some b) (fun e => hab (by cases e; rfl))
          have hsl : sTree.leaves = {some a, some b} := mkBinTree_leaves g.op _ _
          have hN_in : some N ∈ D.tNeg.leaves := mem_optWires.mp hNH
          have hdisj : Disjoint (D.tNeg.leaves.erase (some N)) sTree.leaves := by
            rw [hsl, Finset.disjoint_right]; intro o ho
            simp only [Finset.mem_insert, Finset.mem_singleton] at ho
            rcases ho with rfl | rfl
            · intro hm; have := Finset.mem_erase.mp hm
              exact ha_not (Finset.mem_erase.mpr ⟨fun e => this.1 (by rw [e]), hHU (mem_optWires.mpr this.2)⟩)
            · intro hm; have := Finset.mem_erase.mp hm
              exact hb_not (Finset.mem_erase.mpr ⟨fun e => this.1 (by rw [e]), hHU (mem_optWires.mpr this.2)⟩)
          let tNeg' := D.tNeg.subst (some N) sTree
          have htNeg'_l : tNeg'.leaves = D.tNeg.leaves.erase (some N) ∪ {some a, some b} := by
            rw [MTree.leaves_subst _ _ _ D.roNeg hN_in, hsl]
          have how : optWires tNeg'.leaves = H.erase N ∪ {a, b} := by
            ext w; rw [mem_optWires, htNeg'_l]
            simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton,
              H, mem_optWires, Option.some.injEq, ne_eq]
          have ha_notP : a ∉ P := fun hm => ha_not (Finset.mem_erase.mpr ⟨fun e => hN_notP (e ▸ hm), hPU hm⟩)
          have hb_notP : b ∉ P := fun hm => hb_not (Finset.mem_erase.mpr ⟨fun e => hN_notP (e ▸ hm), hPU hm⟩)
          have ha_notU : a ∉ U := fun hm => ha_not (Finset.mem_erase.mpr ⟨fun e => hN_notU (e ▸ hm), hUU hm⟩)
          have hb_notU : b ∉ U := fun hm => hb_not (Finset.mem_erase.mpr ⟨fun e => hN_notU (e ▸ hm), hUU hm⟩)
          let D' : Decomp N (fun x => f (stp x g)) := {
            tPos := D.tPos
            tNeg := tNeg'
            sSh := D.sSh
            roPos := D.roPos
            roNeg := MTree.readOnce_subst _ _ _ D.roNeg hsro hdisj
            roSh := D.roSh
            sh_in_pos := D.sh_in_pos
            neg_in_pos := D.neg_in_pos
            sh_in_neg := by rw [htNeg'_l, Finset.mem_union]; left; exact Finset.mem_erase.mpr ⟨(by intro e; cases e), D.sh_in_neg⟩
            disj_PH := by
              rw [how, Finset.disjoint_union_right]
              refine ⟨Finset.disjoint_of_subset_right (Finset.erase_subset _ _) D.disj_PH, ?_⟩
              rw [Finset.disjoint_right]; intro w hw; simp at hw; rcases hw with rfl | rfl; exact ha_notP; exact hb_notP
            disj_PU := D.disj_PU
            disj_HU := by
              rw [how, Finset.disjoint_union_left]
              refine ⟨Finset.disjoint_of_subset_left (Finset.erase_subset _ _) D.disj_HU, ?_⟩
              rw [Finset.disjoint_left]; intro w hw; simp at hw; rcases hw with rfl | rfl; exact ha_notU; exact hb_notU
            eval_eq := fun x hx => by
              dsimp only [tNeg']
              rw [D.eval_eq (stp x g) (by simp [stp, hx]), MTree.eval_subst]
              have hsh_eq : D.sSh.eval (fun w => (stp x g).getD w false) = D.sSh.eval (fun w => x.getD w false) :=
                D.sSh.eval_congr (fun w hw => getD_stp_ne_of hx (fun e => hN_notU (e ▸ hw)))
              have hneg_eq : D.tNeg.eval (fun o => match o with | none => D.sSh.eval (fun w => (stp x g).getD w false) | some w => (stp x g).getD w false) =
                  D.tNeg.eval (Function.update (fun o => match o with | none => D.sSh.eval (fun w => x.getD w false) | some w => x.getD w false) (some N) (sTree.eval (fun o => match o with | none => D.sSh.eval (fun w => x.getD w false) | some w => x.getD w false))) := by
                apply D.tNeg.eval_congr; intro o _
                cases o with
                | none =>
                  dsimp only
                  rw [Function.update_of_ne (by intro e; cases e)]
                  exact hsh_eq
                | some w =>
                  dsimp only
                  by_cases hwN : w = N
                  · subst hwN
                    rw [Function.update_self, getD_stp_eq_of hx, hgeval x]
                    rcases hop_ao with h1 | h1 <;> simp [sTree, mkBinTree, h1, MTree.eval]
                  · rw [Function.update_of_ne (fun e => hwN (by cases e; rfl)), getD_stp_ne_of hx hwN]
              apply D.tPos.eval_congr; intro s hs
              cases s with
              | sh => exact hsh_eq
              | neg => dsimp only; rw [hneg_eq]
              | wire w => exact getD_stp_ne_of hx (fun e => hN_notP (e ▸ mem_slotWires.mpr hs))
          }
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨D', ?_⟩))))
          have hDw : D'.wires = D.wires.erase N ∪ {a, b} := by
            simp only [Decomp.wires, D', how]
            ext w; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, H]
            constructor
            · rintro ((h1 | (⟨h2, h3⟩ | h4)) | h5)
              · exact Or.inl ⟨fun e => hN_notP (e ▸ h1), Or.inl (Or.inl h1)⟩
              · exact Or.inl ⟨h2, Or.inl (Or.inr h3)⟩
              · exact Or.inr h4
              · exact Or.inl ⟨fun e => hN_notU (e ▸ h5), Or.inr h5⟩
            · rintro (⟨h1, (h2 | h3) | h4⟩ | h5)
              · exact Or.inl (Or.inl h2)
              · exact Or.inl (Or.inr (Or.inl ⟨h1, h3⟩))
              · exact Or.inr h4
              · exact Or.inl (Or.inr (Or.inr h5))
          rw [hDw]
          have h1 := Finset.card_union_le (D.wires.erase N) {a, b}
          have h2 := Finset.card_erase_of_mem ht
          have h3 : ({a, b} : Finset ℕ).card ≤ 2 := Finset.card_insert_le _ _
          have hpos : 0 < D.wires.card := Finset.card_pos.mpr ⟨N, ht⟩
          omega
      · have hN_notP : N ∉ P := Finset.disjoint_right.mp D.disj_PU hNU
        have hN_notH : N ∉ H := Finset.disjoint_right.mp D.disj_HU hNU
        let sTree : MTree ℕ := mkBinTree g.op a b
        have hsro : sTree.ReadOnce := mkBinTree_ro g.op a b hab
        have hsl : sTree.leaves = {a, b} := mkBinTree_leaves g.op a b
        have hdisj : Disjoint (U.erase N) sTree.leaves := by
          rw [hsl, Finset.disjoint_right]; intro w hw
          simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl
          · intro hm; exact ha_not (Finset.erase_subset_erase N hUU hm)
          · intro hm; exact hb_not (Finset.erase_subset_erase N hUU hm)
        let sSh' := D.sSh.subst N sTree
        have hsSh'_l : sSh'.leaves = U.erase N ∪ {a, b} := by
          rw [MTree.leaves_subst _ _ _ D.roSh hNU, hsl]
        have ha_notP : a ∉ P := fun hm => ha_not (Finset.mem_erase.mpr ⟨fun e => hN_notP (e ▸ hm), hPU hm⟩)
        have hb_notP : b ∉ P := fun hm => hb_not (Finset.mem_erase.mpr ⟨fun e => hN_notP (e ▸ hm), hPU hm⟩)
        have ha_notH : a ∉ H := fun hm => ha_not (Finset.mem_erase.mpr ⟨fun e => hN_notH (e ▸ hm), hHU hm⟩)
        have hb_notH : b ∉ H := fun hm => hb_not (Finset.mem_erase.mpr ⟨fun e => hN_notH (e ▸ hm), hHU hm⟩)
        let D' : Decomp N (fun x => f (stp x g)) := {
          tPos := D.tPos
          tNeg := D.tNeg
          sSh := sSh'
          roPos := D.roPos
          roNeg := D.roNeg
          roSh := MTree.readOnce_subst _ _ _ D.roSh hsro hdisj
          sh_in_pos := D.sh_in_pos
          neg_in_pos := D.neg_in_pos
          sh_in_neg := D.sh_in_neg
          disj_PH := D.disj_PH
          disj_PU := by
            rw [hsSh'_l, Finset.disjoint_union_right]
            refine ⟨Finset.disjoint_of_subset_right (Finset.erase_subset _ _) D.disj_PU, ?_⟩
            rw [Finset.disjoint_right]; intro w hw; simp at hw; rcases hw with rfl | rfl; exact ha_notP; exact hb_notP
          disj_HU := by
            rw [hsSh'_l, Finset.disjoint_union_right]
            refine ⟨Finset.disjoint_of_subset_right (Finset.erase_subset _ _) D.disj_HU, ?_⟩
            rw [Finset.disjoint_right]; intro w hw; simp at hw; rcases hw with rfl | rfl; exact ha_notH; exact hb_notH
          eval_eq := fun x hx => by
            dsimp only [sSh']
            rw [D.eval_eq (stp x g) (by simp [stp, hx]), MTree.eval_subst]
            have hsh_eq : D.sSh.eval (fun w => (stp x g).getD w false) =
                D.sSh.eval (Function.update (fun w => x.getD w false) N (sTree.eval (fun w => x.getD w false))) := by
              apply D.sSh.eval_congr; intro w _
              by_cases hwN : w = N
              · subst hwN; rw [Function.update_self, getD_stp_eq_of hx, hgeval x]
              · rw [Function.update_of_ne hwN, getD_stp_ne_of hx hwN]
            have hneg_eq : D.tNeg.eval (fun o => match o with | none => D.sSh.eval (fun w => (stp x g).getD w false) | some w => (stp x g).getD w false) =
                D.tNeg.eval (fun o => match o with | none => D.sSh.eval (Function.update (fun w => x.getD w false) N (sTree.eval (fun w => x.getD w false))) | some w => x.getD w false) := by
              apply D.tNeg.eval_congr; intro o ho; cases o with
              | none => exact hsh_eq
              | some w => exact getD_stp_ne_of hx (fun e => hN_notH (e ▸ mem_optWires.mpr ho))
            apply D.tPos.eval_congr; intro s hs
            cases s with
            | sh => exact hsh_eq
            | neg => dsimp only; rw [hneg_eq]
            | wire w => exact getD_stp_ne_of hx (fun e => hN_notP (e ▸ mem_slotWires.mpr hs))
        }
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨D', ?_⟩))))
        have hDw : D'.wires = D.wires.erase N ∪ {a, b} := by
          simp only [Decomp.wires, D', hsSh'_l]
          ext w; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, U]
          constructor
          · rintro ((h1 | h2) | (⟨h3, h4⟩ | h5))
            · exact Or.inl ⟨fun e => hN_notP (e ▸ h1), Or.inl (Or.inl h1)⟩
            · exact Or.inl ⟨fun e => hN_notH (e ▸ h2), Or.inl (Or.inr h2)⟩
            · exact Or.inl ⟨h3, Or.inr h4⟩
            · exact Or.inr h5
          · rintro (⟨h1, (h2 | h3) | h4⟩ | h5)
            · exact Or.inl (Or.inl h2)
            · exact Or.inl (Or.inr h3)
            · exact Or.inr (Or.inl ⟨h1, h4⟩)
            · exact Or.inr (Or.inr h5)
        rw [hDw]
        have h1 := Finset.card_union_le (D.wires.erase N) {a, b}
        have h2 := Finset.card_erase_of_mem ht
        have h3 : ({a, b} : Finset ℕ).card ≤ 2 := Finset.card_insert_le _ _
        have hpos : 0 < D.wires.card := Finset.card_pos.mpr ⟨N, ht⟩
        omega
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨D.wires.erase N ∪ (effInputs g).toFinset, ?_, ?_⟩))))
      · have h2 := Finset.card_erase_of_mem ht
        have hpos : 0 < D.wires.card := Finset.card_pos.mpr ⟨N, ht⟩
        by_cases h1 : (effInputs g).toFinset.card ≤ 1
        · have hc := Finset.card_union_le (D.wires.erase N) (effInputs g).toFinset
          omega
        · have hle2 := List.toFinset_card_le (effInputs g)
          have hlen2 := effInputs_len_le2 g hg
          have heff2 : (effInputs g).length = 2 := by omega
          have hop_ao : g.op = .and ∨ g.op = .or := by
            rcases hop with h | h | h
            · exact Or.inl h
            · exact Or.inr h
            · exfalso; cases hin : g.inputs <;> simp [effInputs, h, hin] at heff2
          have heff_eq : effInputs g = g.inputs := by rcases hop_ao with h | h <;> simp [effInputs, h]
          rw [heff_eq] at heff2
          rcases hgin : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> simp [hgin] at heff2
          have hab : a ≠ b := by
            intro e; subst e
            have : (effInputs g).toFinset = {a} := by rw [heff_eq, hgin]; ext w; simp
            rw [this] at h1; simp at h1
          have hmem : a ∈ D.wires.erase N ∨ b ∈ D.wires.erase N := by
            by_contra hn; push Not at hn
            exact hbin ⟨hop_ao, a, b, hgin, hab, hn.1, hn.2⟩
          have heff_pair : (effInputs g).toFinset = {a, b} := by rw [heff_eq, hgin]; ext w; simp
          rw [heff_pair]
          rcases hmem with ha | hb
          · have : D.wires.erase N ∪ {a, b} = insert b (D.wires.erase N) := by
              ext w; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
              constructor; · rintro (h | rfl | rfl); exact Or.inr h; exact Or.inr ha; exact Or.inl rfl
              · rintro (rfl | h); exact Or.inr (Or.inr rfl); exact Or.inl h
            rw [this]; have := Finset.card_insert_le b (D.wires.erase N); omega
          · have : D.wires.erase N ∪ {a, b} = insert a (D.wires.erase N) := by
              ext w; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
              constructor; · rintro (h | rfl | rfl); exact Or.inr h; exact Or.inl rfl; exact Or.inr hb
              · rintro (rfl | h); exact Or.inr (Or.inl rfl); exact Or.inl h
            rw [this]; have := Finset.card_insert_le a (D.wires.erase N); omega
      · simpa [ht] using dep_step_aux D.dependsOn g
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨D.wires, by omega, ?_⟩))))
    simpa [ht] using dep_step_aux D.dependsOn g

lemma tightInv_step (N s : ℕ) (hasNot : Bool) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (f : List Bool → Bool) (hf : TightInv (N + 1) s hasNot f) :
    TightInv N (s + 1) (hasNot || isNotOp g.op) (fun x => f (stp x g)) := by
  rcases hf with ⟨hfn, t, hro, htc, hte⟩ | ⟨R, hRc, hMono⟩ | ⟨T, hTc⟩ | ⟨R, sgn, hRc, hUn⟩ | ⟨D, hDc⟩ | ⟨R, hRc, hDep⟩
  · exact tightInv_step_treePos N s hasNot g hg f hfn t hro htc hte
  · exact tightInv_step_monoSlack N s hasNot g hg f R hRc hMono
  · exact tightInv_step_negTree N s hasNot g hg f T hTc
  · rcases unate_step_unate_or_dep hUn hRc g hg with ⟨R', sgn', h1, h2⟩ | ⟨R', h1, h2⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨R', sgn', h1, h2⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨R', h1, h2⟩))))
  · exact tightInv_step_decomp N s hasNot g hg f D hDc
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨if N ∈ R then R.erase N ∪ (effInputs g).toFinset else R, ?_, dep_step_aux hDep g⟩))))
    split_ifs with ht
    · have h1 := Finset.card_union_le (R.erase N) (effInputs g).toFinset
      have h2 := Finset.card_erase_of_mem ht
      have h3 := List.toFinset_card_le (effInputs g)
      have h4 := effInputs_len_le2 g hg
      have hpos : 0 < R.card := Finset.card_pos.mpr ⟨N, ht⟩
      omega
    · omega

def hasNotGate (gs : List Gate) : Bool :=
  gs.any (fun g => isNotOp g.op)

lemma tightInv_circuit (N : ℕ) (C : Circuit) (hC : FanInTwo C) :
    TightInv N C.size (hasNotGate C.gates) (fun x => C.eval x) := by
  suffices ∀ (gs : List Gate) (M : ℕ) (out : ℕ),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      TightInv M gs.length (hasNotGate gs) (fun x => (gs.foldl stp x).getD out false) by
    exact this C.gates N C.output hC
  intro gs
  induction gs with
  | nil =>
    intro M out _
    refine Or.inl ⟨rfl, MTree.leaf out, trivial, by simp [MTree.leaves], fun x _ => rfl⟩
  | cons g gs ih =>
    intro M out hg
    have htail := ih (M + 1) out (fun g' h => hg g' (List.mem_cons_of_mem g h))
    have hstep := tightInv_step M gs.length (hasNotGate gs) g (hg g (List.mem_cons_self ..)) _ htail
    have hnot_eq : (hasNotGate gs || isNotOp g.op) = hasNotGate (g :: gs) := by
      simp [hasNotGate, Bool.or_comm]
    rw [hnot_eq] at hstep
    simpa [List.foldl_cons, List.length_cons, Nat.add_comm] using hstep

lemma dep_card_lb_rect {n m : ℕ} (A : Fin n → Fin m → Bool)
    (hInjR : Function.Injective A) (hInjC : Function.Injective (fun j i => A i j))
    (C : Circuit) (hrep : Represents A C)
    (R : Finset ℕ) (hDep : DependsOn (n + m) (fun x => C.eval x) R) :
    (n - 1 ≤ (Finset.univ.filter (fun i : Fin n => i.val ∈ R)).card) ∧
    (m - 1 ≤ (Finset.univ.filter (fun j : Fin m => n + j.val ∈ R)).card) ∧
    (n + m - 2 ≤ R.card) := by
  let RL : Finset (Fin n) := Finset.univ.filter (fun i => i.val ∈ R)
  let RR : Finset (Fin m) := Finset.univ.filter (fun j => n + j.val ∈ R)
  have hL : n - 1 ≤ RL.card := by
    by_contra hlt
    have hcompl : 2 ≤ (Finset.univ \ RL).card := by
      have h1 : RL.card + (Finset.univ \ RL).card = n := by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
        have := Finset.card_le_univ RL
        rw [Fintype.card_fin] at this
        omega
      omega
    obtain ⟨i1, hi1, i2, hi2, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < (Finset.univ \ RL).card)
    have hni1 : i1.val ∉ R := by simpa [RL] using (Finset.mem_sdiff.mp hi1).2
    have hni2 : i2.val ∉ R := by simpa [RL] using (Finset.mem_sdiff.mp hi2).2
    have hneq : A i1 ≠ A i2 := fun e => hne (hInjR e)
    have hex : ∃ j : Fin m, A i1 j ≠ A i2 j := by
      by_contra hall; push Not at hall; exact hneq (funext hall)
    obtain ⟨j, hj⟩ := hex
    apply hj
    rw [← hrep i1 j, ← hrep i2 j]
    apply hDep _ _ (oneEach_len i1 j) (oneEach_len i2 j)
    intro k hk
    by_cases hkn : k < n
    · rw [oneEach_getD_left i1 j hkn, oneEach_getD_left i2 j hkn]
      have h1 : i1.val ≠ k := fun e => hni1 (e ▸ hk)
      have h2 : i2.val ≠ k := fun e => hni2 (e ▸ hk)
      simp [h1, h2]
    · by_cases hk2 : k < n + m
      · have hkm : k - n < m := by omega
        have hk' : k = n + (k - n) := by omega
        rw [hk', oneEach_getD_right i1 j hkm, oneEach_getD_right i2 j hkm]
      · rw [List.getD_eq_default _ _ (by rw [oneEach_len]; omega),
            List.getD_eq_default _ _ (by rw [oneEach_len]; omega)]
  have hR : m - 1 ≤ RR.card := by
    by_contra hlt
    have hcompl : 2 ≤ (Finset.univ \ RR).card := by
      have h1 : RR.card + (Finset.univ \ RR).card = m := by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
        have := Finset.card_le_univ RR
        rw [Fintype.card_fin] at this
        omega
      omega
    obtain ⟨j1, hj1, j2, hj2, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < (Finset.univ \ RR).card)
    have hnj1 : n + j1.val ∉ R := by simpa [RR] using (Finset.mem_sdiff.mp hj1).2
    have hnj2 : n + j2.val ∉ R := by simpa [RR] using (Finset.mem_sdiff.mp hj2).2
    have hneq : (fun i => A i j1) ≠ (fun i => A i j2) := fun e => hne (hInjC e)
    have hex : ∃ i : Fin n, A i j1 ≠ A i j2 := by
      by_contra hall; push Not at hall; exact hneq (funext hall)
    obtain ⟨i, hi⟩ := hex
    apply hi
    rw [← hrep i j1, ← hrep i j2]
    apply hDep _ _ (oneEach_len i j1) (oneEach_len i j2)
    intro k hk
    by_cases hkn : k < n
    · rw [oneEach_getD_left i j1 hkn, oneEach_getD_left i j2 hkn]
    · by_cases hk2 : k < n + m
      · have hkm : k - n < m := by omega
        have hk' : k = n + (k - n) := by omega
        rw [hk', oneEach_getD_right i j1 hkm, oneEach_getD_right i j2 hkm]
        have h1 : j1.val ≠ k - n := fun e => hnj1 (by rw [← e] at hk'; exact hk' ▸ hk)
        have h2 : j2.val ≠ k - n := fun e => hnj2 (by rw [← e] at hk'; exact hk' ▸ hk)
        simp [h1, h2]
      · rw [List.getD_eq_default _ _ (by rw [oneEach_len]; omega),
            List.getD_eq_default _ _ (by rw [oneEach_len]; omega)]
  let SL := RL.image (fun i : Fin n => i.val)
  let SR := RR.image (fun j : Fin m => n + j.val)
  have hSL : SL.card = RL.card := Finset.card_image_of_injective _ Fin.val_injective
  have hSR : SR.card = RR.card := Finset.card_image_of_injective _ (fun a b h => Fin.ext (by omega))
  have hdisj : Disjoint SL SR := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    rcases Finset.mem_image.mp hk1 with ⟨i, _, rfl⟩
    rcases Finset.mem_image.mp hk2 with ⟨j, _, he⟩
    omega
  have hsub : SL ∪ SR ⊆ R := by
    intro k hk
    rcases Finset.mem_union.mp hk with h | h
    · rcases Finset.mem_image.mp h with ⟨i, hi, rfl⟩; exact (Finset.mem_filter.mp hi).2
    · rcases Finset.mem_image.mp h with ⟨j, hj, rfl⟩; exact (Finset.mem_filter.mp hj).2
  have htot := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hSL, hSR] at htot
  exact ⟨hL, hR, by omega⟩

lemma unate_card_lb_rect {n m : ℕ} (A : Fin n → Fin m → Bool)
    (hRowInc : ∀ i : Fin n, ∃ k : Fin n, ¬ ((∀ j, A i j = true → A k j = true) ∨ (∀ j, A k j = true → A i j = true)))
    (hColInc : ∀ j : Fin m, ∃ l : Fin m, ¬ ((∀ i, A i j = true → A i l = true) ∨ (∀ i, A i l = true → A i j = true)))
    (C : Circuit) (hrep : Represents A C)
    (R : Finset ℕ) (sgn : ℕ → Bool) (hUn : UnateOn (n + m) (fun x => C.eval x) R sgn) :
    n + m ≤ R.card := by
  have hall : Finset.range (n + m) ⊆ R := by
    intro k hk
    have hkl : k < n + m := Finset.mem_range.mp hk
    by_contra hkR
    by_cases hkn : k < n
    · let i0 : Fin n := ⟨k, hkn⟩
      obtain ⟨u, hu_inc⟩ := hRowInc i0
      push Not at hu_inc
      obtain ⟨⟨v1, h1t, h1f⟩, ⟨v2, h2t, h2f⟩⟩ := hu_inc
      have h1f' : A u v1 = false := Bool.eq_false_iff.mpr h1f
      have h2f' : A i0 v2 = false := Bool.eq_false_iff.mpr h2f
      by_cases hs : sgn u.val = true
      · have htrue : C.eval (oneEach u v1) = true := by
          apply hUn (oneEach i0 v1) (oneEach u v1) (oneEach_len ..) (oneEach_len ..) ?_ (by dsimp only; rw [hrep, h1t])
          intro w hw
          have hw0 : w ≠ i0.val := fun e => hkR (by simpa [i0, e] using hw)
          by_cases hwu : w = u.val
          · subst hwu; simp only [hs, ite_true]; rw [oneEach_getD_left u v1 u.isLt]; simp
          · by_cases hwn : w < n
            · rw [oneEach_getD_left i0 v1 hwn, oneEach_getD_left u v1 hwn]
              simp [show i0.val ≠ w by omega, show u.val ≠ w by omega]
            · by_cases hw2 : w < n + m
              · have hwm : w - n < m := by omega
                have hw' : w = n + (w - n) := by omega
                rw [hw', oneEach_getD_right i0 v1 hwm, oneEach_getD_right u v1 hwm]
                split_ifs <;> intro h <;> exact h
              · rw [List.getD_eq_default _ _ (by rw [oneEach_len]; omega),
                    List.getD_eq_default _ _ (by rw [oneEach_len]; omega)]
                split_ifs <;> intro h <;> exact h
        rw [hrep, h1f'] at htrue; cases htrue
      · have hsf : sgn u.val = false := Bool.eq_false_iff.mpr hs
        have htrue : C.eval (oneEach i0 v2) = true := by
          apply hUn (oneEach u v2) (oneEach i0 v2) (oneEach_len ..) (oneEach_len ..) ?_ (by dsimp only; rw [hrep, h2t])
          intro w hw
          have hw0 : w ≠ i0.val := fun e => hkR (by simpa [i0, e] using hw)
          by_cases hwu : w = u.val
          · subst hwu; simp only [hsf, Bool.false_eq_true, ite_false]; rw [oneEach_getD_left u v2 u.isLt]; simp
          · by_cases hwn : w < n
            · rw [oneEach_getD_left u v2 hwn, oneEach_getD_left i0 v2 hwn]
              simp [show i0.val ≠ w by omega, show u.val ≠ w by omega]
            · by_cases hw2 : w < n + m
              · have hwm : w - n < m := by omega
                have hw' : w = n + (w - n) := by omega
                rw [hw', oneEach_getD_right u v2 hwm, oneEach_getD_right i0 v2 hwm]
                split_ifs <;> intro h <;> exact h
              · rw [List.getD_eq_default _ _ (by rw [oneEach_len]; omega),
                    List.getD_eq_default _ _ (by rw [oneEach_len]; omega)]
                split_ifs <;> intro h <;> exact h
        rw [hrep, h2f'] at htrue; cases htrue
    · let j0 : Fin m := ⟨k - n, by omega⟩
      obtain ⟨v, hv_inc⟩ := hColInc j0
      push Not at hv_inc
      obtain ⟨⟨u1, h1t, h1f⟩, ⟨u2, h2t, h2f⟩⟩ := hv_inc
      have h1f' : A u1 v = false := Bool.eq_false_iff.mpr h1f
      have h2f' : A u2 j0 = false := Bool.eq_false_iff.mpr h2f
      by_cases hs : sgn (n + v.val) = true
      · have htrue : C.eval (oneEach u1 v) = true := by
          apply hUn (oneEach u1 j0) (oneEach u1 v) (oneEach_len ..) (oneEach_len ..) ?_ (by dsimp only; rw [hrep, h1t])
          intro w hw
          have hw0 : w ≠ n + j0.val := fun e => hkR (by have hwk : w = k := (by simp [j0] at e; omega); exact hwk ▸ hw)
          by_cases hwv : w = n + v.val
          · subst hwv; simp only [hs, ite_true]; rw [oneEach_getD_right u1 v v.isLt]; simp
          · by_cases hwn : w < n
            · rw [oneEach_getD_left u1 j0 hwn, oneEach_getD_left u1 v hwn]
              split_ifs <;> intro h <;> exact h
            · by_cases hw2 : w < n + m
              · have hwm : w - n < m := by omega
                have hw' : w = n + (w - n) := by omega
                rw [hw', oneEach_getD_right u1 j0 hwm, oneEach_getD_right u1 v hwm]
                simp [show j0.val ≠ w - n by omega, show v.val ≠ w - n by omega]
              · rw [List.getD_eq_default _ _ (by rw [oneEach_len]; omega),
                    List.getD_eq_default _ _ (by rw [oneEach_len]; omega)]
                split_ifs <;> intro h <;> exact h
        rw [hrep, h1f'] at htrue; cases htrue
      · have hsf : sgn (n + v.val) = false := Bool.eq_false_iff.mpr hs
        have htrue : C.eval (oneEach u2 j0) = true := by
          apply hUn (oneEach u2 v) (oneEach u2 j0) (oneEach_len ..) (oneEach_len ..) ?_ (by dsimp only; rw [hrep, h2t])
          intro w hw
          have hw0 : w ≠ n + j0.val := fun e => hkR (by have hwk : w = k := (by simp [j0] at e; omega); exact hwk ▸ hw)
          by_cases hwv : w = n + v.val
          · subst hwv; simp only [hsf, Bool.false_eq_true, ite_false]; rw [oneEach_getD_right u2 v v.isLt]; simp
          · by_cases hwn : w < n
            · rw [oneEach_getD_left u2 v hwn, oneEach_getD_left u2 j0 hwn]
              split_ifs <;> intro h <;> exact h
            · by_cases hw2 : w < n + m
              · have hwm : w - n < m := by omega
                have hw' : w = n + (w - n) := by omega
                rw [hw', oneEach_getD_right u2 v hwm, oneEach_getD_right u2 j0 hwm]
                simp [show j0.val ≠ w - n by omega, show v.val ≠ w - n by omega]
              · rw [List.getD_eq_default _ _ (by rw [oneEach_len]; omega),
                    List.getD_eq_default _ _ (by rw [oneEach_len]; omega)]
                split_ifs <;> intro h <;> exact h
        rw [hrep, h2f'] at htrue; cases htrue
  have hle := Finset.card_le_card hall
  simpa using hle

lemma extract_decomp {n m : ℕ} (hn : 3 ≤ n) (hm : 3 ≤ m) (A : Fin n → Fin m → Bool)
    (hInjR : Function.Injective A) (hInjC : Function.Injective (fun j i => A i j))
    (hRowInc : ∀ i : Fin n, ∃ k : Fin n, ¬ ((∀ j, A i j = true → A k j = true) ∨ (∀ j, A k j = true → A i j = true)))
    (hColInc : ∀ j : Fin m, ∃ l : Fin m, ¬ ((∀ i, A i j = true → A i l = true) ∨ (∀ i, A i l = true → A i j = true)))
    (C : Circuit) (hC : FanInTwo C) (hrep : Represents A C)
    (hsize : C.size ≤ n + m - 1) (hnot : ∃ g ∈ C.gates, g.op = GateOp.not) :
    ∃ (D : Decomp (n + m) (fun x => C.eval x)) (r : Fin n) (c : Fin m),
      r.val ∉ D.wires ∧ n + c.val ∉ D.wires ∧
      (∀ i : Fin n, i ≠ r → i.val ∈ D.wires) ∧
      (∀ j : Fin m, j ≠ c → n + j.val ∈ D.wires) ∧
      (∀ w ∈ D.wires, w < n + m) := by
  have hnotB : hasNotGate C.gates = true := by
    rw [hasNotGate, List.any_eq_true]
    obtain ⟨g, hg, hop⟩ := hnot
    exact ⟨g, hg, by simp [hop, isNotOp]⟩
  have hinv := tightInv_circuit (n + m) C hC
  rw [hnotB] at hinv
  rcases hinv with ⟨hf, _⟩ | ⟨R, hRc, hMono⟩ | ⟨T, hTc⟩ | ⟨R, sgn, hRc, hUn⟩ | ⟨D, hDc⟩ | ⟨R, hRc, hDep⟩
  · cases hf
  · exfalso
    have := unate_card_lb_rect A hRowInc hColInc C hrep R (fun _ => true) hMono
    omega
  · exfalso
    have := unate_card_lb_rect A hRowInc hColInc C hrep T.wires _ T.unateOn
    omega
  · exfalso
    have := unate_card_lb_rect A hRowInc hColInc C hrep R sgn hUn
    omega
  · obtain ⟨hL, hR, htot⟩ := dep_card_lb_rect A hInjR hInjC C hrep D.wires D.dependsOn
    let RL : Finset (Fin n) := Finset.univ.filter (fun i => i.val ∈ D.wires)
    let RR : Finset (Fin m) := Finset.univ.filter (fun j => n + j.val ∈ D.wires)
    let SL := RL.image (fun i : Fin n => i.val)
    let SR := RR.image (fun j : Fin m => n + j.val)
    have hSL : SL.card = RL.card := Finset.card_image_of_injective _ Fin.val_injective
    have hSR : SR.card = RR.card := Finset.card_image_of_injective _ (fun a b h => Fin.ext (by omega))
    have hdisj : Disjoint SL SR := by
      rw [Finset.disjoint_left]; intro k hk1 hk2
      rcases Finset.mem_image.mp hk1 with ⟨i, _, rfl⟩
      rcases Finset.mem_image.mp hk2 with ⟨j, _, he⟩; omega
    have hsub : SL ∪ SR ⊆ D.wires := by
      intro k hk; rcases Finset.mem_union.mp hk with h | h
      · rcases Finset.mem_image.mp h with ⟨i, hi, rfl⟩; exact (Finset.mem_filter.mp hi).2
      · rcases Finset.mem_image.mp h with ⟨j, hj, rfl⟩; exact (Finset.mem_filter.mp hj).2
    have hcard_u : (SL ∪ SR).card = RL.card + RR.card := by rw [Finset.card_union_of_disjoint hdisj, hSL, hSR]
    have hle_D : RL.card + RR.card ≤ D.wires.card := by rw [← hcard_u]; exact Finset.card_le_card hsub
    have hRL_le : RL.card ≤ n := by have := Finset.card_le_univ RL; rwa [Fintype.card_fin] at this
    have hRR_le : RR.card ≤ m := by have := Finset.card_le_univ RR; rwa [Fintype.card_fin] at this
    have hL' : n - 1 ≤ RL.card := hL
    have hR' : m - 1 ≤ RR.card := hR
    have hD_eq : D.wires.card = n + m - 2 := by omega
    have hRL_eq : RL.card = n - 1 := by omega
    have hRR_eq : RR.card = m - 1 := by omega
    have hW_eq : SL ∪ SR = D.wires := Finset.eq_of_subset_of_card_le hsub (by omega)
    have hL1 : (Finset.univ \ RL).card = 1 := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]; omega
    have hR1 : (Finset.univ \ RR).card = 1 := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]; omega
    obtain ⟨r, hr_eq⟩ := Finset.card_eq_one.mp hL1
    obtain ⟨c, hc_eq⟩ := Finset.card_eq_one.mp hR1
    have hr_not : r.val ∉ D.wires := by
      have : r ∈ Finset.univ \ RL := by rw [hr_eq]; simp
      simpa [RL] using (Finset.mem_sdiff.mp this).2
    have hc_not : n + c.val ∉ D.wires := by
      have : c ∈ Finset.univ \ RR := by rw [hc_eq]; simp
      simpa [RR] using (Finset.mem_sdiff.mp this).2
    have hallR : ∀ i : Fin n, i ≠ r → i.val ∈ D.wires := by
      intro i hir
      by_contra hni
      have : i ∈ Finset.univ \ RL := Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, by simp [RL, hni]⟩
      rw [hr_eq, Finset.mem_singleton] at this
      exact hir this
    have hallC : ∀ j : Fin m, j ≠ c → n + j.val ∈ D.wires := by
      intro j hjc
      by_contra hnj
      have : j ∈ Finset.univ \ RR := Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, by simp [RR, hnj]⟩
      rw [hc_eq, Finset.mem_singleton] at this
      exact hjc this
    have hlt_nm : ∀ w ∈ D.wires, w < n + m := by
      intro w hw
      rw [← hW_eq, Finset.mem_union] at hw
      rcases hw with h | h
      · rcases Finset.mem_image.mp h with ⟨i, _, rfl⟩; have := i.isLt; omega
      · rcases Finset.mem_image.mp h with ⟨j, _, rfl⟩; have := j.isLt; omega
    exact ⟨D, r, c, hr_not, hc_not, hallR, hallC, hlt_nm⟩
  · exfalso
    have h := (dep_card_lb_rect A hInjR hInjC C hrep R hDep).2.2
    omega

lemma decomp_eval_row_col {n m : ℕ} {A : Fin n → Fin m → Bool} {C : Circuit} (hrep : Represents A C)
    (D : Decomp (n + m) (fun x => C.eval x)) (i : Fin n) (j : Fin m) :
    let env : ℕ → Bool := fun w => decide (w = i.val ∨ w = n + j.val)
    let sh := D.sSh.eval env
    let neg := !D.tNeg.eval (fun o => match o with | none => sh | some w => env w)
    A i j = D.tPos.eval (fun s => match s with | .sh => sh | .neg => neg | .wire w => env w) := by
  have h1 := D.eval_eq (oneEach i j) (oneEach_len i j)
  rw [hrep i j] at h1
  rw [h1]
  have henv : ∀ w ∈ D.wires, (oneEach i j).getD w false = decide (w = i.val ∨ w = n + j.val) := by
    intro w _
    by_cases h1 : w < n
    · rw [oneEach_getD_left i j h1]
      rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]
      constructor; · intro e; exact Or.inl e.symm
      · rintro (e | e); exact e.symm; omega
    · by_cases h2 : w < n + m
      · have hwm : w - n < m := by omega
        have hw' : w = n + (w - n) := by omega
        rw [hw', oneEach_getD_right i j hwm]
        rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]
        constructor; · intro e; exact Or.inr (by omega)
        · rintro (e | e)
          · have := i.isLt; omega
          · omega
      · rw [List.getD_eq_default _ _ (by rw [oneEach_len]; omega)]
        have hi := i.isLt; have hj := j.isLt
        simp [show w ≠ i.val by omega, show w ≠ n + j.val by omega]
  have hsh : D.sSh.eval (fun w => (oneEach i j).getD w false) =
      D.sSh.eval (fun w => decide (w = i.val ∨ w = n + j.val)) :=
    D.sSh.eval_congr (fun w hw => henv w (Finset.mem_union_right _ hw))
  have hneg : D.tNeg.eval (fun o => match o with
      | none => D.sSh.eval (fun w => (oneEach i j).getD w false)
      | some w => (oneEach i j).getD w false) =
      D.tNeg.eval (fun o => match o with
      | none => D.sSh.eval (fun w => decide (w = i.val ∨ w = n + j.val))
      | some w => decide (w = i.val ∨ w = n + j.val)) := by
    apply D.tNeg.eval_congr; intro o ho; cases o with
    | none => exact hsh
    | some w => exact henv w (Finset.mem_union_left _ (Finset.mem_union_right _ (mem_optWires.mpr ho)))
  apply D.tPos.eval_congr; intro s hs; cases s with
  | sh => exact hsh
  | neg => dsimp only; rw [hneg]
  | wire w => exact henv w (Finset.mem_union_left _ (Finset.mem_union_left _ (mem_slotWires.mpr hs)))

def shValOf {n m : ℕ} {C : Circuit} (D : Decomp (n + m) (fun x => C.eval x)) (i : Fin n) (j : Fin m) : Bool :=
  D.sSh.eval (fun w => decide (w = i.val ∨ w = n + j.val))

def tnegValOf {n m : ℕ} {C : Circuit} (D : Decomp (n + m) (fun x => C.eval x)) (i : Fin n) (j : Fin m) : Bool :=
  D.tNeg.eval (fun o => match o with | none => shValOf D i j | some w => decide (w = i.val ∨ w = n + j.val))

lemma shValOf_row_mono {n m : ℕ} {C : Circuit} (D : Decomp (n + m) (fun x => C.eval x))
    {r : Fin n} (hr_U : r.val ∉ D.sSh.leaves) (i : Fin n) (j : Fin m)
    (h : shValOf D r j = true) : shValOf D i j = true := by
  apply D.sSh.eval_mono _ h
  intro w hw hw1
  simp only [decide_eq_true_eq] at hw1 ⊢
  rcases hw1 with rfl | rfl
  · exact absurd hw hr_U
  · exact Or.inr rfl

lemma shValOf_col_mono {n m : ℕ} {C : Circuit} (D : Decomp (n + m) (fun x => C.eval x))
    {c : Fin m} (hc_U : n + c.val ∉ D.sSh.leaves) (i : Fin n) (j : Fin m)
    (h : shValOf D i c = true) : shValOf D i j = true := by
  apply D.sSh.eval_mono _ h
  intro w hw hw1
  simp only [decide_eq_true_eq] at hw1 ⊢
  rcases hw1 with rfl | rfl
  · exact Or.inl rfl
  · exact absurd hw hc_U

lemma shValOf_notU_row {n m : ℕ} {C : Circuit} (D : Decomp (n + m) (fun x => C.eval x))
    {r : Fin n} (hr_U : r.val ∉ D.sSh.leaves) (i : Fin n) (j : Fin m)
    (hiU : i.val ∉ D.sSh.leaves) : shValOf D i j = shValOf D r j := by
  apply D.sSh.eval_congr; intro w hw
  have h1 : w ≠ i.val := fun e => hiU (e ▸ hw)
  have h2 : w ≠ r.val := fun e => hr_U (e ▸ hw)
  simp [h1, h2]

lemma shValOf_notU_col {n m : ℕ} {C : Circuit} (D : Decomp (n + m) (fun x => C.eval x))
    {c : Fin m} (hc_U : n + c.val ∉ D.sSh.leaves) (i : Fin n) (j : Fin m)
    (hjU : n + j.val ∉ D.sSh.leaves) : shValOf D i j = shValOf D i c := by
  apply D.sSh.eval_congr; intro w hw
  have h1 : w ≠ n + j.val := fun e => hjU (e ▸ hw)
  have h2 : w ≠ n + c.val := fun e => hc_U (e ▸ hw)
  simp [h1, h2]

lemma pos_row_le_of {n m : ℕ} {A : Fin n → Fin m → Bool} {C : Circuit} (hrep : Represents A C)
    (D : Decomp (n + m) (fun x => C.eval x)) {r : Fin n} (hr_not : r.val ∉ D.wires)
    (p : Fin n) (hpP : p.val ∈ slotWires D.tPos.leaves) (j : Fin m) (hrj : A r j = true) :
    A p j = true := by
  have hr_P : r.val ∉ slotWires D.tPos.leaves := fun hm => hr_not (Finset.mem_union_left _ (Finset.mem_union_left _ hm))
  have hr_H : r.val ∉ optWires D.tNeg.leaves := fun hm => hr_not (Finset.mem_union_left _ (Finset.mem_union_right _ hm))
  have hr_U : r.val ∉ D.sSh.leaves := fun hm => hr_not (Finset.mem_union_right _ hm)
  have hpH : p.val ∉ optWires D.tNeg.leaves := Finset.disjoint_left.mp D.disj_PH hpP
  have hpU : p.val ∉ D.sSh.leaves := Finset.disjoint_left.mp D.disj_PU hpP
  have hsh_eq : shValOf D p j = shValOf D r j := shValOf_notU_row D hr_U p j hpU
  have htneg_eq : tnegValOf D p j = tnegValOf D r j := by
    apply D.tNeg.eval_congr; intro o ho; cases o with
    | none => exact hsh_eq
    | some w =>
      have hwH : w ∈ optWires D.tNeg.leaves := mem_optWires.mpr ho
      have h1 : w ≠ p.val := fun e => hpH (e ▸ hwH)
      have h2 : w ≠ r.val := fun e => hr_H (e ▸ hwH)
      simp [h1, h2]
  rw [decomp_eval_row_col hrep D r j] at hrj
  rw [decomp_eval_row_col hrep D p j]
  apply D.tPos.eval_mono _ hrj
  intro s hs hst
  cases s with
  | sh => change shValOf D r j = true at hst; change shValOf D p j = true; rwa [hsh_eq]
  | neg => change (!tnegValOf D r j) = true at hst; change (!tnegValOf D p j) = true; rwa [htneg_eq]
  | wire w =>
    have hwP : w ∈ slotWires D.tPos.leaves := mem_slotWires.mpr hs
    simp only [decide_eq_true_eq] at hst ⊢
    rcases hst with rfl | rfl
    · exact absurd hwP hr_P
    · exact Or.inr rfl

lemma neg_row_le_of {n m : ℕ} {A : Fin n → Fin m → Bool} {C : Circuit} (hrep : Represents A C)
    (D : Decomp (n + m) (fun x => C.eval x)) {r : Fin n} (hr_not : r.val ∉ D.wires)
    (h : Fin n) (hhH : h.val ∈ optWires D.tNeg.leaves) (j : Fin m) (hhj : A h j = true) :
    A r j = true := by
  have hr_H : r.val ∉ optWires D.tNeg.leaves := fun hm => hr_not (Finset.mem_union_left _ (Finset.mem_union_right _ hm))
  have hr_U : r.val ∉ D.sSh.leaves := fun hm => hr_not (Finset.mem_union_right _ hm)
  have hhP : h.val ∉ slotWires D.tPos.leaves := Finset.disjoint_right.mp D.disj_PH hhH
  have hhU : h.val ∉ D.sSh.leaves := Finset.disjoint_left.mp D.disj_HU hhH
  have hsh_eq : shValOf D h j = shValOf D r j := shValOf_notU_row D hr_U h j hhU
  have htneg_le : tnegValOf D r j = true → tnegValOf D h j = true := by
    intro hrt
    apply D.tNeg.eval_mono _ hrt
    intro o ho hot
    cases o with
    | none => rwa [hsh_eq]
    | some w =>
      have hwH : w ∈ optWires D.tNeg.leaves := mem_optWires.mpr ho
      simp only [decide_eq_true_eq] at hot ⊢
      rcases hot with rfl | rfl
      · exact absurd hwH hr_H
      · exact Or.inr rfl
  rw [decomp_eval_row_col hrep D h j] at hhj
  rw [decomp_eval_row_col hrep D r j]
  apply D.tPos.eval_mono _ hhj
  intro s hs hst
  cases s with
  | sh => change shValOf D h j = true at hst; change shValOf D r j = true; rwa [← hsh_eq]
  | neg =>
    change (!tnegValOf D h j) = true at hst
    change (!tnegValOf D r j) = true
    simp only [Bool.not_eq_true'] at hst ⊢
    by_contra hrt
    have := htneg_le (Bool.eq_true_of_not_eq_false hrt)
    rw [hst] at this; cases this
  | wire w =>
    have hwP : w ∈ slotWires D.tPos.leaves := mem_slotWires.mpr hs
    simp only [decide_eq_true_eq] at hst ⊢
    rcases hst with rfl | rfl
    · exact absurd hwP hhP
    · exact Or.inr rfl

lemma uniq_sh_col_of {n m : ℕ} {A : Fin n → Fin m → Bool} {C : Circuit}
    (hInjC : Function.Injective (fun j i => A i j)) (hrep : Represents A C)
    (D : Decomp (n + m) (fun x => C.eval x)) {r : Fin n} (hr_not : r.val ∉ D.wires)
    (j1 j2 : Fin m) (h1 : shValOf D r j1 = true) (h2 : shValOf D r j2 = true) : j1 = j2 := by
  have hr_U : r.val ∉ D.sSh.leaves := fun hm => hr_not (Finset.mem_union_right _ hm)
  have hj1U : n + j1.val ∈ D.sSh.leaves := by
    by_contra hnu
    have hcongr : shValOf D r j1 = D.sSh.eval (fun _ => false) :=
      D.sSh.eval_congr (fun w hw => by
        have ha : w ≠ r.val := fun e => hr_U (e ▸ hw)
        have hb : w ≠ n + j1.val := fun e => hnu (e ▸ hw)
        simp [ha, hb])
    rw [MTree.eval_false] at hcongr; rw [h1] at hcongr; cases hcongr
  have hj2U : n + j2.val ∈ D.sSh.leaves := by
    by_contra hnu
    have hcongr : shValOf D r j2 = D.sSh.eval (fun _ => false) :=
      D.sSh.eval_congr (fun w hw => by
        have ha : w ≠ r.val := fun e => hr_U (e ▸ hw)
        have hb : w ≠ n + j2.val := fun e => hnu (e ▸ hw)
        simp [ha, hb])
    rw [MTree.eval_false] at hcongr; rw [h2] at hcongr; cases hcongr
  have hj1P : n + j1.val ∉ slotWires D.tPos.leaves := Finset.disjoint_right.mp D.disj_PU hj1U
  have hj2P : n + j2.val ∉ slotWires D.tPos.leaves := Finset.disjoint_right.mp D.disj_PU hj2U
  have hj1H : n + j1.val ∉ optWires D.tNeg.leaves := Finset.disjoint_right.mp D.disj_HU hj1U
  have hj2H : n + j2.val ∉ optWires D.tNeg.leaves := Finset.disjoint_right.mp D.disj_HU hj2U
  apply hInjC; funext i; dsimp only
  have hsh_eq : shValOf D i j1 = shValOf D i j2 := by
    rw [shValOf_row_mono D hr_U i j1 h1, shValOf_row_mono D hr_U i j2 h2]
  have htneg_eq : tnegValOf D i j1 = tnegValOf D i j2 := by
    apply D.tNeg.eval_congr; intro o ho; cases o with
    | none => exact hsh_eq
    | some w =>
      have hwH : w ∈ optWires D.tNeg.leaves := mem_optWires.mpr ho
      have ha : w ≠ n + j1.val := fun e => hj1H (e ▸ hwH)
      have hb : w ≠ n + j2.val := fun e => hj2H (e ▸ hwH)
      simp [ha, hb]
  rw [decomp_eval_row_col hrep D i j1, decomp_eval_row_col hrep D i j2]
  apply D.tPos.eval_congr; intro s hs; cases s with
  | sh => exact hsh_eq
  | neg => dsimp only; exact congrArg Bool.not htneg_eq
  | wire w =>
    have hwP : w ∈ slotWires D.tPos.leaves := mem_slotWires.mpr hs
    have ha : w ≠ n + j1.val := fun e => hj1P (e ▸ hwP)
    have hb : w ≠ n + j2.val := fun e => hj2P (e ▸ hwP)
    simp [ha, hb]

lemma uniq_sh_row_of {n m : ℕ} {A : Fin n → Fin m → Bool} {C : Circuit}
    (hInjR : Function.Injective A) (hrep : Represents A C)
    (D : Decomp (n + m) (fun x => C.eval x)) {c : Fin m} (hc_not : n + c.val ∉ D.wires)
    (i1 i2 : Fin n) (h1 : shValOf D i1 c = true) (h2 : shValOf D i2 c = true) : i1 = i2 := by
  have hc_U : n + c.val ∉ D.sSh.leaves := fun hm => hc_not (Finset.mem_union_right _ hm)
  have hi1U : i1.val ∈ D.sSh.leaves := by
    by_contra hnu
    have hcongr : shValOf D i1 c = D.sSh.eval (fun _ => false) :=
      D.sSh.eval_congr (fun w hw => by
        have ha : w ≠ i1.val := fun e => hnu (e ▸ hw)
        have hb : w ≠ n + c.val := fun e => hc_U (e ▸ hw)
        simp [ha, hb])
    rw [MTree.eval_false] at hcongr; rw [h1] at hcongr; cases hcongr
  have hi2U : i2.val ∈ D.sSh.leaves := by
    by_contra hnu
    have hcongr : shValOf D i2 c = D.sSh.eval (fun _ => false) :=
      D.sSh.eval_congr (fun w hw => by
        have ha : w ≠ i2.val := fun e => hnu (e ▸ hw)
        have hb : w ≠ n + c.val := fun e => hc_U (e ▸ hw)
        simp [ha, hb])
    rw [MTree.eval_false] at hcongr; rw [h2] at hcongr; cases hcongr
  have hi1P : i1.val ∉ slotWires D.tPos.leaves := Finset.disjoint_right.mp D.disj_PU hi1U
  have hi2P : i2.val ∉ slotWires D.tPos.leaves := Finset.disjoint_right.mp D.disj_PU hi2U
  have hi1H : i1.val ∉ optWires D.tNeg.leaves := Finset.disjoint_right.mp D.disj_HU hi1U
  have hi2H : i2.val ∉ optWires D.tNeg.leaves := Finset.disjoint_right.mp D.disj_HU hi2U
  apply hInjR; funext j
  have hsh_eq : shValOf D i1 j = shValOf D i2 j := by
    rw [shValOf_col_mono D hc_U i1 j h1, shValOf_col_mono D hc_U i2 j h2]
  have htneg_eq : tnegValOf D i1 j = tnegValOf D i2 j := by
    apply D.tNeg.eval_congr; intro o ho; cases o with
    | none => exact hsh_eq
    | some w =>
      have hwH : w ∈ optWires D.tNeg.leaves := mem_optWires.mpr ho
      have ha : w ≠ i1.val := fun e => hi1H (e ▸ hwH)
      have hb : w ≠ i2.val := fun e => hi2H (e ▸ hwH)
      simp [ha, hb]
  rw [decomp_eval_row_col hrep D i1 j, decomp_eval_row_col hrep D i2 j]
  apply D.tPos.eval_congr; intro s hs; cases s with
  | sh => exact hsh_eq
  | neg => dsimp only; exact congrArg Bool.not htneg_eq
  | wire w =>
    have hwP : w ∈ slotWires D.tPos.leaves := mem_slotWires.mpr hs
    have ha : w ≠ i1.val := fun e => hi1P (e ▸ hwP)
    have hb : w ≠ i2.val := fun e => hi2P (e ▸ hwP)
    simp [ha, hb]

lemma tneg_row_false_of {n m : ℕ} {A : Fin n → Fin m → Bool} {C : Circuit}
    (hRowInc : ∀ i : Fin n, ∃ k : Fin n, ¬ ((∀ j, A i j = true → A k j = true) ∨ (∀ j, A k j = true → A i j = true)))
    (hrep : Represents A C) (D : Decomp (n + m) (fun x => C.eval x))
    {r : Fin n} {c : Fin m} (hr_not : r.val ∉ D.wires) (hc_not : n + c.val ∉ D.wires)
    (h : Fin n) (hhH : h.val ∈ optWires D.tNeg.leaves) : tnegValOf D h c = false := by
  have hr_U : r.val ∉ D.sSh.leaves := fun hm => hr_not (Finset.mem_union_right _ hm)
  have hc_H : n + c.val ∉ optWires D.tNeg.leaves := fun hm => hc_not (Finset.mem_union_left _ (Finset.mem_union_right _ hm))
  have hc_U : n + c.val ∉ D.sSh.leaves := fun hm => hc_not (Finset.mem_union_right _ hm)
  by_contra hne
  have hht : tnegValOf D h c = true := Bool.eq_true_of_not_eq_false hne
  have hhP : h.val ∉ slotWires D.tPos.leaves := Finset.disjoint_right.mp D.disj_PH hhH
  have hhU : h.val ∉ D.sSh.leaves := Finset.disjoint_left.mp D.disj_HU hhH
  have hsh_hc : shValOf D h c = false := by
    have hcongr : shValOf D h c = D.sSh.eval (fun _ => false) :=
      D.sSh.eval_congr (fun w hw => by
        have ha : w ≠ h.val := fun e => hhU (e ▸ hw)
        have hb : w ≠ n + c.val := fun e => hc_U (e ▸ hw)
        simp [ha, hb])
    rw [hcongr, MTree.eval_false]
  have htneg_all : ∀ j : Fin m, tnegValOf D h j = true := by
    intro j
    apply D.tNeg.eval_mono _ hht
    intro o ho hot
    cases o with
    | none => rw [hsh_hc] at hot; cases hot
    | some w =>
      have hwH : w ∈ optWires D.tNeg.leaves := mem_optWires.mpr ho
      simp only [decide_eq_true_eq] at hot ⊢
      rcases hot with rfl | rfl
      · exact Or.inl rfl
      · exact absurd hwH hc_H
  have hle_all : ∀ k : Fin n, ∀ j : Fin m, A h j = true → A k j = true := by
    intro k j hhj
    rw [decomp_eval_row_col hrep D h j] at hhj
    rw [decomp_eval_row_col hrep D k j]
    apply D.tPos.eval_mono _ hhj
    intro s hs hst
    cases s with
    | sh =>
      change shValOf D h j = true at hst
      change shValOf D k j = true
      rw [shValOf_notU_row D hr_U h j hhU] at hst
      exact shValOf_row_mono D hr_U k j hst
    | neg =>
      change (!tnegValOf D h j) = true at hst
      rw [htneg_all j] at hst; simp at hst
    | wire w =>
      have hwP : w ∈ slotWires D.tPos.leaves := mem_slotWires.mpr hs
      simp only [decide_eq_true_eq] at hst ⊢
      rcases hst with rfl | rfl
      · exact absurd hwP hhP
      · exact Or.inr rfl
  obtain ⟨k, hk⟩ := hRowInc h
  exact hk (Or.inl (hle_all k))

lemma tneg_col_false_of {n m : ℕ} {A : Fin n → Fin m → Bool} {C : Circuit}
    (hColInc : ∀ j : Fin m, ∃ l : Fin m, ¬ ((∀ i, A i j = true → A i l = true) ∨ (∀ i, A i l = true → A i j = true)))
    (hrep : Represents A C) (D : Decomp (n + m) (fun x => C.eval x))
    {r : Fin n} {c : Fin m} (hr_not : r.val ∉ D.wires) (hc_not : n + c.val ∉ D.wires)
    (j : Fin m) (hjH : n + j.val ∈ optWires D.tNeg.leaves) : tnegValOf D r j = false := by
  have hr_H : r.val ∉ optWires D.tNeg.leaves := fun hm => hr_not (Finset.mem_union_left _ (Finset.mem_union_right _ hm))
  have hr_U : r.val ∉ D.sSh.leaves := fun hm => hr_not (Finset.mem_union_right _ hm)
  have hc_U : n + c.val ∉ D.sSh.leaves := fun hm => hc_not (Finset.mem_union_right _ hm)
  by_contra hne
  have hjt : tnegValOf D r j = true := Bool.eq_true_of_not_eq_false hne
  have hjP : n + j.val ∉ slotWires D.tPos.leaves := Finset.disjoint_right.mp D.disj_PH hjH
  have hjU : n + j.val ∉ D.sSh.leaves := Finset.disjoint_left.mp D.disj_HU hjH
  have hsh_rj : shValOf D r j = false := by
    have hcongr : shValOf D r j = D.sSh.eval (fun _ => false) :=
      D.sSh.eval_congr (fun w hw => by
        have ha : w ≠ r.val := fun e => hr_U (e ▸ hw)
        have hb : w ≠ n + j.val := fun e => hjU (e ▸ hw)
        simp [ha, hb])
    rw [hcongr, MTree.eval_false]
  have htneg_all : ∀ i : Fin n, tnegValOf D i j = true := by
    intro i
    apply D.tNeg.eval_mono _ hjt
    intro o ho hot
    cases o with
    | none => rw [hsh_rj] at hot; cases hot
    | some w =>
      have hwH : w ∈ optWires D.tNeg.leaves := mem_optWires.mpr ho
      simp only [decide_eq_true_eq] at hot ⊢
      rcases hot with rfl | rfl
      · exact absurd hwH hr_H
      · exact Or.inr rfl
  have hle_all : ∀ l : Fin m, ∀ i : Fin n, A i j = true → A i l = true := by
    intro l i hij
    rw [decomp_eval_row_col hrep D i j] at hij
    rw [decomp_eval_row_col hrep D i l]
    apply D.tPos.eval_mono _ hij
    intro s hs hst
    cases s with
    | sh =>
      change shValOf D i j = true at hst
      change shValOf D i l = true
      rw [shValOf_notU_col D hc_U i j hjU] at hst
      exact shValOf_col_mono D hc_U i l hst
    | neg =>
      change (!tnegValOf D i j) = true at hst
      rw [htneg_all i] at hst; simp at hst
    | wire w =>
      have hwP : w ∈ slotWires D.tPos.leaves := mem_slotWires.mpr hs
      simp only [decide_eq_true_eq] at hst ⊢
      rcases hst with rfl | rfl
      · exact Or.inl rfl
      · exact absurd hwP hjP
  obtain ⟨l, hl⟩ := hColInc j
  exact hl (Or.inl (hle_all l))

lemma neg_alone_false_of {n m : ℕ} {A : Fin n → Fin m → Bool} {C : Circuit}
    (hInjC : Function.Injective (fun j i => A i j))
    (hRowInc : ∀ i : Fin n, ∃ k : Fin n, ¬ ((∀ j, A i j = true → A k j = true) ∨ (∀ j, A k j = true → A i j = true)))
    (hColInc : ∀ j : Fin m, ∃ l : Fin m, ¬ ((∀ i, A i j = true → A i l = true) ∨ (∀ i, A i l = true → A i j = true)))
    (hrep : Represents A C) (D : Decomp (n + m) (fun x => C.eval x))
    {r : Fin n} {c : Fin m} (hr_not : r.val ∉ D.wires) (hc_not : n + c.val ∉ D.wires) :
    D.tPos.eval (fun s => decide (s = Slot.neg)) = false := by
  have hr_P : r.val ∉ slotWires D.tPos.leaves := fun hm => hr_not (Finset.mem_union_left _ (Finset.mem_union_left _ hm))
  have hr_H : r.val ∉ optWires D.tNeg.leaves := fun hm => hr_not (Finset.mem_union_left _ (Finset.mem_union_right _ hm))
  have hr_U : r.val ∉ D.sSh.leaves := fun hm => hr_not (Finset.mem_union_right _ hm)
  by_contra hne
  have hpos_neg : D.tPos.eval (fun s => decide (s = Slot.neg)) = true := Bool.eq_true_of_not_eq_false hne
  have hAr_of_sh0 : ∀ j : Fin m, shValOf D r j = false → A r j = true := by
    intro j hsh0
    have htneg0 : tnegValOf D r j = false := by
      by_cases hjH : n + j.val ∈ optWires D.tNeg.leaves
      · exact tneg_col_false_of hColInc hrep D hr_not hc_not j hjH
      · have hcongr : tnegValOf D r j = D.tNeg.eval (fun _ => false) := by
          apply D.tNeg.eval_congr; intro o ho; cases o with
          | none => exact hsh0
          | some w =>
            have hwH : w ∈ optWires D.tNeg.leaves := mem_optWires.mpr ho
            have ha : w ≠ r.val := fun e => hr_H (e ▸ hwH)
            have hb : w ≠ n + j.val := fun e => hjH (e ▸ hwH)
            simp [ha, hb]
        rw [hcongr, MTree.eval_false]
    rw [decomp_eval_row_col hrep D r j]
    apply D.tPos.eval_mono _ hpos_neg
    intro s _ hs
    have : s = Slot.neg := of_decide_eq_true hs
    subst this
    change (!tnegValOf D r j) = true
    simp [htneg0]
  obtain ⟨k, hk_inc⟩ := hRowInc r
  push Not at hk_inc
  obtain ⟨⟨_, _, _⟩, ⟨v0, hkv0, hrv0_n⟩⟩ := hk_inc
  have hrv0 : A r v0 = false := Bool.eq_false_iff.mpr hrv0_n
  have hsh_v0 : shValOf D r v0 = true := by
    by_contra h0
    have := hAr_of_sh0 v0 (Bool.eq_false_iff.mpr h0)
    rw [hrv0] at this; cases this
  have hAr_other : ∀ j : Fin m, j ≠ v0 → A r j = true := by
    intro j hjv0
    apply hAr_of_sh0 j
    by_contra h1
    exact hjv0 (uniq_sh_col_of hInjC hrep D hr_not j v0 (Bool.eq_true_of_not_eq_false h1) hsh_v0)
  have hk_notP : k.val ∉ slotWires D.tPos.leaves := by
    intro hkP
    have hall_k : ∀ j : Fin m, A k j = true := by
      intro j
      by_cases hj : j = v0
      · subst hj; exact hkv0
      · exact pos_row_le_of hrep D hr_not k hkP j (hAr_other j hj)
    obtain ⟨k2, hk2⟩ := hRowInc k
    exact hk2 (Or.inr fun j _ => hall_k j)
  have hk_notH : k.val ∉ optWires D.tNeg.leaves := by
    intro hkH
    have := neg_row_le_of hrep D hr_not k hkH v0 hkv0
    rw [hrv0] at this; cases this
  have hsh_kv0 : shValOf D k v0 = shValOf D r v0 := by
    rw [shValOf_row_mono D hr_U k v0 hsh_v0, hsh_v0]
  have htneg_kv0 : tnegValOf D k v0 = tnegValOf D r v0 := by
    apply D.tNeg.eval_congr; intro o ho; cases o with
    | none => exact hsh_kv0
    | some w =>
      have hwH : w ∈ optWires D.tNeg.leaves := mem_optWires.mpr ho
      have ha : w ≠ k.val := fun e => hk_notH (e ▸ hwH)
      have hb : w ≠ r.val := fun e => hr_H (e ▸ hwH)
      simp [ha, hb]
  have hAkv0_eq : A k v0 = A r v0 := by
    rw [decomp_eval_row_col hrep D k v0, decomp_eval_row_col hrep D r v0]
    apply D.tPos.eval_congr; intro s hs; cases s with
    | sh => exact hsh_kv0
    | neg => dsimp only; exact congrArg Bool.not htneg_kv0
    | wire w =>
      have hwP : w ∈ slotWires D.tPos.leaves := mem_slotWires.mpr hs
      have ha : w ≠ k.val := fun e => hk_notP (e ▸ hwP)
      have hb : w ≠ r.val := fun e => hr_P (e ▸ hwP)
      simp [ha, hb]
  rw [hkv0, hrv0] at hAkv0_eq; cases hAkv0_eq

lemma decomp_H_no_row {n m : ℕ} {A : Fin n → Fin m → Bool} {C : Circuit}
    (hInjR : Function.Injective A) (hInjC : Function.Injective (fun j i => A i j))
    (hRowInc : ∀ i : Fin n, ∃ k : Fin n, ¬ ((∀ j, A i j = true → A k j = true) ∨ (∀ j, A k j = true → A i j = true)))
    (hColInc : ∀ j : Fin m, ∃ l : Fin m, ¬ ((∀ i, A i j = true → A i l = true) ∨ (∀ i, A i l = true → A i j = true)))
    (hrep : Represents A C) (D : Decomp (n + m) (fun x => C.eval x))
    {r : Fin n} {c : Fin m} (hr_not : r.val ∉ D.wires) (hc_not : n + c.val ∉ D.wires) :
    ∀ h : Fin n, h.val ∉ optWires D.tNeg.leaves := by
  have hr_P : r.val ∉ slotWires D.tPos.leaves := fun hm => hr_not (Finset.mem_union_left _ (Finset.mem_union_left _ hm))
  have hr_H : r.val ∉ optWires D.tNeg.leaves := fun hm => hr_not (Finset.mem_union_left _ (Finset.mem_union_right _ hm))
  have hr_U : r.val ∉ D.sSh.leaves := fun hm => hr_not (Finset.mem_union_right _ hm)
  have hc_H : n + c.val ∉ optWires D.tNeg.leaves := fun hm => hc_not (Finset.mem_union_left _ (Finset.mem_union_right _ hm))
  have hc_U : n + c.val ∉ D.sSh.leaves := fun hm => hc_not (Finset.mem_union_right _ hm)
  have hneg_alone_false := neg_alone_false_of hInjC hRowInc hColInc hrep D hr_not hc_not
  intro h hhH
  have hhP : h.val ∉ slotWires D.tPos.leaves := Finset.disjoint_right.mp D.disj_PH hhH
  have hhU : h.val ∉ D.sSh.leaves := Finset.disjoint_left.mp D.disj_HU hhH
  have hhr : h ≠ r := fun e => hr_H (e ▸ hhH)
  have hneq : A h ≠ A r := fun e => hhr (hInjR e)
  have hex1 : ∃ j' : Fin m, A h j' ≠ A r j' := by
    by_contra hall; push Not at hall; exact hneq (funext hall)
  obtain ⟨j', hj'⟩ := hex1
  have hAr_j' : A r j' = true := by
    cases h1 : A r j' with
    | true => rfl
    | false =>
      exfalso
      cases h2 : A h j' with
      | false => exact hj' (h2.trans h1.symm)
      | true => have := neg_row_le_of hrep D hr_not h hhH j' h2; rw [h1] at this; cases this
  have hsh_j'_eq : shValOf D h j' = shValOf D r j' := shValOf_notU_row D hr_U h j' hhU
  have htneg_j' : tnegValOf D r j' = false ∧ tnegValOf D h j' = true := by
    by_cases h1 : tnegValOf D r j' = tnegValOf D h j'
    · exfalso
      have heqA : A h j' = A r j' := by
        rw [decomp_eval_row_col hrep D h j', decomp_eval_row_col hrep D r j']
        apply D.tPos.eval_congr; intro s hs; cases s with
        | sh => exact hsh_j'_eq
        | neg => dsimp only; exact congrArg Bool.not h1.symm
        | wire w =>
          have hwP : w ∈ slotWires D.tPos.leaves := mem_slotWires.mpr hs
          have ha : w ≠ h.val := fun e => hhP (e ▸ hwP)
          have hb : w ≠ r.val := fun e => hr_P (e ▸ hwP)
          simp [ha, hb]
      exact hj' heqA
    · have hle : tnegValOf D r j' = true → tnegValOf D h j' = true := by
        intro hrt; apply D.tNeg.eval_mono _ hrt; intro o ho hot; cases o with
        | none => rwa [hsh_j'_eq]
        | some w =>
          have hwH : w ∈ optWires D.tNeg.leaves := mem_optWires.mpr ho
          simp only [decide_eq_true_eq] at hot ⊢
          rcases hot with rfl | rfl; exact absurd hwH hr_H; exact Or.inr rfl
      cases ha : tnegValOf D r j' <;> cases hb : tnegValOf D h j'
      · exact absurd (ha.trans hb.symm) h1
      · exact ⟨rfl, rfl⟩
      · exact absurd (hle ha) (by rw [hb]; decide)
      · exact absurd (ha.trans hb.symm) h1
  have hj'_notP : n + j'.val ∉ slotWires D.tPos.leaves := by
    intro hj'P
    have hj'H : n + j'.val ∉ optWires D.tNeg.leaves := Finset.disjoint_left.mp D.disj_PH hj'P
    have hj'U : n + j'.val ∉ D.sSh.leaves := Finset.disjoint_left.mp D.disj_PU hj'P
    have hsh_eq : shValOf D h j' = shValOf D h c := shValOf_notU_col D hc_U h j' hj'U
    have htneg_eq : tnegValOf D h j' = tnegValOf D h c := by
      apply D.tNeg.eval_congr; intro o ho; cases o with
      | none => exact hsh_eq
      | some w =>
        have hwH : w ∈ optWires D.tNeg.leaves := mem_optWires.mpr ho
        have ha : w ≠ n + j'.val := fun e => hj'H (e ▸ hwH)
        have hb : w ≠ n + c.val := fun e => hc_H (e ▸ hwH)
        simp [ha, hb]
    rw [tneg_row_false_of hRowInc hrep D hr_not hc_not h hhH] at htneg_eq
    rw [htneg_j'.2] at htneg_eq; cases htneg_eq
  have hsh_j'_true : shValOf D r j' = true := by
    by_contra h0
    have hsh0 : shValOf D r j' = false := Bool.eq_false_iff.mpr h0
    have hcongr : A r j' = D.tPos.eval (fun s => decide (s = Slot.neg)) := by
      rw [decomp_eval_row_col hrep D r j']
      apply D.tPos.eval_congr; intro s hs; cases s with
      | sh => exact hsh0
      | neg => change (!tnegValOf D r j') = true; simp [htneg_j'.1]
      | wire w =>
        have hwP : w ∈ slotWires D.tPos.leaves := mem_slotWires.mpr hs
        have ha : w ≠ r.val := fun e => hr_P (e ▸ hwP)
        have hb : w ≠ n + j'.val := fun e => hj'_notP (e ▸ hwP)
        simp [ha, hb]
    rw [hAr_j', hneg_alone_false] at hcongr; cases hcongr
  have htneg_sh_false : D.tNeg.eval (fun o => decide (o = none)) = false := by
    have hj'U : n + j'.val ∈ D.sSh.leaves := by
      by_contra hnu
      have hcongr : shValOf D r j' = D.sSh.eval (fun _ => false) :=
        D.sSh.eval_congr (fun w hw => by
          have ha : w ≠ r.val := fun e => hr_U (e ▸ hw)
          have hb : w ≠ n + j'.val := fun e => hnu (e ▸ hw)
          simp [ha, hb])
      rw [MTree.eval_false] at hcongr; rw [hsh_j'_true] at hcongr; cases hcongr
    have hj'H : n + j'.val ∉ optWires D.tNeg.leaves := Finset.disjoint_right.mp D.disj_HU hj'U
    have hcongr : tnegValOf D r j' = D.tNeg.eval (fun o => decide (o = none)) := by
      apply D.tNeg.eval_congr; intro o ho; cases o with
      | none => simp [hsh_j'_true]
      | some w =>
        have hwH : w ∈ optWires D.tNeg.leaves := mem_optWires.mpr ho
        have ha : w ≠ r.val := fun e => hr_H (e ▸ hwH)
        have hb : w ≠ n + j'.val := fun e => hj'H (e ▸ hwH)
        simp [ha, hb]
    rw [← hcongr, htneg_j'.1]
  obtain ⟨k, hk_inc⟩ := hRowInc h
  push Not at hk_inc
  obtain ⟨⟨j0, hhj0, hkj0_n⟩, _⟩ := hk_inc
  have hkj0 : A k j0 = false := Bool.eq_false_iff.mpr hkj0_n
  have htneg_j0 : tnegValOf D h j0 = false ∧ tnegValOf D k j0 = true := by
    by_contra hbad
    have hneg_le : (!tnegValOf D h j0) = true → (!tnegValOf D k j0) = true := by
      cases ha : tnegValOf D h j0 <;> cases hb : tnegValOf D k j0
      · simp
      · exact absurd ⟨ha, hb⟩ hbad
      · simp
      · simp
    have hkt : A k j0 = true := by
      rw [decomp_eval_row_col hrep D h j0] at hhj0
      rw [decomp_eval_row_col hrep D k j0]
      apply D.tPos.eval_mono _ hhj0
      intro s hs hst; cases s with
      | sh =>
        change shValOf D h j0 = true at hst
        change shValOf D k j0 = true
        rw [shValOf_notU_row D hr_U h j0 hhU] at hst
        exact shValOf_row_mono D hr_U k j0 hst
      | neg => exact hneg_le hst
      | wire w =>
        have hwP : w ∈ slotWires D.tPos.leaves := mem_slotWires.mpr hs
        simp only [decide_eq_true_eq] at hst ⊢
        rcases hst with rfl | rfl; exact absurd hwP hhP; exact Or.inr rfl
    rw [hkj0] at hkt; cases hkt
  have hj0_notP : n + j0.val ∉ slotWires D.tPos.leaves := by
    intro hj0P
    have hj0H : n + j0.val ∉ optWires D.tNeg.leaves := Finset.disjoint_left.mp D.disj_PH hj0P
    have hj0U : n + j0.val ∉ D.sSh.leaves := Finset.disjoint_left.mp D.disj_PU hj0P
    by_cases hkH : k.val ∈ optWires D.tNeg.leaves
    · have hsh_eq : shValOf D k j0 = shValOf D k c := shValOf_notU_col D hc_U k j0 hj0U
      have htneg_eq : tnegValOf D k j0 = tnegValOf D k c := by
        apply D.tNeg.eval_congr; intro o ho; cases o with
        | none => exact hsh_eq
        | some w =>
          have hwH : w ∈ optWires D.tNeg.leaves := mem_optWires.mpr ho
          have ha : w ≠ n + j0.val := fun e => hj0H (e ▸ hwH)
          have hb : w ≠ n + c.val := fun e => hc_H (e ▸ hwH)
          simp [ha, hb]
      rw [tneg_row_false_of hRowInc hrep D hr_not hc_not k hkH] at htneg_eq
      rw [htneg_j0.2] at htneg_eq; cases htneg_eq
    · have hkt : D.tNeg.eval (fun o => decide (o = none)) = true := by
        apply D.tNeg.eval_mono _ htneg_j0.2
        intro o ho hot; cases o with
        | none => simp
        | some w =>
          have hwH : w ∈ optWires D.tNeg.leaves := mem_optWires.mpr ho
          simp only [decide_eq_true_eq] at hot
          rcases hot with rfl | rfl
          · exact absurd hwH hkH
          · exact absurd hwH hj0H
      rw [htneg_sh_false] at hkt; cases hkt
  have hsh_j0_true : shValOf D r j0 = true := by
    by_contra h0
    have hsh0 : shValOf D r j0 = false := Bool.eq_false_iff.mpr h0
    have hsh_h0 : shValOf D h j0 = false := by rw [shValOf_notU_row D hr_U h j0 hhU, hsh0]
    have hcongr : A h j0 = D.tPos.eval (fun s => decide (s = Slot.neg)) := by
      rw [decomp_eval_row_col hrep D h j0]
      apply D.tPos.eval_congr; intro s hs; cases s with
      | sh => exact hsh_h0
      | neg => change (!tnegValOf D h j0) = true; simp [htneg_j0.1]
      | wire w =>
        have hwP : w ∈ slotWires D.tPos.leaves := mem_slotWires.mpr hs
        have ha : w ≠ h.val := fun e => hhP (e ▸ hwP)
        have hb : w ≠ n + j0.val := fun e => hj0_notP (e ▸ hwP)
        simp [ha, hb]
    rw [hhj0, hneg_alone_false] at hcongr; cases hcongr
  have hj_eq : j0 = j' := uniq_sh_col_of hInjC hrep D hr_not j0 j' hsh_j0_true hsh_j'_true
  subst hj_eq
  rw [htneg_j0.1] at htneg_j'
  cases htneg_j'.2

lemma decomp_H_no_col {n m : ℕ} {A : Fin n → Fin m → Bool} {C : Circuit}
    (hInjR : Function.Injective A) (hInjC : Function.Injective (fun j i => A i j))
    (hRowInc : ∀ i : Fin n, ∃ k : Fin n, ¬ ((∀ j, A i j = true → A k j = true) ∨ (∀ j, A k j = true → A i j = true)))
    (hColInc : ∀ j : Fin m, ∃ l : Fin m, ¬ ((∀ i, A i j = true → A i l = true) ∨ (∀ i, A i l = true → A i j = true)))
    (hrep : Represents A C) (D : Decomp (n + m) (fun x => C.eval x))
    {r : Fin n} {c : Fin m} (hr_not : r.val ∉ D.wires) (hc_not : n + c.val ∉ D.wires) :
    ∀ j : Fin m, n + j.val ∉ optWires D.tNeg.leaves := by
  have hr_H : r.val ∉ optWires D.tNeg.leaves := fun hm => hr_not (Finset.mem_union_left _ (Finset.mem_union_right _ hm))
  have hr_U : r.val ∉ D.sSh.leaves := fun hm => hr_not (Finset.mem_union_right _ hm)
  have hc_P : n + c.val ∉ slotWires D.tPos.leaves := fun hm => hc_not (Finset.mem_union_left _ (Finset.mem_union_left _ hm))
  have hc_H : n + c.val ∉ optWires D.tNeg.leaves := fun hm => hc_not (Finset.mem_union_left _ (Finset.mem_union_right _ hm))
  have hc_U : n + c.val ∉ D.sSh.leaves := fun hm => hc_not (Finset.mem_union_right _ hm)
  have hneg_alone_false := neg_alone_false_of hInjC hRowInc hColInc hrep D hr_not hc_not
  have hH_no_row := decomp_H_no_row hInjR hInjC hRowInc hColInc hrep D hr_not hc_not
  intro j hjH
  have hjP : n + j.val ∉ slotWires D.tPos.leaves := Finset.disjoint_right.mp D.disj_PH hjH
  have hjU : n + j.val ∉ D.sSh.leaves := Finset.disjoint_left.mp D.disj_HU hjH
  have hjc : j ≠ c := fun e => hc_H (e ▸ hjH)
  have hneq : (fun i => A i j) ≠ (fun i => A i c) := fun e => hjc (hInjC e)
  have hex1 : ∃ i' : Fin n, A i' j ≠ A i' c := by
    by_contra hall; push Not at hall; exact hneq (funext hall)
  obtain ⟨i', hi'⟩ := hex1
  have hneg_col_le : ∀ i : Fin n, A i j = true → A i c = true := by
    intro i hij
    have hsh_eq : shValOf D i j = shValOf D i c := shValOf_notU_col D hc_U i j hjU
    have htneg_le : tnegValOf D i c = true → tnegValOf D i j = true := by
      intro hct; apply D.tNeg.eval_mono _ hct; intro o ho hot; cases o with
      | none => rwa [hsh_eq]
      | some w =>
        have hwH : w ∈ optWires D.tNeg.leaves := mem_optWires.mpr ho
        simp only [decide_eq_true_eq] at hot ⊢
        rcases hot with rfl | rfl; exact Or.inl rfl; exact absurd hwH hc_H
    rw [decomp_eval_row_col hrep D i j] at hij
    rw [decomp_eval_row_col hrep D i c]
    apply D.tPos.eval_mono _ hij; intro s hs hst; cases s with
    | sh => change shValOf D i j = true at hst; change shValOf D i c = true; rwa [← hsh_eq]
    | neg =>
      change (!tnegValOf D i j) = true at hst
      change (!tnegValOf D i c) = true
      simp only [Bool.not_eq_true'] at hst ⊢
      by_contra hct; have := htneg_le (Bool.eq_true_of_not_eq_false hct); rw [hst] at this; cases this
    | wire w =>
      have hwP : w ∈ slotWires D.tPos.leaves := mem_slotWires.mpr hs
      simp only [decide_eq_true_eq] at hst ⊢
      rcases hst with rfl | rfl; exact Or.inl rfl; exact absurd hwP hjP
  have hAc_i' : A i' c = true := by
    cases h1 : A i' c with
    | true => rfl
    | false =>
      cases h2 : A i' j with
      | false => exact absurd (h2.trans h1.symm) hi'
      | true => have := hneg_col_le i' h2; rw [h1] at this; cases this
  have hsh_i'_eq : shValOf D i' j = shValOf D i' c := shValOf_notU_col D hc_U i' j hjU
  have htneg_i' : tnegValOf D i' c = false ∧ tnegValOf D i' j = true := by
    by_cases h1 : tnegValOf D i' c = tnegValOf D i' j
    · exfalso
      have heqA : A i' j = A i' c := by
        rw [decomp_eval_row_col hrep D i' j, decomp_eval_row_col hrep D i' c]
        apply D.tPos.eval_congr; intro s hs; cases s with
        | sh => exact hsh_i'_eq
        | neg => dsimp only; exact congrArg Bool.not h1.symm
        | wire w =>
          have hwP : w ∈ slotWires D.tPos.leaves := mem_slotWires.mpr hs
          have ha : w ≠ n + j.val := fun e => hjP (e ▸ hwP)
          have hb : w ≠ n + c.val := fun e => hc_P (e ▸ hwP)
          simp [ha, hb]
      exact hi' heqA
    · have hle : tnegValOf D i' c = true → tnegValOf D i' j = true := by
        intro hct; apply D.tNeg.eval_mono _ hct; intro o ho hot; cases o with
        | none => rwa [hsh_i'_eq]
        | some w =>
          have hwH : w ∈ optWires D.tNeg.leaves := mem_optWires.mpr ho
          simp only [decide_eq_true_eq] at hot ⊢
          rcases hot with rfl | rfl; exact Or.inl rfl; exact absurd hwH hc_H
      cases ha : tnegValOf D i' c <;> cases hb : tnegValOf D i' j
      · exact absurd (ha.trans hb.symm) h1
      · exact ⟨rfl, rfl⟩
      · exact absurd (hle ha) (by rw [hb]; decide)
      · exact absurd (ha.trans hb.symm) h1
  have hi'U : i'.val ∈ D.sSh.leaves := by
    by_contra hnu
    have hsh_eq : shValOf D i' j = shValOf D r j := shValOf_notU_row D hr_U i' j hnu
    have htneg_eq : tnegValOf D i' j = tnegValOf D r j := by
      apply D.tNeg.eval_congr; intro o ho; cases o with
      | none => exact hsh_eq
      | some w =>
        have hwH : w ∈ optWires D.tNeg.leaves := mem_optWires.mpr ho
        have ha : w ≠ i'.val := fun e => hH_no_row i' (e ▸ hwH)
        have hb : w ≠ r.val := fun e => hr_H (e ▸ hwH)
        simp [ha, hb]
    rw [tneg_col_false_of hColInc hrep D hr_not hc_not j hjH] at htneg_eq
    rw [htneg_i'.2] at htneg_eq; cases htneg_eq
  have hi'P : i'.val ∉ slotWires D.tPos.leaves := Finset.disjoint_right.mp D.disj_PU hi'U
  have hsh_i'_true : shValOf D i' c = true := by
    by_contra h0
    have hsh0 : shValOf D i' c = false := Bool.eq_false_iff.mpr h0
    have hcongr : A i' c = D.tPos.eval (fun s => decide (s = Slot.neg)) := by
      rw [decomp_eval_row_col hrep D i' c]
      apply D.tPos.eval_congr; intro s hs; cases s with
      | sh => exact hsh0
      | neg => change (!tnegValOf D i' c) = true; simp [htneg_i'.1]
      | wire w =>
        have hwP : w ∈ slotWires D.tPos.leaves := mem_slotWires.mpr hs
        have ha : w ≠ i'.val := fun e => hi'P (e ▸ hwP)
        have hb : w ≠ n + c.val := fun e => hc_P (e ▸ hwP)
        simp [ha, hb]
    rw [hAc_i', hneg_alone_false] at hcongr; cases hcongr
  have htneg_sh_false : D.tNeg.eval (fun o => decide (o = none)) = false := by
    have hcongr : tnegValOf D i' c = D.tNeg.eval (fun o => decide (o = none)) := by
      apply D.tNeg.eval_congr; intro o ho; cases o with
      | none => simp [hsh_i'_true]
      | some w =>
        have hwH : w ∈ optWires D.tNeg.leaves := mem_optWires.mpr ho
        have ha : w ≠ i'.val := fun e => hH_no_row i' (e ▸ hwH)
        have hb : w ≠ n + c.val := fun e => hc_H (e ▸ hwH)
        simp [ha, hb]
    rw [← hcongr, htneg_i'.1]
  obtain ⟨l, hl_inc⟩ := hColInc j
  push Not at hl_inc
  obtain ⟨⟨i0, hi0j, hi0l_n⟩, _⟩ := hl_inc
  have hi0l : A i0 l = false := Bool.eq_false_iff.mpr hi0l_n
  have htneg_i0 : tnegValOf D i0 j = false ∧ tnegValOf D i0 l = true := by
    by_contra hbad
    have hneg_le : (!tnegValOf D i0 j) = true → (!tnegValOf D i0 l) = true := by
      cases ha : tnegValOf D i0 j <;> cases hb : tnegValOf D i0 l
      · simp
      · exact absurd ⟨ha, hb⟩ hbad
      · simp
      · simp
    have hlt : A i0 l = true := by
      rw [decomp_eval_row_col hrep D i0 j] at hi0j
      rw [decomp_eval_row_col hrep D i0 l]
      apply D.tPos.eval_mono _ hi0j
      intro s hs hst; cases s with
      | sh =>
        change shValOf D i0 j = true at hst
        change shValOf D i0 l = true
        rw [shValOf_notU_col D hc_U i0 j hjU] at hst
        exact shValOf_col_mono D hc_U i0 l hst
      | neg => exact hneg_le hst
      | wire w =>
        have hwP : w ∈ slotWires D.tPos.leaves := mem_slotWires.mpr hs
        simp only [decide_eq_true_eq] at hst ⊢
        rcases hst with rfl | rfl; exact Or.inl rfl; exact absurd hwP hjP
    rw [hi0l] at hlt; cases hlt
  have hi0_notP : i0.val ∉ slotWires D.tPos.leaves := by
    intro hi0P
    have hi0U : i0.val ∉ D.sSh.leaves := Finset.disjoint_left.mp D.disj_PU hi0P
    have hsh_eq : shValOf D i0 l = shValOf D r l := shValOf_notU_row D hr_U i0 l hi0U
    have htneg_eq : tnegValOf D i0 l = tnegValOf D r l := by
      apply D.tNeg.eval_congr; intro o ho; cases o with
      | none => exact hsh_eq
      | some w =>
        have hwH : w ∈ optWires D.tNeg.leaves := mem_optWires.mpr ho
        have ha : w ≠ i0.val := fun e => hH_no_row i0 (e ▸ hwH)
        have hb : w ≠ r.val := fun e => hr_H (e ▸ hwH)
        simp [ha, hb]
    by_cases hlH : n + l.val ∈ optWires D.tNeg.leaves
    · rw [tneg_col_false_of hColInc hrep D hr_not hc_not l hlH] at htneg_eq
      rw [htneg_i0.2] at htneg_eq; cases htneg_eq
    · have hrt : D.tNeg.eval (fun o => decide (o = none)) = true := by
        apply D.tNeg.eval_mono _ (htneg_eq ▸ htneg_i0.2)
        intro o ho hot; cases o with
        | none => simp
        | some w =>
          have hwH : w ∈ optWires D.tNeg.leaves := mem_optWires.mpr ho
          simp only [decide_eq_true_eq] at hot
          rcases hot with rfl | rfl; exact absurd hwH hr_H; exact absurd hwH hlH
      rw [htneg_sh_false] at hrt; cases hrt
  have hsh_i0_true : shValOf D i0 c = true := by
    by_contra h0
    have hsh0 : shValOf D i0 c = false := Bool.eq_false_iff.mpr h0
    have hsh_j0 : shValOf D i0 j = false := by rw [shValOf_notU_col D hc_U i0 j hjU, hsh0]
    have hcongr : A i0 j = D.tPos.eval (fun s => decide (s = Slot.neg)) := by
      rw [decomp_eval_row_col hrep D i0 j]
      apply D.tPos.eval_congr; intro s hs; cases s with
      | sh => exact hsh_j0
      | neg => change (!tnegValOf D i0 j) = true; simp [htneg_i0.1]
      | wire w =>
        have hwP : w ∈ slotWires D.tPos.leaves := mem_slotWires.mpr hs
        have ha : w ≠ i0.val := fun e => hi0_notP (e ▸ hwP)
        have hb : w ≠ n + j.val := fun e => hjP (e ▸ hwP)
        simp [ha, hb]
    rw [hi0j, hneg_alone_false] at hcongr; cases hcongr
  have hi_eq : i0 = i' := uniq_sh_row_of hInjR hrep D hc_not i0 i' hsh_i0_true hsh_i'_true
  subst hi_eq
  rw [htneg_i0.1] at htneg_i'
  cases htneg_i'.2

lemma decomp_tneg_eq_sh {n m : ℕ} {A : Fin n → Fin m → Bool} {C : Circuit}
    (hInjR : Function.Injective A) (hInjC : Function.Injective (fun j i => A i j))
    (hRowInc : ∀ i : Fin n, ∃ k : Fin n, ¬ ((∀ j, A i j = true → A k j = true) ∨ (∀ j, A k j = true → A i j = true)))
    (hColInc : ∀ j : Fin m, ∃ l : Fin m, ¬ ((∀ i, A i j = true → A i l = true) ∨ (∀ i, A i l = true → A i j = true)))
    (hrep : Represents A C) (D : Decomp (n + m) (fun x => C.eval x))
    {r : Fin n} {c : Fin m} (hr_not : r.val ∉ D.wires) (hc_not : n + c.val ∉ D.wires)
    (hlt_nm : ∀ w ∈ D.wires, w < n + m) :
    ∀ i j, tnegValOf D i j = shValOf D i j := by
  have hH_no_row := decomp_H_no_row hInjR hInjC hRowInc hColInc hrep D hr_not hc_not
  have hH_no_col := decomp_H_no_col hInjR hInjC hRowInc hColInc hrep D hr_not hc_not
  have hH_empty : optWires D.tNeg.leaves = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro w hwH
    have hlt := hlt_nm w (Finset.mem_union_left _ (Finset.mem_union_right _ hwH))
    by_cases h1 : w < n
    · exact hH_no_row ⟨w, h1⟩ hwH
    · have h2 : w - n < m := by omega
      have h3 : n + (w - n) = w := by omega
      exact hH_no_col ⟨w - n, h2⟩ (by simpa [h3] using hwH)
  have hsub : D.tNeg.leaves = {none} := by
    ext o; simp only [Finset.mem_singleton]
    constructor
    · intro ho; cases o with
      | none => rfl
      | some w =>
        have hw : w ∈ optWires D.tNeg.leaves := mem_optWires.mpr ho
        rw [hH_empty] at hw; exact absurd hw (Finset.notMem_empty w)
    · rintro rfl; exact D.sh_in_neg
  intro i j
  exact D.tNeg.eval_singleton_eq D.roNeg none hsub _

lemma decomp_col_pair_uniq {n m : ℕ} {A : Fin n → Fin m → Bool} {C : Circuit}
    (hInjC : Function.Injective (fun j i => A i j)) (hrep : Represents A C)
    (D : Decomp (n + m) (fun x => C.eval x)) {c : Fin m} (hc_U : n + c.val ∉ D.sSh.leaves)
    (htneg_eq_sh : ∀ i j, tnegValOf D i j = shValOf D i j)
    (z : Slot) (hz_sh_or_neg : z = Slot.sh ∨ z = Slot.neg)
    (hz_f : D.tPos.eval (fun s => decide (s = z)) = false)
    (a b : Fin m) (haP : n + a.val ∈ slotWires D.tPos.leaves) (hbP : n + b.val ∈ slotWires D.tPos.leaves)
    (hna_t : D.tPos.eval (fun s => decide (s = z ∨ s = Slot.wire (n + a.val))) = true)
    (hnb_t : D.tPos.eval (fun s => decide (s = z ∨ s = Slot.wire (n + b.val))) = true)
    (ha_f : D.tPos.eval (fun s => decide (s = Slot.wire (n + a.val))) = false)
    (hb_f : D.tPos.eval (fun s => decide (s = Slot.wire (n + b.val))) = false) :
    a = b := by
  by_contra hab
  have ha_notU : n + a.val ∉ D.sSh.leaves := Finset.disjoint_left.mp D.disj_PU haP
  have hb_notU : n + b.val ∉ D.sSh.leaves := Finset.disjoint_left.mp D.disj_PU hbP
  have hza : z ≠ Slot.wire (n + a.val) := by rcases hz_sh_or_neg with rfl | rfl <;> intro e <;> cases e
  have hzb : z ≠ Slot.wire (n + b.val) := by rcases hz_sh_or_neg with rfl | rfl <;> intro e <;> cases e
  have heqv := D.tPos.min_pair_equiv D.roPos z (Slot.wire (n + a.val)) (Slot.wire (n + b.val))
    hza hzb (fun e => hab (Fin.ext (by have h := slot_wire_inj.mp e; omega)))
    hna_t hnb_t hz_f ha_f hb_f
  apply hab; apply hInjC; funext i; dsimp only
  have hsh_eq : shValOf D i a = shValOf D i b := by
    rw [shValOf_notU_col D hc_U i a ha_notU, shValOf_notU_col D hc_U i b hb_notU]
  let baseEnv : Slot → Bool := fun s => match s with
    | .sh => shValOf D i a
    | .neg => !shValOf D i a
    | .wire w => decide (w = i.val)
  have hba : baseEnv (Slot.wire (n + a.val)) = false := by
    simp [baseEnv]; have := i.isLt; omega
  have hbb : baseEnv (Slot.wire (n + b.val)) = false := by
    simp [baseEnv]; have := i.isLt; omega
  have hAi_a : A i a = D.tPos.eval (Function.update baseEnv (Slot.wire (n + a.val)) true) := by
    rw [decomp_eval_row_col hrep D i a]; apply D.tPos.eval_congr; intro s _; cases s with
    | sh =>
      dsimp only
      rw [Function.update_of_ne (by intro e; cases e)]; rfl
    | neg =>
      dsimp only
      rw [Function.update_of_ne (by intro e; cases e)]
      change (!tnegValOf D i a) = !shValOf D i a
      rw [htneg_eq_sh]
    | wire w =>
      dsimp only
      by_cases hw : w = n + a.val
      · subst hw; simp [baseEnv]
      · rw [Function.update_of_ne (fun e => hw (by cases e; rfl))]
        simp [baseEnv, hw]
  have hAi_b : A i b = D.tPos.eval (Function.update baseEnv (Slot.wire (n + b.val)) true) := by
    rw [decomp_eval_row_col hrep D i b]; apply D.tPos.eval_congr; intro s _; cases s with
    | sh =>
      dsimp only
      rw [Function.update_of_ne (by intro e; cases e)]
      exact hsh_eq.symm
    | neg =>
      dsimp only
      rw [Function.update_of_ne (by intro e; cases e)]
      change (!tnegValOf D i b) = !shValOf D i a
      rw [htneg_eq_sh, hsh_eq]
    | wire w =>
      dsimp only
      by_cases hw : w = n + b.val
      · subst hw; simp [baseEnv]
      · rw [Function.update_of_ne (fun e => hw (by cases e; rfl))]
        simp [baseEnv, hw]
  rw [hAi_a, hAi_b]
  exact heqv baseEnv hba hbb

lemma row_part {n m : ℕ} (hn : 3 ≤ n) (hm : 3 ≤ m) (A : Fin n → Fin m → Bool)
    (hInjR : Function.Injective A) (hInjC : Function.Injective (fun j i => A i j))
    (hRowInc : ∀ i : Fin n, ∃ k : Fin n, ¬ ((∀ j, A i j = true → A k j = true) ∨ (∀ j, A k j = true → A i j = true)))
    (hColInc : ∀ j : Fin m, ∃ l : Fin m, ¬ ((∀ i, A i j = true → A i l = true) ∨ (∀ i, A i l = true → A i j = true)))
    (C : Circuit) (hC : FanInTwo C) (hrep : Represents A C)
    (hsize : C.size ≤ n + m - 1) (hnot : ∃ g ∈ C.gates, g.op = GateOp.not) :
    let X := fun i : Fin n => Finset.univ.filter (fun j : Fin m => A i j = true)
    ∃ r u : Fin n, r ≠ u ∧ ((X r) \ (X u)).card = 1 ∧ ((X u) \ (X r)).card = 1 ∧
      (∀ i, i ≠ r → i ≠ u → X r ⊂ X i) ∧
      ∀ i, (∀ k, (X i).card ≤ (X k).card) ↔ i = r ∨ i = u := by
  obtain ⟨D, r, c, hr_not, hc_not, hallR, hallC, hlt_nm⟩ :=
    extract_decomp hn hm A hInjR hInjC hRowInc hColInc C hC hrep hsize hnot
  have hr_P : r.val ∉ slotWires D.tPos.leaves := fun hm => hr_not (Finset.mem_union_left _ (Finset.mem_union_left _ hm))
  have hr_U : r.val ∉ D.sSh.leaves := fun hm => hr_not (Finset.mem_union_right _ hm)
  have hc_U : n + c.val ∉ D.sSh.leaves := fun hm => hc_not (Finset.mem_union_right _ hm)
  have hneg_alone_false := neg_alone_false_of hInjC hRowInc hColInc hrep D hr_not hc_not
  have hH_no_row := decomp_H_no_row hInjR hInjC hRowInc hColInc hrep D hr_not hc_not
  have htneg_eq_sh := decomp_tneg_eq_sh hInjR hInjC hRowInc hColInc hrep D hr_not hc_not hlt_nm
  obtain ⟨u, hu_inc⟩ := hRowInc r
  push Not at hu_inc
  obtain ⟨⟨j2, hAr_j2, hAu_j2_n⟩, ⟨j1, hAu_j1, hAr_j1_n⟩⟩ := hu_inc
  have hAu_j2 : A u j2 = false := Bool.eq_false_iff.mpr hAu_j2_n
  have hAr_j1 : A r j1 = false := Bool.eq_false_iff.mpr hAr_j1_n
  have hru : r ≠ u := fun e => by subst e; rw [hAr_j1] at hAu_j1; cases hAu_j1
  have hu_notP : u.val ∉ slotWires D.tPos.leaves := fun huP => by
    have := pos_row_le_of hrep D hr_not u huP j2 hAr_j2; rw [hAu_j2] at this; cases this
  have hdiff_sh : ∀ j : Fin m, A u j ≠ A r j → shValOf D u j = true ∧ shValOf D r j = false := by
    intro j hneq
    have hsh_neq : shValOf D u j ≠ shValOf D r j := by
      intro heq
      apply hneq
      rw [decomp_eval_row_col hrep D u j, decomp_eval_row_col hrep D r j]
      apply D.tPos.eval_congr; intro s hs; cases s with
      | sh => exact heq
      | neg =>
        change (!tnegValOf D u j) = !tnegValOf D r j
        rw [htneg_eq_sh, htneg_eq_sh, heq]
      | wire w =>
        have hwP : w ∈ slotWires D.tPos.leaves := mem_slotWires.mpr hs
        have ha : w ≠ u.val := fun e => hu_notP (e ▸ hwP)
        have hb : w ≠ r.val := fun e => hr_P (e ▸ hwP)
        simp [ha, hb]
    cases h1 : shValOf D r j with
    | true => exfalso; exact hsh_neq ((shValOf_row_mono D hr_U u j h1).trans h1.symm)
    | false =>
      cases h2 : shValOf D u j with
      | false => exact absurd (h2.trans h1.symm) hsh_neq
      | true => exact ⟨rfl, rfl⟩
  have hsh_j1 := hdiff_sh j1 (by rw [hAu_j1, hAr_j1]; decide)
  have hsh_j2 := hdiff_sh j2 (by rw [hAu_j2, hAr_j2]; decide)
  have hsh_alone_false : D.tPos.eval (fun s => decide (s = Slot.sh)) = false := by
    by_contra hne
    have ht : D.tPos.eval (fun s => decide (s = Slot.sh)) = true := Bool.eq_true_of_not_eq_false hne
    have hAu : A u j2 = true := by
      rw [decomp_eval_row_col hrep D u j2]
      apply D.tPos.eval_mono _ ht
      intro s _ hs
      have : s = Slot.sh := of_decide_eq_true hs
      subst this; exact hsh_j2.1
    rw [hAu_j2] at hAu; cases hAu
  have hdiff_col_P : ∀ j : Fin m, A u j ≠ A r j → n + j.val ∈ slotWires D.tPos.leaves := by
    intro j hneq
    have hshj := hdiff_sh j hneq
    by_contra hj_notP
    have hArj : A r j = false := by
      have hcongr : A r j = D.tPos.eval (fun s => decide (s = Slot.neg)) := by
        rw [decomp_eval_row_col hrep D r j]
        apply D.tPos.eval_congr; intro s hs; cases s with
        | sh => exact hshj.2
        | neg => change (!tnegValOf D r j) = true; rw [htneg_eq_sh, hshj.2]; rfl
        | wire w =>
          have hwP : w ∈ slotWires D.tPos.leaves := mem_slotWires.mpr hs
          have ha : w ≠ r.val := fun e => hr_P (e ▸ hwP)
          have hb : w ≠ n + j.val := fun e => hj_notP (e ▸ hwP)
          simp [ha, hb]
      rw [hcongr, hneg_alone_false]
    have hAuj : A u j = false := by
      have hcongr : A u j = D.tPos.eval (fun s => decide (s = Slot.sh)) := by
        rw [decomp_eval_row_col hrep D u j]
        apply D.tPos.eval_congr; intro s hs; cases s with
        | sh => exact hshj.1
        | neg => change (!tnegValOf D u j) = false; rw [htneg_eq_sh, hshj.1]; rfl
        | wire w =>
          have hwP : w ∈ slotWires D.tPos.leaves := mem_slotWires.mpr hs
          have ha : w ≠ u.val := fun e => hu_notP (e ▸ hwP)
          have hb : w ≠ n + j.val := fun e => hj_notP (e ▸ hwP)
          simp [ha, hb]
      rw [hcongr, hsh_alone_false]
    exact hneq (hAuj.trans hArj.symm)
  have hj1P : n + j1.val ∈ slotWires D.tPos.leaves := hdiff_col_P j1 (by rw [hAu_j1, hAr_j1]; decide)
  have hj1_notU : n + j1.val ∉ D.sSh.leaves := Finset.disjoint_left.mp D.disj_PU hj1P
  have hsh_uc : shValOf D u c = true := by
    rw [← shValOf_notU_col D hc_U u j1 hj1_notU]; exact hsh_j1.1
  have hother_P : ∀ i : Fin n, i ≠ r → i ≠ u → i.val ∈ slotWires D.tPos.leaves := by
    intro i hir hiu
    by_contra hi_notP
    have hsh_ic : shValOf D i c = false := by
      by_contra h1
      exact hiu (uniq_sh_row_of hInjR hrep D hc_not i u (Bool.eq_true_of_not_eq_false h1) hsh_uc)
    have hAi_eq_r : A i = A r := by
      funext j
      by_cases hjU : n + j.val ∈ D.sSh.leaves
      · have hjP : n + j.val ∉ slotWires D.tPos.leaves := Finset.disjoint_right.mp D.disj_PU hjU
        cases hsr : shValOf D r j with
        | true =>
          have hsi : shValOf D i j = true := shValOf_row_mono D hr_U i j hsr
          rw [decomp_eval_row_col hrep D i j, decomp_eval_row_col hrep D r j]
          apply D.tPos.eval_congr; intro s hs; cases s with
          | sh => change shValOf D i j = shValOf D r j; rw [hsi, hsr]
          | neg => change (!tnegValOf D i j) = !tnegValOf D r j; rw [htneg_eq_sh, htneg_eq_sh, hsi, hsr]
          | wire w =>
            have hwP : w ∈ slotWires D.tPos.leaves := mem_slotWires.mpr hs
            have ha : w ≠ i.val := fun e => hi_notP (e ▸ hwP)
            have hb : w ≠ r.val := fun e => hr_P (e ▸ hwP)
            simp [ha, hb]
        | false =>
          have hArj : A r j = false := by
            have hcongr : A r j = D.tPos.eval (fun s => decide (s = Slot.neg)) := by
              rw [decomp_eval_row_col hrep D r j]
              apply D.tPos.eval_congr; intro s hs; cases s with
              | sh => exact hsr
              | neg => change (!tnegValOf D r j) = true; rw [htneg_eq_sh, hsr]; rfl
              | wire w =>
                have hwP : w ∈ slotWires D.tPos.leaves := mem_slotWires.mpr hs
                have ha : w ≠ r.val := fun e => hr_P (e ▸ hwP)
                have hb : w ≠ n + j.val := fun e => hjP (e ▸ hwP)
                simp [ha, hb]
            rw [hcongr, hneg_alone_false]
          have hAij : A i j = false := by
            cases hsi : shValOf D i j with
            | false =>
              have hcongr : A i j = D.tPos.eval (fun s => decide (s = Slot.neg)) := by
                rw [decomp_eval_row_col hrep D i j]
                apply D.tPos.eval_congr; intro s hs; cases s with
                | sh => exact hsi
                | neg => change (!tnegValOf D i j) = true; rw [htneg_eq_sh, hsi]; rfl
                | wire w =>
                  have hwP : w ∈ slotWires D.tPos.leaves := mem_slotWires.mpr hs
                  have ha : w ≠ i.val := fun e => hi_notP (e ▸ hwP)
                  have hb : w ≠ n + j.val := fun e => hjP (e ▸ hwP)
                  simp [ha, hb]
              rw [hcongr, hneg_alone_false]
            | true =>
              have hcongr : A i j = D.tPos.eval (fun s => decide (s = Slot.sh)) := by
                rw [decomp_eval_row_col hrep D i j]
                apply D.tPos.eval_congr; intro s hs; cases s with
                | sh => exact hsi
                | neg => change (!tnegValOf D i j) = false; rw [htneg_eq_sh, hsi]; rfl
                | wire w =>
                  have hwP : w ∈ slotWires D.tPos.leaves := mem_slotWires.mpr hs
                  have ha : w ≠ i.val := fun e => hi_notP (e ▸ hwP)
                  have hb : w ≠ n + j.val := fun e => hjP (e ▸ hwP)
                  simp [ha, hb]
              rw [hcongr, hsh_alone_false]
          rw [hAij, hArj]
      · have hsi : shValOf D i j = false := by rw [shValOf_notU_col D hc_U i j hjU, hsh_ic]
        have hsr : shValOf D r j = false := by
          rw [shValOf_notU_col D hc_U r j hjU]
          have hcongr : shValOf D r c = D.sSh.eval (fun _ => false) :=
            D.sSh.eval_congr (fun w hw => by
              have ha : w ≠ r.val := fun e => hr_U (e ▸ hw)
              have hb : w ≠ n + c.val := fun e => hc_U (e ▸ hw)
              simp [ha, hb])
          rw [hcongr, MTree.eval_false]
        rw [decomp_eval_row_col hrep D i j, decomp_eval_row_col hrep D r j]
        apply D.tPos.eval_congr; intro s hs; cases s with
        | sh => change shValOf D i j = shValOf D r j; rw [hsi, hsr]
        | neg => change (!tnegValOf D i j) = !tnegValOf D r j; rw [htneg_eq_sh, htneg_eq_sh, hsi, hsr]
        | wire w =>
          have hwP : w ∈ slotWires D.tPos.leaves := mem_slotWires.mpr hs
          have ha : w ≠ i.val := fun e => hi_notP (e ▸ hwP)
          have hb : w ≠ r.val := fun e => hr_P (e ▸ hwP)
          simp [ha, hb]
    exact hir (hInjR hAi_eq_r)
  let X := fun i : Fin n => Finset.univ.filter (fun j : Fin m => A i j = true)
  have hX_ssub : ∀ i : Fin n, i ≠ r → i ≠ u → X r ⊂ X i := by
    intro i hir hiu
    have hsub : X r ⊆ X i := by
      intro j hj
      simp only [X, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact pos_row_le_of hrep D hr_not i (hother_P i hir hiu) j hj
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq => hir (hInjR (funext fun j => ?_)).symm⟩
    rw [Bool.eq_iff_iff]
    have hj : j ∈ X r ↔ j ∈ X i := by rw [heq]
    simpa [X] using hj
  have hdiff_ru_uniq : ∀ a b : Fin m, a ∈ X r \ X u → b ∈ X r \ X u → a = b := by
    intro a b ha hb
    simp only [X, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    have hAua : A u a = false := Bool.eq_false_iff.mpr ha.2
    have hAub : A u b = false := Bool.eq_false_iff.mpr hb.2
    have haP : n + a.val ∈ slotWires D.tPos.leaves := hdiff_col_P a (by rw [hAua, ha.1]; decide)
    have hbP : n + b.val ∈ slotWires D.tPos.leaves := hdiff_col_P b (by rw [hAub, hb.1]; decide)
    have hsha := hdiff_sh a (by rw [hAua, ha.1]; decide)
    have hshb := hdiff_sh b (by rw [hAub, hb.1]; decide)
    have hna_t : D.tPos.eval (fun s => decide (s = Slot.neg ∨ s = Slot.wire (n + a.val))) = true := by
      have hcongr : A r a = D.tPos.eval (fun s => decide (s = Slot.neg ∨ s = Slot.wire (n + a.val))) := by
        rw [decomp_eval_row_col hrep D r a]
        apply D.tPos.eval_congr; intro s hs; cases s with
        | sh => exact hsha.2
        | neg => change (!tnegValOf D r a) = true; rw [htneg_eq_sh, hsha.2]; rfl
        | wire w =>
          have hwP : w ∈ slotWires D.tPos.leaves := mem_slotWires.mpr hs
          have hwr : w ≠ r.val := fun e => hr_P (e ▸ hwP)
          simp [hwr]
      rw [← hcongr, ha.1]
    have hnb_t : D.tPos.eval (fun s => decide (s = Slot.neg ∨ s = Slot.wire (n + b.val))) = true := by
      have hcongr : A r b = D.tPos.eval (fun s => decide (s = Slot.neg ∨ s = Slot.wire (n + b.val))) := by
        rw [decomp_eval_row_col hrep D r b]
        apply D.tPos.eval_congr; intro s hs; cases s with
        | sh => exact hshb.2
        | neg => change (!tnegValOf D r b) = true; rw [htneg_eq_sh, hshb.2]; rfl
        | wire w =>
          have hwP : w ∈ slotWires D.tPos.leaves := mem_slotWires.mpr hs
          have hwr : w ≠ r.val := fun e => hr_P (e ▸ hwP)
          simp [hwr]
      rw [← hcongr, hb.1]
    have ha_f : D.tPos.eval (fun s => decide (s = Slot.wire (n + a.val))) = false := by
      by_contra h1
      have ht : D.tPos.eval (fun s => decide (s = Slot.wire (n + a.val))) = true := Bool.eq_true_of_not_eq_false h1
      have hAu : A u a = true := by
        rw [decomp_eval_row_col hrep D u a]; apply D.tPos.eval_mono _ ht; intro s _ hs
        have : s = Slot.wire (n + a.val) := of_decide_eq_true hs; subst this; simp
      rw [hAua] at hAu; cases hAu
    have hb_f : D.tPos.eval (fun s => decide (s = Slot.wire (n + b.val))) = false := by
      by_contra h1
      have ht : D.tPos.eval (fun s => decide (s = Slot.wire (n + b.val))) = true := Bool.eq_true_of_not_eq_false h1
      have hAu : A u b = true := by
        rw [decomp_eval_row_col hrep D u b]; apply D.tPos.eval_mono _ ht; intro s _ hs
        have : s = Slot.wire (n + b.val) := of_decide_eq_true hs; subst this; simp
      rw [hAub] at hAu; cases hAu
    exact decomp_col_pair_uniq hInjC hrep D hc_U htneg_eq_sh Slot.neg (Or.inr rfl)
      hneg_alone_false a b haP hbP hna_t hnb_t ha_f hb_f
  have hdiff_ur_uniq : ∀ a b : Fin m, a ∈ X u \ X r → b ∈ X u \ X r → a = b := by
    intro a b ha hb
    simp only [X, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    have hAra : A r a = false := Bool.eq_false_iff.mpr ha.2
    have hArb : A r b = false := Bool.eq_false_iff.mpr hb.2
    have haP : n + a.val ∈ slotWires D.tPos.leaves := hdiff_col_P a (by rw [ha.1, hAra]; decide)
    have hbP : n + b.val ∈ slotWires D.tPos.leaves := hdiff_col_P b (by rw [hb.1, hArb]; decide)
    have hsha := hdiff_sh a (by rw [ha.1, hAra]; decide)
    have hshb := hdiff_sh b (by rw [hb.1, hArb]; decide)
    have hna_t : D.tPos.eval (fun s => decide (s = Slot.sh ∨ s = Slot.wire (n + a.val))) = true := by
      have hcongr : A u a = D.tPos.eval (fun s => decide (s = Slot.sh ∨ s = Slot.wire (n + a.val))) := by
        rw [decomp_eval_row_col hrep D u a]
        apply D.tPos.eval_congr; intro s hs; cases s with
        | sh => exact hsha.1
        | neg => change (!tnegValOf D u a) = false; rw [htneg_eq_sh, hsha.1]; rfl
        | wire w =>
          have hwP : w ∈ slotWires D.tPos.leaves := mem_slotWires.mpr hs
          have hwu : w ≠ u.val := fun e => hu_notP (e ▸ hwP)
          simp [hwu]
      rw [← hcongr, ha.1]
    have hnb_t : D.tPos.eval (fun s => decide (s = Slot.sh ∨ s = Slot.wire (n + b.val))) = true := by
      have hcongr : A u b = D.tPos.eval (fun s => decide (s = Slot.sh ∨ s = Slot.wire (n + b.val))) := by
        rw [decomp_eval_row_col hrep D u b]
        apply D.tPos.eval_congr; intro s hs; cases s with
        | sh => exact hshb.1
        | neg => change (!tnegValOf D u b) = false; rw [htneg_eq_sh, hshb.1]; rfl
        | wire w =>
          have hwP : w ∈ slotWires D.tPos.leaves := mem_slotWires.mpr hs
          have hwu : w ≠ u.val := fun e => hu_notP (e ▸ hwP)
          simp [hwu]
      rw [← hcongr, hb.1]
    have ha_f : D.tPos.eval (fun s => decide (s = Slot.wire (n + a.val))) = false := by
      by_contra h1
      have ht : D.tPos.eval (fun s => decide (s = Slot.wire (n + a.val))) = true := Bool.eq_true_of_not_eq_false h1
      have hAr : A r a = true := by
        rw [decomp_eval_row_col hrep D r a]; apply D.tPos.eval_mono _ ht; intro s _ hs
        have : s = Slot.wire (n + a.val) := of_decide_eq_true hs; subst this; simp
      rw [hAra] at hAr; cases hAr
    have hb_f : D.tPos.eval (fun s => decide (s = Slot.wire (n + b.val))) = false := by
      by_contra h1
      have ht : D.tPos.eval (fun s => decide (s = Slot.wire (n + b.val))) = true := Bool.eq_true_of_not_eq_false h1
      have hAr : A r b = true := by
        rw [decomp_eval_row_col hrep D r b]; apply D.tPos.eval_mono _ ht; intro s _ hs
        have : s = Slot.wire (n + b.val) := of_decide_eq_true hs; subst this; simp
      rw [hArb] at hAr; cases hAr
    exact decomp_col_pair_uniq hInjC hrep D hc_U htneg_eq_sh Slot.sh (Or.inl rfl)
      hsh_alone_false a b haP hbP hna_t hnb_t ha_f hb_f
  have hcard_ru : (X r \ X u).card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨j2, ?_⟩
    ext j; simp only [Finset.mem_singleton]
    have hj2_in : j2 ∈ X r \ X u := by simp [X, hAr_j2, hAu_j2]
    exact ⟨fun hj => hdiff_ru_uniq j j2 hj hj2_in, fun e => e ▸ hj2_in⟩
  have hcard_ur : (X u \ X r).card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨j1, ?_⟩
    ext j; simp only [Finset.mem_singleton]
    have hj1_in : j1 ∈ X u \ X r := by simp [X, hAu_j1, hAr_j1]
    exact ⟨fun hj => hdiff_ur_uniq j j1 hj hj1_in, fun e => e ▸ hj1_in⟩
  have hdeg_eq : (X r).card = (X u).card := by
    have h1 := Finset.card_sdiff_add_card_inter (X r) (X u)
    have h2 := Finset.card_sdiff_add_card_inter (X u) (X r)
    rw [Finset.inter_comm (X u) (X r)] at h2
    rw [hcard_ru] at h1
    rw [hcard_ur] at h2
    omega
  refine ⟨r, u, hru, hcard_ru, hcard_ur, hX_ssub, ?_⟩
  intro i
  constructor
  · intro hmin
    by_contra hnot_ru
    push Not at hnot_ru
    have hlt := Finset.card_lt_card (hX_ssub i hnot_ru.1 hnot_ru.2)
    have hle : (X i).card ≤ (X r).card := hmin r
    omega
  · rintro (hi | hi) k
    · rw [hi]
      by_cases h1 : k = r
      · subst h1; exact le_rfl
      · by_cases h2 : k = u
        · subst h2; exact le_of_eq hdeg_eq
        · exact le_of_lt (Finset.card_lt_card (hX_ssub k h1 h2))
    · rw [hi]
      by_cases h1 : k = r
      · subst h1; exact le_of_eq hdeg_eq.symm
      · by_cases h2 : k = u
        · subst h2; exact le_rfl
        · rw [← hdeg_eq]; exact le_of_lt (Finset.card_lt_card (hX_ssub k h1 h2))

def swapWire (n m w : ℕ) : ℕ :=
  if w < n then m + w else if w < n + m then w - n else w

def swapGate (n m : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (swapWire n m)⟩

def swapCircuit (n m : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.map (swapGate n m), swapWire n m C.output⟩

lemma swapCircuit_eval (n m : ℕ) (C : Circuit) (i : Fin n) (j : Fin m) :
    (swapCircuit n m C).eval (oneEach j i) = C.eval (oneEach i j) := by
  have hfold : ∀ (gs : List Gate) (x y : List Bool),
      x.length = y.length → n + m ≤ x.length →
      (∀ w, x.getD (swapWire n m w) false = y.getD w false) →
      ∀ w, ((gs.map (swapGate n m)).foldl stp x).getD (swapWire n m w) false =
        (gs.foldl stp y).getD w false := by
    intro gs
    induction gs with
    | nil => intro x y _ _ h w; exact h w
    | cons g gs ih =>
      intro x y hlen hnm h
      simp only [List.map_cons, List.foldl_cons]
      apply ih (stp x (swapGate n m g)) (stp y g) (by simp [stp, hlen]) (by simp [stp]; omega)
      intro w
      by_cases hweq : w = y.length
      · subst hweq
        have hsw : swapWire n m y.length = x.length := by
          unfold swapWire; split_ifs <;> omega
        rw [hsw, getD_stp_eq, getD_stp_eq]
        simp only [swapGate, List.map_map]
        congr 1
        apply List.map_congr_left
        intro a _; exact h a
      · have hsw_ne : swapWire n m w ≠ x.length := by
          unfold swapWire; split_ifs <;> omega
        rw [getD_stp_ne x _ hsw_ne, getD_stp_ne y _ hweq]
        exact h w
  rw [eval_eq, eval_eq]
  apply hfold C.gates (oneEach j i) (oneEach i j) (by rw [oneEach_len, oneEach_len]; omega)
    (by rw [oneEach_len]; omega)
  intro w
  unfold swapWire
  split_ifs with h1 h2
  · rw [oneEach_getD_right j i h1, oneEach_getD_left i j h1]
  · have hwm : w - n < m := by omega
    have hw' : w = n + (w - n) := by omega
    rw [oneEach_getD_left j i hwm, hw', oneEach_getD_right i j hwm, Nat.add_sub_cancel_left]
  · rw [List.getD_eq_default _ _ (by rw [oneEach_len]; omega),
        List.getD_eq_default _ _ (by rw [oneEach_len]; omega)]

lemma main_proof :
    ∀ (n m : Nat) (A : Fin n → Fin m → Bool), 3 ≤ n → 3 ≤ m →
      let rowLE := fun i k : Fin n => ∀ j, A i j = true → A k j = true
      let colLE := fun j l : Fin m => ∀ i, A i j = true → A i l = true
      let rc := fun i k : Fin n => rowLE i k ∨ rowLE k i
      let cc := fun j l : Fin m => colLE j l ∨ colLE l j
      Function.Injective A → Function.Injective (fun j i => A i j) →
      (∀ i, ∃ k, ¬ rc i k) → (∀ j, ∃ l, ¬ cc j l) →
      ∀ C : Circuit,
      FanInTwo C → Represents A C →
      C.size ≤ n + m - 1 →
      (∃ g ∈ C.gates, g.op = GateOp.not) →
      let X := fun i : Fin n => Finset.univ.filter (fun j : Fin m => A i j = true)
      let Y := fun j : Fin m => Finset.univ.filter (fun i : Fin n => A i j = true)
      (∃ r u : Fin n, r ≠ u ∧ ((X r) \ (X u)).card = 1 ∧ ((X u) \ (X r)).card = 1 ∧
        (∀ i, i ≠ r → i ≠ u → X r ⊂ X i) ∧
        ∀ i, (∀ k, (X i).card ≤ (X k).card) ↔ i = r ∨ i = u) ∧
      (∃ c v : Fin m, c ≠ v ∧ ((Y c) \ (Y v)).card = 1 ∧ ((Y v) \ (Y c)).card = 1 ∧
        (∀ j, j ≠ c → j ≠ v → Y c ⊂ Y j) ∧
        ∀ j, (∀ l, (Y j).card ≤ (Y l).card) ↔ j = c ∨ j = v) := by
  intro n m A hn hm _ _ _ _ hInjR hInjC hRowInc hColInc C hC hrep hsize hnot
  constructor
  · exact row_part hn hm A hInjR hInjC hRowInc hColInc C hC hrep hsize hnot
  · let AT : Fin m → Fin n → Bool := fun j i => A i j
    let CT := swapCircuit n m C
    have hCT_fan : FanInTwo CT := by
      intro g hg
      simp only [CT, swapCircuit, List.mem_map] at hg
      rcases hg with ⟨g0, hg0, rfl⟩
      have h0 := hC g0 hg0
      exact ⟨h0.1, by simp [swapGate, h0.2]⟩
    have hCT_rep : Represents AT CT := fun j i => by
      rw [swapCircuit_eval n m C i j, hrep i j]
    have hCT_size : CT.size ≤ m + n - 1 := by
      simp only [Circuit.size, CT, swapCircuit, List.length_map]
      simp only [Circuit.size] at hsize
      omega
    have hCT_not : ∃ g ∈ CT.gates, g.op = GateOp.not := by
      obtain ⟨g0, hg0, hop⟩ := hnot
      exact ⟨swapGate n m g0, List.mem_map_of_mem hg0, hop⟩
    exact row_part hm hn AT hInjC hInjR hColInc hRowInc CT hCT_fan hCT_rep hCT_size hCT_not

end PEqualNP.Outside.L_meta_27809_aux

theorem PEqualNP.Outside.L_meta_27809 :
  ∀ (n m : Nat) (A : Fin n → Fin m → Bool), 3 ≤ n → 3 ≤ m →
    let rowLE := fun i k : Fin n => ∀ j, A i j = true → A k j = true
    let colLE := fun j l : Fin m => ∀ i, A i j = true → A i l = true
    let rc := fun i k : Fin n => rowLE i k ∨ rowLE k i
    let cc := fun j l : Fin m => colLE j l ∨ colLE l j
    Function.Injective A → Function.Injective (fun j i => A i j) →
    (∀ i, ∃ k, ¬ rc i k) → (∀ j, ∃ l, ¬ cc j l) →
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C →
    C.size ≤ n + m - 1 →
    (∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
    let X := fun i : Fin n => Finset.univ.filter (fun j : Fin m => A i j = true)
    let Y := fun j : Fin m => Finset.univ.filter (fun i : Fin n => A i j = true)
    (∃ r u : Fin n, r ≠ u ∧ ((X r) \ (X u)).card = 1 ∧ ((X u) \ (X r)).card = 1 ∧
      (∀ i, i ≠ r → i ≠ u → X r ⊂ X i) ∧
      ∀ i, (∀ k, (X i).card ≤ (X k).card) ↔ i = r ∨ i = u) ∧
    (∃ c v : Fin m, c ≠ v ∧ ((Y c) \ (Y v)).card = 1 ∧ ((Y v) \ (Y c)).card = 1 ∧
      (∀ j, j ≠ c → j ≠ v → Y c ⊂ Y j) ∧
      ∀ j, (∀ l, (Y j).card ≤ (Y l).card) ↔ j = c ∨ j = v) := by
  exact PEqualNP.Outside.L_meta_27809_aux.main_proof
