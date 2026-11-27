import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import PEqualNP.Defs

-- Formula extraction and positive normal forms adapt L_meta_25021 from this repository.

namespace PEqualNP.Outside.L_meta_29938_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem getD_snoc (V : List Bool) (e : Bool) (i : ℕ) :
    (V ++ [e]).getD i false = if i = V.length then e else V.getD i false := by
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_gt_of_ne h with h | h
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem wiresFrom_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    wiresFrom (gs ++ [g]) x = wiresFrom gs x ++
      [g.op.eval (g.inputs.map fun i => (wiresFrom gs x).getD i false)] := by
  rw [wiresFrom_append]; rfl

def run : List Gate → ℕ → (ℕ → Bool) → ℕ → Bool
  | [], _, x => x
  | g :: gs, t, x => run gs (t + 1) (Function.update x t (g.op.eval (g.inputs.map x)))

theorem run_eq (gs : List Gate) : ∀ w : List Bool, ∀ i,
    (wiresFrom gs w).getD i false = run gs w.length (fun j => w.getD j false) i := by
  induction gs with
  | nil => intro w i; rfl
  | cons g gs ih =>
    intro w i
    change (wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD i false = _
    rw [ih, List.length_append, List.length_singleton, run]
    congr 2; funext j
    rw [getD_snoc, Function.update_apply]

theorem oneEach_len {n m : ℕ} (u : Fin n) (v : Fin m) : (oneEach u v).length = n + m := by
  simp [oneEach]

theorem oneEach_getD {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (oneEach u v).getD i false = decide (i = u.val ∨ i = n + v.val) := by
  have hu := u.isLt; have hv := v.isLt
  unfold oneEach
  by_cases h1 : i < n
  · rw [List.getD_append _ _ _ _ (by simp [h1])]
    simp [List.getD_eq_getElem?_getD, h1, Fin.ext_iff]
    omega
  · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    simp only [List.length_ofFn]
    by_cases h2 : i < n + m
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, show i - n < m by omega,
        ↓reduceDIte, Option.getD_some, Fin.ext_iff, decide_eq_decide]
      omega
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      simp only [false_eq_decide_iff]; omega

def GateAon (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def GateMono (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

def effective (g : Gate) : List ℕ :=
  match g.op with
  | .not => g.inputs.take 1
  | _ => g.inputs

theorem gate_effective (g : Gate) (x : ℕ → Bool) :
    g.op.eval (g.inputs.map x) = g.op.eval ((effective g).map x) := by
  rcases g with ⟨op, is⟩
  cases op <;> cases is <;> rfl

def Dep (F : (ℕ → Bool) → Bool) (N : Finset ℕ) : Prop :=
  ∀ x y : ℕ → Bool, (∀ i ∈ N, x i = y i) → F x = F y

inductive Form where
  | var : ℕ → Form
  | not : Form → Form
  | and : Form → Form → Form
  | or  : Form → Form → Form

def Form.eval (x : ℕ → Bool) : Form → Bool
  | .var w   => x w
  | .not f   => !(f.eval x)
  | .and l r => l.eval x && r.eval x
  | .or  l r => l.eval x || r.eval x

def Form.vars : Form → Finset ℕ
  | .var w   => {w}
  | .not f   => f.vars
  | .and l r => l.vars ∪ r.vars
  | .or  l r => l.vars ∪ r.vars

def Form.nots : Form → ℕ
  | .var _   => 0
  | .not f   => f.nots + 1
  | .and l r => l.nots + r.nots
  | .or  l r => l.nots + r.nots

def Form.bins : Form → ℕ
  | .var _   => 0
  | .not f   => f.bins
  | .and l r => l.bins + r.bins + 1
  | .or  l r => l.bins + r.bins + 1

def Form.ReadOnce : Form → Prop
  | .var _   => True
  | .not f   => f.ReadOnce
  | .and l r => l.ReadOnce ∧ r.ReadOnce ∧ Disjoint l.vars r.vars
  | .or  l r => l.ReadOnce ∧ r.ReadOnce ∧ Disjoint l.vars r.vars

theorem Form.vars_card_of_readOnce : ∀ {f : Form}, f.ReadOnce → f.vars.card = f.bins + 1 := by
  intro f
  induction f with
  | var _ => intro _; simp [Form.vars, Form.bins]
  | not f ih => intro h; exact ih h
  | and l r ihl ihr =>
      rintro ⟨hl, hr, hd⟩
      simp only [Form.vars, Form.bins, Finset.card_union_of_disjoint hd]
      have h1 := ihl hl; have h2 := ihr hr; omega
  | or l r ihl ihr =>
      rintro ⟨hl, hr, hd⟩
      simp only [Form.vars, Form.bins, Finset.card_union_of_disjoint hd]
      have h1 := ihl hl; have h2 := ihr hr; omega

theorem Form.eval_congr (f : Form) : ∀ (x y : ℕ → Bool),
    (∀ i ∈ f.vars, x i = y i) → f.eval x = f.eval y := by
  induction f with
  | var w => intro x y h; exact h w (by simp [Form.vars])
  | not f ih => intro x y h; simp [Form.eval, ih x y h]
  | and l r ihl ihr =>
      intro x y h; simp only [Form.eval]
      rw [ihl x y (fun i hi => h i (Finset.mem_union_left _ hi)),
          ihr x y (fun i hi => h i (Finset.mem_union_right _ hi))]
  | or l r ihl ihr =>
      intro x y h; simp only [Form.eval]
      rw [ihl x y (fun i hi => h i (Finset.mem_union_left _ hi)),
          ihr x y (fun i hi => h i (Finset.mem_union_right _ hi))]

def Form.subst (f : Form) (t : ℕ) (sub : Form) : Form :=
  match f with
  | .var w   => if w = t then sub else .var w
  | .not f'  => .not (f'.subst t sub)
  | .and l r => .and (l.subst t sub) (r.subst t sub)
  | .or  l r => .or  (l.subst t sub) (r.subst t sub)

theorem Form.eval_subst (t : ℕ) (sub : Form) (f : Form) (x : ℕ → Bool) :
    (f.subst t sub).eval x = f.eval (Function.update x t (sub.eval x)) := by
  induction f with
  | var w => by_cases h : w = t <;> simp [Form.subst, Form.eval, Function.update, h]
  | not f ih => simp [Form.subst, Form.eval, ih]
  | and l r ihl ihr => simp [Form.subst, Form.eval, ihl, ihr]
  | or l r ihl ihr => simp [Form.subst, Form.eval, ihl, ihr]

theorem Form.subst_id_of_notMem (t : ℕ) (sub : Form) {f : Form} (h : t ∉ f.vars) : f.subst t sub = f := by
  induction f with
  | var w =>
      have : w ≠ t := fun e => h (by simp [Form.vars, e])
      simp [Form.subst, this]
  | not f ih => simp [Form.subst, ih h]
  | and l r ihl ihr =>
      simp only [Form.vars, Finset.mem_union, not_or] at h
      simp [Form.subst, ihl h.1, ihr h.2]
  | or l r ihl ihr =>
      simp only [Form.vars, Finset.mem_union, not_or] at h
      simp [Form.subst, ihl h.1, ihr h.2]

theorem Form.subst_props (t : ℕ) (sub : Form) (hsub : sub.ReadOnce) :
    ∀ {f : Form}, f.ReadOnce → t ∈ f.vars → Disjoint (f.vars.erase t) sub.vars →
      (f.subst t sub).ReadOnce ∧
      (f.subst t sub).vars = f.vars.erase t ∪ sub.vars ∧
      (f.subst t sub).nots = f.nots + sub.nots := by
  intro f
  induction f with
  | var w =>
    intro _ ht _
    have hwt : w = t := by simp [Form.vars] at ht; exact ht.symm
    subst hwt
    simp [Form.subst, Form.vars, Form.nots, hsub]
  | not f ih =>
    intro hro ht hdis
    obtain ⟨r1, r2, r3⟩ := ih hro ht hdis
    exact ⟨r1, r2, by simp [Form.subst, Form.nots, r3]; omega⟩
  | and l r ihl ihr =>
    intro ⟨hl, hr, hlr⟩ ht hdis
    simp only [Form.vars, Finset.mem_union] at ht
    rcases ht with htl | htr
    · have htr_not : t ∉ r.vars := fun h => Finset.disjoint_left.1 hlr htl h
      have hsubr : r.subst t sub = r := Form.subst_id_of_notMem t sub htr_not
      have hdis_l : Disjoint (l.vars.erase t) sub.vars :=
        hdis.mono_left (Finset.erase_subset_erase t Finset.subset_union_left)
      have hdis_rs : Disjoint r.vars sub.vars := by
        refine hdis.mono_left (fun x hx => Finset.mem_erase.2 ⟨fun (e : x = t) => htr_not (e ▸ hx), Finset.mem_union_right _ hx⟩)
      obtain ⟨ro1, v1, n1⟩ := ihl hl htl hdis_l
      refine ⟨⟨ro1, by rw [hsubr]; exact hr, ?_⟩, ?_, ?_⟩
      · rw [v1, hsubr]
        exact Finset.disjoint_union_left.2 ⟨hlr.mono_left (Finset.erase_subset _ _), hdis_rs.symm⟩
      · simp only [Form.subst, Form.vars, v1, hsubr]
        ext x; simp only [Finset.mem_union, Finset.mem_erase]
        by_cases hxt : x = t
        · subst hxt; simp [htr_not]
        · tauto
      · simp [Form.subst, Form.nots, hsubr, n1]; omega
    · have htl_not : t ∉ l.vars := fun h => Finset.disjoint_left.1 hlr h htr
      have hsubl : l.subst t sub = l := Form.subst_id_of_notMem t sub htl_not
      have hdis_r : Disjoint (r.vars.erase t) sub.vars :=
        hdis.mono_left (Finset.erase_subset_erase t Finset.subset_union_right)
      have hdis_ls : Disjoint l.vars sub.vars := by
        refine hdis.mono_left (fun x hx => Finset.mem_erase.2 ⟨fun (e : x = t) => htl_not (e ▸ hx), Finset.mem_union_left _ hx⟩)
      obtain ⟨ro2, v2, n2⟩ := ihr hr htr hdis_r
      refine ⟨⟨by rw [hsubl]; exact hl, ro2, ?_⟩, ?_, ?_⟩
      · rw [v2, hsubl]
        exact Finset.disjoint_union_right.2 ⟨hlr.mono_right (Finset.erase_subset _ _), hdis_ls⟩
      · simp only [Form.subst, Form.vars, v2, hsubl]
        ext x; simp only [Finset.mem_union, Finset.mem_erase]
        by_cases hxt : x = t
        · subst hxt; simp [htl_not]
        · tauto
      · simp [Form.subst, Form.nots, hsubl, n2]; omega
  | or l r ihl ihr =>
    intro ⟨hl, hr, hlr⟩ ht hdis
    simp only [Form.vars, Finset.mem_union] at ht
    rcases ht with htl | htr
    · have htr_not : t ∉ r.vars := fun h => Finset.disjoint_left.1 hlr htl h
      have hsubr : r.subst t sub = r := Form.subst_id_of_notMem t sub htr_not
      have hdis_l : Disjoint (l.vars.erase t) sub.vars :=
        hdis.mono_left (Finset.erase_subset_erase t Finset.subset_union_left)
      have hdis_rs : Disjoint r.vars sub.vars := by
        refine hdis.mono_left (fun x hx => Finset.mem_erase.2 ⟨fun (e : x = t) => htr_not (e ▸ hx), Finset.mem_union_right _ hx⟩)
      obtain ⟨ro1, v1, n1⟩ := ihl hl htl hdis_l
      refine ⟨⟨ro1, by rw [hsubr]; exact hr, ?_⟩, ?_, ?_⟩
      · rw [v1, hsubr]
        exact Finset.disjoint_union_left.2 ⟨hlr.mono_left (Finset.erase_subset _ _), hdis_rs.symm⟩
      · simp only [Form.subst, Form.vars, v1, hsubr]
        ext x; simp only [Finset.mem_union, Finset.mem_erase]
        by_cases hxt : x = t
        · subst hxt; simp [htr_not]
        · tauto
      · simp [Form.subst, Form.nots, hsubr, n1]; omega
    · have htl_not : t ∉ l.vars := fun h => Finset.disjoint_left.1 hlr h htr
      have hsubl : l.subst t sub = l := Form.subst_id_of_notMem t sub htl_not
      have hdis_r : Disjoint (r.vars.erase t) sub.vars :=
        hdis.mono_left (Finset.erase_subset_erase t Finset.subset_union_right)
      have hdis_ls : Disjoint l.vars sub.vars := by
        refine hdis.mono_left (fun x hx => Finset.mem_erase.2 ⟨fun (e : x = t) => htl_not (e ▸ hx), Finset.mem_union_left _ hx⟩)
      obtain ⟨ro2, v2, n2⟩ := ihr hr htr hdis_r
      refine ⟨⟨by rw [hsubl]; exact hl, ro2, ?_⟩, ?_, ?_⟩
      · rw [v2, hsubl]
        exact Finset.disjoint_union_right.2 ⟨hlr.mono_right (Finset.erase_subset _ _), hdis_ls⟩
      · simp only [Form.subst, Form.vars, v2, hsubl]
        ext x; simp only [Finset.mem_union, Finset.mem_erase]
        by_cases hxt : x = t
        · subst hxt; simp [htl_not]
        · tauto
      · simp [Form.subst, Form.nots, hsubl, n2]; omega

theorem back_mono (o : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, GateMono g) :
    ∀ t, ∃ N : Finset ℕ, N.card ≤ 1 + gs.length ∧ Dep (fun x => run gs t x o) N ∧
      (N.card = 1 + gs.length → ∃ f : Form, f.ReadOnce ∧ f.nots = 0 ∧ f.vars = N ∧
        ∀ x, run gs t x o = f.eval x) := by
  induction gs with
  | nil =>
    intro t
    exact ⟨{o}, by simp, fun x y h => h o (by simp),
      fun _ => ⟨.var o, trivial, rfl, rfl, fun _ => rfl⟩⟩
  | cons g gs ih =>
    intro t
    have hg0 := hg g (by simp)
    obtain ⟨N, hc, hd, hf⟩ := ih (fun g' h => hg g' (List.mem_cons_of_mem _ h)) (t + 1)
    by_cases ht : t ∈ N
    · refine ⟨N.erase t ∪ g.inputs.toFinset, ?_, ?_, ?_⟩
      · have h1 := Finset.card_union_le (N.erase t) g.inputs.toFinset
        have h2 := Finset.card_erase_of_mem ht
        have h3 := List.toFinset_card_le g.inputs
        have h4 : 0 < N.card := Finset.card_pos.2 ⟨_, ht⟩
        have h5 := hg0.2
        rw [List.length_cons]; omega
      · intro x y h
        refine hd _ _ fun i hi => ?_
        by_cases hit : i = t
        · subst hit; simp only [Function.update_self]
          congr 1; apply List.map_congr_left
          intro a ha; exact h a (Finset.mem_union_right _ (List.mem_toFinset.2 ha))
        · simp only [Function.update_of_ne hit]
          exact h i (Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hit, hi⟩))
      · intro heq
        rw [List.length_cons] at heq
        have h1 := Finset.card_union_add_card_inter (N.erase t) g.inputs.toFinset
        have h2 := Finset.card_erase_of_mem ht
        have h3 := List.toFinset_card_le g.inputs
        have h4 : 0 < N.card := Finset.card_pos.2 ⟨_, ht⟩
        have h5 := hg0.2
        have hN : N.card = 1 + gs.length := by omega
        have hI : (N.erase t ∩ g.inputs.toFinset).card = 0 := by omega
        have hT : g.inputs.toFinset.card = 2 := by omega
        have hL : g.inputs.length = 2 := by omega
        obtain ⟨p, q, hpq⟩ := List.length_eq_two.1 hL
        rw [hpq] at hT hI
        have hne : p ≠ q := by rintro rfl; simp at hT
        have hdis : Disjoint (N.erase t) ({p, q} : Finset ℕ) := by
          rw [Finset.disjoint_iff_inter_eq_empty]
          simpa using Finset.card_eq_zero.1 hI
        obtain ⟨f, fro, fn0, fvs, fev⟩ := hf hN
        have hop := hg0.1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        rcases hop with hop | hop
        · let sub : Form := .and (.var p) (.var q)
          have hsub_ro : sub.ReadOnce := ⟨trivial, trivial, Finset.disjoint_singleton.2 hne⟩
          have hsub_v : sub.vars = ({p, q} : Finset ℕ) := by ext; simp [sub, Form.vars]
          obtain ⟨ro', v', n'⟩ := Form.subst_props t sub hsub_ro fro (fvs ▸ ht) (by rw [fvs, hsub_v]; exact hdis)
          refine ⟨f.subst t sub, ro', by simp [n', fn0, sub, Form.nots], ?_, fun x => ?_⟩
          · rw [v', fvs, hsub_v, hpq]; ext; simp
          · rw [Form.eval_subst, ← fev]; simp [run, hop, hpq, GateOp.eval, sub, Form.eval]
        · let sub : Form := .or (.var p) (.var q)
          have hsub_ro : sub.ReadOnce := ⟨trivial, trivial, Finset.disjoint_singleton.2 hne⟩
          have hsub_v : sub.vars = ({p, q} : Finset ℕ) := by ext; simp [sub, Form.vars]
          obtain ⟨ro', v', n'⟩ := Form.subst_props t sub hsub_ro fro (fvs ▸ ht) (by rw [fvs, hsub_v]; exact hdis)
          refine ⟨f.subst t sub, ro', by simp [n', fn0, sub, Form.nots], ?_, fun x => ?_⟩
          · rw [v', fvs, hsub_v, hpq]; ext; simp
          · rw [Form.eval_subst, ← fev]; simp [run, hop, hpq, GateOp.eval, sub, Form.eval]
    · refine ⟨N, by rw [List.length_cons]; omega, ?_, fun heq => by rw [List.length_cons] at heq; omega⟩
      intro x y h
      refine hd _ _ fun i hi => ?_
      have hit : i ≠ t := fun e => ht (e ▸ hi)
      simp only [Function.update_of_ne hit]; exact h i hi

theorem back_aon (o : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, GateAon g) :
    ∀ t,
      (∃ gs' : List Gate, (∀ g ∈ gs', GateMono g) ∧ gs'.length ≤ gs.length ∧
        ∀ x, run gs' t x o = run gs t x o)
      ∨
      (∃ N : Finset ℕ, N.card ≤ gs.length ∧ Dep (fun x => run gs t x o) N ∧
        (N.card = gs.length → ∃ f : Form, f.ReadOnce ∧ f.nots = 1 ∧ f.vars = N ∧
          ∀ x, run gs t x o = f.eval x)) := by
  induction gs with
  | nil =>
    intro t; left
    exact ⟨[], by simp, le_rfl, fun _ => rfl⟩
  | cons g gs ih =>
    intro t
    have hg0 := hg g (by simp)
    rcases ih (fun g' h => hg g' (List.mem_cons_of_mem _ h)) (t + 1) with
      ⟨gs', hgm', hlen', heq'⟩ | ⟨N, hc, hd, hf⟩
    · 
      have hop := hg0.1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with hop | hop | hop
      · left
        refine ⟨g :: gs', ?_, by simp; omega, fun x => by simp [run, heq']⟩
        intro d hd; rcases List.mem_cons.1 hd with rfl | hd
        · exact ⟨by simp [hop], hg0.2⟩
        · exact hgm' d hd
      · left
        refine ⟨g :: gs', ?_, by simp; omega, fun x => by simp [run, heq']⟩
        intro d hd; rcases List.mem_cons.1 hd with rfl | hd
        · exact ⟨by simp [hop], hg0.2⟩
        · exact hgm' d hd
      · 
        obtain ⟨N, hcN, hdN, hfN⟩ := back_mono o gs' hgm' (t + 1)
        by_cases ht : t ∈ N
        · cases hins : g.inputs with
          | nil =>
            
            left
            refine ⟨⟨GateOp.and, []⟩ :: gs', ?_, by simp; omega, fun x => ?_⟩
            · intro d hd; rcases List.mem_cons.1 hd with rfl | hd
              · exact ⟨by simp, by simp⟩
              · exact hgm' d hd
            · simp [run, hop, hins, GateOp.eval, heq']
          | cons p rest =>
            right
            refine ⟨N.erase t ∪ {p}, ?_, ?_, ?_⟩
            · have h1 := Finset.card_union_le (N.erase t) {p}
              have h2 := Finset.card_erase_of_mem ht
              have h4 : 0 < N.card := Finset.card_pos.2 ⟨_, ht⟩
              rw [Finset.card_singleton] at h1
              rw [List.length_cons]; omega
            · intro x y h
              simp only [run, ← heq']
              refine hdN _ _ fun i hi => ?_
              by_cases hit : i = t
              · subst hit; simp only [Function.update_self, hop, hins, GateOp.eval, List.map_cons, List.headD_cons]
                rw [h p (Finset.mem_union_right _ (Finset.mem_singleton_self _))]
              · simp only [Function.update_of_ne hit]
                exact h i (Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hit, hi⟩))
            · intro heq
              rw [List.length_cons] at heq
              have h1 := Finset.card_union_add_card_inter (N.erase t) {p}
              have h2 := Finset.card_erase_of_mem ht
              have h4 : 0 < N.card := Finset.card_pos.2 ⟨_, ht⟩
              rw [Finset.card_singleton] at h1
              have hN : N.card = 1 + gs'.length := by omega
              have hI : (N.erase t ∩ {p}).card = 0 := by omega
              have hdis : Disjoint (N.erase t) {p} := by
                rw [Finset.disjoint_iff_inter_eq_empty]; exact Finset.card_eq_zero.1 hI
              obtain ⟨f, fro, fn0, fvs, fev⟩ := hfN hN
              let sub : Form := .not (.var p)
              have hsub_ro : sub.ReadOnce := trivial
              have hsub_v : sub.vars = {p} := rfl
              obtain ⟨ro', v', n'⟩ := Form.subst_props t sub hsub_ro fro (fvs ▸ ht) (by rw [fvs, hsub_v]; exact hdis)
              refine ⟨f.subst t sub, ro', by simp [n', fn0, sub, Form.nots], by rw [v', fvs, hsub_v], fun x => ?_⟩
              rw [Form.eval_subst, ← fev, heq']
              simp [run, hop, hins, GateOp.eval, sub, Form.eval]
        · 
          left
          refine ⟨⟨GateOp.or, []⟩ :: gs', ?_, by simp; omega, fun x => ?_⟩
          · intro d hd; rcases List.mem_cons.1 hd with rfl | hd
            · exact ⟨by simp, by simp⟩
            · exact hgm' d hd
          · simp only [run, ← heq']
            refine hdN _ _ fun i hi => ?_
            have hit : i ≠ t := fun e => ht (e ▸ hi)
            simp [Function.update_of_ne hit]
    · 
      right
      by_cases ht : t ∈ N
      · have hop := hg0.1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        rcases hop with hop | hop | hop
        · 
          refine ⟨N.erase t ∪ g.inputs.toFinset, ?_, ?_, ?_⟩
          · have h1 := Finset.card_union_le (N.erase t) g.inputs.toFinset
            have h2 := Finset.card_erase_of_mem ht
            have h3 := List.toFinset_card_le g.inputs
            have h4 : 0 < N.card := Finset.card_pos.2 ⟨_, ht⟩
            have h5 := hg0.2
            rw [List.length_cons]; omega
          · intro x y h
            refine hd _ _ fun i hi => ?_
            by_cases hit : i = t
            · subst hit; simp only [Function.update_self]
              congr 1; apply List.map_congr_left
              intro a ha; exact h a (Finset.mem_union_right _ (List.mem_toFinset.2 ha))
            · simp only [Function.update_of_ne hit]
              exact h i (Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hit, hi⟩))
          · intro heq
            rw [List.length_cons] at heq
            have h1 := Finset.card_union_add_card_inter (N.erase t) g.inputs.toFinset
            have h2 := Finset.card_erase_of_mem ht
            have h3 := List.toFinset_card_le g.inputs
            have h4 : 0 < N.card := Finset.card_pos.2 ⟨_, ht⟩
            have h5 := hg0.2
            have hN : N.card = gs.length := by omega
            have hI : (N.erase t ∩ g.inputs.toFinset).card = 0 := by omega
            have hT : g.inputs.toFinset.card = 2 := by omega
            have hL : g.inputs.length = 2 := by omega
            obtain ⟨p, q, hpq⟩ := List.length_eq_two.1 hL
            rw [hpq] at hT hI
            have hne : p ≠ q := by rintro rfl; simp at hT
            have hdis : Disjoint (N.erase t) ({p, q} : Finset ℕ) := by
              rw [Finset.disjoint_iff_inter_eq_empty]
              simpa using Finset.card_eq_zero.1 hI
            obtain ⟨f, fro, fn1, fvs, fev⟩ := hf hN
            let sub : Form := .and (.var p) (.var q)
            have hsub_ro : sub.ReadOnce := ⟨trivial, trivial, Finset.disjoint_singleton.2 hne⟩
            have hsub_v : sub.vars = ({p, q} : Finset ℕ) := by ext; simp [sub, Form.vars]
            obtain ⟨ro', v', n'⟩ := Form.subst_props t sub hsub_ro fro (fvs ▸ ht) (by rw [fvs, hsub_v]; exact hdis)
            refine ⟨f.subst t sub, ro', by simp [n', fn1, sub, Form.nots], ?_, fun x => ?_⟩
            · rw [v', fvs, hsub_v, hpq]; ext; simp
            · rw [Form.eval_subst, ← fev]; simp [run, hop, hpq, GateOp.eval, sub, Form.eval]
        · 
          refine ⟨N.erase t ∪ g.inputs.toFinset, ?_, ?_, ?_⟩
          · have h1 := Finset.card_union_le (N.erase t) g.inputs.toFinset
            have h2 := Finset.card_erase_of_mem ht
            have h3 := List.toFinset_card_le g.inputs
            have h4 : 0 < N.card := Finset.card_pos.2 ⟨_, ht⟩
            have h5 := hg0.2
            rw [List.length_cons]; omega
          · intro x y h
            refine hd _ _ fun i hi => ?_
            by_cases hit : i = t
            · subst hit; simp only [Function.update_self]
              congr 1; apply List.map_congr_left
              intro a ha; exact h a (Finset.mem_union_right _ (List.mem_toFinset.2 ha))
            · simp only [Function.update_of_ne hit]
              exact h i (Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hit, hi⟩))
          · intro heq
            rw [List.length_cons] at heq
            have h1 := Finset.card_union_add_card_inter (N.erase t) g.inputs.toFinset
            have h2 := Finset.card_erase_of_mem ht
            have h3 := List.toFinset_card_le g.inputs
            have h4 : 0 < N.card := Finset.card_pos.2 ⟨_, ht⟩
            have h5 := hg0.2
            have hN : N.card = gs.length := by omega
            have hI : (N.erase t ∩ g.inputs.toFinset).card = 0 := by omega
            have hT : g.inputs.toFinset.card = 2 := by omega
            have hL : g.inputs.length = 2 := by omega
            obtain ⟨p, q, hpq⟩ := List.length_eq_two.1 hL
            rw [hpq] at hT hI
            have hne : p ≠ q := by rintro rfl; simp at hT
            have hdis : Disjoint (N.erase t) ({p, q} : Finset ℕ) := by
              rw [Finset.disjoint_iff_inter_eq_empty]
              simpa using Finset.card_eq_zero.1 hI
            obtain ⟨f, fro, fn1, fvs, fev⟩ := hf hN
            let sub : Form := .or (.var p) (.var q)
            have hsub_ro : sub.ReadOnce := ⟨trivial, trivial, Finset.disjoint_singleton.2 hne⟩
            have hsub_v : sub.vars = ({p, q} : Finset ℕ) := by ext; simp [sub, Form.vars]
            obtain ⟨ro', v', n'⟩ := Form.subst_props t sub hsub_ro fro (fvs ▸ ht) (by rw [fvs, hsub_v]; exact hdis)
            refine ⟨f.subst t sub, ro', by simp [n', fn1, sub, Form.nots], ?_, fun x => ?_⟩
            · rw [v', fvs, hsub_v, hpq]; ext; simp
            · rw [Form.eval_subst, ← fev]; simp [run, hop, hpq, GateOp.eval, sub, Form.eval]
        · 
          refine ⟨N.erase t ∪ (effective g).toFinset, ?_, ?_, fun heq => ?_⟩
          · have h1 := Finset.card_union_le (N.erase t) (effective g).toFinset
            have h2 := Finset.card_erase_of_mem ht
            have h3 := List.toFinset_card_le (effective g)
            have h4 : 0 < N.card := Finset.card_pos.2 ⟨_, ht⟩
            have h5 : (effective g).length ≤ 1 := by simp [effective, hop]
            rw [List.length_cons]; omega
          · intro x y h
            refine hd _ _ fun i hi => ?_
            by_cases hit : i = t
            · subst hit; simp only [Function.update_self]
              rw [gate_effective g, gate_effective g y]
              congr 1; apply List.map_congr_left
              intro a ha; exact h a (Finset.mem_union_right _ (List.mem_toFinset.2 ha))
            · simp only [Function.update_of_ne hit]
              exact h i (Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hit, hi⟩))
          · have h1 := Finset.card_union_le (N.erase t) (effective g).toFinset
            have h2 := Finset.card_erase_of_mem ht
            have h3 := List.toFinset_card_le (effective g)
            have h4 : 0 < N.card := Finset.card_pos.2 ⟨_, ht⟩
            have h5 : (effective g).length ≤ 1 := by simp [effective, hop]
            rw [List.length_cons] at heq; omega
      · refine ⟨N, by rw [List.length_cons]; omega, ?_, fun heq => by rw [List.length_cons] at heq; omega⟩
        intro x y h
        refine hd _ _ fun i hi => ?_
        have hit : i ≠ t := fun e => ht (e ▸ hi)
        simp only [Function.update_of_ne hit]; exact h i hi

structure MonoNF (n m : ℕ) where
  S0 : Finset (Fin n)
  T0 : Finset (Fin m)
  rects : List (Finset (Fin n) × Finset (Fin m))

def MonoNF.eval {n m : ℕ} (nf : MonoNF n m) (u : Fin n) (v : Fin m) : Bool :=
  decide (u ∈ nf.S0 ∨ v ∈ nf.T0 ∨ ∃ p ∈ nf.rects, u ∈ p.1 ∧ v ∈ p.2)

def MonoNF.Valid {n m : ℕ} (X : Finset (Fin n)) (Y : Finset (Fin m)) (nf : MonoNF n m) : Prop :=
  nf.S0 ⊆ X ∧ nf.T0 ⊆ Y ∧
  (∀ p ∈ nf.rects, p.1.Nonempty ∧ p.2.Nonempty ∧ p.1 ⊆ X ∧ p.2 ⊆ Y ∧
    Disjoint p.1 nf.S0 ∧ Disjoint p.2 nf.T0) ∧
  nf.rects.Pairwise (fun p q => Disjoint p.1 q.1 ∧ Disjoint p.2 q.2)

def oneEachFn {n m : ℕ} (u : Fin n) (v : Fin m) : ℕ → Bool :=
  fun i => decide (i = u.val ∨ i = n + v.val)

def rowVars (n : ℕ) (V : Finset ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun u : Fin n => u.val ∈ V

def colVars (n m : ℕ) (V : Finset ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun v : Fin m => n + v.val ∈ V

theorem card_row_add_col (n m : ℕ) (V : Finset ℕ) (hV : ∀ i ∈ V, i < n + m) :
    (rowVars n V).card + (colVars n m V).card = V.card := by
  have h1 : (rowVars n V).image (fun u : Fin n => u.val) ∪
            (colVars n m V).image (fun v : Fin m => n + v.val) = V := by
    ext i
    simp only [Finset.mem_union, Finset.mem_image, rowVars, colVars, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro (⟨u, hu, rfl⟩ | ⟨v, hv, rfl⟩) <;> assumption
    · intro hi
      have hlt := hV i hi
      by_cases h : i < n
      · left; exact ⟨⟨i, h⟩, hi, rfl⟩
      · right; exact ⟨⟨i - n, by omega⟩, by simpa [show n + (i - n) = i by omega] using hi, by simp; omega⟩
  have hdis : Disjoint ((rowVars n V).image (fun u : Fin n => u.val))
                       ((colVars n m V).image (fun v : Fin m => n + v.val)) := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.1 hi1
    obtain ⟨v, _, hv⟩ := Finset.mem_image.1 hi2
    have := u.isLt; omega
  conv_rhs => rw [← h1]
  rw [Finset.card_union_of_disjoint hdis,
      Finset.card_image_of_injective _ (fun a b h => Fin.ext h),
      Finset.card_image_of_injective _ (fun a b h => Fin.ext (by simpa using h))]

theorem rowVars_disjoint (n : ℕ) {A B : Finset ℕ} (h : Disjoint A B) :
    Disjoint (rowVars n A) (rowVars n B) := by
  rw [Finset.disjoint_left]
  intro u h1 h2
  exact Finset.disjoint_left.1 h (Finset.mem_filter.1 h1).2 (Finset.mem_filter.1 h2).2

theorem colVars_disjoint (n m : ℕ) {A B : Finset ℕ} (h : Disjoint A B) :
    Disjoint (colVars n m A) (colVars n m B) := by
  rw [Finset.disjoint_left]
  intro v h1 h2
  exact Finset.disjoint_left.1 h (Finset.mem_filter.1 h1).2 (Finset.mem_filter.1 h2).2

theorem mono_normal_form (n m : ℕ) : ∀ (h : Form), h.ReadOnce → h.nots = 0 →
    (∀ i ∈ h.vars, i < n + m) →
    ∃ nf : MonoNF n m, nf.Valid (rowVars n h.vars) (colVars n m h.vars) ∧
      ∀ (u : Fin n) (v : Fin m), h.eval (oneEachFn u v) = nf.eval u v := by
  intro h
  induction h with
  | var w =>
    intro _ _ hw
    have hlt := hw w (by simp [Form.vars])
    by_cases h1 : w < n
    · refine ⟨⟨{⟨w, h1⟩}, ∅, []⟩, ?_, fun u v => ?_⟩
      · refine ⟨?_, by simp, by simp, by simp⟩
        intro a ha; simp only [Finset.mem_singleton] at ha; subst ha
        simp [rowVars, Form.vars]
      · simp only [Form.eval, oneEachFn, MonoNF.eval, Finset.mem_singleton, Finset.notMem_empty,
          List.not_mem_nil, false_and, exists_false, or_false, Fin.ext_iff, decide_eq_decide]
        have := v.isLt; omega
    · refine ⟨⟨∅, {⟨w - n, by omega⟩}, []⟩, ?_, fun u v => ?_⟩
      · refine ⟨by simp, ?_, by simp, by simp⟩
        intro b hb; simp only [Finset.mem_singleton] at hb; subst hb
        simp [colVars, Form.vars, show n + (w - n) = w by omega]
      · simp only [Form.eval, oneEachFn, MonoNF.eval, Finset.mem_singleton, Finset.notMem_empty,
          List.not_mem_nil, false_and, exists_false, false_or, or_false, Fin.ext_iff, decide_eq_decide]
        have := u.isLt; omega
  | not f _ => intro _ hn; simp [Form.nots] at hn
  | or l r ihl ihr =>
    intro ⟨hl, hr, hdis⟩ hn hw
    have hnl : l.nots = 0 := by simp [Form.nots] at hn; omega
    have hnr : r.nots = 0 := by simp [Form.nots] at hn; omega
    obtain ⟨nf1, hv1, he1⟩ := ihl hl hnl (fun i hi => hw i (Finset.mem_union_left _ hi))
    obtain ⟨nf2, hv2, he2⟩ := ihr hr hnr (fun i hi => hw i (Finset.mem_union_right _ hi))
    have hdX := rowVars_disjoint n hdis
    have hdY := colVars_disjoint n m hdis
    have hXl : rowVars n l.vars ⊆ rowVars n (l.vars ∪ r.vars) :=
      fun u hu => Finset.mem_filter.2 ⟨Finset.mem_univ _, Finset.mem_union_left _ (Finset.mem_filter.1 hu).2⟩
    have hXr : rowVars n r.vars ⊆ rowVars n (l.vars ∪ r.vars) :=
      fun u hu => Finset.mem_filter.2 ⟨Finset.mem_univ _, Finset.mem_union_right _ (Finset.mem_filter.1 hu).2⟩
    have hYl : colVars n m l.vars ⊆ colVars n m (l.vars ∪ r.vars) :=
      fun v hv => Finset.mem_filter.2 ⟨Finset.mem_univ _, Finset.mem_union_left _ (Finset.mem_filter.1 hv).2⟩
    have hYr : colVars n m r.vars ⊆ colVars n m (l.vars ∪ r.vars) :=
      fun v hv => Finset.mem_filter.2 ⟨Finset.mem_univ _, Finset.mem_union_right _ (Finset.mem_filter.1 hv).2⟩
    refine ⟨⟨nf1.S0 ∪ nf2.S0, nf1.T0 ∪ nf2.T0, nf1.rects ++ nf2.rects⟩, ?_, fun u v => ?_⟩
    · refine ⟨Finset.union_subset (hv1.1.trans hXl) (hv2.1.trans hXr),
              Finset.union_subset (hv1.2.1.trans hYl) (hv2.2.1.trans hYr), ?_, ?_⟩
      · intro p hp
        rcases List.mem_append.1 hp with hp | hp
        · obtain ⟨ne1, ne2, sub1, sub2, d1, d2⟩ := hv1.2.2.1 p hp
          exact ⟨ne1, ne2, sub1.trans hXl, sub2.trans hYl,
            Finset.disjoint_union_right.2 ⟨d1, hdX.mono sub1 hv2.1⟩,
            Finset.disjoint_union_right.2 ⟨d2, hdY.mono sub2 hv2.2.1⟩⟩
        · obtain ⟨ne1, ne2, sub1, sub2, d1, d2⟩ := hv2.2.2.1 p hp
          exact ⟨ne1, ne2, sub1.trans hXr, sub2.trans hYr,
            Finset.disjoint_union_right.2 ⟨hdX.symm.mono sub1 hv1.1, d1⟩,
            Finset.disjoint_union_right.2 ⟨hdY.symm.mono sub2 hv1.2.1, d2⟩⟩
      · rw [List.pairwise_append]
        refine ⟨hv1.2.2.2, hv2.2.2.2, fun p hp q hq => ?_⟩
        obtain ⟨_, _, sp1, sp2, _, _⟩ := hv1.2.2.1 p hp
        obtain ⟨_, _, sq1, sq2, _, _⟩ := hv2.2.2.1 q hq
        exact ⟨hdX.mono sp1 sq1, hdY.mono sp2 sq2⟩
    · simp only [Form.eval, he1, he2, MonoNF.eval]
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_eq, Finset.mem_union, List.mem_append]
      constructor
      · rintro ((h | h | ⟨p, hp, h1, h2⟩) | (h | h | ⟨p, hp, h1, h2⟩))
        · exact Or.inl (Or.inl h)
        · exact Or.inr (Or.inl (Or.inl h))
        · exact Or.inr (Or.inr ⟨p, Or.inl hp, h1, h2⟩)
        · exact Or.inl (Or.inr h)
        · exact Or.inr (Or.inl (Or.inr h))
        · exact Or.inr (Or.inr ⟨p, Or.inr hp, h1, h2⟩)
      · rintro ((h | h) | (h | h) | ⟨p, hp | hp, h1, h2⟩)
        · exact Or.inl (Or.inl h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inl (Or.inr (Or.inr ⟨p, hp, h1, h2⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨p, hp, h1, h2⟩))
  | and l r ihl ihr =>
    intro ⟨hl, hr, hdis⟩ hn hw
    have hnl : l.nots = 0 := by simp [Form.nots] at hn; omega
    have hnr : r.nots = 0 := by simp [Form.nots] at hn; omega
    obtain ⟨nf1, hv1, he1⟩ := ihl hl hnl (fun i hi => hw i (Finset.mem_union_left _ hi))
    obtain ⟨nf2, hv2, he2⟩ := ihr hr hnr (fun i hi => hw i (Finset.mem_union_right _ hi))
    have hdX := rowVars_disjoint n hdis
    have hdY := colVars_disjoint n m hdis
    have hXl : rowVars n l.vars ⊆ rowVars n (l.vars ∪ r.vars) :=
      fun u hu => Finset.mem_filter.2 ⟨Finset.mem_univ _, Finset.mem_union_left _ (Finset.mem_filter.1 hu).2⟩
    have hXr : rowVars n r.vars ⊆ rowVars n (l.vars ∪ r.vars) :=
      fun u hu => Finset.mem_filter.2 ⟨Finset.mem_univ _, Finset.mem_union_right _ (Finset.mem_filter.1 hu).2⟩
    have hYl : colVars n m l.vars ⊆ colVars n m (l.vars ∪ r.vars) :=
      fun v hv => Finset.mem_filter.2 ⟨Finset.mem_univ _, Finset.mem_union_left _ (Finset.mem_filter.1 hv).2⟩
    have hYr : colVars n m r.vars ⊆ colVars n m (l.vars ∪ r.vars) :=
      fun v hv => Finset.mem_filter.2 ⟨Finset.mem_univ _, Finset.mem_union_right _ (Finset.mem_filter.1 hv).2⟩
    
    let r1 : List (Finset (Fin n) × Finset (Fin m)) :=
      if nf1.S0.Nonempty ∧ nf2.T0.Nonempty then [(nf1.S0, nf2.T0)] else []
    let r2 : List (Finset (Fin n) × Finset (Fin m)) :=
      if nf2.S0.Nonempty ∧ nf1.T0.Nonempty then [(nf2.S0, nf1.T0)] else []
    refine ⟨⟨∅, ∅, r1 ++ r2⟩, ?_, fun u v => ?_⟩
    · refine ⟨by simp, by simp, ?_, ?_⟩
      · intro p hp
        rcases List.mem_append.1 hp with hp | hp
        · simp only [r1] at hp
          split_ifs at hp with hc
          · simp only [List.mem_singleton] at hp; subst hp
            exact ⟨hc.1, hc.2, hv1.1.trans hXl, hv2.2.1.trans hYr, by simp, by simp⟩
          · simp at hp
        · simp only [r2] at hp
          split_ifs at hp with hc
          · simp only [List.mem_singleton] at hp; subst hp
            exact ⟨hc.1, hc.2, hv2.1.trans hXr, hv1.2.1.trans hYl, by simp, by simp⟩
          · simp at hp
      · rw [List.pairwise_append]
        refine ⟨by simp only [r1]; split_ifs <;> simp, by simp only [r2]; split_ifs <;> simp, ?_⟩
        intro p hp q hq
        simp only [r1] at hp; simp only [r2] at hq
        split_ifs at hp with h1
        · split_ifs at hq with h2
          · simp only [List.mem_singleton] at hp hq; subst hp; subst hq
            exact ⟨hdX.mono hv1.1 hv2.1, hdY.symm.mono hv2.2.1 hv1.2.1⟩
          · simp at hq
        · simp at hp
    · simp only [Form.eval, he1, he2, MonoNF.eval]
      rw [Bool.eq_iff_iff]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨h1, h2⟩
        have notBothL : ∀ u, u ∈ rowVars n l.vars → u ∈ rowVars n r.vars → False :=
          fun u a b => Finset.disjoint_left.1 hdX a b
        have notBothR : ∀ v, v ∈ colVars n m l.vars → v ∈ colVars n m r.vars → False :=
          fun v a b => Finset.disjoint_left.1 hdY a b
        have h1X : ∀ p ∈ nf1.rects, u ∈ p.1 → u ∈ rowVars n l.vars :=
          fun p hp hu => (hv1.2.2.1 p hp).2.2.1 hu
        have h1Y : ∀ p ∈ nf1.rects, v ∈ p.2 → v ∈ colVars n m l.vars :=
          fun p hp hv => (hv1.2.2.1 p hp).2.2.2.1 hv
        have h2X : ∀ p ∈ nf2.rects, u ∈ p.1 → u ∈ rowVars n r.vars :=
          fun p hp hu => (hv2.2.2.1 p hp).2.2.1 hu
        have h2Y : ∀ p ∈ nf2.rects, v ∈ p.2 → v ∈ colVars n m r.vars :=
          fun p hp hv => (hv2.2.2.1 p hp).2.2.2.1 hv
        rcases h1 with hu1 | hv1' | ⟨p1, hp1, hu1, hv1'⟩ <;>
        rcases h2 with hu2 | hv2' | ⟨p2, hp2, hu2, hv2'⟩
        · exact (notBothL u (hv1.1 hu1) (hv2.1 hu2)).elim
        · right; right; refine ⟨(nf1.S0, nf2.T0), List.mem_append_left _ ?_, hu1, hv2'⟩
          simp [r1, show nf1.S0.Nonempty from ⟨u, hu1⟩, show nf2.T0.Nonempty from ⟨v, hv2'⟩]
        · exact (notBothL u (hv1.1 hu1) (h2X p2 hp2 hu2)).elim
        · right; right; refine ⟨(nf2.S0, nf1.T0), List.mem_append_right _ ?_, hu2, hv1'⟩
          simp [r2, show nf2.S0.Nonempty from ⟨u, hu2⟩, show nf1.T0.Nonempty from ⟨v, hv1'⟩]
        · exact (notBothR v (hv1.2.1 hv1') (hv2.2.1 hv2')).elim
        · exact (notBothR v (hv1.2.1 hv1') (h2Y p2 hp2 hv2')).elim
        · exact (notBothL u (h1X p1 hp1 hu1) (hv2.1 hu2)).elim
        · exact (notBothR v (h1Y p1 hp1 hv1') (hv2.2.1 hv2')).elim
        · exact (notBothL u (h1X p1 hp1 hu1) (h2X p2 hp2 hu2)).elim
      · rintro (h | h | ⟨p, hp, hu, hv⟩)
        · simp at h
        · simp at h
        · rcases List.mem_append.1 hp with hp | hp
          · simp only [r1] at hp; split_ifs at hp
            · simp only [List.mem_singleton] at hp; subst hp
              exact ⟨Or.inl hu, Or.inr (Or.inl hv)⟩
            · simp at hp
          · simp only [r2] at hp; split_ifs at hp
            · simp only [List.mem_singleton] at hp; subst hp
              exact ⟨Or.inr (Or.inl hv), Or.inl hu⟩
            · simp at hp

theorem mem_foldr_union_iff {α : Type*} [DecidableEq α] (a : α) :
    ∀ (Ss : List (Finset α)), a ∈ Ss.foldr (· ∪ ·) ∅ ↔ ∃ S ∈ Ss, a ∈ S
  | [] => by simp
  | S :: Ss => by
    simp only [List.foldr_cons, Finset.mem_union, List.mem_cons, exists_eq_or_imp]
    rw [mem_foldr_union_iff a Ss]

theorem length_le_sum_card {α : Type*} :
    ∀ (Ss : List (Finset α)), (∀ S ∈ Ss, S.Nonempty) → Ss.length ≤ (Ss.map Finset.card).sum
  | [], _ => by simp
  | S :: Ss, h => by
    have h1 : 1 ≤ S.card := Finset.card_pos.2 (h S (by simp))
    have h2 := length_le_sum_card Ss fun T hT => h T (List.mem_cons_of_mem _ hT)
    simp only [List.length_cons, List.map_cons, List.sum_cons]; omega


end PEqualNP.Outside.L_meta_29938_aux

open PEqualNP.Outside.L_meta_29938_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

namespace PEqualNP.Outside.L_meta_29938_aux

theorem threshold_shape {n m s : Nat} (A : Fin n → Fin m → Bool)
    (hn : 2 ≤ n) (hm : 2 ≤ m) (hr : Function.Injective A)
    (hc : Function.Injective (fun j i => A i j)) (budget : s + 2 ≤ n + m)
    (C : Circuit) (hC : FanInTwo C) (hs0 : C.size ≤ s) (hR : Represents A C) :
    RepSizeAtMost A s ∨
      (s + 2 = n + m ∧ C.size = s ∧
       ∃ f : Form, f.ReadOnce ∧ f.nots = 1 ∧ f.vars.card = s ∧
          (∀ i ∈ f.vars, i < n + m) ∧ (rowVars n f.vars).card + 1 = n ∧
          (colVars n m f.vars).card + 1 = m ∧ ∀ u v, f.eval (oneEachFn u v) = A u v) := by
  classical
  have hrow : ∀ u u' : Fin n, (∀ v : Fin m, A u v = A u' v) → u = u' :=
    fun u u' h => hr (funext h)
  have hcol : ∀ v v' : Fin m, (∀ u : Fin n, A u v = A u v') → v = v' :=
    fun v v' h => hc (funext h)
  have hs : C.size ≤ n + m - 2 := by omega
  have hCeval : ∀ u v, run C.gates (n + m) (oneEachFn u v) C.output = A u v := by
    intro u v
    have := hR u v
    rw [← this]
    change run C.gates (n + m) (oneEachFn u v) C.output = (wiresFrom C.gates (oneEach u v)).getD C.output false
    rw [run_eq, oneEach_len]
    congr 2; funext i; exact (oneEach_getD u v i).symm
  rcases back_aon C.output C.gates hC (n + m) with ⟨gs', hgm', hlen', heq'⟩ | ⟨N, hcN, hdN, hfN⟩
  · 
    have hC' : Monotone2 ⟨gs', C.output⟩ := hgm'
    have hR' : Represents A ⟨gs', C.output⟩ := by
      intro u v
      change (wiresFrom gs' (oneEach u v)).getD C.output false = A u v
      rw [run_eq, oneEach_len]
      have hfn : (fun j => (oneEach u v).getD j false) = oneEachFn u v := by
        funext i; exact oneEach_getD u v i
      rw [hfn, heq', hCeval]
    left
    refine ⟨⟨gs', C.output⟩, hC', ?_, hR'⟩
    change gs'.length ≤ s
    exact hlen'.trans hs0
  · 
    
    have hrow_miss : ∀ u u' : Fin n, u.val ∉ N → u'.val ∉ N → u = u' := by
      intro u u' hu hu'
      apply hrow u u'; intro v
      rw [← hCeval u v, ← hCeval u' v]
      refine hdN _ _ fun i hi => ?_
      have hiu : i ≠ u.val := fun (e : i = u.val) => hu (e ▸ hi)
      have hiu' : i ≠ u'.val := fun (e : i = u'.val) => hu' (e ▸ hi)
      simp [oneEachFn, hiu, hiu']
    have hcol_miss : ∀ v v' : Fin m, n + v.val ∉ N → n + v'.val ∉ N → v = v' := by
      intro v v' hv hv'
      apply hcol v v'; intro u
      rw [← hCeval u v, ← hCeval u v']
      refine hdN _ _ fun i hi => ?_
      have hiv : i ≠ n + v.val := fun (e : i = n + v.val) => hv (e ▸ hi)
      have hiv' : i ≠ n + v'.val := fun (e : i = n + v'.val) => hv' (e ▸ hi)
      simp [oneEachFn, hiv, hiv']
    have hRL_ge : n - 1 ≤ (rowVars n N).card := by
      have hcomp : (Finset.univ \ rowVars n N).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, rowVars, Finset.mem_filter] at ha hb
        exact hrow_miss a b ha hb
      have hadd := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (rowVars n N))
      simp only [Finset.card_univ, Fintype.card_fin] at hadd; omega
    have hCR_ge : m - 1 ≤ (colVars n m N).card := by
      have hcomp : (Finset.univ \ colVars n m N).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, colVars, Finset.mem_filter] at ha hb
        exact hcol_miss a b ha hb
      have hadd := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (colVars n m N))
      simp only [Finset.card_univ, Fintype.card_fin] at hadd; omega
    have hsubN : (rowVars n N).image (fun u : Fin n => u.val) ∪
                 (colVars n m N).image (fun v : Fin m => n + v.val) ⊆ N := by
      intro i hi
      rcases Finset.mem_union.1 hi with hi | hi
      · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hi; exact (Finset.mem_filter.1 hu).2
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hi; exact (Finset.mem_filter.1 hv).2
    have hdisN : Disjoint ((rowVars n N).image (fun u : Fin n => u.val))
                          ((colVars n m N).image (fun v : Fin m => n + v.val)) := by
      rw [Finset.disjoint_left]; intro i h1 h2
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.1 h1
      obtain ⟨v, _, hv⟩ := Finset.mem_image.1 h2
      have := u.isLt; omega
    have hcard_sub := Finset.card_le_card hsubN
    rw [Finset.card_union_of_disjoint hdisN,
        Finset.card_image_of_injective _ (fun a b h => Fin.ext h),
        Finset.card_image_of_injective _ (fun a b h => Fin.ext (by simpa using h))] at hcard_sub
    have hsz : C.gates.length ≤ n + m - 2 := hs
    have hNeq : N.card = C.gates.length := by omega
    have hNnm : N.card = n + m - 2 := by omega
    have hRL_eq : (rowVars n N).card = n - 1 := by omega
    have hCR_eq : (colVars n m N).card = m - 1 := by omega
    
    have hN_eq_union : (rowVars n N).image (fun u : Fin n => u.val) ∪
                       (colVars n m N).image (fun v : Fin m => n + v.val) = N := by
      refine Finset.eq_of_subset_of_card_le hsubN ?_
      rw [Finset.card_union_of_disjoint hdisN,
          Finset.card_image_of_injective _ (fun a b h => Fin.ext h),
          Finset.card_image_of_injective _ (fun a b h => Fin.ext (by simpa using h))]
      omega
    have hN_lt : ∀ i ∈ N, i < n + m := by
      intro i hi
      rw [← hN_eq_union] at hi
      rcases Finset.mem_union.1 hi with hi | hi
      · obtain ⟨u, _, rfl⟩ := Finset.mem_image.1 hi; have := u.isLt; omega
      · obtain ⟨v, _, rfl⟩ := Finset.mem_image.1 hi; have := v.isLt; omega
    
    obtain ⟨f, fro, fn1, fvs, fev⟩ := hfN hNeq
    have hlen0 : C.gates.length ≤ s := hs0
    right
    refine ⟨by omega, by change C.gates.length = s; omega, f, fro, fn1, ?_, ?_, ?_, ?_, ?_⟩
    · rw [fvs]; omega
    · simpa only [fvs] using hN_lt
    · rw [fvs, hRL_eq]; omega
    · rw [fvs, hCR_eq]; omega
    · intro u v
      rw [← fev, hCeval]

theorem subthreshold {n m s : Nat} (A : Fin n → Fin m → Bool)
    (hn : 2 ≤ n) (hm : 2 ≤ m) (hr : Function.Injective A)
    (hc : Function.Injective (fun j i => A i j)) (budget : s + 3 ≤ n + m)
    (h : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ s ∧ Represents A C) :
    RepSizeAtMost A s := by
  obtain ⟨C, hC, hs0, hR⟩ := h
  rcases threshold_shape A hn hm hr hc (by omega : s + 2 ≤ n + m) C hC hs0 hR with mono | ⟨eq, _⟩
  · exact mono
  · omega

end PEqualNP.Outside.L_meta_29938_aux

open PEqualNP.Outside.L_meta_29938_aux

namespace PEqualNP.Outside.L_meta_29938_aux

abbrev Region := Option Form

def Region.eval (a : Region) (x : Nat → Bool) : Bool :=
  match a with | none => false | some f => f.eval x

def Region.vars (a : Region) : Finset Nat :=
  match a with | none => ∅ | some f => f.vars

def Region.Good (a : Region) : Prop :=
  match a with | none => True | some f => f.ReadOnce ∧ f.nots = 0

def Region.join (a b : Region) : Region :=
  match a, b with
  | none, t => t
  | t, none => t
  | some l, some r => some (.or l r)

def Region.meet (a b : Region) : Region :=
  match a, b with
  | some l, some r => some (.and l r)
  | _, _ => none

theorem Region.join_vars (a b : Region) : (a.join b).vars = a.vars ∪ b.vars := by
  cases a <;> cases b <;> simp [Region.join, Region.vars, Form.vars]

theorem Region.meet_vars (a b : Region) : (a.meet b).vars ⊆ a.vars ∪ b.vars := by
  cases a <;> cases b <;> simp [Region.meet, Region.vars, Form.vars]

theorem Region.join_eval (a b : Region) (x : Nat → Bool) :
    (a.join b).eval x = (a.eval x || b.eval x) := by
  cases a <;> cases b <;> simp [Region.join, Region.eval, Form.eval]

theorem Region.meet_eval (a b : Region) (x : Nat → Bool) :
    (a.meet b).eval x = (a.eval x && b.eval x) := by
  cases a <;> cases b <;> simp [Region.meet, Region.eval, Form.eval]

theorem Region.join_good {a b : Region} (ha : a.Good) (hb : b.Good) (d : Disjoint a.vars b.vars) :
    (a.join b).Good := by
  cases a <;> cases b <;> simp_all [Region.join, Region.Good, Region.vars, Form.ReadOnce, Form.nots]

theorem Region.meet_good {a b : Region} (ha : a.Good) (hb : b.Good) (d : Disjoint a.vars b.vars) :
    (a.meet b).Good := by
  cases a <;> cases b <;> simp_all [Region.meet, Region.Good, Region.vars, Form.ReadOnce, Form.nots]

theorem Region.witness {a : Region} (h : a.Good) {x : Nat → Bool} (hit : a.eval x = true) :
    ∃ i ∈ a.vars, x i = true := by
  cases a with
  | none => simp [Region.eval] at hit
  | some f =>
    change f.eval x = true at hit
    change ∃ i ∈ f.vars, x i = true
    have z : f.nots = 0 := h.2
    clear h
    induction f with
    | var w => exact ⟨w, by simp [Form.vars], hit⟩
    | not g ih => simp [Form.nots] at z
    | and a b ia ib =>
      simp only [Form.nots, Nat.add_eq_zero_iff] at z
      simp only [Form.eval, Bool.and_eq_true] at hit
      obtain ⟨i, hi, hv⟩ := ia hit.1 z.1
      exact ⟨i, Finset.mem_union_left _ hi, hv⟩
    | or a b ia ib =>
      simp only [Form.nots, Nat.add_eq_zero_iff] at z
      simp only [Form.eval, Bool.or_eq_true] at hit
      rcases hit with ha | hb
      · obtain ⟨i, hi, hv⟩ := ia ha z.1
        exact ⟨i, Finset.mem_union_left _ hi, hv⟩
      · obtain ⟨i, hi, hv⟩ := ib hb z.2
        exact ⟨i, Finset.mem_union_right _ hi, hv⟩

def TwoSparse (x : Nat → Bool) : Prop :=
  ∀ i j k, x i = true → x j = true → x k = true → i = j ∨ i = k ∨ j = k

theorem oneEach_sparse {n m} (u : Fin n) (v : Fin m) : TwoSparse (oneEachFn u v) := by
  intro i j k hi hj hk
  simp only [oneEachFn, decide_eq_true_eq] at hi hj hk
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> rcases hk with rfl | rfl <;> simp

theorem not_three {a b c : Region} (ha : a.Good) (hb : b.Good) (hc : c.Good)
    (ab : Disjoint a.vars b.vars) (ac : Disjoint a.vars c.vars) (bc : Disjoint b.vars c.vars)
    {x : Nat → Bool} (sp : TwoSparse x) (va : a.eval x = true) (vb : b.eval x = true)
    (vc : c.eval x = true) : False := by
  obtain ⟨i, hi, ei⟩ := Region.witness ha va
  obtain ⟨j, hj, ej⟩ := Region.witness hb vb
  obtain ⟨k, hk, ek⟩ := Region.witness hc vc
  rcases sp i j k ei ej ek with e | e | e
  · exact Finset.disjoint_left.1 ab hi (e ▸ hj)
  · exact Finset.disjoint_left.1 ac hi (e ▸ hk)
  · exact Finset.disjoint_left.1 bc hj (e ▸ hk)

def Region.Fits (r : Region) (S : Finset Nat) := r.Good ∧ r.vars ⊆ S

def MaskView (S : Finset Nat) (F : (Nat → Bool) → Bool) : Prop :=
  (∃ g : Region, g.Fits S ∧ ∀ x, TwoSparse x → F x = g.eval x) ∨
  (∃ b u : Region, b.Fits S ∧ u.Fits S ∧ Disjoint b.vars u.vars ∧
      ∀ x, TwoSparse x → F x = (!(b.eval x) || u.eval x)) ∨
  (∃ p b w : Region, p.Fits S ∧ b.Fits S ∧ w.Fits S ∧
      Disjoint p.vars b.vars ∧ Disjoint p.vars w.vars ∧ Disjoint b.vars w.vars ∧
      ∀ x, TwoSparse x → F x = ((p.eval x && !(b.eval x)) || w.eval x))

theorem Region.lift {r : Region} {S T : Finset Nat} (h : r.Fits S) (sub : S ⊆ T) : r.Fits T :=
  ⟨h.1, h.2.trans sub⟩

theorem Region.none_fits (S : Finset Nat) : Region.Fits none S :=
  ⟨trivial, Finset.empty_subset S⟩

theorem view_join {S T : Finset Nat} {F : (Nat → Bool) → Bool} (h : MaskView S F)
    (v : Region) (hv : v.Fits T) (hST : Disjoint S T) :
    MaskView (S ∪ T) (fun x => F x || v.eval x) := by
  have vd {r : Region} (hr : r.Fits S) : Disjoint r.vars v.vars :=
    hST.mono hr.2 hv.2
  have liftR {r : Region} (hr : r.Fits S) : r.Fits (S ∪ T) := Region.lift hr Finset.subset_union_left
  have joinR {r : Region} (hr : r.Fits S) : (r.join v).Fits (S ∪ T) := by
    refine ⟨Region.join_good hr.1 hv.1 (vd hr), ?_⟩
    rw [Region.join_vars]
    exact Finset.union_subset_union hr.2 hv.2
  rcases h with ⟨g, hg, eg⟩ | ⟨b, u, hb, hu, dbu, eu⟩ | ⟨p, b, w, hp, hb, hw, dpb, dpw, dbw, ew⟩
  · exact Or.inl ⟨g.join v, joinR hg, fun x hx => by simp only [eg x hx, Region.join_eval]⟩
  · right; left
    exact ⟨b, u.join v, liftR hb, joinR hu, by rw [Region.join_vars]; exact Finset.disjoint_union_right.2 ⟨dbu, vd hb⟩,
      fun x hx => by simp only [eu x hx, Region.join_eval, Bool.or_assoc]⟩
  · right; right
    refine ⟨p, b, w.join v, liftR hp, liftR hb, joinR hw, dpb, ?_, ?_, ?_⟩
    · rw [Region.join_vars]; exact Finset.disjoint_union_right.2 ⟨dpw, vd hp⟩
    · rw [Region.join_vars]; exact Finset.disjoint_union_right.2 ⟨dbw, vd hb⟩
    · intro x hx; simp only [ew x hx, Region.join_eval, Bool.or_assoc]

theorem view_meet {S T : Finset Nat} {F : (Nat → Bool) → Bool} (h : MaskView S F)
    (v : Region) (hv : v.Fits T) (hST : Disjoint S T) :
    MaskView (S ∪ T) (fun x => F x && v.eval x) := by
  have vd {r : Region} (hr : r.Fits S) : Disjoint r.vars v.vars := hST.mono hr.2 hv.2
  have liftR {r : Region} (hr : r.Fits S) : r.Fits (S ∪ T) := Region.lift hr Finset.subset_union_left
  have meetR {r : Region} (hr : r.Fits S) : (r.meet v).Fits (S ∪ T) :=
    ⟨Region.meet_good hr.1 hv.1 (vd hr), (Region.meet_vars r v).trans (Finset.union_subset_union hr.2 hv.2)⟩
  rcases h with ⟨g, hg, eg⟩ | ⟨b, u, hb, hu, dbu, eu⟩ | ⟨p, b, w, hp, hb, hw, dpb, dpw, dbw, ew⟩
  · exact Or.inl ⟨g.meet v, meetR hg, fun x hx => by simp only [eg x hx, Region.meet_eval]⟩
  · right; right
    refine ⟨v, b, none, Region.lift hv Finset.subset_union_right, liftR hb, Region.none_fits _, (vd hb).symm, ?_, ?_, ?_⟩
    · simp [Region.vars]
    · simp [Region.vars]
    · intro x hx
      simp only [eu x hx]
      change ((!b.eval x || u.eval x) && v.eval x) = ((v.eval x && !b.eval x) || false)
      have hn := not_three hb.1 hu.1 hv.1 dbu (vd hb) (vd hu) hx
      cases eb : b.eval x <;> cases he : u.eval x <;> cases ev : v.eval x <;> simp_all
  · left
    have j : (p.join w).Fits S :=
      ⟨Region.join_good hp.1 hw.1 dpw, by rw [Region.join_vars]; exact Finset.union_subset hp.2 hw.2⟩
    refine ⟨(p.join w).meet v, meetR j, ?_⟩
    intro x hx
    simp only [ew x hx, Region.meet_eval, Region.join_eval]
    have hn := not_three hp.1 hb.1 hv.1 dpb (vd hp) (vd hb) hx
    cases ep : p.eval x <;> cases eb : b.eval x <;> cases ew' : w.eval x <;> cases ev : v.eval x <;> simp_all

theorem readOnce_mask (f : Form) (hr : f.ReadOnce) (h1 : f.nots = 1) :
    MaskView f.vars (fun x => f.eval x) := by
  induction f with
  | var w => simp [Form.nots] at h1
  | not b ih =>
    have hb : b.nots = 0 := by simp [Form.nots] at h1; omega
    right; left
    refine ⟨some b, none, ⟨⟨hr,hb⟩, subset_rfl⟩, Region.none_fits _, ?_, ?_⟩
    · simp [Region.vars]
    · intro x hx
      simp [Region.eval, Form.eval]
  | and l r il ir =>
    obtain ⟨hl,hr,d⟩ := hr
    simp only [Form.nots] at h1
    by_cases e : l.nots = 1
    · have er : r.nots = 0 := by omega
      exact view_meet (il hl e) (some r) ⟨⟨hr,er⟩,subset_rfl⟩ d
    · have e0 : l.nots = 0 := by omega
      have er : r.nots = 1 := by omega
      have z := view_meet (ir hr er) (some l) ⟨⟨hl,e0⟩,subset_rfl⟩ d.symm
      simpa only [Form.vars, Form.eval, Region.vars, Region.eval, Finset.union_comm, Bool.and_comm] using z
  | or l r il ir =>
    obtain ⟨hl,hr,d⟩ := hr
    simp only [Form.nots] at h1
    by_cases e : l.nots = 1
    · have er : r.nots = 0 := by omega
      exact view_join (il hl e) (some r) ⟨⟨hr,er⟩,subset_rfl⟩ d
    · have e0 : l.nots = 0 := by omega
      have er : r.nots = 1 := by omega
      have z := view_join (ir hr er) (some l) ⟨⟨hl,e0⟩,subset_rfl⟩ d.symm
      simpa only [Form.vars, Form.eval, Region.vars, Region.eval, Finset.union_comm, Bool.or_comm] using z

end PEqualNP.Outside.L_meta_29938_aux

namespace PEqualNP.Outside.L_meta_29938_aux

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

def LocalRows (F : ι → κ → Bool) (R : Finset ι) (i₀ : ι) : Prop :=
  ∀ i, i ∉ R → ∀ j, F i j = F i₀ j

def LocalCols (F : ι → κ → Bool) (C : Finset κ) (j₀ : κ) : Prop :=
  ∀ j, j ∉ C → ∀ i, F i j = F i j₀

theorem regionalRows {A F G H : ι → κ → Bool} {i₀ : ι} {R S T : Finset ι}
    (hinj : Function.Injective A)
    (dS : Disjoint R S) (dT : Disjoint R T)
    (lS : LocalRows G S i₀) (lT : LocalRows H T i₀)
    (op : Bool → Bool → Bool → Bool) (ev : ∀ i j, A i j = op (F i j) (G i j) (H i j)) :
    ∀ i ∈ insert i₀ R, ∀ i' ∈ insert i₀ R, (∀ j, F i j = F i' j) → i = i' := by
  have loc {Q : ι → κ → Bool} {U : Finset ι} (d : Disjoint R U) (l : LocalRows Q U i₀)
      (i : ι) (hi : i ∈ insert i₀ R) (j : κ) : Q i j = Q i₀ j := by
    rcases Finset.mem_insert.mp hi with rfl | h
    · rfl
    · exact l i (Finset.disjoint_left.mp d h) j
  intro i hi i' hi' h
  apply hinj
  funext j
  rw [ev i, ev i', h j, loc dS lS i hi j, loc dS lS i' hi' j, loc dT lT i hi j, loc dT lT i' hi' j]

theorem regionalCols {A F G H : ι → κ → Bool} {j₀ : κ} {R S T : Finset κ}
    (hinj : Function.Injective (fun j i => A i j))
    (dS : Disjoint R S) (dT : Disjoint R T)
    (lS : LocalCols G S j₀) (lT : LocalCols H T j₀)
    (op : Bool → Bool → Bool → Bool) (ev : ∀ i j, A i j = op (F i j) (G i j) (H i j)) :
    ∀ j ∈ insert j₀ R, ∀ j' ∈ insert j₀ R, (∀ i, F i j = F i j') → j = j' :=
  regionalRows (F := fun j i => F i j) (G := fun j i => G i j) (H := fun j i => H i j)
    hinj dS dT lS lT op (fun j i => ev i j)

structure PositiveProfile (F : ι → κ → Bool) (i₀ : ι) (j₀ : κ) where
  rows : Finset ι
  cols : Finset κ
  fullRows : Finset ι
  fullCols : Finset κ
  pairs : ℕ
  locR : LocalRows F rows i₀
  locC : LocalCols F cols j₀
  base : F i₀ j₀ = false
  fullRsub : fullRows ⊆ rows
  fullCsub : fullCols ⊆ cols
  fullR : ∀ i ∈ fullRows, ∀ j, F i j = true
  fullC : ∀ j ∈ fullCols, ∀ i, F i j = true
  unaryR : ∀ i, F i j₀ = true → i ∈ fullRows
  unaryC : ∀ j, F i₀ j = true → j ∈ fullCols
  boundR : fullRows.card ≤ 1
  boundC : fullCols.card ≤ 1
  countR : rows.card = pairs + fullRows.card
  countC : cols.card = pairs + fullCols.card

def PositiveProfile.transpose {F : ι → κ → Bool} {i₀ j₀}
    (p : PositiveProfile F i₀ j₀) : PositiveProfile (fun j i => F i j) j₀ i₀ where
  rows := p.cols
  cols := p.rows
  fullRows := p.fullCols
  fullCols := p.fullRows
  pairs := p.pairs
  locR := p.locC
  locC := p.locR
  base := p.base
  fullRsub := p.fullCsub
  fullCsub := p.fullRsub
  fullR := p.fullC
  fullC := p.fullR
  unaryR := p.unaryC
  unaryC := p.unaryR
  boundR := p.boundC
  boundC := p.boundR
  countR := p.countC
  countC := p.countR

structure Regions (P B W A : ι → κ → Bool) (i₀ : ι) (j₀ : κ) where
  p : PositiveProfile P i₀ j₀
  w : PositiveProfile W i₀ j₀
  br : Finset ι
  bc : Finset κ
  blr : LocalRows B br i₀
  blc : LocalCols B bc j₀
  bbase : B i₀ j₀ = false
  baseR : i₀ ∉ br
  baseC : j₀ ∉ bc
  rbp : Disjoint br p.rows
  rbw : Disjoint br w.rows
  rpw : Disjoint p.rows w.rows
  cbp : Disjoint bc p.cols
  cbw : Disjoint bc w.cols
  cpw : Disjoint p.cols w.cols
  eval : ∀ i j, A i j = ((P i j && !(B i j)) || W i j)

def Regions.transpose {P B W A : ι → κ → Bool} {i₀ j₀}
    (d : Regions P B W A i₀ j₀) : Regions
      (fun j i => P i j) (fun j i => B i j) (fun j i => W i j) (fun j i => A i j) j₀ i₀ where
  p := d.p.transpose
  w := d.w.transpose
  br := d.bc
  bc := d.br
  blr := d.blc
  blc := d.blr
  bbase := d.bbase
  baseR := d.baseC
  baseC := d.baseR
  rbp := d.cbp
  rbw := d.cbw
  rpw := d.cpw
  cbp := d.rbp
  cbw := d.rbw
  cpw := d.rpw
  eval := fun j i => d.eval i j

variable {P B W A : ι → κ → Bool} {i₀ : ι} {j₀ : κ}

theorem maskRowProfile (d : Regions P B W A i₀ j₀) {i} (hi : i ∈ d.br ∨ i = i₀) (j : κ) :
    A i j = ((P i₀ j && !(B i j₀)) || W i₀ j) := by
  rw [d.eval]
  have hP : P i j = P i₀ j := by
    rcases hi with hi | rfl
    · exact d.p.locR i (Finset.disjoint_left.mp d.rbp hi) j
    · rfl
  have hW : W i j = W i₀ j := by
    rcases hi with hi | rfl
    · exact d.w.locR i (Finset.disjoint_left.mp d.rbw hi) j
    · rfl
  rw [hP, hW]
  by_cases hj : j ∈ d.bc
  · rw [d.p.locC j (Finset.disjoint_left.mp d.cbp hj) i₀, d.p.base]
    simp
  · rw [d.blc j hj i]

theorem maskRowCount (d : Regions P B W A i₀ j₀) (hA : Function.Injective A) :
    d.br.card ≤ d.p.fullCols.card := by
  have active : ∀ i ∈ d.br, B i j₀ = true := by
    intro i hi
    cases hb : B i j₀ with
    | false =>
      exfalso
      have eq : A i = A i₀ := funext fun j => by
        rw [maskRowProfile d (Or.inl hi), maskRowProfile d (Or.inr rfl), hb, d.bbase]
      exact d.baseR (hA eq ▸ hi)
    | true => rfl
  have ub : d.br.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi i' hi'
    apply hA
    funext j
    rw [maskRowProfile d (Or.inl hi), maskRowProfile d (Or.inl hi'), active i hi, active i' hi']
  by_cases empty : d.p.fullCols = ∅
  · have bz : d.br = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      apply d.baseR
      have eq : A i = A i₀ := funext fun j => by
        have hp : P i₀ j = false := by
          cases h : P i₀ j with
          | false => rfl
          | true => simpa [empty] using d.p.unaryC j h
        rw [maskRowProfile d (Or.inl hi), maskRowProfile d (Or.inr rfl), hp]
        simp
      exact hA eq ▸ hi
    simp [bz]
  · have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr empty)
    omega

theorem unpuncturedRows (d : Regions P B W A i₀ j₀) (hA : Function.Injective A) :
    d.bc = ∅ → d.p.fullRows.card + d.w.fullRows.card ≤ 1 := by
  intro hbc
  have distin := d.rpw.mono d.p.fullRsub d.w.fullRsub
  rw [← Finset.card_union_of_disjoint distin]
  apply Finset.card_le_one.mpr
  have full : ∀ i ∈ d.p.fullRows ∪ d.w.fullRows, ∀ j, A i j = true := by
    intro i hi j
    rw [d.eval]
    rcases Finset.mem_union.mp hi with hi | hi
    · have hbr : i ∉ d.br := Finset.disjoint_right.mp d.rbp (d.p.fullRsub hi)
      have hb := d.blc j (by simp [hbc]) i₀
      rw [d.blr i hbr j, hb, d.bbase, d.p.fullR i hi j]
      rfl
    · simp [d.w.fullR i hi j]
  intro i hi i' hi'
  apply hA
  funext j
  rw [full i hi j, full i' hi' j]

theorem maskedBudget (d : Regions P B W A i₀ j₀) (hr : Function.Injective A)
    (hc : Function.Injective (fun j i => A i j)) :
    let nr := d.p.rows.card + d.br.card + d.w.rows.card
    let nc := d.p.cols.card + d.bc.card + d.w.cols.card
    nr ≤ nc + 1 ∧ nc ≤ nr + 1 := by
  dsimp only
  have hbr := maskRowCount d hr
  have hbc : d.bc.card ≤ d.p.fullRows.card := maskRowCount d.transpose hc
  have hzeroR : d.bc.card = 0 → d.p.fullRows.card + d.w.fullRows.card ≤ 1 :=
    fun h => unpuncturedRows d hr (Finset.card_eq_zero.mp h)
  have hzeroC : d.br.card = 0 → d.p.fullCols.card + d.w.fullCols.card ≤ 1 :=
    fun h => unpuncturedRows d.transpose hc (Finset.card_eq_zero.mp h)
  have hpR := d.p.boundR
  have hpC := d.p.boundC
  have hwR := d.w.boundR
  have hwC := d.w.boundC
  rw [d.p.countR, d.p.countC, d.w.countR, d.w.countC]
  omega

theorem regionsRowCard [Fintype ι] (d : Regions P B W A i₀ j₀) (hr : Function.Injective A)
    (hp : i₀ ∉ d.p.rows) (hw : i₀ ∉ d.w.rows) :
    Fintype.card ι = d.p.rows.card + d.br.card + d.w.rows.card + 1 := by
  let S := d.p.rows ∪ d.br ∪ d.w.rows
  have h0 : i₀ ∉ S := by simp [S, hp, hw, d.baseR]
  have cover : Finset.univ = insert i₀ S := by
    apply Finset.Subset.antisymm _ (Finset.subset_univ _)
    intro i _
    by_cases hs : i ∈ S
    · exact Finset.mem_insert_of_mem hs
    · have h : i ∉ d.p.rows ∧ i ∉ d.br ∧ i ∉ d.w.rows := by simpa [S] using hs
      have he : A i = A i₀ := funext fun j => by
        rw [d.eval, d.eval i₀, d.p.locR i h.1, d.blr i h.2.1, d.w.locR i h.2.2]
      simp [hr he]
  have hs : S.card = d.p.rows.card + d.br.card + d.w.rows.card := by
    dsimp [S]
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨d.rpw, d.rbw⟩),
      Finset.card_union_of_disjoint d.rbp.symm]
  rw [← Finset.card_univ, cover, Finset.card_insert_of_notMem h0, hs]

theorem maskedWidth [Fintype ι] [Fintype κ]
    (d : Regions P B W A i₀ j₀) (hr : Function.Injective A)
    (hc : Function.Injective (fun j i => A i j))
    (hpr : i₀ ∉ d.p.rows) (hwr : i₀ ∉ d.w.rows)
    (hpc : j₀ ∉ d.p.cols) (hwc : j₀ ∉ d.w.cols) :
    Fintype.card ι ≤ Fintype.card κ + 1 ∧ Fintype.card κ ≤ Fintype.card ι + 1 := by
  have h := maskedBudget d hr hc
  have cr := regionsRowCard d hr hpr hwr
  have cc : Fintype.card κ = d.p.cols.card + d.bc.card + d.w.cols.card + 1 :=
    regionsRowCard d.transpose hc hpc hwc
  dsimp only at h
  omega

end PEqualNP.Outside.L_meta_29938_aux

open PEqualNP.Outside.L_meta_29938_aux

namespace PEqualNP.Outside.L_meta_29938_aux

private theorem fold_card {α : Type} [DecidableEq α] (L : List (Finset α))
    (hp : L.Pairwise Disjoint) :
    (L.foldr (fun (a b : Finset α) => a ∪ b) ∅).card = (L.map Finset.card).sum := by
  induction L with
  | nil => simp
  | cons a t ih =>
    rcases List.pairwise_cons.1 hp with ⟨hd, ht⟩
    have h : Disjoint a (t.foldr (· ∪ ·) ∅) := by
      apply Finset.disjoint_left.2
      intro x hx hxt
      obtain ⟨b,hb,hxb⟩ := (mem_foldr_union_iff ..).1 hxt
      exact Finset.disjoint_left.1 (hd b hb) hx hxb
    simp only [List.foldr_cons,List.map_cons,List.sum_cons]
    rw [Finset.card_union_of_disjoint h, ih ht]

private theorem each_card_one {α : Type} [DecidableEq α] (L : List (Finset α))
    (h : ∀ s ∈ L, s.card = 1) : (L.map Finset.card).sum = L.length := by
  induction L with
  | nil => simp
  | cons a t ih =>
    simp [h a (by simp), ih (fun s hs => h s (by simp [hs])), Nat.add_comm]

private theorem nf_row_count {n m : Nat} {X : Finset (Fin n)} {Y : Finset (Fin m)}
    (nf : MonoNF n m) (hv : nf.Valid X Y) (u0 : Fin n) (hu0 : u0 ∉ X)
    (hr : ∀ u ∈ insert u0 X, ∀ w ∈ insert u0 X,
      (∀ v, nf.eval u v = nf.eval w v) → u = w) :
    nf.S0.card ≤ 1 ∧ X.card = nf.S0.card + nf.rects.length := by
  classical
  rcases hv with ⟨hS, hT, hb, hpw⟩
  have hpure : nf.S0.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro u hu w hw
    exact hr u (Finset.mem_insert_of_mem (hS hu)) w (Finset.mem_insert_of_mem (hS hw))
      (fun v => by simp [MonoNF.eval, hu,hw])
  have equiv : ∀ p ∈ nf.rects, ∀ q ∈ nf.rects, p = q ∨ Disjoint p.1 q.1 := by
    exact fun p hp q hq => List.Pairwise.forall_of_forall_of_flip
      (R := fun p q : Finset (Fin n) × Finset (Fin m) => p = q ∨ Disjoint p.1 q.1)
      (fun _ _ => Or.inl rfl) (hpw.imp (fun h => Or.inr h.1))
      (hpw.imp (fun h => Or.inr h.1.symm)) hp hq
  have single : ∀ p ∈ nf.rects, p.1.card = 1 := by
    intro p hp
    have h₁ := (hb p hp).1.card_pos
    have h₂ : p.1.card ≤ 1 := by
      apply Finset.card_le_one.2
      intro u hu w hw
      have spec : ∀ a ∈ p.1, ∀ v, nf.eval a v = decide (v ∈ nf.T0 ∨ v ∈ p.2) := by
        intro a ha v
        simp only [MonoNF.eval, decide_eq_decide]
        have hn := Finset.disjoint_left.1 (hb p hp).2.2.2.2.1 ha
        simp only [hn,false_or]
        apply or_congr_right
        constructor
        · rintro ⟨q,hq,haq,hvq⟩
          rcases equiv p hp q hq with he | hd
          · simpa [he] using hvq
          · exact (Finset.disjoint_left.1 hd ha haq).elim
        · intro hvp; exact ⟨p,hp,ha,hvp⟩
      exact hr u (Finset.mem_insert_of_mem ((hb p hp).2.2.1 hu))
        w (Finset.mem_insert_of_mem ((hb p hp).2.2.1 hw))
        (fun v => (spec u hu v).trans (spec w hw v).symm)
    omega
  let blocks := nf.rects.map Prod.fst
  have hclass : X = nf.S0 ∪ blocks.foldr (· ∪ ·) ∅ := by
    ext u
    constructor
    · intro hu
      by_contra h
      have hn : u ∉ nf.S0 := fun hS' => h (Finset.mem_union_left _ hS')
      have hnone : ∀ p ∈ nf.rects, u ∉ p.1 := by
        intro p hp hu'
        apply h
        exact Finset.mem_union_right _ ((mem_foldr_union_iff ..).2 ⟨p.1, List.mem_map_of_mem hp, hu'⟩)
      have he : u = u0 := by
        apply hr u (Finset.mem_insert_of_mem hu) u0 (Finset.mem_insert_self ..)
        intro v
        have hn0 : u0 ∉ nf.S0 := fun h => hu0 (hS h)
        have hnone0 : ∀ p ∈ nf.rects, u0 ∉ p.1 := fun p hp ha => hu0 ((hb p hp).2.2.1 ha)
        have hf : ¬∃ p ∈ nf.rects, u ∈ p.1 ∧ v ∈ p.2 :=
          fun ⟨p,hp,hup,_⟩ => hnone p hp hup
        have hf0 : ¬∃ p ∈ nf.rects, u0 ∈ p.1 ∧ v ∈ p.2 :=
          fun ⟨p,hp,hup,_⟩ => hnone0 p hp hup
        simp only [MonoNF.eval, hn,hn0, hf,hf0, false_or, or_false]
      exact hu0 (he ▸ hu)
    · intro ha
      rcases Finset.mem_union.1 ha with hs | hrs
      · exact hS hs
      · obtain ⟨S,hSm,huS⟩ := (mem_foldr_union_iff ..).1 hrs
        obtain ⟨p,hp,rfl⟩ := List.mem_map.1 hSm
        exact (hb p hp).2.2.1 huS
  have hdis : Disjoint nf.S0 (blocks.foldr (· ∪ ·) ∅) := by
    apply Finset.disjoint_left.2; intro u hu h
    obtain ⟨S,hSm,huS⟩ := (mem_foldr_union_iff ..).1 h
    obtain ⟨p,hp,rfl⟩ := List.mem_map.1 hSm
    exact Finset.disjoint_left.1 (hb p hp).2.2.2.2.1 huS hu
  have hpair : blocks.Pairwise Disjoint := List.pairwise_map.2 (hpw.imp (·.1))
  have hones : ∀ S ∈ blocks, S.card = 1 := by
    intro S hS'; obtain ⟨p,hp,rfl⟩ := List.mem_map.1 hS'; exact single p hp
  exact ⟨hpure, by rw [hclass,Finset.card_union_of_disjoint hdis,fold_card blocks hpair,
    each_card_one blocks hones]; simp [blocks]⟩

private def nfTranspose {n m : Nat} (a : MonoNF n m) : MonoNF m n :=
  ⟨a.T0, a.S0, a.rects.map Prod.swap⟩

private theorem transpose_valid {n m : Nat} {X : Finset (Fin n)} {Y : Finset (Fin m)}
    {a : MonoNF n m} (ha : a.Valid X Y) : (nfTranspose a).Valid Y X := by
  refine ⟨ha.2.1,ha.1,?_,?_⟩
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.1 hp
    obtain ⟨hr,hc,hr',hc',hds,hdt⟩ := ha.2.2.1 q hq
    exact ⟨hc,hr,hc',hr',hdt,hds⟩
  · exact List.pairwise_map.2 (ha.2.2.2.imp (fun h => ⟨h.2,h.1⟩))

private theorem eval_transpose {n m : Nat} (a : MonoNF n m) (v : Fin m) (u : Fin n) :
    (nfTranspose a).eval v u = a.eval u v := by
  simp only [nfTranspose, MonoNF.eval, List.mem_map, Prod.fst_swap, Prod.snd_swap,
    decide_eq_decide]
  aesop

theorem positive_nf_balance {n m : Nat} {X : Finset (Fin n)} {Y : Finset (Fin m)}
    (a : MonoNF n m) (ha : a.Valid X Y)
    (u0 : Fin n) (v0 : Fin m) (hu0 : u0 ∉ X) (hv0 : v0 ∉ Y)
    (hr : ∀ u ∈ insert u0 X, ∀ w ∈ insert u0 X,
      (∀ v, a.eval u v = a.eval w v) → u = w)
    (hc : ∀ v ∈ insert v0 Y, ∀ z ∈ insert v0 Y,
      (∀ u, a.eval u v = a.eval u z) → v = z) :
    a.S0.card ≤ 1 ∧ a.T0.card ≤ 1 ∧
    X.card = a.S0.card + a.rects.length ∧ Y.card = a.T0.card + a.rects.length := by
  have ⟨hs, hx⟩ := nf_row_count a ha u0 hu0 hr
  have ⟨ht, hy⟩ := nf_row_count (nfTranspose a) (transpose_valid ha) v0 hv0
    (fun v hv z hz h => hc v hv z hz (fun u => by simpa [eval_transpose] using h u))
  exact ⟨hs,ht,hx,by simpa [nfTranspose] using hy⟩

theorem positive_nf_eval_dummy_col {n m : Nat} {X : Finset (Fin n)} {Y : Finset (Fin m)}
    {a : MonoNF n m} (ha : a.Valid X Y) (u : Fin n) (v : Fin m) (hv : v ∉ Y) :
    a.eval u v = decide (u ∈ a.S0) := by
  have hT : v ∉ a.T0 := fun h => hv (ha.2.1 h)
  have hR : ∀ p ∈ a.rects, v ∉ p.2 := fun p hp h => hv ((ha.2.2.1 p hp).2.2.2.1 h)
  have hnone : ¬ ∃ p ∈ a.rects, u ∈ p.1 ∧ v ∈ p.2 :=
    fun ⟨p,hp,_,hvp⟩ => hR p hp hvp
  simp only [MonoNF.eval,hT,hnone,false_or,or_false]

theorem positive_nf_eval_dummy_row {n m : Nat} {X : Finset (Fin n)} {Y : Finset (Fin m)}
    {a : MonoNF n m} (ha : a.Valid X Y) (u : Fin n) (v : Fin m) (hu : u ∉ X) :
    a.eval u v = decide (v ∈ a.T0) := by
  rw [← eval_transpose a v u]
  exact positive_nf_eval_dummy_col (transpose_valid ha) v u hu

end PEqualNP.Outside.L_meta_29938_aux

open PEqualNP.Outside.L_meta_29938_aux

namespace PEqualNP.Outside.L_meta_29938_aux

noncomputable def positiveProfileOfNF {n m : Nat} {X : Finset (Fin n)} {Y : Finset (Fin m)}
    (a : MonoNF n m) (ha : a.Valid X Y)
    (u0 : Fin n) (v0 : Fin m) (hu0 : u0 ∉ X) (hv0 : v0 ∉ Y)
    (hr : ∀ u ∈ insert u0 X, ∀ w ∈ insert u0 X,
      (∀ v, a.eval u v = a.eval w v) → u = w)
    (hc : ∀ v ∈ insert v0 Y, ∀ z ∈ insert v0 Y,
      (∀ u, a.eval u v = a.eval u z) → v = z) :
    PositiveProfile a.eval u0 v0 where
  rows := X
  cols := Y
  fullRows := a.S0
  fullCols := a.T0
  pairs := a.rects.length
  locR := fun i hi j => (positive_nf_eval_dummy_row ha i j hi).trans
    (positive_nf_eval_dummy_row ha u0 j hu0).symm
  locC := fun j hj i => (positive_nf_eval_dummy_col ha i j hj).trans
    (positive_nf_eval_dummy_col ha i v0 hv0).symm
  base := by rw [positive_nf_eval_dummy_row ha u0 v0 hu0]; exact decide_eq_false (fun h => hv0 (ha.2.1 h))
  fullRsub := ha.1
  fullCsub := ha.2.1
  fullR := fun i hi j => by simp [MonoNF.eval,hi]
  fullC := fun j hj i => by simp [MonoNF.eval,hj]
  unaryR := fun i h => of_decide_eq_true ((positive_nf_eval_dummy_col ha i v0 hv0).symm.trans h)
  unaryC := fun j h => of_decide_eq_true ((positive_nf_eval_dummy_row ha u0 j hu0).symm.trans h)
  boundR := (positive_nf_balance a ha u0 v0 hu0 hv0 hr hc).1
  boundC := (positive_nf_balance a ha u0 v0 hu0 hv0 hr hc).2.1
  countR := by rw [Nat.add_comm]; exact (positive_nf_balance a ha u0 v0 hu0 hv0 hr hc).2.2.1
  countC := by rw [Nat.add_comm]; exact (positive_nf_balance a ha u0 v0 hu0 hv0 hr hc).2.2.2

theorem positiveProfileOfForm {n m : Nat} (f : Form) (hro : f.ReadOnce) (hpos : f.nots = 0)
    (hbound : ∀ i ∈ f.vars, i < n + m)
    (u0 : Fin n) (v0 : Fin m)
    (hu0 : u0 ∉ rowVars n f.vars) (hv0 : v0 ∉ colVars n m f.vars)
    (hr : ∀ u ∈ insert u0 (rowVars n f.vars), ∀ w ∈ insert u0 (rowVars n f.vars),
      (∀ v : Fin m, f.eval (oneEachFn u v) = f.eval (oneEachFn w v)) → u = w)
    (hc : ∀ v ∈ insert v0 (colVars n m f.vars), ∀ z ∈ insert v0 (colVars n m f.vars),
      (∀ u : Fin n, f.eval (oneEachFn u v) = f.eval (oneEachFn u z)) → v = z) :
    ∃ p : PositiveProfile (fun u v => f.eval (oneEachFn u v)) u0 v0,
      p.rows = rowVars n f.vars ∧ p.cols = colVars n m f.vars := by
  obtain ⟨nf,hv,he⟩ := mono_normal_form n m f hro hpos hbound
  have eqf : (fun (u : Fin n) (v : Fin m) => f.eval (oneEachFn u v)) = nf.eval :=
    funext fun u => funext fun v => he u v
  rw [eqf]
  refine ⟨positiveProfileOfNF nf hv u0 v0 hu0 hv0 ?_ ?_,rfl,rfl⟩
  · intro u hu w hw h
    exact hr u hu w hw (fun v => by simpa only [he] using h v)
  · intro v hv z hz h
    exact hc v hv z hz (fun u => by simpa only [he] using h u)

end PEqualNP.Outside.L_meta_29938_aux

open PEqualNP.Outside.L_meta_29938_aux

namespace PEqualNP.Outside.L_meta_29938_aux

def Region.table {n m : Nat} (r : Region) (i : Fin n) (j : Fin m) : Bool :=
  r.eval (oneEachFn i j)

theorem Region.congr (r : Region) {x y : Nat → Bool} (he : ∀ t ∈ r.vars, x t = y t) :
    r.eval x = r.eval y := by
  cases r with
  | none => rfl
  | some f => exact Form.eval_congr f x y he

theorem Region.localRows {n m : Nat} (r : Region) {i₀ : Fin n}
    (h₀ : i₀ ∉ rowVars n r.vars) :
    LocalRows (@Region.table n m r) (rowVars n r.vars) i₀ := by
  intro i hi j
  apply Region.congr
  have ne (a : Fin n) (h : a ∉ rowVars n r.vars) (t : Nat) (ht : t ∈ r.vars) : t ≠ a.val := by
    intro e
    apply h
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, e ▸ ht⟩
  intro t ht
  simp [oneEachFn, ne i hi t ht, ne i₀ h₀ t ht]

theorem Region.localCols {n m : Nat} (r : Region) {j₀ : Fin m}
    (h₀ : j₀ ∉ colVars n m r.vars) :
    LocalCols (@Region.table n m r) (colVars n m r.vars) j₀ := by
  intro j hj i
  apply Region.congr
  have ne (a : Fin m) (h : a ∉ colVars n m r.vars) (t : Nat) (ht : t ∈ r.vars) :
      t ≠ n + a.val := by
    intro e
    apply h
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, e ▸ ht⟩
  intro t ht
  simp [oneEachFn, ne j hj t ht, ne j₀ h₀ t ht]

theorem Region.baseFalse {n m : Nat} (r : Region) (h : r.Good) {i₀ : Fin n} {j₀ : Fin m}
    (hi : i₀ ∉ rowVars n r.vars) (hj : j₀ ∉ colVars n m r.vars) :
    r.table i₀ j₀ = false := by
  cases hv : r.table i₀ j₀ with
  | false => rfl
  | true =>
    obtain ⟨t, ht, hw⟩ := Region.witness h hv
    simp only [oneEachFn, decide_eq_true_eq] at hw
    rcases hw with e | e
    · exact (hi (Finset.mem_filter.2 ⟨Finset.mem_univ _, e ▸ ht⟩)).elim
    · exact (hj (Finset.mem_filter.2 ⟨Finset.mem_univ _, e ▸ ht⟩)).elim

theorem Region.missingRow {n : Nat} {S : Finset Nat} {r : Region} (fits : r.Fits S) {i₀ : Fin n}
    (h : i₀ ∉ rowVars n S) : i₀ ∉ rowVars n r.vars := by
  intro he
  exact h (Finset.mem_filter.2 ⟨Finset.mem_univ _, fits.2 (Finset.mem_filter.1 he).2⟩)

theorem Region.missingCol {n m : Nat} {S : Finset Nat} {r : Region} (fits : r.Fits S) {j₀ : Fin m}
    (h : j₀ ∉ colVars n m S) : j₀ ∉ colVars n m r.vars := by
  intro he
  exact h (Finset.mem_filter.2 ⟨Finset.mem_univ _, fits.2 (Finset.mem_filter.1 he).2⟩)

end PEqualNP.Outside.L_meta_29938_aux

open PEqualNP.Outside.L_meta_29938_aux

namespace PEqualNP.Outside.L_meta_29938_aux

theorem regionProfile {n m : Nat} (r : Region) (hg : r.Good)
    (hbound : ∀ i ∈ r.vars, i < n+m) (z : Fin n) (t : Fin m)
    (hz : z ∉ rowVars n r.vars) (ht : t ∉ colVars n m r.vars)
    (hr : ∀ i ∈ insert z (rowVars n r.vars), ∀ i' ∈ insert z (rowVars n r.vars),
      (∀ j : Fin m, r.table i j = r.table i' j) → i = i')
    (hc : ∀ j ∈ insert t (colVars n m r.vars), ∀ j' ∈ insert t (colVars n m r.vars),
      (∀ i : Fin n, r.table i j = r.table i j') → j = j') :
    ∃ d : PositiveProfile (@Region.table n m r) z t,
      d.rows = rowVars n r.vars ∧ d.cols = colVars n m r.vars := by
  cases r with
  | some f => exact positiveProfileOfForm f hg.1 hg.2 hbound z t hz ht hr hc
  | none =>
    let d : PositiveProfile (@Region.table n m none) z t :=
      { rows := ∅, cols := ∅, fullRows := ∅, fullCols := ∅, pairs := 0
        locR := fun _ _ _ => rfl
        locC := fun _ _ _ => rfl
        base := rfl
        fullRsub := Finset.Subset.refl _
        fullCsub := Finset.Subset.refl _
        fullR := by simp
        fullC := by simp
        unaryR := by intro i h; contradiction
        unaryC := by intro j h; contradiction
        boundR := by simp
        boundC := by simp
        countR := by simp
        countC := by simp }
    refine ⟨d, ?_, ?_⟩
    · change ∅ = rowVars n ∅
      ext i
      simp [rowVars]
    · change ∅ = colVars n m ∅
      ext j
      simp [colVars]

theorem regionWidth {n m : Nat} (S : Finset Nat) (p b w : Region)
    (hp : p.Fits S) (hb : b.Fits S) (hw : w.Fits S)
    (dpb : Disjoint p.vars b.vars) (dpw : Disjoint p.vars w.vars) (dbw : Disjoint b.vars w.vars)
    (hlt : ∀ i ∈ S, i < n+m) (hx : (rowVars n S).card+1=n) (hy : (colVars n m S).card+1=m)
    (A : Fin n → Fin m → Bool)
    (he : ∀ i j, A i j = ((p.eval (oneEachFn i j) && !(b.eval (oneEachFn i j))) || w.eval (oneEachFn i j)))
    (hr : Function.Injective A) (hc : Function.Injective (fun j i => A i j)) :
    n ≤ m+1 ∧ m ≤ n+1 := by
  classical
  have missing {k : Nat} (V : Finset (Fin k)) (card : V.card+1=k) : ∃ i, i ∉ V := by
    by_contra! all
    have hv : V = Finset.univ := by ext i; simp [all i]
    simp [hv] at card
  obtain ⟨z,hz⟩ := missing _ hx
  obtain ⟨t,ht⟩ := missing _ hy
  have pz := Region.missingRow hp hz
  have bz := Region.missingRow hb hz
  have wz := Region.missingRow hw hz
  have pt := Region.missingCol hp ht
  have bt := Region.missingCol hb ht
  have wt := Region.missingCol hw ht
  let op := fun (pv bv wv : Bool) => ((pv && !bv) || wv)
  let opw := fun (wv pv bv : Bool) => ((pv && !bv) || wv)
  have dpr := regionalRows (F := @Region.table n m p) hr (rowVars_disjoint n dpb)
    (rowVars_disjoint n dpw) (b.localRows bz) (w.localRows wz) op he
  have dpc := regionalCols (F := @Region.table n m p) hc (colVars_disjoint n m dpb)
    (colVars_disjoint n m dpw) (b.localCols bt) (w.localCols wt) op he
  have dwr := regionalRows (F := @Region.table n m w) hr (rowVars_disjoint n dpw.symm)
    (rowVars_disjoint n dbw.symm) (p.localRows pz) (b.localRows bz) opw he
  have dwc := regionalCols (F := @Region.table n m w) hc (colVars_disjoint n m dpw.symm)
    (colVars_disjoint n m dbw.symm) (p.localCols pt) (b.localCols bt) opw he
  obtain ⟨pp, pr, pc⟩ := regionProfile p hp.1 (fun i hi => hlt i (hp.2 hi)) z t pz pt dpr dpc
  obtain ⟨ww, wr, wc⟩ := regionProfile w hw.1 (fun i hi => hlt i (hw.2 hi)) z t wz wt dwr dwc
  let d : Regions (@Region.table n m p) (@Region.table n m b) (@Region.table n m w) A z t :=
    { p := pp, w := ww, br := rowVars n b.vars, bc := colVars n m b.vars
      blr := b.localRows bz, blc := b.localCols bt, bbase := b.baseFalse hb.1 bz bt
      baseR := bz, baseC := bt
      rbp := by rw [pr]; exact rowVars_disjoint n dpb.symm
      rbw := by rw [wr]; exact rowVars_disjoint n dbw
      rpw := by rw [pr, wr]; exact rowVars_disjoint n dpw
      cbp := by rw [pc]; exact colVars_disjoint n m dpb.symm
      cbw := by rw [wc]; exact colVars_disjoint n m dbw
      cpw := by rw [pc,wc]; exact colVars_disjoint n m dpw
      eval := he }
  have h := maskedWidth d hr hc (show z ∉ pp.rows by rwa [pr])
    (show z ∉ ww.rows by rwa [wr]) (show t ∉ pp.cols by rwa [pc]) (show t ∉ ww.cols by rwa [wc])
  simpa only [Fintype.card_fin] using h

end PEqualNP.Outside.L_meta_29938_aux

open PEqualNP.Outside.L_meta_29938_aux PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity PEqualNP.Represents

namespace PEqualNP.Outside.L_meta_29938_aux

def WidthPrinciple : Prop :=
  ∀ {n m : Nat} (S : Finset Nat) (p b w : Region),
    p.Fits S → b.Fits S → w.Fits S →
    Disjoint p.vars b.vars → Disjoint p.vars w.vars → Disjoint b.vars w.vars →
    (∀ i ∈ S, i < n + m) → (rowVars n S).card + 1 = n → (colVars n m S).card + 1 = m →
    ∀ (A : Fin n → Fin m → Bool),
    (∀ i j, A i j = ((p.eval (oneEachFn i j) && !(b.eval (oneEachFn i j))) || w.eval (oneEachFn i j))) →
    Function.Injective A → Function.Injective (fun j i => A i j) →
    n ≤ m + 1 ∧ m ≤ n + 1

theorem complement_inj {n m : Nat} {A : Fin n → Fin m → Bool}
    (hr : Function.Injective A) : Function.Injective (fun i j => !(A i j)) := by
  intro a b hab
  apply hr
  funext j
  exact Bool.not_inj (congrFun hab j)

theorem finish_of_width (width : WidthPrinciple) :
    ∀ (n m : Nat) (A : Fin n → Fin m → Bool), 2 ≤ n → 2 ≤ m → Function.Injective A →
    Function.Injective (fun j i => A i j) → ∀ s : Nat, s + 2 ≤ n+m →
    (n+2 ≤ m ∨ m+2 ≤ n) →
    ((∃ C : Circuit, FanInTwo C ∧ C.size ≤ s ∧ Represents A C) ↔ RepSizeAtMost A s) := by
  intro n m A hn hm hr hc s hs hu
  constructor
  · rintro ⟨C,hC,hsize,hCA⟩
    rcases threshold_shape A hn hm hr hc hs C hC hsize hCA with mono | z
    · exact mono
    obtain ⟨_,_,f,hro,hnot,_,hlt,hx,hy,he⟩ := z
    have ht {u : Fin n} {v : Fin m} : TwoSparse (oneEachFn u v) := oneEach_sparse u v
    have nonefit := Region.none_fits f.vars
    have hb : n ≤ m + 1 ∧ m ≤ n + 1 := by
      rcases readOnce_mask f hro hnot with
        ⟨g,hg,eg⟩ | ⟨b,u,hb,hu,dbu,eu⟩ | ⟨p,b,w,hp,hb,hw,dpb,dpw,dbw,ew⟩
      · apply width f.vars none none g nonefit nonefit hg (by simp [Region.vars])
            (by simp [Region.vars]) (by simp [Region.vars]) hlt hx hy A _ hr hc
        intro i j
        simpa only [Region.eval, Bool.false_and, Bool.false_or] using (he i j).symm.trans (eg _ ht)
      · let B := fun (i : Fin n) (j : Fin m) => !(A i j)
        apply width f.vars b u none hb hu nonefit dbu (by simp [Region.vars])
            (by simp [Region.vars]) hlt hx hy B _ (complement_inj hr)
            (complement_inj (A := fun j i => A i j) hc)
        intro i j
        have eq := (he i j).symm.trans (eu _ ht)
        change (!(A i j)) = ((b.eval (oneEachFn i j) && !(u.eval (oneEachFn i j))) || false)
        simp only [eq, Bool.not_or, Bool.not_not, Bool.or_false]
      · exact width f.vars p b w hp hb hw dpb dpw dbw hlt hx hy A
          (fun i j => (he i j).symm.trans (ew _ ht)) hr hc
    omega
  · rintro ⟨C,hC,hsize,hR⟩
    refine ⟨C, ?_, hsize, hR⟩
    intro g hg
    obtain ⟨hop,hlen⟩ := hC g hg
    refine ⟨?_,hlen⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
    tauto

end PEqualNP.Outside.L_meta_29938_aux

theorem PEqualNP.Outside.L_meta_29938 : ∀ (n m : Nat) (A : Fin n → Fin m → Bool),
  2 ≤ n → 2 ≤ m → Function.Injective A → Function.Injective (fun j i => A i j) →
  ∀ s : Nat, s + 2 ≤ n+m →
  (n+2 ≤ m ∨ m+2 ≤ n) →
  ((∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ s ∧ PEqualNP.Represents.Represents A C) ↔ PEqualNP.Represents.RepSizeAtMost A s) :=
  PEqualNP.Outside.L_meta_29938_aux.finish_of_width PEqualNP.Outside.L_meta_29938_aux.regionWidth
