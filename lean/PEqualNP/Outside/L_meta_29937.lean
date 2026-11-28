import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29937_aux

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

end PEqualNP.Outside.L_meta_29937_aux

open PEqualNP.Outside.L_meta_29937_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

namespace PEqualNP.Outside.L_meta_29937_aux

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

end PEqualNP.Outside.L_meta_29937_aux

open PEqualNP.Outside.L_meta_29937_aux

namespace PEqualNP.Outside.L_meta_29937_aux

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

end PEqualNP.Outside.L_meta_29937_aux

namespace PEqualNP.Outside.L_meta_29937_aux

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

theorem Region.missingRow {n : Nat} {S : Finset Nat} {r : Region} (fits : r.Fits S) {i₀ : Fin n}
    (h : i₀ ∉ rowVars n S) : i₀ ∉ rowVars n r.vars := by
  intro he
  exact h (Finset.mem_filter.2 ⟨Finset.mem_univ _, fits.2 (Finset.mem_filter.1 he).2⟩)

theorem Region.missingCol {n m : Nat} {S : Finset Nat} {r : Region} (fits : r.Fits S) {j₀ : Fin m}
    (h : j₀ ∉ colVars n m S) : j₀ ∉ colVars n m r.vars := by
  intro he
  exact h (Finset.mem_filter.2 ⟨Finset.mem_univ _, fits.2 (Finset.mem_filter.1 he).2⟩)

def Form.compile : Form → Nat → Circuit
  | .var k, _ => ⟨[], k⟩
  | .not f, w =>
    let a := f.compile w
    ⟨a.gates ++ [⟨.not, [a.output]⟩], w + a.size⟩
  | .and f g, w =>
    let a := f.compile w
    let b := g.compile (w + a.size)
    ⟨a.gates ++ b.gates ++ [⟨.and,[a.output,b.output]⟩], w + a.size + b.size⟩
  | .or f g, w =>
    let a := f.compile w
    let b := g.compile (w + a.size)
    ⟨a.gates ++ b.gates ++ [⟨.or,[a.output,b.output]⟩], w + a.size + b.size⟩

theorem Form.compile_size (f : Form) (w : Nat) :
    (f.compile w).size = f.bins + f.nots := by
  induction f generalizing w with
  | var => rfl
  | not a ih => simp [Circuit.size] at ih; simp [compile, bins, nots, Circuit.size, ih]; omega
  | and a b ia ib => simp [Circuit.size] at ia ib; simp [compile, bins, nots, Circuit.size, ia, ib]; omega
  | or a b ia ib => simp [Circuit.size] at ia ib; simp [compile, bins, nots, Circuit.size, ia, ib]; omega

theorem Form.compile_fan (f : Form) (w : Nat) : FanInTwo (f.compile w) := by
  induction f generalizing w with
  | var => simp [FanInTwo, compile]
  | not a ih =>
    intro g hg
    simp only [compile, List.mem_append, List.mem_singleton] at hg
    rcases hg with h | rfl
    · exact ih _ _ h
    · simp
  | and a b ia ib =>
    intro g hg
    simp only [compile, List.mem_append, List.mem_singleton] at hg
    rcases hg with (h | h) | rfl
    · exact ia _ _ h
    · exact ib _ _ h
    · simp
  | or a b ia ib =>
    intro g hg
    simp only [compile, List.mem_append, List.mem_singleton] at hg
    rcases hg with (h | h) | rfl
    · exact ia _ _ h
    · exact ib _ _ h
    · simp

theorem Form.compile_mono (f : Form) (w : Nat) (h : f.nots = 0) :
    Monotone2 (f.compile w) := by
  induction f generalizing w with
  | var => simp [Monotone2, compile]
  | not a ih => simp [nots] at h
  | and a b ia ib =>
    have hh : a.nots = 0 ∧ b.nots = 0 := Nat.add_eq_zero_iff.mp h
    intro g hg
    simp only [compile, List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | rfl
    · exact ia _ hh.1 _ hg
    · exact ib _ hh.2 _ hg
    · simp
  | or a b ia ib =>
    have hh : a.nots = 0 ∧ b.nots = 0 := Nat.add_eq_zero_iff.mp h
    intro g hg
    simp only [compile, List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | rfl
    · exact ia _ hh.1 _ hg
    · exact ib _ hh.2 _ hg
    · simp

theorem Form.compile_eval (f : Form) (N : Nat) (hb : ∀ i ∈ f.vars, i < N)
    (x : Nat → Bool) (w : List Bool) (hw : ∀ i < N, w.getD i false = x i)
    (hlen : N ≤ w.length) :
    let c := f.compile w.length
    c.output < w.length + c.size ∧
    (wiresFrom c.gates w).getD c.output false = f.eval x := by
  induction f generalizing w with
  | var v =>
    have hv := hb v (by simp [vars])
    exact ⟨by simpa [compile, Circuit.size] using hv.trans_le hlen, hw v hv⟩
  | not a ih =>
    obtain ⟨_, he⟩ := ih hb w hw hlen
    let c := a.compile w.length
    change w.length + c.size < w.length + (c.gates ++ [_]).length ∧
      (wiresFrom (c.gates ++ [_]) w).getD (w.length + c.size) false = !(a.eval x)
    constructor
    · simp [Circuit.size]
    · rw [wiresFrom_snoc, getD_snoc, length_wiresFrom]
      simpa [c, Circuit.size, GateOp.eval, he]
  | and a b ia ib =>
    have ha : ∀ i ∈ a.vars, i < N := fun i hi => hb i (by simp [vars,hi])
    have hb' : ∀ i ∈ b.vars, i < N := fun i hi => hb i (by simp [vars,hi])
    let ca := a.compile w.length
    let wa := wiresFrom ca.gates w
    have hwa : wa.length = w.length + ca.size := length_wiresFrom _ _
    let cb := b.compile (w.length + ca.size)
    obtain ⟨haout, hae⟩ := ia ha w hw hlen
    have hstay : ∀ i < N, wa.getD i false = x i := fun i hi =>
      (getD_wiresFrom _ _ _ (hi.trans_le hlen)).trans (hw i hi)
    obtain ⟨_, hbe⟩ := ib hb' wa hstay (by omega)
    rw [hwa] at hbe
    change (wiresFrom cb.gates wa).getD cb.output false = b.eval x at hbe
    have haout' : ca.output < wa.length := by rw [hwa]; exact haout
    have ha' : (wiresFrom cb.gates wa).getD ca.output false = a.eval x :=
      (getD_wiresFrom _ _ _ haout').trans hae
    change w.length + ca.size + cb.size <
      w.length + ((ca.gates ++ cb.gates) ++ [_]).length ∧
      (wiresFrom ((ca.gates ++ cb.gates) ++ [_]) w).getD (w.length + ca.size + cb.size) false =
      (a.eval x && b.eval x)
    constructor
    · simp [Circuit.size]; omega
    · rw [wiresFrom_snoc, getD_snoc, length_wiresFrom, List.length_append, wiresFrom_append]
      have e : w.length + ca.size + cb.size = w.length + (ca.gates.length + cb.gates.length) := by
        simp [Circuit.size, Nat.add_assoc]
      simp only [e, ite_true, List.map_cons, List.map_nil, GateOp.eval, List.all_cons,
        List.all_nil, id_eq, Bool.and_true]
      rw [ha', hbe]
  | or a b ia ib =>
    have ha : ∀ i ∈ a.vars, i < N := fun i hi => hb i (by simp [vars,hi])
    have hb' : ∀ i ∈ b.vars, i < N := fun i hi => hb i (by simp [vars,hi])
    let ca := a.compile w.length
    let wa := wiresFrom ca.gates w
    have hwa : wa.length = w.length + ca.size := length_wiresFrom _ _
    let cb := b.compile (w.length + ca.size)
    obtain ⟨haout, hae⟩ := ia ha w hw hlen
    have hstay : ∀ i < N, wa.getD i false = x i := fun i hi =>
      (getD_wiresFrom _ _ _ (hi.trans_le hlen)).trans (hw i hi)
    obtain ⟨_, hbe⟩ := ib hb' wa hstay (by omega)
    rw [hwa] at hbe
    change (wiresFrom cb.gates wa).getD cb.output false = b.eval x at hbe
    have haout' : ca.output < wa.length := by rw [hwa]; exact haout
    have ha' : (wiresFrom cb.gates wa).getD ca.output false = a.eval x :=
      (getD_wiresFrom _ _ _ haout').trans hae
    change w.length + ca.size + cb.size <
      w.length + ((ca.gates ++ cb.gates) ++ [_]).length ∧
      (wiresFrom ((ca.gates ++ cb.gates) ++ [_]) w).getD (w.length + ca.size + cb.size) false =
      (a.eval x || b.eval x)
    constructor
    · simp [Circuit.size]; omega
    · rw [wiresFrom_snoc, getD_snoc, length_wiresFrom, List.length_append, wiresFrom_append]
      have e : w.length + ca.size + cb.size = w.length + (ca.gates.length + cb.gates.length) := by
        simp [Circuit.size, Nat.add_assoc]
      simp only [e, ite_true, List.map_cons, List.map_nil, GateOp.eval, List.any_cons,
        List.any_nil, id_eq, Bool.or_false]
      rw [ha', hbe]

theorem Form.compile_rep {n m : Nat} {A : Fin n → Fin m → Bool} (f : Form)
    (hb : ∀ i ∈ f.vars, i < n + m) (he : ∀ i j, f.eval (oneEachFn i j) = A i j) :
    Represents A (f.compile (n+m)) := by
  intro i j
  have h := (f.compile_eval (n+m) hb (oneEachFn i j) (oneEach i j)
    (fun k _ => oneEach_getD i j k) (by rw [oneEach_len])).2
  rw [oneEach_len] at h
  exact h.trans (he i j)

end PEqualNP.Outside.L_meta_29937_aux

namespace PEqualNP.Outside.L_meta_29937_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def unionForms (l : List Form) : Region :=
  l.foldr (fun f r => Region.join (some f) r) none

theorem unionForms_eval (l : List Form) (x : Nat → Bool) :
    (unionForms l).eval x = l.any (Form.eval x) := by
  induction l with
  | nil => rfl
  | cons f l ih =>
    change (Region.join (some f) (unionForms l)).eval x = _
    rw [Region.join_eval, ih]
    rfl

theorem unionForms_vars (l : List Form) (i : Nat) :
    i ∈ (unionForms l).vars ↔ ∃ f ∈ l, i ∈ Form.vars f := by
  induction l with
  | nil => simp [unionForms, Region.vars]
  | cons f l ih =>
    change i ∈ (Region.join (some f) (unionForms l)).vars ↔ _
    rw [Region.join_vars, Finset.mem_union, ih]; simp [Region.vars]

theorem unionForms_good (l : List Form) (h : ∀ f ∈ l, Region.Good (some f))
    (hp : l.Pairwise (fun a b => Disjoint a.vars b.vars)) :
    (unionForms l).Good := by
  induction l with
  | nil => trivial
  | cons f l ih =>
    have hrest := List.pairwise_cons.mp hp
    apply Region.join_good (h _ (by simp)) (ih (fun a ha => h a (by simp [ha])) hrest.2)
    refine Finset.disjoint_left.mpr (fun i hi hj => ?_)
    obtain ⟨g,hg,hi'⟩ := (unionForms_vars l i).mp hj
    exact Finset.disjoint_left.mp (hrest.1 g hg) hi hi'

def tagWires {n m : Nat} (row : Fin n → Fin 5) (col : Fin m → Fin 5) (t : Fin 5) : Finset Nat :=
  (Finset.univ.filter (fun i => row i = t)).image Fin.val ∪
    (Finset.univ.filter (fun j => col j = t)).image (fun j => n + j.val)

theorem tagWires_mem {n m : Nat} (row : Fin n → Fin 5) (col : Fin m → Fin 5) (t : Fin 5) (w : Nat) :
    w ∈ tagWires row col t ↔ (∃ i, row i = t ∧ w = i.val) ∨
                              (∃ j, col j = t ∧ w = n + j.val) := by
  simp only [tagWires,Finset.mem_union,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
  simp only [eq_comm]

theorem tagWires_disj {n m : Nat} (row : Fin n → Fin 5) (col : Fin m → Fin 5) {a b : Fin 5}
    (hab : a ≠ b) : Disjoint (tagWires row col a) (tagWires row col b) := by
  refine Finset.disjoint_left.mpr fun k hka hkb => ?_
  rw [tagWires_mem] at hka hkb
  rcases hka with ⟨i,hi,hik⟩ | ⟨j,hj,hjk⟩ <;>
  rcases hkb with ⟨i',hi',hi'k⟩ | ⟨j',hj',hj'k⟩
  · have he : i = i' := Fin.ext (hik.symm.trans hi'k)
    exact hab (hi.symm.trans (he ▸ hi'))
  · have hiN := i.isLt
    omega
  · have hiN := i'.isLt
    omega
  · have he : j = j' := Fin.ext (by omega)
    exact hab (hj.symm.trans (he ▸ hj'))

noncomputable def singletonMask {n m : Nat} (row : Fin n → Fin 5) (col : Fin m → Fin 5) (t : Fin 5) :
    Region :=
  unionForms ((tagWires row col t).toList.map Form.var)

theorem singletonMask_vars {n m : Nat} (row : Fin n → Fin 5) (col : Fin m → Fin 5) (t : Fin 5) :
    (singletonMask row col t).vars = tagWires row col t := by
  ext i
  simp [singletonMask, unionForms_vars, Form.vars]

theorem singletonMask_good {n m : Nat} (row : Fin n → Fin 5) (col : Fin m → Fin 5) (t : Fin 5) :
    (singletonMask row col t).Good := by
  unfold singletonMask
  apply unionForms_good
  · intro f hf
    obtain ⟨_,_,rfl⟩ := List.mem_map.mp hf
    exact ⟨trivial,rfl⟩
  · rw [List.pairwise_map]
    have hn : ((tagWires row col t).toList).Pairwise (fun a b : Nat => a ≠ b) := (tagWires row col t).nodup_toList
    refine List.Pairwise.imp (fun {a b} hab => ?_) hn
    simpa [Form.vars] using hab

theorem singletonMask_eval {n m : Nat} (row : Fin n → Fin 5) (col : Fin m → Fin 5)
    (t : Fin 5) (i : Fin n) (j : Fin m) :
    (singletonMask row col t).eval (oneEachFn i j) = decide (row i = t ∨ col j = t) := by
  rw [singletonMask, unionForms_eval]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.mem_map, Finset.mem_toList, exists_exists_and_eq_and,
    Form.eval, oneEachFn, decide_eq_true_eq]
  constructor
  · rintro ⟨w, hw, hip | hjp⟩
    · left
      rcases (tagWires_mem row col t w).mp hw with ⟨i',h,r⟩ | ⟨j',_,r⟩
      · have he : i = i' := Fin.ext (hip.symm.trans r)
        exact he ▸ h
      · have hiN := i.isLt
        omega
    · right
      rcases (tagWires_mem row col t w).mp hw with ⟨i',_,r⟩ | ⟨j',h,r⟩
      · have hiN := i'.isLt
        omega
      · have he : j = j' := Fin.ext (by omega)
        exact he ▸ h
  · rintro (hr | hc)
    · exact ⟨i.val,(tagWires_mem row col t _).mpr (Or.inl ⟨i,hr,rfl⟩),Or.inl rfl⟩
    · exact ⟨n+j.val,(tagWires_mem row col t _).mpr (Or.inr ⟨j,hc,rfl⟩),Or.inr rfl⟩

def matchPairs {n m : Nat} (edge : Fin n → Fin m → Bool) : Finset (Fin n × Fin m) :=
  Finset.univ.filter fun p => edge p.1 p.2 = true

def matchForm {n m : Nat} (p : Fin n × Fin m) : Form :=
  .and (.var p.1.val) (.var (n + p.2.val))

noncomputable def matchMask {n m : Nat} (edge : Fin n → Fin m → Bool) : Region :=
  unionForms ((matchPairs edge).toList.map matchForm)

theorem matchMask_vars {n m : Nat} {row : Fin n → Fin 5} {col : Fin m → Fin 5}
    {edge : Fin n → Fin m → Bool} (he : ∀ i j, edge i j = true → row i = 4 ∧ col j = 4) :
    (matchMask edge).vars ⊆ tagWires row col 4 := by
  intro w hw
  obtain ⟨f,hf,hw⟩ := (unionForms_vars _ _).mp hw
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hf
  have hp' : edge p.1 p.2 = true := by simpa [matchPairs] using hp
  rw [tagWires_mem]
  rcases (show w = p.1.val ∨ w = n+p.2.val by simpa [matchForm, Form.vars] using hw) with hw | hw
  · exact Or.inl ⟨p.1,(he _ _ hp').1,hw⟩
  · exact Or.inr ⟨p.2,(he _ _ hp').2,hw⟩

theorem matchMask_good {n m : Nat} {row : Fin n → Fin 5} {col : Fin m → Fin 5}
    {edge : Fin n → Fin m → Bool} (he : ∀ i j, edge i j = true → row i = 4 ∧ col j = 4)
    (hr : ∀ i, row i = 4 → ∃! j, edge i j = true)
    (hc : ∀ j, col j = 4 → ∃! i, edge i j = true) :
    (matchMask edge).Good := by
  unfold matchMask
  apply unionForms_good
  · intro f hf
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp hf
    have hb := p.1.isLt
    exact ⟨by simp [matchForm, Form.ReadOnce, Form.vars]; omega,rfl⟩
  · rw [List.pairwise_map]
    have h := (matchPairs edge).nodup_toList
    apply (List.pairwise_iff_getElem).mpr
    intro i j hi hj hij
    have hpq := (List.pairwise_iff_getElem.mp h) i j hi hj hij
    let p := (matchPairs edge).toList[i]
    let q := (matchPairs edge).toList[j]
    change p ≠ q at hpq
    have hp : edge p.1 p.2 = true := by
      have hh : p ∈ (matchPairs edge).toList := List.getElem_mem hi
      exact (Finset.mem_filter.mp (Finset.mem_toList.mp hh)).2
    have hq : edge q.1 q.2 = true := by
      have hh : q ∈ (matchPairs edge).toList := List.getElem_mem hj
      exact (Finset.mem_filter.mp (Finset.mem_toList.mp hh)).2
    have hpr : p.1 ≠ q.1 := by
      intro heq
      obtain ⟨u,_,hu⟩ := hr p.1 (he _ _ hp).1
      have hq' : edge p.1 q.2 = true := heq.symm ▸ hq
      exact hpq (Prod.ext heq ((hu _ hp).trans (hu _ hq').symm))
    have hpc : p.2 ≠ q.2 := by
      intro heq
      obtain ⟨u,_,hu⟩ := hc p.2 (he _ _ hp).2
      have hq' : edge q.1 p.2 = true := heq.symm ▸ hq
      exact hpq (Prod.ext ((hu _ hp).trans (hu _ hq').symm) heq)
    change Disjoint (matchForm p).vars (matchForm q).vars
    rw [Finset.disjoint_left]
    intro k hkp hkq
    simp only [matchForm,Form.vars,Finset.mem_union,Finset.mem_singleton] at hkp hkq
    rcases hkp with hp' | hp' <;> rcases hkq with hq' | hq'
    · exact hpr (Fin.ext (hp'.symm.trans hq'))
    · have := p.1.isLt
      omega
    · have := q.1.isLt
      omega
    · exact hpc (Fin.ext (by omega))

theorem matchMask_eval {n m : Nat} (edge : Fin n → Fin m → Bool) (i : Fin n) (j : Fin m) :
    (matchMask edge).eval (oneEachFn i j) = edge i j := by
  have h (p : Fin n × Fin m) :
      (matchForm p).eval (oneEachFn i j) = decide (p = (i,j)) := by
    have hi := p.1.isLt
    have hj := i.isLt
    have hl : p.1.val ≠ n + j.val := by omega
    have hr : n + p.2.val ≠ i.val := by omega
    simp [matchForm,Form.eval,oneEachFn,hl,hr,Prod.ext_iff,Fin.ext_iff]
  rw [matchMask, unionForms_eval]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.mem_map, Finset.mem_toList, exists_exists_and_eq_and,
    h, decide_eq_true_eq, exists_eq_right, matchPairs, Finset.mem_filter,
    Finset.mem_univ, true_and]

theorem Form.withinBudget {n m : Nat} {A : Fin n → Fin m → Bool} (f : Form)
    (hro : f.ReadOnce) (hnot : f.nots ≤ 1) (i : Fin n) (j : Fin m)
    (hvars : ∀ w ∈ f.vars, w < n+m ∧ w ≠ i.val ∧ w ≠ n+j.val)
    (heval : ∀ a b, f.eval (oneEachFn a b) = A a b) :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ n + m - 2 ∧ Represents A C := by
  refine ⟨f.compile (n+m), f.compile_fan _, ?_, f.compile_rep (fun w hw => (hvars w hw).1) heval⟩
  have hab : i.val ≠ n+j.val := by have := i.isLt; omega
  have key : (insert i.val (insert (n+j.val) f.vars)).card ≤ n+m := by
    have hh : insert i.val (insert (n+j.val) f.vars) ⊆ Finset.range (n+m) := by
      intro w hw
      simp only [Finset.mem_insert,Finset.mem_range] at hw ⊢
      rcases hw with rfl | rfl | h
      · have := i.isLt; omega
      · have := j.isLt; omega
      · exact (hvars w h).1
    simpa using Finset.card_le_card hh
  have hii : i.val ∉ f.vars := fun h => (hvars _ h).2.1 rfl
  have hjj : n+j.val ∉ f.vars := fun h => (hvars _ h).2.2 rfl
  rw [Finset.card_insert_of_notMem (by simp [hab,hii]), Finset.card_insert_of_notMem hjj] at key
  rw [Form.compile_size]
  have card := Form.vars_card_of_readOnce hro
  omega

theorem tagWires_within {n m : Nat} {row : Fin n → Fin 5} {col : Fin m → Fin 5}
    {i : Fin n} {j : Fin m} (hi : row i = 0) (hj : col j = 0) {t : Fin 5} (ht : t ≠ 0)
    {w : Nat} (hw : w ∈ tagWires row col t) : w < n+m ∧ w ≠ i.val ∧ w ≠ n+j.val := by
  rcases (tagWires_mem _ _ _ _).mp hw with ⟨a,ha,rfl⟩ | ⟨b,hb,rfl⟩
  · refine ⟨by have := a.isLt; omega, ?_, by have := a.isLt; omega⟩
    intro h
    exact ht (ha.symm.trans ((Fin.ext h : a = i) ▸ hi))
  · refine ⟨by have := b.isLt; omega, by have := i.isLt; omega, ?_⟩
    intro h
    exact ht (hb.symm.trans ((Fin.ext (by omega) : b = j) ▸ hj))

theorem singletonMask_some {n m : Nat} {row : Fin n → Fin 5} {col : Fin m → Fin 5} {t : Fin 5}
    (hi : (∃ i, row i = t) ∨ ∃ j, col j = t) :
    ∃ f, singletonMask row col t = some f := by
  cases e : singletonMask row col t with
  | some f => exact ⟨f,rfl⟩
  | none =>
    rcases hi with ⟨i,hi⟩ | ⟨j,hj⟩
    · have hmem := (tagWires_mem row col t i.val).mpr (Or.inl ⟨i,hi,rfl⟩)
      rw [← singletonMask_vars, e] at hmem
      simp [Region.vars] at hmem
    · have hmem := (tagWires_mem row col t (n+j.val)).mpr (Or.inr ⟨j,hj,rfl⟩)
      rw [← singletonMask_vars, e] at hmem
      simp [Region.vars] at hmem

theorem Region.join_some {a b : Region} (h : (∃ f, a = some f) ∨ (∃ f, b = some f)) :
    ∃ f, a.join b = some f := by
  cases a <;> cases b <;> simp [Region.join] at h ⊢

theorem some_of_match {n m : Nat} {edge : Fin n → Fin m → Bool} {i : Fin n} {j : Fin m}
    (h : edge i j = true) : ∃ f, matchMask edge = some f := by
  cases e : matchMask edge with
  | none => have hf := matchMask_eval edge i j; simp [e,Region.eval,h] at hf
  | some f => exact ⟨f,rfl⟩

theorem combineOneNot {n m : Nat} {A : Fin n → Fin m → Bool}
    {r : Region} {f : Form} (hr : r.Good) (hf : f.ReadOnce) (hnot : f.nots ≤ 1)
    (hd : Disjoint r.vars f.vars) (i : Fin n) (j : Fin m)
    (hw : ∀ w ∈ r.vars ∪ f.vars, w < n+m ∧ w ≠ i.val ∧ w ≠ n+j.val)
    (he : ∀ a b, A a b = (r.eval (oneEachFn a b) || f.eval (oneEachFn a b))) :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ n+m-2 ∧ Represents A C := by
  cases r with
  | none =>
    exact f.withinBudget hf hnot i j (fun w h => hw w (Finset.mem_union_right _ h))
      (by intro a b; simpa [Region.eval] using (he a b).symm)
  | some g =>
    exact (Form.or g f).withinBudget ⟨hr.1,hf,hd⟩
      (by simpa [Form.nots,hr.2]) i j hw (fun a b => (he a b).symm)

theorem tagConstruct {n m : Nat} {A : Fin n → Fin m → Bool}
    (row : Fin n → Fin 5) (col : Fin m → Fin 5) (edge : Fin n → Fin m → Bool)
    (i : Fin n) (j : Fin m) (hi : row i = 0) (hj : col j = 0)
    (he : ∀ u v, edge u v = true → row u = 4 ∧ col v = 4)
    (hr : ∀ u, row u = 4 → ∃! v, edge u v = true)
    (hc : ∀ v, col v = 4 → ∃! u, edge u v = true)
    (desc :
      let has := fun t : Fin 5 => (∃ i, row i = t) ∨ ∃ j, col j = t
      let hit := fun (t : Fin 5) (i : Fin n) (j : Fin m) => decide (row i = t ∨ col j = t)
      ((has 1 ∧ has 2 ∧ ∀ i j, A i j =
          (hit 3 i j || edge i j || (hit 2 i j && !(hit 1 i j)))) ∨
       (¬has 3 ∧ (has 2 ∨ has 4) ∧ ∀ i j, A i j =
          (hit 1 i j || !(hit 2 i j || edge i j))))) :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ n+m-2 ∧ Represents A C := by
  let G := singletonMask row col
  let E := matchMask edge
  let Tg := tagWires row col
  have mg : ∀ t, (G t).Good := singletonMask_good row col
  have ev : ∀ t u v, (G t).eval (oneEachFn u v) = decide (row u = t ∨ col v = t) :=
    singletonMask_eval row col
  have ee : ∀ u v, E.eval (oneEachFn u v) = edge u v := matchMask_eval edge
  have me : E.Good := matchMask_good he hr hc
  have ve : E.vars ⊆ Tg 4 := matchMask_vars he
  have vv : ∀ t, (G t).vars = Tg t := singletonMask_vars row col
  have dd : ∀ {a b}, a ≠ b → Disjoint (Tg a) (Tg b) :=
    fun h => tagWires_disj row col h
  have within : ∀ {t w}, t ≠ 0 → w ∈ Tg t → w < n+m ∧ w ≠ i.val ∧ w ≠ n+j.val :=
    fun ht hw => tagWires_within hi hj ht hw
  rcases desc with ⟨h1,h2,hF⟩ | ⟨_,h2or,hF⟩
  · obtain ⟨f1,e1⟩ := singletonMask_some h1
    obtain ⟨f2,e2⟩ := singletonMask_some h2
    change G 1 = some f1 at e1
    change G 2 = some f2 at e2
    have g1 := mg 1
    have g2 := mg 2
    rw [e1] at g1
    rw [e2] at g2
    have v1 := vv 1
    have v2 := vv 2
    rw [e1] at v1
    rw [e2] at v2
    change f1.vars = Tg 1 at v1
    change f2.vars = Tg 2 at v2
    let f := Form.and f2 (.not f1)
    have hfvars : f.vars = Tg 2 ∪ Tg 1 := by simp [f, Form.vars, v1, v2]
    have hfro : f.ReadOnce := ⟨g2.1, g1.1, by change Disjoint f2.vars f1.vars; rw [v2,v1]; exact dd (by decide)⟩
    have hfnot : f.nots ≤ 1 := by
      have h1z := g1.2
      have h2z := g2.2
      change f1.nots = 0 at h1z
      change f2.nots = 0 at h2z
      simp [f,Form.nots,h1z,h2z]
    let r := (G 3).join E
    have vr : r.vars = Tg 3 ∪ E.vars := by
      rw [Region.join_vars,vv]
    have rg : r.Good := Region.join_good (mg 3) me
      (by rw [vv]; exact (dd (by decide : (3 : Fin 5) ≠ 4)).mono_right ve)
    refine combineOneNot rg hfro hfnot ?_ i j ?_ ?_
    · rw [vr,hfvars,Finset.disjoint_union_left,Finset.disjoint_union_right,Finset.disjoint_union_right]
      exact ⟨⟨dd (by decide),dd (by decide)⟩,
        ⟨(dd (by decide)).mono_left ve,(dd (by decide)).mono_left ve⟩⟩
    · intro w hw
      rw [vr,hfvars] at hw
      simp only [Finset.mem_union] at hw
      rcases hw with (a | b) | (c | d)
      · exact within (by decide) a
      · exact within (by decide) (ve b)
      · exact within (by decide) c
      · exact within (by decide) d
    · intro u v
      have a := ev 1 u v
      have b := ev 2 u v
      rw [e1] at a
      rw [e2] at b
      change f1.eval _ = _ at a
      change f2.eval _ = _ at b
      simpa only [r, f, Region.join_eval, ee, ev, Form.eval, a,b] using hF u v
  · let r := (G 2).join E
    have rg : r.Good := Region.join_good (mg 2) me
      (by rw [vv]; exact (dd (by decide : (2 : Fin 5) ≠ 4)).mono_right ve)
    have ex : ∃ f, r = some f := by
      apply Region.join_some
      rcases h2or with h2 | h4
      · exact Or.inl (singletonMask_some h2)
      · right
        rcases h4 with ⟨u,hu⟩ | ⟨v,hv⟩
        · obtain ⟨v,ev,_⟩ := hr u hu
          exact some_of_match ev
        · obtain ⟨u,ev,_⟩ := hc v hv
          exact some_of_match ev
    obtain ⟨f,ef⟩ := ex
    have vg : f.vars = Tg 2 ∪ E.vars := by
      change Region.vars (some f) = _
      rw [← ef, Region.join_vars,vv]
    rw [ef] at rg
    have hn : (Form.not f).nots ≤ 1 := by
      have z := rg.2
      change f.nots = 0 at z
      simp [Form.nots,z]
    refine combineOneNot (mg 1) (show (Form.not f).ReadOnce from rg.1) hn ?_ i j ?_ ?_
    · change Disjoint ((G 1).vars) f.vars
      rw [vv,vg,Finset.disjoint_union_right]
      exact ⟨dd (by decide),(dd (by decide)).mono_right ve⟩
    · intro w hw
      change w ∈ (G 1).vars ∪ f.vars at hw
      rw [vv,vg] at hw
      simp only [Finset.mem_union] at hw
      rcases hw with a | b | c
      · exact within (by decide) a
      · exact within (by decide) b
      · exact within (by decide) (ve c)
    · intro u v
      have h : r.eval (oneEachFn u v) =
          (decide (row u = 2 ∨ col v = 2) || edge u v) := by
        rw [Region.join_eval, ev, ee]
      rw [ef] at h
      change f.eval _ = _ at h
      simpa only [Form.eval, ev, h] using hF u v

end PEqualNP.Outside.L_meta_29937_aux

namespace PEqualNP.Outside.L_meta_29937_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

structure PosSplit {n m : Nat} (F : Fin n → Fin m → Bool) (R : Finset (Fin n))
    (S : Finset (Fin m)) where
  sr : Finset (Fin n)
  sc : Finset (Fin m)
  E : Fin n → Fin m → Bool
  rs : sr ⊆ R
  cs : sc ⊆ S
  smallR : sr.card ≤ 1
  smallC : sc.card ≤ 1
  edgeSupp : ∀ i j, E i j = true → i ∈ R ∧ j ∈ S ∧ i ∉ sr ∧ j ∉ sc
  uniqueR : ∀ i j k, E i j = true → E i k = true → j = k
  uniqueC : ∀ i j k, E i j = true → E k j = true → i = k
  eval : ∀ i j, F i j = (decide (i ∈ sr ∨ j ∈ sc) || E i j)

theorem nf_rect_row {n m : Nat} {X : Finset (Fin n)} {Y : Finset (Fin m)}
    (nf : MonoNF n m) (hv : nf.Valid X Y) (u0 : Fin n)
    (hr : ∀ u ∈ insert u0 X, ∀ w ∈ insert u0 X,
      (∀ v, nf.eval u v = nf.eval w v) → u = w) :
    ∀ p ∈ nf.rects, p.1.card ≤ 1 := by
  classical
  rcases hv with ⟨hS, hT, hb, hpw⟩
  have equiv : ∀ p ∈ nf.rects, ∀ q ∈ nf.rects, p = q ∨ Disjoint p.1 q.1 :=
    fun p hp q hq => List.Pairwise.forall_of_forall_of_flip
      (R := fun p q : Finset (Fin n) × Finset (Fin m) => p = q ∨ Disjoint p.1 q.1)
      (fun _ _ => Or.inl rfl) (hpw.imp (fun h => Or.inr h.1))
      (hpw.imp (fun h => Or.inr h.1.symm)) hp hq
  intro p hp
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

theorem nf_rect_col {n m : Nat} {X : Finset (Fin n)} {Y : Finset (Fin m)}
    (nf : MonoNF n m) (hv : nf.Valid X Y) (v0 : Fin m)
    (hc : ∀ v ∈ insert v0 Y, ∀ z ∈ insert v0 Y,
      (∀ u, nf.eval u v = nf.eval u z) → v = z) :
    ∀ p ∈ nf.rects, p.2.card ≤ 1 := by
  classical
  rcases hv with ⟨hS, hT, hb, hpw⟩
  have equiv : ∀ p ∈ nf.rects, ∀ q ∈ nf.rects, p = q ∨ Disjoint p.2 q.2 :=
    fun p hp q hq => List.Pairwise.forall_of_forall_of_flip
      (R := fun p q : Finset (Fin n) × Finset (Fin m) => p = q ∨ Disjoint p.2 q.2)
      (fun _ _ => Or.inl rfl) (hpw.imp (fun h => Or.inr h.2))
      (hpw.imp (fun h => Or.inr h.2.symm)) hp hq
  intro p hp
  apply Finset.card_le_one.2
  intro v hv z hz
  have spec : ∀ a ∈ p.2, ∀ u, nf.eval u a = decide (u ∈ nf.S0 ∨ u ∈ p.1) := by
    intro a ha u
    simp only [MonoNF.eval, decide_eq_decide]
    have hn := Finset.disjoint_left.1 (hb p hp).2.2.2.2.2 ha
    simp only [hn,false_or]
    apply or_congr_right
    constructor
    · rintro ⟨q,hq,huq,haq⟩
      rcases equiv p hp q hq with he | hd
      · simpa [he] using huq
      · exact (Finset.disjoint_left.1 hd ha haq).elim
    · intro hup; exact ⟨p,hp,hup,ha⟩
  exact hc v (Finset.mem_insert_of_mem ((hb p hp).2.2.2.1 hv))
    z (Finset.mem_insert_of_mem ((hb p hp).2.2.2.1 hz))
    (fun u => (spec v hv u).trans (spec z hz u).symm)

noncomputable def nfSplit {n m : Nat} {X : Finset (Fin n)} {Y : Finset (Fin m)}
    (f : MonoNF n m) (hv : f.Valid X Y) (u0 : Fin n) (v0 : Fin m)
    (hr : ∀ u ∈ insert u0 X, ∀ w ∈ insert u0 X, (∀ v, f.eval u v = f.eval w v) → u = w)
    (hc : ∀ v ∈ insert v0 Y, ∀ z ∈ insert v0 Y, (∀ u, f.eval u v = f.eval u z) → v = z) :
    PosSplit f.eval X Y := by
  classical
  let E := fun i j => decide (∃ p ∈ f.rects, i ∈ p.1 ∧ j ∈ p.2)
  refine ⟨f.S0, f.T0, E, hv.1, hv.2.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_le_one]
    intro u hu w hw
    exact hr u (Finset.mem_insert_of_mem (hv.1 hu))
      w (Finset.mem_insert_of_mem (hv.1 hw)) (fun v => by simp [MonoNF.eval,hu,hw])
  · rw [Finset.card_le_one]
    intro v hv' w hw
    exact hc v (Finset.mem_insert_of_mem (hv.2.1 hv'))
      w (Finset.mem_insert_of_mem (hv.2.1 hw)) (fun u => by simp [MonoNF.eval,hv',hw])
  · intro i j hij
    obtain ⟨p,hp,hip,hjp⟩ := of_decide_eq_true hij
    have h := hv.2.2.1 p hp
    exact ⟨h.2.2.1 hip,h.2.2.2.1 hjp,Finset.disjoint_left.mp h.2.2.2.2.1 hip,
      Finset.disjoint_left.mp h.2.2.2.2.2 hjp⟩
  · intro i j k hij hik
    obtain ⟨p,hp,hip,hjp⟩ := of_decide_eq_true hij
    obtain ⟨q,hq,hiq,hkq⟩ := of_decide_eq_true hik
    have disj := List.Pairwise.forall_of_forall_of_flip
      (R := fun p q : Finset (Fin n) × Finset (Fin m) => p = q ∨ Disjoint p.1 q.1)
      (fun _ _ => Or.inl rfl) (hv.2.2.2.imp (fun h => Or.inr h.1))
      (hv.2.2.2.imp (fun h => Or.inr h.1.symm)) hp hq
    rcases disj with rfl | hd
    · exact Finset.card_le_one.mp (nf_rect_col f hv v0 hc p hp) _ hjp _ hkq
    · exact (Finset.disjoint_left.mp hd hip hiq).elim
  · intro i j k hij hkj
    obtain ⟨p,hp,hip,hjp⟩ := of_decide_eq_true hij
    obtain ⟨q,hq,hkq,hjq⟩ := of_decide_eq_true hkj
    have disj := List.Pairwise.forall_of_forall_of_flip
      (R := fun p q : Finset (Fin n) × Finset (Fin m) => p = q ∨ Disjoint p.2 q.2)
      (fun _ _ => Or.inl rfl) (hv.2.2.2.imp (fun h => Or.inr h.2))
      (hv.2.2.2.imp (fun h => Or.inr h.2.symm)) hp hq
    rcases disj with rfl | hd
    · exact Finset.card_le_one.mp (nf_rect_row f hv u0 hr p hp) _ hip _ hkq
    · exact (Finset.disjoint_left.mp hd hjp hjq).elim
  · intro i j
    simp [MonoNF.eval,E,Bool.or_assoc]

theorem regionSplit {n m : Nat} (r : Region) (g : r.Good)
    (hb : ∀ i ∈ r.vars, i < n+m) (z : Fin n) (t : Fin m)
    (hr : ∀ i ∈ insert z (rowVars n r.vars), ∀ i' ∈ insert z (rowVars n r.vars),
      (∀ j : Fin m, r.table i j = r.table i' j) → i = i')
    (hc : ∀ j ∈ insert t (colVars n m r.vars), ∀ j' ∈ insert t (colVars n m r.vars),
      (∀ i : Fin n, r.table i j = r.table i j') → j = j') :
    Nonempty (PosSplit (@Region.table n m r) (rowVars n r.vars) (colVars n m r.vars)) := by
  cases r with
  | none =>
    refine ⟨⟨∅,∅,fun _ _ => false, by simp, by simp, by simp, by simp, ?_, ?_, ?_, ?_⟩⟩
    · simp
    · simp
    · simp
    · simp [Region.table,Region.eval]
  | some f =>
    obtain ⟨nf,hv,he⟩ := mono_normal_form n m f g.1 g.2 hb
    have hr' : ∀ i ∈ insert z (rowVars n f.vars), ∀ i' ∈ insert z (rowVars n f.vars),
        (∀ j : Fin m, nf.eval i j = nf.eval i' j) → i = i' := by
      intro i hi i' hi' hh
      apply hr i hi i' hi'
      intro j
      change f.eval (oneEachFn i j) = f.eval (oneEachFn i' j)
      rw [he,he,hh]
    have hc' : ∀ j ∈ insert t (colVars n m f.vars), ∀ j' ∈ insert t (colVars n m f.vars),
        (∀ i : Fin n, nf.eval i j = nf.eval i j') → j = j' := by
      intro j hj j' hj' hh
      apply hc j hj j' hj'
      intro i
      change f.eval (oneEachFn i j) = f.eval (oneEachFn i j')
      rw [he,he,hh]
    let x := nfSplit nf hv z t hr' hc'
    exact ⟨⟨x.sr,x.sc,x.E,x.rs,x.cs,x.smallR,x.smallC,x.edgeSupp,x.uniqueR,x.uniqueC,
      fun i j => (he i j).trans (x.eval i j)⟩⟩

def labelOf (one two three pair : Prop)
    [Decidable one] [Decidable two] [Decidable three] [Decidable pair] : Fin 5 :=
  if one then 1 else if two then 2 else if three then 3 else if pair then 4 else 0

theorem labelOf_specs (one two three pair : Prop)
    [Decidable one] [Decidable two] [Decidable three] [Decidable pair]
    (h1 : one → ¬two ∧ ¬three ∧ ¬pair) (h2 : two → ¬three ∧ ¬pair)
    (h3 : three → ¬pair) :
    ((labelOf one two three pair = 1) ↔ one) ∧
    ((labelOf one two three pair = 2) ↔ two) ∧
    ((labelOf one two three pair = 3) ↔ three) ∧
    ((labelOf one two three pair = 4) ↔ pair) := by
  by_cases a : one <;> by_cases b : two <;> by_cases c : three <;>
    by_cases d : pair <;> simp_all [labelOf]

theorem rowLabelInj {n m : Nat} {A E : Fin n → Fin m → Bool} {row : Fin n → Fin 5}
    {col : Fin m → Fin 5} (hr : Function.Injective A)
    (he : ∀ i j, E i j = true → row i = 4)
    (ha : ∀ i j, A i j =
      (decide (row i = 3 ∨ col j = 3) || E i j ||
        (decide (row i = 2 ∨ col j = 2) && !decide (row i = 1 ∨ col j = 1)))) :
    ∀ i u, row i = row u → row i ≠ 4 → i = u := by
  intro i u h hne
  apply hr
  funext j
  have hz : E i j = false := by
    cases h : E i j
    · rfl
    · exact (hne (he _ _ h)).elim
  have hz' : E u j = false := by
    cases hh : E u j
    · rfl
    · exact (hne (h.trans (he _ _ hh))).elim
  rw [ha i,ha u,h,hz,hz']

theorem labelRecipes {α : Type*} [DecidableEq α] {R₁ R₂ R₃ U₁ U₂ U₃ : Finset α}
    {P₂ P₃ : α → Prop} [DecidablePred P₂] [DecidablePred P₃]
    (r₁ : U₁ ⊆ R₁) (r₂ : U₂ ⊆ R₂) (r₃ : U₃ ⊆ R₃)
    (d12 : Disjoint R₁ R₂) (d13 : Disjoint R₁ R₃) (d23 : Disjoint R₂ R₃)
    (e₂ : ∀ x, P₂ x → x ∈ R₂ ∧ x ∉ U₂) (e₃ : ∀ x, P₃ x → x ∈ R₃ ∧ x ∉ U₃) :
    let a := fun x => labelOf (x ∈ U₁) (x ∈ U₂) (x ∈ U₃) (P₂ x ∨ P₃ x)
    (∀ x, (a x = 1 ↔ x ∈ U₁) ∧ (a x = 2 ↔ x ∈ U₂) ∧ (a x = 3 ↔ x ∈ U₃) ∧
      (a x = 4 ↔ P₂ x ∨ P₃ x)) ∧
    (∀ x, x ∉ R₁ → x ∉ R₂ → x ∉ R₃ → a x = 0) := by
  have h12 := Finset.disjoint_left.mp d12
  have h13 := Finset.disjoint_left.mp d13
  have h23 := Finset.disjoint_left.mp d23
  constructor
  · intro x
    apply labelOf_specs
    · intro hx
      refine ⟨fun h => h12 (r₁ hx) (r₂ h),fun h => h13 (r₁ hx) (r₃ h),?_⟩
      rintro (h | h)
      · exact h12 (r₁ hx) (e₂ x h).1
      · exact h13 (r₁ hx) (e₃ x h).1
    · intro hx
      refine ⟨fun h => h23 (r₂ hx) (r₃ h),?_⟩
      rintro (h | h)
      · exact (e₂ x h).2 hx
      · exact h23 (r₂ hx) (e₃ x h).1
    · intro hx
      rintro (h | h)
      · exact h23 (e₂ x h).1 (r₃ hx)
      · exact (e₃ x h).2 hx
  · intro x h1 h2 h3
    have hn1 : x ∉ U₁ := fun h => h1 (r₁ h)
    have hn2 : x ∉ U₂ := fun h => h2 (r₂ h)
    have hn3 : x ∉ U₃ := fun h => h3 (r₃ h)
    have he2 : ¬ P₂ x := fun h => h2 (e₂ x h).1
    have he3 : ¬ P₃ x := fun h => h3 (e₃ x h).1
    simp [labelOf, hn1, hn2, hn3, he2, he3]

structure TagData {n m : Nat} (A : Fin n → Fin m → Bool) where
  row : Fin n → Fin 5
  col : Fin m → Fin 5
  edge : Fin n → Fin m → Bool
  row0 : ∃ i, row i = 0
  col0 : ∃ j, col j = 0
  rowInj : ∀ i u, row i = row u → row i ≠ 4 → i = u
  colInj : ∀ j v, col j = col v → col j ≠ 4 → j = v
  edgeTag : ∀ i j, edge i j = true → row i = 4 ∧ col j = 4
  rowEdge : ∀ i, row i = 4 → ∃! j, edge i j = true
  colEdge : ∀ j, col j = 4 → ∃! i, edge i j = true
  formula : ∀ i j, A i j =
    (decide (row i = 3 ∨ col j = 3) || edge i j ||
       (decide (row i = 2 ∨ col j = 2) && !decide (row i = 1 ∨ col j = 1)))

theorem colLabelInj {n m : Nat} {A E : Fin n → Fin m → Bool} {row : Fin n → Fin 5}
    {col : Fin m → Fin 5} (hc : Function.Injective (fun j i => A i j))
    (he : ∀ i j, E i j = true → col j = 4)
    (ha : ∀ i j, A i j =
      (decide (row i = 3 ∨ col j = 3) || E i j ||
        (decide (row i = 2 ∨ col j = 2) && !decide (row i = 1 ∨ col j = 1)))) :
    ∀ j v, col j = col v → col j ≠ 4 → j = v := by
  apply rowLabelInj (E := (fun j i => E i j)) (col := row) hc (fun j i => he i j)
  intro j i
  simpa only [or_comm] using ha i j

theorem boolOrTrue {a b : Bool} : (a || b) = true ↔ a = true ∨ b = true := by cases a <;> cases b <;> decide

theorem tagFromSplits {n m : Nat} {A F G H : Fin n → Fin m → Bool}
    {R₁ R₂ R₃ : Finset (Fin n)} {C₁ C₂ C₃ : Finset (Fin m)}
    (B : PosSplit G R₁ C₁) (P : PosSplit F R₂ C₂) (W : PosSplit H R₃ C₃)
    (d12 : Disjoint R₁ R₂) (d13 : Disjoint R₁ R₃) (d23 : Disjoint R₂ R₃)
    (e12 : Disjoint C₁ C₂) (e13 : Disjoint C₁ C₃) (e23 : Disjoint C₂ C₃)
    (z : Fin n) (t : Fin m)
    (z1 : z ∉ R₁) (z2 : z ∉ R₂) (z3 : z ∉ R₃)
    (t1 : t ∉ C₁) (t2 : t ∉ C₂) (t3 : t ∉ C₃)
    (hr : Function.Injective A) (hc : Function.Injective (fun j i => A i j))
    (hev : ∀ i j, A i j = ((F i j && !(G i j)) || H i j)) :
    ∃ d : TagData A,
      (∀ i j, decide (d.row i = 2 ∨ d.col j = 2) = decide (i ∈ P.sr ∨ j ∈ P.sc)) ∧
      (∀ i j, d.edge i j = (P.E i j || W.E i j)) ∧
      (∀ i, d.row i = 3 ↔ i ∈ W.sr) ∧ (∀ j, d.col j = 3 ↔ j ∈ W.sc) := by
  classical
  let RP := fun i => ∃ j, P.E i j = true
  let RW := fun i => ∃ j, W.E i j = true
  let CP := fun j => ∃ i, P.E i j = true
  let CW := fun j => ∃ i, W.E i j = true
  let row := fun i => labelOf (i ∈ B.sr) (i ∈ P.sr) (i ∈ W.sr) (RP i ∨ RW i)
  let col := fun j => labelOf (j ∈ B.sc) (j ∈ P.sc) (j ∈ W.sc) (CP j ∨ CW j)
  let edge := fun i j => P.E i j || W.E i j
  have rp : ∀ i, RP i → i ∈ R₂ ∧ i ∉ P.sr := by
    rintro i ⟨j,h⟩
    have hh := P.edgeSupp i j h
    exact ⟨hh.1,hh.2.2.1⟩
  have rw' : ∀ i, RW i → i ∈ R₃ ∧ i ∉ W.sr := by
    rintro i ⟨j,h⟩
    have hh := W.edgeSupp i j h
    exact ⟨hh.1,hh.2.2.1⟩
  have cp : ∀ j, CP j → j ∈ C₂ ∧ j ∉ P.sc := by
    rintro j ⟨i,h⟩
    have hh := P.edgeSupp i j h
    exact ⟨hh.2.1,hh.2.2.2⟩
  have cw : ∀ j, CW j → j ∈ C₃ ∧ j ∉ W.sc := by
    rintro j ⟨i,h⟩
    have hh := W.edgeSupp i j h
    exact ⟨hh.2.1,hh.2.2.2⟩
  have ⟨r, rz⟩ := labelRecipes B.rs P.rs W.rs d12 d13 d23 rp rw'
  have ⟨c, cz⟩ := labelRecipes B.cs P.cs W.cs e12 e13 e23 cp cw
  have r1 (i) : row i = 1 ↔ i ∈ B.sr := (r i).1
  have r2 (i) : row i = 2 ↔ i ∈ P.sr := (r i).2.1
  have r3 (i) : row i = 3 ↔ i ∈ W.sr := (r i).2.2.1
  have r4 (i) : row i = 4 ↔ RP i ∨ RW i := (r i).2.2.2
  have c1 (j) : col j = 1 ↔ j ∈ B.sc := (c j).1
  have c2 (j) : col j = 2 ↔ j ∈ P.sc := (c j).2.1
  have c3 (j) : col j = 3 ↔ j ∈ W.sc := (c j).2.2.1
  have c4 (j) : col j = 4 ↔ CP j ∨ CW j := (c j).2.2.2
  have etag (i) (j) (h : edge i j = true) : row i = 4 ∧ col j = 4 := by
    rcases boolOrTrue.mp h with h | h
    · exact ⟨(r4 _).mpr (Or.inl ⟨j,h⟩),(c4 _).mpr (Or.inl ⟨i,h⟩)⟩
    · exact ⟨(r4 _).mpr (Or.inr ⟨j,h⟩),(c4 _).mpr (Or.inr ⟨i,h⟩)⟩
  have ur (i j k) (h : edge i j = true) (h' : edge i k = true) : j = k := by
    rcases boolOrTrue.mp h with h | h <;> rcases boolOrTrue.mp h' with h' | h'
    · exact P.uniqueR _ _ _ h h'
    · exact (Finset.disjoint_left.mp d23 (P.edgeSupp _ _ h).1 (W.edgeSupp _ _ h').1).elim
    · exact (Finset.disjoint_left.mp d23 (P.edgeSupp _ _ h').1 (W.edgeSupp _ _ h).1).elim
    · exact W.uniqueR _ _ _ h h'
  have uc (i j k) (h : edge i j = true) (h' : edge k j = true) : i = k := by
    rcases boolOrTrue.mp h with h | h <;> rcases boolOrTrue.mp h' with h' | h'
    · exact P.uniqueC _ _ _ h h'
    · exact (Finset.disjoint_left.mp e23 (P.edgeSupp _ _ h).2.1 (W.edgeSupp _ _ h').2.1).elim
    · exact (Finset.disjoint_left.mp e23 (P.edgeSupp _ _ h').2.1 (W.edgeSupp _ _ h).2.1).elim
    · exact W.uniqueC _ _ _ h h'
  have rE : ∀ i, row i = 4 → ∃! j, edge i j = true := by
    intro i hi
    rcases (r4 i).mp hi with ⟨j,h⟩ | ⟨j,h⟩
    · have e : edge i j = true := boolOrTrue.mpr (Or.inl h)
      exact ⟨j,e,fun k hk => ur i k j hk e⟩
    · have e : edge i j = true := boolOrTrue.mpr (Or.inr h)
      exact ⟨j,e,fun k hk => ur i k j hk e⟩
  have cE : ∀ j, col j = 4 → ∃! i, edge i j = true := by
    intro j hj
    rcases (c4 j).mp hj with ⟨i,h⟩ | ⟨i,h⟩
    · have e : edge i j = true := boolOrTrue.mpr (Or.inl h)
      exact ⟨i,e,fun k hk => uc k j i hk e⟩
    · have e : edge i j = true := boolOrTrue.mpr (Or.inr h)
      exact ⟨i,e,fun k hk => uc k j i hk e⟩
  have form : ∀ i j, A i j =
    (decide (row i = 3 ∨ col j = 3) || edge i j ||
       (decide (row i = 2 ∨ col j = 2) && !decide (row i = 1 ∨ col j = 1))) := by
    intro i j
    simp only [r1,r2,r3,c1,c2,c3,hev,P.eval,B.eval,W.eval]
    change
      ((decide (i ∈ P.sr ∨ j ∈ P.sc) || P.E i j) &&
        !(decide (i ∈ B.sr ∨ j ∈ B.sc) || B.E i j) ||
        (decide (i ∈ W.sr ∨ j ∈ W.sc) || W.E i j)) = _
    have bp : B.E i j = true → ¬ (i ∈ P.sr ∨ j ∈ P.sc) := by
      intro h h'
      have bh := B.edgeSupp i j h
      rcases h' with h' | h'
      · exact Finset.disjoint_left.mp d12 bh.1 (P.rs h')
      · exact Finset.disjoint_left.mp e12 bh.2.1 (P.cs h')
    have pb : P.E i j = true → ¬ (i ∈ B.sr ∨ j ∈ B.sc) := by
      intro h h'
      have ph := P.edgeSupp i j h
      rcases h' with h' | h'
      · exact Finset.disjoint_left.mp d12 (B.rs h') ph.1
      · exact Finset.disjoint_left.mp e12 (B.cs h') ph.2.1
    have pbedge : P.E i j = true → B.E i j = false := by
      intro h
      cases ee : B.E i j
      · rfl
      · exact (Finset.disjoint_left.mp d12 (B.edgeSupp _ _ ee).1 (P.edgeSupp _ _ h).1).elim
    cases pe : P.E i j <;> cases be : B.E i j
    · simp [edge,pe,be,Bool.or_assoc,Bool.or_comm,Bool.or_left_comm]
    · simp [edge,pe,be,bp be,Bool.or_assoc]
    · simp [edge,pe,be,pb pe]
    · exact (Bool.noConfusion ((pbedge pe).symm.trans be))
  exact ⟨⟨row,col,edge,⟨z,rz z z1 z2 z3⟩,⟨t,cz t t1 t2 t3⟩,
    rowLabelInj hr (fun i j h => (etag i j h).1) form,
    colLabelInj hc (fun i j h => (etag i j h).2) form,etag,rE,cE,form⟩,
    fun i j => by change decide (row i = 2 ∨ col j = 2) = _; simp only [r2,c2],fun _ _ => rfl,r3,c3⟩

theorem missingFin {k : Nat} (V : Finset (Fin k)) (card : V.card+1=k) : ∃ i, i ∉ V := by
  by_contra! all
  have hv : V = Finset.univ := by ext i; simp [all i]
  simp [hv] at card

def TagData.has {n m : Nat} {A : Fin n → Fin m → Bool} (d : TagData A) (k : Fin 5) : Prop :=
  (∃ i, d.row i = k) ∨ ∃ j, d.col j = k

def TagData.hit {n m : Nat} {A : Fin n → Fin m → Bool} (d : TagData A) (k : Fin 5)
    (i : Fin n) (j : Fin m) : Bool :=
  decide (d.row i = k ∨ d.col j = k)

theorem TagData.hit_false {n m : Nat} {A : Fin n → Fin m → Bool} (d : TagData A)
    {k : Fin 5} (h : ¬d.has k) (i : Fin n) (j : Fin m) : d.hit k i j = false := by
  simp only [TagData.hit, decide_eq_false_iff_not]
  rintro (hi | hj)
  · exact h (Or.inl ⟨i,hi⟩)
  · exact h (Or.inr ⟨j,hj⟩)

theorem TagData.edge_false {n m : Nat} {A : Fin n → Fin m → Bool} (d : TagData A)
    (h : ¬d.has 4) (i : Fin n) (j : Fin m) : d.edge i j = false := by
  cases e : d.edge i j
  · rfl
  · exact (h (Or.inl ⟨i,(d.edgeTag i j e).1⟩)).elim

theorem regionTagData {n m : Nat} (S : Finset Nat) (p b w : Region)
    (hp : p.Fits S) (hb : b.Fits S) (hw : w.Fits S)
    (dpb : Disjoint p.vars b.vars) (dpw : Disjoint p.vars w.vars) (dbw : Disjoint b.vars w.vars)
    (hlt : ∀ i ∈ S, i < n+m) (hx : (rowVars n S).card+1=n) (hy : (colVars n m S).card+1=m)
    (A : Fin n → Fin m → Bool)
    (he : ∀ i j, A i j = ((p.eval (oneEachFn i j) && !(b.eval (oneEachFn i j))) || w.eval (oneEachFn i j)))
    (hr : Function.Injective A) (hc : Function.Injective (fun j i => A i j)) :
    ∃ d : TagData A,
      (∀ i j, (p.join w).table i j = (d.hit 3 i j || d.edge i j || d.hit 2 i j)) ∧
      (w = none → ¬ d.has 3) := by
  classical
  obtain ⟨z,hz⟩ := missingFin _ hx
  obtain ⟨t,ht⟩ := missingFin _ hy
  have pz := Region.missingRow hp hz
  have bz := Region.missingRow hb hz
  have wz := Region.missingRow hw hz
  have pt := Region.missingCol hp ht
  have bt := Region.missingCol hb ht
  have wt := Region.missingCol hw ht
  let op := fun (pv bv wv : Bool) => ((pv && !bv) || wv)
  let opb := fun (bv pv wv : Bool) => ((pv && !bv) || wv)
  let opw := fun (wv pv bv : Bool) => ((pv && !bv) || wv)
  have dpr := regionalRows (F := @Region.table n m p) hr (rowVars_disjoint n dpb)
    (rowVars_disjoint n dpw) (b.localRows bz) (w.localRows wz) op he
  have dpc := regionalCols (F := @Region.table n m p) hc (colVars_disjoint n m dpb)
    (colVars_disjoint n m dpw) (b.localCols bt) (w.localCols wt) op he
  have dbr := regionalRows (F := @Region.table n m b) hr (rowVars_disjoint n dpb.symm)
    (rowVars_disjoint n dbw) (p.localRows pz) (w.localRows wz) opb he
  have dbc := regionalCols (F := @Region.table n m b) hc (colVars_disjoint n m dpb.symm)
    (colVars_disjoint n m dbw) (p.localCols pt) (w.localCols wt) opb he
  have dwr := regionalRows (F := @Region.table n m w) hr (rowVars_disjoint n dpw.symm)
    (rowVars_disjoint n dbw.symm) (p.localRows pz) (b.localRows bz) opw he
  have dwc := regionalCols (F := @Region.table n m w) hc (colVars_disjoint n m dpw.symm)
    (colVars_disjoint n m dbw.symm) (p.localCols pt) (b.localCols bt) opw he
  obtain ⟨P⟩ := regionSplit p hp.1 (fun i hi => hlt i (hp.2 hi)) z t dpr dpc
  obtain ⟨B⟩ := regionSplit b hb.1 (fun i hi => hlt i (hb.2 hi)) z t dbr dbc
  obtain ⟨W⟩ := regionSplit w hw.1 (fun i hi => hlt i (hw.2 hi)) z t dwr dwc
  obtain ⟨d,hp2,hed,hr3,hc3⟩ := tagFromSplits B P W (rowVars_disjoint _ dpb.symm)
    (rowVars_disjoint _ dbw) (rowVars_disjoint _ dpw) (colVars_disjoint _ _ dpb.symm)
    (colVars_disjoint _ _ dbw) (colVars_disjoint _ _ dpw) z t bz pz wz bt pt wt hr hc he
  refine ⟨d, ?_, ?_⟩
  · intro i j
    have h3 : d.hit 3 i j = decide (i ∈ W.sr ∨ j ∈ W.sc) := by simp only [TagData.hit, hr3,hc3]
    change (p.join w).eval (oneEachFn i j) = _
    rw [Region.join_eval]
    change (p.table i j || w.table i j) = _
    rw [P.eval,W.eval,h3,hed]
    change _ = (_ || _ || decide (d.row i = 2 ∨ d.col j = 2))
    rw [hp2]
    ac_rfl
  · intro h h3
    have wf : ∀ (i : Fin n) (j : Fin m), w.table i j = false := by rw [h]; intros; rfl
    rcases h3 with ⟨i,hi⟩ | ⟨j,hj⟩
    · have q := W.eval i t
      rw [wf] at q
      simp [Region.table, Region.eval,(hr3 i).mp hi] at q
    · have q := W.eval z j
      rw [wf] at q
      simp [Region.table, Region.eval,(hc3 j).mp hj] at q

end PEqualNP.Outside.L_meta_29937_aux

namespace PEqualNP.Outside.L_meta_29937_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem noConstantRows {n m : Nat} {A : Fin n → Fin m → Bool}
    (hn : 2 ≤ n) (hr : Function.Injective A) (b : Bool) :
    ¬ ∀ i j, A i j = b := by
  intro h
  let a : Fin n := ⟨0,by omega⟩
  let c : Fin n := ⟨1,by omega⟩
  have hh : a = c := hr (funext fun j => (h a j).trans (h c j).symm)
  have hv := congrArg Fin.val hh
  simp [a,c] at hv

theorem monoRegion {n m s : Nat} {A : Fin n → Fin m → Bool}
    (hn : 2 ≤ n) (hr : Function.Injective A) (S : Finset Nat)
    (hS : S.card ≤ s) (hb : ∀ w ∈ S, w < n+m) (r : Region) (hg : r.Fits S)
    (he : ∀ i j, r.table i j = A i j) : RepSizeAtMost A s := by
  cases r with
  | none =>
    exact (noConstantRows hn hr false (fun i j => (he i j).symm)).elim
  | some f =>
    have g : f.ReadOnce ∧ f.nots = 0 := hg.1
    have hsub : f.vars ⊆ S := hg.2
    refine ⟨f.compile (n+m),f.compile_mono _ g.2,?_,
      f.compile_rep (fun w hw => hb w (hsub hw)) he⟩
    rw [f.compile_size,g.2,Nat.add_zero]
    have a := Form.vars_card_of_readOnce g.1
    have b := (Finset.card_le_card hsub).trans hS
    omega

theorem Region.join_fits_of {a b : Region} {S : Finset Nat}
    (ha : a.Fits S) (hb : b.Fits S) (h : Disjoint a.vars b.vars) :
    (a.join b).Fits S := by
  refine ⟨Region.join_good ha.1 hb.1 h,?_⟩
  rw [Region.join_vars]
  exact Finset.union_subset ha.2 hb.2

theorem complement_inj {n m : Nat} {A : Fin n → Fin m → Bool}
    (hr : Function.Injective A) : Function.Injective (fun i j => !(A i j)) := by
  intro a b hab
  apply hr
  funext j
  exact Bool.not_inj (congrFun hab j)

end PEqualNP.Outside.L_meta_29937_aux

open PEqualNP.Outside.L_meta_29937_aux PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_29937 : (∀ (n m : Nat) (A : Fin n → Fin m → Bool),
  2 ≤ n → 2 ≤ m → Function.Injective A → Function.Injective (fun j i => A i j) →
  ∀ s : Nat, s + 2 ≤ n+m →
  ((∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ s ∧ PEqualNP.Represents.Represents A C) ↔
  PEqualNP.Represents.RepSizeAtMost A s ∨ (s+2=n+m ∧
    ∃ (row : Fin n → Fin 5) (col : Fin m → Fin 5) (edge : Fin n → Fin m → Bool),
      let has := fun t : Fin 5 => (∃ i, row i = t) ∨ ∃ j, col j = t
      let hit := fun (t : Fin 5) (i : Fin n) (j : Fin m) => decide (row i = t ∨ col j = t)
      (∃ i, row i = 0) ∧ (∃ j, col j = 0) ∧
      (∀ i a, row i = row a → row i ≠ 4 → i = a) ∧
      (∀ j b, col j = col b → col j ≠ 4 → j = b) ∧
      (∀ i j, edge i j = true → row i = 4 ∧ col j = 4) ∧
      (∀ i, row i = 4 → ∃! j, edge i j = true) ∧
      (∀ j, col j = 4 → ∃! i, edge i j = true) ∧
      ((has 1 ∧ has 2 ∧ ∀ i j, A i j =
          (hit 3 i j || edge i j || (hit 2 i j && !(hit 1 i j)))) ∨
       (¬ has 3 ∧ (has 2 ∨ has 4) ∧ ∀ i j, A i j =
          (hit 1 i j || !(hit 2 i j || edge i j))))))) := by
  intro n m A hn hm hr hc s hlim
  constructor
  · rintro ⟨C,hC,hsize,hrep⟩
    rcases threshold_shape A hn hm hr hc hlim C hC hsize hrep with h | h
    · exact Or.inl h
    obtain ⟨hs,_,f,hro,hnot,hcard,hbound,hx,hy,hf⟩ := h
    have hsparse {i : Fin n} {j : Fin m} : TwoSparse (oneEachFn i j) := oneEach_sparse i j
    have nf := Region.none_fits f.vars
    rcases readOnce_mask f hro hnot with ⟨g,hg,eg⟩ | ⟨b,u,hb,hu,dbu,eu⟩ |
      ⟨p,b,w,hp,hb,hw,dpb,dpw,dbw,ew⟩
    · exact Or.inl (monoRegion hn hr f.vars hcard.le hbound g hg
        (fun i j => (eg _ hsparse).symm.trans (hf i j)))
    · let Ac := fun i j => !(A i j)
      have hri : Function.Injective Ac := complement_inj hr
      have hci : Function.Injective (fun j i => Ac i j) :=
        complement_inj (A := fun j i => A i j) hc
      have e : ∀ i j, Ac i j = ((b.eval (oneEachFn i j) && !(u.eval (oneEachFn i j))) ||
          Region.eval none (oneEachFn i j)) := by
        intro i j
        have eq := (hf i j).symm.trans (eu _ hsparse)
        change (!(A i j)) = ((b.eval (oneEachFn i j) && !(u.eval (oneEachFn i j))) || false)
        simp only [eq,Bool.not_or,Bool.not_not,Bool.or_false]
      obtain ⟨d,_,wnone⟩ := regionTagData f.vars b u none hb hu nf dbu
        (by simp [Region.vars]) (by simp [Region.vars]) hbound hx hy Ac e hri hci
      have no3 : ¬ d.has 3 := wnone rfl
      have nonempty : d.has 2 ∨ d.has 4 := by
        by_contra! hn'
        apply noConstantRows hn hri false
        intro i j
        have eq := d.formula i j
        change Ac i j = (d.hit 3 i j || d.edge i j ||
          (d.hit 2 i j && !(d.hit 1 i j))) at eq
        simpa [d.hit_false no3 i j,d.hit_false hn'.1 i j,d.edge_false hn'.2 i j] using eq
      refine Or.inr ⟨hs,d.row,d.col,d.edge,d.row0,d.col0,d.rowInj,d.colInj,
        d.edgeTag,d.rowEdge,d.colEdge,Or.inr ⟨no3,nonempty,?_⟩⟩
      intro i j
      have eq := d.formula i j
      change (!(A i j)) = (d.hit 3 i j || d.edge i j ||
        (d.hit 2 i j && !(d.hit 1 i j))) at eq
      rw [d.hit_false no3 i j, Bool.false_or] at eq
      have disj : d.edge i j = true → d.hit 1 i j = false := by
        intro hh
        have htag := d.edgeTag i j hh
        simp [TagData.hit,htag.1,htag.2]
      change A i j = (d.hit 1 i j || !(d.hit 2 i j || d.edge i j))
      apply Bool.not_inj
      rw [eq]
      cases hh : d.edge i j
      · cases h1 : d.hit 1 i j <;> cases h2 : d.hit 2 i j <;> simp [h1,h2]
      · simp [disj hh]
    · obtain ⟨d,hd,_⟩ := regionTagData f.vars p b w hp hb hw dpb dpw dbw hbound hx hy A
        (fun i j => (hf i j).symm.trans (ew _ hsparse)) hr hc
      by_cases ok : d.has 1 ∧ d.has 2
      · exact Or.inr ⟨hs,d.row,d.col,d.edge,d.row0,d.col0,d.rowInj,d.colInj,
          d.edgeTag,d.rowEdge,d.colEdge,Or.inl ⟨ok.1,ok.2,d.formula⟩⟩
      · refine Or.inl (monoRegion hn hr f.vars hcard.le hbound (p.join w)
          (Region.join_fits_of hp hw dpw) (fun i j => ?_))
        have e := d.formula i j
        change A i j = (d.hit 3 i j || d.edge i j ||
          (d.hit 2 i j && !(d.hit 1 i j))) at e
        rw [hd,e]
        by_cases h1 : d.has 1
        · have h2 : ¬ d.has 2 := fun h2 => ok ⟨h1,h2⟩
          rw [d.hit_false h2 i j]
          simp
        · rw [d.hit_false h1 i j]
          simp
  · rintro (⟨C,hC,hsize,hR⟩ | ⟨hs,row,col,edge,⟨i,hi⟩,⟨j,hj⟩,_,_,he,hre,hce,desc⟩)
    · refine ⟨C, ?_, hsize, hR⟩
      intro g hg
      obtain ⟨hop,hlen⟩ := hC g hg
      refine ⟨?_,hlen⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
      tauto
    · obtain ⟨C,hC,hsize,hrep⟩ := tagConstruct row col edge i j hi hj he hre hce desc
      exact ⟨C,hC,by omega,hrep⟩
