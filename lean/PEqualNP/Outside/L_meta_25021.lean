import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25021_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-!
Proof of `L-meta-25021`:
  On the one-a-side promise, if `A : Fin n → Fin m → Bool` (`2 ≤ n`, `2 ≤ m`) has no equal rows
  and no equal columns and is represented by a `FanInTwo` circuit `C` of size `≤ n + m - 2`,
  then `RepSizeAtMost A (2 * (n + m) - 7)`.
-/

/-! ### Part 1: Straight-line evaluation helpers -/

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

/-! ### Part 2: Read-once formulas & backward circuit analysis -/

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

/-- Monotone backward analysis: `N.card ≤ 1 + gs.length`, and equality yields a read-once plain `Form`. -/
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

/-- Full `FanInTwo` backward analysis: either `gs` is equivalent to a plain `Monotone2` gate list
of no larger size, OR `|N| ≤ gs.length` with equality yielding a read-once 1-NOT `Form`! -/
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
    · -- Tail `gs` is equivalent to plain `gs'`
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
      · -- `g.op = GateOp.not`!
        obtain ⟨N, hcN, hdN, hfN⟩ := back_mono o gs' hgm' (t + 1)
        by_cases ht : t ∈ N
        · cases hins : g.inputs with
          | nil =>
            -- `not []` evaluates to `true`, identical to `and []`!
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
        · -- `g` is dead (`t ∉ N`): replace `g` by `⟨GateOp.or, []⟩`!
          left
          refine ⟨⟨GateOp.or, []⟩ :: gs', ?_, by simp; omega, fun x => ?_⟩
          · intro d hd; rcases List.mem_cons.1 hd with rfl | hd
            · exact ⟨by simp, by simp⟩
            · exact hgm' d hd
          · simp only [run, ← heq']
            refine hdN _ _ fun i hi => ?_
            have hit : i ≠ t := fun e => ht (e ▸ hi)
            simp [Function.update_of_ne hit]
    · -- Tail `gs` already has `N.card ≤ gs.length`
      right
      by_cases ht : t ∈ N
      · have hop := hg0.1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        rcases hop with hop | hop | hop
        · -- `and`
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
        · -- `or`
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
        · -- Second `not` gate: `|N'| ≤ |N| ≤ gs.length < (g :: gs).length`, strictly smaller!
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

/-! ### Part 3: Splitting a 1-NOT read-once formula `f = K[z := ¬H]` & Normal Form of `H` -/

/-- Normal form of a read-once monotone formula `H` on `oneEach u v`:
    either identically `false` (on ≥ 2 vars), or `S0 × univ ∪ univ × T0 ∪ ⋃ (Si × Ti)` with
    pairwise-disjoint `S0, S1..St ⊆ X_H` and `T0, T1..Tt ⊆ Y_H`! -/
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
    -- Under `AND` of disjoint variable sets, ONLY `(S0_1 × T0_2)` and `(S0_2 × T0_1)` survive!
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

/-! ### Part 4: Monotone circuit building blocks (`OR` list, `Th_2`, `compileForm`) -/

/-- Append gates computing `OR` of a non-empty list of wires `ws`, costing `ws.length - 1` gates. -/
def buildOr (base : ℕ) : List ℕ → List Gate × ℕ
  | []      => ([], base)
  | [w]     => ([], w)
  | w :: ws =>
    let (gs, acc) := buildOr base ws
    (gs ++ [⟨GateOp.or, [w, acc]⟩], base + gs.length)

theorem buildOr_props (base : ℕ) : ∀ (ws : List ℕ), ws ≠ [] → (∀ i ∈ ws, i < base) →
    let res := buildOr base ws
    (∀ g ∈ res.1, GateMono g) ∧
    res.1.length = ws.length - 1 ∧
    res.2 < base + res.1.length ∧
    ∀ w : List Bool, w.length = base →
      (wiresFrom res.1 w).getD res.2 false = ws.any (fun i => w.getD i false) := by
  intro ws
  induction ws with
  | nil => intro h; exact (h rfl).elim
  | cons a ws ih =>
    intro _ hlt
    cases ws with
    | nil =>
      refine ⟨by simp [buildOr], by simp [buildOr], by simpa [buildOr] using hlt a (by simp),
        fun w _ => by simp [buildOr, wiresFrom]⟩
    | cons b bs =>
      have hws : b :: bs ≠ [] := List.cons_ne_nil _ _
      obtain ⟨hm, hl, ho, hev⟩ := ih hws (fun i hi => hlt i (List.mem_cons_of_mem _ hi))
      set p := buildOr base (b :: bs)
      refine ⟨?_, ?_, ?_, fun w hw => ?_⟩
      · intro g hg
        rcases List.mem_append.1 hg with hg | hg
        · exact hm g hg
        · simp only [List.mem_singleton] at hg; subst hg; exact ⟨by simp, by simp⟩
      · simp [buildOr, p, hl]
      · simp [buildOr, p]
      · simp only [buildOr, wiresFrom_snoc, getD_snoc, length_wiresFrom, hw, ↓reduceIte,
          GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, id]
        rw [getD_wiresFrom _ _ a (by have := hlt a (by simp); omega), hev w hw]
        simp [List.any_cons]

/-- Pairwise `(OR, Th_2)` builder on a list of ≥ 1 wires:
    for `k ≥ 1` wires, builds `(gs, w_or, w_th2)` where `gs.length = 3 * k - 4` for `k ≥ 2`,
    and for `k ≥ 2` the root `Th_2` skips the final `w_or` gate, costing `3 * k - 5`! -/
def buildOrTh2 (base : ℕ) : List ℕ → List Gate × ℕ × ℕ
  | []      => ([], base, base)
  | [a]     => ([], a, base) -- unused for k ≥ 2
  | [a, b]  => ([⟨GateOp.or, [a, b]⟩, ⟨GateOp.and, [a, b]⟩], base, base + 1)
  | a :: b :: c :: rest =>
    let (gs, wOr, wTh) := buildOrTh2 base (b :: c :: rest)
    let m := base + gs.length
    -- m: a | wOr, m+1: a & wOr, m+2: wTh | (a & wOr)
    (gs ++ [⟨GateOp.or, [a, wOr]⟩, ⟨GateOp.and, [a, wOr]⟩, ⟨GateOp.or, [wTh, m + 1]⟩],
     m, m + 2)

/-- `Th_2` ONLY (skips the unnecessary top `a | wOr` gate!), costing `3 * ws.length - 5` for `ws.length ≥ 2`! -/
def buildTh2 (base : ℕ) : List ℕ → List Gate × ℕ
  | [a, b] => ([⟨GateOp.and, [a, b]⟩], base)
  | a :: b :: c :: rest =>
    let (gs, wOr, wTh) := buildOrTh2 base (b :: c :: rest)
    let m := base + gs.length
    -- m: a & wOr, m+1: wTh | (a & wOr)
    (gs ++ [⟨GateOp.and, [a, wOr]⟩, ⟨GateOp.or, [wTh, m]⟩], m + 1)
  | _ => ([], base)

def atLeastTwo (f : ℕ → Bool) (ws : List ℕ) : Bool :=
  decide (2 ≤ (ws.map f).count true)

theorem atLeastTwo_cons (f : ℕ → Bool) (a : ℕ) (ws : List ℕ) :
    atLeastTwo f (a :: ws) = (atLeastTwo f ws || (f a && ws.any f)) := by
  unfold atLeastTwo
  cases ha : f a <;> simp only [List.map_cons, ha, List.count_cons, Bool.false_and, Bool.true_and,
    Bool.or_false, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte, Bool.decide_or]
  · simp
  · have h : ws.any f = true ↔ 1 ≤ (ws.map f).count true := by
      rw [List.any_eq_true]
      constructor
      · rintro ⟨x, hx, hfx⟩
        have : true ∈ ws.map f := List.mem_map.2 ⟨x, hx, hfx⟩
        exact List.count_pos_iff.2 this
      · intro hc
        obtain ⟨x, hx, hfx⟩ := List.mem_map.1 (List.count_pos_iff.1 hc)
        exact ⟨x, hx, hfx⟩
    by_cases h2 : 2 ≤ (ws.map f).count true
    · have h1 : 1 ≤ (ws.map f).count true := by omega
      have h2' : 2 ≤ (ws.map f).count true + 1 := by omega
      simp only [h2, h2', h.2 h1, decide_true, Bool.or_true]
    · by_cases h1 : 1 ≤ (ws.map f).count true
      · simp [show ¬(2 ≤ (ws.map f).count true) from h2, h.2 h1, show 2 ≤ (ws.map f).count true + 1 by omega]
      · have h0 : (ws.map f).count true = 0 := by omega
        have hfalse : ws.any f = false := by
          cases hwf : ws.any f
          · rfl
          · exfalso; have := h.1 hwf; omega
        simp [h0, hfalse]

theorem buildOrTh2_props (base : ℕ) : ∀ (ws : List ℕ), 2 ≤ ws.length → (∀ i ∈ ws, i < base) →
    let res := buildOrTh2 base ws
    (∀ g ∈ res.1, GateMono g) ∧
    res.1.length = 3 * ws.length - 4 ∧
    res.2.1 < base + res.1.length ∧
    res.2.2 < base + res.1.length ∧
    ∀ w : List Bool, w.length = base →
      (wiresFrom res.1 w).getD res.2.1 false = ws.any (fun i => w.getD i false) ∧
      (wiresFrom res.1 w).getD res.2.2 false = atLeastTwo (fun i => w.getD i false) ws := by
  intro ws
  induction ws with
  | nil => intro h; simp at h
  | cons a tl ih =>
    intro hlen hlt
    cases tl with
    | nil => simp at hlen
    | cons b bs =>
      cases bs with
      | nil =>
        have ha := hlt a (by simp)
        have hb := hlt b (by simp)
        refine ⟨?_, by simp [buildOrTh2], by simp [buildOrTh2], by simp [buildOrTh2], fun w hw => ?_⟩
        · intro g hg
          simp only [buildOrTh2, List.mem_cons, List.not_mem_nil, or_false] at hg
          rcases hg with rfl | rfl <;> exact ⟨by simp, by simp⟩
        · simp only [buildOrTh2]
          set e1 := w.getD a false || w.getD b false
          set e2 := w.getD a false && w.getD b false
          have hwf : wiresFrom [⟨GateOp.or, [a, b]⟩, ⟨GateOp.and, [a, b]⟩] w = w ++ [e1, e2] := by
            rw [wiresFrom, List.foldl_cons, List.foldl_cons, List.foldl_nil]
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
              List.all_cons, List.all_nil, Bool.or_false, Bool.and_true, id]
            rw [getD_snoc, getD_snoc, if_neg (by omega), if_neg (by omega)]
            simp [e1, e2]
          rw [hwf, ← hw]
          constructor
          · rw [List.getD_append_right _ _ _ _ (le_refl _)]
            simp [e1]
          · rw [List.getD_append_right _ _ _ _ (by omega)]
            simp only [Nat.add_sub_cancel_left, List.getD_cons_succ, List.getD_cons_zero, e2, atLeastTwo,
              List.map_cons, List.map_nil]
            cases w.getD a false <;> cases w.getD b false <;> rfl
      | cons c cs =>
        set p := buildOrTh2 base (b :: c :: cs)
        obtain ⟨hm, hl, ho1, ho2, hev⟩ :
            (∀ g ∈ p.1, GateMono g) ∧
            p.1.length = 3 * (b :: c :: cs).length - 4 ∧
            p.2.1 < base + p.1.length ∧
            p.2.2 < base + p.1.length ∧
            ∀ w : List Bool, w.length = base →
              (wiresFrom p.1 w).getD p.2.1 false = (b :: c :: cs).any (fun i => w.getD i false) ∧
              (wiresFrom p.1 w).getD p.2.2 false = atLeastTwo (fun i => w.getD i false) (b :: c :: cs) :=
          ih (by simp) (fun i hi => hlt i (List.mem_cons_of_mem _ hi))
        have ha : a < base := hlt a (by simp)
        refine ⟨?_, ?_, ?_, ?_, fun w hw => ?_⟩
        · intro g hg
          change g ∈ p.1 ++ [Gate.mk GateOp.or [a, p.2.1], Gate.mk GateOp.and [a, p.2.1],
            Gate.mk GateOp.or [p.2.2, base + p.1.length + 1]] at hg
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
          rcases hg with hg | rfl | rfl | rfl
          · exact hm g hg
          all_goals exact ⟨by simp, by simp⟩
        · change (p.1 ++ [Gate.mk GateOp.or [a, p.2.1], Gate.mk GateOp.and [a, p.2.1],
            Gate.mk GateOp.or [p.2.2, base + p.1.length + 1]]).length = _
          rw [List.length_append, hl]
          simp only [List.length_cons, List.length_nil]; omega
        · change base + p.1.length < base + (p.1 ++ [Gate.mk GateOp.or [a, p.2.1],
            Gate.mk GateOp.and [a, p.2.1], Gate.mk GateOp.or [p.2.2, base + p.1.length + 1]]).length
          rw [List.length_append]; simp
        · change base + p.1.length + 2 < base + (p.1 ++ [Gate.mk GateOp.or [a, p.2.1],
            Gate.mk GateOp.and [a, p.2.1], Gate.mk GateOp.or [p.2.2, base + p.1.length + 1]]).length
          rw [List.length_append]; simp; omega
        · change (wiresFrom (p.1 ++ [Gate.mk GateOp.or [a, p.2.1], Gate.mk GateOp.and [a, p.2.1],
            Gate.mk GateOp.or [p.2.2, base + p.1.length + 1]]) w).getD (base + p.1.length) false = _ ∧
            (wiresFrom (p.1 ++ [Gate.mk GateOp.or [a, p.2.1], Gate.mk GateOp.and [a, p.2.1],
            Gate.mk GateOp.or [p.2.2, base + p.1.length + 1]]) w).getD (base + p.1.length + 2) false = _
          rw [wiresFrom_append]
          set w1 := wiresFrom p.1 w
          have lw1 : w1.length = base + p.1.length := by rw [length_wiresFrom, hw]
          have hwa : w1.getD a false = w.getD a false := getD_wiresFrom p.1 w a (by omega)
          have ⟨hOr, hTh⟩ := hev w hw
          change w1.getD p.2.1 false = _ at hOr
          change w1.getD p.2.2 false = _ at hTh
          set x1 := w.getD a false || (b :: c :: cs).any (fun i => w.getD i false)
          set x2 := w.getD a false && (b :: c :: cs).any (fun i => w.getD i false)
          set x3 := atLeastTwo (fun i => w.getD i false) (b :: c :: cs) || x2
          have hstep : wiresFrom [Gate.mk GateOp.or [a, p.2.1], Gate.mk GateOp.and [a, p.2.1],
              Gate.mk GateOp.or [p.2.2, base + p.1.length + 1]] w1 = w1 ++ [x1, x2, x3] := by
            rw [wiresFrom, List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_nil]
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
              List.all_cons, List.all_nil, Bool.or_false, Bool.and_true, id]
            have hg1 : (w1.getD a false || w1.getD p.2.1 false) = x1 := by rw [hwa, hOr]
            rw [hg1]
            have hg2 : ((w1 ++ [x1]).getD a false && (w1 ++ [x1]).getD p.2.1 false) = x2 := by
              rw [getD_snoc, getD_snoc, if_neg (by omega), if_neg (by omega), hwa, hOr]
            rw [hg2]
            have hg3 : ((w1 ++ [x1] ++ [x2]).getD p.2.2 false || (w1 ++ [x1] ++ [x2]).getD (base + p.1.length + 1) false) = x3 := by
              rw [getD_snoc, getD_snoc, getD_snoc,
                if_neg (by simp [lw1]; omega), if_neg (by omega),
                if_pos (by simp [lw1]), hTh]
            rw [hg3]
            simp
          rw [hstep]
          constructor
          · rw [← lw1, List.getD_append_right _ _ _ _ (le_refl _)]
            simp [x1]
          · rw [show base + p.1.length + 2 = w1.length + 2 by omega,
              List.getD_append_right _ _ _ _ (by omega)]
            simp only [Nat.add_sub_cancel_left, List.getD_cons_succ, List.getD_cons_zero, x3, x2]
            exact (atLeastTwo_cons (fun i => w.getD i false) a (b :: c :: cs)).symm

theorem buildTh2_props (base : ℕ) (ws : List ℕ) (hlen : 2 ≤ ws.length) (hlt : ∀ i ∈ ws, i < base) :
    let res := buildTh2 base ws
    (∀ g ∈ res.1, GateMono g) ∧
    res.1.length = 3 * ws.length - 5 ∧
    res.2 < base + res.1.length ∧
    ∀ w : List Bool, w.length = base →
      (wiresFrom res.1 w).getD res.2 false = atLeastTwo (fun i => w.getD i false) ws := by
  rcases ws with _ | ⟨a, _ | ⟨b, bs⟩⟩
  · simp at hlen
  · simp at hlen
  · cases bs with
    | nil =>
      have ha := hlt a (by simp); have hb := hlt b (by simp)
      refine ⟨fun g hg => by simp [buildTh2] at hg; subst hg; exact ⟨by simp, by simp⟩,
        by simp [buildTh2], by simp [buildTh2], fun w hw => ?_⟩
      simp only [buildTh2, wiresFrom, List.foldl_cons, List.foldl_nil, getD_snoc, hw, ↓reduceIte,
        GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id, atLeastTwo]
      cases w.getD a false <;> cases w.getD b false <;> rfl
    | cons c cs =>
      set p := buildOrTh2 base (b :: c :: cs)
      obtain ⟨hm, hl, ho1, ho2, hev⟩ :
          (∀ g ∈ p.1, GateMono g) ∧
          p.1.length = 3 * (b :: c :: cs).length - 4 ∧
          p.2.1 < base + p.1.length ∧
          p.2.2 < base + p.1.length ∧
          ∀ w : List Bool, w.length = base →
            (wiresFrom p.1 w).getD p.2.1 false = (b :: c :: cs).any (fun i => w.getD i false) ∧
            (wiresFrom p.1 w).getD p.2.2 false = atLeastTwo (fun i => w.getD i false) (b :: c :: cs) :=
        buildOrTh2_props base (b :: c :: cs) (by simp)
          (fun i hi => hlt i (List.mem_cons_of_mem _ hi))
      have ha : a < base := hlt a (by simp)
      refine ⟨?_, ?_, ?_, fun w hw => ?_⟩
      · intro g hg
        change g ∈ p.1 ++ [Gate.mk GateOp.and [a, p.2.1], Gate.mk GateOp.or [p.2.2, base + p.1.length]] at hg
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with hg | rfl | rfl
        · exact hm g hg
        all_goals exact ⟨by simp, by simp⟩
      · change (p.1 ++ [Gate.mk GateOp.and [a, p.2.1], Gate.mk GateOp.or [p.2.2, base + p.1.length]]).length = _
        rw [List.length_append, hl]
        simp only [List.length_cons, List.length_nil]; omega
      · change base + p.1.length + 1 < base + (p.1 ++ [Gate.mk GateOp.and [a, p.2.1],
          Gate.mk GateOp.or [p.2.2, base + p.1.length]]).length
        rw [List.length_append]; simp; omega
      · change (wiresFrom (p.1 ++ [Gate.mk GateOp.and [a, p.2.1], Gate.mk GateOp.or [p.2.2, base + p.1.length]]) w).getD
          (base + p.1.length + 1) false = _
        rw [wiresFrom_append]
        set w1 := wiresFrom p.1 w
        have lw1 : w1.length = base + p.1.length := by rw [length_wiresFrom, hw]
        have hwa : w1.getD a false = w.getD a false := getD_wiresFrom p.1 w a (by omega)
        have ⟨hOr, hTh⟩ := hev w hw
        change w1.getD p.2.1 false = _ at hOr
        change w1.getD p.2.2 false = _ at hTh
        set x1 := w.getD a false && (b :: c :: cs).any (fun i => w.getD i false)
        set x2 := atLeastTwo (fun i => w.getD i false) (b :: c :: cs) || x1
        have hstep : wiresFrom [Gate.mk GateOp.and [a, p.2.1], Gate.mk GateOp.or [p.2.2, base + p.1.length]] w1
            = w1 ++ [x1, x2] := by
          rw [wiresFrom, List.foldl_cons, List.foldl_cons, List.foldl_nil]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
            List.all_cons, List.all_nil, Bool.or_false, Bool.and_true, id]
          have hg1 : (w1.getD a false && w1.getD p.2.1 false) = x1 := by rw [hwa, hOr]
          rw [hg1]
          have hg2 : ((w1 ++ [x1]).getD p.2.2 false || (w1 ++ [x1]).getD (base + p.1.length) false) = x2 := by
            rw [getD_snoc, getD_snoc, if_neg (by omega), if_pos lw1.symm, hTh]
          rw [hg2]
          simp
        rw [hstep, show base + p.1.length + 1 = w1.length + 1 by omega,
            List.getD_append_right _ _ _ _ (by omega)]
        simp only [Nat.add_sub_cancel_left, List.getD_cons_succ, List.getD_cons_zero, x2, x1]
        exact (atLeastTwo_cons (fun i => w.getD i false) a (b :: c :: cs)).symm

/-- Compile a `Form` with `nots = 0` directly into monotone gates of length `f.bins`! -/
def compileMono (base : ℕ) : Form → List Gate × ℕ
  | .var w   => ([], w)
  | .not _   => ([], base)
  | .and l r =>
    let (gl, wl) := compileMono base l
    let (gr, wr) := compileMono (base + gl.length) r
    (gl ++ gr ++ [⟨GateOp.and, [wl, wr]⟩], base + gl.length + gr.length)
  | .or l r =>
    let (gl, wl) := compileMono base l
    let (gr, wr) := compileMono (base + gl.length) r
    (gl ++ gr ++ [⟨GateOp.or, [wl, wr]⟩], base + gl.length + gr.length)

theorem compileMono_props : ∀ (f : Form) (base : ℕ), f.nots = 0 → (∀ i ∈ f.vars, i < base) →
    let res := compileMono base f
    (∀ g ∈ res.1, GateMono g) ∧
    res.1.length = f.bins ∧
    res.2 < base + res.1.length ∧
    ∀ w : List Bool, w.length = base →
      (wiresFrom res.1 w).getD res.2 false = f.eval (fun i => w.getD i false) := by
  intro f
  induction f with
  | var v =>
    intro base _ hv
    exact ⟨by simp [compileMono], rfl, by simpa [compileMono] using hv v (by simp [Form.vars]),
      fun w _ => by simp [compileMono, wiresFrom, Form.eval]⟩
  | not _ _ => intro _ hn; simp [Form.nots] at hn
  | and l r ihl ihr =>
    intro base hn hv
    have hnl : l.nots = 0 := by simp [Form.nots] at hn; omega
    have hnr : r.nots = 0 := by simp [Form.nots] at hn; omega
    set p1 := compileMono base l
    obtain ⟨hm1, hl1, ho1, he1⟩ :
        (∀ g ∈ p1.1, GateMono g) ∧ p1.1.length = l.bins ∧ p1.2 < base + p1.1.length ∧
        ∀ w : List Bool, w.length = base → (wiresFrom p1.1 w).getD p1.2 false = l.eval (fun i => w.getD i false) :=
      ihl base hnl (fun i hi => hv i (Finset.mem_union_left _ hi))
    set p2 := compileMono (base + p1.1.length) r
    obtain ⟨hm2, hl2, ho2, he2⟩ :
        (∀ g ∈ p2.1, GateMono g) ∧ p2.1.length = r.bins ∧ p2.2 < base + p1.1.length + p2.1.length ∧
        ∀ w : List Bool, w.length = base + p1.1.length → (wiresFrom p2.1 w).getD p2.2 false = r.eval (fun i => w.getD i false) :=
      ihr (base + p1.1.length) hnr (fun i hi => by have := hv i (Finset.mem_union_right _ hi); omega)
    refine ⟨?_, ?_, ?_, fun w hw => ?_⟩
    · intro g hg
      change g ∈ p1.1 ++ p2.1 ++ [⟨GateOp.and, [p1.2, p2.2]⟩] at hg
      simp only [List.mem_append, List.mem_singleton] at hg
      rcases hg with (hg | hg) | rfl
      · exact hm1 g hg
      · exact hm2 g hg
      · exact ⟨by simp, by simp⟩
    · change (p1.1 ++ p2.1 ++ [Gate.mk GateOp.and [p1.2, p2.2]]).length = (Form.and l r).bins
      rw [List.length_append, List.length_append, List.length_singleton, hl1, hl2]; rfl
    · change base + p1.1.length + p2.1.length < base + (p1.1 ++ p2.1 ++ [Gate.mk GateOp.and [p1.2, p2.2]]).length
      rw [List.length_append, List.length_append, List.length_singleton]; omega
    · change (wiresFrom (p1.1 ++ p2.1 ++ [Gate.mk GateOp.and [p1.2, p2.2]]) w).getD
        (base + p1.1.length + p2.1.length) false = (l.eval (fun i => w.getD i false) && r.eval (fun i => w.getD i false))
      rw [wiresFrom_snoc, wiresFrom_append, getD_snoc, length_wiresFrom, length_wiresFrom, hw]
      simp only [↓reduceIte, GateOp.eval, List.map_cons, List.map_nil,
        List.all_cons, List.all_nil, Bool.and_true, id]
      have h1 : (wiresFrom p2.1 (wiresFrom p1.1 w)).getD p1.2 false = l.eval (fun i => w.getD i false) := by
        rw [getD_wiresFrom _ _ _ (by rw [length_wiresFrom, hw]; exact ho1), he1 w hw]
      have h2 : (wiresFrom p2.1 (wiresFrom p1.1 w)).getD p2.2 false = r.eval (fun i => w.getD i false) := by
        rw [he2 (wiresFrom p1.1 w) (by rw [length_wiresFrom, hw])]
        exact Form.eval_congr r _ _ (fun i hi => getD_wiresFrom _ _ _ (by have := hv i (Finset.mem_union_right _ hi); omega))
      rw [h1, h2]
  | or l r ihl ihr =>
    intro base hn hv
    have hnl : l.nots = 0 := by simp [Form.nots] at hn; omega
    have hnr : r.nots = 0 := by simp [Form.nots] at hn; omega
    set p1 := compileMono base l
    obtain ⟨hm1, hl1, ho1, he1⟩ :
        (∀ g ∈ p1.1, GateMono g) ∧ p1.1.length = l.bins ∧ p1.2 < base + p1.1.length ∧
        ∀ w : List Bool, w.length = base → (wiresFrom p1.1 w).getD p1.2 false = l.eval (fun i => w.getD i false) :=
      ihl base hnl (fun i hi => hv i (Finset.mem_union_left _ hi))
    set p2 := compileMono (base + p1.1.length) r
    obtain ⟨hm2, hl2, ho2, he2⟩ :
        (∀ g ∈ p2.1, GateMono g) ∧ p2.1.length = r.bins ∧ p2.2 < base + p1.1.length + p2.1.length ∧
        ∀ w : List Bool, w.length = base + p1.1.length → (wiresFrom p2.1 w).getD p2.2 false = r.eval (fun i => w.getD i false) :=
      ihr (base + p1.1.length) hnr (fun i hi => by have := hv i (Finset.mem_union_right _ hi); omega)
    refine ⟨?_, ?_, ?_, fun w hw => ?_⟩
    · intro g hg
      change g ∈ p1.1 ++ p2.1 ++ [Gate.mk GateOp.or [p1.2, p2.2]] at hg
      simp only [List.mem_append, List.mem_singleton] at hg
      rcases hg with (hg | hg) | rfl
      · exact hm1 g hg
      · exact hm2 g hg
      · exact ⟨by simp, by simp⟩
    · change (p1.1 ++ p2.1 ++ [Gate.mk GateOp.or [p1.2, p2.2]]).length = (Form.or l r).bins
      rw [List.length_append, List.length_append, List.length_singleton, hl1, hl2]; rfl
    · change base + p1.1.length + p2.1.length < base + (p1.1 ++ p2.1 ++ [Gate.mk GateOp.or [p1.2, p2.2]]).length
      rw [List.length_append, List.length_append, List.length_singleton]; omega
    · change (wiresFrom (p1.1 ++ p2.1 ++ [Gate.mk GateOp.or [p1.2, p2.2]]) w).getD
        (base + p1.1.length + p2.1.length) false = (l.eval (fun i => w.getD i false) || r.eval (fun i => w.getD i false))
      rw [wiresFrom_snoc, wiresFrom_append, getD_snoc, length_wiresFrom, length_wiresFrom, hw]
      simp only [↓reduceIte, GateOp.eval, List.map_cons, List.map_nil,
        List.any_cons, List.any_nil, Bool.or_false, id]
      have h1 : (wiresFrom p2.1 (wiresFrom p1.1 w)).getD p1.2 false = l.eval (fun i => w.getD i false) := by
        rw [getD_wiresFrom _ _ _ (by rw [length_wiresFrom, hw]; exact ho1), he1 w hw]
      have h2 : (wiresFrom p2.1 (wiresFrom p1.1 w)).getD p2.2 false = r.eval (fun i => w.getD i false) := by
        rw [he2 (wiresFrom p1.1 w) (by rw [length_wiresFrom, hw])]
        exact Form.eval_congr r _ _ (fun i hi => getD_wiresFrom _ _ _ (by have := hv i (Finset.mem_union_right _ hi); omega))
      rw [h1, h2]

/-- Extract the unique `.not h` subformula from a read-once 1-NOT formula `f`, replacing it by
    wire `z` (`z ∉ f.vars`) to get a plain context `K` with `K.bins + h.bins = f.bins`! -/
theorem split_unique_not (z : ℕ) : ∀ (f : Form), f.ReadOnce → f.nots = 1 → z ∉ f.vars →
    ∃ (K h : Form), K.ReadOnce ∧ h.ReadOnce ∧ K.nots = 0 ∧ h.nots = 0 ∧
      h.vars ⊆ f.vars ∧ K.vars ⊆ insert z f.vars ∧
      K.bins + h.bins = f.bins ∧
      ∀ x : ℕ → Bool, f.eval x = K.eval (Function.update x z (!(h.eval x))) := by
  intro f
  induction f with
  | var _ => intro _ hn; simp [Form.nots] at hn
  | not h _ =>
    intro hro hn _
    have hn0 : h.nots = 0 := by simp [Form.nots] at hn; omega
    refine ⟨.var z, h, trivial, hro, rfl, hn0, subset_rfl, by simp [Form.vars], by simp [Form.bins],
      fun x => by simp [Form.eval]⟩
  | and l r ihl ihr =>
    intro ⟨hl, hr, hdis⟩ hn hz
    simp only [Form.vars, Finset.mem_union, not_or] at hz
    simp only [Form.nots] at hn
    by_cases hnl : l.nots = 1
    · have hnr : r.nots = 0 := by omega
      obtain ⟨Kl, h, Klr, hr', Kln, hn0, hv, Kvs, hbin, hev⟩ := ihl hl hnl hz.1
      have hdisK : Disjoint Kl.vars r.vars := by
        rw [Finset.disjoint_left]
        intro a ha1 ha2
        have := Kvs ha1
        simp only [Finset.mem_insert] at this
        rcases this with rfl | ha1'
        · exact hz.2 ha2
        · exact Finset.disjoint_left.1 hdis ha1' ha2
      refine ⟨.and Kl r, h, ⟨Klr, hr, hdisK⟩, hr', by simp [Form.nots, Kln, hnr], hn0,
        hv.trans Finset.subset_union_left,
        Finset.union_subset (Kvs.trans (Finset.insert_subset_insert z Finset.subset_union_left))
          (Finset.subset_union_right.trans (Finset.subset_insert z _)),
        by simp [Form.bins]; omega, fun x => ?_⟩
      simp only [Form.eval, hev x]
      congr 1
      exact (Form.eval_congr r _ _ fun i hi => Function.update_of_ne (fun (e : i = z) => hz.2 (e ▸ hi)) _ _).symm
    · have hnl0 : l.nots = 0 := by omega
      have hnr1 : r.nots = 1 := by omega
      obtain ⟨Kr, h, Krr, hr', Krn, hn0, hv, Kvs, hbin, hev⟩ := ihr hr hnr1 hz.2
      have hdisK : Disjoint l.vars Kr.vars := by
        rw [Finset.disjoint_left]
        intro a ha1 ha2
        have := Kvs ha2
        simp only [Finset.mem_insert] at this
        rcases this with rfl | ha2'
        · exact hz.1 ha1
        · exact Finset.disjoint_left.1 hdis ha1 ha2'
      refine ⟨.and l Kr, h, ⟨hl, Krr, hdisK⟩, hr', by simp [Form.nots, hnl0, Krn], hn0,
        hv.trans Finset.subset_union_right,
        Finset.union_subset (Finset.subset_union_left.trans (Finset.subset_insert z _))
          (Kvs.trans (Finset.insert_subset_insert z Finset.subset_union_right)),
        by simp [Form.bins]; omega, fun x => ?_⟩
      simp only [Form.eval, hev x]
      congr 1
      exact (Form.eval_congr l _ _ fun i hi => Function.update_of_ne (fun (e : i = z) => hz.1 (e ▸ hi)) _ _).symm
  | or l r ihl ihr =>
    intro ⟨hl, hr, hdis⟩ hn hz
    simp only [Form.vars, Finset.mem_union, not_or] at hz
    simp only [Form.nots] at hn
    by_cases hnl : l.nots = 1
    · have hnr : r.nots = 0 := by omega
      obtain ⟨Kl, h, Klr, hr', Kln, hn0, hv, Kvs, hbin, hev⟩ := ihl hl hnl hz.1
      have hdisK : Disjoint Kl.vars r.vars := by
        rw [Finset.disjoint_left]
        intro a ha1 ha2
        have := Kvs ha1
        simp only [Finset.mem_insert] at this
        rcases this with rfl | ha1'
        · exact hz.2 ha2
        · exact Finset.disjoint_left.1 hdis ha1' ha2
      refine ⟨.or Kl r, h, ⟨Klr, hr, hdisK⟩, hr', by simp [Form.nots, Kln, hnr], hn0,
        hv.trans Finset.subset_union_left,
        Finset.union_subset (Kvs.trans (Finset.insert_subset_insert z Finset.subset_union_left))
          (Finset.subset_union_right.trans (Finset.subset_insert z _)),
        by simp [Form.bins]; omega, fun x => ?_⟩
      simp only [Form.eval, hev x]
      congr 1
      exact (Form.eval_congr r _ _ fun i hi => Function.update_of_ne (fun (e : i = z) => hz.2 (e ▸ hi)) _ _).symm
    · have hnl0 : l.nots = 0 := by omega
      have hnr1 : r.nots = 1 := by omega
      obtain ⟨Kr, h, Krr, hr', Krn, hn0, hv, Kvs, hbin, hev⟩ := ihr hr hnr1 hz.2
      have hdisK : Disjoint l.vars Kr.vars := by
        rw [Finset.disjoint_left]
        intro a ha1 ha2
        have := Kvs ha2
        simp only [Finset.mem_insert] at this
        rcases this with rfl | ha2'
        · exact hz.1 ha1
        · exact Finset.disjoint_left.1 hdis ha1 ha2'
      refine ⟨.or l Kr, h, ⟨hl, Krr, hdisK⟩, hr', by simp [Form.nots, hnl0, Krn], hn0,
        hv.trans Finset.subset_union_right,
        Finset.union_subset (Finset.subset_union_left.trans (Finset.subset_insert z _))
          (Kvs.trans (Finset.insert_subset_insert z Finset.subset_union_right)),
        by simp [Form.bins]; omega, fun x => ?_⟩
      simp only [Form.eval, hev x]
      congr 1
      exact (Form.eval_congr l _ _ fun i hi => Function.update_of_ne (fun (e : i = z) => hz.1 (e ▸ hi)) _ _).symm

/-! ### Part 5: Building the monotone circuit for `¬(nf.eval)` of size `≤ n + m - 5 + X.card + Y.card` -/

/-- Build ORs of a list of non-empty Finsets of wires, appending to `base`. -/
noncomputable def buildOrFinsets (base : ℕ) (f : α → ℕ) : List (Finset α) → List Gate × List ℕ
  | [] => ([], [])
  | S :: Ss =>
    let ws := S.toList.map f
    let (g1, w1) := buildOr base ws
    let (g2, ws2) := buildOrFinsets (base + g1.length) f Ss
    (g1 ++ g2, w1 :: ws2)

theorem buildOrFinsets_props {α : Type*} [DecidableEq α] (f : α → ℕ) (base : ℕ) :
    ∀ (Ss : List (Finset α)), (∀ S ∈ Ss, S.Nonempty) → (∀ S ∈ Ss, ∀ a ∈ S, f a < base) →
    let res := buildOrFinsets base f Ss
    (∀ g ∈ res.1, GateMono g) ∧
    res.1.length = (Ss.map fun S => S.card - 1).sum ∧
    res.2.length = Ss.length ∧
    (∀ i ∈ res.2, i < base + res.1.length) ∧
    ∀ w : List Bool, w.length = base →
      res.2.map (fun i => (wiresFrom res.1 w).getD i false) =
      Ss.map (fun S => decide (∃ a ∈ S, w.getD (f a) false = true)) := by
  intro Ss
  induction Ss generalizing base with
  | nil => intro _ _; exact ⟨by simp [buildOrFinsets], rfl, rfl, by simp [buildOrFinsets], fun _ _ => rfl⟩
  | cons S Ss ih =>
    intro hne hlt
    have hS : S.Nonempty := hne S (by simp)
    have hws_ne : S.toList.map f ≠ [] := by
      intro he; have := List.map_eq_nil_iff.1 he
      obtain ⟨a, ha⟩ := hS; exact List.not_mem_nil (this ▸ Finset.mem_toList.2 ha)
    have hws_lt : ∀ i ∈ S.toList.map f, i < base := by
      intro i hi; obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hi
      exact hlt S (by simp) a (Finset.mem_toList.1 ha)
    set p1 := buildOr base (S.toList.map f)
    obtain ⟨hm1, hl1, ho1, he1⟩ :
        (∀ g ∈ p1.1, GateMono g) ∧ p1.1.length = (S.toList.map f).length - 1 ∧
        p1.2 < base + p1.1.length ∧
        ∀ w : List Bool, w.length = base →
          (wiresFrom p1.1 w).getD p1.2 false = (S.toList.map f).any (fun i => w.getD i false) :=
      buildOr_props base (S.toList.map f) hws_ne hws_lt
    set p2 := buildOrFinsets (base + p1.1.length) f Ss
    obtain ⟨hm2, hl2, hlen2, ho2, he2⟩ :
        (∀ g ∈ p2.1, GateMono g) ∧ p2.1.length = (Ss.map fun S => S.card - 1).sum ∧
        p2.2.length = Ss.length ∧ (∀ i ∈ p2.2, i < base + p1.1.length + p2.1.length) ∧
        ∀ w : List Bool, w.length = base + p1.1.length →
          p2.2.map (fun i => (wiresFrom p2.1 w).getD i false) =
          Ss.map (fun S => decide (∃ a ∈ S, w.getD (f a) false = true)) :=
      ih (base + p1.1.length)
        (fun T hT => hne T (List.mem_cons_of_mem _ hT))
        (fun T hT a ha => by have := hlt T (List.mem_cons_of_mem _ hT) a ha; omega)
    refine ⟨?_, ?_, ?_, ?_, fun w hw => ?_⟩
    · intro g hg
      change g ∈ p1.1 ++ p2.1 at hg
      rcases List.mem_append.1 hg with hg | hg
      · exact hm1 g hg
      · exact hm2 g hg
    · change (p1.1 ++ p2.1).length = ((S :: Ss).map fun S => S.card - 1).sum
      rw [List.length_append, List.map_cons, List.sum_cons, hl1, hl2, List.length_map, Finset.length_toList]
    · change (p1.2 :: p2.2).length = (S :: Ss).length
      rw [List.length_cons, List.length_cons, hlen2]
    · intro i hi
      change i ∈ p1.2 :: p2.2 at hi
      change i < base + (p1.1 ++ p2.1).length
      rw [List.length_append]
      rcases List.mem_cons.1 hi with rfl | hi
      · omega
      · have := ho2 i hi; omega
    · change (p1.2 :: p2.2).map (fun i => (wiresFrom (p1.1 ++ p2.1) w).getD i false) = _
      rw [List.map_cons, List.map_cons, wiresFrom_append]
      congr 1
      · rw [getD_wiresFrom p2.1 _ _ (by rw [length_wiresFrom, hw]; exact ho1), he1 w hw, Bool.eq_iff_iff]
        simp only [List.any_map, Function.comp_def, List.any_eq_true, decide_eq_true_eq]
        constructor
        · rintro ⟨a, ha, hfa⟩; exact ⟨a, Finset.mem_toList.1 ha, hfa⟩
        · rintro ⟨a, ha, hfa⟩; exact ⟨a, Finset.mem_toList.2 ha, hfa⟩
      · rw [he2 (wiresFrom p1.1 w) (by rw [length_wiresFrom, hw])]
        apply List.map_congr_left
        intro T hT
        rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
        constructor <;> rintro ⟨a, ha, hfa⟩
        · exact ⟨a, ha, by rwa [getD_wiresFrom p1.1 w (f a) (by have := hlt T (List.mem_cons_of_mem _ hT) a ha; omega)] at hfa⟩
        · exact ⟨a, ha, by rwa [getD_wiresFrom p1.1 w (f a) (by have := hlt T (List.mem_cons_of_mem _ hT) a ha; omega)]⟩

theorem zipWith_congr_mem {α β γ : Type*} (f g : α → β → γ) :
    ∀ (as : List α) (bs : List β),
      (∀ a ∈ as, ∀ b ∈ bs, f a b = g a b) →
      List.zipWith f as bs = List.zipWith g as bs
  | [], _, _ => rfl
  | _, [], _ => by simp
  | a :: as, b :: bs, h => by
    simp only [List.zipWith_cons_cons, h a (by simp) b (by simp)]
    congr 1
    exact zipWith_congr_mem f g as bs fun x hx y hy =>
      h x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)

theorem zipWith_map_bool (f : ℕ → Bool) :
    ∀ (us vs : List ℕ),
      List.zipWith (fun a b => f a || f b) us vs =
      List.zipWith (· || ·) (us.map f) (vs.map f)
  | [], _ => rfl
  | _, [] => by simp
  | a :: as, b :: bs => by simp only [List.map_cons, List.zipWith_cons_cons, zipWith_map_bool f as bs]

theorem zipWith_rects {α β : Type*} (f : α → Bool) (g : β → Bool) :
    ∀ (rs : List (α × β)),
      List.zipWith (· || ·) ((rs.map Prod.fst).map f) ((rs.map Prod.snd).map g) =
      rs.map (fun p => f p.1 || g p.2)
  | [] => rfl
  | p :: ps => by simp only [List.map_cons, List.zipWith_cons_cons, zipWith_rects f g ps]

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

/-- Pairwise OR of two equal-length wire lists `us, vs`, costing `us.length` gates. -/
def buildPairOrs (base : ℕ) : List ℕ → List ℕ → List Gate × List ℕ
  | a :: as, b :: bs =>
    let (gs, zs) := buildPairOrs (base + 1) as bs
    (⟨GateOp.or, [a, b]⟩ :: gs, base :: zs)
  | _, _ => ([], [])

theorem buildPairOrs_props (base : ℕ) : ∀ (us vs : List ℕ), us.length = vs.length →
    (∀ i ∈ us, i < base) → (∀ i ∈ vs, i < base) →
    let res := buildPairOrs base us vs
    (∀ g ∈ res.1, GateMono g) ∧
    res.1.length = us.length ∧
    res.2.length = us.length ∧
    (∀ i ∈ res.2, i < base + res.1.length) ∧
    ∀ w : List Bool, w.length = base →
      res.2.map (fun i => (wiresFrom res.1 w).getD i false) =
      List.zipWith (fun a b => w.getD a false || w.getD b false) us vs := by
  intro us
  induction us generalizing base with
  | nil =>
    intro vs hlen _ _
    cases vs with
    | nil => exact ⟨by simp [buildPairOrs], rfl, rfl, by simp [buildPairOrs], fun _ _ => rfl⟩
    | cons _ _ => simp at hlen
  | cons a as ih =>
    intro vs hlen hu hv
    cases vs with
    | nil => simp at hlen
    | cons b bs =>
      have hlen' : as.length = bs.length := by simpa using hlen
      set p := buildPairOrs (base + 1) as bs
      obtain ⟨hm, hl, hlr, ho, hev⟩ :
          (∀ g ∈ p.1, GateMono g) ∧ p.1.length = as.length ∧ p.2.length = as.length ∧
          (∀ i ∈ p.2, i < base + 1 + p.1.length) ∧
          ∀ w : List Bool, w.length = base + 1 →
            p.2.map (fun i => (wiresFrom p.1 w).getD i false) =
            List.zipWith (fun a b => w.getD a false || w.getD b false) as bs :=
        ih (base + 1) bs hlen'
          (fun i hi => by have := hu i (List.mem_cons_of_mem _ hi); omega)
          (fun i hi => by have := hv i (List.mem_cons_of_mem _ hi); omega)
      refine ⟨?_, ?_, ?_, ?_, fun w hw => ?_⟩
      · intro g hg
        change g ∈ ⟨GateOp.or, [a, b]⟩ :: p.1 at hg
        rcases List.mem_cons.1 hg with rfl | hg
        · exact ⟨by simp, by simp⟩
        · exact hm g hg
      · change (⟨GateOp.or, [a, b]⟩ :: p.1).length = (a :: as).length
        rw [List.length_cons, List.length_cons, hl]
      · change (base :: p.2).length = (a :: as).length
        rw [List.length_cons, List.length_cons, hlr]
      · intro i hi
        change i ∈ base :: p.2 at hi
        change i < base + (⟨GateOp.or, [a, b]⟩ :: p.1).length
        rw [List.length_cons]
        rcases List.mem_cons.1 hi with rfl | hi
        · omega
        · have := ho i hi; omega
      · change (base :: p.2).map (fun i => (wiresFrom (⟨GateOp.or, [a, b]⟩ :: p.1) w).getD i false) = _
        simp only [List.map_cons, List.zipWith_cons_cons]
        set w1 := w ++ [w.getD a false || w.getD b false]
        have hwf : wiresFrom (⟨GateOp.or, [a, b]⟩ :: p.1) w = wiresFrom p.1 w1 := by
          simp [wiresFrom, GateOp.eval, w1]
        rw [hwf]
        congr 1
        · rw [getD_wiresFrom p.1 w1 base (by simp [w1, hw])]
          simp [w1, getD_snoc, hw]
        · rw [hev w1 (by simp [w1, hw])]
          refine zipWith_congr_mem _ _ as bs fun x hx y hy => ?_
          have hx' : x < w.length := by have := hu x (List.mem_cons_of_mem _ hx); omega
          have hy' : y < w.length := by have := hv y (List.mem_cons_of_mem _ hy); omega
          rw [show w1.getD x false = w.getD x false from by rw [getD_snoc, if_neg (by omega)],
              show w1.getD y false = w.getD y false from by rw [getD_snoc, if_neg (by omega)]]

theorem pairwise_sum_card_le {α : Type*} [DecidableEq α] {X : Finset α} :
    ∀ (Ss : List (Finset α)), (∀ S ∈ Ss, S ⊆ X) → Ss.Pairwise Disjoint →
      (Ss.map Finset.card).sum ≤ X.card := by
  intro Ss
  induction Ss generalizing X with
  | nil => intro _ _; simp
  | cons S Ss ih =>
    intro hsub hpw
    rw [List.pairwise_cons] at hpw
    have hS : S ⊆ X := hsub S (by simp)
    have hrest : ∀ T ∈ Ss, T ⊆ X \ S := fun T hT => by
      intro x hx
      exact Finset.mem_sdiff.2 ⟨hsub T (List.mem_cons_of_mem _ hT) hx,
        Finset.disjoint_right.1 (hpw.1 T hT) hx⟩
    have h1 := ih hrest hpw.2
    have h2 : (X \ S).card + S.card = X.card := Finset.card_sdiff_add_card_eq_card hS
    simp only [List.map_cons, List.sum_cons]
    omega

theorem sum_sub_one_eq {α : Type*} (Ss : List (Finset α)) (hne : ∀ S ∈ Ss, S.Nonempty) :
    (Ss.map fun S => S.card - 1).sum + Ss.length = (Ss.map Finset.card).sum := by
  induction Ss with
  | nil => simp
  | cons S Ss ih =>
    have hpos : 1 ≤ S.card := Finset.card_pos.2 (hne S (by simp))
    have := ih (fun T hT => hne T (List.mem_cons_of_mem _ hT))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

/-- Key monotone replacement theorem for `¬(nf.eval)`!
    Given `nf : MonoNF n m` valid on `(X, Y)` with `X ⊂ Finset.univ` (`X.card < n`),
    `Y ⊂ Finset.univ` (`Y.card < m`), `2 ≤ n`, `2 ≤ m`, `1 ≤ X.card + Y.card`,
    and if `nf.S0 = ∅ ∧ nf.T0 = ∅ ∧ nf.rects = []` then `2 ≤ X.card + Y.card`:
    there exist monotone gates `gs` and output wire `ow` computing `!(nf.eval u v)` on `oneEach u v`
    with **`gs.length + 5 ≤ n + m + X.card + Y.card`**!! -/
theorem build_not_nf (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (X : Finset (Fin n)) (Y : Finset (Fin m)) (hXlt : X.card < n) (hYlt : Y.card < m)
    (hXY : 1 ≤ X.card + Y.card)
    (nf : MonoNF n m) (hval : nf.Valid X Y)
    (hempty : nf.S0 = ∅ → nf.T0 = ∅ → nf.rects = [] → 2 ≤ X.card + Y.card) :
    ∃ (gs : List Gate) (ow : ℕ), (∀ g ∈ gs, GateMono g) ∧
      gs.length + 5 ≤ n + m + X.card + Y.card ∧
      ow < n + m + gs.length ∧
      ∀ (u : Fin n) (v : Fin m), (wiresFrom gs (oneEach u v)).getD ow false = !(nf.eval u v) := by
  classical
  let R_L : Finset (Fin n) := Finset.univ \ (nf.S0 ∪ (nf.rects.map Prod.fst).foldr (· ∪ ·) ∅)
  let R_R : Finset (Fin m) := Finset.univ \ (nf.T0 ∪ (nf.rects.map Prod.snd).foldr (· ∪ ·) ∅)
  have hL_sub : nf.S0 ∪ (nf.rects.map Prod.fst).foldr (· ∪ ·) ∅ ⊆ X := by
    refine Finset.union_subset hval.1 ?_
    intro a ha
    obtain ⟨S, hS, haS⟩ := (mem_foldr_union_iff a _).1 ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hS
    exact (hval.2.2.1 p hp).2.2.1 haS
  have hR_sub : nf.T0 ∪ (nf.rects.map Prod.snd).foldr (· ∪ ·) ∅ ⊆ Y := by
    refine Finset.union_subset hval.2.1 ?_
    intro b hb
    obtain ⟨T, hT, hbT⟩ := (mem_foldr_union_iff b _).1 hb
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hT
    exact (hval.2.2.1 p hp).2.2.2.1 hbT
  have hRL_ne : R_L.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    have : (Finset.univ : Finset (Fin n)) ⊆ X := (Finset.sdiff_eq_empty_iff_subset.1 he).trans hL_sub
    have := Finset.card_le_card this
    simp at this; omega
  have hRR_ne : R_R.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    have : (Finset.univ : Finset (Fin m)) ⊆ Y := (Finset.sdiff_eq_empty_iff_subset.1 he).trans hR_sub
    have := Finset.card_le_card this
    simp at this; omega
  have hpwL : (nf.rects.map Prod.fst).Pairwise Disjoint :=
    List.pairwise_map.2 (hval.2.2.2.imp fun h => h.1)
  have hpwR : (nf.rects.map Prod.snd).Pairwise Disjoint :=
    List.pairwise_map.2 (hval.2.2.2.imp fun h => h.2)
  have hsumL_le_X : nf.S0.card + (nf.rects.map (fun p => p.1.card)).sum ≤ X.card := by
    have h1 := pairwise_sum_card_le (X := X \ nf.S0) (nf.rects.map Prod.fst) (fun S hS => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hS
      intro a ha; exact Finset.mem_sdiff.2 ⟨(hval.2.2.1 p hp).2.2.1 ha,
        Finset.disjoint_left.1 (hval.2.2.1 p hp).2.2.2.2.1 ha⟩) hpwL
    have h2 : (X \ nf.S0).card + nf.S0.card = X.card := Finset.card_sdiff_add_card_eq_card hval.1
    rw [List.map_map] at h1
    change nf.S0.card + (nf.rects.map (Finset.card ∘ Prod.fst)).sum ≤ X.card
    omega
  have hsumR_le_Y : nf.T0.card + (nf.rects.map (fun p => p.2.card)).sum ≤ Y.card := by
    have h1 := pairwise_sum_card_le (X := Y \ nf.T0) (nf.rects.map Prod.snd) (fun T hT => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hT
      intro b hb; exact Finset.mem_sdiff.2 ⟨(hval.2.2.1 p hp).2.2.2.1 hb,
        Finset.disjoint_left.1 (hval.2.2.1 p hp).2.2.2.2.2 hb⟩) hpwR
    have h2 : (Y \ nf.T0).card + nf.T0.card = Y.card := Finset.card_sdiff_add_card_eq_card hval.2.1
    rw [List.map_map] at h1
    change nf.T0.card + (nf.rects.map (Finset.card ∘ Prod.snd)).sum ≤ Y.card
    omega
  have ht_le_X : nf.S0.card + nf.rects.length ≤ X.card := by
    have hge := length_le_sum_card (nf.rects.map Prod.fst) fun S hS => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hS; exact (hval.2.2.1 p hp).1
    rw [List.length_map, List.map_map] at hge
    change nf.S0.card + nf.rects.length ≤ X.card
    have : (nf.rects.map (Finset.card ∘ Prod.fst)).sum = (nf.rects.map (fun p => p.1.card)).sum := rfl
    omega
  have ht_le_Y : nf.T0.card + nf.rects.length ≤ Y.card := by
    have hge := length_le_sum_card (nf.rects.map Prod.snd) fun T hT => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hT; exact (hval.2.2.1 p hp).2.1
    rw [List.length_map, List.map_map] at hge
    have : (nf.rects.map (Finset.card ∘ Prod.snd)).sum = (nf.rects.map (fun p => p.2.card)).sum := rfl
    omega
  have hRL_card : R_L.card + nf.S0.card + (nf.rects.map (fun p => p.1.card)).sum ≤ n := by
    have hpw_all : (R_L :: nf.S0 :: nf.rects.map Prod.fst).Pairwise Disjoint := by
      rw [List.pairwise_cons, List.pairwise_cons]
      refine ⟨?_, ?_, hpwL⟩
      · intro S hS
        rw [Finset.disjoint_left]
        intro a haR haS
        have hnot := (Finset.mem_sdiff.1 haR).2
        apply hnot
        rcases List.mem_cons.1 hS with rfl | hS
        · exact Finset.mem_union_left _ haS
        · exact Finset.mem_union_right _ ((mem_foldr_union_iff a _).2 ⟨S, hS, haS⟩)
      · intro S hS
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hS
        exact (hval.2.2.1 p hp).2.2.2.2.1.symm
    have h := pairwise_sum_card_le (X := (Finset.univ : Finset (Fin n)))
      (R_L :: nf.S0 :: nf.rects.map Prod.fst) (fun _ _ => Finset.subset_univ _) hpw_all
    simp only [List.map_cons, List.sum_cons, List.map_map, Finset.card_univ, Fintype.card_fin] at h
    have : (nf.rects.map (Finset.card ∘ Prod.fst)).sum = (nf.rects.map (fun p => p.1.card)).sum := rfl
    omega
  have hRR_card : R_R.card + nf.T0.card + (nf.rects.map (fun p => p.2.card)).sum ≤ m := by
    have hpw_all : (R_R :: nf.T0 :: nf.rects.map Prod.snd).Pairwise Disjoint := by
      rw [List.pairwise_cons, List.pairwise_cons]
      refine ⟨?_, ?_, hpwR⟩
      · intro T hT
        rw [Finset.disjoint_left]
        intro b hbR hbT
        have hnot := (Finset.mem_sdiff.1 hbR).2
        apply hnot
        rcases List.mem_cons.1 hT with rfl | hT
        · exact Finset.mem_union_left _ hbT
        · exact Finset.mem_union_right _ ((mem_foldr_union_iff b _).2 ⟨T, hT, hbT⟩)
      · intro T hT
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hT
        exact (hval.2.2.1 p hp).2.2.2.2.2.symm
    have h := pairwise_sum_card_le (X := (Finset.univ : Finset (Fin m)))
      (R_R :: nf.T0 :: nf.rects.map Prod.snd) (fun _ _ => Finset.subset_univ _) hpw_all
    simp only [List.map_cons, List.sum_cons, List.map_map, Finset.card_univ, Fintype.card_fin] at h
    have : (nf.rects.map (Finset.card ∘ Prod.snd)).sum = (nf.rects.map (fun p => p.2.card)).sum := rfl
    omega
  have eval_rowS : ∀ (S : Finset (Fin n)) (u : Fin n) (v : Fin m)
      {d : Decidable (∃ a ∈ S, (oneEach u v).getD a.val false = true)},
      @decide (∃ a ∈ S, (oneEach u v).getD a.val false = true) d = decide (u ∈ S) := by
    intro S u v d
    rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
    constructor
    · rintro ⟨a, ha, h⟩
      rw [oneEach_getD, decide_eq_true_eq] at h
      have ha' := a.isLt; have hv' := v.isLt
      have : a = u := Fin.ext (by omega)
      exact this ▸ ha
    · intro hu; exact ⟨u, hu, by rw [oneEach_getD]; simp⟩
  have eval_colT : ∀ (T : Finset (Fin m)) (u : Fin n) (v : Fin m)
      {d : Decidable (∃ b ∈ T, (oneEach u v).getD (n + b.val) false = true)},
      @decide (∃ b ∈ T, (oneEach u v).getD (n + b.val) false = true) d = decide (v ∈ T) := by
    intro T u v d
    rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
    constructor
    · rintro ⟨b, hb, h⟩
      rw [oneEach_getD, decide_eq_true_eq] at h
      have hu' := u.isLt
      have : b = v := Fin.ext (by omega)
      exact this ▸ hb
    · intro hv; exact ⟨v, hv, by rw [oneEach_getD]; simp⟩
  have eval_colT_after : ∀ (T : Finset (Fin m)) (u : Fin n) (v : Fin m) (gs : List Gate)
      {d : Decidable (∃ b ∈ T, (wiresFrom gs (oneEach u v)).getD (n + b.val) false = true)},
      @decide (∃ b ∈ T, (wiresFrom gs (oneEach u v)).getD (n + b.val) false = true) d = decide (v ∈ T) := by
    intro T u v gs d
    rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
    constructor
    · rintro ⟨b, hb, h⟩
      rw [getD_wiresFrom gs (oneEach u v) (n + b.val) (by rw [oneEach_len]; have := b.isLt; omega),
          oneEach_getD, decide_eq_true_eq] at h
      have hu' := u.isLt
      have : b = v := Fin.ext (by omega)
      exact this ▸ hb
    · intro hv
      refine ⟨v, hv, ?_⟩
      rw [getD_wiresFrom gs (oneEach u v) (n + v.val) (by rw [oneEach_len]; have := v.isLt; omega),
          oneEach_getD]; simp
  have count_Z : ∀ (u : Fin n) (v : Fin m),
      ((nf.rects.map fun p => decide (u ∈ p.1) || decide (v ∈ p.2)).count true) =
        (if ∃ p ∈ nf.rects, u ∈ p.1 ∧ v ∈ p.2 then 1
         else (if ∃ p ∈ nf.rects, u ∈ p.1 then 1 else 0) +
              (if ∃ p ∈ nf.rects, v ∈ p.2 then 1 else 0)) := by
    intro u v
    have gen : ∀ (rs : List (Finset (Fin n) × Finset (Fin m))),
        rs.Pairwise (fun p q => Disjoint p.1 q.1 ∧ Disjoint p.2 q.2) →
        (rs.map fun p => decide (u ∈ p.1) || decide (v ∈ p.2)).count true =
          (if ∃ p ∈ rs, u ∈ p.1 ∧ v ∈ p.2 then 1
           else (if ∃ p ∈ rs, u ∈ p.1 then 1 else 0) +
                (if ∃ p ∈ rs, v ∈ p.2 then 1 else 0)) := by
      intro rs
      induction rs with
      | nil => intro _; simp
      | cons p ps ih =>
        intro hpw
        rw [List.pairwise_cons] at hpw
        have hrec := ih hpw.2
        simp only [List.map_cons, List.count_cons, hrec]
        by_cases hu : u ∈ p.1 <;> by_cases hv : v ∈ p.2
        · have hu_ps : ¬ ∃ q ∈ ps, u ∈ q.1 := fun ⟨q, hq, huq⟩ =>
            Finset.disjoint_left.1 (hpw.1 q hq).1 hu huq
          have hv_ps : ¬ ∃ q ∈ ps, v ∈ q.2 := fun ⟨q, hq, hvq⟩ =>
            Finset.disjoint_left.1 (hpw.1 q hq).2 hv hvq
          have hboth_ps : ¬ ∃ q ∈ ps, u ∈ q.1 ∧ v ∈ q.2 := fun ⟨q, hq, huq, _⟩ => hu_ps ⟨q, hq, huq⟩
          have hboth : ∃ q ∈ p :: ps, u ∈ q.1 ∧ v ∈ q.2 := ⟨p, by simp, hu, hv⟩
          simp [hu, hv, hu_ps, hv_ps, hboth_ps, hboth]
        · have hu_ps : ¬ ∃ q ∈ ps, u ∈ q.1 := fun ⟨q, hq, huq⟩ =>
            Finset.disjoint_left.1 (hpw.1 q hq).1 hu huq
          have hboth_ps : ¬ ∃ q ∈ ps, u ∈ q.1 ∧ v ∈ q.2 := fun ⟨q, hq, huq, _⟩ => hu_ps ⟨q, hq, huq⟩
          have hboth : ¬ ∃ q ∈ p :: ps, u ∈ q.1 ∧ v ∈ q.2 := by
            rintro ⟨q, hq, huq, hvq⟩
            rcases List.mem_cons.1 hq with rfl | hq
            · exact hv hvq
            · exact hu_ps ⟨q, hq, huq⟩
          have hu_all : ∃ q ∈ p :: ps, u ∈ q.1 := ⟨p, by simp, hu⟩
          by_cases hv_ps : ∃ q ∈ ps, v ∈ q.2
          · have hv_all : ∃ q ∈ p :: ps, v ∈ q.2 := by obtain ⟨q, hq, hvq⟩ := hv_ps; exact ⟨q, List.mem_cons_of_mem _ hq, hvq⟩
            simp [hu, hv, hu_ps, hboth_ps, hboth, hu_all, hv_ps, hv_all]
          · have hv_all : ¬ ∃ q ∈ p :: ps, v ∈ q.2 := by
              rintro ⟨q, hq, hvq⟩; rcases List.mem_cons.1 hq with rfl | hq
              · exact hv hvq
              · exact hv_ps ⟨q, hq, hvq⟩
            simp [hu, hv, hu_ps, hboth_ps, hboth, hu_all, hv_ps, hv_all]
        · have hv_ps : ¬ ∃ q ∈ ps, v ∈ q.2 := fun ⟨q, hq, hvq⟩ =>
            Finset.disjoint_left.1 (hpw.1 q hq).2 hv hvq
          have hboth_ps : ¬ ∃ q ∈ ps, u ∈ q.1 ∧ v ∈ q.2 := fun ⟨q, hq, _, hvq⟩ => hv_ps ⟨q, hq, hvq⟩
          have hboth : ¬ ∃ q ∈ p :: ps, u ∈ q.1 ∧ v ∈ q.2 := by
            rintro ⟨q, hq, huq, hvq⟩
            rcases List.mem_cons.1 hq with rfl | hq
            · exact hu huq
            · exact hv_ps ⟨q, hq, hvq⟩
          have hv_all : ∃ q ∈ p :: ps, v ∈ q.2 := ⟨p, by simp, hv⟩
          by_cases hu_ps : ∃ q ∈ ps, u ∈ q.1
          · have hu_all : ∃ q ∈ p :: ps, u ∈ q.1 := by obtain ⟨q, hq, huq⟩ := hu_ps; exact ⟨q, List.mem_cons_of_mem _ hq, huq⟩
            simp [hu, hv, hv_ps, hboth_ps, hboth, hv_all, hu_ps, hu_all]
          · have hu_all : ¬ ∃ q ∈ p :: ps, u ∈ q.1 := by
              rintro ⟨q, hq, huq⟩; rcases List.mem_cons.1 hq with rfl | hq
              · exact hu huq
              · exact hu_ps ⟨q, hq, huq⟩
            simp [hu, hv, hv_ps, hboth_ps, hboth, hv_all, hu_ps, hu_all]
        · have hboth_iff : (∃ q ∈ p :: ps, u ∈ q.1 ∧ v ∈ q.2) ↔ (∃ q ∈ ps, u ∈ q.1 ∧ v ∈ q.2) := by
            simp [hu]
          have hu_iff : (∃ q ∈ p :: ps, u ∈ q.1) ↔ (∃ q ∈ ps, u ∈ q.1) := by simp [hu]
          have hv_iff : (∃ q ∈ p :: ps, v ∈ q.2) ↔ (∃ q ∈ ps, v ∈ q.2) := by simp [hv]
          simp [hu, hv, hboth_iff, hu_iff, hv_iff]
    exact gen nf.rects hval.2.2.2
  have u_part : ∀ u : Fin n,
      (u ∈ R_L ↔ u ∉ nf.S0 ∧ ¬ ∃ p ∈ nf.rects, u ∈ p.1) ∧
      (u ∈ nf.S0 → ¬ ∃ p ∈ nf.rects, u ∈ p.1) := by
    intro u
    constructor
    · simp only [R_L, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union, not_or,
        mem_foldr_union_iff, List.mem_map]
      constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩
      · rintro ⟨p, hp, hup⟩; exact h2 ⟨p.1, ⟨p, hp, rfl⟩, hup⟩
      · rintro ⟨S, ⟨p, hp, rfl⟩, hup⟩; exact h2 ⟨p, hp, hup⟩
    · intro hu ⟨p, hp, hup⟩
      exact Finset.disjoint_left.1 (hval.2.2.1 p hp).2.2.2.2.1 hup hu
  have v_part : ∀ v : Fin m,
      (v ∈ R_R ↔ v ∉ nf.T0 ∧ ¬ ∃ p ∈ nf.rects, v ∈ p.2) ∧
      (v ∈ nf.T0 → ¬ ∃ p ∈ nf.rects, v ∈ p.2) := by
    intro v
    constructor
    · simp only [R_R, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union, not_or,
        mem_foldr_union_iff, List.mem_map]
      constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩
      · rintro ⟨p, hp, hvp⟩; exact h2 ⟨p.2, ⟨p, hp, rfl⟩, hvp⟩
      · rintro ⟨T, ⟨p, hp, rfl⟩, hvp⟩; exact h2 ⟨p, hp, hvp⟩
    · intro hv ⟨p, hp, hvp⟩
      exact Finset.disjoint_left.1 (hval.2.2.1 p hp).2.2.2.2.2 hvp hv

  -- NOW CASE SPLIT ON `(nf.S0 = ∅, nf.T0 = ∅)`!
  by_cases hS0 : nf.S0 = ∅ <;> by_cases hT0 : nf.T0 = ∅
  · -- CASE A: `S0 = ∅ ∧ T0 = ∅`
    by_cases hrt : nf.rects = []
    · -- Form 1: `nf.eval ≡ false`, so `¬nf ≡ true` (`[⟨.and, []⟩]`, 1 gate!)
      have h2 := hempty hS0 hT0 hrt
      refine ⟨[⟨GateOp.and, []⟩], n + m, fun g hg => by simp at hg; subst hg; exact ⟨by simp, by simp⟩,
        by simp; omega, by simp, fun u v => ?_⟩
      simp [wiresFrom, GateOp.eval, getD_snoc, oneEach_len, MonoNF.eval, hS0, hT0, hrt]
    · by_cases ht1 : nf.rects.length = 1
      · -- `t = 1`: `¬H = U_0 | V_0`!
        have hRL_neL : R_L.toList.map (fun a : Fin n => a.val) ≠ [] := by
          intro h; obtain ⟨a, ha⟩ := hRL_ne
          exact List.not_mem_nil (List.map_eq_nil_iff.1 h ▸ Finset.mem_toList.2 ha)
        set pU := buildOr (n + m) (R_L.toList.map fun a : Fin n => a.val)
        obtain ⟨hmU, hlU, hoU, heU⟩ :
            (∀ g ∈ pU.1, GateMono g) ∧
            pU.1.length = (R_L.toList.map fun a : Fin n => a.val).length - 1 ∧
            pU.2 < n + m + pU.1.length ∧
            ∀ w : List Bool, w.length = n + m →
              (wiresFrom pU.1 w).getD pU.2 false = (R_L.toList.map fun a : Fin n => a.val).any (fun i => w.getD i false) :=
          buildOr_props (n + m) (R_L.toList.map fun a : Fin n => a.val)
            hRL_neL (fun i hi => by obtain ⟨a, _, rfl⟩ := List.mem_map.1 hi; have := a.isLt; omega)
        set base1 := n + m + pU.1.length
        have hRR_neL : R_R.toList.map (fun b : Fin m => n + b.val) ≠ [] := by
          intro h; obtain ⟨b, hb⟩ := hRR_ne
          exact List.not_mem_nil (List.map_eq_nil_iff.1 h ▸ Finset.mem_toList.2 hb)
        set pV := buildOr base1 (R_R.toList.map fun b : Fin m => n + b.val)
        obtain ⟨hmV, hlV, hoV, heV⟩ :
            (∀ g ∈ pV.1, GateMono g) ∧
            pV.1.length = (R_R.toList.map fun b : Fin m => n + b.val).length - 1 ∧
            pV.2 < base1 + pV.1.length ∧
            ∀ w : List Bool, w.length = base1 →
              (wiresFrom pV.1 w).getD pV.2 false = (R_R.toList.map fun b : Fin m => n + b.val).any (fun i => w.getD i false) :=
          buildOr_props base1 (R_R.toList.map fun b : Fin m => n + b.val)
            hRR_neL (fun i hi => by obtain ⟨b, _, rfl⟩ := List.mem_map.1 hi; have := b.isLt; omega)
        set ow := base1 + pV.1.length
        refine ⟨pU.1 ++ pV.1 ++ [⟨GateOp.or, [pU.2, pV.2]⟩], ow, ?_, ?_, ?_, fun u v => ?_⟩
        · intro g hg
          simp only [List.mem_append, List.mem_singleton] at hg
          rcases hg with (hg | hg) | rfl
          · exact hmU g hg
          · exact hmV g hg
          · exact ⟨by simp, by simp⟩
        · simp only [List.length_append, List.length_singleton, hlU, hlV, List.length_map,
            Finset.length_toList]
          have hRL1 : 1 ≤ R_L.card := Finset.card_pos.2 hRL_ne
          have hRR1 : 1 ≤ R_R.card := Finset.card_pos.2 hRR_ne
          simp only [hS0, hT0, Finset.card_empty, Nat.add_zero, Nat.zero_add] at ht_le_X ht_le_Y hRL_card hRR_card
          have hsumL1 : 1 ≤ (nf.rects.map fun p => p.1.card).sum := by
            rcases List.length_eq_one_iff.1 ht1 with ⟨p, hp⟩
            rw [hp]; simpa using Finset.card_pos.2 (hval.2.2.1 p (by simp [hp])).1
          have hsumR1 : 1 ≤ (nf.rects.map fun p => p.2.card).sum := by
            rcases List.length_eq_one_iff.1 ht1 with ⟨p, hp⟩
            rw [hp]; simpa using Finset.card_pos.2 (hval.2.2.1 p (by simp [hp])).2.1
          omega
        · simp [ow, base1, List.length_append]; omega
        · rw [wiresFrom_snoc, wiresFrom_append, getD_snoc, length_wiresFrom, length_wiresFrom,
            oneEach_len]
          simp only [ow, base1, ↓reduceIte, GateOp.eval, List.map_cons, List.map_nil,
            List.any_cons, List.any_nil, Bool.or_false, id]
          have h1 : (wiresFrom pV.1 (wiresFrom pU.1 (oneEach u v))).getD pU.2 false = decide (u ∈ R_L) := by
            rw [getD_wiresFrom pV.1 _ _ (by rw [length_wiresFrom, oneEach_len]; exact hoU),
                heU _ (oneEach_len u v), ← @eval_rowS R_L u v (Classical.propDecidable _), Bool.eq_iff_iff]
            simp only [List.any_map, Function.comp_def, List.any_eq_true, decide_eq_true_eq]
            exact ⟨fun ⟨a, ha, h⟩ => ⟨a, Finset.mem_toList.1 ha, h⟩,
                   fun ⟨a, ha, h⟩ => ⟨a, Finset.mem_toList.2 ha, h⟩⟩
          have h2 : (wiresFrom pV.1 (wiresFrom pU.1 (oneEach u v))).getD pV.2 false = decide (v ∈ R_R) := by
            rw [heV _ (by rw [length_wiresFrom, oneEach_len]), ← @eval_colT R_R u v (Classical.propDecidable _), Bool.eq_iff_iff]
            simp only [List.any_map, Function.comp_def, List.any_eq_true, decide_eq_true_eq]
            constructor
            · rintro ⟨b, hb, h⟩
              rw [getD_wiresFrom pU.1 _ _ (by rw [oneEach_len]; have := b.isLt; omega)] at h
              exact ⟨b, Finset.mem_toList.1 hb, h⟩
            · rintro ⟨b, hb, h⟩
              refine ⟨b, Finset.mem_toList.2 hb, ?_⟩
              rwa [getD_wiresFrom pU.1 _ _ (by rw [oneEach_len]; have := b.isLt; omega)]
          rw [h1, h2]
          rcases List.length_eq_one_iff.1 ht1 with ⟨p, hp⟩
          have hRu := (u_part u).1
          have hRv := (v_part v).1
          simp only [MonoNF.eval, hS0, hT0, hp, Finset.notMem_empty, false_or, List.mem_singleton,
            exists_eq_left, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false] at hRu hRv ⊢
          by_cases hu : u ∈ p.1 <;> by_cases hv : v ∈ p.2 <;> simp [hRu, hRv, hu, hv]
      · -- `t ≥ 2` and `S0 = ∅, T0 = ∅`: `Th_2(Z_1, ..., Z_t) | (U_0 | V_0)`!
        have ht2 : 2 ≤ nf.rects.length := by
          have : 0 < nf.rects.length := List.length_pos_iff.2 hrt
          omega
        let rowBlocks := R_L :: nf.rects.map Prod.fst
        let colBlocks := R_R :: nf.rects.map Prod.snd
        have hrb_ne : ∀ S ∈ rowBlocks, S.Nonempty := by
          intro S hS; rcases List.mem_cons.1 hS with rfl | hS
          · exact hRL_ne
          · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hS; exact (hval.2.2.1 p hp).1
        have hcb_ne : ∀ T ∈ colBlocks, T.Nonempty := by
          intro T hT; rcases List.mem_cons.1 hT with rfl | hT
          · exact hRR_ne
          · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hT; exact (hval.2.2.1 p hp).2.1
        obtain ⟨hmU, hlU, hlenU, hoU, heU⟩ := buildOrFinsets_props (fun a : Fin n => a.val) (n + m)
          rowBlocks hrb_ne (fun _ _ a _ => by have := a.isLt; omega)
        set pU := buildOrFinsets (n + m) (fun a : Fin n => a.val) rowBlocks
        set b1 := n + m + pU.1.length
        obtain ⟨hmV, hlV, hlenV, hoV, heV⟩ := buildOrFinsets_props (fun b : Fin m => n + b.val) b1
          colBlocks hcb_ne (fun _ _ b _ => by have := b.isLt; omega)
        set pV := buildOrFinsets b1 (fun b : Fin m => n + b.val) colBlocks
        set b2 := b1 + pV.1.length
        have hlenUV : pU.2.length = pV.2.length := by simp [hlenU, hlenV, rowBlocks, colBlocks]
        set pZ := buildPairOrs b2 pU.2 pV.2
        obtain ⟨hmZ, hlZ, hlenZ, hoZ, heZ⟩ :
            (∀ g ∈ pZ.1, GateMono g) ∧ pZ.1.length = pU.2.length ∧ pZ.2.length = pU.2.length ∧
            (∀ i ∈ pZ.2, i < b2 + pZ.1.length) ∧
            ∀ w : List Bool, w.length = b2 →
              pZ.2.map (fun i => (wiresFrom pZ.1 w).getD i false) =
              List.zipWith (fun a b => w.getD a false || w.getD b false) pU.2 pV.2 :=
          buildPairOrs_props b2 pU.2 pV.2 hlenUV
            (fun i hi => by have := hoU i hi; omega) (fun i hi => by have := hoV i hi; omega)
        cases hZcons : pZ.2 with
        | nil => exfalso; have := hlenZ; rw [hZcons, hlenU] at this; simp [rowBlocks] at this
        | cons wZ0 wZs =>
          have hwZs_len : wZs.length = nf.rects.length := by
            have := hlenZ; rw [hZcons, hlenU] at this; simpa [rowBlocks] using this
          set b3 := b2 + pZ.1.length
          set pT := buildTh2 b3 wZs
          obtain ⟨hmT, hlT, hoT, heT⟩ :
              (∀ g ∈ pT.1, GateMono g) ∧ pT.1.length = 3 * wZs.length - 5 ∧ pT.2 < b3 + pT.1.length ∧
              ∀ w : List Bool, w.length = b3 → (wiresFrom pT.1 w).getD pT.2 false = atLeastTwo (fun i => w.getD i false) wZs :=
            buildTh2_props b3 wZs (by omega)
              (fun i hi => hoZ i (by rw [hZcons]; exact List.mem_cons_of_mem _ hi))
          set ow := b3 + pT.1.length
          refine ⟨pU.1 ++ pV.1 ++ pZ.1 ++ pT.1 ++ [⟨GateOp.or, [wZ0, pT.2]⟩], ow, ?_, ?_, ?_, fun u v => ?_⟩
          · intro g hg
            simp only [List.mem_append, List.mem_singleton] at hg
            rcases hg with (((hg | hg) | hg) | hg) | rfl
            · exact hmU g hg
            · exact hmV g hg
            · exact hmZ g hg
            · exact hmT g hg
            · exact ⟨by simp, by simp⟩
          · have hsumU : (rowBlocks.map fun S => S.card - 1).sum + (nf.rects.length + 1) =
                R_L.card + (nf.rects.map fun p => p.1.card).sum := by
              have h := sum_sub_one_eq rowBlocks hrb_ne
              have hlen : rowBlocks.length = nf.rects.length + 1 := by simp [rowBlocks]
              have hrhs : (rowBlocks.map Finset.card).sum = R_L.card + (nf.rects.map fun p => p.1.card).sum := by
                simp [rowBlocks, List.map_map, Function.comp_def]
              omega
            have hsumV : (colBlocks.map fun S => S.card - 1).sum + (nf.rects.length + 1) =
                R_R.card + (nf.rects.map fun p => p.2.card).sum := by
              have h := sum_sub_one_eq colBlocks hcb_ne
              have hlen : colBlocks.length = nf.rects.length + 1 := by simp [colBlocks]
              have hrhs : (colBlocks.map Finset.card).sum = R_R.card + (nf.rects.map fun p => p.2.card).sum := by
                simp [colBlocks, List.map_map, Function.comp_def]
              omega
            simp only [hS0, hT0, Finset.card_empty, Nat.add_zero, Nat.zero_add] at ht_le_X ht_le_Y hRL_card hRR_card
            simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil,
              hlU, hlV, hlZ, hlT, hlenU, hwZs_len, rowBlocks, List.length_map]
            have hsumU' : ((R_L :: nf.rects.map Prod.fst).map fun S => S.card - 1).sum + (nf.rects.length + 1) =
                R_L.card + (nf.rects.map fun p => p.1.card).sum := hsumU
            have hsumV' : ((R_R :: nf.rects.map Prod.snd).map fun S => S.card - 1).sum + (nf.rects.length + 1) =
                R_R.card + (nf.rects.map fun p => p.2.card).sum := hsumV
            omega
          · simp [ow, b3, b2, b1, List.length_append]; omega
          · set w0 := oneEach u v
            have lw0 : w0.length = n + m := oneEach_len u v
            set w1 := wiresFrom pU.1 w0; have lw1 : w1.length = b1 := by rw [length_wiresFrom, lw0]
            set w2 := wiresFrom pV.1 w1; have lw2 : w2.length = b2 := by rw [length_wiresFrom, lw1]
            set w3 := wiresFrom pZ.1 w2; have lw3 : w3.length = b3 := by rw [length_wiresFrom, lw2]
            have hmapU : pU.2.map (fun i => w2.getD i false) =
                rowBlocks.map (fun S => decide (u ∈ S)) := by
              have : pU.2.map (fun i => w2.getD i false) = pU.2.map (fun i => w1.getD i false) :=
                List.map_congr_left fun i hi => getD_wiresFrom pV.1 w1 i (by rw [lw1]; exact hoU i hi)
              rw [this, heU w0 lw0]
              exact List.map_congr_left fun S _ => eval_rowS S u v
            have hmapV : pV.2.map (fun i => w2.getD i false) =
                colBlocks.map (fun T => decide (v ∈ T)) := by
              rw [heV w1 lw1]
              exact List.map_congr_left fun T _ => eval_colT_after T u v pU.1
            have hmapZ : pZ.2.map (fun i => w3.getD i false) =
                (decide (u ∈ R_L) || decide (v ∈ R_R)) ::
                nf.rects.map (fun p => decide (u ∈ p.1) || decide (v ∈ p.2)) := by
              rw [heZ w2 lw2, zipWith_map_bool (fun i => w2.getD i false) pU.2 pV.2, hmapU, hmapV]
              simp only [rowBlocks, colBlocks, List.map_cons, List.zipWith_cons_cons]
              congr 1
              exact zipWith_rects (fun S => decide (u ∈ S)) (fun T => decide (v ∈ T)) nf.rects
            rw [hZcons, List.map_cons] at hmapZ
            have hZ0 : w3.getD wZ0 false = (decide (u ∈ R_L) || decide (v ∈ R_R)) := by
              injection hmapZ with h1 _
            have hZs : wZs.map (fun i => w3.getD i false) =
                nf.rects.map (fun p => decide (u ∈ p.1) || decide (v ∈ p.2)) := by
              injection hmapZ with _ h2
            rw [wiresFrom_snoc, wiresFrom_append, wiresFrom_append, wiresFrom_append]
            change (wiresFrom pT.1 w3 ++ _).getD ow false = !nf.eval u v
            rw [getD_snoc, length_wiresFrom, lw3]
            simp only [ow, ↓reduceIte, GateOp.eval, List.map_cons, List.map_nil,
              List.any_cons, List.any_nil, Bool.or_false, id]
            have hwZ0_lt : wZ0 < b3 := hoZ wZ0 (by rw [hZcons]; simp)
            rw [getD_wiresFrom pT.1 w3 wZ0 (by rw [lw3]; exact hwZ0_lt), hZ0,
                heT w3 lw3, atLeastTwo, hZs, count_Z u v]
            have hRu := (u_part u).1
            have hRv := (v_part v).1
            simp only [MonoNF.eval, hS0, hT0, Finset.notMem_empty, false_or] at hRu hRv ⊢
            by_cases hhit : ∃ p ∈ nf.rects, u ∈ p.1 ∧ v ∈ p.2
            · have ⟨p, hp, hu, hv⟩ := hhit
              have h1 : ¬ u ∈ R_L := fun h => (hRu.1 h).2 ⟨p, hp, hu⟩
              have h2 : ¬ v ∈ R_R := fun h => (hRv.1 h).2 ⟨p, hp, hv⟩
              simp [hhit, h1, h2]
            · by_cases hu_r : ∃ p ∈ nf.rects, u ∈ p.1 <;> by_cases hv_r : ∃ p ∈ nf.rects, v ∈ p.2
              · simp [hhit, hu_r, hv_r]
              · have h2 : v ∈ R_R := hRv.2 ⟨by simp, hv_r⟩
                simp [hhit, h2]
              · have h1 : u ∈ R_L := hRu.2 ⟨by simp, hu_r⟩
                simp [hhit, h1]
              · have h1 : u ∈ R_L := hRu.2 ⟨by simp, hu_r⟩
                simp [hhit, h1]
  · -- CASE B: `S0 = ∅ ∧ T0 ≠ ∅` -> `Th_2(U_0, Z_1..Z_t) | V_0` (or just `V_0` if `t = 0`)!
    have hT0_pos : 1 ≤ nf.T0.card := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hT0)
    by_cases hrt : nf.rects = []
    · -- `t = 0`: `¬H = (v ∈ R_R)` = `V_0`!
      have hRR_neL : R_R.toList.map (fun b : Fin m => n + b.val) ≠ [] := by
        intro h; obtain ⟨b, hb⟩ := hRR_ne
        exact List.not_mem_nil (List.map_eq_nil_iff.1 h ▸ Finset.mem_toList.2 hb)
      set pV := buildOr (n + m) (R_R.toList.map fun b : Fin m => n + b.val)
      obtain ⟨hmV, hlV, hoV, heV⟩ :
          (∀ g ∈ pV.1, GateMono g) ∧
          pV.1.length = (R_R.toList.map fun b : Fin m => n + b.val).length - 1 ∧
          pV.2 < n + m + pV.1.length ∧
          ∀ w : List Bool, w.length = n + m →
            (wiresFrom pV.1 w).getD pV.2 false = (R_R.toList.map fun b : Fin m => n + b.val).any (fun i => w.getD i false) :=
        buildOr_props (n + m) (R_R.toList.map fun b : Fin m => n + b.val)
          hRR_neL (fun i hi => by obtain ⟨b, _, rfl⟩ := List.mem_map.1 hi; have := b.isLt; omega)
      refine ⟨pV.1, pV.2, hmV, ?_, hoV, fun u v => ?_⟩
      · simp only [hlV, List.length_map, Finset.length_toList]
        simp only [hrt, List.map_nil, List.sum_nil, Nat.add_zero] at hRR_card
        have : 1 ≤ R_R.card := Finset.card_pos.2 hRR_ne
        have : nf.T0.card ≤ Y.card := Finset.card_le_card hval.2.1
        omega
      · rw [heV _ (oneEach_len u v)]
        have hEq : (R_R.toList.map fun b : Fin m => n + b.val).any (fun i => (oneEach u v).getD i false) =
            decide (∃ b ∈ R_R, (oneEach u v).getD (n + b.val) false = true) := by
          rw [Bool.eq_iff_iff]
          simp only [List.any_map, Function.comp_def, List.any_eq_true, decide_eq_true_eq]
          exact ⟨fun ⟨b, hb, h⟩ => ⟨b, Finset.mem_toList.1 hb, h⟩,
                 fun ⟨b, hb, h⟩ => ⟨b, Finset.mem_toList.2 hb, h⟩⟩
        rw [hEq, eval_colT]
        have hRv := (v_part v).1
        simp only [MonoNF.eval, hS0, hrt, Finset.notMem_empty, false_or, List.not_mem_nil,
          false_and, exists_false, or_false] at hRv ⊢
        by_cases hv : v ∈ nf.T0 <;> simp [hRv, hv]
    · -- `t ≥ 1`, `S0 = ∅, T0 ≠ ∅`: `Th_2(U_0, Z_1..Z_t) | V_0`!
      have ht1 : 1 ≤ nf.rects.length := List.length_pos_iff.2 hrt
      let rowBlocks := R_L :: nf.rects.map Prod.fst
      let colBlocks := R_R :: nf.rects.map Prod.snd
      have hrb_ne : ∀ S ∈ rowBlocks, S.Nonempty := fun S hS => by
        rcases List.mem_cons.1 hS with rfl | hS
        · exact hRL_ne
        · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hS; exact (hval.2.2.1 p hp).1
      have hcb_ne : ∀ T ∈ colBlocks, T.Nonempty := fun T hT => by
        rcases List.mem_cons.1 hT with rfl | hT
        · exact hRR_ne
        · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hT; exact (hval.2.2.1 p hp).2.1
      obtain ⟨hmU, hlU, hlenU, hoU, heU⟩ := buildOrFinsets_props (fun a : Fin n => a.val) (n + m)
        rowBlocks hrb_ne (fun _ _ a _ => by have := a.isLt; omega)
      set pU := buildOrFinsets (n + m) (fun a : Fin n => a.val) rowBlocks
      set b1 := n + m + pU.1.length
      obtain ⟨hmV, hlV, hlenV, hoV, heV⟩ := buildOrFinsets_props (fun b : Fin m => n + b.val) b1
        colBlocks hcb_ne (fun _ _ b _ => by have := b.isLt; omega)
      set pV := buildOrFinsets b1 (fun b : Fin m => n + b.val) colBlocks
      set b2 := b1 + pV.1.length
      cases hUcons : pU.2 with
      | nil => exfalso; have := hlenU; rw [hUcons] at this; simp [rowBlocks] at this
      | cons wU0 wUs =>
        cases hVcons : pV.2 with
        | nil => exfalso; have := hlenV; rw [hVcons] at this; simp [colBlocks] at this
        | cons wV0 wVs =>
          have hlenUV : wUs.length = wVs.length := by
            have h1 := hlenU; rw [hUcons] at h1
            have h2 := hlenV; rw [hVcons] at h2
            simp [rowBlocks, colBlocks] at h1 h2; omega
          have hwUs_len : wUs.length = nf.rects.length := by
            have h1 := hlenU; rw [hUcons] at h1; simpa [rowBlocks] using h1
          set pZ := buildPairOrs b2 wUs wVs
          obtain ⟨hmZ, hlZ, hlenZ, hoZ, heZ⟩ :
              (∀ g ∈ pZ.1, GateMono g) ∧ pZ.1.length = wUs.length ∧ pZ.2.length = wUs.length ∧
              (∀ i ∈ pZ.2, i < b2 + pZ.1.length) ∧
              ∀ w : List Bool, w.length = b2 →
                pZ.2.map (fun i => (wiresFrom pZ.1 w).getD i false) =
                List.zipWith (fun a b => w.getD a false || w.getD b false) wUs wVs :=
            buildPairOrs_props b2 wUs wVs hlenUV
              (fun i hi => by have := hoU i (by rw [hUcons]; exact List.mem_cons_of_mem _ hi); omega)
              (fun i hi => by have := hoV i (by rw [hVcons]; exact List.mem_cons_of_mem _ hi); omega)
          set b3 := b2 + pZ.1.length
          set pT := buildTh2 b3 (wU0 :: pZ.2)
          obtain ⟨hmT, hlT, hoT, heT⟩ :
              (∀ g ∈ pT.1, GateMono g) ∧ pT.1.length = 3 * (wU0 :: pZ.2).length - 5 ∧ pT.2 < b3 + pT.1.length ∧
              ∀ w : List Bool, w.length = b3 → (wiresFrom pT.1 w).getD pT.2 false = atLeastTwo (fun i => w.getD i false) (wU0 :: pZ.2) :=
            buildTh2_props b3 (wU0 :: pZ.2)
              (by simp [hlenZ, hwUs_len]; omega)
              (fun i hi => by
                rcases List.mem_cons.1 hi with rfl | hi
                · have := hoU i (by rw [hUcons]; simp); omega
                · exact hoZ i hi)
          set ow := b3 + pT.1.length
          refine ⟨pU.1 ++ pV.1 ++ pZ.1 ++ pT.1 ++ [⟨GateOp.or, [wV0, pT.2]⟩], ow, ?_, ?_, ?_, fun u v => ?_⟩
          · intro g hg
            simp only [List.mem_append, List.mem_singleton] at hg
            rcases hg with (((hg | hg) | hg) | hg) | rfl
            · exact hmU g hg
            · exact hmV g hg
            · exact hmZ g hg
            · exact hmT g hg
            · exact ⟨by simp, by simp⟩
          · have hsumU : (rowBlocks.map fun S => S.card - 1).sum + (nf.rects.length + 1) =
                R_L.card + (nf.rects.map fun p => p.1.card).sum := by
              have h := sum_sub_one_eq rowBlocks hrb_ne
              have hlen : rowBlocks.length = nf.rects.length + 1 := by simp [rowBlocks]
              have hrhs : (rowBlocks.map Finset.card).sum = R_L.card + (nf.rects.map fun p => p.1.card).sum := by
                simp [rowBlocks, List.map_map, Function.comp_def]
              omega
            have hsumV : (colBlocks.map fun S => S.card - 1).sum + (nf.rects.length + 1) =
                R_R.card + (nf.rects.map fun p => p.2.card).sum := by
              have h := sum_sub_one_eq colBlocks hcb_ne
              have hlen : colBlocks.length = nf.rects.length + 1 := by simp [colBlocks]
              have hrhs : (colBlocks.map Finset.card).sum = R_R.card + (nf.rects.map fun p => p.2.card).sum := by
                simp [colBlocks, List.map_map, Function.comp_def]
              omega
            simp only [hS0, Finset.card_empty, Nat.add_zero, Nat.zero_add] at ht_le_X hRL_card
            simp only [List.length_append, List.length_cons, List.length_nil, hlU, hlV, hlZ, hlT,
              hlenZ, hwUs_len]
            omega
          · simp [ow, b3, b2, b1, List.length_append]; omega
          · set w0 := oneEach u v
            have lw0 : w0.length = n + m := oneEach_len u v
            set w1 := wiresFrom pU.1 w0; have lw1 : w1.length = b1 := by rw [length_wiresFrom, lw0]
            set w2 := wiresFrom pV.1 w1; have lw2 : w2.length = b2 := by rw [length_wiresFrom, lw1]
            set w3 := wiresFrom pZ.1 w2; have lw3 : w3.length = b3 := by rw [length_wiresFrom, lw2]
            have hmapU : pU.2.map (fun i => w2.getD i false) = rowBlocks.map (fun S => decide (u ∈ S)) := by
              have : pU.2.map (fun i => w2.getD i false) = pU.2.map (fun i => w1.getD i false) :=
                List.map_congr_left fun i hi => getD_wiresFrom pV.1 w1 i (by rw [lw1]; exact hoU i hi)
              rw [this, heU w0 lw0]; exact List.map_congr_left fun S _ => eval_rowS S u v
            have hmapV : pV.2.map (fun i => w2.getD i false) = colBlocks.map (fun T => decide (v ∈ T)) := by
              rw [heV w1 lw1]; exact List.map_congr_left fun T _ => eval_colT_after T u v pU.1
            rw [hUcons, List.map_cons] at hmapU; rw [hVcons, List.map_cons] at hmapV
            have hU0 : w2.getD wU0 false = decide (u ∈ R_L) := by injection hmapU with h1 _
            have hUs : wUs.map (fun i => w2.getD i false) = (nf.rects.map Prod.fst).map (fun S => decide (u ∈ S)) := by
              injection hmapU with _ h2
            have hV0 : w2.getD wV0 false = decide (v ∈ R_R) := by injection hmapV with h1 _
            have hVs : wVs.map (fun i => w2.getD i false) = (nf.rects.map Prod.snd).map (fun T => decide (v ∈ T)) := by
              injection hmapV with _ h2
            have hZs : pZ.2.map (fun i => w3.getD i false) =
                nf.rects.map (fun p => decide (u ∈ p.1) || decide (v ∈ p.2)) := by
              rw [heZ w2 lw2, zipWith_map_bool (fun i => w2.getD i false) wUs wVs, hUs, hVs]
              exact zipWith_rects (fun S => decide (u ∈ S)) (fun T => decide (v ∈ T)) nf.rects
            have hwU0_lt : wU0 < b2 := by have := hoU wU0 (by rw [hUcons]; simp); omega
            have hwV0_lt : wV0 < b2 := hoV wV0 (by rw [hVcons]; simp)
            rw [wiresFrom_snoc, wiresFrom_append, wiresFrom_append, wiresFrom_append]
            change (wiresFrom pT.1 w3 ++ _).getD ow false = !nf.eval u v
            rw [getD_snoc, length_wiresFrom, lw3]
            simp only [ow, ↓reduceIte, GateOp.eval, List.map_cons, List.map_nil,
              List.any_cons, List.any_nil, Bool.or_false, id]
            rw [getD_wiresFrom pT.1 w3 wV0 (by rw [lw3]; omega),
                getD_wiresFrom pZ.1 w2 wV0 (by rw [lw2]; exact hwV0_lt), hV0,
                heT w3 lw3, atLeastTwo, List.map_cons,
                getD_wiresFrom pZ.1 w2 wU0 (by rw [lw2]; exact hwU0_lt), hU0, hZs,
                List.count_cons, count_Z u v]
            have hRu := (u_part u).1; have hRv := (v_part v).1; have hTdis := (v_part v).2
            simp only [MonoNF.eval, hS0, Finset.notMem_empty, false_or] at hRu hRv ⊢
            by_cases hv0 : v ∈ nf.T0
            · have hv_notR : v ∉ R_R := fun h => (hRv.1 h).1 hv0
              have hv_notRec : ¬ ∃ p ∈ nf.rects, v ∈ p.2 := hTdis hv0
              have hboth : ¬ ∃ p ∈ nf.rects, u ∈ p.1 ∧ v ∈ p.2 := fun ⟨p, hp, _, hv⟩ => hv_notRec ⟨p, hp, hv⟩
              by_cases hu_r : ∃ p ∈ nf.rects, u ∈ p.1
              · have hu_notR : u ∉ R_L := fun h => (hRu.1 h).2 hu_r
                simp [hv0, hv_notR, hv_notRec, hboth, hu_r, hu_notR]
              · have hu_R : u ∈ R_L := hRu.2 ⟨by simp, hu_r⟩
                simp [hv0, hv_notR, hv_notRec, hboth, hu_r, hu_R]
            · by_cases hhit : ∃ p ∈ nf.rects, u ∈ p.1 ∧ v ∈ p.2
              · have ⟨p, hp, hu, hv⟩ := hhit
                have hu_notR : u ∉ R_L := fun h => (hRu.1 h).2 ⟨p, hp, hu⟩
                have hv_notR : v ∉ R_R := fun h => (hRv.1 h).2 ⟨p, hp, hv⟩
                simp [hv0, hhit, hu_notR, hv_notR]
              · by_cases hv_r : ∃ p ∈ nf.rects, v ∈ p.2
                · by_cases hu_r : ∃ p ∈ nf.rects, u ∈ p.1
                  · simp [hv0, hhit, hv_r, hu_r]
                  · have hu_R : u ∈ R_L := hRu.2 ⟨by simp, hu_r⟩
                    simp [hv0, hhit, hv_r, hu_r, hu_R]
                · have hv_R : v ∈ R_R := hRv.2 ⟨hv0, hv_r⟩
                  simp [hv0, hhit, hv_R]
  · -- CASE C: `S0 ≠ ∅ ∧ T0 = ∅` -> symmetric to Case B (`Th_2(V_0, Z_1..Z_t) | U_0` or `U_0`)!
    have hS0_pos : 1 ≤ nf.S0.card := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hS0)
    by_cases hrt : nf.rects = []
    · have hRL_neL : R_L.toList.map (fun a : Fin n => a.val) ≠ [] := by
        intro h; obtain ⟨a, ha⟩ := hRL_ne
        exact List.not_mem_nil (List.map_eq_nil_iff.1 h ▸ Finset.mem_toList.2 ha)
      set pU := buildOr (n + m) (R_L.toList.map fun a : Fin n => a.val)
      obtain ⟨hmU, hlU, hoU, heU⟩ :
          (∀ g ∈ pU.1, GateMono g) ∧
          pU.1.length = (R_L.toList.map fun a : Fin n => a.val).length - 1 ∧
          pU.2 < n + m + pU.1.length ∧
          ∀ w : List Bool, w.length = n + m →
            (wiresFrom pU.1 w).getD pU.2 false = (R_L.toList.map fun a : Fin n => a.val).any (fun i => w.getD i false) :=
        buildOr_props (n + m) (R_L.toList.map fun a : Fin n => a.val)
          hRL_neL (fun i hi => by obtain ⟨a, _, rfl⟩ := List.mem_map.1 hi; have := a.isLt; omega)
      refine ⟨pU.1, pU.2, hmU, ?_, hoU, fun u v => ?_⟩
      · simp only [hlU, List.length_map, Finset.length_toList]
        simp only [hrt, List.map_nil, List.sum_nil, Nat.add_zero] at hRL_card
        have : 1 ≤ R_L.card := Finset.card_pos.2 hRL_ne
        have : nf.S0.card ≤ X.card := Finset.card_le_card hval.1
        omega
      · rw [heU _ (oneEach_len u v)]
        have hEq : (R_L.toList.map fun a : Fin n => a.val).any (fun i => (oneEach u v).getD i false) =
            decide (∃ a ∈ R_L, (oneEach u v).getD a.val false = true) := by
          rw [Bool.eq_iff_iff]
          simp only [List.any_map, Function.comp_def, List.any_eq_true, decide_eq_true_eq]
          exact ⟨fun ⟨a, ha, h⟩ => ⟨a, Finset.mem_toList.1 ha, h⟩,
                 fun ⟨a, ha, h⟩ => ⟨a, Finset.mem_toList.2 ha, h⟩⟩
        rw [hEq, eval_rowS]
        have hRu := (u_part u).1
        simp only [MonoNF.eval, hT0, hrt, Finset.notMem_empty, false_or, List.not_mem_nil,
          false_and, exists_false, or_false] at hRu ⊢
        by_cases hu : u ∈ nf.S0 <;> simp [hRu, hu]
    · have ht1 : 1 ≤ nf.rects.length := List.length_pos_iff.2 hrt
      let rowBlocks := R_L :: nf.rects.map Prod.fst
      let colBlocks := R_R :: nf.rects.map Prod.snd
      have hrb_ne : ∀ S ∈ rowBlocks, S.Nonempty := fun S hS => by
        rcases List.mem_cons.1 hS with rfl | hS
        · exact hRL_ne
        · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hS; exact (hval.2.2.1 p hp).1
      have hcb_ne : ∀ T ∈ colBlocks, T.Nonempty := fun T hT => by
        rcases List.mem_cons.1 hT with rfl | hT
        · exact hRR_ne
        · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hT; exact (hval.2.2.1 p hp).2.1
      obtain ⟨hmU, hlU, hlenU, hoU, heU⟩ := buildOrFinsets_props (fun a : Fin n => a.val) (n + m)
        rowBlocks hrb_ne (fun _ _ a _ => by have := a.isLt; omega)
      set pU := buildOrFinsets (n + m) (fun a : Fin n => a.val) rowBlocks
      set b1 := n + m + pU.1.length
      obtain ⟨hmV, hlV, hlenV, hoV, heV⟩ := buildOrFinsets_props (fun b : Fin m => n + b.val) b1
        colBlocks hcb_ne (fun _ _ b _ => by have := b.isLt; omega)
      set pV := buildOrFinsets b1 (fun b : Fin m => n + b.val) colBlocks
      set b2 := b1 + pV.1.length
      cases hUcons : pU.2 with
      | nil => exfalso; have := hlenU; rw [hUcons] at this; simp [rowBlocks] at this
      | cons wU0 wUs =>
        cases hVcons : pV.2 with
        | nil => exfalso; have := hlenV; rw [hVcons] at this; simp [colBlocks] at this
        | cons wV0 wVs =>
          have hlenUV : wUs.length = wVs.length := by
            have h1 := hlenU; rw [hUcons] at h1
            have h2 := hlenV; rw [hVcons] at h2
            simp [rowBlocks, colBlocks] at h1 h2; omega
          have hwUs_len : wUs.length = nf.rects.length := by
            have h1 := hlenU; rw [hUcons] at h1; simpa [rowBlocks] using h1
          set pZ := buildPairOrs b2 wUs wVs
          obtain ⟨hmZ, hlZ, hlenZ, hoZ, heZ⟩ :
              (∀ g ∈ pZ.1, GateMono g) ∧ pZ.1.length = wUs.length ∧ pZ.2.length = wUs.length ∧
              (∀ i ∈ pZ.2, i < b2 + pZ.1.length) ∧
              ∀ w : List Bool, w.length = b2 →
                pZ.2.map (fun i => (wiresFrom pZ.1 w).getD i false) =
                List.zipWith (fun a b => w.getD a false || w.getD b false) wUs wVs :=
            buildPairOrs_props b2 wUs wVs hlenUV
              (fun i hi => by have := hoU i (by rw [hUcons]; exact List.mem_cons_of_mem _ hi); omega)
              (fun i hi => by have := hoV i (by rw [hVcons]; exact List.mem_cons_of_mem _ hi); omega)
          set b3 := b2 + pZ.1.length
          set pT := buildTh2 b3 (wV0 :: pZ.2)
          obtain ⟨hmT, hlT, hoT, heT⟩ :
              (∀ g ∈ pT.1, GateMono g) ∧ pT.1.length = 3 * (wV0 :: pZ.2).length - 5 ∧ pT.2 < b3 + pT.1.length ∧
              ∀ w : List Bool, w.length = b3 → (wiresFrom pT.1 w).getD pT.2 false = atLeastTwo (fun i => w.getD i false) (wV0 :: pZ.2) :=
            buildTh2_props b3 (wV0 :: pZ.2)
              (by simp [hlenZ, hwUs_len]; omega)
              (fun i hi => by
                rcases List.mem_cons.1 hi with rfl | hi
                · have := hoV i (by rw [hVcons]; simp); omega
                · exact hoZ i hi)
          set ow := b3 + pT.1.length
          refine ⟨pU.1 ++ pV.1 ++ pZ.1 ++ pT.1 ++ [⟨GateOp.or, [wU0, pT.2]⟩], ow, ?_, ?_, ?_, fun u v => ?_⟩
          · intro g hg
            simp only [List.mem_append, List.mem_singleton] at hg
            rcases hg with (((hg | hg) | hg) | hg) | rfl
            · exact hmU g hg
            · exact hmV g hg
            · exact hmZ g hg
            · exact hmT g hg
            · exact ⟨by simp, by simp⟩
          · have hsumU : (rowBlocks.map fun S => S.card - 1).sum + (nf.rects.length + 1) =
                R_L.card + (nf.rects.map fun p => p.1.card).sum := by
              have h := sum_sub_one_eq rowBlocks hrb_ne
              have hlen : rowBlocks.length = nf.rects.length + 1 := by simp [rowBlocks]
              have hrhs : (rowBlocks.map Finset.card).sum = R_L.card + (nf.rects.map fun p => p.1.card).sum := by
                simp [rowBlocks, List.map_map, Function.comp_def]
              omega
            have hsumV : (colBlocks.map fun S => S.card - 1).sum + (nf.rects.length + 1) =
                R_R.card + (nf.rects.map fun p => p.2.card).sum := by
              have h := sum_sub_one_eq colBlocks hcb_ne
              have hlen : colBlocks.length = nf.rects.length + 1 := by simp [colBlocks]
              have hrhs : (colBlocks.map Finset.card).sum = R_R.card + (nf.rects.map fun p => p.2.card).sum := by
                simp [colBlocks, List.map_map, Function.comp_def]
              omega
            simp only [hT0, Finset.card_empty, Nat.add_zero, Nat.zero_add] at ht_le_Y hRR_card
            simp only [List.length_append, List.length_cons, List.length_nil, hlU, hlV, hlZ, hlT,
              hlenZ, hwUs_len]
            omega
          · simp [ow, b3, b2, b1, List.length_append]; omega
          · set w0 := oneEach u v
            have lw0 : w0.length = n + m := oneEach_len u v
            set w1 := wiresFrom pU.1 w0; have lw1 : w1.length = b1 := by rw [length_wiresFrom, lw0]
            set w2 := wiresFrom pV.1 w1; have lw2 : w2.length = b2 := by rw [length_wiresFrom, lw1]
            set w3 := wiresFrom pZ.1 w2; have lw3 : w3.length = b3 := by rw [length_wiresFrom, lw2]
            have hmapU : pU.2.map (fun i => w2.getD i false) = rowBlocks.map (fun S => decide (u ∈ S)) := by
              have : pU.2.map (fun i => w2.getD i false) = pU.2.map (fun i => w1.getD i false) :=
                List.map_congr_left fun i hi => getD_wiresFrom pV.1 w1 i (by rw [lw1]; exact hoU i hi)
              rw [this, heU w0 lw0]; exact List.map_congr_left fun S _ => eval_rowS S u v
            have hmapV : pV.2.map (fun i => w2.getD i false) = colBlocks.map (fun T => decide (v ∈ T)) := by
              rw [heV w1 lw1]; exact List.map_congr_left fun T _ => eval_colT_after T u v pU.1
            rw [hUcons, List.map_cons] at hmapU; rw [hVcons, List.map_cons] at hmapV
            have hU0 : w2.getD wU0 false = decide (u ∈ R_L) := by injection hmapU with h1 _
            have hUs : wUs.map (fun i => w2.getD i false) = (nf.rects.map Prod.fst).map (fun S => decide (u ∈ S)) := by
              injection hmapU with _ h2
            have hV0 : w2.getD wV0 false = decide (v ∈ R_R) := by injection hmapV with h1 _
            have hVs : wVs.map (fun i => w2.getD i false) = (nf.rects.map Prod.snd).map (fun T => decide (v ∈ T)) := by
              injection hmapV with _ h2
            have hZs : pZ.2.map (fun i => w3.getD i false) =
                nf.rects.map (fun p => decide (u ∈ p.1) || decide (v ∈ p.2)) := by
              rw [heZ w2 lw2, zipWith_map_bool (fun i => w2.getD i false) wUs wVs, hUs, hVs]
              exact zipWith_rects (fun S => decide (u ∈ S)) (fun T => decide (v ∈ T)) nf.rects
            have hwU0_lt : wU0 < b2 := by have := hoU wU0 (by rw [hUcons]; simp); omega
            have hwV0_lt : wV0 < b2 := hoV wV0 (by rw [hVcons]; simp)
            rw [wiresFrom_snoc, wiresFrom_append, wiresFrom_append, wiresFrom_append]
            change (wiresFrom pT.1 w3 ++ _).getD ow false = !nf.eval u v
            rw [getD_snoc, length_wiresFrom, lw3]
            simp only [ow, ↓reduceIte, GateOp.eval, List.map_cons, List.map_nil,
              List.any_cons, List.any_nil, Bool.or_false, id]
            rw [getD_wiresFrom pT.1 w3 wU0 (by rw [lw3]; omega),
                getD_wiresFrom pZ.1 w2 wU0 (by rw [lw2]; exact hwU0_lt), hU0,
                heT w3 lw3, atLeastTwo, List.map_cons,
                getD_wiresFrom pZ.1 w2 wV0 (by rw [lw2]; exact hwV0_lt), hV0, hZs,
                List.count_cons, count_Z u v]
            have hRu := (u_part u).1; have hRv := (v_part v).1; have hSdis := (u_part u).2
            simp only [MonoNF.eval, hT0, Finset.notMem_empty, false_or] at hRu hRv ⊢
            by_cases hu0 : u ∈ nf.S0
            · have hu_notR : u ∉ R_L := fun h => (hRu.1 h).1 hu0
              have hu_notRec : ¬ ∃ p ∈ nf.rects, u ∈ p.1 := hSdis hu0
              have hboth : ¬ ∃ p ∈ nf.rects, u ∈ p.1 ∧ v ∈ p.2 := fun ⟨p, hp, hu, _⟩ => hu_notRec ⟨p, hp, hu⟩
              by_cases hv_r : ∃ p ∈ nf.rects, v ∈ p.2
              · have hv_notR : v ∉ R_R := fun h => (hRv.1 h).2 hv_r
                simp [hu0, hu_notR, hu_notRec, hboth, hv_r, hv_notR]
              · have hv_R : v ∈ R_R := hRv.2 ⟨by simp, hv_r⟩
                simp [hu0, hu_notR, hu_notRec, hboth, hv_r, hv_R]
            · by_cases hhit : ∃ p ∈ nf.rects, u ∈ p.1 ∧ v ∈ p.2
              · have ⟨p, hp, hu, hv⟩ := hhit
                have hu_notR : u ∉ R_L := fun h => (hRu.1 h).2 ⟨p, hp, hu⟩
                have hv_notR : v ∉ R_R := fun h => (hRv.1 h).2 ⟨p, hp, hv⟩
                simp [hu0, hhit, hu_notR, hv_notR]
              · by_cases hu_r : ∃ p ∈ nf.rects, u ∈ p.1
                · by_cases hv_r : ∃ p ∈ nf.rects, v ∈ p.2
                  · simp [hu0, hhit, hu_r, hv_r]
                  · have hv_R : v ∈ R_R := hRv.2 ⟨by simp, hv_r⟩
                    simp [hu0, hhit, hu_r, hv_r, hv_R]
                · have hu_R : u ∈ R_L := hRu.2 ⟨hu0, hu_r⟩
                  simp [hu0, hhit, hu_R]
  · -- CASE D: `S0 ≠ ∅ ∧ T0 ≠ ∅` -> `Th_2(U_0, V_0, Z_1..Z_t)` works for ALL `t ≥ 0`!!
    have hS0_pos : 1 ≤ nf.S0.card := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hS0)
    have hT0_pos : 1 ≤ nf.T0.card := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hT0)
    let rowBlocks := R_L :: nf.rects.map Prod.fst
    let colBlocks := R_R :: nf.rects.map Prod.snd
    have hrb_ne : ∀ S ∈ rowBlocks, S.Nonempty := fun S hS => by
      rcases List.mem_cons.1 hS with rfl | hS
      · exact hRL_ne
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hS; exact (hval.2.2.1 p hp).1
    have hcb_ne : ∀ T ∈ colBlocks, T.Nonempty := fun T hT => by
      rcases List.mem_cons.1 hT with rfl | hT
      · exact hRR_ne
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hT; exact (hval.2.2.1 p hp).2.1
    obtain ⟨hmU, hlU, hlenU, hoU, heU⟩ := buildOrFinsets_props (fun a : Fin n => a.val) (n + m)
      rowBlocks hrb_ne (fun _ _ a _ => by have := a.isLt; omega)
    set pU := buildOrFinsets (n + m) (fun a : Fin n => a.val) rowBlocks
    set b1 := n + m + pU.1.length
    obtain ⟨hmV, hlV, hlenV, hoV, heV⟩ := buildOrFinsets_props (fun b : Fin m => n + b.val) b1
      colBlocks hcb_ne (fun _ _ b _ => by have := b.isLt; omega)
    set pV := buildOrFinsets b1 (fun b : Fin m => n + b.val) colBlocks
    set b2 := b1 + pV.1.length
    cases hUcons : pU.2 with
    | nil => exfalso; have := hlenU; rw [hUcons] at this; simp [rowBlocks] at this
    | cons wU0 wUs =>
      cases hVcons : pV.2 with
      | nil => exfalso; have := hlenV; rw [hVcons] at this; simp [colBlocks] at this
      | cons wV0 wVs =>
        have hlenUV : wUs.length = wVs.length := by
          have h1 := hlenU; rw [hUcons] at h1
          have h2 := hlenV; rw [hVcons] at h2
          simp [rowBlocks, colBlocks] at h1 h2; omega
        have hwUs_len : wUs.length = nf.rects.length := by
          have h1 := hlenU; rw [hUcons] at h1; simpa [rowBlocks] using h1
        set pZ := buildPairOrs b2 wUs wVs
        obtain ⟨hmZ, hlZ, hlenZ, hoZ, heZ⟩ :
            (∀ g ∈ pZ.1, GateMono g) ∧ pZ.1.length = wUs.length ∧ pZ.2.length = wUs.length ∧
            (∀ i ∈ pZ.2, i < b2 + pZ.1.length) ∧
            ∀ w : List Bool, w.length = b2 →
              pZ.2.map (fun i => (wiresFrom pZ.1 w).getD i false) =
              List.zipWith (fun a b => w.getD a false || w.getD b false) wUs wVs :=
          buildPairOrs_props b2 wUs wVs hlenUV
            (fun i hi => by have := hoU i (by rw [hUcons]; exact List.mem_cons_of_mem _ hi); omega)
            (fun i hi => by have := hoV i (by rw [hVcons]; exact List.mem_cons_of_mem _ hi); omega)
        set b3 := b2 + pZ.1.length
        set pT := buildTh2 b3 (wU0 :: wV0 :: pZ.2)
        obtain ⟨hmT, hlT, hoT, heT⟩ :
            (∀ g ∈ pT.1, GateMono g) ∧ pT.1.length = 3 * (wU0 :: wV0 :: pZ.2).length - 5 ∧ pT.2 < b3 + pT.1.length ∧
            ∀ w : List Bool, w.length = b3 → (wiresFrom pT.1 w).getD pT.2 false = atLeastTwo (fun i => w.getD i false) (wU0 :: wV0 :: pZ.2) :=
          buildTh2_props b3 (wU0 :: wV0 :: pZ.2)
            (by simp)
            (fun i hi => by
              rcases List.mem_cons.1 hi with rfl | hi
              · have := hoU i (by rw [hUcons]; simp); omega
              · rcases List.mem_cons.1 hi with rfl | hi
                · have := hoV i (by rw [hVcons]; simp); omega
                · exact hoZ i hi)
        refine ⟨pU.1 ++ pV.1 ++ pZ.1 ++ pT.1, pT.2, ?_, ?_, ?_, fun u v => ?_⟩
        · intro g hg
          simp only [List.mem_append] at hg
          rcases hg with ((hg | hg) | hg) | hg
          · exact hmU g hg
          · exact hmV g hg
          · exact hmZ g hg
          · exact hmT g hg
        · have hsumU : (rowBlocks.map fun S => S.card - 1).sum + (nf.rects.length + 1) =
              R_L.card + (nf.rects.map fun p => p.1.card).sum := by
            have h := sum_sub_one_eq rowBlocks hrb_ne
            have hlen : rowBlocks.length = nf.rects.length + 1 := by simp [rowBlocks]
            have hrhs : (rowBlocks.map Finset.card).sum = R_L.card + (nf.rects.map fun p => p.1.card).sum := by
              simp [rowBlocks, List.map_map, Function.comp_def]
            omega
          have hsumV : (colBlocks.map fun S => S.card - 1).sum + (nf.rects.length + 1) =
              R_R.card + (nf.rects.map fun p => p.2.card).sum := by
            have h := sum_sub_one_eq colBlocks hcb_ne
            have hlen : colBlocks.length = nf.rects.length + 1 := by simp [colBlocks]
            have hrhs : (colBlocks.map Finset.card).sum = R_R.card + (nf.rects.map fun p => p.2.card).sum := by
              simp [colBlocks, List.map_map, Function.comp_def]
            omega
          simp only [List.length_append, List.length_cons, List.length_nil, hlU, hlV, hlZ, hlT, hlenZ, hwUs_len]
          omega
        · simp [b3, b2, b1, List.length_append] at hoT ⊢; omega
        · set w0 := oneEach u v
          have lw0 : w0.length = n + m := oneEach_len u v
          set w1 := wiresFrom pU.1 w0; have lw1 : w1.length = b1 := by rw [length_wiresFrom, lw0]
          set w2 := wiresFrom pV.1 w1; have lw2 : w2.length = b2 := by rw [length_wiresFrom, lw1]
          set w3 := wiresFrom pZ.1 w2; have lw3 : w3.length = b3 := by rw [length_wiresFrom, lw2]
          have hmapU : pU.2.map (fun i => w2.getD i false) = rowBlocks.map (fun S => decide (u ∈ S)) := by
            have : pU.2.map (fun i => w2.getD i false) = pU.2.map (fun i => w1.getD i false) :=
              List.map_congr_left fun i hi => getD_wiresFrom pV.1 w1 i (by rw [lw1]; exact hoU i hi)
            rw [this, heU w0 lw0]; exact List.map_congr_left fun S _ => eval_rowS S u v
          have hmapV : pV.2.map (fun i => w2.getD i false) = colBlocks.map (fun T => decide (v ∈ T)) := by
            rw [heV w1 lw1]; exact List.map_congr_left fun T _ => eval_colT_after T u v pU.1
          rw [hUcons, List.map_cons] at hmapU; rw [hVcons, List.map_cons] at hmapV
          have hU0 : w2.getD wU0 false = decide (u ∈ R_L) := by injection hmapU with h1 _
          have hUs : wUs.map (fun i => w2.getD i false) = (nf.rects.map Prod.fst).map (fun S => decide (u ∈ S)) := by
            injection hmapU with _ h2
          have hV0 : w2.getD wV0 false = decide (v ∈ R_R) := by injection hmapV with h1 _
          have hVs : wVs.map (fun i => w2.getD i false) = (nf.rects.map Prod.snd).map (fun T => decide (v ∈ T)) := by
            injection hmapV with _ h2
          have hZs : pZ.2.map (fun i => w3.getD i false) =
              nf.rects.map (fun p => decide (u ∈ p.1) || decide (v ∈ p.2)) := by
            rw [heZ w2 lw2, zipWith_map_bool (fun i => w2.getD i false) wUs wVs, hUs, hVs]
            exact zipWith_rects (fun S => decide (u ∈ S)) (fun T => decide (v ∈ T)) nf.rects
          have hwU0_lt : wU0 < b2 := by have := hoU wU0 (by rw [hUcons]; simp); omega
          have hwV0_lt : wV0 < b2 := hoV wV0 (by rw [hVcons]; simp)
          rw [wiresFrom_append, wiresFrom_append, wiresFrom_append]
          change (wiresFrom pT.1 w3).getD pT.2 false = !nf.eval u v
          rw [heT w3 lw3, atLeastTwo,
            List.map_cons, List.map_cons,
            getD_wiresFrom pZ.1 w2 wU0 (by rw [lw2]; exact hwU0_lt), hU0,
            getD_wiresFrom pZ.1 w2 wV0 (by rw [lw2]; exact hwV0_lt), hV0, hZs,
            List.count_cons, List.count_cons, count_Z u v]
          have hRu := (u_part u).1; have hRv := (v_part v).1
          have hSdis := (u_part u).2; have hTdis := (v_part v).2
          simp only [MonoNF.eval]
          by_cases hu0 : u ∈ nf.S0
          · have hu_notR : u ∉ R_L := fun h => (hRu.1 h).1 hu0
            have hu_notRec : ¬ ∃ p ∈ nf.rects, u ∈ p.1 := hSdis hu0
            have hboth : ¬ ∃ p ∈ nf.rects, u ∈ p.1 ∧ v ∈ p.2 := fun ⟨p, hp, hu, _⟩ => hu_notRec ⟨p, hp, hu⟩
            by_cases hv0 : v ∈ nf.T0
            · have hv_notR : v ∉ R_R := fun h => (hRv.1 h).1 hv0
              have hv_notRec : ¬ ∃ p ∈ nf.rects, v ∈ p.2 := hTdis hv0
              simp [hu0, hv0, hu_notR, hv_notR, hu_notRec, hv_notRec, hboth]
            · by_cases hv_r : ∃ p ∈ nf.rects, v ∈ p.2
              · have hv_notR : v ∉ R_R := fun h => (hRv.1 h).2 hv_r
                simp [hu0, hv0, hu_notR, hv_notR, hu_notRec, hv_r, hboth]
              · have hv_R : v ∈ R_R := hRv.2 ⟨hv0, hv_r⟩
                simp [hu0, hv0, hu_notR, hv_R, hu_notRec, hv_r, hboth]
          · by_cases hv0 : v ∈ nf.T0
            · have hv_notR : v ∉ R_R := fun h => (hRv.1 h).1 hv0
              have hv_notRec : ¬ ∃ p ∈ nf.rects, v ∈ p.2 := hTdis hv0
              have hboth : ¬ ∃ p ∈ nf.rects, u ∈ p.1 ∧ v ∈ p.2 := fun ⟨p, hp, _, hv⟩ => hv_notRec ⟨p, hp, hv⟩
              by_cases hu_r : ∃ p ∈ nf.rects, u ∈ p.1
              · have hu_notR : u ∉ R_L := fun h => (hRu.1 h).2 hu_r
                simp [hu0, hv0, hu_notR, hv_notR, hu_r, hv_notRec, hboth]
              · have hu_R : u ∈ R_L := hRu.2 ⟨hu0, hu_r⟩
                simp [hu0, hv0, hu_R, hv_notR, hu_r, hv_notRec, hboth]
            · by_cases hhit : ∃ p ∈ nf.rects, u ∈ p.1 ∧ v ∈ p.2
              · have ⟨p, hp, hu, hv⟩ := hhit
                have hu_notR : u ∉ R_L := fun h => (hRu.1 h).2 ⟨p, hp, hu⟩
                have hv_notR : v ∉ R_R := fun h => (hRv.1 h).2 ⟨p, hp, hv⟩
                simp [hu0, hv0, hhit, hu_notR, hv_notR]
              · by_cases hu_r : ∃ p ∈ nf.rects, u ∈ p.1 <;> by_cases hv_r : ∃ p ∈ nf.rects, v ∈ p.2
                · simp [hu0, hv0, hhit, hu_r, hv_r]; omega
                · have hv_R : v ∈ R_R := hRv.2 ⟨hv0, hv_r⟩
                  simp [hu0, hv0, hhit, hu_r, hv_r, hv_R]
                · have hu_R : u ∈ R_L := hRu.2 ⟨hu0, hu_r⟩
                  simp [hu0, hv0, hhit, hu_r, hv_r, hu_R]
                · have hu_R : u ∈ R_L := hRu.2 ⟨hu0, hu_r⟩
                  have hv_R : v ∈ R_R := hRv.2 ⟨hv0, hv_r⟩
                  simp [hu0, hv0, hhit, hu_r, hv_r, hu_R, hv_R]

/-! ### Part 6: Handling the `n = 2, m = 2` monotone edge case -/

theorem two_by_two_mono (A : Fin 2 → Fin 2 → Bool)
    (hrow : ∀ u u' : Fin 2, (∀ v : Fin 2, A u v = A u' v) → u = u')
    (hcol : ∀ v v' : Fin 2, (∀ u : Fin 2, A u v = A u v') → v = v')
    (C : Circuit) (hM : Monotone2 C) (hs : C.size ≤ 2) (hR : Represents A C) :
    RepSizeAtMost A 1 := by
  -- Either `A` has a 1-gate representation (all 8 non-diagonal 2x2 matrices with distinct rows/cols),
  -- or `A` is `I_2` / `¬I_2`, which cannot be computed by a 2-gate monotone circuit!
  have hcheck : (∃ i j : Fin 2, ∀ u v : Fin 2, A u v = decide (u = i ∧ v = j)) ∨
                (∃ i j : Fin 2, ∀ u v : Fin 2, A u v = decide (u = i ∨ v = j)) ∨
                (∀ u v : Fin 2, A u v = decide (u = v)) ∨
                (∀ u v : Fin 2, A u v = decide (u ≠ v)) := by
    -- Finite case split over the 4 bits of `A`!
    cases h00 : A 0 0 <;> cases h01 : A 0 1 <;> cases h10 : A 1 0 <;> cases h11 : A 1 1
    · exfalso; exact absurd (hrow 0 1 (fun v => by fin_cases v <;> simp [h00, h01, h10, h11])) (by decide)
    · left; exact ⟨1, 1, fun u v => by fin_cases u <;> fin_cases v <;> simp [h00, h01, h10, h11]⟩
    · left; exact ⟨1, 0, fun u v => by fin_cases u <;> fin_cases v <;> simp [h00, h01, h10, h11]⟩
    · exfalso; exact absurd (hcol 0 1 (fun u => by fin_cases u <;> simp [h00, h01, h10, h11])) (by decide)
    · left; exact ⟨0, 1, fun u v => by fin_cases u <;> fin_cases v <;> simp [h00, h01, h10, h11]⟩
    · exfalso; exact absurd (hrow 0 1 (fun v => by fin_cases v <;> simp [h00, h01, h10, h11])) (by decide)
    · right; right; right; exact fun u v => by fin_cases u <;> fin_cases v <;> simp [h00, h01, h10, h11]
    · right; left; exact ⟨1, 1, fun u v => by fin_cases u <;> fin_cases v <;> simp [h00, h01, h10, h11]⟩
    · left; exact ⟨0, 0, fun u v => by fin_cases u <;> fin_cases v <;> simp [h00, h01, h10, h11]⟩
    · right; right; left; exact fun u v => by fin_cases u <;> fin_cases v <;> simp [h00, h01, h10, h11]
    · exfalso; exact absurd (hrow 0 1 (fun v => by fin_cases v <;> simp [h00, h01, h10, h11])) (by decide)
    · right; left; exact ⟨1, 0, fun u v => by fin_cases u <;> fin_cases v <;> simp [h00, h01, h10, h11]⟩
    · exfalso; exact absurd (hcol 0 1 (fun u => by fin_cases u <;> simp [h00, h01, h10, h11])) (by decide)
    · right; left; exact ⟨0, 1, fun u v => by fin_cases u <;> fin_cases v <;> simp [h00, h01, h10, h11]⟩
    · right; left; exact ⟨0, 0, fun u v => by fin_cases u <;> fin_cases v <;> simp [h00, h01, h10, h11]⟩
    · exfalso; exact absurd (hrow 0 1 (fun v => by fin_cases v <;> simp [h00, h01, h10, h11])) (by decide)
  rcases hcheck with ⟨i, j, hA⟩ | ⟨i, j, hA⟩ | hA | hA
  · refine ⟨⟨[⟨GateOp.and, [i.val, 2 + j.val]⟩], 4⟩, fun g hg => by simp at hg; subst hg; exact ⟨by simp, by simp⟩,
      by simp [Circuit.size], fun u v => ?_⟩
    rw [hA u v]; fin_cases i <;> fin_cases j <;> fin_cases u <;> fin_cases v <;> decide
  · refine ⟨⟨[⟨GateOp.or, [i.val, 2 + j.val]⟩], 4⟩, fun g hg => by simp at hg; subst hg; exact ⟨by simp, by simp⟩,
      by simp [Circuit.size], fun u v => ?_⟩
    rw [hA u v]; fin_cases i <;> fin_cases j <;> fin_cases u <;> fin_cases v <;> decide
  · -- Contradiction: `I_2` needs `≥ 3` monotone gates because all 4 inputs must be in `N` (`|N| ≤ 3`)!
    exfalso
    obtain ⟨N, hcN, hdN, _⟩ := back_mono C.output C.gates hM 4
    have hmono : ∀ (x y : ℕ → Bool), (∀ i, x i = true → y i = true) →
        run C.gates 4 x C.output = true → run C.gates 4 y C.output = true := by
      have aux : ∀ (gs : List Gate) (t : ℕ) (x y : ℕ → Bool), (∀ g ∈ gs, GateMono g) →
          (∀ i, x i = true → y i = true) → ∀ o, run gs t x o = true → run gs t y o = true := by
        intro gs; induction gs with
        | nil => intro t x y _ hxy o h; exact hxy o h
        | cons g gs ih =>
          intro t x y hg hxy o
          apply ih (t + 1) _ _ (fun d hd => hg d (List.mem_cons_of_mem _ hd))
          intro i hi
          by_cases hit : i = t
          · subst hit; simp only [Function.update_self] at hi ⊢
            have hop := (hg g (by simp)).1
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
            rcases hop with hop | hop <;> rw [hop] at hi ⊢
            · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id] at hi ⊢
              exact fun a ha => hxy a (hi a ha)
            · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id] at hi ⊢
              obtain ⟨a, ha, hva⟩ := hi; exact ⟨a, ha, hxy a hva⟩
          · simp only [Function.update_of_ne hit] at hi ⊢; exact hxy i hi
      exact fun x y hxy => aux C.gates 4 x y hM hxy C.output
    have hev : ∀ u v : Fin 2, run C.gates 4 (oneEachFn u v) C.output = decide (u = v) := by
      intro u v
      have h1 := hR u v
      rw [hA u v] at h1
      rw [← h1]
      change run C.gates 4 (oneEachFn u v) C.output = (wiresFrom C.gates (oneEach u v)).getD C.output false
      rw [run_eq, oneEach_len]
      congr 2; funext i; exact (oneEach_getD u v i).symm
    have hmem : ∀ k ∈ ({0, 1, 2, 3} : Finset ℕ), k ∈ N := by
      intro k hk
      by_contra hkn
      have kill : ∀ (u v u' v' : Fin 2), u = v → u' ≠ v' →
          (∀ i, i ≠ k → oneEachFn u v i = true → oneEachFn u' v' i = true) → False := by
        intro u v u' v' h1 h2 hle
        have htrue : run C.gates 4 (oneEachFn u v) C.output = true := by rw [hev, h1]; simp
        have hdrop : run C.gates 4 (Function.update (oneEachFn u v) k false) C.output = true := by
          rw [← htrue]
          exact hdN _ _ fun i hi => Function.update_of_ne (fun (e : i = k) => hkn (e ▸ hi)) _ _
        have hfalse := hmono _ (oneEachFn u' v') (fun i hi => by
          by_cases hik : i = k
          · subst hik; simp at hi
          · rw [Function.update_of_ne hik] at hi; exact hle i hik hi) hdrop
        rw [hev] at hfalse
        exact absurd (of_decide_eq_true hfalse) h2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl | rfl
      · exact kill 0 0 1 0 rfl (by decide) (fun i hik hi => by simp [oneEachFn] at hi ⊢; omega)
      · exact kill 1 1 0 1 rfl (by decide) (fun i hik hi => by simp [oneEachFn] at hi ⊢; omega)
      · exact kill 0 0 0 1 rfl (by decide) (fun i hik hi => by simp [oneEachFn] at hi ⊢; omega)
      · exact kill 1 1 1 0 rfl (by decide) (fun i hik hi => by simp [oneEachFn] at hi ⊢; omega)
    have h4 : 4 ≤ N.card := by
      have := Finset.card_le_card hmem; simpa using this
    have : C.gates.length ≤ 2 := hs
    omega
  · -- Contradiction: `¬I_2` also needs `≥ 3` monotone gates (identical argument)!
    exfalso
    obtain ⟨N, hcN, hdN, _⟩ := back_mono C.output C.gates hM 4
    have hmono : ∀ (x y : ℕ → Bool), (∀ i, x i = true → y i = true) →
        run C.gates 4 x C.output = true → run C.gates 4 y C.output = true := by
      have aux : ∀ (gs : List Gate) (t : ℕ) (x y : ℕ → Bool), (∀ g ∈ gs, GateMono g) →
          (∀ i, x i = true → y i = true) → ∀ o, run gs t x o = true → run gs t y o = true := by
        intro gs; induction gs with
        | nil => intro t x y _ hxy o h; exact hxy o h
        | cons g gs ih =>
          intro t x y hg hxy o
          apply ih (t + 1) _ _ (fun d hd => hg d (List.mem_cons_of_mem _ hd))
          intro i hi
          by_cases hit : i = t
          · subst hit; simp only [Function.update_self] at hi ⊢
            have hop := (hg g (by simp)).1
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
            rcases hop with hop | hop <;> rw [hop] at hi ⊢
            · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id] at hi ⊢
              exact fun a ha => hxy a (hi a ha)
            · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id] at hi ⊢
              obtain ⟨a, ha, hva⟩ := hi; exact ⟨a, ha, hxy a hva⟩
          · simp only [Function.update_of_ne hit] at hi ⊢; exact hxy i hi
      exact fun x y hxy => aux C.gates 4 x y hM hxy C.output
    have hev : ∀ u v : Fin 2, run C.gates 4 (oneEachFn u v) C.output = decide (u ≠ v) := by
      intro u v
      have h1 := hR u v
      rw [hA u v] at h1
      rw [← h1]
      change run C.gates 4 (oneEachFn u v) C.output = (wiresFrom C.gates (oneEach u v)).getD C.output false
      rw [run_eq, oneEach_len]
      congr 2; funext i; exact (oneEach_getD u v i).symm
    have hmem : ∀ k ∈ ({0, 1, 2, 3} : Finset ℕ), k ∈ N := by
      intro k hk
      by_contra hkn
      have kill : ∀ (u v u' v' : Fin 2), u ≠ v → u' = v' →
          (∀ i, i ≠ k → oneEachFn u v i = true → oneEachFn u' v' i = true) → False := by
        intro u v u' v' h1 h2 hle
        have htrue : run C.gates 4 (oneEachFn u v) C.output = true := by rw [hev]; simp [h1]
        have hdrop : run C.gates 4 (Function.update (oneEachFn u v) k false) C.output = true := by
          rw [← htrue]
          exact hdN _ _ fun i hi => Function.update_of_ne (fun (e : i = k) => hkn (e ▸ hi)) _ _
        have hfalse := hmono _ (oneEachFn u' v') (fun i hi => by
          by_cases hik : i = k
          · subst hik; simp at hi
          · rw [Function.update_of_ne hik] at hi; exact hle i hik hi) hdrop
        rw [hev, h2] at hfalse
        simp at hfalse
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl | rfl
      · exact kill 0 1 1 1 (by decide) rfl (fun i hik hi => by simp [oneEachFn] at hi ⊢; omega)
      · exact kill 1 0 0 0 (by decide) rfl (fun i hik hi => by simp [oneEachFn] at hi ⊢; omega)
      · exact kill 1 0 1 1 (by decide) rfl (fun i hik hi => by simp [oneEachFn] at hi ⊢; omega)
      · exact kill 0 1 0 0 (by decide) rfl (fun i hik hi => by simp [oneEachFn] at hi ⊢; omega)
    have h4 : 4 ≤ N.card := by
      have := Finset.card_le_card hmem; simpa using this
    have : C.gates.length ≤ 2 := hs
    omega

end PEqualNP.Outside.L_meta_25021_aux

open PEqualNP.Outside.L_meta_25021_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents in
theorem PEqualNP.Outside.L_meta_25021 : ∀ (n m : ℕ) (A : Fin n → Fin m → Bool), 2 ≤ n → 2 ≤ m → (∀ u u' : Fin n, (∀ v : Fin m, A u v = A u' v) → u = u') → (∀ v v' : Fin m, (∀ u : Fin n, A u v = A u v') → v = v') → (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ n + m - 2 ∧ PEqualNP.Represents.Represents A C) → PEqualNP.Represents.RepSizeAtMost A (2 * (n + m) - 7) := by
  classical
  intro n m A hn hm hrow hcol ⟨C, hC, hs, hR⟩
  have hCeval : ∀ u v, run C.gates (n + m) (oneEachFn u v) C.output = A u v := by
    intro u v
    have := hR u v
    rw [← this]
    change run C.gates (n + m) (oneEachFn u v) C.output = (wiresFrom C.gates (oneEach u v)).getD C.output false
    rw [run_eq, oneEach_len]
    congr 2; funext i; exact (oneEach_getD u v i).symm
  rcases back_aon C.output C.gates hC (n + m) with ⟨gs', hgm', hlen', heq'⟩ | ⟨N, hcN, hdN, hfN⟩
  · -- Case 1: Equivalent plain `Monotone2` circuit `⟨gs', C.output⟩` of size `≤ n + m - 2`!
    have hC' : Monotone2 ⟨gs', C.output⟩ := hgm'
    have hR' : Represents A ⟨gs', C.output⟩ := by
      intro u v
      change (wiresFrom gs' (oneEach u v)).getD C.output false = A u v
      rw [run_eq, oneEach_len]
      have hfn : (fun j => (oneEach u v).getD j false) = oneEachFn u v := by
        funext i; exact oneEach_getD u v i
      rw [hfn, heq', hCeval]
    by_cases h4 : n = 2 ∧ m = 2
    · obtain ⟨rfl, rfl⟩ := h4
      have hCsz : C.gates.length ≤ 2 := hs
      exact two_by_two_mono A hrow hcol ⟨gs', C.output⟩ hC' (by simp [Circuit.size]; omega) hR'
    · refine ⟨⟨gs', C.output⟩, hC', ?_, hR'⟩
      have : C.gates.length ≤ n + m - 2 := hs
      simp only [Circuit.size]
      omega
  · -- Case 2: `|N| ≤ C.size ≤ n + m - 2`; prove `|N| = C.size = n + m - 2` and extract 1-NOT read-once `f`!
    -- At most one row `u` is not in `rowVars n N`, and at most one col `v` is not in `colVars n m N`!
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
    -- Every element of `N` is `< n + m`!
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
    -- Extract the read-once 1-NOT formula `f`!
    obtain ⟨f, fro, fn1, fvs, fev⟩ := hfN hNeq
    -- Split `f = K[z := ¬H]` using a fresh wire `z = n + m` (which is `∉ N = f.vars`)!
    have hz_not : n + m ∉ f.vars := fun h => by have := hN_lt (n + m) (fvs ▸ h); omega
    obtain ⟨K, H, Kro, Hro, Kn0, Hn0, Hsub, Ksub, hbins, hsplit⟩ := split_unique_not (n + m) f fro fn1 hz_not
    have hHlt : ∀ i ∈ H.vars, i < n + m := fun i hi => hN_lt i (fvs ▸ Hsub hi)
    -- Obtain normal form of `H`!
    obtain ⟨nf, hval, hnf_ev⟩ := mono_normal_form n m H Hro Hn0 hHlt
    set X := rowVars n H.vars
    set Y := colVars n m H.vars
    have hXY_sum : X.card + Y.card = H.vars.card := card_row_add_col n m H.vars hHlt
    have hXsub : X ⊆ rowVars n N := fun u hu => Finset.mem_filter.2 ⟨Finset.mem_univ _, fvs ▸ Hsub (Finset.mem_filter.1 hu).2⟩
    have hYsub : Y ⊆ colVars n m N := fun v hv => Finset.mem_filter.2 ⟨Finset.mem_univ _, fvs ▸ Hsub (Finset.mem_filter.1 hv).2⟩
    have hXlt : X.card < n := by have := Finset.card_le_card hXsub; omega
    have hYlt : Y.card < m := by have := Finset.card_le_card hYsub; omega
    have hHcard : H.vars.card = H.bins + 1 := Form.vars_card_of_readOnce Hro
    have hFcard : f.vars.card = f.bins + 1 := Form.vars_card_of_readOnce fro
    have hfcardN : f.vars.card = n + m - 2 := by rw [fvs, hNnm]
    have hXY_pos : 1 ≤ X.card + Y.card := by omega
    have hempty : nf.S0 = ∅ → nf.T0 = ∅ → nf.rects = [] → 2 ≤ X.card + Y.card := by
      intro h1 h2 h3
      by_contra hlt2
      have hH0 : H.bins = 0 := by omega
      have hHvar : ∃ w, H = .var w := by
        cases H with
        | var w => exact ⟨w, rfl⟩
        | not _ => simp [Form.nots] at Hn0
        | and _ _ => simp [Form.bins] at hH0
        | or _ _ => simp [Form.bins] at hH0
      obtain ⟨w, hHw⟩ := hHvar
      have hwlt : w < n + m := hHlt w (by rw [hHw]; simp [Form.vars])
      by_cases hw : w < n
      · have he := hnf_ev ⟨w, hw⟩ ⟨0, by omega⟩
        rw [hHw] at he
        simp [Form.eval, oneEachFn, MonoNF.eval, h1, h2, h3] at he
      · have he := hnf_ev ⟨0, by omega⟩ ⟨w - n, by omega⟩
        rw [hHw] at he
        simp [Form.eval, oneEachFn, MonoNF.eval, h1, h2, h3, show n + (w - n) = w by omega] at he
    -- Build monotone circuit `(gsM, owM)` computing `!(nf.eval u v)` with `gsM.length + 5 ≤ n + m + X.card + Y.card`!
    obtain ⟨gsM, owM, hmM, hlenM, howM, hevM⟩ := build_not_nf n m hn hm X Y hXlt hYlt hXY_pos nf hval hempty
    -- Now rename wire `n + m` in `K` to `owM`, and compile `K` on top of `gsM`!
    have hK'n0 : (K.subst (n + m) (.var owM)).nots = 0 := by
      clear * - Kn0
      induction K with
      | var w => by_cases h : w = n + m <;> simp [Form.subst, Form.nots, h]
      | not _ _ => simp [Form.nots] at Kn0
      | and l r ihl ihr => simp [Form.nots] at Kn0; simp [Form.subst, Form.nots, ihl Kn0.1, ihr Kn0.2]
      | or l r ihl ihr => simp [Form.nots] at Kn0; simp [Form.subst, Form.nots, ihl Kn0.1, ihr Kn0.2]
    have hK'bins : (K.subst (n + m) (.var owM)).bins = K.bins := by
      clear * -
      induction K with
      | var w => by_cases h : w = n + m <;> simp [Form.subst, Form.bins, h]
      | not f ih => simp [Form.subst, Form.bins, ih]
      | and l r ihl ihr => simp [Form.subst, Form.bins, ihl, ihr]
      | or l r ihl ihr => simp [Form.subst, Form.bins, ihl, ihr]
    have hK'lt : ∀ i ∈ (K.subst (n + m) (.var owM)).vars, i < n + m + gsM.length := by
      intro i hi
      have : i = owM ∨ i ∈ K.vars := by
        clear * - hi
        induction K with
        | var w =>
          by_cases h : w = n + m
          · simp [Form.subst, Form.vars, h] at hi; exact Or.inl hi
          · simp [Form.subst, Form.vars, h] at hi; exact Or.inr (by simp [Form.vars, hi])
        | not f ih => exact ih hi
        | and l r ihl ihr =>
          simp only [Form.subst, Form.vars, Finset.mem_union] at hi ⊢
          rcases hi with hi | hi
          · rcases ihl hi with rfl | h; exact Or.inl rfl; exact Or.inr (Or.inl h)
          · rcases ihr hi with rfl | h; exact Or.inl rfl; exact Or.inr (Or.inr h)
        | or l r ihl ihr =>
          simp only [Form.subst, Form.vars, Finset.mem_union] at hi ⊢
          rcases hi with hi | hi
          · rcases ihl hi with rfl | h; exact Or.inl rfl; exact Or.inr (Or.inl h)
          · rcases ihr hi with rfl | h; exact Or.inl rfl; exact Or.inr (Or.inr h)
      rcases this with rfl | hiK
      · exact howM
      · have := Ksub hiK
        simp only [Finset.mem_insert] at this
        rcases this with rfl | hif
        · by_cases hEq : owM = n + m
          · omega
          · exfalso
            have hnot : n + m ∉ (K.subst (n + m) (.var owM)).vars := by
              clear * - hEq
              induction K with
              | var w =>
                by_cases h : w = n + m
                · simp [Form.subst, Form.vars, h, Ne.symm hEq]
                · simp [Form.subst, Form.vars, h]; omega
              | not f ih => exact ih
              | and l r ihl ihr => simp [Form.subst, Form.vars, ihl, ihr]
              | or l r ihl ihr => simp [Form.subst, Form.vars, ihl, ihr]
            exact hnot hi
        · have := hN_lt i (fvs ▸ hif); omega
    set pK := compileMono (n + m + gsM.length) (K.subst (n + m) (.var owM))
    obtain ⟨hmK, hlK, _, hevK⟩ :
        (∀ g ∈ pK.1, GateMono g) ∧ pK.1.length = (K.subst (n + m) (.var owM)).bins ∧
        pK.2 < n + m + gsM.length + pK.1.length ∧
        ∀ w : List Bool, w.length = n + m + gsM.length →
          (wiresFrom pK.1 w).getD pK.2 false = (K.subst (n + m) (.var owM)).eval (fun i => w.getD i false) :=
      compileMono_props (K.subst (n + m) (.var owM)) (n + m + gsM.length) hK'n0 hK'lt
    refine ⟨⟨gsM ++ pK.1, pK.2⟩, ?_, ?_, fun u v => ?_⟩
    · intro g hg
      rcases List.mem_append.1 hg with hg | hg
      · exact hmM g hg
      · exact hmK g hg
    · simp only [Circuit.size, List.length_append, hlK, hK'bins]
      omega
    · change (wiresFrom (gsM ++ pK.1) (oneEach u v)).getD pK.2 false = A u v
      rw [wiresFrom_append, hevK (wiresFrom gsM (oneEach u v)) (by rw [length_wiresFrom, oneEach_len])]
      rw [Form.eval_subst, ← hCeval u v, fev, hsplit]
      refine Form.eval_congr K _ _ fun i hi => ?_
      by_cases hiz : i = n + m
      · subst hiz
        simp only [Function.update_self, Form.eval, hevM u v, hnf_ev u v]
      · simp only [Function.update_of_ne hiz]
        have hiK : i ∈ f.vars := by
          have := Ksub hi; simp only [Finset.mem_insert] at this
          rcases this with rfl | h; exact (hiz rfl).elim; exact h
        have hilt : i < n + m := hN_lt i (fvs ▸ hiK)
        rw [getD_wiresFrom gsM (oneEach u v) i (by rw [oneEach_len]; exact hilt)]
        exact oneEach_getD u v i
