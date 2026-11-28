import PEqualNP.Defs
import Mathlib

namespace PEqualNP.Outside.L_meta_53190_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover


/-! ## Running gates -/

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = run C.gates x := rfl

theorem run_append (a b : List Gate) (w : List Bool) : run (a ++ b) w = run b (run a w) := by
  unfold run; rw [List.foldl_append]

theorem run_singleton (g : Gate) (w : List Bool) :
    run [g] w = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := rfl

theorem run_prefix (gs : List Gate) :
    ∀ w : List Bool, ∃ t, run gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [-Fin.natAdd_eq_addNat, run]⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, ?_⟩
    · rw [show g :: gs = [g] ++ gs from rfl, run_append, run_singleton, ht]; simp [-Fin.natAdd_eq_addNat]
    · simp [-Fin.natAdd_eq_addNat, hl]

theorem run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := run_prefix gs w
  rw [ht, List.length_append, hl]

theorem getD_run (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := run_prefix gs w
  rw [ht]; simp [-Fin.natAdd_eq_addNat, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem eval_or2 (a b : Bool) : GateOp.eval GateOp.or [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

theorem eval_and2 (a b : Bool) : GateOp.eval GateOp.and [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

/-! ## Monotonicity of AND/OR circuits -/

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (is : List ℕ)
    (u v : ℕ → Bool) (h : ∀ i, u i = true → v i = true) :
    op.eval (is.map u) = true → op.eval (is.map v) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro H a ha
    obtain ⟨i, hi, rfl⟩ := ha
    exact h i (H (u i) ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨a, ⟨i, hi, rfl⟩, ha⟩
    exact ⟨v i, ⟨i, hi, rfl⟩, h i ha⟩

theorem run_mono (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ x y : List Bool, x.length = y.length →
      (∀ i, x.getD i false = true → y.getD i false = true) →
      ∀ i, (run gs x).getD i false = true → (run gs y).getD i false = true := by
  induction gs with
  | nil => intro x y _ h; exact h
  | cons g gs ih =>
    intro x y hl h
    have hg' := hg g (by simp [-Fin.natAdd_eq_addNat])
    have key := ih (fun g' hg'' => hg g' (by simp [-Fin.natAdd_eq_addNat, hg'']))
      (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])
      (y ++ [g.op.eval (g.inputs.map fun i => y.getD i false)]) (by simp [-Fin.natAdd_eq_addNat, hl]) ?_
    · exact key
    · intro i hi
      by_cases h1 : i < x.length
      · rw [List.getD_append _ _ _ _ h1] at hi
        rw [List.getD_append _ _ _ _ (hl ▸ h1)]
        exact h i hi
      · by_cases h2 : i = x.length
        · subst h2
          simp only [List.getD_eq_getElem?_getD] at hi ⊢
          rw [List.getElem?_append_right (le_refl _)] at hi
          rw [hl, List.getElem?_append_right (le_refl _)]
          simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some] at hi ⊢
          exact eval_mono g.op hg' g.inputs _ _ h hi
        · exfalso
          have : x.length + 1 ≤ i := by omega
          simp only [List.getD_eq_getElem?_getD] at hi
          rw [List.getElem?_eq_none (by simp [-Fin.natAdd_eq_addNat]; omega)] at hi
          simp [-Fin.natAdd_eq_addNat] at hi

theorem wires_mono (C : Circuit) (hC : Monotone2 C) (x y : List Bool) (hl : x.length = y.length)
    (h : ∀ i, x.getD i false = true → y.getD i false = true) (i : ℕ) :
    (C.wires x).getD i false = true → (C.wires y).getD i false = true := by
  rw [wires_eq, wires_eq]
  refine run_mono C.gates ?_ x y hl h i
  intro g hg
  have := (hC g hg).1
  simpa [-Fin.natAdd_eq_addNat] using this

/-! ## Monotone nets -/

structure Net (n : Nat) where
  gates : List Gate
  mono : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2
  back : ∀ j (hj : j < gates.length), ∀ i ∈ gates[j].inputs, i < n + j

def Net.empty (n : Nat) : Net n := ⟨[], by simp, by simp⟩

variable {X J : Type} {n : Nat}

def Net.has (p : Net n) (raw : X → List Bool) (f : X → Bool) : Prop :=
  ∃ i, i < n + p.gates.length ∧ ∀ x, (run p.gates (raw x)).getD i false = f x

def Grow (raw : X → List Bool) (p q : Net n) (size : Nat) : Prop :=
  (∀ f, p.has raw f → q.has raw f) ∧ q.gates.length ≤ p.gates.length + size

theorem Grow.refl (raw : X → List Bool) (p : Net n) : Grow raw p p 0 :=
  ⟨fun _ h => h, by simp⟩

theorem Grow.trans {raw : X → List Bool} {p q r : Net n} {a b : Nat}
    (pq : Grow raw p q a) (qr : Grow raw q r b) : Grow raw p r (a + b) :=
  ⟨fun f h => qr.1 f (pq.1 f h), by have := pq.2; have := qr.2; omega⟩

theorem Grow.weaken {raw : X → List Bool} {p q : Net n} {a b : Nat}
    (g : Grow raw p q a) (h : a ≤ b) : Grow raw p q b := ⟨g.1, by have := g.2; omega⟩

theorem Net.has_congr {raw : X → List Bool} {p : Net n} {f g : X → Bool} (h : p.has raw f)
    (e : ∀ x, f x = g x) : p.has raw g := by
  obtain ⟨i, hi, hr⟩ := h
  exact ⟨i, hi, fun x => (hr x).trans (e x)⟩

def Net.extend (p : Net n) (g : Gate)
    (ops : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (ok : ∀ i ∈ g.inputs, i < n + p.gates.length) : Net n where
  gates := p.gates ++ [g]
  mono := by
    intro v hv
    rcases List.mem_append.mp hv with old | last
    · exact p.mono v old
    · exact (List.mem_singleton.mp last) ▸ ops
  back := by
    intro j hj i hi
    by_cases h : j < p.gates.length
    · rw [List.getElem_append_left h] at hi
      exact p.back j h i hi
    · have len : j = p.gates.length := by simp [-Fin.natAdd_eq_addNat] at hj; omega
      subst len
      simp [-Fin.natAdd_eq_addNat] at hi
      exact ok i hi

theorem Net.emit {raw : X → List Bool} (width : ∀ x, (raw x).length = n)
    (p : Net n) (g : Gate)
    (ops : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (ok : ∀ i ∈ g.inputs, i < n + p.gates.length) :
    ∃ q, Grow raw p q 1 ∧
      q.has raw (fun x => g.op.eval (g.inputs.map (fun i => (run p.gates (raw x)).getD i false))) := by
  let q := p.extend g ops ok
  have len (x : X) : (run p.gates (raw x)).length = n + p.gates.length := by
    rw [run_length, width]
  refine ⟨q, ⟨?_, by simp [-Fin.natAdd_eq_addNat, q, Net.extend]⟩, n + p.gates.length, by simp [-Fin.natAdd_eq_addNat, q, Net.extend], ?_⟩
  · rintro f ⟨i, hi, read⟩
    refine ⟨i, by simp [-Fin.natAdd_eq_addNat, q, Net.extend]; omega, ?_⟩
    intro x
    change (run (p.gates ++ [g]) (raw x)).getD i false = _
    rw [run_append, run_singleton, List.getD_append _ _ _ _ ((len x).symm ▸ hi), read]
  · intro x
    change (run (p.gates ++ [g]) (raw x)).getD (n + p.gates.length) false = _
    rw [run_append, run_singleton, ← len x]; simp [-Fin.natAdd_eq_addNat]

theorem Net.and2 {raw : X → List Bool} (width : ∀ x, (raw x).length = n)
    (p : Net n) (a b c : X → Bool) (ha : p.has raw a) (hb : p.has raw b)
    (e : ∀ x, (a x && b x) = c x) :
    ∃ q, Grow raw p q 1 ∧ q.has raw c := by
  obtain ⟨i, hi, readI⟩ := ha
  obtain ⟨j, hj, readJ⟩ := hb
  let g : Gate := ⟨.and, [i, j]⟩
  obtain ⟨q, grow, w⟩ := p.emit width g (by simp [-Fin.natAdd_eq_addNat, g]) (by simp [-Fin.natAdd_eq_addNat, g, hi, hj])
  refine ⟨q, grow, Net.has_congr w ?_⟩
  intro x
  simp only [g, List.map_cons, List.map_nil, readI, readJ, eval_and2]
  exact e x

theorem Net.or2 {raw : X → List Bool} (width : ∀ x, (raw x).length = n)
    (p : Net n) (a b c : X → Bool) (ha : p.has raw a) (hb : p.has raw b)
    (e : ∀ x, (a x || b x) = c x) :
    ∃ q, Grow raw p q 1 ∧ q.has raw c := by
  obtain ⟨i, hi, readI⟩ := ha
  obtain ⟨j, hj, readJ⟩ := hb
  let g : Gate := ⟨.or, [i, j]⟩
  obtain ⟨q, grow, w⟩ := p.emit width g (by simp [-Fin.natAdd_eq_addNat, g]) (by simp [-Fin.natAdd_eq_addNat, g, hi, hj])
  refine ⟨q, grow, Net.has_congr w ?_⟩
  intro x
  simp only [g, List.map_cons, List.map_nil, readI, readJ, eval_or2]
  exact e x

theorem Net.anyList {raw : X → List Bool} (width : ∀ x, (raw x).length = n) (p : Net n)
    (zero : p.has raw (fun _ => false)) (l : List J) (f : J → X → Bool)
    (known : ∀ j ∈ l, p.has raw (f j)) :
    ∃ q, Grow raw p q l.length ∧ q.has raw (fun x => l.any (fun j => f j x)) := by
  induction l with
  | nil => exact ⟨p, Grow.refl raw p, Net.has_congr zero (fun _ => rfl)⟩
  | cons j l ih =>
    obtain ⟨q, gq, old⟩ := ih (fun i hi => known i (by simp [-Fin.natAdd_eq_addNat, hi]))
    obtain ⟨r, gr, ans⟩ := Net.or2 width q _ _ (fun x => (j :: l).any (fun j => f j x))
      (gq.1 _ (known j (by simp [-Fin.natAdd_eq_addNat]))) old (fun x => by simp [-Fin.natAdd_eq_addNat, List.any_cons])
    exact ⟨r, (gq.trans gr).weaken (by simp [-Fin.natAdd_eq_addNat]), ans⟩

theorem Net.allList {raw : X → List Bool} (width : ∀ x, (raw x).length = n) (p : Net n)
    (one : p.has raw (fun _ => true)) (l : List J) (f : J → X → Bool)
    (known : ∀ j ∈ l, p.has raw (f j)) :
    ∃ q, Grow raw p q l.length ∧ q.has raw (fun x => l.all (fun j => f j x)) := by
  induction l with
  | nil => exact ⟨p, Grow.refl raw p, Net.has_congr one (fun _ => rfl)⟩
  | cons j l ih =>
    obtain ⟨q, gq, old⟩ := ih (fun i hi => known i (by simp [-Fin.natAdd_eq_addNat, hi]))
    obtain ⟨r, gr, ans⟩ := Net.and2 width q _ _ (fun x => (j :: l).all (fun j => f j x))
      (gq.1 _ (known j (by simp [-Fin.natAdd_eq_addNat]))) old (fun x => by simp [-Fin.natAdd_eq_addNat, List.all_cons])
    exact ⟨r, (gq.trans gr).weaken (by simp [-Fin.natAdd_eq_addNat]), ans⟩

/-- Sequential building with a cost per item. -/
theorem Net.foldCost {raw : X → List Bool} (fs : J → List (X → Bool)) (cost : J → ℕ)
    (step : ∀ j (q : Net n), ∃ r, Grow raw q r (cost j) ∧ ∀ f ∈ fs j, r.has raw f) :
    ∀ (l : List J) (p : Net n), ∃ r, Grow raw p r (l.map cost).sum ∧
      ∀ j ∈ l, ∀ f ∈ fs j, r.has raw f := by
  intro l
  induction l with
  | nil => intro p; exact ⟨p, Grow.refl raw p, by simp⟩
  | cons j l ih =>
    intro p
    obtain ⟨q, gq, old⟩ := ih p
    obtain ⟨r, gr, ans⟩ := step j q
    refine ⟨r, (gq.trans gr).weaken (by simp [-Fin.natAdd_eq_addNat]; omega), ?_⟩
    intro j' hj' f hf
    rcases List.mem_cons.mp hj' with rfl | h
    · exact ans f hf
    · exact gr.1 _ (old j' h f hf)

/-- Sequential building with no size control. -/
theorem Net.foldAny {raw : X → List Bool} (fs : J → X → Bool) (l : List J) (p : Net n)
    (step : ∀ j ∈ l, ∀ q : Net n, (∀ a, p.has raw a → q.has raw a) →
      ∃ r s, Grow raw q r s ∧ r.has raw (fs j)) :
    ∃ r s, Grow raw p r s ∧ ∀ j ∈ l, r.has raw (fs j) := by
  induction l with
  | nil => exact ⟨p, 0, Grow.refl raw p, by simp⟩
  | cons j l ih =>
    obtain ⟨q, s, gq, old⟩ := ih (fun i hi => step i (by simp [-Fin.natAdd_eq_addNat, hi]))
    obtain ⟨r, s', gr, ans⟩ := step j (by simp [-Fin.natAdd_eq_addNat]) q gq.1
    refine ⟨r, s + s', gq.trans gr, ?_⟩
    intro j' hj'
    rcases List.mem_cons.mp hj' with rfl | h
    · exact ans
    · exact gr.1 _ (old j' h)

/-! ## From nets to the circuit requirement -/

def NeedOK {W : Type} (L : List (W → Bool)) (Z : Finset W) (need : Finset (W → Bool)) (p : ℕ) :
    Prop :=
  ∃ C : Circuit, Monotone2 C ∧ ReadsBack L.length C ∧ C.output < L.length + C.size ∧
    C.size ≤ p ∧ ∀ f ∈ need, ∃ j < L.length + C.size, ∀ x ∈ Z,
      (C.wires (L.map (fun g => g x))).getD j false = f x

theorem NeedOK.weaken {W : Type} {L : List (W → Bool)} {Z : Finset W} {need : Finset (W → Bool)}
    {p q : ℕ} (h : NeedOK L Z need p) (hpq : p ≤ q) : NeedOK L Z need q := by
  obtain ⟨C, h1, h2, h3, h4, h5⟩ := h
  exact ⟨C, h1, h2, h3, h4.trans hpq, h5⟩

theorem inHas {W : Type} (L : List (W → Bool)) (Z : Finset W) (p : Net L.length) (g : W → Bool)
    (hg : g ∈ L) :
    p.has (fun x : {x // x ∈ Z} => L.map (fun g => g x.1)) (fun x => g x.1) := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
  refine ⟨k, by omega, ?_⟩
  intro x
  rw [getD_run _ _ _ (by simp [-Fin.natAdd_eq_addNat, hk])]
  simp [-Fin.natAdd_eq_addNat, List.getD_eq_getElem?_getD, hk]

theorem netNeedOK {W : Type} (L : List (W → Bool)) (Z : Finset W) (need : Finset (W → Bool))
    (p : ℕ) (hL : 0 < L.length) (q : Net L.length) (hq : q.gates.length ≤ p)
    (hneed : ∀ f ∈ need, q.has (fun x : {x // x ∈ Z} => L.map (fun g => g x.1)) (fun x => f x.1)) :
    NeedOK L Z need p := by
  refine ⟨⟨q.gates, 0⟩, ?_, ?_, ?_, hq, ?_⟩
  · intro g hg
    exact q.mono g hg
  · intro j hj i hi
    exact q.back j hj i (by simpa [-Fin.natAdd_eq_addNat, gateAt, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hj] using hi)
  · show 0 < L.length + q.gates.length
    omega
  · intro f hf
    obtain ⟨i, hi, hr⟩ := hneed f hf
    exact ⟨i, hi, fun x hx => hr ⟨x, hx⟩⟩

/-! ## The set system bound -/

theorem setsys {T : Type} [Fintype T] [DecidableEq T] (m : ℕ) (hm : 0 < m)
    (U V : Fin m → Finset T)
    (hdisj : ∀ i, Disjoint (U i) (V i)) (hcov : ∀ i, U i ∪ V i ≠ Finset.univ)
    (hU : ∀ i, (U i).Nonempty) (hV : ∀ i, (V i).Nonempty)
    (hUU : ∀ i j, U i = U j → i = j) (hVV : ∀ i j, V i = V j → i = j)
    (hUV : ∀ i j, U i ≠ V j) :
    2 * m + 2 + (Fintype.card T).choose (Fintype.card T - Fintype.card T / 2) ≤
      2 ^ Fintype.card T := by
  set h := Fintype.card T with hh
  set ℓ := h - h / 2 with hℓ
  let atom : Fin m × Bool → Finset T := fun ι => if ι.2 then U ι.1 else V ι.1
  let part : Fin m × Bool → Finset T := fun ι => if ι.2 then V ι.1 else U ι.1
  have sizes : ∀ ι, (atom ι).card + (part ι).card + 1 ≤ h ∧ 1 ≤ (atom ι).card ∧
      1 ≤ (part ι).card := by
    rintro ⟨i, s⟩
    have hd := hdisj i
    have hc := hcov i
    have hu := (hU i).card_pos
    have hv := (hV i).card_pos
    have hlt : (U i ∪ V i).card < h := by
      rw [hh, ← Finset.card_univ]
      exact Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hc)
    rw [Finset.card_union_of_disjoint hd] at hlt
    cases s <;> simp only [atom, part, Bool.false_eq_true, ite_true, ite_false] <;> omega
  have atom_inj : ∀ ι κ, atom ι = atom κ → ι = κ := by
    rintro ⟨i, s⟩ ⟨j, t⟩ e
    cases s <;> cases t <;> simp only [atom, ite_true, ite_false, Bool.false_eq_true] at e
    · rw [hVV i j e]
    · exact absurd e.symm (hUV j i)
    · exact absurd e (hUV i j)
    · rw [hUU i j e]
  have part_eq : ∀ ι : Fin m × Bool, part ι = atom (ι.1, !ι.2) := by
    rintro ⟨i, s⟩; cases s <;> rfl
  let φ : Fin m × Bool → Finset T := fun ι =>
    if (atom ι).card ≤ (part ι).card then atom ι else (part ι)ᶜ
  have hφcard : ∀ ι, 1 ≤ (φ ι).card ∧ (φ ι).card + 1 ≤ h ∧ (φ ι).card ≠ ℓ ∧
      ((atom ι).card ≤ (part ι).card → 2 * (φ ι).card + 1 ≤ h) ∧
      (¬ (atom ι).card ≤ (part ι).card → h + 2 ≤ 2 * (φ ι).card) := by
    intro ι
    obtain ⟨s1, s2, s3⟩ := sizes ι
    by_cases c : (atom ι).card ≤ (part ι).card
    · have e : φ ι = atom ι := by simp only [φ]; rw [ite_eq_left_iff]; intro h'; exact absurd c h'
      rw [e]
      refine ⟨s2, by omega, by omega, fun _ => by omega, fun h' => absurd c h'⟩
    · have e : φ ι = (part ι)ᶜ := by simp only [φ]; rw [ite_eq_right_iff]; intro h'; exact absurd h' c
      rw [e, Finset.card_compl, ← hh]
      refine ⟨by omega, by omega, by omega, fun h' => absurd h' c, fun _ => by omega⟩
  have φinj : ∀ ι κ, φ ι = φ κ → ι = κ := by
    intro ι κ e
    have cι := hφcard ι
    have cκ := hφcard κ
    by_cases a : (atom ι).card ≤ (part ι).card <;> by_cases b : (atom κ).card ≤ (part κ).card
    · have e' : atom ι = atom κ := by simpa [-Fin.natAdd_eq_addNat, φ, a, b] using e
      exact atom_inj _ _ e'
    · have := cι.2.2.2.1 a
      have := cκ.2.2.2.2 b
      rw [e] at *
      omega
    · have := cι.2.2.2.2 a
      have := cκ.2.2.2.1 b
      rw [e] at *
      omega
    · have e' : (part ι)ᶜ = (part κ)ᶜ := by simpa [-Fin.natAdd_eq_addNat, φ, a, b] using e
      have e'' := compl_injective e'
      rw [part_eq, part_eq] at e''
      have := atom_inj _ _ e''
      rcases ι with ⟨i, s⟩
      rcases κ with ⟨j, t⟩
      simp only [Prod.mk.injEq, Bool.not_inj_iff] at this
      rw [this.1, this.2]
  let good : Finset T → Prop := fun Y => 1 ≤ Y.card ∧ Y.card + 1 ≤ h ∧ Y.card ≠ ℓ
  have h3 : 2 * m ≤ ((Finset.univ : Finset (Finset T)).filter good).card := by
    have : (Finset.univ : Finset (Fin m × Bool)).card = 2 * m := by
      simp [-Fin.natAdd_eq_addNat, Finset.card_univ, Fintype.card_prod, Fintype.card_bool]; ring
    rw [← this]
    apply Finset.card_le_card_of_injOn φ
    · intro ι _
      have := hφcard ι
      rw [Finset.mem_coe, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, this.1, this.2.1, this.2.2.1⟩
    · intro ι _ κ _ e
      exact φinj ι κ e
  have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Finset T))) good
  have hp : (Finset.univ : Finset (Finset T)).card = 2 ^ h := by
    rw [Finset.card_univ, Fintype.card_finset, hh]
  have hge3 : 3 ≤ h := by
    obtain ⟨s1, s2, s3⟩ := sizes (⟨0, hm⟩, true)
    omega
  have h2 : 2 + h.choose ℓ ≤ ((Finset.univ : Finset (Finset T)).filter (fun Y => ¬ good Y)).card := by
    have sub : (Finset.univ.powersetCard 0 ∪ Finset.univ.powersetCard h) ∪
        Finset.univ.powersetCard ℓ ⊆
        ((Finset.univ : Finset (Finset T)).filter (fun Y => ¬ good Y)) := by
      intro Y hY
      simp only [Finset.mem_union, Finset.mem_powersetCard, Finset.subset_univ, true_and] at hY
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, good]
      omega
    refine le_trans ?_ (Finset.card_le_card sub)
    rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint]
    · simp only [Finset.card_powersetCard, Finset.card_univ, ← hh, Nat.choose_zero_right,
        Nat.choose_self]
      omega
    · rw [Finset.disjoint_left]
      intro Y h1 h2
      simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and] at h1 h2
      omega
    · rw [Finset.disjoint_left]
      intro Y h1 h2
      simp only [Finset.mem_union, Finset.mem_powersetCard, Finset.subset_univ, true_and] at h1 h2
      omega
  omega


/-! ## The functions -/

section Defs
variable {m : ℕ}

def bitF (v : Fin (m+m)) (x : Finset (Fin (m+m))) : Bool := decide (v ∈ x)
def negF (v : Fin (m+m)) (x : Finset (Fin (m+m))) : Bool := !decide (v ∈ x)
def sameF (i : Fin m) (x : Finset (Fin (m+m))) : Bool :=
  decide ((Fin.castAdd m i ∈ x) ↔ (Fin.natAdd m i ∈ x))
def nsameF (i : Fin m) (x : Finset (Fin (m+m))) : Bool := !sameF i x
def zF (i : Fin m) (x : Finset (Fin (m+m))) : Bool :=
  negF (Fin.castAdd m i) x && negF (Fin.natAdd m i) x
def dpF (i : Fin m) (x : Finset (Fin (m+m))) : Bool :=
  bitF (Fin.castAdd m i) x && negF (Fin.natAdd m i) x
def dmF (i : Fin m) (x : Finset (Fin (m+m))) : Bool :=
  negF (Fin.castAdd m i) x && bitF (Fin.natAdd m i) x

def IsIn (S : Finset (Fin (m+m))) (g : Finset (Fin (m+m)) → Bool) : Prop :=
  g = (fun _ => false) ∨ g = (fun _ => true) ∨ (∃ v, g = bitF v) ∨ (∃ i, g = sameF i) ∨
    (∃ i, g = nsameF i) ∨ (∃ u ∈ S, g = negF u)

def IsNeed (f : Finset (Fin (m+m)) → Bool) : Prop :=
  (∃ v, f = negF v) ∨ (∃ i, f = zF i) ∨ (∃ i, f = dpF i) ∨ (∃ i, f = dmF i)

theorem fz1 (i : Fin m) (x : Finset (Fin (m+m))) :
    (negF (Fin.castAdd m i) x && sameF i x) = zF i x := by
  simp only [bitF, negF, nsameF, sameF, dpF, dmF, zF]
  by_cases h1 : Fin.castAdd m i ∈ x <;> by_cases h2 : Fin.natAdd m i ∈ x <;> simp [-Fin.natAdd_eq_addNat, h1, h2]

theorem fz2 (i : Fin m) (x : Finset (Fin (m+m))) :
    (negF (Fin.natAdd m i) x && sameF i x) = zF i x := by
  simp only [bitF, negF, nsameF, sameF, dpF, dmF, zF]
  by_cases h1 : Fin.castAdd m i ∈ x <;> by_cases h2 : Fin.natAdd m i ∈ x <;> simp [-Fin.natAdd_eq_addNat, h1, h2]

theorem fdp (i : Fin m) (x : Finset (Fin (m+m))) :
    (bitF (Fin.castAdd m i) x && nsameF i x) = dpF i x := by
  simp only [bitF, negF, nsameF, sameF, dpF, dmF, zF]
  by_cases h1 : Fin.castAdd m i ∈ x <;> by_cases h2 : Fin.natAdd m i ∈ x <;> simp [-Fin.natAdd_eq_addNat, h1, h2]

theorem fdm (i : Fin m) (x : Finset (Fin (m+m))) :
    (bitF (Fin.natAdd m i) x && nsameF i x) = dmF i x := by
  simp only [bitF, negF, nsameF, sameF, dpF, dmF, zF]
  by_cases h1 : Fin.castAdd m i ∈ x <;> by_cases h2 : Fin.natAdd m i ∈ x <;> simp [-Fin.natAdd_eq_addNat, h1, h2]

theorem fnb (i : Fin m) (x : Finset (Fin (m+m))) :
    (zF i x || dpF i x) = negF (Fin.natAdd m i) x := by
  simp only [bitF, negF, nsameF, sameF, dpF, dmF, zF]
  by_cases h1 : Fin.castAdd m i ∈ x <;> by_cases h2 : Fin.natAdd m i ∈ x <;> simp [-Fin.natAdd_eq_addNat, h1, h2]

theorem fna (i : Fin m) (x : Finset (Fin (m+m))) :
    (zF i x || dmF i x) = negF (Fin.castAdd m i) x := by
  simp only [bitF, negF, nsameF, sameF, dpF, dmF, zF]
  by_cases h1 : Fin.castAdd m i ∈ x <;> by_cases h2 : Fin.natAdd m i ∈ x <;> simp [-Fin.natAdd_eq_addNat, h1, h2]

theorem ca_ne_na (i j : Fin m) : Fin.castAdd m i ≠ Fin.natAdd m j := by
  intro e
  have h1 := congrArg Fin.val e
  simp [-Fin.natAdd_eq_addNat] at h1
  have := i.isLt
  omega

theorem vertex_cases (v : Fin (m+m)) : ∃ i : Fin m, v = Fin.castAdd m i ∨ v = Fin.natAdd m i := by
  by_cases h : v.val < m
  · exact ⟨⟨v.val, h⟩, Or.inl (Fin.ext (by simp [-Fin.natAdd_eq_addNat]))⟩
  · refine ⟨⟨v.val - m, by omega⟩, Or.inr (Fin.ext (by simp [-Fin.natAdd_eq_addNat]; omega))⟩

theorem sum_unseeded (S : Finset (Fin (m+m))) :
    ∑ i : Fin m, ((if Fin.castAdd m i ∉ S then 1 else 0) + (if Fin.natAdd m i ∉ S then 1 else 0))
      = m + m - S.card := by
  rw [Finset.sum_add_distrib]
  have e := Fin.sum_univ_add (a := m) (b := m) (fun v : Fin (m+m) => if v ∉ S then 1 else 0)
  rw [← e, Finset.sum_boole]
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (m+m))))
    (fun v => v ∈ S)
  have h2 : (Finset.univ.filter (fun v : Fin (m+m) => v ∈ S)) = S := by ext v; simp [-Fin.natAdd_eq_addNat]
  rw [h2, Finset.card_univ, Fintype.card_fin] at h
  simp only [Nat.cast_id]
  omega

end Defs

/-! ## The seeded edge construction -/

theorem upper (m : ℕ) (Z : Finset (Finset (Fin (m+m)))) (S : Finset (Fin (m+m)))
    (hit : ∀ i : Fin m, Fin.castAdd m i ∈ S ∨ Fin.natAdd m i ∈ S)
    (L : List (Finset (Fin (m+m)) → Bool)) (hL : ∀ g, g ∈ L ↔ IsIn S g)
    (need : Finset (Finset (Fin (m+m)) → Bool)) (hneed : ∀ f, f ∈ need → IsNeed f) :
    NeedOK L Z need (m + m + 3 * m - S.card) := by
  let raw : {x // x ∈ Z} → List Bool := fun x => L.map (fun g => g x.1)
  have width : ∀ x, (raw x).length = L.length := by intro x; simp [-Fin.natAdd_eq_addNat, raw]
  have hin : ∀ (p : Net L.length) g, IsIn S g → p.has raw (fun x => g x.1) :=
    fun p g hg => inHas L Z p g ((hL g).mpr hg)
  have hbit : ∀ v, IsIn S (bitF v) := fun v => Or.inr (Or.inr (Or.inl ⟨v, rfl⟩))
  have hsame : ∀ i, IsIn S (sameF i) := fun i => Or.inr (Or.inr (Or.inr (Or.inl ⟨i, rfl⟩)))
  have hnsame : ∀ i, IsIn S (nsameF i) :=
    fun i => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, rfl⟩))))
  have hneg : ∀ u ∈ S, IsIn S (negF u) :=
    fun u hu => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨u, hu, rfl⟩))))
  have hfalse : IsIn S (fun _ => false) := Or.inl rfl
  have hL0 : 0 < L.length := by
    have : (fun _ => false) ∈ L := (hL _).mpr hfalse
    exact List.length_pos_of_mem this
  let cost : Fin m → ℕ := fun i =>
    3 + ((if Fin.castAdd m i ∉ S then 1 else 0) + (if Fin.natAdd m i ∉ S then 1 else 0))
  let fs : Fin m → List ({x // x ∈ Z} → Bool) := fun i =>
    [fun x => negF (Fin.castAdd m i) x.1, fun x => negF (Fin.natAdd m i) x.1,
     fun x => zF i x.1, fun x => dpF i x.1, fun x => dmF i x.1]
  have step : ∀ i (q : Net L.length), ∃ r, Grow raw q r (cost i) ∧ ∀ f ∈ fs i, r.has raw f := by
    intro i q
    by_cases ha : Fin.castAdd m i ∈ S <;> by_cases hb : Fin.natAdd m i ∈ S
    · obtain ⟨q1, g1, z1⟩ := Net.and2 width q _ _ (fun x => zF i x.1)
        (hin q _ (hneg _ ha)) (hin q _ (hneg _ hb)) (fun x => rfl)
      obtain ⟨q2, g2, z2⟩ := Net.and2 width q1 _ _ (fun x => dpF i x.1)
        (hin q1 _ (hbit _)) (hin q1 _ (hneg _ hb)) (fun x => rfl)
      obtain ⟨q3, g3, z3⟩ := Net.and2 width q2 _ _ (fun x => dmF i x.1)
        (hin q2 _ (hneg _ ha)) (hin q2 _ (hbit _)) (fun x => rfl)
      refine ⟨q3, ((g1.trans g2).trans g3).weaken (by simp only [cost]; rw [if_neg (not_not.mpr ha), if_neg (not_not.mpr hb)]), ?_⟩
      intro f hf
      simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl
      · exact hin q3 _ (hneg _ ha)
      · exact hin q3 _ (hneg _ hb)
      · exact g3.1 _ (g2.1 _ z1)
      · exact g3.1 _ z2
      · exact z3
    · obtain ⟨q1, g1, z1⟩ := Net.and2 width q _ _ (fun x => zF i x.1)
        (hin q _ (hneg _ ha)) (hin q _ (hsame i)) (fun x => fz1 i x.1)
      obtain ⟨q2, g2, z2⟩ := Net.and2 width q1 _ _ (fun x => dpF i x.1)
        (hin q1 _ (hbit _)) (hin q1 _ (hnsame i)) (fun x => fdp i x.1)
      obtain ⟨q3, g3, z3⟩ := Net.and2 width q2 _ _ (fun x => dmF i x.1)
        (hin q2 _ (hneg _ ha)) (hin q2 _ (hbit _)) (fun x => rfl)
      obtain ⟨q4, g4, z4⟩ := Net.or2 width q3 _ _ (fun x => negF (Fin.natAdd m i) x.1)
        (g3.1 _ (g2.1 _ z1)) (g3.1 _ z2) (fun x => fnb i x.1)
      refine ⟨q4, (((g1.trans g2).trans g3).trans g4).weaken (by simp only [cost]; rw [if_neg (not_not.mpr ha), if_pos hb]), ?_⟩
      intro f hf
      simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl
      · exact hin q4 _ (hneg _ ha)
      · exact z4
      · exact g4.1 _ (g3.1 _ (g2.1 _ z1))
      · exact g4.1 _ (g3.1 _ z2)
      · exact g4.1 _ z3
    · obtain ⟨q1, g1, z1⟩ := Net.and2 width q _ _ (fun x => zF i x.1)
        (hin q _ (hneg _ hb)) (hin q _ (hsame i)) (fun x => fz2 i x.1)
      obtain ⟨q2, g2, z2⟩ := Net.and2 width q1 _ _ (fun x => dmF i x.1)
        (hin q1 _ (hbit _)) (hin q1 _ (hnsame i)) (fun x => fdm i x.1)
      obtain ⟨q3, g3, z3⟩ := Net.and2 width q2 _ _ (fun x => dpF i x.1)
        (hin q2 _ (hbit _)) (hin q2 _ (hneg _ hb)) (fun x => rfl)
      obtain ⟨q4, g4, z4⟩ := Net.or2 width q3 _ _ (fun x => negF (Fin.castAdd m i) x.1)
        (g3.1 _ (g2.1 _ z1)) (g3.1 _ z2) (fun x => fna i x.1)
      refine ⟨q4, (((g1.trans g2).trans g3).trans g4).weaken (by simp only [cost]; rw [if_pos ha, if_neg (not_not.mpr hb)]), ?_⟩
      intro f hf
      simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl
      · exact z4
      · exact hin q4 _ (hneg _ hb)
      · exact g4.1 _ (g3.1 _ (g2.1 _ z1))
      · exact g4.1 _ z3
      · exact g4.1 _ (g3.1 _ z2)
    · exact absurd (hit i) (by tauto)
  obtain ⟨r, gr, hr⟩ := Net.foldCost fs cost step (List.finRange m) (Net.empty _)
  have hsum : ((List.finRange m).map cost).sum = 3 * m + (m + m - S.card) := by
    rw [← Fin.sum_univ_def]
    simp only [cost]
    rw [Finset.sum_add_distrib, sum_unseeded]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    omega
  apply netNeedOK L Z need _ hL0 r
  · have := gr.2
    simp only [Net.empty, List.length_nil, zero_add] at this
    have hS : S.card ≤ m + m := by
      have := Finset.card_le_univ S
      simpa [-Fin.natAdd_eq_addNat] using this
    omega
  · intro f hf
    rcases hneed f hf with ⟨v, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
    · obtain ⟨i, hv | hv⟩ := vertex_cases v
      · subst hv; exact hr i (List.mem_finRange i) _ (by simp [-Fin.natAdd_eq_addNat, fs])
      · subst hv; exact hr i (List.mem_finRange i) _ (by simp [-Fin.natAdd_eq_addNat, fs])
    · exact hr i (List.mem_finRange i) _ (by simp [-Fin.natAdd_eq_addNat, fs])
    · exact hr i (List.mem_finRange i) _ (by simp [-Fin.natAdd_eq_addNat, fs])
    · exact hr i (List.mem_finRange i) _ (by simp [-Fin.natAdd_eq_addNat, fs])

/-! ## The sample -/

section Sample
variable {m : ℕ}

def chainPt (m t : ℕ) : Finset (Fin (m+m)) := Finset.univ.filter (fun v => v.val % m < t)

def code (i : Fin m) (r : ℕ) : Bool := Nat.testBit (i.val + 1) r

def extraPt (m r : ℕ) : Finset (Fin (m+m)) :=
  Finset.univ.filter (fun v => if v.val < m then Nat.testBit (v.val + 1) r = true
    else Nat.testBit (v.val - m + 1) r = false)

def sampleA (m h : ℕ) : Finset (Finset (Fin (m+m))) :=
  (Finset.range (m+1)).image (chainPt m) ∪ (Finset.range h).image (extraPt m)

theorem sampleA_card (m h : ℕ) : (sampleA m h).card ≤ m + 1 + h := by
  unfold sampleA
  refine (Finset.card_union_le _ _).trans ?_
  have h1 := Finset.card_image_le (s := Finset.range (m+1)) (f := chainPt m)
  have h2 := Finset.card_image_le (s := Finset.range h) (f := extraPt m)
  simp only [Finset.card_range] at h1 h2
  omega

theorem chain_mem {h : ℕ} (t : ℕ) (ht : t ≤ m) : chainPt m t ∈ sampleA m h := by
  unfold sampleA
  apply Finset.mem_union_left
  exact Finset.mem_image_of_mem _ (by simp [-Fin.natAdd_eq_addNat]; omega)

theorem extra_mem {h : ℕ} (r : ℕ) (hr : r < h) : extraPt m r ∈ sampleA m h := by
  unfold sampleA
  apply Finset.mem_union_right
  exact Finset.mem_image_of_mem _ (by simp [-Fin.natAdd_eq_addNat]; omega)

theorem mem_chain_a (i : Fin m) (t : ℕ) : Fin.castAdd m i ∈ chainPt m t ↔ i.val < t := by
  simp [-Fin.natAdd_eq_addNat, chainPt, Nat.mod_eq_of_lt i.isLt]

theorem mem_chain_b (i : Fin m) (t : ℕ) : Fin.natAdd m i ∈ chainPt m t ↔ i.val < t := by
  have : (Fin.natAdd m i).val % m = i.val := by
    rw [Fin.coe_natAdd, Nat.add_mod_left, Nat.mod_eq_of_lt i.isLt]
  simp only [chainPt, Finset.mem_filter, Finset.mem_univ, true_and, this]

theorem mem_extra_a (i : Fin m) (r : ℕ) : Fin.castAdd m i ∈ extraPt m r ↔ code i r = true := by
  simp [-Fin.natAdd_eq_addNat, extraPt, code]

theorem mem_extra_b (i : Fin m) (r : ℕ) : Fin.natAdd m i ∈ extraPt m r ↔ code i r = false := by
  have h1 : ¬ (Fin.natAdd m i).val < m := by simp [-Fin.natAdd_eq_addNat]
  have h2 : (Fin.natAdd m i).val - m + 1 = i.val + 1 := by simp [-Fin.natAdd_eq_addNat]
  simp only [extraPt, Finset.mem_filter, Finset.mem_univ, true_and, h1, if_false, h2, code]

/-- The need functions, indexed. -/
def NF (ι : Fin m × Fin 5) : Finset (Fin (m+m)) → Bool :=
  if ι.2.val = 0 then negF (Fin.castAdd m ι.1) else if ι.2.val = 1 then negF (Fin.natAdd m ι.1)
  else if ι.2.val = 2 then zF ι.1 else if ι.2.val = 3 then dpF ι.1 else dmF ι.1

theorem NF_need (ι : Fin m × Fin 5) : IsNeed (NF ι) := by
  rcases ι with ⟨i, k⟩
  fin_cases k
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr (Or.inl ⟨i, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨i, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨i, rfl⟩))

theorem NF_chain (ι : Fin m × Fin 5) (t : ℕ) :
    NF ι (chainPt m t) = (decide (ι.2.val ≤ 2) && !decide (ι.1.val < t)) := by
  rcases ι with ⟨i, k⟩
  fin_cases k <;> simp [-Fin.natAdd_eq_addNat, NF, negF, zF, dpF, dmF, bitF, mem_chain_a, mem_chain_b]

theorem NF_extra (ι : Fin m × Fin 5) (r : ℕ) :
    NF ι (extraPt m r) = (if ι.2.val = 0 then !code ι.1 r else if ι.2.val = 1 then code ι.1 r
      else if ι.2.val = 2 then false else if ι.2.val = 3 then code ι.1 r else !code ι.1 r) := by
  rcases ι with ⟨i, k⟩
  cases hc : code i r <;>
    fin_cases k <;> simp [-Fin.natAdd_eq_addNat, NF, negF, zF, dpF, dmF, bitF, mem_extra_a, mem_extra_b, hc]

theorem bit_chain0 (v : Fin (m+m)) : bitF v (chainPt m 0) = false := by
  simp [-Fin.natAdd_eq_addNat, bitF, chainPt]

theorem bit_chainm (hm : 0 < m) (v : Fin (m+m)) : bitF v (chainPt m m) = true := by
  simp [-Fin.natAdd_eq_addNat, bitF, chainPt, Nat.mod_lt _ hm]

theorem same_chain (j : Fin m) (t : ℕ) : sameF j (chainPt m t) = true := by
  simp [-Fin.natAdd_eq_addNat, sameF, mem_chain_a, mem_chain_b]

theorem nsame_extra (j : Fin m) (r : ℕ) : nsameF j (extraPt m r) = true := by
  cases hc : code j r <;> simp [-Fin.natAdd_eq_addNat, nsameF, sameF, mem_extra_a, mem_extra_b, hc]

/-! ### Codes -/

theorem code_top {h : ℕ} (hh : 2*m+2 ≤ 2^h) (i : Fin m) : code i (h-1) = false := by
  unfold code
  apply Nat.testBit_eq_false_of_lt
  have := i.isLt
  have h2 : 2 ≤ h := by
    by_contra hc
    interval_cases h <;> simp [-Fin.natAdd_eq_addNat] at hh <;> omega
  have : 2^h = 2 * 2^(h-1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  have := i.isLt
  omega

theorem code_some {h : ℕ} (hh : 2*m+2 ≤ 2^h) (i : Fin m) : ∃ r < h, code i r = true := by
  obtain ⟨r, hr, _⟩ := Nat.exists_most_significant_bit (n := i.val + 1) (by omega)
  refine ⟨r, ?_, hr⟩
  by_contra hc
  have : i.val + 1 < 2^r := by
    have := i.isLt
    have : 2^h ≤ 2^r := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [Nat.testBit_eq_false_of_lt this] at hr
  exact absurd hr (by simp [-Fin.natAdd_eq_addNat])

theorem code_inj {h : ℕ} (hh : 2*m+2 ≤ 2^h) (i j : Fin m) (e : ∀ r < h, code i r = code j r) :
    i = j := by
  have : i.val + 1 = j.val + 1 := by
    apply Nat.eq_of_testBit_eq
    intro r
    by_cases hr : r < h
    · exact e r hr
    · have hp : 2^h ≤ 2^r := Nat.pow_le_pow_right (by norm_num) (by omega)
      have := i.isLt
      have := j.isLt
      rw [Nat.testBit_eq_false_of_lt (by omega), Nat.testBit_eq_false_of_lt (by omega)]
  exact Fin.ext (by omega)

/-! ### Separation on the sample -/

theorem chain_eq (hm : 0 < m) (i j : Fin m) (e : ∀ t ≤ m, decide (i.val < t) = decide (j.val < t)) :
    i = j := by
  have e1 := e (i.val + 1) (by have := i.isLt; omega)
  have e2 := e (j.val + 1) (by have := j.isLt; omega)
  simp [-Fin.natAdd_eq_addNat] at e1 e2
  exact Fin.ext (by omega)

theorem NF_sep {h : ℕ} (hm : 0 < m) (hh : 2*m+2 ≤ 2^h) (ι κ : Fin m × Fin 5) (hne : ι ≠ κ) :
    ∃ x ∈ sampleA m h, NF ι x ≠ NF κ x := by
  by_contra hcon
  push_neg at hcon
  have hc : ∀ t ≤ m, NF ι (chainPt m t) = NF κ (chainPt m t) :=
    fun t ht => hcon _ (chain_mem t ht)
  have he : ∀ r < h, NF ι (extraPt m r) = NF κ (extraPt m r) :=
    fun r hr => hcon _ (extra_mem r hr)
  simp only [NF_chain] at hc
  simp only [NF_extra] at he
  apply hne
  rcases ι with ⟨i, k⟩
  rcases κ with ⟨j, l⟩
  have top := h - 1
  have hh1 : h - 1 < h := by
    have : 2 ≤ h := by
      by_contra hc'
      interval_cases h <;> simp [-Fin.natAdd_eq_addNat] at hh <;> omega
    omega
  have ci := code_top hh i
  have cj := code_top hh j
  obtain ⟨ri, hri, hri'⟩ := code_some hh i
  obtain ⟨rj, hrj, hrj'⟩ := code_some hh j
  have c0 := hc 0 (Nat.zero_le _)
  have chainEq : k.val ≤ 2 → l.val ≤ 2 → i = j := by
    intro hk hl
    apply chain_eq hm
    intro t ht
    have := hc t ht
    simp only [hk, hl, decide_true, Bool.true_and] at this
    simpa [-Fin.natAdd_eq_addNat] using this
  fin_cases k <;> fin_cases l <;> simp [-Fin.natAdd_eq_addNat] at c0 ⊢
  all_goals first
    | exact chainEq (by decide) (by decide)
    | exact code_inj hh i j (fun r hr => by simpa [-Fin.natAdd_eq_addNat] using he r hr)
    | (have := he ri hri; simp [-Fin.natAdd_eq_addNat, hri'] at this; done)
    | (have := he rj hrj; simp [-Fin.natAdd_eq_addNat, hrj'] at this; done)
    | (have := he (h-1) hh1; simp [-Fin.natAdd_eq_addNat, ci, cj] at this; done)
    | (have e1 := chainEq (by decide) (by decide); subst e1;
        have := he ri hri; simp [-Fin.natAdd_eq_addNat, hri'] at this; done)
    | skip

theorem NF_notraw {h : ℕ} (hm : 0 < m) (hh : 2*m+2 ≤ 2^h) (ι : Fin m × Fin 5)
    (g : Finset (Fin (m+m)) → Bool)
    (hg : g = (fun _ => false) ∨ g = (fun _ => true) ∨ (∃ v, g = bitF v) ∨ (∃ j, g = sameF j) ∨
      (∃ j, g = nsameF j)) :
    ∃ x ∈ sampleA m h, NF ι x ≠ g x := by
  have hh1 : h - 1 < h := by
    have : 2 ≤ h := by
      by_contra hc'
      interval_cases h <;> simp [-Fin.natAdd_eq_addNat] at hh <;> omega
    omega
  rcases ι with ⟨i, k⟩
  have ci := code_top hh i
  obtain ⟨ri, hri, hri'⟩ := code_some hh i
  have m0 : chainPt m 0 ∈ sampleA m h := chain_mem 0 (Nat.zero_le _)
  have mm : chainPt m m ∈ sampleA m h := chain_mem m le_rfl
  have il := i.isLt
  by_cases hk : k.val ≤ 2
  · rcases hg with rfl | rfl | ⟨v, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact ⟨_, m0, by simp [-Fin.natAdd_eq_addNat, NF_chain, hk]⟩
    · exact ⟨_, mm, by simp [-Fin.natAdd_eq_addNat, NF_chain, hk, il]⟩
    · exact ⟨_, m0, by simp [-Fin.natAdd_eq_addNat, NF_chain, hk, bit_chain0]⟩
    · exact ⟨_, mm, by simp [-Fin.natAdd_eq_addNat, NF_chain, hk, il, same_chain]⟩
    · exact ⟨_, m0, by simp [-Fin.natAdd_eq_addNat, NF_chain, hk, nsameF, same_chain]⟩
  · have hk' : k.val = 3 ∨ k.val = 4 := by omega
    rcases hg with rfl | rfl | ⟨v, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rcases hk' with hk' | hk'
      · exact ⟨_, extra_mem ri hri, by simp [-Fin.natAdd_eq_addNat, NF_extra, hk', hri']⟩
      · exact ⟨_, extra_mem (h-1) hh1, by simp [-Fin.natAdd_eq_addNat, NF_extra, hk', ci]⟩
    · exact ⟨_, m0, by simp [-Fin.natAdd_eq_addNat, NF_chain, hk]⟩
    · exact ⟨_, mm, by simp [-Fin.natAdd_eq_addNat, NF_chain, hk, bit_chainm hm]⟩
    · exact ⟨_, m0, by simp [-Fin.natAdd_eq_addNat, NF_chain, hk, same_chain]⟩
    · rcases hk' with hk' | hk'
      · exact ⟨_, extra_mem (h-1) hh1, by simp [-Fin.natAdd_eq_addNat, NF_extra, hk', ci, nsame_extra]⟩
      · exact ⟨_, extra_mem ri hri, by simp [-Fin.natAdd_eq_addNat, NF_extra, hk', hri', nsame_extra]⟩

end Sample

theorem wire_input {W : Type} (C : Circuit) (L : List (W → Bool)) (x : W) (k : ℕ)
    (hk : k < L.length) : (C.wires (L.map (fun g => g x))).getD k false = L[k] x := by
  rw [wires_eq, getD_run _ _ _ (by simpa [-Fin.natAdd_eq_addNat] using hk)]
  simp [-Fin.natAdd_eq_addNat, List.getD_eq_getElem?_getD, hk]

/-! ## The sample keeps every cost -/

theorem keepsA (m h : ℕ) (hm : 0 < m) (hh : 2*m+2 ≤ 2^h) (S : Finset (Fin (m+m))) (p : ℕ)
    (L : List (Finset (Fin (m+m)) → Bool)) (hL : ∀ g, g ∈ L ↔ IsIn S g)
    (need : Finset (Finset (Fin (m+m)) → Bool)) (hneed : ∀ f, f ∈ need ↔ IsNeed f) :
    NeedOK L (sampleA m h) need p ↔
      ((∀ i : Fin m, Fin.castAdd m i ∈ S ∨ Fin.natAdd m i ∈ S) ∧ m + m + 3*m - S.card ≤ p) := by
  constructor
  · rintro ⟨C, hmono, hback, hout, hsize, hall⟩
    have hit : ∀ i : Fin m, Fin.castAdd m i ∈ S ∨ Fin.natAdd m i ∈ S := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨i, ha, hb⟩ := hcon
      have il := i.isLt
      obtain ⟨j, -, hj⟩ := hall (negF (Fin.castAdd m i)) ((hneed _).mpr (Or.inl ⟨_, rfl⟩))
      have x1 := hj _ (chain_mem (h := h) i.val (by omega))
      have x2 := hj _ (chain_mem (h := h) (i.val + 1) (by omega))
      have v1 : negF (Fin.castAdd m i) (chainPt m i.val) = true := by
        simp [-Fin.natAdd_eq_addNat, negF, mem_chain_a]
      have v2 : negF (Fin.castAdd m i) (chainPt m (i.val+1)) = false := by
        simp [-Fin.natAdd_eq_addNat, negF, mem_chain_a]
      have mono := wires_mono C hmono (L.map (fun g => g (chainPt m i.val)))
        (L.map (fun g => g (chainPt m (i.val+1)))) (by simp [-Fin.natAdd_eq_addNat]) ?_ j
      · rw [x1, x2, v1, v2] at mono
        exact absurd (mono rfl) (by simp [-Fin.natAdd_eq_addNat])
      · intro k hk
        by_cases hkl : k < L.length
        · simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hkl,
            Option.map_some, Option.getD_some] at hk ⊢
          have hg := (hL _).mp (List.getElem_mem hkl)
          rcases hg with e | e | ⟨v, e⟩ | ⟨j', e⟩ | ⟨j', e⟩ | ⟨u, hu, e⟩
          · simp [-Fin.natAdd_eq_addNat, e] at hk
          · simp [-Fin.natAdd_eq_addNat, e]
          · rw [e] at hk ⊢
            simp only [bitF, chainPt, Finset.mem_filter, Finset.mem_univ, true_and,
              decide_eq_true_eq] at hk ⊢
            omega
          · rw [e]; exact same_chain _ _
          · rw [e] at hk; simp [-Fin.natAdd_eq_addNat, nsameF, same_chain] at hk
          · rw [e] at hk ⊢
            simp only [negF, chainPt, Finset.mem_filter, Finset.mem_univ, true_and,
              Bool.not_eq_true', decide_eq_false_iff_not, not_lt] at hk ⊢
            by_contra hlt
            have hv : u.val % m = i.val := by omega
            obtain ⟨i', hu' | hu'⟩ := vertex_cases u
            · subst hu'
              have : i' = i := Fin.ext (by simpa [-Fin.natAdd_eq_addNat, Nat.mod_eq_of_lt i'.isLt] using hv)
              subst this; exact ha hu
            · subst hu'
              have : i' = i := Fin.ext (by
                rw [Fin.coe_natAdd, Nat.add_mod_left, Nat.mod_eq_of_lt i'.isLt] at hv; exact hv)
              subst this; exact hb hu
        · simp [-Fin.natAdd_eq_addNat, List.getD_eq_getElem?_getD, hkl] at hk
    refine ⟨hit, ?_⟩
    -- counting
    have hsel : ∀ ι : Fin m × Fin 5, ∃ j, j < L.length + C.size ∧ ∀ x ∈ sampleA m h,
        (C.wires (L.map (fun g => g x))).getD j false = NF ι x := by
      intro ι
      obtain ⟨j, hj, e⟩ := hall (NF ι) ((hneed _).mpr (NF_need ι))
      exact ⟨j, hj, e⟩
    choose jj hjj hjv using hsel
    let I : Finset (Fin m × Fin 5) := Finset.univ.filter
      (fun ι => ¬ (ι.2.val = 0 ∧ Fin.castAdd m ι.1 ∈ S) ∧ ¬ (ι.2.val = 1 ∧ Fin.natAdd m ι.1 ∈ S))
    have hI : I.card ≤ C.size := by
      have : (Finset.Ico L.length (L.length + C.size)).card = C.size := by simp [-Fin.natAdd_eq_addNat]
      rw [← this]
      apply Finset.card_le_card_of_injOn jj
      · intro ι hι
        rw [Finset.mem_coe, Finset.mem_Ico]
        refine ⟨?_, hjj ι⟩
        by_contra hlt
        push_neg at hlt
        have hg := (hL _).mp (List.getElem_mem hlt)
        have eq : ∀ x ∈ sampleA m h, NF ι x = L[jj ι] x := by
          intro x hx
          rw [← hjv ι x hx, wire_input C L x _ hlt]
        rcases hg with e | e | ⟨v, e⟩ | ⟨j', e⟩ | ⟨j', e⟩ | ⟨u, hu, e⟩
        · obtain ⟨x, hx, hne⟩ := NF_notraw hm hh ι _ (Or.inl e)
          exact hne (eq x hx)
        · obtain ⟨x, hx, hne⟩ := NF_notraw hm hh ι _ (Or.inr (Or.inl e))
          exact hne (eq x hx)
        · obtain ⟨x, hx, hne⟩ := NF_notraw hm hh ι _ (Or.inr (Or.inr (Or.inl ⟨v, e⟩)))
          exact hne (eq x hx)
        · obtain ⟨x, hx, hne⟩ := NF_notraw hm hh ι _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨j', e⟩))))
          exact hne (eq x hx)
        · obtain ⟨x, hx, hne⟩ := NF_notraw hm hh ι _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨j', e⟩))))
          exact hne (eq x hx)
        · simp only [I, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hι
          obtain ⟨i', hu' | hu'⟩ := vertex_cases u
          · subst hu'
            have hne : ι ≠ (i', 0) := by
              rintro rfl; exact hι.1 ⟨rfl, hu⟩
            obtain ⟨x, hx, hx'⟩ := NF_sep hm hh ι (i', 0) hne
            apply hx'
            rw [eq x hx, e]; simp [-Fin.natAdd_eq_addNat, NF]
          · subst hu'
            have hne : ι ≠ (i', 1) := by
              rintro rfl; exact hι.2 ⟨rfl, hu⟩
            obtain ⟨x, hx, hx'⟩ := NF_sep hm hh ι (i', 1) hne
            apply hx'
            rw [eq x hx, e]; simp [-Fin.natAdd_eq_addNat, NF]
      · intro ι _ κ _ e
        by_contra hne
        obtain ⟨x, hx, hx'⟩ := NF_sep hm hh ι κ hne
        apply hx'
        rw [← hjv ι x hx, ← hjv κ x hx, e]
    have hIc : (Finset.univ.filter (fun ι : Fin m × Fin 5 => ¬ (¬ (ι.2.val = 0 ∧
        Fin.castAdd m ι.1 ∈ S) ∧ ¬ (ι.2.val = 1 ∧ Fin.natAdd m ι.1 ∈ S)))).card ≤ S.card := by
      apply Finset.card_le_card_of_injOn (fun ι => if ι.2.val = 0 then Fin.castAdd m ι.1
        else Fin.natAdd m ι.1)
      · intro ι hι
        have key : (ι.2.val = 0 ∧ Fin.castAdd m ι.1 ∈ S) ∨ (ι.2.val = 1 ∧ Fin.natAdd m ι.1 ∈ S) := by
          rw [Finset.mem_coe, Finset.mem_filter] at hι; tauto
        rw [Finset.mem_coe]
        rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · simp only [h1, if_true]; exact h2
        · have : ι.2.val ≠ 0 := by omega
          simp only [this, if_false]; exact h2
      · intro ι hι κ hκ e
        have kι : (ι.2.val = 0 ∧ Fin.castAdd m ι.1 ∈ S) ∨ (ι.2.val = 1 ∧ Fin.natAdd m ι.1 ∈ S) := by
          rw [Finset.mem_coe, Finset.mem_filter] at hι; tauto
        have kκ : (κ.2.val = 0 ∧ Fin.castAdd m κ.1 ∈ S) ∨ (κ.2.val = 1 ∧ Fin.natAdd m κ.1 ∈ S) := by
          rw [Finset.mem_coe, Finset.mem_filter] at hκ; tauto
        rcases ι with ⟨i, k⟩
        rcases κ with ⟨j, l⟩
        have hk : k.val = 0 ∨ k.val = 1 := by
          rcases kι with h | h
          · exact Or.inl h.1
          · exact Or.inr h.1
        have hl : l.val = 0 ∨ l.val = 1 := by
          rcases kκ with h | h
          · exact Or.inl h.1
          · exact Or.inr h.1
        rcases hk with hk | hk <;> rcases hl with hl | hl
        · simp only [hk, hl, if_true] at e
          have := Fin.castAdd_injective m m e
          exact Prod.ext this (Fin.ext (by simp [-Fin.natAdd_eq_addNat, hk, hl]))
        · simp only [hk, hl, if_true, if_false, one_ne_zero] at e
          exact absurd e (ca_ne_na i j)
        · simp only [hk, hl, if_true, if_false, one_ne_zero] at e
          exact absurd e.symm (ca_ne_na j i)
        · simp only [hk, hl, if_false, one_ne_zero] at e
          have := Fin.natAdd_injective m m e
          exact Prod.ext this (Fin.ext (by simp [-Fin.natAdd_eq_addNat, hk, hl]))
    have htot := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m × Fin 5)))
      (fun ι : Fin m × Fin 5 => ¬ (ι.2.val = 0 ∧ Fin.castAdd m ι.1 ∈ S) ∧
        ¬ (ι.2.val = 1 ∧ Fin.natAdd m ι.1 ∈ S))
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at htot
    change I.card + _ = _ at htot
    omega
  · rintro ⟨hit, hp⟩
    exact (upper m _ S hit L hL need (fun f hf => (hneed f).mp hf)).weaken hp

/-! ## Necessity -/

section Nec
variable {m : ℕ}

def AF (ι : Fin m × Fin 3) : Finset (Fin (m+m)) → Bool :=
  if ι.2.val = 0 then zF ι.1 else if ι.2.val = 1 then dpF ι.1 else dmF ι.1

theorem AF_and (ι : Fin m × Fin 3) : ∃ g1 g2, IsIn Finset.univ g1 ∧ IsIn Finset.univ g2 ∧
    ∀ x, (g1 x && g2 x) = AF ι x := by
  have hbit : ∀ v, IsIn (Finset.univ : Finset (Fin (m+m))) (bitF v) :=
    fun v => Or.inr (Or.inr (Or.inl ⟨v, rfl⟩))
  have hneg : ∀ v, IsIn (Finset.univ : Finset (Fin (m+m))) (negF v) :=
    fun v => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨v, Finset.mem_univ _, rfl⟩))))
  rcases ι with ⟨i, k⟩
  fin_cases k
  · exact ⟨_, _, hneg (Fin.castAdd m i), hneg (Fin.natAdd m i), fun x => by simp [-Fin.natAdd_eq_addNat, AF, zF]⟩
  · exact ⟨_, _, hbit (Fin.castAdd m i), hneg (Fin.natAdd m i), fun x => by simp [-Fin.natAdd_eq_addNat, AF, dpF]⟩
  · exact ⟨_, _, hneg (Fin.castAdd m i), hbit (Fin.natAdd m i), fun x => by simp [-Fin.natAdd_eq_addNat, AF, dmF]⟩

/-- With every vertex seeded, one atom coinciding on the sample with an input or another atom
saves a gate. -/
theorem n1 (hm : 0 < m) (Z : Finset (Finset (Fin (m+m))))
    (L : List (Finset (Fin (m+m)) → Bool)) (hL : ∀ g, g ∈ L ↔ IsIn Finset.univ g)
    (need : Finset (Finset (Fin (m+m)) → Bool)) (hneed : ∀ f, f ∈ need → IsNeed f)
    (ι0 : Fin m × Fin 3) (g : Finset (Fin (m+m)) → Bool)
    (hg : IsIn Finset.univ g ∨ ∃ κ, κ ≠ ι0 ∧ g = AF κ) (hZ : ∀ x ∈ Z, g x = AF ι0 x) :
    NeedOK L Z need (3 * m - 1) := by
  let raw : {x // x ∈ Z} → List Bool := fun x => L.map (fun g => g x.1)
  have width : ∀ x, (raw x).length = L.length := by intro x; simp [-Fin.natAdd_eq_addNat, raw]
  have hin : ∀ (p : Net L.length) g, IsIn Finset.univ g → p.has raw (fun x => g x.1) :=
    fun p g hg => inHas L Z p g ((hL g).mpr hg)
  have hL0 : 0 < L.length := List.length_pos_of_mem ((hL _).mpr (Or.inl rfl))
  let l := ((Finset.univ : Finset (Fin m × Fin 3)).erase ι0).toList
  have hl : l.length = 3 * m - 1 := by
    simp only [l, Finset.length_toList]
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_fin]
    omega
  let fs : Fin m × Fin 3 → List ({x // x ∈ Z} → Bool) := fun ι => [fun x => AF ι x.1]
  have step : ∀ ι (q : Net L.length), ∃ r, Grow raw q r 1 ∧ ∀ f ∈ fs ι, r.has raw f := by
    intro ι q
    obtain ⟨g1, g2, h1, h2, e⟩ := AF_and ι
    obtain ⟨r, gr, hr⟩ := Net.and2 width q _ _ (fun x => AF ι x.1) (hin q g1 h1) (hin q g2 h2)
      (fun x => e x.1)
    refine ⟨r, gr, ?_⟩
    intro f hf
    simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hf
    subst hf; exact hr
  obtain ⟨r, gr, hr⟩ := Net.foldCost fs (fun _ => 1) step l (Net.empty _)
  have hAF : ∀ κ, r.has raw (fun x => AF κ x.1) := by
    intro κ
    by_cases hκ : κ = ι0
    · subst hκ
      rcases hg with hg | ⟨κ', hκ', rfl⟩
      · exact Net.has_congr (hin r g hg) (fun x => hZ x.1 x.2)
      · have := hr κ' (by simp [-Fin.natAdd_eq_addNat, l, hκ']) (fun x => AF κ' x.1) (by simp [-Fin.natAdd_eq_addNat, fs])
        exact Net.has_congr this (fun x => hZ x.1 x.2)
    · exact hr κ (by simp [-Fin.natAdd_eq_addNat, l, hκ]) (fun x => AF κ x.1) (by simp [-Fin.natAdd_eq_addNat, fs])
  apply netNeedOK L Z need _ hL0 r
  · have := gr.2
    have hs1 : ∀ (l' : List (Fin m × Fin 3)), (l'.map (fun _ => (1:ℕ))).sum = l'.length := by
      intro l'
      induction l' with
      | nil => rfl
      | cons a l' ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; omega
    rw [hs1] at this
    simp only [Net.empty, List.length_nil, zero_add] at this
    omega
  · intro f hf
    rcases hneed f hf with ⟨v, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact hin r _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨v, Finset.mem_univ _, rfl⟩)))))
    · exact Net.has_congr (hAF (i, 0)) (fun x => by simp [-Fin.natAdd_eq_addNat, AF])
    · exact Net.has_congr (hAF (i, 1)) (fun x => by simp [-Fin.natAdd_eq_addNat, AF])
    · exact Net.has_congr (hAF (i, 2)) (fun x => by simp [-Fin.natAdd_eq_addNat, AF])

def S0 (i0 : Fin m) : Finset (Fin (m+m)) :=
  (Finset.univ.erase (Fin.castAdd m i0)).erase (Fin.natAdd m i0)

/-- Without an increasing pair for edge `i0`, an unseeded edge is still computable. -/
theorem n2 (Z : Finset (Finset (Fin (m+m)))) (i0 : Fin m)
    (L : List (Finset (Fin (m+m)) → Bool)) (hL : ∀ g, g ∈ L ↔ IsIn (S0 i0) g)
    (need : Finset (Finset (Fin (m+m)) → Bool)) (hneed : ∀ f, f ∈ need → IsNeed f)
    (hnot : ∀ x ∈ Z, ∀ y ∈ Z, (∀ v, v ≠ Fin.castAdd m i0 → v ≠ Fin.natAdd m i0 → (v ∈ x ↔ v ∈ y)) →
      Fin.castAdd m i0 ∉ x → Fin.natAdd m i0 ∉ x → Fin.castAdd m i0 ∈ y → Fin.natAdd m i0 ∈ y →
        False) :
    ∃ p, NeedOK L Z need p := by
  set a := Fin.castAdd m i0 with ha_def
  set b := Fin.natAdd m i0 with hb_def
  let raw : {x // x ∈ Z} → List Bool := fun x => L.map (fun g => g x.1)
  have width : ∀ x, (raw x).length = L.length := by intro x; simp [-Fin.natAdd_eq_addNat, raw]
  have hin : ∀ (p : Net L.length) g, IsIn (S0 i0) g → p.has raw (fun x => g x.1) :=
    fun p g hg => inHas L Z p g ((hL g).mpr hg)
  have hL0 : 0 < L.length := List.length_pos_of_mem ((hL _).mpr (Or.inl rfl))
  have inS : ∀ v, v ≠ a → v ≠ b → v ∈ S0 i0 := by
    intro v h1 h2; simp only [S0, Finset.mem_erase, ← ha_def, ← hb_def]; exact ⟨h2, h1, Finset.mem_univ _⟩
  have hbit : ∀ v, IsIn (S0 i0) (bitF v) := fun v => Or.inr (Or.inr (Or.inl ⟨v, rfl⟩))
  have hsame : IsIn (S0 i0) (sameF i0) := Or.inr (Or.inr (Or.inr (Or.inl ⟨i0, rfl⟩)))
  have hnsame : IsIn (S0 i0) (nsameF i0) := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i0, rfl⟩))))
  have hneg : ∀ v, v ≠ a → v ≠ b → IsIn (S0 i0) (negF v) :=
    fun v h1 h2 => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨v, inS v h1 h2, rfl⟩))))
  let lit : Finset (Fin (m+m)) → Fin (m+m) → Finset (Fin (m+m)) → Bool :=
    fun z v x => if v ∈ z then bitF v x else negF v x
  have hlit : ∀ z v, v ≠ a → v ≠ b → IsIn (S0 i0) (lit z v) := by
    intro z v h1 h2
    by_cases hv : v ∈ z
    · have : lit z v = bitF v := by funext x; simp [-Fin.natAdd_eq_addNat, lit, hv]
      rw [this]; exact hbit v
    · have : lit z v = negF v := by funext x; simp [-Fin.natAdd_eq_addNat, lit, hv]
      rw [this]; exact hneg v h1 h2
  let vl := (Finset.univ.filter (fun v : Fin (m+m) => v ≠ a ∧ v ≠ b)).toList
  let eqz : Finset (Fin (m+m)) → {x // x ∈ Z} → Bool := fun z x => vl.all (fun v => lit z v x.1)
  let rows := (Z.filter (fun z => a ∉ z ∧ b ∉ z)).toList
  -- step 1: every row indicator
  obtain ⟨r1, s1, g1, h1⟩ := Net.foldAny (raw := raw) eqz rows (Net.empty L.length) (by
    intro z _ q _
    obtain ⟨r, gr, hr⟩ := Net.allList width q (hin q _ (Or.inr (Or.inl rfl))) vl
      (fun v x => lit z v x.1) (by
        intro v hv
        simp only [vl, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and] at hv
        exact hin q _ (hlit z v hv.1 hv.2))
    exact ⟨r, _, gr, Net.has_congr hr (fun x => rfl)⟩)
  -- step 2: their disjunction
  obtain ⟨r2, g2, h2⟩ := Net.anyList width r1 (hin r1 _ (Or.inl rfl)) rows eqz h1
  -- step 3: the 00 atom
  have key : ∀ x ∈ Z, (sameF i0 x && rows.any (fun z => vl.all (fun v => lit z v x))) =
      zF i0 x := by
    intro x hx
    by_cases hxa : a ∈ x <;> by_cases hxb : b ∈ x
    · have hs : sameF i0 x = true := by simp [-Fin.natAdd_eq_addNat, sameF, ← ha_def, ← hb_def, hxa, hxb]
      have hz : zF i0 x = false := by simp [-Fin.natAdd_eq_addNat, zF, negF, ← ha_def, ← hb_def, hxa]
      rw [hs, hz, Bool.true_and]
      rw [Bool.eq_false_iff]
      intro hany
      rw [List.any_eq_true] at hany
      obtain ⟨z, hz, hall⟩ := hany
      simp only [rows, Finset.mem_toList, Finset.mem_filter] at hz
      rw [List.all_eq_true] at hall
      apply hnot z hz.1 x hx _ hz.2.1 hz.2.2 hxa hxb
      intro v hva hvb
      have := hall v (by simp [-Fin.natAdd_eq_addNat, vl, hva, hvb])
      by_cases hvz : v ∈ z
      · simp [-Fin.natAdd_eq_addNat, lit, hvz, bitF] at this; exact ⟨fun _ => this, fun _ => hvz⟩
      · simp [-Fin.natAdd_eq_addNat, lit, hvz, negF] at this; exact ⟨fun h => absurd h hvz, fun h => absurd h this⟩
    · have hs : sameF i0 x = false := by simp [-Fin.natAdd_eq_addNat, sameF, ← ha_def, ← hb_def, hxa, hxb]
      have hz : zF i0 x = false := by simp [-Fin.natAdd_eq_addNat, zF, negF, ← ha_def, ← hb_def, hxa]
      rw [hs, hz, Bool.false_and]
    · have hs : sameF i0 x = false := by simp [-Fin.natAdd_eq_addNat, sameF, ← ha_def, ← hb_def, hxa, hxb]
      have hz : zF i0 x = false := by simp [-Fin.natAdd_eq_addNat, zF, negF, ← ha_def, ← hb_def, hxb]
      rw [hs, hz, Bool.false_and]
    · have hs : sameF i0 x = true := by simp [-Fin.natAdd_eq_addNat, sameF, ← ha_def, ← hb_def, hxa, hxb]
      have hz : zF i0 x = true := by simp [-Fin.natAdd_eq_addNat, zF, negF, ← ha_def, ← hb_def, hxa, hxb]
      rw [hs, hz, Bool.true_and, List.any_eq_true]
      refine ⟨x, by simp [-Fin.natAdd_eq_addNat, rows, hx, hxa, hxb], ?_⟩
      rw [List.all_eq_true]
      intro v _
      by_cases hvx : v ∈ x
      · simp [-Fin.natAdd_eq_addNat, lit, hvx, bitF]
      · simp [-Fin.natAdd_eq_addNat, lit, hvx, negF]
  obtain ⟨r3, g3, h3⟩ := Net.and2 width r2 _ _ (fun x => zF i0 x.1) (hin r2 _ hsame) h2
    (fun x => key x.1 x.2)
  obtain ⟨r4, g4, h4⟩ := Net.and2 width r3 _ _ (fun x => dpF i0 x.1) (hin r3 _ (hbit a))
    (hin r3 _ hnsame) (fun x => fdp i0 x.1)
  obtain ⟨r5, g5, h5⟩ := Net.and2 width r4 _ _ (fun x => dmF i0 x.1) (hin r4 _ (hbit b))
    (hin r4 _ hnsame) (fun x => fdm i0 x.1)
  obtain ⟨r6, g6, h6⟩ := Net.or2 width r5 _ _ (fun x => negF a x.1) (g5.1 _ (g4.1 _ h3)) h5
    (fun x => fna i0 x.1)
  obtain ⟨r7, g7, h7⟩ := Net.or2 width r6 _ _ (fun x => negF b x.1)
    (g6.1 _ (g5.1 _ (g4.1 _ h3))) (g6.1 _ (g5.1 _ h4)) (fun x => fnb i0 x.1)
  -- step 6: the other edges
  let jobs := (Finset.univ.filter (fun ι : Fin m × Fin 3 => ι.1 ≠ i0)).toList
  obtain ⟨r8, s8, g8, h8⟩ := Net.foldAny (raw := raw) (fun ι x => AF ι x.1) jobs r7 (by
    intro ι hι q _
    simp only [jobs, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and] at hι
    have n1 : Fin.castAdd m ι.1 ≠ a := fun e => hι (Fin.castAdd_injective m m e)
    have n2 : Fin.castAdd m ι.1 ≠ b := ca_ne_na _ _
    have n3 : Fin.natAdd m ι.1 ≠ a := fun e => ca_ne_na _ _ e.symm
    have n4 : Fin.natAdd m ι.1 ≠ b := fun e => hι (Fin.natAdd_injective m m e)
    rcases ι with ⟨j, k⟩
    fin_cases k
    · obtain ⟨r, gr, hr⟩ := Net.and2 width q _ _ (fun x => AF (j, 0) x.1)
        (hin q _ (hneg _ n1 n2)) (hin q _ (hneg _ n3 n4)) (fun x => by simp [-Fin.natAdd_eq_addNat, AF, zF])
      exact ⟨r, _, gr, hr⟩
    · obtain ⟨r, gr, hr⟩ := Net.and2 width q _ _ (fun x => AF (j, 1) x.1)
        (hin q _ (hbit (Fin.castAdd m j))) (hin q _ (hneg _ n3 n4)) (fun x => by simp [-Fin.natAdd_eq_addNat, AF, dpF])
      exact ⟨r, _, gr, hr⟩
    · obtain ⟨r, gr, hr⟩ := Net.and2 width q _ _ (fun x => AF (j, 2) x.1)
        (hin q _ (hneg _ n1 n2)) (hin q _ (hbit (Fin.natAdd m j))) (fun x => by simp [-Fin.natAdd_eq_addNat, AF, dmF])
      exact ⟨r, _, gr, hr⟩)
  refine ⟨r8.gates.length, netNeedOK L Z need _ hL0 r8 le_rfl ?_⟩
  have up7 : ∀ f, r7.has raw f → r8.has raw f := g8.1
  have up6 : ∀ f, r6.has raw f → r8.has raw f := fun f h => up7 f (g7.1 f h)
  have up5 : ∀ f, r5.has raw f → r8.has raw f := fun f h => up6 f (g6.1 f h)
  have up4 : ∀ f, r4.has raw f → r8.has raw f := fun f h => up5 f (g5.1 f h)
  have up3 : ∀ f, r3.has raw f → r8.has raw f := fun f h => up4 f (g4.1 f h)
  have hjob : ∀ j, j ≠ i0 → ∀ k, r8.has raw (fun x => AF (j, k) x.1) := by
    intro j hj k
    exact h8 (j, k) (by simp [-Fin.natAdd_eq_addNat, jobs, hj])
  intro f hf
  rcases hneed f hf with ⟨v, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · by_cases hva : v = a
    · subst hva; exact up6 _ h6
    · by_cases hvb : v = b
      · subst hvb; exact up7 _ h7
      · exact hin r8 _ (hneg v hva hvb)
  · by_cases hi : i = i0
    · subst hi; exact up3 _ h3
    · exact Net.has_congr (hjob i hi 0) (fun x => by simp [-Fin.natAdd_eq_addNat, AF])
  · by_cases hi : i = i0
    · subst hi; exact up4 _ h4
    · exact Net.has_congr (hjob i hi 1) (fun x => by simp [-Fin.natAdd_eq_addNat, AF])
  · by_cases hi : i = i0
    · subst hi; exact up5 _ h5
    · exact Net.has_congr (hjob i hi 2) (fun x => by simp [-Fin.natAdd_eq_addNat, AF])

def sig (x : Finset (Fin (m+m))) : Fin m → Bool × Bool := fun i => (dpF i x, dmF i x)

theorem xor_aux (A A' B B' P P' c c' : Bool) (hB : B = A) (hB' : B' = A')
    (e1 : Bool.xor A P = Bool.xor A' P') (e2 : Bool.xor B (Bool.xor P c) = Bool.xor B' (Bool.xor P' c')) :
    c = c' := by
  rw [hB, hB'] at e2
  cases A <;> cases A' <;> cases P <;> cases P' <;> cases c <;> cases c' <;> simp_all [-Fin.natAdd_eq_addNat]

theorem bool_eq_of_iff (a b : Bool) (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all [-Fin.natAdd_eq_addNat]

theorem xor_aux2 (A A' P : Bool) (e : Bool.xor A P = Bool.xor A' P) : A = A' := by
  cases A <;> cases A' <;> cases P <;> simp_all [-Fin.natAdd_eq_addNat]

/-- The contracted rows: at most `|Z| - m` of them. -/
theorem inj_bound (Z : Finset (Finset (Fin (m+m)))) (px py : Fin m → Finset (Fin (m+m)))
    (hpx : ∀ i, px i ∈ Z) (hpy : ∀ i, py i ∈ Z)
    (hagree : ∀ i v, v ≠ Fin.castAdd m i → v ≠ Fin.natAdd m i → (v ∈ px i ↔ v ∈ py i))
    (h00 : ∀ i, Fin.castAdd m i ∉ px i ∧ Fin.natAdd m i ∉ px i)
    (h11 : ∀ i, Fin.castAdd m i ∈ py i ∧ Fin.natAdd m i ∈ py i) :
    (Z.image sig).card + m ≤ Z.card := by
  set Q := Z.image sig with hQ
  let F : (Fin m → Bool) → Finset (Fin (m+m)) → Finset (Fin m) :=
    fun s x => Finset.univ.filter (fun k => s k = true ∧ Fin.castAdd m k ∈ x)
  let par : (Fin m → Bool) → Finset (Fin (m+m)) → Bool := fun s x => decide (Odd (F s x).card)
  have sigpair : ∀ j, sig (px j) = sig (py j) := by
    intro j
    funext i
    simp only [sig, dpF, dmF, bitF, negF]
    by_cases hij : i = j
    · subst hij
      simp [-Fin.natAdd_eq_addNat, (h00 i).1, (h00 i).2, (h11 i).1, (h11 i).2]
    · have e1 : Fin.castAdd m i ∈ px j ↔ Fin.castAdd m i ∈ py j :=
        hagree j _ (fun e => hij (Fin.castAdd_injective m m e)) (ca_ne_na _ _)
      have e2 : Fin.natAdd m i ∈ px j ↔ Fin.natAdd m i ∈ py j :=
        hagree j _ (fun e => ca_ne_na _ _ e.symm) (fun e => hij (Fin.natAdd_injective m m e))
      simp only [e1, e2]
  have parpair : ∀ s j, par s (py j) = Bool.xor (par s (px j)) (s j) := by
    intro s j
    have hj : j ∉ F s (px j) := by simp [-Fin.natAdd_eq_addNat, F, (h00 j).1]
    have hmem : ∀ k, k ≠ j → (k ∈ F s (py j) ↔ k ∈ F s (px j)) := by
      intro k hk
      have e1 : Fin.castAdd m k ∈ px j ↔ Fin.castAdd m k ∈ py j :=
        hagree j _ (fun e => hk (Fin.castAdd_injective m m e)) (ca_ne_na _ _)
      simp [-Fin.natAdd_eq_addNat, F, e1]
    by_cases hs : s j = true
    · have : F s (py j) = insert j (F s (px j)) := by
        ext k
        by_cases hk : k = j
        · subst hk; simp [-Fin.natAdd_eq_addNat, F, hs, (h11 k).1]
        · rw [hmem k hk, Finset.mem_insert]; simp [-Fin.natAdd_eq_addNat, hk]
      simp only [par, this, Finset.card_insert_of_notMem hj, Nat.odd_add_one, hs]
      by_cases ho : Odd (F s (px j)).card <;> simp [-Fin.natAdd_eq_addNat, ho]
    · have : F s (py j) = F s (px j) := by
        ext k
        by_cases hk : k = j
        · subst hk; simp [-Fin.natAdd_eq_addNat, F, hs, (h00 k).1]
        · exact hmem k hk
      simp only [par, this]
      simp [-Fin.natAdd_eq_addNat] at hs
      simp [-Fin.natAdd_eq_addNat, hs]
  let Φ : ({q // q ∈ Q} → Bool) × (Fin m → Bool) → ({x // x ∈ Z} → Bool) :=
    fun gs x => Bool.xor (gs.1 ⟨sig x.1, Finset.mem_image_of_mem _ x.2⟩) (par gs.2 x.1)
  have hinj : Function.Injective Φ := by
    rintro ⟨g, s⟩ ⟨g', s'⟩ e
    have hs : s = s' := by
      funext j
      have e1 := congrFun e ⟨px j, hpx j⟩
      have e2 := congrFun e ⟨py j, hpy j⟩
      simp only [Φ] at e1 e2
      rw [parpair, parpair] at e2
      have hq : (⟨sig (py j), Finset.mem_image_of_mem _ (hpy j)⟩ : {q // q ∈ Q}) =
          ⟨sig (px j), Finset.mem_image_of_mem _ (hpx j)⟩ := Subtype.ext (sigpair j).symm
      exact xor_aux _ _ _ _ _ _ _ _ (congrArg g hq) (congrArg g' hq) e1 e2
    subst hs
    have hg : g = g' := by
      funext t
      obtain ⟨q, hq⟩ := t
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
      have := congrFun e ⟨x, hx⟩
      simp only [Φ] at this
      exact xor_aux2 _ _ _ this
    rw [hg]
  have hc := Fintype.card_le_of_injective Φ hinj
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe,
    Fintype.card_fin] at hc
  rw [← pow_add] at hc
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hc

/-- Every keeping sample with at most `m + h` rows forces the middle-layer bound. -/
theorem necessity (m h : ℕ) (hm : 0 < m) (Z : Finset (Finset (Fin (m+m))))
    (LL : Finset (Fin (m+m)) → List (Finset (Fin (m+m)) → Bool))
    (hLL : ∀ S g, g ∈ LL S ↔ IsIn S g)
    (need : Finset (Finset (Fin (m+m)) → Bool)) (hneed : ∀ f, f ∈ need ↔ IsNeed f)
    (keeps : ∀ S p, NeedOK (LL S) Z need p ↔
      ((∀ i : Fin m, Fin.castAdd m i ∈ S ∨ Fin.natAdd m i ∈ S) ∧ m + m + 3*m - S.card ≤ p))
    (hZ : Z.card ≤ m + h) :
    2 * m + 2 + h.choose (h - h / 2) ≤ 2 ^ h := by
  -- increasing pairs
  have hC : ∀ i : Fin m, ∃ x ∈ Z, ∃ y ∈ Z,
      (∀ v, v ≠ Fin.castAdd m i → v ≠ Fin.natAdd m i → (v ∈ x ↔ v ∈ y)) ∧
      (Fin.castAdd m i ∉ x ∧ Fin.natAdd m i ∉ x) ∧ (Fin.castAdd m i ∈ y ∧ Fin.natAdd m i ∈ y) := by
    intro i
    by_contra hcon
    obtain ⟨p, hp⟩ := n2 Z i (LL (S0 i)) (hLL _) need (fun f hf => (hneed f).mp hf)
      (fun x hx y hy hag h1 h2 h3 h4 => hcon ⟨x, hx, y, hy, hag, ⟨h1, h2⟩, ⟨h3, h4⟩⟩)
    have := ((keeps _ p).mp hp).1 i
    revert this
    simp [-Fin.natAdd_eq_addNat, S0, Finset.mem_erase]
  choose px hpx py hpy hagree h00 h11 using hC
  -- atom separation
  have sepF : ∀ (ι0 : Fin m × Fin 3) (g : Finset (Fin (m+m)) → Bool),
      (IsIn Finset.univ g ∨ ∃ κ, κ ≠ ι0 ∧ g = AF κ) → ∃ x ∈ Z, g x ≠ AF ι0 x := by
    intro ι0 g hg
    by_contra hcon
    push_neg at hcon
    have hp := n1 hm Z (LL Finset.univ) (hLL _) need (fun f hf => (hneed f).mp hf) ι0 g hg hcon
    have := ((keeps _ _).mp hp).2
    simp only [Finset.card_univ, Fintype.card_fin] at this
    omega
  have hD1 : ∀ i, ∃ x ∈ Z, dpF i x = true := by
    intro i
    obtain ⟨x, hx, hne⟩ := sepF (i, 1) (fun _ => false) (Or.inl (Or.inl rfl))
    refine ⟨x, hx, ?_⟩
    simp [-Fin.natAdd_eq_addNat, AF] at hne
    simpa [-Fin.natAdd_eq_addNat] using hne
  have hD2 : ∀ i, ∃ x ∈ Z, dmF i x = true := by
    intro i
    obtain ⟨x, hx, hne⟩ := sepF (i, 2) (fun _ => false) (Or.inl (Or.inl rfl))
    refine ⟨x, hx, ?_⟩
    simp [-Fin.natAdd_eq_addNat, AF] at hne
    simpa [-Fin.natAdd_eq_addNat] using hne
  have hD3 : ∀ i j, i ≠ j → ∃ x ∈ Z, dpF j x ≠ dpF i x := by
    intro i j hij
    obtain ⟨x, hx, hne⟩ := sepF (i, 1) (AF (j, 1)) (Or.inr ⟨(j, 1), by simp [-Fin.natAdd_eq_addNat, Ne.symm hij], rfl⟩)
    exact ⟨x, hx, by simpa [-Fin.natAdd_eq_addNat, AF] using hne⟩
  have hD4 : ∀ i j, i ≠ j → ∃ x ∈ Z, dmF j x ≠ dmF i x := by
    intro i j hij
    obtain ⟨x, hx, hne⟩ := sepF (i, 2) (AF (j, 2)) (Or.inr ⟨(j, 2), by simp [-Fin.natAdd_eq_addNat, Ne.symm hij], rfl⟩)
    exact ⟨x, hx, by simpa [-Fin.natAdd_eq_addNat, AF] using hne⟩
  have hD5 : ∀ i j, ∃ x ∈ Z, dmF j x ≠ dpF i x := by
    intro i j
    obtain ⟨x, hx, hne⟩ := sepF (i, 1) (AF (j, 2)) (Or.inr ⟨(j, 2), by simp, rfl⟩)
    exact ⟨x, hx, by simpa [-Fin.natAdd_eq_addNat, AF] using hne⟩
  -- contracted rows
  have hQ := inj_bound Z px py hpx hpy hagree h00 h11
  set Q := Z.image sig with hQdef
  have hQh : Q.card ≤ h := by omega
  let T := {q // q ∈ Q} ⊕ Fin (h - Q.card)
  have hT : Fintype.card T = h := by
    simp only [T, Fintype.card_sum, Fintype.card_coe, Fintype.card_fin]
    omega
  let U : Fin m → Finset T := fun i =>
    Finset.univ.filter (fun t => Sum.elim (fun q : {q // q ∈ Q} => (q.1 i).1) (fun _ => false) t = true)
  let V : Fin m → Finset T := fun i =>
    Finset.univ.filter (fun t => Sum.elim (fun q : {q // q ∈ Q} => (q.1 i).2) (fun _ => false) t = true)
  have memU : ∀ i (x : Finset (Fin (m+m))) (hx : x ∈ Z),
      (Sum.inl ⟨sig x, Finset.mem_image_of_mem _ hx⟩ : T) ∈ U i ↔ dpF i x = true := by
    intro i x hx; simp [-Fin.natAdd_eq_addNat, U, sig]
  have memV : ∀ i (x : Finset (Fin (m+m))) (hx : x ∈ Z),
      (Sum.inl ⟨sig x, Finset.mem_image_of_mem _ hx⟩ : T) ∈ V i ↔ dmF i x = true := by
    intro i x hx; simp [-Fin.natAdd_eq_addNat, V, sig]
  have c1 : ∀ i, Disjoint (U i) (V i) := by
    intro i
    rw [Finset.disjoint_left]
    intro t ht1 ht2
    rcases t with ⟨q, hq⟩ | t
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
      rw [memU i x hx] at ht1
      rw [memV i x hx] at ht2
      simp [-Fin.natAdd_eq_addNat, dpF, dmF, bitF, negF] at ht1 ht2
      exact ht2.1 ht1.1
    · simp [-Fin.natAdd_eq_addNat, U] at ht1
  have c2 : ∀ i, U i ∪ V i ≠ Finset.univ := by
    intro i e
    have : (Sum.inl ⟨sig (px i), Finset.mem_image_of_mem _ (hpx i)⟩ : T) ∈ U i ∪ V i := by
      rw [e]; exact Finset.mem_univ _
    rw [Finset.mem_union, memU i _ (hpx i), memV i _ (hpx i)] at this
    simp [-Fin.natAdd_eq_addNat, dpF, dmF, bitF, negF, (h00 i).1, (h00 i).2] at this
  have c3 : ∀ i, (U i).Nonempty := by
    intro i
    obtain ⟨x, hx, hv⟩ := hD1 i
    exact ⟨_, (memU i x hx).mpr hv⟩
  have c4 : ∀ i, (V i).Nonempty := by
    intro i
    obtain ⟨x, hx, hv⟩ := hD2 i
    exact ⟨_, (memV i x hx).mpr hv⟩
  have c5 : ∀ i j, U i = U j → i = j := by
    intro i j e
    by_contra hij
    obtain ⟨x, hx, hne⟩ := hD3 i j hij
    have h1 := memU i x hx
    have h2 := memU j x hx
    rw [e] at h1
    exact hne (bool_eq_of_iff _ _ (h2.symm.trans h1))
  have c6 : ∀ i j, V i = V j → i = j := by
    intro i j e
    by_contra hij
    obtain ⟨x, hx, hne⟩ := hD4 i j hij
    have h1 := memV i x hx
    have h2 := memV j x hx
    rw [e] at h1
    exact hne (bool_eq_of_iff _ _ (h2.symm.trans h1))
  have c7 : ∀ i j, U i ≠ V j := by
    intro i j e
    obtain ⟨x, hx, hne⟩ := hD5 i j
    have h1 := memU i x hx
    have h2 := memV j x hx
    rw [e] at h1
    exact hne (bool_eq_of_iff _ _ (h2.symm.trans h1))
  have key := setsys (T := T) m hm U V c1 c2 c3 c4 c5 c6 c7
  rw [hT] at key
  exact key

end Nec

end PEqualNP.Outside.L_meta_53190_aux

open PEqualNP.Outside.L_meta_53190_aux in
theorem PEqualNP.Outside.L_meta_53190 : ∀ (m h : Nat), 0 < m → 2*m+2 ≤ 2^h →
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
  ∃ A : Finset W, keeps A ∧ A.card ≤ m+1+h ∧
    (2^h < 2*m + Nat.choose h (h/2) + 2 → ∀ Z : Finset W, keeps Z → m+1+h ≤ Z.card) := by
  intro m h hm hh n E W bit neg same raw need keeps
  have hbit' : ∀ v, bit v = bitF v := by
    intro v; funext x
    by_cases hv : v ∈ x <;> simp [-Fin.natAdd_eq_addNat, bit, bitF, hv]
  have hneg' : ∀ v, neg v = negF v := by
    intro v; funext x
    by_cases hv : v ∈ x <;> simp [-Fin.natAdd_eq_addNat, neg, bit, negF, hv]
  have hsame' : ∀ i : Fin m, same (Fin.castAdd m i, Fin.natAdd m i) = sameF i := by
    intro i; funext x
    by_cases h1 : Fin.castAdd m i ∈ x <;> by_cases h2 : Fin.natAdd m i ∈ x <;>
      simp [-Fin.natAdd_eq_addNat, same, bit, sameF, h1, h2]
  have mE : ∀ (P : Fin n × Fin n → Prop), (∃ e ∈ E, P e) ↔
      ∃ i : Fin m, P (Fin.castAdd m i, Fin.natAdd m i) := by
    intro P; simp [-Fin.natAdd_eq_addNat, E]
  have hraw : ∀ g, g ∈ raw ↔ ((((g = fun _ => false) ∨ g = fun _ => true) ∨ ∃ a : Fin n, bitF a = g) ∨
      ∃ i : Fin m, sameF i = g) ∨ ∃ i : Fin m, (fun x => !sameF i x) = g := by
    intro g
    simp only [raw, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
      Finset.mem_univ, true_and]
    rw [mE (fun e => same e = g), mE (fun e => (fun x => !same e x) = g)]
    simp only [hsame', hbit']
    first
    | done
    | exact Iff.rfl
  have hLmem : letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
      ∀ (S : Finset (Fin (m+m))) g, g ∈ (raw ∪ S.image neg).toList ↔ IsIn S g := by
    intro S g
    simp only [Finset.mem_toList, Finset.mem_union, Finset.mem_image]
    rw [hraw]
    simp only [hneg']
    constructor
    · intro h
      rcases h with h | ⟨u, hu, hu'⟩
      · rcases h with h | ⟨i, hi⟩
        · rcases h with h | ⟨i, hi⟩
          · rcases h with h | ⟨v, hv⟩
            · rcases h with h | h
              · exact Or.inl h
              · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (Or.inl ⟨v, hv.symm⟩))
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i, hi.symm⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, hi.symm⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨u, hu, hu'.symm⟩))))
    · intro h
      rcases h with h | h | ⟨v, hv⟩ | ⟨i, hi⟩ | ⟨i, hi⟩ | ⟨u, hu, hu'⟩
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))
      · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨v, hv.symm⟩)))
      · exact Or.inl (Or.inl (Or.inr ⟨i, hi.symm⟩))
      · exact Or.inl (Or.inr ⟨i, hi.symm⟩)
      · exact Or.inr ⟨u, hu, hu'.symm⟩
  have hneedmem : ∀ f, f ∈ need ↔ IsNeed f := by
    intro f
    simp only [need, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    rw [mE (fun e => (fun x => neg e.1 x && neg e.2 x) = f),
      mE (fun e => (fun x => bit e.1 x && neg e.2 x) = f),
      mE (fun e => (fun x => neg e.1 x && bit e.2 x) = f)]
    simp only [hneg', hbit']
    constructor
    · intro h
      rcases h with h | ⟨i, hi⟩
      · rcases h with h | ⟨i, hi⟩
        · rcases h with ⟨v, hv⟩ | ⟨i, hi⟩
          · exact Or.inl ⟨v, hv.symm⟩
          · exact Or.inr (Or.inl ⟨i, hi.symm⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨i, hi.symm⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨i, hi.symm⟩))
    · intro h
      rcases h with ⟨v, hv⟩ | ⟨i, hi⟩ | ⟨i, hi⟩ | ⟨i, hi⟩
      · exact Or.inl (Or.inl (Or.inl ⟨v, hv.symm⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨i, hi.symm⟩))
      · exact Or.inl (Or.inr ⟨i, hi.symm⟩)
      · exact Or.inr ⟨i, hi.symm⟩
  refine ⟨sampleA m h, ?_, sampleA_card m h, ?_⟩
  · intro S p
    exact keepsA m h hm hh S p _ (hLmem S) need hneedmem
  · intro hlt Z hZ
    by_contra hc
    push_neg at hc
    have key := necessity m h hm Z _ hLmem need hneedmem
      (fun S p => hZ S p) (by omega)
    rw [Nat.choose_symm (Nat.div_le_self h 2)] at key
    omega
