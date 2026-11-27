import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7907.Aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs rest : List Gate) (w : List Bool) :
    wiresFrom (gs ++ rest) w = wiresFrom rest (wiresFrom gs w) := by
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

theorem wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem prefix_val (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (wiresFrom C.gates (List.ofFn x)).getD i false

theorem val_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    val C x i.val = x i := by
  rw [val, prefix_val _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

theorem val_beyond {n : ℕ} (C : Circuit) (x : Fin n → Bool) {i : ℕ}
    (hi : n + C.gates.length ≤ i) : val C x i = false := by
  rw [val, List.getD_eq_default _ _ (by simpa [wiresFrom_length] using hi)]

def operand {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j i : ℕ) : Bool :=
  if i < j then val C x i else false

theorem val_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) {p : ℕ} {g : Gate}
    (hp : C.gates[p]? = some g) :
    val C x (n+p) = g.op.eval (g.inputs.map (operand C x (n+p))) := by
  obtain ⟨hb, heq⟩ := List.getElem?_eq_some_iff.1 hp
  have hsplit : C.gates = (C.gates.take p ++ [g]) ++ C.gates.drop (p+1) := by
    conv_lhs => rw [← List.take_append_drop (p+1) C.gates]
    rw [List.take_succ_eq_append_getElem hb, heq]
  let w := wiresFrom (C.gates.take p) (List.ofFn x)
  have hw : w.length = n+p := by
    simp [w, wiresFrom_length, List.length_take, Nat.min_eq_left hb.le]
  have hread (i : ℕ) : w.getD i false = operand C x (n+p) i := by
    by_cases hi : i < n+p
    · have hv : val C x i = w.getD i false := by
        unfold val
        conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
        exact prefix_val _ w i (hw.symm ▸ hi)
      simp only [operand, ite_eq_left hi, hv]
    · rw [operand, ite_eq_right hi, List.getD_eq_default _ _ (by omega)]
  have he : (g.inputs.map fun i => w.getD i false) = g.inputs.map (operand C x (n+p)) :=
    List.map_congr_left fun i _ => hread i
  unfold val
  conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
  change (wiresFrom (C.gates.drop (p+1))
    (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD (n+p) false = _
  rw [prefix_val _ _ _ (by simp [hw]), ← hw, he]
  simp [hw]

def Next (n : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
  a < b ∧ ∃ p g, C.gates[p]? = some g ∧ b = n+p ∧ a ∈ g.inputs

def Live (n : ℕ) (C : Circuit) (i : ℕ) : Prop :=
  ReflTransGen (Next n C) i C.output

def LNext (n : ℕ) (C : Circuit) (a b : ℕ) : Prop := Next n C a b ∧ Live n C b

def Trace (n : ℕ) (C : Circuit) (P : ℕ → Prop) (i j : ℕ) : Prop :=
  ReflTransGen (fun a b => P a ∧ LNext n C a b) i j

theorem next_le {n : ℕ} {C : Circuit} {a b : ℕ} (h : ReflTransGen (Next n C) a b) :
    a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact ih.trans h.1.le

theorem trace_le {n : ℕ} {C : Circuit} {P : ℕ → Prop} {a b : ℕ}
    (h : Trace n C P a b) : a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact ih.trans h.2.1.1.le

theorem live_before {n : ℕ} {C : Circuit} {a b : ℕ} (hn : Next n C a b) (h : Live n C b) :
    Live n C a := (ReflTransGen.single hn).trans h

theorem trace_start {n : ℕ} {C : Circuit} {P : ℕ → Prop} {a b : ℕ}
    (h : Trace n C P a b) (hb : P b) : P a := by
  rcases h.cases_head with rfl | ⟨_, hs, _⟩
  · exact hb
  · exact hs.1

theorem align {n : ℕ} {C : Circuit} {P Q : ℕ → Prop} {v b : ℕ}
    (p : Trace n C P v b)
    (unique : ∀ a j j', a < b → P a → LNext n C a j → LNext n C a j' → j = j') :
    ∀ d, Trace n C Q v d → (d < b ∧ P d) ∨ Trace n C Q b d := by
  induction p using ReflTransGen.head_induction_on with
  | refl =>
    intro d q
    exact Or.inr q
  | head hp pt ih =>
    intro d q
    have hlt := hp.2.1.1.trans_le (trace_le pt)
    rcases q.cases_head with rfl | ⟨j, hq, qt⟩
    · exact Or.inl ⟨hlt, hp.1⟩
    · have e := unique _ _ _ hlt hp.1 hp.2 hq.2
      subst j
      exact ih _ qt

theorem difference {n : ℕ} (C : Circuit) (x y : Fin n → Bool) :
    ∀ j, Live n C j → val C x j ≠ val C y j →
      ∃ i : Fin n, x i ≠ y i ∧ Trace n C (fun a => val C x a ≠ val C y a) i.val j := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj hd
    by_cases hin : j < n
    · let i : Fin n := ⟨j,hin⟩
      exact ⟨i, by simpa only [← val_input C x i, ← val_input C y i] using hd, .refl⟩
    have hb : j < n+C.gates.length := by
      by_contra! he
      exact hd ((val_beyond C x he).trans (val_beyond C y he).symm)
    obtain ⟨p, hp, rfl⟩ : ∃ p, p < C.gates.length ∧ j = n+p := ⟨j-n, by omega, by omega⟩
    let g := C.gates[p]
    have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp, rfl⟩
    have hdiff : ∃ i ∈ g.inputs, i < n+p ∧ val C x i ≠ val C y i := by
      by_contra! hn
      apply hd
      rw [val_gate C x hg, val_gate C y hg]
      apply congrArg _
      apply List.map_congr_left
      intro i hi
      by_cases hj : i < n+p
      · simp [operand, hj, hn i hi hj]
      · simp [operand, hj]
    obtain ⟨a, ha, hlt, ha'⟩ := hdiff
    have hs : Next n C a (n+p) := ⟨hlt,p,g,hg,rfl,ha⟩
    obtain ⟨i, hi, hpath⟩ := ih a hlt (live_before hs hj) ha'
    exact ⟨i, hi, hpath.tail ⟨ha',hs,hj⟩⟩

section Circ2

variable {n : ℕ} {C : Circuit}

theorem acts_mono (hC : Monotone2 C) {x y : Fin n → Bool}
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ j, val C x j = true → val C y j = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    by_cases hin : j < n
    · let i : Fin n := ⟨j, hin⟩
      simpa only [← val_input C x i, ← val_input C y i] using hxy i (by
        simpa only [← val_input C x i] using hj)
    by_cases hgt : n + C.gates.length ≤ j
    · rw [val_beyond C x hgt] at hj
      contradiction
    obtain ⟨p, hp, rfl⟩ : ∃ p, p < C.gates.length ∧ j = n+p := ⟨j-n, by omega, by omega⟩
    let g := C.gates[p]
    have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp, rfl⟩
    have hgate := (hC g (List.mem_of_getElem? hg)).1
    have hm (a : ℕ) : operand C x (n+p) a = true → operand C y (n+p) a = true := by
      by_cases ha : a < n+p
      · simp only [operand, ite_eq_left ha]
        exact ih a ha
      · simp [operand, ha]
    rw [val_gate C x hg] at hj
    rw [val_gate C y hg]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgate
    rcases hgate with h | h
    · simp only [h, GateOp.eval, List.all_map, Function.comp_apply, id, List.all_eq_true] at hj ⊢
      exact fun a ha => hm a (hj a ha)
    · simp only [h, GateOp.eval, List.any_map, Function.comp_apply, id, List.any_eq_true] at hj ⊢
      obtain ⟨a, ha, he⟩ := hj
      exact ⟨a, ha, hm a he⟩

def point (s : Finset (Fin n)) (i : Fin n) : Bool := decide (i ∈ s)

theorem point_mono {s t : Finset (Fin n)} (h : s ⊆ t) :
    ∀ i, point s i = true → point t i = true := by
  intro i hi
  simpa only [point, decide_eq_true_eq] using h (by simpa only [point, decide_eq_true_eq] using hi)

theorem point_insert {s : Finset (Fin n)} {v u : Fin n} (h : u ≠ v) :
    point (insert v s) u = point s u := by simp [point, h]

theorem influence {v : Fin n} {P : ℕ → Prop} {b j : ℕ} {x y : Fin n → Bool}
    (path : Trace n C P v.val b)
    (unique : ∀ a k k', a < b → P a → LNext n C a k → LNext n C a k' → k = k')
    (agrees : ∀ i, i ≠ v → x i = y i) (hj : Live n C j) (hd : val C x j ≠ val C y j) :
    (j < b ∧ P j) ∨ (b ≤ j ∧ val C x b ≠ val C y b) := by
  obtain ⟨i, hi, trace⟩ := difference C x y j hj hd
  have e : i = v := by
    by_contra h
    exact hi (agrees i h)
  subst i
  rcases align path unique j trace with ha | hb
  · exact Or.inl ha
  · exact Or.inr ⟨trace_le hb, trace_start hb hd⟩

theorem next_in_range {a b : ℕ} (h : Next n C a b) : b < n+C.gates.length := by
  obtain ⟨_,p,g,hg,rfl,_⟩ := h
  exact Nat.add_lt_add_left (List.getElem?_eq_some_iff.1 hg).1 n

noncomputable def living (n : ℕ) (C : Circuit) : Finset ℕ :=
  open Classical in (Finset.range (n+C.gates.length)).filter (Live n C)

theorem mem_living {w : ℕ} : w ∈ living n C ↔ w < n+C.gates.length ∧ Live n C w := by
  classical
  simp [living]

def GraphEval (C : Circuit) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ v w : Fin n, val C (point {v,w}) C.output = true ↔ G.Adj v w

variable {G : SimpleGraph (Fin n)}

theorem point_contains_edge (hC : Monotone2 C) (he : GraphEval C G)
    {u v : Fin n} {S : Finset (Fin n)} (hu : u ∈ S) (hv : v ∈ S) (edge : G.Adj u v) :
    val C (point S) C.output = true :=
  acts_mono hC (point_mono (Finset.insert_subset hu (Finset.singleton_subset_iff.mpr hv)))
    C.output ((he u v).mpr edge)

theorem point_pair_quiet (he : GraphEval C G) {v w : Fin n} (hn : ¬ G.Adj v w) :
    val C (point {v,w}) C.output = false := by
  rw [← Bool.not_eq_true, he]
  exact hn

theorem point_single_quiet (he : GraphEval C G) (v : Fin n) :
    val C (point {v}) C.output = false := by
  simpa using point_pair_quiet he (G.irrefl (v := v))

theorem input_live (he : GraphEval C G) {v u : Fin n} (hvu : G.Adj v u) :
    Live n C v.val := by
  have hx : val C (point {u}) C.output = false := point_single_quiet he u
  have hy : val C (point {v,u}) C.output = true := (he v u).2 hvu
  obtain ⟨i,hi,trace⟩ := difference C (point {u}) (point {v,u}) C.output ReflTransGen.refl
    (by rw [hx,hy]; decide)
  have ei : i=v := by
    by_contra h
    exact hi ((point_insert h).symm)
  subst i
  rcases trace.cases_head with h | ⟨b,hb,_⟩
  · rw [h]
    exact .refl
  · exact live_before hb.2.1 hb.2.2

theorem incoming_bound {j : ℕ} (hC : Monotone2 C) (hj : j ∈ living n C) :
    open Classical in
    ((living n C).filter fun i => LNext n C i j).card ≤ if j<n then 0 else 2 := by
  classical
  by_cases hi : j < n
  · rw [ite_eq_left hi]
    apply Nat.le_of_eq
    rw [Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.2
    intro i hm
    obtain ⟨_,⟨_,p,g,hg,hp,_⟩,_⟩ := Finset.mem_filter.mp hm
    omega
  rw [ite_eq_right hi]
  have hj' := (mem_living.1 hj).1
  let p := j-n
  have hp : p < C.gates.length := by dsimp [p]; omega
  have he : j=n+p := by dsimp [p]; omega
  let g := C.gates[p]
  have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp,rfl⟩
  have hsub : ((living n C).filter fun i => LNext n C i j) ⊆ g.inputs.toFinset := by
    intro a ha
    obtain ⟨_,⟨_,q,g',hg',hq,hm⟩,_⟩ := Finset.mem_filter.1 ha
    have ep : p=q := by omega
    subst q
    rw [hg] at hg'
    cases hg'
    exact List.mem_toFinset.2 hm
  exact (Finset.card_le_card hsub).trans (g.inputs.toFinset_card_le.trans
    (hC g (List.mem_of_getElem? hg)).2)

theorem live_reader {a : ℕ} (ha : Live n C a) (hneq : a ≠ C.output) :
    ∃ b, LNext n C a b := by
  rcases ha.cases_head with h | ⟨b,hb,hpath⟩
  · exact (hneq h).elim
  · exact ⟨b, hb, hpath⟩

end Circ2

section Forest

def ReachIn (A : ℕ → ℕ → Prop) : ℕ → ℕ → ℕ → Prop
  | 0, a, b => a = b
  | k+1, a, b => ∃ c, ReachIn A k a c ∧ A c b

theorem reachIn_of_rtg {A : ℕ → ℕ → Prop} {a b : ℕ} (h : ReflTransGen A a b) :
    ∃ k, ReachIn A k a b := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hbc ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k+1, _, hk, hbc⟩

noncomputable def root (A : ℕ → ℕ → Prop) (v : ℕ) : ℕ := by
  classical exact Nat.find (⟨v, ReflTransGen.refl⟩ : ∃ r, ReflTransGen A r v)

theorem root_spec (A : ℕ → ℕ → Prop) (v : ℕ) : ReflTransGen A (root A v) v := by
  classical exact Nat.find_spec (⟨v, ReflTransGen.refl⟩ : ∃ r, ReflTransGen A r v)

theorem root_min (A : ℕ → ℕ → Prop) {v r : ℕ} (h : ReflTransGen A r v) : root A v ≤ r := by
  classical exact Nat.find_min' (⟨v, ReflTransGen.refl⟩ : ∃ r, ReflTransGen A r v) h

theorem root_eq {A : ℕ → ℕ → Prop} (hs : ∀ a b, A a b → A b a) {a b : ℕ}
    (h : ReflTransGen A a b) : root A a = root A b := by
  have hsym : ∀ {a b : ℕ}, ReflTransGen A a b → ReflTransGen A b a := by
    intro a b h
    induction h with
    | refl => exact .refl
    | tail _ hbc ih => exact (ReflTransGen.single (hs _ _ hbc)).trans ih
  apply le_antisymm
  · exact root_min A ((root_spec A b).trans (hsym h))
  · exact root_min A ((root_spec A a).trans h)

noncomputable def rdist (A : ℕ → ℕ → Prop) (v : ℕ) : ℕ := by
  classical exact Nat.find (reachIn_of_rtg (root_spec A v))

theorem rdist_spec (A : ℕ → ℕ → Prop) (v : ℕ) : ReachIn A (rdist A v) (root A v) v := by
  classical exact Nat.find_spec (reachIn_of_rtg (root_spec A v))

theorem rdist_min (A : ℕ → ℕ → Prop) {v k : ℕ} (h : ReachIn A k (root A v) v) :
    rdist A v ≤ k := by
  classical exact Nat.find_min' (reachIn_of_rtg (root_spec A v)) h

theorem rtg_of_reachIn {A : ℕ → ℕ → Prop} : ∀ {k a b : ℕ}, ReachIn A k a b → ReflTransGen A a b
  | 0, _, _, h => by
    change _ = _ at h
    subst h
    exact .refl
  | _+1, _, _, ⟨_, hc, hcb⟩ => (rtg_of_reachIn hc).tail hcb

theorem root_pred {A : ℕ → ℕ → Prop} (hs : ∀ a b, A a b → A b a) {v : ℕ} (hv : root A v ≠ v) :
    ∃ c, A c v ∧ rdist A c < rdist A v := by
  have hsp := rdist_spec A v
  rcases hk : rdist A v with _ | k
  · rw [hk] at hsp
    exact (hv hsp).elim
  · rw [hk] at hsp
    obtain ⟨c, hc, hcv⟩ := hsp
    have hr : root A c = root A v := root_eq hs (ReflTransGen.single hcv)
    refine ⟨c, hcv, ?_⟩
    have := rdist_min A (v := c) (k := k) (by rw [hr]; exact hc)
    omega

theorem forest_count (V : Finset ℕ) (F : Finset (ℕ × ℕ)) (A : ℕ → ℕ → Prop)
    (hs : ∀ a b, A a b → A b a) (hF : ∀ a b, A a b → (a, b) ∈ F ∨ (b, a) ∈ F) :
    V.card ≤ F.card + (V.image (root A)).card := by
  classical
  choose! pr hpr using fun v (hv : root A v ≠ v) => root_pred hs hv
  let φ : ℕ → ℕ × ℕ := fun v => if (pr v, v) ∈ F then (pr v, v) else (v, pr v)
  have hφ : ∀ v, root A v ≠ v → φ v ∈ F := by
    intro v hv
    dsimp only [φ]
    split_ifs with h
    · exact h
    · exact (hF _ _ (hpr v hv).1).resolve_left h
  have h1 : (V.filter (fun v => root A v ≠ v)).card ≤ F.card := by
    apply Finset.card_le_card_of_injOn φ
    · intro v hv
      exact hφ v (Finset.mem_filter.1 hv).2
    · intro v hv w hw hvw
      have hv' := hpr v (Finset.mem_filter.1 hv).2
      have hw' := hpr w (Finset.mem_filter.1 hw).2
      dsimp only [φ] at hvw
      have a1 := hv'.2
      have a2 := hw'.2
      split_ifs at hvw <;> simp only [Prod.mk.injEq] at hvw
      all_goals first
        | exact hvw.2
        | exact hvw.1
        | (obtain ⟨e1, e2⟩ := hvw
           first
             | (rw [e1] at a1; rw [← e2] at a2; omega)
             | (rw [e2] at a1; rw [← e1] at a2; omega))
  have h2 : (V.filter (fun v => ¬ root A v ≠ v)).card ≤ (V.image (root A)).card := by
    apply Finset.card_le_card
    intro v hv
    obtain ⟨hvV, hr⟩ := Finset.mem_filter.1 hv
    exact Finset.mem_image.2 ⟨v, hvV, not_not.1 hr⟩
  have := Finset.card_filter_add_card_filter_not (s := V) (fun v => root A v ≠ v)
  omega

end Forest

section Regions

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} {d : ℕ}

structure Good (n : ℕ) (C : Circuit) (G : SimpleGraph (Fin n)) (d : ℕ) : Prop where
  mono : Monotone2 C
  shape : ∀ p g, C.gates[p]? = some g → ∃ a b, g.inputs = [a, b] ∧ a < b ∧ b < n + p
  eval : GraphEval C G
  two : 2 ≤ d
  deg : ∀ u : Fin n, ∃ S : Finset (Fin n), d ≤ S.card ∧ ∀ t ∈ S, G.Adj u t
  dist : ∀ u v : Fin n, u ≠ v → ∃ t, G.Adj u t ∧ ¬ G.Adj v t ∧ t ≠ v

theorem Good.nbr (H : Good n C G d) (u : Fin n) : ∃ t, G.Adj u t := by
  obtain ⟨S, hS, hA⟩ := H.deg u
  obtain ⟨t, ht⟩ : S.Nonempty := Finset.card_pos.1 (by have := H.two; omega)
  exact ⟨t, hA t ht⟩

theorem Good.two_nbrs (H : Good n C G d) (u : Fin n) :
    ∃ t t', t ≠ t' ∧ G.Adj u t ∧ G.Adj u t' := by
  obtain ⟨S, hS, hA⟩ := H.deg u
  obtain ⟨t, ht, t', ht', hne⟩ := Finset.one_lt_card.1 (by have := H.two; omega : 1 < S.card)
  exact ⟨t, t', hne, hA t ht, hA t' ht'⟩

theorem Good.live_in (H : Good n C G d) (u : Fin n) : Live n C u.val := by
  obtain ⟨t, ht⟩ := H.nbr u
  exact input_live H.eval ht

theorem gate_val (H : Good n C G d) {p : ℕ} {g : Gate} {a b : ℕ} (hg : C.gates[p]? = some g)
    (hi : g.inputs = [a, b]) (hb : b < n + p) (hab : a < b) (x : Fin n → Bool) :
    (g.op = GateOp.and ∧ val C x (n+p) = (val C x a && val C x b)) ∨
      (g.op = GateOp.or ∧ val C x (n+p) = (val C x a || val C x b)) := by
  have hop := (H.mono g (List.mem_of_getElem? hg)).1
  rw [val_gate C x hg, hi]
  have ea : operand C x (n+p) a = val C x a := by simp [operand, show a < n+p by omega]
  have eb : operand C x (n+p) b = val C x b := by simp [operand, hb]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with h | h
  · left; simp [h, GateOp.eval, ea, eb]
  · right; simp [h, GateOp.eval, ea, eb]

theorem lnext_gate (H : Good n C G d) {m h : ℕ} (hm : LNext n C m h) :
    ∃ p g a b, C.gates[p]? = some g ∧ h = n + p ∧ g.inputs = [a, b] ∧ a < b ∧ b < n + p ∧
      (m = a ∨ m = b) := by
  obtain ⟨⟨_, p, g, hg, rfl, hmem⟩, _⟩ := hm
  obtain ⟨a, b, hi, hab, hb⟩ := H.shape p g hg
  refine ⟨p, g, a, b, hg, rfl, hi, hab, hb, ?_⟩
  rw [hi] at hmem
  simpa using hmem

theorem input_lnext {p : ℕ} {g : Gate} {a b : ℕ} (hg : C.gates[p]? = some g)
    (hi : g.inputs = [a, b]) (hb : b < n + p) (hab : a < b) (hl : Live n C (n+p)) :
    LNext n C a (n+p) ∧ LNext n C b (n+p) :=
  ⟨⟨⟨by omega, p, g, hg, rfl, by simp [hi]⟩, hl⟩, ⟨⟨hb, p, g, hg, rfl, by simp [hi]⟩, hl⟩⟩

def Single (C : Circuit) {n : ℕ} (u : Fin n) (w : ℕ) : Prop :=
  ∀ v : Fin n, val C (point {v}) w = true ↔ v = u

theorem single_input (u : Fin n) : Single C u u.val := by
  intro v
  rw [val_input]
  simp [point, eq_comm]

theorem single_unique {u u' : Fin n} {w : ℕ} (h : Single C u w) (h' : Single C u' w) :
    u = u' :=
  (h' u).1 ((h u).2 rfl)

theorem single_true {u : Fin n} {w : ℕ} (h : Single C u w) : val C (point {u}) w = true :=
  (h u).2 rfl

theorem out_not_single (H : Good n C G d) (u : Fin n) : ¬ Single C u C.output := by
  intro h
  have := single_true h
  rw [point_single_quiet H.eval] at this
  exact Bool.false_ne_true this

noncomputable def Preg (n : ℕ) (C : Circuit) (u : Fin n) : Finset ℕ :=
  open Classical in
  (living n C).filter (fun w => Trace n C (Single C u) u.val w ∧ Single C u w)

theorem mem_Preg {u : Fin n} {w : ℕ} : w ∈ Preg n C u ↔
    (w < n + C.gates.length ∧ Live n C w) ∧ Trace n C (Single C u) u.val w ∧ Single C u w := by
  classical
  unfold Preg; rw [Finset.mem_filter, mem_living]

noncomputable def Zreg (n : ℕ) (C : Circuit) : Finset ℕ :=
  open Classical in (living n C).filter (fun w => ∀ v : Fin n, val C (point {v}) w = false)

theorem mem_Zreg {w : ℕ} : w ∈ Zreg n C ↔
    (w < n + C.gates.length ∧ Live n C w) ∧ ∀ v : Fin n, val C (point {v}) w = false := by
  classical
  unfold Zreg; rw [Finset.mem_filter, mem_living]

noncomputable def Dreg (n : ℕ) (C : Circuit) : Finset ℕ :=
  open Classical in (living n C).filter
    (fun w => (∃ v : Fin n, val C (point {v}) w = true) ∧ ∀ u : Fin n, w ∉ Preg n C u)

theorem mem_Dreg {w : ℕ} : w ∈ Dreg n C ↔ (w < n + C.gates.length ∧ Live n C w) ∧
    (∃ v : Fin n, val C (point {v}) w = true) ∧ ∀ u : Fin n, w ∉ Preg n C u := by
  classical
  unfold Dreg; rw [Finset.mem_filter, mem_living]

noncomputable def Edges (n : ℕ) (C : Circuit) : Finset (ℕ × ℕ) :=
  open Classical in (living n C ×ˢ living n C).filter (fun e => LNext n C e.1 e.2)

theorem mem_Edges {e : ℕ × ℕ} : e ∈ Edges n C ↔ LNext n C e.1 e.2 := by
  classical
  unfold Edges
  rw [Finset.mem_filter, Finset.mem_product, mem_living, mem_living]
  constructor
  · exact fun h => h.2
  · intro h
    have h2 := next_in_range h.1
    exact ⟨⟨⟨by have := h.1.1; omega, live_before h.1 h.2⟩, h2, h.2⟩, h⟩

noncomputable def outE (n : ℕ) (C : Circuit) (R : Finset ℕ) : Finset (ℕ × ℕ) :=
  open Classical in (Edges n C).filter (fun e => e.1 ∈ R)

noncomputable def intE (n : ℕ) (C : Circuit) (R : Finset ℕ) : Finset (ℕ × ℕ) :=
  open Classical in (Edges n C).filter (fun e => e.1 ∈ R ∧ e.2 ∈ R)

noncomputable def extE (n : ℕ) (C : Circuit) (R : Finset ℕ) : Finset (ℕ × ℕ) :=
  open Classical in (Edges n C).filter (fun e => e.1 ∈ R ∧ e.2 ∉ R)

theorem mem_outE {R : Finset ℕ} {e : ℕ × ℕ} :
    e ∈ outE n C R ↔ LNext n C e.1 e.2 ∧ e.1 ∈ R := by
  classical
  unfold outE; rw [Finset.mem_filter, mem_Edges]

theorem mem_intE {R : Finset ℕ} {e : ℕ × ℕ} :
    e ∈ intE n C R ↔ LNext n C e.1 e.2 ∧ e.1 ∈ R ∧ e.2 ∈ R := by
  classical
  unfold intE; rw [Finset.mem_filter, mem_Edges]

theorem mem_extE {R : Finset ℕ} {e : ℕ × ℕ} :
    e ∈ extE n C R ↔ LNext n C e.1 e.2 ∧ e.1 ∈ R ∧ e.2 ∉ R := by
  classical
  unfold extE; rw [Finset.mem_filter, mem_Edges]

theorem card_outE (R : Finset ℕ) :
    (outE n C R).card = (intE n C R).card + (extE n C R).card := by
  classical
  have h1 : (outE n C R).filter (fun e => e.2 ∈ R) = intE n C R := by
    ext e; simp only [Finset.mem_filter, mem_outE, mem_intE]; tauto
  have h2 : (outE n C R).filter (fun e => ¬ e.2 ∈ R) = extE n C R := by
    ext e; simp only [Finset.mem_filter, mem_outE, mem_extE]; tauto
  rw [← h1, ← h2, Finset.card_filter_add_card_filter_not]

theorem out_bound (R : Finset ℕ) (hR : ∀ w ∈ R, Live n C w) :
    R.card ≤ (outE n C R).card + 1 := by
  classical
  have hex : ∀ w ∈ R.erase C.output, ∃ b, LNext n C w b := fun w hw =>
    live_reader (hR w (Finset.mem_of_mem_erase hw)) (Finset.ne_of_mem_erase hw)
  choose! ρ hρ using hex
  have h1 : (R.erase C.output).card ≤ (outE n C R).card := by
    apply Finset.card_le_card_of_injOn (fun w => (w, ρ w))
    · intro w hw
      exact mem_outE.2 ⟨hρ w hw, Finset.mem_of_mem_erase hw⟩
    · intro w _ w' _ h
      exact congrArg Prod.fst h
  have h2 := Finset.pred_card_le_card_erase (s := R) (a := C.output)
  omega

theorem max_exit (R : Finset ℕ) (hne : R.Nonempty)
    (hR : ∀ w ∈ R, Live n C w ∧ w ≠ C.output) :
    ∃ b, LNext n C (R.max' hne) b ∧ b ∉ R := by
  obtain ⟨b, hb⟩ := live_reader (hR _ (R.max'_mem hne)).1 (hR _ (R.max'_mem hne)).2
  refine ⟨b, hb, fun hbR => ?_⟩
  have := R.le_max' b hbR
  have := hb.1.1
  omega

theorem Preg_single {u : Fin n} {w : ℕ} (h : w ∈ Preg n C u) : Single C u w :=
  (mem_Preg.1 h).2.2

theorem Preg_live {u : Fin n} {w : ℕ} (h : w ∈ Preg n C u) : Live n C w := (mem_Preg.1 h).1.2

theorem Preg_disj {u u' : Fin n} {w : ℕ} (h : w ∈ Preg n C u) (h' : w ∈ Preg n C u') :
    u = u' :=
  single_unique (Preg_single h) (Preg_single h')

theorem self_Preg (H : Good n C G d) (u : Fin n) : u.val ∈ Preg n C u :=
  mem_Preg.2 ⟨⟨by have := u.isLt; omega, H.live_in u⟩, .refl, single_input u⟩

theorem Preg_close {u : Fin n} {w h : ℕ} (hw : w ∈ Preg n C u) (hn : LNext n C w h)
    (hs : Single C u h) : h ∈ Preg n C u := by
  obtain ⟨_, ht, hsw⟩ := mem_Preg.1 hw
  exact mem_Preg.2 ⟨⟨next_in_range hn.1, hn.2⟩, ht.tail ⟨hsw, hn⟩, hs⟩

theorem trace_Preg {u : Fin n} {w : ℕ} (h : Trace n C (Single C u) u.val w) :
    Trace n C (· ∈ Preg n C u) u.val w := by
  induction h with
  | refl => exact .refl
  | tail hua hab ih =>
    refine ih.tail ⟨?_, hab.2⟩
    exact mem_Preg.2 ⟨⟨by have := next_in_range hab.2.1; have := hab.2.1.1; omega,
      live_before hab.2.1 hab.2.2⟩, hua, hab.1⟩

theorem Preg_parent {u : Fin n} {h : ℕ} (hh : h ∈ Preg n C u) (hne : h ≠ u.val) :
    ∃ a, a ∈ Preg n C u ∧ LNext n C a h := by
  obtain ⟨_, ht, _⟩ := mem_Preg.1 hh
  rcases ht.cases_tail with e | ⟨a, hua, hs, hn⟩
  · exact (hne e).elim
  · exact ⟨a, mem_Preg.2 ⟨⟨by have := next_in_range hn.1; have := hn.1.1; omega,
      live_before hn.1 hn.2⟩, hua, hs⟩, hn⟩

theorem int_bound (u : Fin n) : (Preg n C u).card ≤ (intE n C (Preg n C u)).card + 1 := by
  classical
  have hex : ∀ h ∈ (Preg n C u).erase u.val, ∃ a, a ∈ Preg n C u ∧ LNext n C a h :=
    fun h hh => Preg_parent (Finset.mem_of_mem_erase hh) (Finset.ne_of_mem_erase hh)
  choose! par hpar using hex
  have h1 : ((Preg n C u).erase u.val).card ≤ (intE n C (Preg n C u)).card := by
    apply Finset.card_le_card_of_injOn (fun h => (par h, h))
    · intro h hh
      exact mem_intE.2 ⟨(hpar h hh).2, (hpar h hh).1, Finset.mem_of_mem_erase hh⟩
    · intro h _ h' _ e
      exact congrArg Prod.snd e
  have h2 := Finset.pred_card_le_card_erase (s := Preg n C u) (a := u.val)
  omega

theorem ext_pos (H : Good n C G d) (u : Fin n) : 1 ≤ (extE n C (Preg n C u)).card := by
  have hne : (Preg n C u).Nonempty := ⟨_, self_Preg H u⟩
  obtain ⟨b, hb, hbR⟩ := max_exit (Preg n C u) hne (fun w hw =>
    ⟨Preg_live hw, fun e => out_not_single H u (e ▸ Preg_single hw)⟩)
  exact Finset.card_pos.2 ⟨((Preg n C u).max' hne, b),
    mem_extE.2 ⟨hb, (Preg n C u).max'_mem hne, hbR⟩⟩

theorem living_cover : (living n C).card ≤
    (∑ u : Fin n, (Preg n C u).card) + (Dreg n C).card + (Zreg n C).card := by
  classical
  have hsub : living n C ⊆ (Finset.univ.biUnion (Preg n C)) ∪ Dreg n C ∪ Zreg n C := by
    intro w hw
    have hw' := mem_living.1 hw
    by_cases hz : ∀ v : Fin n, val C (point {v}) w = false
    · exact Finset.mem_union_right _ (mem_Zreg.2 ⟨hw', hz⟩)
    · obtain ⟨v, hv⟩ := not_forall.1 hz
      by_cases hp : ∃ u, w ∈ Preg n C u
      · obtain ⟨u, hu⟩ := hp
        exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_biUnion.2 ⟨u, Finset.mem_univ _, hu⟩))
      · refine Finset.mem_union_left _ (Finset.mem_union_right _
          (mem_Dreg.2 ⟨hw', ⟨v, by simpa using hv⟩, not_exists.1 hp⟩))
  have h0 := Finset.card_le_card hsub
  have h1 := Finset.card_union_le (Finset.univ.biUnion (Preg n C) ∪ Dreg n C) (Zreg n C)
  have h2 := Finset.card_union_le (Finset.univ.biUnion (Preg n C)) (Dreg n C)
  have h3 := Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin n))) (t := Preg n C)
  omega

theorem edges_split :
    (∑ u : Fin n, (outE n C (Preg n C u)).card) + (outE n C (Dreg n C)).card +
      (outE n C (Zreg n C)).card ≤ (Edges n C).card := by
  classical
  let B := Finset.univ.biUnion fun u : Fin n => outE n C (Preg n C u)
  have hB : B.card = ∑ u : Fin n, (outE n C (Preg n C u)).card := by
    apply Finset.card_biUnion
    intro x _ y _ hxy
    change Disjoint (outE n C (Preg n C x)) (outE n C (Preg n C y))
    refine Finset.disjoint_left.2 fun e h1 h2 => hxy ?_
    exact Preg_disj (mem_outE.1 h1).2 (mem_outE.1 h2).2
  have d1 : Disjoint B (outE n C (Dreg n C)) := by
    refine Finset.disjoint_left.2 fun e h1 h2 => ?_
    obtain ⟨u, _, hu⟩ := Finset.mem_biUnion.1 h1
    exact (mem_Dreg.1 (mem_outE.1 h2).2).2.2 u (mem_outE.1 hu).2
  have d2 : Disjoint (B ∪ outE n C (Dreg n C)) (outE n C (Zreg n C)) := by
    refine Finset.disjoint_left.2 fun e h1 h2 => ?_
    have hz := (mem_Zreg.1 (mem_outE.1 h2).2).2
    rcases Finset.mem_union.1 h1 with h | h
    · obtain ⟨u, _, hu⟩ := Finset.mem_biUnion.1 h
      have := single_true (Preg_single (mem_outE.1 hu).2)
      rw [hz u] at this
      exact Bool.false_ne_true this
    · obtain ⟨v, hv⟩ := (mem_Dreg.1 (mem_outE.1 h).2).2.1
      rw [hz v] at hv
      exact Bool.false_ne_true hv
  have hsub : B ∪ outE n C (Dreg n C) ∪ outE n C (Zreg n C) ⊆ Edges n C := by
    intro e he
    rcases Finset.mem_union.1 he with h | h
    · rcases Finset.mem_union.1 h with h' | h'
      · obtain ⟨u, _, hu⟩ := Finset.mem_biUnion.1 h'
        exact mem_Edges.2 (mem_outE.1 hu).1
      · exact mem_Edges.2 (mem_outE.1 h').1
    · exact mem_Edges.2 (mem_outE.1 h).1
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint d2, Finset.card_union_of_disjoint d1, hB] at this
  exact this

theorem edges_le (hC : Monotone2 C) :
    (Edges n C).card ≤ 2 * ((living n C).filter (fun j => ¬ j < n)).card := by
  classical
  let W := living n C
  have hcard : (Edges n C).card = ∑ j ∈ W, (W.filter fun i => LNext n C i j).card := by
    unfold Edges
    rw [Finset.card_filter, Finset.sum_product_right]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.card_filter]
  have H : (∑ j ∈ W, (W.filter fun i => LNext n C i j).card) ≤
      ∑ j ∈ W, (if j<n then 0 else 2 : ℕ) :=
    Finset.sum_le_sum fun j hj => incoming_bound hC hj
  have e : (∑ j ∈ W, (if j<n then 0 else 2 : ℕ)) = 2 * (W.filter (fun j => ¬ j < n)).card := by
    rw [Finset.sum_ite]
    simp [Nat.mul_comm]
  rw [hcard]
  exact H.trans_eq e

theorem living_eq (H : Good n C G d) :
    (living n C).card = n + ((living n C).filter (fun j => ¬ j < n)).card := by
  classical
  have hSub : Finset.range n ⊆ living n C := by
    intro a ha
    have hi := Finset.mem_range.1 ha
    exact mem_living.2 ⟨by omega, H.live_in ⟨a, hi⟩⟩
  have h := Finset.card_sdiff_add_card_eq_card hSub
  have e : living n C \ Finset.range n = (living n C).filter (fun j => ¬ j < n) := by
    ext a; simp
  rw [e, Finset.card_range] at h
  omega

theorem gates_le : ((living n C).filter (fun j => ¬ j < n)).card ≤ C.gates.length := by
  rw [show C.gates.length = (Finset.range C.gates.length).card by simp]
  apply Finset.card_le_card_of_injOn (fun a => a-n)
  · intro a ha
    have h : a < n+C.gates.length := (mem_living.1 (Finset.mem_filter.1 ha).1).1
    have h0 : n ≤ a := Nat.le_of_not_gt (Finset.mem_filter.1 ha).2
    apply Finset.mem_range.2
    change a-n < C.gates.length
    omega
  · intro a ha b hb hab
    have h1 : n ≤ a := Nat.le_of_not_gt (Finset.mem_filter.1 ha).2
    have h2 : n ≤ b := Nat.le_of_not_gt (Finset.mem_filter.1 hb).2
    change a-n=b-n at hab
    omega

end Regions

section Terminal

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} {d : ℕ}

theorem terminal_unique (H : Good n C G d) {u : Fin n}
    (ht : (intE n C (Preg n C u)).card + (extE n C (Preg n C u)).card ≤ (Preg n C u).card)
    {w k k' : ℕ} (hw : w ∈ Preg n C u) (hk : LNext n C w k) (hk' : LNext n C w k') :
    k = k' := by
  classical
  by_contra hne
  have hex : ∀ w' ∈ Preg n C u, ∃ b, LNext n C w' b := fun w' hw' =>
    live_reader (Preg_live hw') (fun e => out_not_single H u (e ▸ Preg_single hw'))
  choose! ρ hρ using hex
  obtain ⟨k'', hk'', hne''⟩ : ∃ k'', LNext n C w k'' ∧ k'' ≠ ρ w := by
    by_cases h : k = ρ w
    · exact ⟨k', hk', fun e => hne (h.trans e.symm)⟩
    · exact ⟨k, hk, h⟩
  have hsub : insert (w, k'') ((Preg n C u).image fun w' => (w', ρ w')) ⊆
      outE n C (Preg n C u) := by
    intro e he
    rcases Finset.mem_insert.1 he with rfl | he
    · exact mem_outE.2 ⟨hk'', hw⟩
    · obtain ⟨w', hw', rfl⟩ := Finset.mem_image.1 he
      exact mem_outE.2 ⟨hρ w' hw', hw'⟩
  have hnot : (w, k'') ∉ (Preg n C u).image fun w' => (w', ρ w') := by
    intro he
    obtain ⟨w', _, he'⟩ := Finset.mem_image.1 he
    have e1 : w' = w := congrArg Prod.fst he'
    have e2 : ρ w' = k'' := congrArg Prod.snd he'
    rw [e1] at e2
    exact hne'' e2.symm
  have hinj : ((Preg n C u).image fun w' => (w', ρ w')).card = (Preg n C u).card :=
    Finset.card_image_of_injective _ (fun a b h => congrArg Prod.fst h)
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot, hinj, card_outE] at this
  omega

theorem dominator (H : Good n C G d) {u : Fin n} {P : ℕ → Prop} {g : ℕ}
    (path : Trace n C P u.val g)
    (uniq : ∀ a k k', a < g → P a → LNext n C a k → LNext n C a k' → k = k')
    (hg : Live n C g) {v : Fin n} (hvu : v ≠ u) : val C (point {v}) g = false := by
  classical
  rw [← Bool.not_eq_true]
  intro hv
  obtain ⟨t, hut, hvt, _⟩ := H.dist u v (Ne.symm hvu)
  have hx : val C (point ({t, v} : Finset (Fin n))) C.output = false :=
    point_pair_quiet H.eval (fun h => hvt h.symm)
  have hy : val C (point (insert u ({t, v} : Finset (Fin n)))) C.output = true :=
    point_contains_edge H.mono H.eval (u := u) (v := t) (by simp) (by simp) hut
  have hd := influence path uniq (x := point ({t, v} : Finset (Fin n)))
    (y := point (insert u ({t, v} : Finset (Fin n))))
    (fun i hi => (point_insert hi).symm) ReflTransGen.refl (by rw [hx, hy]; decide)
  have hgo := next_le hg
  rcases hd with h | h
  · exact absurd h.1 (by omega)
  · apply h.2
    have h1 : val C (point ({t, v} : Finset (Fin n))) g = true :=
      acts_mono H.mono (point_mono (by simp)) g hv
    have h2 : val C (point (insert u ({t, v} : Finset (Fin n)))) g = true :=
      acts_mono H.mono (point_mono (by simp)) g hv
    rw [h1, h2]

theorem terminal (H : Good n C G d) {u : Fin n}
    (ht : (intE n C (Preg n C u)).card + (extE n C (Preg n C u)).card ≤ (Preg n C u).card) :
    ∃ m a g, (∀ e ∈ extE n C (Preg n C u), e = (m, g)) ∧ Single C u m ∧ LNext n C m g ∧
      LNext n C a g ∧ a ≠ m ∧ (∀ x, LNext n C x g → x = m ∨ x = a) ∧ g ∈ Zreg n C ∧
      a ∈ Dreg n C ∧ (∀ t, G.Adj u t → val C (point {t}) a = true) := by
  classical
  have hint := int_bound (C := C) u
  have hext := ext_pos H u
  obtain ⟨e0, he0⟩ := Finset.card_eq_one.1 (show (extE n C (Preg n C u)).card = 1 by omega)
  obtain ⟨m, g⟩ := e0
  have hall : ∀ e ∈ extE n C (Preg n C u), e = (m, g) := by
    intro e he
    rw [he0] at he
    exact Finset.mem_singleton.1 he
  have hmg : (m, g) ∈ extE n C (Preg n C u) := by
    rw [he0]; exact Finset.mem_singleton_self _
  have hmgL : LNext n C m g := (mem_extE.1 hmg).1
  have hmP : m ∈ Preg n C u := (mem_extE.1 hmg).2.1
  have hgP : g ∉ Preg n C u := (mem_extE.1 hmg).2.2
  have hsm : Single C u m := Preg_single hmP
  have hgl : Live n C g := hmgL.2
  have path : Trace n C (· ∈ Preg n C u) u.val g :=
    (trace_Preg (mem_Preg.1 hmP).2.1).tail ⟨hmP, hmgL⟩
  have uniq : ∀ a k k', a < g → a ∈ Preg n C u → LNext n C a k → LNext n C a k' → k = k' :=
    fun a k k' _ ha hk hk' => terminal_unique H ht ha hk hk'
  have hZ : ∀ v : Fin n, val C (point {v}) g = false := by
    have hother : ∀ v : Fin n, v ≠ u → val C (point {v}) g = false :=
      fun v hv => dominator H path uniq hgl hv
    intro v
    by_cases hv : v = u
    · subst hv
      rw [← Bool.not_eq_true]
      intro hu
      apply hgP
      refine Preg_close hmP hmgL fun w => ⟨fun hw => ?_, fun hw => hw ▸ hu⟩
      by_contra hne
      rw [hother w hne] at hw
      exact Bool.false_ne_true hw
    · exact hother v hv
  have hgZ : g ∈ Zreg n C := mem_Zreg.2 ⟨⟨next_in_range hmgL.1, hgl⟩, hZ⟩
  obtain ⟨p, gt, i1, i2, hgt, hgp, hi, h12, hi2, hm12⟩ := lnext_gate H hmgL
  subst hgp
  have hin : ∀ x, LNext n C x (n+p) → x = i1 ∨ x = i2 := by
    intro x hx
    obtain ⟨⟨_, p', g', hg', hpp, hxm⟩, _⟩ := hx
    have hp' : p' = p := by omega
    subst hp'
    rw [hgt] at hg'
    cases hg'
    rw [hi] at hxm
    simpa using hxm
  obtain ⟨hl1, hl2⟩ := input_lnext hgt hi hi2 h12 hgl
  obtain ⟨a, ham, ha12, hal, hma⟩ : ∃ a, a ≠ m ∧ (a = i1 ∨ a = i2) ∧ LNext n C a (n+p) ∧
      ∀ x, LNext n C x (n+p) → x = m ∨ x = a := by
    rcases hm12 with rfl | rfl
    · exact ⟨i2, by omega, Or.inr rfl, hl2, hin⟩
    · exact ⟨i1, by omega, Or.inl rfl, hl1, fun x hx => (hin x hx).symm⟩
  have hand : gt.op = GateOp.and := by
    rcases gate_val H hgt hi hi2 h12 (point {u}) with h | h
    · exact h.1
    · exfalso
      have hv := h.2
      rw [hZ u] at hv
      have hm' := single_true hsm
      rcases hm12 with rfl | rfl
      · rw [hm'] at hv; simp at hv
      · rw [hm'] at hv; simp at hv
  have hT : ∀ t : Fin n, G.Adj u t → val C (point {t}) a = true := by
    intro t hut
    have hx : val C (point {t}) C.output = false := point_single_quiet H.eval t
    have hy : val C (point (insert u ({t} : Finset (Fin n)))) C.output = true :=
      point_contains_edge H.mono H.eval (u := u) (v := t) (by simp) (by simp) hut
    have agrees : ∀ i, i ≠ u →
        point ({t} : Finset (Fin n)) i = point (insert u ({t} : Finset (Fin n))) i :=
      fun i hi => (point_insert hi).symm
    have hgo := next_le hgl
    have hdg : val C (point {t}) (n+p) ≠ val C (point (insert u ({t} : Finset (Fin n)))) (n+p) := by
      rcases influence path uniq agrees ReflTransGen.refl (by rw [hx, hy]; decide) with h | h
      · exact absurd h.1 (by omega)
      · exact h.2
    have hyg : val C (point (insert u ({t} : Finset (Fin n)))) (n+p) = true := by
      cases hxg : val C (point {t}) (n+p)
      · rw [hxg] at hdg
        simpa using hdg.symm
      · exact acts_mono H.mono (point_mono (by simp)) _ hxg
    have hya : val C (point (insert u ({t} : Finset (Fin n)))) a = true := by
      rcases gate_val H hgt hi hi2 h12 (point (insert u ({t} : Finset (Fin n)))) with h | h
      · rw [h.2, Bool.and_eq_true] at hyg
        rcases ha12 with rfl | rfl
        · exact hyg.1
        · exact hyg.2
      · exfalso
        have e := h.1.symm.trans hand
        cases e
    by_contra hxa
    have hda : val C (point {t}) a ≠ val C (point (insert u ({t} : Finset (Fin n)))) a := by
      rw [hya]; exact hxa
    rcases influence path uniq agrees (live_before hal.1 hal.2) hda with h | h
    · have := hall (a, n+p) (mem_extE.2 ⟨hal, h.2, hgP⟩)
      exact ham (congrArg Prod.fst this)
    · exact absurd h.1 (by have := hal.1.1; omega)
  have haD : a ∈ Dreg n C := by
    obtain ⟨t1, t2, h12', ht1, ht2⟩ := H.two_nbrs u
    refine mem_Dreg.2 ⟨⟨by have := next_in_range hal.1; have := hal.1.1; omega,
      live_before hal.1 hal.2⟩, ⟨t1, hT t1 ht1⟩, fun u' hu' => ?_⟩
    have hs := Preg_single hu'
    exact h12' (((hs t1).1 (hT t1 ht1)).trans ((hs t2).1 (hT t2 ht2)).symm)
  exact ⟨m, a, n+p, hall, hsm, hmgL, hal, ham, hma, hgZ, haD, hT⟩

end Terminal

section Count

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} {d : ℕ}

def DAdj (n : ℕ) (C : Circuit) (x y : ℕ) : Prop :=
  x ∈ Dreg n C ∧ y ∈ Dreg n C ∧ (LNext n C x y ∨ LNext n C y x)

theorem DAdj_symm : ∀ x y, DAdj n C x y → DAdj n C y x :=
  fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩

noncomputable def Uset (n : ℕ) (C : Circuit) (r : ℕ) : Finset (Fin n) :=
  open Classical in Finset.univ.filter (fun u' => ∃ e ∈ Edges n C,
    e.1 ∈ Preg n C u' ∧ e.2 ∈ Dreg n C ∧ root (DAdj n C) e.2 = r)

theorem mem_Uset {r : ℕ} {u' : Fin n} : u' ∈ Uset n C r ↔ ∃ e ∈ Edges n C,
    e.1 ∈ Preg n C u' ∧ e.2 ∈ Dreg n C ∧ root (DAdj n C) e.2 = r := by
  classical
  unfold Uset
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem T_sub_U (H : Good n C G d) : ∀ h, h ∈ Dreg n C → ∀ v : Fin n,
    val C (point {v}) h = true → v ∈ Uset n C (root (DAdj n C) h) := by
  intro h
  induction h using Nat.strong_induction_on with
  | ind h ih =>
    intro hD v hv
    obtain ⟨⟨hlt, hl⟩, _, hnP⟩ := mem_Dreg.1 hD
    have hge : n ≤ h := by
      by_contra hh
      have hh' : h < n := by omega
      exact hnP ⟨h, hh'⟩ (self_Preg H ⟨h, hh'⟩)
    obtain ⟨p, rfl⟩ : ∃ p, h = n + p := ⟨h - n, by omega⟩
    have hp : p < C.gates.length := by omega
    obtain ⟨gt, hgt⟩ : ∃ gt, C.gates[p]? = some gt := ⟨C.gates[p], List.getElem?_eq_getElem hp⟩
    obtain ⟨i1, i2, hi, h12, hi2⟩ := H.shape p gt hgt
    obtain ⟨hl1, hl2⟩ := input_lnext hgt hi hi2 h12 hl
    have hc : ∃ c, LNext n C c (n+p) ∧ val C (point {v}) c = true := by
      rcases gate_val H hgt hi hi2 h12 (point {v}) with h' | h'
      · rw [h'.2, Bool.and_eq_true] at hv
        exact ⟨i1, hl1, hv.1⟩
      · rw [h'.2, Bool.or_eq_true] at hv
        rcases hv with hv | hv
        · exact ⟨i1, hl1, hv⟩
        · exact ⟨i2, hl2, hv⟩
    obtain ⟨c, hcL, hcv⟩ := hc
    by_cases hcP : ∃ u', c ∈ Preg n C u'
    · obtain ⟨u', hu'⟩ := hcP
      have e : v = u' := (Preg_single hu' v).1 hcv
      subst e
      exact mem_Uset.2 ⟨(c, n+p), mem_Edges.2 hcL, hu', hD, rfl⟩
    · have hcr : c < n + C.gates.length := by
        have := next_in_range hcL.1; have := hcL.1.1; omega
      have hcD : c ∈ Dreg n C :=
        mem_Dreg.2 ⟨⟨hcr, live_before hcL.1 hcL.2⟩, ⟨v, hcv⟩, not_exists.1 hcP⟩
      have hr : root (DAdj n C) c = root (DAdj n C) (n+p) :=
        root_eq DAdj_symm (ReflTransGen.single ⟨hcD, hD, Or.inl hcL⟩)
      rw [← hr]
      exact ih c hcL.1.1 hcD v hcv

theorem exit_inj (H : Good n C G d) {u u' : Fin n} {m a m' g : ℕ} (hsm : Single C u m)
    (hT : ∀ t : Fin n, G.Adj u t → val C (point {t}) a = true)
    (hx : ∀ x, LNext n C x g → x = m ∨ x = a) (hsm' : Single C u' m') (hm' : LNext n C m' g) :
    u = u' := by
  rcases hx m' hm' with rfl | rfl
  · exact single_unique hsm hsm'
  · exfalso
    obtain ⟨t1, t2, h12, ht1, ht2⟩ := H.two_nbrs u
    exact h12 (((hsm' t1).1 (hT t1 ht1)).trans ((hsm' t2).1 (hT t2 ht2)).symm)

noncomputable def pc (n : ℕ) (C : Circuit) (u : Fin n) : ℕ := (Preg n C u).card
noncomputable def ic (n : ℕ) (C : Circuit) (u : Fin n) : ℕ := (intE n C (Preg n C u)).card
noncomputable def ec (n : ℕ) (C : Circuit) (u : Fin n) : ℕ := (extE n C (Preg n C u)).card

theorem final_arith (sg n d τ X NEc Elc Se : ℤ) (hmain : sg + 1 + τ ≥ X + n + NEc)
    (hS2 : Se + Elc * d ≤ d * X + Elc * 2) (hS3 : Elc ≤ X) (hent : d * τ ≤ Se)
    (hτ : τ ≤ NEc) (hcard : NEc + Elc = n) (hd : 0 ≤ d) :
    2 * n * (d + 1) ≤ (d + 2) * (sg + 1) := by
  have hk : 0 ≤ sg + 1 - (2 * n - (τ - X + Elc)) := by linarith
  nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ d + 2) hk]

theorem main_count (H : Good n C G d) :
    2 * n * (d + 1) ≤ (d + 2) * (((living n C).filter (fun j => ¬ j < n)).card + 1) := by
  classical
  let D := Dreg n C
  let A := DAdj n C
  let NE := (Finset.univ : Finset (Fin n)).filter (fun u => ic n C u + ec n C u ≤ pc n C u)
  let El := (Finset.univ : Finset (Fin n)).filter (fun u => ¬ ic n C u + ec n C u ≤ pc n C u)
  have hNE : ∀ u, u ∈ NE ↔ ic n C u + ec n C u ≤ pc n C u := fun u =>
    ⟨fun h => (Finset.mem_filter.1 h).2, fun h => Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩⟩
  have hEl : ∀ u, u ∈ El ↔ ¬ ic n C u + ec n C u ≤ pc n C u := fun u =>
    ⟨fun h => (Finset.mem_filter.1 h).2, fun h => Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩⟩
  choose! m a g hterm using fun u (hu : u ∈ NE) => terminal H ((hNE u).1 hu)

  have hF : ∀ x y, A x y → (x, y) ∈ intE n C D ∨ (y, x) ∈ intE n C D := by
    rintro x y ⟨hx, hy, h | h⟩
    · exact Or.inl (mem_intE.2 ⟨h, hx, hy⟩)
    · exact Or.inr (mem_intE.2 ⟨h, hy, hx⟩)
  have hforest := forest_count D (intE n C D) A DAdj_symm hF
  let Rt := D.image (root A)
  let TC := NE.image (fun u => root A (a u))
  have hTC : TC ⊆ Rt := by
    intro r hr
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨_, _, _, _, _, _, _, haD, _⟩ := hterm u hu
    exact Finset.mem_image.2 ⟨a u, haD, rfl⟩
  have hτ : TC.card ≤ NE.card := Finset.card_image_le
  have hRTC : (Rt \ TC).card + TC.card = Rt.card := Finset.card_sdiff_add_card_eq_card hTC
  have hZD : ∀ w, w ∈ Zreg n C → w ∉ D := by
    intro w hz hd
    obtain ⟨v, hv⟩ := (mem_Dreg.1 hd).2.1
    rw [(mem_Zreg.1 hz).2 v] at hv
    exact Bool.false_ne_true hv

  have hcomp : ∀ r ∈ Rt, ∃ e ∈ extE n C D, root A e.1 = r := by
    intro r hr
    let K := D.filter (fun w => root A w = r)
    have hKne : K.Nonempty := by
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hr
      exact ⟨w, Finset.mem_filter.2 ⟨hw, rfl⟩⟩
    have hK : ∀ w ∈ K, Live n C w ∧ w ≠ C.output := by
      intro w hw
      have hwD := (Finset.mem_filter.1 hw).1
      refine ⟨(mem_Dreg.1 hwD).1.2, fun e => ?_⟩
      obtain ⟨v, hv⟩ := (mem_Dreg.1 hwD).2.1
      rw [e, point_single_quiet H.eval] at hv
      exact Bool.false_ne_true hv
    obtain ⟨b, hb, hbK⟩ := max_exit K hKne hK
    have hmK := Finset.mem_filter.1 (K.max'_mem hKne)
    refine ⟨(K.max' hKne, b), mem_extE.2 ⟨hb, hmK.1, fun hbD => hbK ?_⟩, hmK.2⟩
    exact Finset.mem_filter.2 ⟨hbD,
      (root_eq DAdj_symm (ReflTransGen.single ⟨hmK.1, hbD, Or.inl hb⟩)).symm.trans hmK.2⟩
  choose! ex hex using hcomp
  have hX1 : (Rt \ TC).card ≤ ((extE n C D).filter (fun e => ¬ root A e.1 ∈ TC)).card := by
    apply Finset.card_le_card_of_injOn ex
    · intro r hr
      have hr' := Finset.mem_sdiff.1 hr
      obtain ⟨he, hroot⟩ := hex r hr'.1
      exact Finset.mem_filter.2 ⟨he, by rw [hroot]; exact hr'.2⟩
    · intro r hr r' hr' heq
      have h1 := (hex r (Finset.mem_sdiff.1 hr).1).2
      have h2 := (hex r' (Finset.mem_sdiff.1 hr').1).2
      exact h1.symm.trans ((congrArg (fun e => root A e.1) heq).trans h2)
  have hX2 : NE.card ≤ ((extE n C D).filter (fun e => root A e.1 ∈ TC)).card := by
    apply Finset.card_le_card_of_injOn (fun u => (a u, g u))
    · intro u hu
      obtain ⟨_, _, _, hag, _, _, hgZ, haD, _⟩ := hterm u hu
      exact Finset.mem_filter.2 ⟨mem_extE.2 ⟨hag, haD, hZD _ hgZ⟩,
        Finset.mem_image.2 ⟨u, hu, rfl⟩⟩
    · intro u hu u' hu' heq
      have hgg : g u = g u' := congrArg Prod.snd heq
      obtain ⟨_, hsm, _, _, _, hin, _, _, hT⟩ := hterm u hu
      obtain ⟨_, hsm', hmg', _, _, _, _, _, _⟩ := hterm u' hu'
      rw [← hgg] at hmg'
      exact exit_inj H hsm hT hin hsm' hmg'
  have hX : (Rt \ TC).card + NE.card ≤ (extE n C D).card := by
    have := Finset.card_filter_add_card_filter_not (s := extE n C D) (fun e => root A e.1 ∈ TC)
    omega

  have hTU := T_sub_U H
  have hU : ∀ c ∈ TC, d ≤ (Uset n C c).card := by
    intro c hc
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨_, _, _, _, _, _, _, haD, hT⟩ := hterm u hu
    obtain ⟨S, hS, hSA⟩ := H.deg u
    exact hS.trans (Finset.card_le_card fun t ht => hTU (a u) haD t (hT t (hSA t ht)))
  let Ent := (Edges n C).filter (fun e => e.2 ∈ D ∧ root A e.2 ∈ TC ∧ ∃ u', e.1 ∈ Preg n C u')
  have hEnt1 : ∀ c ∈ TC, (Uset n C c).card ≤ (Ent.filter (fun e => root A e.2 = c)).card := by
    intro c hc
    have hpick : ∀ u' ∈ Uset n C c, ∃ e ∈ Edges n C,
        e.1 ∈ Preg n C u' ∧ e.2 ∈ D ∧ root A e.2 = c := fun u' hu' => mem_Uset.1 hu'
    choose! pk hpk using hpick
    apply Finset.card_le_card_of_injOn pk
    · intro u' hu'
      obtain ⟨h1, h2, h3, h4⟩ := hpk u' hu'
      exact Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨h1, h3, h4 ▸ hc, u', h2⟩, h4⟩
    · intro u' hu' u'' hu'' heq
      have h1 := (hpk u' hu').2.1
      have h2 := (hpk u'' hu'').2.1
      rw [heq] at h1
      exact Preg_disj h1 h2
  have hEnt2 : Ent.card = ∑ c ∈ TC, (Ent.filter (fun e => root A e.2 = c)).card :=
    Finset.card_eq_sum_card_fiberwise (fun e he => (Finset.mem_filter.1 he).2.2.1)
  have hEnt3 : Ent.card ≤ ∑ u ∈ El, ec n C u := by
    refine le_trans (Finset.card_le_card ?_) Finset.card_biUnion_le
    intro e he
    obtain ⟨heE, heD, _, u', hu'⟩ := Finset.mem_filter.1 he
    have hx : e ∈ extE n C (Preg n C u') :=
      mem_extE.2 ⟨mem_Edges.1 heE, hu', fun h => (mem_Dreg.1 heD).2.2 u' h⟩
    refine Finset.mem_biUnion.2 ⟨u', (hEl u').2 fun hterm' => ?_, hx⟩
    obtain ⟨hall, _, _, _, _, _, hgZ, _, _⟩ := hterm u' ((hNE u').2 hterm')
    rw [hall e hx] at heD
    exact hZD _ hgZ heD
  have hentries : d * TC.card ≤ ∑ u ∈ El, ec n C u := by
    have h1 : d * TC.card ≤ ∑ c ∈ TC, (Uset n C c).card := by
      calc d * TC.card = TC.card • d := by rw [smul_eq_mul, mul_comm]
        _ ≤ _ := Finset.card_nsmul_le_sum _ _ _ hU
    have h2 : ∑ c ∈ TC, (Uset n C c).card ≤ ∑ c ∈ TC, (Ent.filter (fun e => root A e.2 = c)).card :=
      Finset.sum_le_sum hEnt1
    exact h1.trans (h2.trans (hEnt2.symm.le.trans hEnt3))

  have f1 : ∑ u : Fin n, (outE n C (Preg n C u)).card + (outE n C D).card +
      (outE n C (Zreg n C)).card ≤ (Edges n C).card := edges_split
  have f1a : ∑ u : Fin n, (outE n C (Preg n C u)).card = ∑ u : Fin n, (ic n C u + ec n C u) :=
    Finset.sum_congr rfl (fun u _ => card_outE _)
  have f1b : (outE n C D).card = (intE n C D).card + (extE n C D).card := card_outE D
  have f2 : (living n C).card ≤ (∑ u : Fin n, pc n C u) + D.card + (Zreg n C).card :=
    living_cover
  have f3 : D.card ≤ (intE n C D).card + Rt.card := hforest
  have f5 : (Zreg n C).card ≤ (outE n C (Zreg n C)).card + 1 :=
    out_bound _ (fun w hw => (mem_Zreg.1 hw).1.2)
  have f6 : (Edges n C).card ≤ 2 * ((living n C).filter (fun j => ¬ j < n)).card :=
    edges_le H.mono
  have f6b : (living n C).card = n + ((living n C).filter (fun j => ¬ j < n)).card :=
    living_eq H
  have hcard : NE.card + El.card = n := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun u => ic n C u + ec n C u ≤ pc n C u)
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact this
  have hmain : ((((living n C).filter (fun j => ¬ j < n)).card : ℕ) : ℤ) + 1 +
      ((∑ u : Fin n, pc n C u : ℕ) : ℤ) + TC.card ≥
      ((∑ u : Fin n, (ic n C u + ec n C u) : ℕ) : ℤ) + n + NE.card := by
    omega

  have hz : ∀ u ∈ (Finset.univ : Finset (Fin n)), u ∉ El →
      ((ic n C u : ℤ) + ec n C u - pc n C u) = 0 := by
    intro u _ hu
    have h1 : ic n C u + ec n C u ≤ pc n C u := by
      by_contra h
      exact hu ((hEl u).2 h)
    have h2 : pc n C u ≤ ic n C u + 1 := int_bound u
    have h3 : 1 ≤ ec n C u := ext_pos H u
    omega
  have hS1 : ((∑ u : Fin n, (ic n C u + ec n C u) : ℕ) : ℤ) =
      ((∑ u : Fin n, pc n C u : ℕ) : ℤ) + ∑ u ∈ El, ((ic n C u : ℤ) + ec n C u - pc n C u) := by
    rw [Finset.sum_subset (Finset.subset_univ El) hz]
    push_cast
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun u _ => by ring)
  have hper : ∀ u ∈ El, (ec n C u : ℤ) + d ≤ d * ((ic n C u : ℤ) + ec n C u - pc n C u) + 2 := by
    intro u hu
    have h1 := (hEl u).1 hu
    have h2 : pc n C u ≤ ic n C u + 1 := int_bound u
    have h3 : 2 ≤ d := H.two
    have h4 : (0:ℤ) ≤ ((d:ℤ) - 1) * ((ic n C u : ℤ) + ec n C u - pc n C u - 1) :=
      mul_nonneg (by omega) (by omega)
    nlinarith
  have hS2 := Finset.sum_le_sum hper
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
    ← Finset.mul_sum, nsmul_eq_mul, nsmul_eq_mul] at hS2
  have hS3 := Finset.card_nsmul_le_sum El (fun u => (ic n C u : ℤ) + ec n C u - pc n C u) 1
    (fun u hu => by have := (hEl u).1 hu; omega)
  rw [nsmul_eq_mul, mul_one] at hS3
  have hentZ : (d : ℤ) * TC.card ≤ ∑ u ∈ El, (ec n C u : ℤ) := by exact_mod_cast hentries
  have hτZ : (TC.card : ℤ) ≤ NE.card := by exact_mod_cast hτ
  have hcardZ : (NE.card : ℤ) + El.card = n := by exact_mod_cast hcard
  rw [hS1] at hmain
  set X := ∑ u ∈ El, ((ic n C u : ℤ) + ec n C u - pc n C u) with hX
  set sg := ((living n C).filter (fun j => ¬ j < n)).card with hsg
  have hfin : (2 * n * (d + 1) : ℤ) ≤ (d + 2) * (sg + 1) :=
    final_arith (sg : ℤ) n d TC.card X NE.card El.card (∑ u ∈ El, (ec n C u : ℤ))
      (by linarith) hS2 hS3 hentZ hτZ hcardZ (by positivity)
  exact_mod_cast hfin

end Count

section Plane

theorem lines_through (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 2 ≤ q)
    (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb) (p : Fin N) :
    (Finset.univ.filter (fun l => I p l)).card = q + 1 := by
  have : Nonempty (Fin N) := ⟨p⟩
  choose! f hf using fun (p' : Fin N) (h : p' ≠ p) => (hu p' p h).exists
  have hfu : ∀ p' l, p' ≠ p → I p' l → I p l → f p' = l := by
    intro p' l h h1 h2
    exact (hu p' p h).unique (hf p' h) ⟨h1, h2⟩
  have hcount := Finset.card_eq_sum_card_fiberwise (s := Finset.univ.erase p)
    (t := Finset.univ.filter (fun l => I p l)) (f := f) (fun p' hp' => by
      have hne := Finset.ne_of_mem_erase hp'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hf p' hne).2⟩)
  have hfib : ∀ l ∈ Finset.univ.filter (fun l => I p l),
      ((Finset.univ.erase p).filter (fun p' => f p' = l)).card = q := by
    intro l hl'
    have hpl : I p l := (Finset.mem_filter.mp hl').2
    have e : (Finset.univ.erase p).filter (fun p' => f p' = l)
        = (Finset.univ.filter (fun p' => I p' l)).erase p := by
      ext p'
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
      constructor
      · rintro ⟨hne, hfl⟩
        exact ⟨hne, hfl ▸ (hf p' hne).1⟩
      · rintro ⟨hne, hI⟩
        exact ⟨hne, hfu p' l hne hI hpl⟩
    rw [e, Finset.card_erase_of_mem (show p ∈ Finset.univ.filter (fun p' => I p' l) from
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩), hl l]
    rfl
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hcount
  subst hN
  have h2 : q ^ 2 + q + 1 - 1 = (q + 1) * q := by
    rw [Nat.add_sub_cancel]
    ring
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < q) (hcount.symm.trans h2)

theorem left_ne_right {N : ℕ} (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro he
  have hv := congrArg Fin.val he
  simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
  have := p.isLt
  omega

def graph {N : ℕ} (I : Fin N → Fin N → Prop) : SimpleGraph (Fin (N+N)) where
  Adj u v := ∃ p l : Fin N, I p l ∧ (Fin.castAdd N p = u ∨ Fin.castAdd N p = v) ∧
    (Fin.natAdd N l = u ∨ Fin.natAdd N l = v)
  symm := ⟨by
    rintro u v ⟨p,l,h,hp,hl⟩
    exact ⟨p,l,h,hp.symm,hl.symm⟩⟩
  loopless := ⟨by
    rintro v ⟨p,l,h,hp,hl⟩
    exact left_ne_right p l ((hp.elim id id).trans (hl.elim id id).symm)⟩

theorem adj_ll {N : ℕ} (I : Fin N → Fin N → Prop) (p r : Fin N) :
    ¬ (graph I).Adj (Fin.castAdd N p) (Fin.castAdd N r) := by
  rintro ⟨a,b,_,_,h⟩
  exact h.elim (fun he => left_ne_right p b he.symm) (fun he => left_ne_right r b he.symm)

theorem adj_rr {N : ℕ} (I : Fin N → Fin N → Prop) (l m : Fin N) :
    ¬ (graph I).Adj (Fin.natAdd N l) (Fin.natAdd N m) := by
  rintro ⟨a,b,_,h,_⟩
  exact h.elim (left_ne_right a l) (left_ne_right a m)

theorem adj_lr {N : ℕ} (I : Fin N → Fin N → Prop) (p l : Fin N) :
    (graph I).Adj (Fin.castAdd N p) (Fin.natAdd N l) ↔ I p l := by
  constructor
  · rintro ⟨a,b,hab,ha,hb⟩
    have hp := Fin.castAdd_inj.mp (ha.resolve_right (left_ne_right a l))
    have hl := (Fin.natAdd_inj N).mp (hb.resolve_left (left_ne_right p b).symm)
    simpa [hp,hl] using hab
  · intro hi
    exact ⟨p,l,hi,Or.inl rfl,Or.inr rfl⟩

theorem adj_rl {N : ℕ} (I : Fin N → Fin N → Prop) (l p : Fin N) :
    (graph I).Adj (Fin.natAdd N l) (Fin.castAdd N p) ↔ I p l :=
  ((graph I).adj_comm _ _).trans (adj_lr I p l)

theorem no_square {N : ℕ} (I : Fin N → Fin N → Prop)
    (hu : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (u v a b : Fin (N+N)) (uv : u ≠ v) (ab : a ≠ b)
    (ua : (graph I).Adj u a) (ub : (graph I).Adj u b)
    (va : (graph I).Adj v a) (vb : (graph I).Adj v b) : False := by
  have rect {p r l m : Fin N} (pr : p ≠ r) (lm : l ≠ m)
      (pl : I p l) (rl : I r l) (pm : I p m) (rm : I r m) : False :=
    lm ((hu p r pr).unique ⟨pl,rl⟩ ⟨pm,rm⟩)
  induction u using Fin.addCases <;> induction v using Fin.addCases <;>
    induction a using Fin.addCases <;> induction b using Fin.addCases <;>
    simp_all only [adj_ll,adj_rr,adj_lr,adj_rl]
  all_goals first
    | exact rect (fun e => uv (congrArg (Fin.castAdd N) e)) (fun e => ab (congrArg (Fin.natAdd N) e)) ua va ub vb
    | exact rect (fun e => ab (congrArg (Fin.castAdd N) e)) (fun e => uv (congrArg (Fin.natAdd N) e)) ua ub va vb

theorem no_triangle {N : ℕ} (I : Fin N → Fin N → Prop) (x y z : Fin (N+N))
    (hxy : (graph I).Adj x y) (hyz : (graph I).Adj y z) (hxz : (graph I).Adj x z) : False := by
  induction x using Fin.addCases <;> induction y using Fin.addCases <;>
    induction z using Fin.addCases <;> simp_all only [adj_ll, adj_rr]

theorem plane_dist {N : ℕ} (I : Fin N → Fin N → Prop)
    (hu : ∀ p r : Fin N, p ≠ r → ∃! l, I p l ∧ I r l)
    (two : ∀ u : Fin (N+N), ∃ a b, a ≠ b ∧ (graph I).Adj u a ∧ (graph I).Adj u b)
    (u v : Fin (N+N)) (huv : u ≠ v) :
    ∃ t, (graph I).Adj u t ∧ ¬ (graph I).Adj v t ∧ t ≠ v := by
  obtain ⟨a, b, hab, hua, hub⟩ := two u
  by_cases ha : ¬ (graph I).Adj v a ∧ a ≠ v
  · exact ⟨a, hua, ha.1, ha.2⟩
  by_cases hb : ¬ (graph I).Adj v b ∧ b ≠ v
  · exact ⟨b, hub, hb.1, hb.2⟩
  exfalso
  have ha' : (graph I).Adj v a ∨ a = v := by
    by_contra h
    exact ha ⟨fun h' => h (Or.inl h'), fun h' => h (Or.inr h')⟩
  have hb' : (graph I).Adj v b ∨ b = v := by
    by_contra h
    exact hb ⟨fun h' => h (Or.inl h'), fun h' => h (Or.inr h')⟩
  rcases ha' with ha' | hav <;> rcases hb' with hb' | hbv
  · exact no_square I hu u v a b huv hab hua hub ha' hb'
  · exact no_triangle I u v a (hbv ▸ hub) ha' hua
  · exact no_triangle I u v b (hav ▸ hua) hb' hub
  · exact hab (hav.trans hbv.symm)

theorem plane_good {N : ℕ} (q : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1)
    (hu : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (hC : Monotone2 C)
    (hshape : ∀ p g, C.gates[p]? = some g → ∃ a b, g.inputs = [a, b] ∧ a < b ∧ b < N + N + p)
    (hInc : ∀ p l : Fin N, I p l →
      circuitFun (N + N) C (fun z => decide (z = Fin.castAdd N p ∨ z = Fin.natAdd N l)) = true)
    (hRej : ∀ x : Fin (N + N) → Bool,
      Fintype.card { l : Fin N // x (Fin.natAdd N l) = true } ≤ q →
      (¬ ∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
      circuitFun (N + N) C x = false) :
    Good (N + N) C (graph I) (q + 1) := by
  classical
  let G := graph I
  have cols (l : Fin N) : (Finset.univ.filter (fun p => I p l)).card = q + 1 := by
    rw [← Fintype.card_coe]
    refine (Fintype.card_congr (Equiv.subtypeEquivRight ?_)).trans (hline l)
    intro p; simp
  have rows := lines_through q N I hq hN cols hu
  have deg : ∀ u : Fin (N+N), ∃ S : Finset (Fin (N+N)), q + 1 ≤ S.card ∧
      ∀ t ∈ S, G.Adj u t := by
    intro u
    induction u using Fin.addCases with
    | left p =>
      refine ⟨(Finset.univ.filter (fun l => I p l)).map
        ⟨Fin.natAdd N, fun _ _ => (Fin.natAdd_inj N).mp⟩, ?_, ?_⟩
      · rw [Finset.card_map, rows p]
      · intro t ht
        obtain ⟨l, hl, rfl⟩ := Finset.mem_map.1 ht
        exact (adj_lr I p l).2 (Finset.mem_filter.1 hl).2
    | right l =>
      refine ⟨(Finset.univ.filter (fun p => I p l)).map
        ⟨Fin.castAdd N, fun _ _ => Fin.castAdd_inj.mp⟩, ?_, ?_⟩
      · rw [Finset.card_map, cols l]
      · intro t ht
        obtain ⟨p, hp, rfl⟩ := Finset.mem_map.1 ht
        exact (adj_rl I l p).2 (Finset.mem_filter.1 hp).2
  have two : ∀ u : Fin (N+N), ∃ a b, a ≠ b ∧ G.Adj u a ∧ G.Adj u b := by
    intro u
    obtain ⟨S, hS, hA⟩ := deg u
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < S.card)
    exact ⟨a, b, hab, hA a ha, hA b hb⟩
  have eval : GraphEval C G := by
    intro a b
    have hfn : point ({a, b} : Finset (Fin (N + N))) = fun z => decide (z = a ∨ z = b) := by
      funext z; simp [point]
    change circuitFun (N + N) C (point {a, b}) = true ↔ G.Adj a b
    rw [hfn]
    constructor
    · intro ht
      by_contra hnot
      have hcnt : Fintype.card { l : Fin N //
          decide (Fin.natAdd N l = a ∨ Fin.natAdd N l = b) = true } ≤ q := by
        have hle2 : (Finset.univ.filter
            (fun l : Fin N => Fin.natAdd N l = a ∨ Fin.natAdd N l = b)).card ≤ 2 := by
          have hsub : Finset.univ.filter
              (fun l : Fin N => Fin.natAdd N l = a ∨ Fin.natAdd N l = b) ⊆
              (Finset.univ.filter (fun l : Fin N => Fin.natAdd N l = a)) ∪
              (Finset.univ.filter (fun l : Fin N => Fin.natAdd N l = b)) := by
            intro l hl
            simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
            exact hl
          have hc1 : (Finset.univ.filter (fun l : Fin N => Fin.natAdd N l = a)).card ≤ 1 := by
            rw [Finset.card_le_one]
            intro l1 hl1 l2 hl2
            exact (Fin.natAdd_inj N).mp
              ((Finset.mem_filter.mp hl1).2.trans (Finset.mem_filter.mp hl2).2.symm)
          have hc2 : (Finset.univ.filter (fun l : Fin N => Fin.natAdd N l = b)).card ≤ 1 := by
            rw [Finset.card_le_one]
            intro l1 hl1 l2 hl2
            exact (Fin.natAdd_inj N).mp
              ((Finset.mem_filter.mp hl1).2.trans (Finset.mem_filter.mp hl2).2.symm)
          exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by omega))
        have hceq : Fintype.card { l : Fin N //
            decide (Fin.natAdd N l = a ∨ Fin.natAdd N l = b) = true } =
            (Finset.univ.filter
              (fun l : Fin N => Fin.natAdd N l = a ∨ Fin.natAdd N l = b)).card := by
          rw [← Fintype.card_coe]
          apply Fintype.card_congr
          apply Equiv.subtypeEquivRight
          intro l; simp
        omega
      have hno : ¬ ∃ p l : Fin N, I p l ∧
          decide (Fin.castAdd N p = a ∨ Fin.castAdd N p = b) = true ∧
          decide (Fin.natAdd N l = a ∨ Fin.natAdd N l = b) = true := by
        rintro ⟨p, l, hpl, hp, hl⟩
        simp only [decide_eq_true_eq] at hp hl
        exact hnot ⟨p, l, hpl, hp, hl⟩
      have hf := hRej (fun z => decide (z = a ∨ z = b)) hcnt hno
      rw [hf] at ht
      exact Bool.false_ne_true ht
    · rintro ⟨p, l, hpl, hp, hl⟩
      have hset : (fun z : Fin (N + N) => decide (z = a ∨ z = b)) =
          (fun z => decide (z = Fin.castAdd N p ∨ z = Fin.natAdd N l)) := by
        funext z
        have hne : Fin.castAdd N p ≠ Fin.natAdd N l := left_ne_right p l
        rcases hp with rfl | rfl <;> rcases hl with h2 | h2
        · exact (hne h2.symm).elim
        · subst h2; rfl
        · subst h2; simp [or_comm]
        · exact (hne h2.symm).elim
      rw [hset]
      exact hInc p l hpl
  exact ⟨hC, hshape, eval, by omega, deg, plane_dist I hu two⟩

theorem plane_arith (q N s : ℕ) (hq : 300 ≤ q) (hq' : q ≤ 399) (hN : N = q ^ 2 + q + 1)
    (h : 4 * N * (q + 2) ≤ (q + 3) * (s + 1)) : N * q ≤ 100 * s := by
  by_contra hc
  have hc' : 100 * s + 1 ≤ N * q := Nat.lt_of_not_le hc
  have h1 : (4 * N * (q + 2) : ℤ) ≤ (q + 3) * (s + 1) := by exact_mod_cast h
  have h2 : (100 * s + 1 : ℤ) ≤ N * q := by exact_mod_cast hc'
  have hNz : (N : ℤ) = q ^ 2 + q + 1 := by exact_mod_cast hN
  have hqz : (300 : ℤ) ≤ q := by exact_mod_cast hq
  have hqz' : (q : ℤ) ≤ 399 := by exact_mod_cast hq'
  have hN0 : (0 : ℤ) ≤ N := by positivity
  have p1 := mul_le_mul_of_nonneg_left h2 (by linarith : (0:ℤ) ≤ q + 3)
  have p2 := mul_nonneg (mul_nonneg hN0 (by linarith : (0:ℤ) ≤ 399 - q))
    (by linarith : (0:ℤ) ≤ q + 2)
  have p3 := mul_le_mul hqz hqz (by norm_num) (by linarith)
  nlinarith [p1, p2, p3]

theorem plane_main (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hq : 300 ≤ q) (hq' : q ≤ 399) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1)
    (hu : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (hC : Monotone2 C)
    (hshape : ∀ p g, C.gates[p]? = some g → ∃ a b, g.inputs = [a, b] ∧ a < b ∧ b < N + N + p)
    (hInc : ∀ p l : Fin N, I p l →
      circuitFun (N + N) C (fun z => decide (z = Fin.castAdd N p ∨ z = Fin.natAdd N l)) = true)
    (hRej : ∀ x : Fin (N + N) → Bool,
      Fintype.card { l : Fin N // x (Fin.natAdd N l) = true } ≤ q →
      (¬ ∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
      circuitFun (N + N) C x = false) :
    N * q ≤ 100 * C.size := by
  have H := plane_good q I C (by omega) hN hline hu hC hshape hInc hRej
  have hm := main_count H
  have hs := gates_le (n := N + N) (C := C)
  have h4 : 4 * N * (q + 2) ≤ (q + 3) * (C.size + 1) :=
    calc 4 * N * (q + 2) = 2 * (N + N) * (q + 1 + 1) := by ring
      _ ≤ (q + 1 + 2) * (((living (N + N) C).filter (fun j => ¬ j < N + N)).card + 1) := hm
      _ ≤ (q + 3) * (C.size + 1) := Nat.mul_le_mul (le_of_eq (by ring)) (Nat.add_le_add_right hs 1)
  exact plane_arith q N C.size hq hq' hN h4

end Plane

end PEqualNP.Outside.L_meta_7907.Aux

theorem PEqualNP.Outside.L_meta_7907 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (300 : ℕ) ≤ x1 → x1 ≤ (399 : ℕ) → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) → (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) → PEqualNP.MetaComplexity.Monotone2 x5 → x2 + x2 ≤ x5.output → x5.output < x2 + x2 + x5.size → (∃ (x14 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x5.output - (x2 + x2)]? = Option.some x14 ∧ x14.op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ (x15 : ℕ) (x16 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x15]? = Option.some x16 → ∃ (x18 : ℕ) (x19 : ℕ), x16.inputs = [x18, x19] ∧ x18 < x19 ∧ x19 < x2 + x2 + x15) → (∀ (x16 x17 : Fin x2), x3 x16 x17 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x19 : Fin (x2 + x2)) => Decidable.decide (x19 = Fin.castAdd x2 x16 ∨ x19 = Fin.natAdd x2 x17)) = Bool.true) → (∀ (x17 : Fin (x2 + x2) → Bool), Fintype.card { x18 : Fin x2 // x17 (Fin.natAdd x2 x18) = Bool.true } ≤ x1 → (¬∃ (x19 : Fin x2) (x20 : Fin x2), x3 x19 x20 ∧ x17 (Fin.castAdd x2 x19) = Bool.true ∧ x17 (Fin.natAdd x2 x20) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x17 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  intro x1 x2 x3 _ x5 hq hq' hN hline hu hC _ _ _ hshape hInc hRej
  exact PEqualNP.Outside.L_meta_7907.Aux.plane_main x1 x2 x3 x5 hq hq' hN hline hu hC hshape
    hInc hRej
