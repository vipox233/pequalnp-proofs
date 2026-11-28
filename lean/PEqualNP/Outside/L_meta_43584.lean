import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_43584

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev X := Fin 6 → Bool
abbrev F := X → Bool

def Cst (f : F) : Prop := ∃ b, f = fun _ => b

def Av (s : Set F) (f : F) : Prop := Cst f ∨ ∃ u ∈ s, f = u ∨ f = fun x => !u x

def comb (t : Bool) (a b : F) : F := fun x => if t then a x && b x else a x || b x

def rs (i : Fin 6) (c : Bool) (f : F) : F := fun x => f (Function.update x i c)

def Ind (i : Fin 6) (f : F) : Prop := ∀ x b, f (Function.update x i b) = f x

def Smp (i : Fin 6) (c : Bool) (f : F) : Prop := Ind i f ∨ Cst (rs i c f)

def LI (i : Fin 6) (f : F) : Prop := Ind i f ∨ ∃ e, f = fun x => xor (x i) e

inductive Prog : Set F → F → ℕ → Prop where
  | done {s f} (h : Av s f) : Prog s f 0
  | gate {s f a b k} (t : Bool) (ha : Av s a) (hb : Av s b)
      (tail : Prog (insert (comb t a b) s) f k) : Prog s f (k + 1)

theorem av_mem {s : Set F} {f} (h : f ∈ s) : Av s f := Or.inr ⟨f, h, Or.inl rfl⟩

theorem av_ins {s : Set F} {f} (g) (h : Av s f) : Av (insert g s) f := by
  rcases h with h | ⟨u, hu, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨u, Set.mem_insert_of_mem _ hu, h⟩

theorem av_not {s : Set F} {f} (h : Av s f) : Av s (fun x => !f x) := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · exact Or.inl ⟨!b, rfl⟩
  · exact Or.inr ⟨_, hu, Or.inr rfl⟩
  · exact Or.inr ⟨u, hu, Or.inl (by funext x; simp)⟩

theorem av_rs {s t : Set F} {i c} (hs : ∀ u ∈ s, Av t (rs i c u)) {f} (h : Av s f) :
    Av t (rs i c f) := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · exact Or.inl ⟨b, rfl⟩
  · exact hs _ hu
  · exact av_not (hs _ hu)

theorem av_cheap {s : Set F} (t) {a b : F} (ha : Av s a) (hb : Av s b) (h : Cst a ∨ Cst b) :
    Av s (comb t a b) := by
  rcases h with ⟨e, rfl⟩ | ⟨e, rfl⟩
  · by_cases h : e = t
    · subst h
      rw [show comb e (fun _ => e) b = b by funext x; cases e <;> simp [comb]]
      exact hb
    · exact Or.inl ⟨e, by funext x; cases t <;> cases e <;> simp_all [comb]⟩
  · by_cases h : e = t
    · subst h
      rw [show comb e a (fun _ => e) = a by funext x; cases e <;> simp [comb]]
      exact ha
    · exact Or.inl ⟨e, by funext x; cases t <;> cases e <;> simp_all [comb]⟩

theorem smp_av {s : Set F} {i c} (hs : ∀ u ∈ s, Smp i c u) {f} (h : Av s f) : Smp i c f := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · exact Or.inl fun _ _ => rfl
  · exact hs _ hu
  · rcases hs _ hu with h | ⟨b, h⟩
    · exact Or.inl fun x b => congrArg not (h x b)
    · exact Or.inr ⟨!b, by funext x; exact congrArg not (congrFun h x)⟩

theorem li_av {s : Set F} {i} (hs : ∀ u ∈ s, LI i u) {f} (h : Av s f) : LI i f := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · exact Or.inl fun _ _ => rfl
  · exact hs _ hu
  · rcases hs _ hu with h | ⟨e, rfl⟩
    · exact Or.inl fun x b => congrArg not (h x b)
    · exact Or.inr ⟨!e, by funext x; cases e <;> simp⟩

theorem restrict {i : Fin 6} {c : Bool} {s : Set F} {f k} (p : Prog s f k) :
    ∀ t : Set F, (∀ u ∈ s, Av t (rs i c u)) →
    ∃ j ≤ k, Prog t (rs i c f) j ∧ (j = k → (∀ u ∈ s, Smp i c u) → Smp i c f) := by
  induction p with
  | done h => exact fun t hs => ⟨0, le_rfl, .done (av_rs hs h), fun _ h' => smp_av h' h⟩
  | @gate s f a b k tag ha hb tail ih =>
    intro t hs
    have pa := av_rs hs ha
    have pb := av_rs hs hb
    by_cases hc : Cst (rs i c a) ∨ Cst (rs i c b)
    · obtain ⟨j, hj, q, _⟩ := ih t (by
        intro v hv
        rcases Set.mem_insert_iff.mp hv with rfl | hu
        · exact av_cheap tag pa pb hc
        · exact hs _ hu)
      exact ⟨j, by omega, q, fun he => by omega⟩
    · obtain ⟨j, hj, q, act⟩ := ih (insert (comb tag (rs i c a) (rs i c b)) t) (by
        intro v hv
        rcases Set.mem_insert_iff.mp hv with rfl | hu
        · exact av_mem (Set.mem_insert _ _)
        · exact av_ins _ (hs _ hu))
      refine ⟨j + 1, by omega, .gate tag pa pb q, fun he ss => act (by omega) ?_⟩
      intro u hu
      rcases Set.mem_insert_iff.mp hu with rfl | hu
      · have sa := (smp_av ss ha).resolve_right (fun h => hc (.inl h))
        have sb := (smp_av ss hb).resolve_right (fun h => hc (.inr h))
        exact Or.inl fun x e => by simp only [comb, sa x e, sb x e]
      · exact ss _ hu

theorem strict {i : Fin 6} {c : Bool} {s : Set F} {f k} (p : Prog s f k) (t : Set F)
    (hs : ∀ u ∈ s, Av t (rs i c u)) (hi : ∀ u ∈ s, Smp i c u) (hf : ¬ Smp i c f) :
    ∃ j, j + 1 ≤ k ∧ Prog t (rs i c f) j := by
  obtain ⟨j, hj, q, h⟩ := restrict p t hs
  exact ⟨j, lt_of_le_of_ne hj (fun he => hf (h he hi)), q⟩

theorem li_smp {i c f} (h : LI i f) : Smp i c f := by
  rcases h with h | ⟨e, rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨xor c e, by funext x; simp [rs]⟩

theorem kill {i : Fin 6} {t : Bool} {a b : F} (h : (∃ e, a = fun x => xor (x i) e) ∨
    ∃ e, b = fun x => xor (x i) e) : ∃ c, Cst (rs i c (comb t a b)) := by
  rcases h with ⟨e, rfl⟩ | ⟨e, rfl⟩
  · refine ⟨xor e (!t), !t, ?_⟩
    funext x
    cases t <;> cases e <;> simp [rs, comb]
  · refine ⟨xor e (!t), !t, ?_⟩
    funext x
    cases t <;> cases e <;> simp [rs, comb]

theorem double {i : Fin 6} {s : Set F} {f k} (p : Prog s f k) (hs : ∀ u ∈ s, LI i u)
    (hf : ∀ c, ¬ Smp i c f) :
    ∃ c, ∀ t : Set F, (∀ u ∈ s, Av t (rs i c u)) → ∃ j, j + 2 ≤ k ∧ Prog t (rs i c f) j := by
  induction p with
  | done h => exact absurd (li_smp (li_av hs h)) (hf true)
  | @gate s f a b k tag ha hb tail ih =>
    by_cases hl : (∃ e, a = fun x => xor (x i) e) ∨ ∃ e, b = fun x => xor (x i) e
    · obtain ⟨c, hc⟩ := kill (t := tag) hl
      refine ⟨c, fun t ht => ?_⟩
      obtain ⟨j, hj, q⟩ := strict tail t (by
        intro u hu
        rcases Set.mem_insert_iff.mp hu with rfl | hu
        · exact Or.inl hc
        · exact ht _ hu) (by
        intro u hu
        rcases Set.mem_insert_iff.mp hu with rfl | hu
        · exact Or.inr hc
        · exact li_smp (hs _ hu)) (hf c)
      exact ⟨j, by omega, q⟩
    · have ia := (li_av hs ha).resolve_right (fun h => hl (.inl h))
      have ib := (li_av hs hb).resolve_right (fun h => hl (.inr h))
      obtain ⟨c, hc⟩ := ih (by
        intro u hu
        rcases Set.mem_insert_iff.mp hu with rfl | hu
        · exact Or.inl fun x e => by simp only [comb, ia x e, ib x e]
        · exact hs _ hu) hf
      refine ⟨c, fun t ht => ?_⟩
      obtain ⟨j, hj, q⟩ := hc (insert (comb tag (rs i c a) (rs i c b)) t) (by
        intro u hu
        rcases Set.mem_insert_iff.mp hu with rfl | hu
        · exact av_mem (Set.mem_insert _ _)
        · exact av_ins _ (ht _ hu))
      exact ⟨j + 1, by omega, .gate tag (av_rs ht ha) (av_rs ht hb) q⟩

def stock : Set F := Set.range fun (i : Fin 6) (x : X) => x i

theorem stock_li (i) : ∀ u ∈ stock, LI i u := by
  rintro _ ⟨j, rfl⟩
  by_cases h : j = i
  · subst h
    exact Or.inr ⟨false, by simp⟩
  · exact Or.inl fun x b => by simp [Function.update_of_ne h]

theorem stock_rs (i c) : ∀ u ∈ stock, Av stock (rs i c u) := by
  rintro _ ⟨j, rfl⟩
  by_cases h : j = i
  · subst h
    exact Or.inl ⟨c, by funext x; simp [rs]⟩
  · exact Or.inr ⟨_, ⟨j, rfl⟩, Or.inl (by funext x; simp [rs, Function.update_of_ne h])⟩

def pt (n : ℕ) : X := fun i => n.testBit i

theorem good_at {i c f} (a b d : ℕ)
    (h : (f (Function.update (pt a) i true) != f (pt a)) &&
        (rs i c f (pt b) != rs i c f (pt d)) = true) : ¬ Smp i c f := by
  simp only [Bool.and_eq_true, bne_iff_ne] at h
  obtain ⟨ha, hb⟩ := h
  rintro (hi | ⟨v, e⟩)
  · exact ha (hi _ _)
  · rw [e] at hb
    simp at hb

def Low (n : ℕ) (f : F) : Prop := ∀ k, Prog stock f k → n ≤ k

theorem zero (f : F) : Low 0 f := fun _ _ => Nat.zero_le _

theorem one {n f} (i c) (h : ¬ Smp i c f) (t : Low n (rs i c f)) : Low (n + 1) f := by
  intro k p
  obtain ⟨j, hj, q⟩ := strict p stock (stock_rs i c) (fun u hu => li_smp (stock_li i u hu))
    h
  have := t j q
  omega

theorem two {n f} (i) (h0 : ¬ Smp i false f) (h1 : ¬ Smp i true f)
    (t0 : Low n (rs i false f)) (t1 : Low n (rs i true f)) : Low (n + 2) f := by
  intro k p
  obtain ⟨c, hc⟩ := double p (stock_li i) (by
    intro c
    cases c
    · exact h0
    · exact h1)
  obtain ⟨j, hj, q⟩ := hc stock (stock_rs i c)
  cases c
  · have := t0 j q
    omega
  · have := t1 j q
    omega

def rd (w : List F) (i : ℕ) : F := fun x => (w.map fun f => f x).getD i false

def gv (w : List F) (g : Gate) : F := fun x => g.op.eval (g.inputs.map fun i => rd w i x)

theorem rd_av {s : Set F} {w : List F} (hw : ∀ u ∈ w, Av s u) (i : ℕ) : Av s (rd w i) := by
  by_cases h : i < w.length
  · have e : rd w i = w[i] := by funext x; simp [rd, h]
    rw [e]
    exact hw _ (List.getElem_mem h)
  · exact Or.inl ⟨false, by funext x; simp [rd, Nat.le_of_not_lt h]⟩

theorem gv_av {s : Set F} {w : List F} (hw : ∀ u ∈ w, Av s u) (g : Gate)
    (hop : g.op = .and ∨ g.op = .or ∨ g.op = .not) (hl : g.inputs.length ≤ 2) :
    Av s (gv w g) ∨ (g.op ≠ .not ∧ ∃ t a b, Av s a ∧ Av s b ∧ gv w g = comb t a b) := by
  obtain ⟨op, args⟩ := g
  simp only at hop hl
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨k, r⟩⟩⟩
  · left
    exact Or.inl ⟨op.eval [], by funext x; simp [gv]⟩
  · left
    rcases hop with rfl | rfl | rfl
    · rw [show gv w ⟨.and, [i]⟩ = rd w i by funext x; simp [gv, GateOp.eval]]
      exact rd_av hw i
    · rw [show gv w ⟨.or, [i]⟩ = rd w i by funext x; simp [gv, GateOp.eval]]
      exact rd_av hw i
    · rw [show gv w ⟨.not, [i]⟩ = fun x => !rd w i x by funext x; simp [gv, GateOp.eval]]
      exact av_not (rd_av hw i)
  · rcases hop with rfl | rfl | rfl
    · exact Or.inr ⟨by simp, true, _, _, rd_av hw i, rd_av hw j,
        by funext x; simp [gv, GateOp.eval, comb]⟩
    · exact Or.inr ⟨by simp, false, _, _, rd_av hw i, rd_av hw j,
        by funext x; simp [gv, GateOp.eval, comb]⟩
    · left
      rw [show gv w ⟨.not, [i, j]⟩ = fun x => !rd w i x by funext x; simp [gv, GateOp.eval]]
      exact av_not (rd_av hw i)
  · simp at hl

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false

theorem toProg (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) (o : ℕ) :
    ∀ (w : List F) (s : Set F), (∀ u ∈ w, Av s u) →
    ∃ k ≤ (gs.filter fun g => !isNot g).length,
      Prog s (rd (gs.foldl (fun w g => w ++ [gv w g]) w) o) k := by
  induction gs with
  | nil => exact fun w s hw => ⟨0, le_rfl, .done (rd_av hw o)⟩
  | cons g gs ih =>
    intro w s hw
    have hg' := hg g (by simp)
    have ih := ih fun v hv => hg v (by simp [hv])
    have hlen : (gs.filter fun g => !isNot g).length ≤
        ((g :: gs).filter fun g => !isNot g).length := by
      rw [List.filter_cons]
      split <;> simp
    rcases gv_av hw g hg'.1 hg'.2 with h | ⟨hn, t, a, b, ha, hb, e⟩
    · obtain ⟨k, hk, p⟩ := ih (w ++ [gv w g]) s (by
        intro u hu
        rcases List.mem_append.mp hu with h' | h'
        · exact hw _ h'
        · rw [List.mem_singleton.mp h']
          exact h)
      exact ⟨k, hk.trans hlen, p⟩
    · obtain ⟨k, hk, p⟩ := ih (w ++ [gv w g]) (insert (comb t a b) s) (by
        intro u hu
        rcases List.mem_append.mp hu with h' | h'
        · exact av_ins _ (hw _ h')
        · rw [List.mem_singleton.mp h', e]
          exact av_mem (Set.mem_insert _ _))
      refine ⟨k + 1, ?_, .gate t ha hb p⟩
      have : isNot g = false := by
        rcases hg'.1 with h | h | h
        · simp [isNot, h]
        · simp [isNot, h]
        · exact absurd h hn
      simp [this]
      simpa using hk

theorem fold_eval (gs : List Gate) (x : X) : ∀ w : List F,
    (gs.foldl (fun w g => w ++ [gv w g]) w).map (fun f => f x) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (w.map fun f => f x) := by
  induction gs with
  | nil => exact fun _ => rfl
  | cons g gs ih =>
    intro w
    simp only [List.foldl_cons, ih, List.map_append, List.map_cons, List.map_nil]
    rfl

theorem all_not_not {n : ℕ} {f : F} (hl : Low n f) (gs : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : gs.length ≤ n)
    (he : ∀ x : X, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = f x) :
    ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  obtain ⟨k, hk, p⟩ := toProg gs hg o
    (List.ofFn fun (i : Fin 6) (x : X) => x i) stock (by
      intro u hu
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
      exact av_mem ⟨i, rfl⟩)
  have e : rd (gs.foldl (fun w g => w ++ [gv w g])
      (List.ofFn fun (i : Fin 6) (x : X) => x i)) o = f := by
    funext x
    rw [← he x, rd, fold_eval, List.map_ofFn]
    rfl
  rw [e] at p
  have h := hl k p
  have hle := List.length_filter_le (fun g => !isNot g) gs
  have hall : ∀ g ∈ gs, (!isNot g) = true := by
    rw [← List.length_filter_eq_length_iff]
    omega
  intro g hm
  have h2 := hall g hm
  refine ⟨?_, (hg g hm).2⟩
  rcases (hg g hm).1 with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · simp [isNot, h] at h2

namespace CoreSearch

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 128

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 64 := ((x >>> 64) ^^^ x).setWidth 64
def cuts (ws : List W) : BitVec 64 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 64) ++ (0 : BitVec 64)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 64) (w : W) : Prop :=
  w.getLsbD (64+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 64) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 64+i.val < 128 := by omega
  have hi' : i.val < 128 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 64) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 64)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    if w == a || w == b then false else
      let v := sep w ||| base
      ((v == -1) && next extra (w :: r)) ||
      ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                         ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
      ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hza : z ≠ a) (hzb : z ≠ b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  have hguard : (z == a || z == b) = false := by simp [hza,hzb]
  simp only [hguard, Bool.false_eq_true, ite_false]
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        have hza : z ≠ a := by
          intro eq
          exact hout (List.mem_toFinset.mpr (perm.mem_iff.mpr (by simp [eq])))
        have hzb : z ≠ b := by
          intro eq
          exact hout (List.mem_toFinset.mpr (perm.mem_iff.mpr (by simp [eq])))
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hza hzb hk (by omega) (by omega) (cuts_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) ws

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', optimized_complete hg n ws _ hnd (by omega : n+1-ws.length+ws.length=n+1) hl']⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 128 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 128)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def natSep (w : Nat) : Nat := ((w >>> 64) ^^^ w) % (2 ^ 64)

private def natCuts (ws : List Nat) : Nat := ws.foldr (fun w v => natSep w ||| v) 0

private def natOps (x y : Nat) : List Nat :=
  [x &&& y, x ||| y, x &&& ((2 ^ 128 - 1) - y), y &&& ((2 ^ 128 - 1) - x)]

private def natChoice (extra : Nat) (next : Nat → List Nat → Bool) (a b : Nat) (r : List Nat) (w : Nat) : Bool :=
    if w == a || w == b then false else
      let v := natSep w ||| natCuts r
      ((v == 18446744073709551615) && next extra (w :: r)) ||
      ((extra != 0) && (((v ||| natSep a == 18446744073709551615) && next (extra - 1) (w :: a :: r)) ||
                         ((v ||| natSep b == 18446744073709551615) && next (extra - 1) (w :: b :: r)))) ||
      ((extra ≥ 2) && (v ||| natSep a ||| natSep b == 18446744073709551615) && next (extra - 2) (w :: a :: b :: r))

private def natDispatch (extra : Nat) (next : Nat → List Nat → Bool) (a b : Nat) (r : List Nat) : Bool :=
  (natOps a b).any (natChoice extra next a b r)

private def natOptimized : Nat → Nat → List Nat → Bool
  | 0, _, ws => (ws == [((2 ^ 64 - 1) * 2 ^ 64)] || ws == [18446744073709551615])
  | k + 1, extra, ws => (ws == [((2 ^ 64 - 1) * 2 ^ 64)] || ws == [18446744073709551615]) ||
    (pairs ws).any (fun (a, b, r) => natDispatch extra (natOptimized k) a b r)

def replay (n : Nat) (roots : List Nat) : Bool :=
  roots.sublists.any fun ws =>
    decide (ws.length ≤ n + 1) && (natCuts ws == 18446744073709551615) && natOptimized n (n + 1 - ws.length) ws

private theorem natSep_eq (w : W) : natSep w.toNat = (sep w).toNat := by
  simp only [natSep, sep, BitVec.toNat_setWidth, BitVec.toNat_xor, BitVec.toNat_ushiftRight]

private theorem natCuts_eq (ws : List W) : natCuts (ws.map BitVec.toNat) = (cuts ws).toNat := by
  induction ws with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.map_cons, natCuts, cuts, List.foldr_cons] at ih ⊢
    rw [natSep_eq, ih, BitVec.toNat_or]

private theorem natOps_eq (a b : W) : natOps a.toNat b.toNat = (ops a b).map BitVec.toNat := by
  simp only [natOps, ops, List.map_cons, List.map_nil, BitVec.toNat_and, BitVec.toNat_or, BitVec.toNat_not]

private theorem beqNat {n : ℕ} (x y : BitVec n) : (x.toNat == y.toNat) = (x == y) :=
  Bool.eq_iff_iff.mpr (by simp only [beq_iff_eq, BitVec.toNat_inj])

private theorem beqSingle (ws : List W) (w : W) :
    (ws.map BitVec.toNat == [w.toNat]) = (ws == [w]) := by
  cases ws with
  | nil => rfl
  | cons a rest =>
    cases rest with
    | nil => simpa [List.beq] using beqNat a w
    | cons b other => simp [beqNat]

private theorem singles_map {α β : Type} (f : α → β) (ws : List α) :
    singles (ws.map f) = (singles ws).map (fun (a, r) => (f a, r.map f)) := by
  induction ws with
  | nil => rfl
  | cons a r ih => simp only [List.map_cons, singles, ih, List.map_map]; rfl

private theorem pairs_map {α β : Type} (f : α → β) (ws : List α) :
    pairs (ws.map f) = (pairs ws).map (fun (a, b, r) => (f a, f b, r.map f)) := by
  induction ws with
  | nil => rfl
  | cons a r ih =>
    simp only [List.map_cons, pairs, singles_map, ih, List.map_append, List.map_map]
    rfl

private theorem natDispatch_eq (extra : ℕ) (a b : W) (r : List W)
    (natNext : Nat → List Nat → Bool) (wordNext : Nat → List W → Bool)
    (next_eq : ∀ e ws, natNext e (ws.map BitVec.toNat) = wordNext e ws) :
    natDispatch extra natNext a.toNat b.toNat (r.map BitVec.toNat) =
      dispatch extra wordNext a b r := by
  simp only [natDispatch, dispatch, natOps_eq, List.any_map]
  congr 1
  funext w
  have hmask : 18446744073709551615 = (-1 : BitVec 64).toNat := rfl
  have h0 := next_eq extra (w :: r)
  have ha := next_eq (extra - 1) (w :: a :: r)
  have hb := next_eq (extra - 1) (w :: b :: r)
  have hab := next_eq (extra - 2) (w :: a :: b :: r)
  simp only [List.map_cons] at h0 ha hb hab
  simp only [Function.comp_apply, natChoice, natSep_eq, natCuts_eq, ← BitVec.toNat_or, hmask, beqNat, h0, ha, hb, hab]


private theorem natOptimized_eq (fuel extra : ℕ) (ws : List W) :
    natOptimized fuel extra (ws.map BitVec.toNat) = optimized fuel extra ws := by
  have h1 : ((2 ^ 64 - 1) * 2 ^ 64) = goal.toNat := rfl
  have h2 : 18446744073709551615 = (~~~goal).toNat := rfl
  induction fuel generalizing extra ws with
  | zero => simp only [optimized, natOptimized, h1, h2, beqSingle]
  | succ n ih =>
    simp only [optimized, natOptimized, h1, h2, beqSingle, pairs_map, List.any_map]
    congr 1
    congr 1
    funext p
    obtain ⟨a, b, r⟩ := p
    exact natDispatch_eq extra a b r (natOptimized n) (optimized n) ih

theorem replay_eq (n : ℕ) (ws : List W) : replay n (ws.map BitVec.toNat) = search n ws := by
  have hmask : 18446744073709551615 = (-1 : BitVec 64).toNat := rfl
  simp only [replay, search, List.sublists_map, List.any_map]
  congr 1
  funext ws
  simp only [Function.comp_apply, List.length_map, natCuts_eq, hmask, beqNat, natOptimized_eq]

private def viable (n : Nat) (ws : List Nat) : Bool :=
  decide (ws.length ≤ n + 1) && (natCuts ws == 18446744073709551615)

private def doneGoal (ws : List Nat) : Bool :=
  ws == [((2 ^ 64 - 1) * 2 ^ 64)] || ws == [18446744073709551615]

def replayDone (n : Nat) (roots : List Nat) : Bool :=
  roots.sublists.any fun ws => viable n ws && doneGoal ws

def replaySlice (n : Nat) (roots : List Nat) (i : Nat) : Bool :=
  roots.sublists.any fun ws =>
    viable n ws && match n with
    | 0 => false
    | k + 1 =>
      match (pairs ws)[i]? with
      | none => false
      | some (a, b, r) => natDispatch (k + 2 - ws.length) (natOptimized k) a b r

def sliceCount (roots : List Nat) (m : Nat) : Bool :=
  roots.sublists.all fun ws => decide ((pairs ws).length ≤ m)

theorem replay_split {n m : Nat} {roots : List Nat}
    (cover : sliceCount roots m = true) (done : replayDone n roots = false)
    (part : ∀ i : Nat, i < m → replaySlice n roots i = false) :
    replay n roots = false := by
  cases e : replay n roots
  · rfl
  · unfold replay at e
    obtain ⟨ws, hws, hw⟩ := List.any_eq_true.mp e
    have hvi : viable n ws = true := (Bool.and_eq_true_iff.mp hw).1
    have hopt := (Bool.and_eq_true_iff.mp hw).2
    have notDone : doneGoal ws ≠ true := by
      intro yes
      have htrue : replayDone n roots = true := List.any_eq_true.mpr
        ⟨ws, hws, Bool.and_eq_true_iff.mpr ⟨hvi, yes⟩⟩
      rw [done] at htrue
      contradiction
    cases n with
    | zero => exact (notDone hopt).elim
    | succ k =>
      obtain ⟨⟨a, b, r⟩, mem, hit⟩ := List.any_eq_true.mp
        ((Bool.or_eq_true_iff.mp hopt).resolve_left notDone)
      obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp mem
      have le : (pairs ws).length ≤ m :=
        of_decide_eq_true (List.all_eq_true.mp cover ws hws)
      have htrue : replaySlice (k + 1) roots i = true := List.any_eq_true.mpr
        ⟨ws, hws, Bool.and_eq_true_iff.mpr ⟨hvi, by
          rw [List.getElem?_eq_getElem hi, he]
          exact hit⟩⟩
      rw [part i (hi.trans_le le)] at htrue
      contradiction

def replaySliceChoice (n : Nat) (roots : List Nat) (i j : Nat) : Bool :=
  roots.sublists.any fun ws =>
    viable n ws && match n with
    | 0 => false
    | k + 1 =>
      match (pairs ws)[i]? with
      | none => false
      | some (a, b, r) =>
        match (natOps a b)[j]? with
        | some w => natChoice (k + 2 - ws.length) (natOptimized k) a b r w
        | none => false

theorem replaySlice_split {n i : Nat} {roots : List Nat}
    (part : ∀ j : Nat, j < 4 → replaySliceChoice n roots i j = false) :
    replaySlice n roots i = false := by
  cases hh : replaySlice n roots i
  · rfl
  · unfold replaySlice at hh
    obtain ⟨ws, hws, hv⟩ := List.any_eq_true.mp hh
    obtain ⟨hvi, hx⟩ := Bool.and_eq_true_iff.mp hv
    cases n with
    | zero => contradiction
    | succ k =>
      cases hp : (pairs ws)[i]? with
      | none => simp [hp] at hx
      | some q =>
        obtain ⟨a,b,r⟩ := q
        simp only [hp] at hx
        obtain ⟨w, hm, hw⟩ := List.any_eq_true.mp hx
        obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hm
        have hj' : j < 4 := by simpa [natOps] using hj
        have yes : replaySliceChoice (k + 1) roots i j = true := by
          apply List.any_eq_true.mpr
          refine ⟨ws, hws, Bool.and_eq_true_iff.mpr ⟨hvi, ?_⟩⟩
          simpa only [hp, List.getElem?_eq_getElem hj, he] using hw
        rw [part j hj'] at yes
        contradiction

private def searchBlock (fuel block extra : Nat) (ws : List Nat) : Bool :=
  match fuel with
  | 0 => doneGoal ws
  | k + 1 =>
    doneGoal ws || (List.range (pairs ws).length).any fun j =>
      j % 8 == block && match (pairs ws)[j]? with
      | none => false
      | some (a,b,r) => natDispatch extra (natOptimized k) a b r

private theorem searchBlock_hit {fuel extra : Nat} {ws : List Nat}
    (h : natOptimized fuel extra ws = true) :
    ∃ block : Nat, block < 8 ∧ searchBlock fuel block extra ws = true := by
  cases fuel with
  | zero => exact ⟨0, by decide, h⟩
  | succ k =>
    rcases Bool.or_eq_true_iff.mp h with hh | more
    · exact ⟨0, by decide, Bool.or_eq_true_iff.mpr (.inl hh)⟩
    obtain ⟨⟨a,b,r⟩,hm,ht⟩ := List.any_eq_true.mp more
    obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp hm
    refine ⟨j % 8, Nat.mod_lt _ (by decide), Bool.or_eq_true_iff.mpr (.inr ?_)⟩
    apply List.any_eq_true.mpr
    refine ⟨j,List.mem_range.mpr hj, Bool.and_eq_true_iff.mpr ⟨by simp, ?_⟩⟩
    simpa only [List.getElem?_eq_getElem hj, he] using ht

private theorem choiceBlock_hit {k extra a b w : Nat} {r : List Nat}
    (h : natChoice extra (natOptimized k) a b r w = true) :
    ∃ block : Nat, block < 8 ∧ natChoice extra (searchBlock k block) a b r w = true := by
  by_cases same : (w == a || w == b) = true
  · simp only [natChoice, same, ite_true, Bool.false_eq_true] at h
  have off : (w == a || w == b) = false := by cases hval : (w == a || w == b) <;> simp_all
  simp only [natChoice, off, Bool.false_eq_true, ite_false] at h ⊢
  simp only [Bool.and_eq_true, Bool.or_eq_true] at h ⊢
  rcases h with ((⟨hc,ht⟩ | ⟨he,(⟨hc,ht⟩ | ⟨hc,ht⟩)⟩) | ⟨hc,ht⟩)
  · obtain ⟨i,hi,tag⟩ := searchBlock_hit ht
    exact ⟨i,hi,.inl (.inl ⟨hc,tag⟩)⟩
  · obtain ⟨i,hi,tag⟩ := searchBlock_hit ht
    exact ⟨i,hi,.inl (.inr ⟨he,.inl ⟨hc,tag⟩⟩)⟩
  · obtain ⟨i,hi,tag⟩ := searchBlock_hit ht
    exact ⟨i,hi,.inl (.inr ⟨he,.inr ⟨hc,tag⟩⟩)⟩
  · obtain ⟨i,hi,tag⟩ := searchBlock_hit ht
    exact ⟨i,hi,.inr ⟨hc,tag⟩⟩

def replayBlock (n : Nat) (roots : List Nat) (i j block : Nat) : Bool :=
  roots.sublists.any fun ws =>
    viable n ws && match n with
    | 0 => false
    | k + 1 =>
      match (pairs ws)[i]? with
      | none => false
      | some (a,b,r) =>
        match (natOps a b)[j]? with
        | none => false
        | some w => natChoice (k + 2 - ws.length) (searchBlock k block) a b r w

theorem replayBlock_split {n i j : Nat} {roots : List Nat}
    (part : ∀ block : Nat, block < 8 → replayBlock n roots i j block = false) :
    replaySliceChoice n roots i j = false := by
  cases hh : replaySliceChoice n roots i j
  · rfl
  · unfold replaySliceChoice at hh
    obtain ⟨ws,hws,hvi⟩ := List.any_eq_true.mp hh
    obtain ⟨hvi,hx⟩ := Bool.and_eq_true_iff.mp hvi
    cases n with
    | zero => contradiction
    | succ k =>
      cases hp : (pairs ws)[i]? with
      | none => simp [hp] at hx
      | some q =>
        obtain ⟨a,b,r⟩ := q
        cases ho : (natOps a b)[j]? with
        | none => simp [hp,ho] at hx
        | some w =>
          simp only [hp,ho] at hx
          obtain ⟨z,hz,tag⟩ := choiceBlock_hit hx
          have yes : replayBlock (k + 1) roots i j z = true := by
            apply List.any_eq_true.mpr
            refine ⟨ws,hws,Bool.and_eq_true_iff.mpr ⟨hvi, ?_⟩⟩
            simpa only [hp,ho] using tag
          rw [part z hz] at yes
          contradiction

def columnBit (w : W) (i : Fin 128) : Bool := w[i.val]

def point (columns : List W) (i : Fin 128) : X :=
  fun j => columnBit (columns.getD j.val 0) i

def Rep (queries : Fin 128 → X) (f : F) (w : W) : Prop :=
  ∀ i, f (queries i) = columnBit w i

theorem rep_not {queries f w} (h : Rep queries f w) :
    Rep queries (fun x => !f x) (~~~w) := by
  intro i
  simpa only [columnBit, BitVec.getElem_not] using congrArg not (h i)

theorem rep_comb {queries a b wa wb} (ha : Rep queries a wa) (hb : Rep queries b wb) (t : Bool) :
    Rep queries (comb t a b) (if t then wa &&& wb else wa ||| wb) := by
  intro i
  cases t <;> simp [comb, columnBit, ha i, hb i]

theorem rep_av {queries : Fin 128 → X} {s : Set F} {f : F} {roots : Finset W}
    (inv : ∀ u ∈ s, ∃ w, Rep queries u w ∧ holds roots w) (h : Av s f) :
    ∃ w, Rep queries f w ∧ holds roots w := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · cases b
    · exact ⟨0, fun i => by simp [columnBit], .inl rfl⟩
    · refine ⟨~~~0, ?_, .inr (.inl rfl)⟩
      intro i
      exact (BitVec.getElem_allOnes i.val i.isLt).symm
  · exact inv _ hu
  · obtain ⟨w, hw, hav⟩ := inv _ hu
    exact ⟨~~~w, rep_not hw, holds_not hav⟩

theorem project_prog {queries : Fin 128 → X} {g : W}
    (nonzero : g ≠ 0) (nonone : g ≠ ~~~0)
    {s : Set F} {f : F} {k : ℕ} (p : Prog s f k) (target : Rep queries f g) :
    ∀ roots : Finset W, (∀ u ∈ s, ∃ w, Rep queries u w ∧ holds roots w) →
      build basicOps g k roots ∨ build basicOps (~~~g) k roots := by
  induction p with
  | done av =>
    intro roots inv
    obtain ⟨w, hw, hp⟩ := rep_av inv av
    have e : w = g := BitVec.eq_of_getElem_eq (fun i hi => (hw ⟨i, hi⟩).symm.trans (target ⟨i, hi⟩))
    subst w
    rcases hp with h | h | ⟨v, hv, h | h⟩
    · exact (nonzero h).elim
    · exact (nonone h).elim
    · exact .inl (h.symm ▸ hv)
    · right
      change ~~~g ∈ roots
      rw [h, BitVec.not_not]
      exact hv
  | @gate s f a b k t ha hb tail ih =>
    intro roots inv
    obtain ⟨wa, hwa, ava⟩ := rep_av inv ha
    obtain ⟨wb, hwb, avb⟩ := rep_av inv hb
    let z := if t then wa &&& wb else wa ||| wb
    have hz : Rep queries (comb t a b) z := rep_comb hwa hwb t
    have hreach : reachable roots z := by
      cases t
      · exact or_reach ava avb
      · exact and_reach ava avb
    rcases hreach with old | ⟨u, hu, v, hv, ne, w, hw, new⟩
    · have h : ∀ y ∈ insert (comb t a b) s, ∃ w, Rep queries y w ∧ holds roots w := by
        intro y hy
        rcases Set.mem_insert_iff.mp hy with rfl | hy
        · exact ⟨z, hz, old⟩
        · exact inv _ hy
      rcases ih target roots h with l | r
      · exact .inl (.inl l)
      · exact .inr (.inl r)
    · have h : ∀ y ∈ insert (comb t a b) s, ∃ v, Rep queries y v ∧ holds (insert w roots) v := by
        intro y hy
        rcases Set.mem_insert_iff.mp hy with rfl | hy
        · exact ⟨z, hz, new⟩
        · obtain ⟨v, hv, hav⟩ := inv _ hy
          exact ⟨v, hv, holds_insert hav⟩
      rcases ih target (insert w roots) h with l | r
      · exact .inl (.inr ⟨u, hu, v, hv, ne, w, hw, l⟩)
      · exact .inr (.inr ⟨u, hu, v, hv, ne, w, hw, r⟩)

theorem root_at (columns roots : List W)
    (h : columns.all (fun w => w == 0 || w == ~~~0 || roots.contains w) = true)
    (i : ℕ) : holds roots.toFinset (columns.getD i 0) := by
  rw [List.getD_eq_getElem?_getD]
  cases e : columns[i]? with
  | none => exact .inl rfl
  | some w =>
    have ok := List.all_eq_true.mp h w (List.mem_of_getElem? e)
    simp only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at ok
    rcases ok with (h0 | h1) | hw
    · exact .inl h0
    · exact .inr (.inl h1)
    · exact .inr (.inr ⟨w, List.mem_toFinset.mpr hw, .inl rfl⟩)

theorem build_extend {g : W} {k a : ℕ} {roots : Finset W}
    (h : build basicOps g k roots) (le : k ≤ a) : build basicOps g a roots := by
  induction le with
  | refl => exact h
  | step _ ih => exact .inl ih

theorem lower {n : ℕ} {f : F} (columns roots : List W)
    (distinct : roots.Nodup)
    (valid : columns.all (fun w => w == 0 || w == ~~~0 || roots.contains w) = true)
    (sample : Rep (point columns) f goal)
    (reject : replay n (roots.map BitVec.toNat) = false) : Low (n + 1) f := by
  intro k p
  by_contra! small
  have repr : ∀ u ∈ stock, ∃ w, Rep (point columns) u w ∧ holds roots.toFinset w := by
    rintro u ⟨i, rfl⟩
    exact ⟨columns.getD i.val 0, fun _ => rfl, root_at columns roots valid i.val⟩
  have h := project_prog (queries := point columns) (g := goal)
    (by decide) (by decide) p sample roots.toFinset repr
  have bound : k ≤ n := by omega
  have yes : search n roots = true := by
    rcases h with h | h
    · exact search_complete (.inl rfl) n roots distinct (build_extend h bound)
    · exact search_complete (.inr rfl) n roots distinct (build_extend h bound)
  rw [← replay_eq, reject] at yes
  contradiction

end CoreSearch
namespace FirstGate

def unary (i : Fin 6) (f : F) : Prop := ∃ e : Bool → Bool, f = fun x => e (x i)

theorem unary_av {i f} (h : unary i f) : Av stock f := by
  obtain ⟨e, rfl⟩ := h
  cases h0 : e false <;> cases h1 : e true
  · exact Or.inl ⟨false, by funext x; cases u : x i <;> simp [h0, h1]⟩
  · exact Or.inr ⟨fun x => x i, ⟨i, rfl⟩, Or.inl (by funext x; cases u : x i <;> simp [h0, h1])⟩
  · exact Or.inr ⟨fun x => x i, ⟨i, rfl⟩, Or.inr (by funext x; cases u : x i <;> simp [u, h0, h1])⟩
  · exact Or.inl ⟨true, by funext x; cases u : x i <;> simp [h0, h1]⟩

theorem stock_unary {f} (h : Av stock f) : ∃ i, unary i f := by
  rcases h with ⟨b,rfl⟩ | ⟨u, ⟨i,rfl⟩, rfl | rfl⟩
  · exact ⟨0, fun _ => b, rfl⟩
  · exact ⟨i, id, rfl⟩
  · exact ⟨i, not, rfl⟩

def tune (m : Fin 4) (z : Bool) : Bool :=
  if m = 0 then false else if m = 1 then true else if m = 2 then z else !z

def glue (i j : Fin 6) (m : Fin 4) (x : X) : X :=
  fun v => if v = i then tune m (x j) else x v

theorem glue_const (i j : Fin 6) (b : Bool) (f : F) :
    (fun x => f (glue i j (if b then 1 else 0) x)) = rs i b f := by
  funext x
  apply congrArg f
  funext v
  by_cases h : v = i <;> cases b <;> simp [glue,tune,Function.update,h]

theorem glue0 (i j : Fin 6) (f : F) : (fun x => f (glue i j 0 x)) = rs i false f :=
  glue_const i j false f

theorem glue1 (i j : Fin 6) (f : F) : (fun x => f (glue i j 1 x)) = rs i true f :=
  glue_const i j true f

theorem av_pull (p : X → X) {s t : Set F}
    (hs : ∀ u ∈ s, Av t (fun x => u (p x))) {a} (ha : Av s a) :
    Av t (fun x => a (p x)) := by
  rcases ha with ⟨c,rfl⟩ | ⟨u,hu,rfl | rfl⟩
  · exact Or.inl ⟨c,rfl⟩
  · exact hs _ hu
  · exact av_not (hs _ hu)

theorem prog_pull (p : X → X) {s : Set F} {f k} (pr : Prog s f k) :
    ∀ t, (∀ u ∈ s, Av t (fun x => u (p x))) → Prog t (fun x => f (p x)) k := by
  induction pr with
  | done h => exact fun _ hs => .done (av_pull p hs h)
  | @gate s f a b k op ha hb tail ih =>
    intro t hs
    let a' : F := fun x => a (p x)
    let b' : F := fun x => b (p x)
    apply Prog.gate op (av_pull p hs ha) (av_pull p hs hb)
    apply ih
    intro u hu
    rcases Set.mem_insert_iff.mp hu with rfl | hu
    · exact av_mem (Set.mem_insert (comb op a' b') t)
    · exact av_ins _ (hs u hu)

theorem stock_glue (i j : Fin 6) (m : Fin 4) :
    ∀ u ∈ stock, Av stock (fun x => u (glue i j m x)) := by
  rintro u ⟨v,rfl⟩
  by_cases e : v = i
  · exact unary_av (i := j) ⟨tune m, by funext x; simp [glue,e]⟩
  · exact unary_av (i := v) ⟨id, by funext x; simp [glue,e]⟩

theorem same {i a b} (ha : unary i a) (hb : unary i b) (op : Bool) :
    Av stock (comb op a b) := by
  obtain ⟨e,rfl⟩ := ha
  obtain ⟨d,rfl⟩ := hb
  exact unary_av (i := i) ⟨fun z => if op then e z && d z else e z || d z,rfl⟩

theorem fit_left {i j a b} (hij : i ≠ j) (ha : unary i a) (hb : unary j b) (op : Bool) (m : Fin 4) :
    Av stock (fun x => comb op a b (glue i j m x)) := by
  obtain ⟨e,rfl⟩ := ha
  obtain ⟨d,rfl⟩ := hb
  refine unary_av (i := j) ⟨fun z => if op then e (tune m z) && d z else e (tune m z) || d z, ?_⟩
  funext x
  simp [comb,glue,Ne.symm hij]

theorem fit_right {i j a b} (hij : i ≠ j) (ha : unary i a) (hb : unary j b) (op : Bool) (m : Fin 4) :
    Av stock (fun x => comb op a b (glue j i m x)) := by
  obtain ⟨e,rfl⟩ := ha
  obtain ⟨d,rfl⟩ := hb
  refine unary_av (i := i) ⟨fun z => if op then e z && d (tune m z) else e z || d (tune m z), ?_⟩
  funext x
  simp [comb,glue,hij]

def PairLow (n : ℕ) (f : F) (i j : Fin 6) : Prop :=
  (∃ m, Low n (fun x => f (glue i j m x))) ∨ (∃ m, Low n (fun x => f (glue j i m x)))

theorem pairLower {n f} (hp : 0 < n) (baseline : Low n f)
    (pairs : ∀ i j, i < j → PairLow n f i j) : Low (n+1) f := by
  intro k pr
  cases pr with
  | done h =>
    have := baseline 0 (.done h)
    omega
  | @gate s f a b k tag ha hb tail =>
    obtain ⟨i,hi⟩ := stock_unary ha
    obtain ⟨j,hj⟩ := stock_unary hb
    have use (p : X → X) (base : ∀ u ∈ stock, Av stock (fun x => u (p x)))
        (cheap : Av stock (fun x => comb tag a b (p x))) (lower : Low n (fun x => f (p x))) : n ≤ k := by
      apply lower
      apply prog_pull p tail stock
      intro u hu
      rcases Set.mem_insert_iff.mp hu with rfl | hu
      · exact cheap
      · exact base _ hu
    by_cases e : i = j
    · subst j
      have := use id (fun _ hu => av_mem hu) (same hi hj tag) baseline
      omega
    · have hpairs : PairLow n f i j := by
        rcases lt_or_gt_of_ne e with h | h
        · exact pairs i j h
        · exact (pairs j i h).symm
      rcases hpairs with ⟨m,hm⟩ | ⟨m,hm⟩
      · have := use (glue i j m) (stock_glue i j m) (fit_left e hi hj tag m) hm
        omega
      · have := use (glue j i m) (stock_glue j i m) (fit_right e hi hj tag m) hm
        omega

end FirstGate
namespace FirstGate

theorem split_av (p : X → X) {s t : Set F}
    (h : ∀ u ∈ s, Av t u ∨ Cst (fun x => u (p x))) {a} (ha : Av s a) :
    Av t a ∨ Cst (fun x => a (p x)) := by
  rcases ha with hc | ⟨u,hu,rfl | rfl⟩
  · exact Or.inl (Or.inl hc)
  · exact h _ hu
  · rcases h _ hu with h | ⟨b,h⟩
    · exact Or.inl (av_not h)
    · exact Or.inr ⟨!b, by funext x; exact congrArg not (congrFun h x)⟩

theorem skip_use (p : X → X) {s f k} (pr : Prog s f k) :
    ∀ clean t, (∀ u ∈ s, Av t (fun x => u (p x))) →
      (∀ u ∈ s, Av clean u ∨ Cst (fun x => u (p x))) →
      (∃ j < k, Prog t (fun x => f (p x)) j) ∨ Cst (fun x => f (p x)) ∨ Prog clean f k := by
  induction pr with
  | done h =>
    intro clean t h₁ h₂
    rcases split_av p h₂ h with ha | hc
    · exact Or.inr (Or.inr (.done ha))
    · exact Or.inr (Or.inl hc)
  | @gate s f a b k op ha hb tail ih =>
    intro clean t h₁ h₂
    let a' : F := fun x => a (p x)
    let b' : F := fun x => b (p x)
    have pa : Av t a' := av_pull p h₁ ha
    have pb : Av t b' := av_pull p h₁ hb
    by_cases c : Cst a' ∨ Cst b'
    · refine Or.inl ⟨k, by omega, prog_pull p tail t ?_⟩
      intro u hu
      rcases Set.mem_insert_iff.mp hu with rfl | hu
      · exact av_cheap op pa pb c
      · exact h₁ _ hu
    · have oa := (split_av p h₂ ha).resolve_right (fun h => c (.inl h))
      have ob := (split_av p h₂ hb).resolve_right (fun h => c (.inr h))
      obtain short | hc | original := ih (insert (comb op a b) clean) (insert (comb op a' b') t)
        (by
          intro u hu
          rcases Set.mem_insert_iff.mp hu with rfl | hu
          · exact av_mem (Set.mem_insert _ _)
          · exact av_ins _ (h₁ _ hu))
        (by
          intro u hu
          rcases Set.mem_insert_iff.mp hu with rfl | hu
          · exact Or.inl (av_mem (Set.mem_insert _ _))
          · rcases h₂ u hu with h | h
            · exact Or.inl (av_ins _ h)
            · exact Or.inr h)
      · obtain ⟨j,hj,q⟩ := short
        exact Or.inl ⟨j+1,by omega,.gate op pa pb q⟩
      · exact Or.inr (Or.inl hc)
      · exact Or.inr (Or.inr (.gate op oa ob original))

def Relative (n : ℕ) (t : Set F) (f : F) := ∀ k, Prog t f k → n ≤ k

def GateBound (n : ℕ) (f g : F) : Prop :=
  ∃ (p : X → X) (t : Set F), (∀ u ∈ stock, Av t (fun x => u (p x))) ∧
    ((Av t (fun x => g (p x)) ∧ Relative (n+1) t (fun x => f (p x))) ∨
     (Cst (fun x => g (p x)) ∧ Relative n t (fun x => f (p x))))

theorem advance {n f g k} (hp : 0 < n) (h : GateBound n f g)
    (tail : Prog (insert g stock) f k) :
    n+1 ≤ k ∨ Prog stock f k := by
  obtain ⟨p,t,base, cheap | killed⟩ := h
  · left
    apply cheap.2
    apply prog_pull p tail t
    intro u hu
    rcases Set.mem_insert_iff.mp hu with rfl | hu
    · exact cheap.1
    · exact base _ hu
  · obtain short | constant | original := skip_use p tail stock t
      (by
        intro u hu
        rcases Set.mem_insert_iff.mp hu with rfl | hu
        · exact Or.inl killed.1
        · exact base _ hu)
      (by
        intro u hu
        rcases Set.mem_insert_iff.mp hu with rfl | hu
        · exact Or.inr killed.1
        · exact Or.inl (av_mem hu))
    · obtain ⟨j,hj,pr⟩ := short
      have := killed.2 j pr
      exact Or.inl (by omega)
    · have := killed.2 0 (.done (Or.inl constant))
      omega
    · exact Or.inr original

def bit (i : Fin 6) (sign : Bool) : F := fun x => xor (x i) sign

theorem signed_stock {a} (ha : Av stock a) : Cst a ∨ ∃ i sign, a = bit i sign := by
  rcases ha with h | ⟨u,⟨i,rfl⟩,rfl | rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨i,false, by funext x; simp [bit]⟩
  · exact Or.inr ⟨i,true, by funext x; simp [bit]⟩

def killValue (tag sign : Bool) := xor sign (!tag)
def killMode (a b : Bool) : Fin 4 := if a = b then 3 else 2

def restrictPair (i j : Fin 6) (a b : Bool) (x : X) : X :=
  if x i = a ∨ x j = b then x else Function.update x i a

def vars (p : X → X) : Set F := Set.range fun (i : Fin 6) (x : X) => p x i

def DomainLow (n : ℕ) (f : F) (i j : Fin 6) (a b : Bool) : Prop :=
  let p := restrictPair i j a b
  Relative n (vars p) (fun x => f (p x))

theorem stock_vars (p : X → X) : ∀ u ∈ stock, Av (vars p) (fun x => u (p x)) := by
  rintro u ⟨i,rfl⟩
  exact av_mem ⟨i,rfl⟩

theorem whole_kill (i j : Fin 6) (tag sa sb : Bool) :
    let ci := killValue tag sa
    let cj := killValue tag sb
    Cst (fun x => comb tag (bit i sa) (bit j sb) (restrictPair i j ci cj x)) := by
  dsimp only
  refine ⟨!tag,?_⟩
  funext x
  unfold restrictPair
  split
  next h =>
    rcases h with h | h <;> cases tag <;> cases sa <;> cases sb <;>
      simp_all [comb,bit,killValue]
  next h =>
    cases tag <;> cases sa <;> cases sb <;>
      simp [comb,bit,killValue,Function.update]

def exceptionBit (i j : Fin 6) (a b : Bool) : F := fun x => (x i != a) && (x j != b)

def FreeLow (n : ℕ) (f : F) (i j : Fin 6) (a b : Bool) : Prop :=
  Relative n (insert (exceptionBit i j a b) stock) f

theorem first_available (i j : Fin 6) (tag sa sb : Bool) :
    let q := exceptionBit i j (killValue tag sa) (killValue tag sb)
    Av (insert q stock) (comb tag (bit i sa) (bit j sb)) := by
  dsimp only
  cases tag
  · refine Or.inr ⟨_,Set.mem_insert _ _,Or.inr ?_⟩
    funext x
    cases sa <;> cases sb <;> cases u : x i <;> cases v : x j <;>
      simp [comb,bit,exceptionBit,killValue,u,v]
  · refine Or.inr ⟨_,Set.mem_insert _ _,Or.inl ?_⟩
    funext x
    cases sa <;> cases sb <;> cases u : x i <;> cases v : x j <;>
      simp [comb,bit,exceptionBit,killValue,u,v]

def PairKill (n : ℕ) (f : F) (i j : Fin 6) (ci cj : Bool) : Prop :=
  Low n (rs i ci f) ∨ Low n (rs j cj f) ∨
  Low n (fun x => f (glue i j (killMode ci cj) x)) ∨ Low n (fun x => f (glue j i (killMode ci cj) x)) ∨ DomainLow n f i j ci cj ∨ FreeLow (n+1) f i j ci cj

theorem kills {i j : Fin 6} (ne : i ≠ j) (tag sa sb : Bool) :
    let G := comb tag (bit i sa) (bit j sb)
    let ci := killValue tag sa
    let cj := killValue tag sb
    Cst (fun x => G (glue i j (if ci then 1 else 0) x)) ∧
    Cst (fun x => G (glue j i (if cj then 1 else 0) x)) ∧
    Cst (fun x => G (glue i j (killMode ci cj) x)) ∧
    Cst (fun x => G (glue j i (killMode ci cj) x)) := by
  dsimp only
  refine ⟨⟨!tag,?_⟩,⟨!tag,?_⟩,⟨!tag,?_⟩,⟨!tag,?_⟩⟩ <;> funext x <;>
    cases tag <;> cases sa <;> cases sb <;>
    simp [glue,comb,bit,tune,killMode,killValue,ne,Ne.symm ne]

theorem bounded {n f i j} (lt : i < j) (tag sa sb : Bool)
    (h : PairLow (n+1) f i j ∨ ∀ ci cj, PairKill n f i j ci cj) :
    GateBound n f (comb tag (bit i sa) (bit j sb)) := by
  have ha : unary i (bit i sa) := ⟨fun x => xor x sa,rfl⟩
  have hb : unary j (bit j sb) := ⟨fun x => xor x sb,rfl⟩
  rcases h with (⟨m,hm⟩ | ⟨m,hm⟩) | hs
  · exact ⟨_,stock,stock_glue i j m,Or.inl ⟨fit_left lt.ne ha hb tag m,hm⟩⟩
  · exact ⟨_,stock,stock_glue j i m,Or.inl ⟨fit_right lt.ne ha hb tag m,hm⟩⟩
  · let ci := killValue tag sa
    let cj := killValue tag sb
    have hk := kills lt.ne tag sa sb
    rcases hs ci cj with h | h | h | h | h | h
    · exact ⟨_,stock,stock_glue i j (if ci then 1 else 0),Or.inr ⟨hk.1,(glue_const i j ci f).symm ▸ h⟩⟩
    · exact ⟨_,stock,stock_glue j i (if cj then 1 else 0),Or.inr ⟨hk.2.1,(glue_const j i cj f).symm ▸ h⟩⟩
    · exact ⟨_,stock,stock_glue i j (killMode ci cj),Or.inr ⟨hk.2.2.1,h⟩⟩
    · exact ⟨_,stock,stock_glue j i (killMode ci cj),Or.inr ⟨hk.2.2.2,h⟩⟩
    · exact ⟨_,_,stock_vars _,Or.inr ⟨whole_kill i j tag sa sb,h⟩⟩
    · refine ⟨id,_,fun u hu => av_mem (Set.mem_insert_of_mem _ hu),Or.inl ⟨?_,h⟩⟩
      exact first_available i j tag sa sb

theorem strongLower {n f} (hp : 0 < n) (base : Low 1 f)
    (pairs : ∀ i j, i < j → PairLow (n+1) f i j ∨ ∀ ci cj, PairKill n f i j ci cj) : Low (n+2) f := by
  intro k
  induction k with
  | zero =>
    intro pr
    have := base 0 pr
    omega
  | succ k ih =>
    intro pr
    cases pr with
    | @gate s f a b k tag ha hb tail =>
      have cheap (h : Av stock (comb tag a b)) : n+2 ≤ k+1 := by
        have p := prog_pull id tail stock (by
          intro u hu
          rcases Set.mem_insert_iff.mp hu with rfl | hu
          · exact h
          · exact av_mem hu)
        have := ih p
        omega
      rcases signed_stock ha with hc | ⟨i,sa,rfl⟩
      · exact cheap (av_cheap tag ha hb (Or.inl hc))
      rcases signed_stock hb with hc | ⟨j,sb,rfl⟩
      · exact cheap (av_cheap tag ha hb (Or.inr hc))
      rcases lt_trichotomy i j with lt | eq | gt
      · rcases advance hp (bounded lt tag sa sb (pairs i j lt)) tail with short | short
        · omega
        · have := ih short
          omega
      · subst j
        exact cheap (same ⟨fun x => xor x sa,rfl⟩ ⟨fun x => xor x sb,rfl⟩ tag)
      · have e : comb tag (bit i sa) (bit j sb) = comb tag (bit j sb) (bit i sa) := by
          funext x
          cases tag <;> simp [comb,Bool.and_comm,Bool.or_comm]
        rw [e] at tail
        rcases advance hp (bounded gt tag sb sa (pairs j i gt)) tail with short | short
        · omega
        · have := ih short
          omega

end FirstGate
namespace FirstGate

theorem except_ind {i j v : Fin 6} (hi : v ≠ i) (hj : v ≠ j) (a b : Bool) :
    Ind v (exceptionBit i j a b) := by
  intro x c
  simp [exceptionBit,Function.update_of_ne hi.symm,Function.update_of_ne hj.symm]

theorem except_li {i j v : Fin 6} (hi : v ≠ i) (hj : v ≠ j) (a b : Bool) :
    ∀ u ∈ insert (exceptionBit i j a b) stock, LI v u := by
  intro u hu
  rcases Set.mem_insert_iff.mp hu with rfl | hu
  · exact Or.inl (except_ind hi hj a b)
  · exact stock_li v _ hu

theorem except_rs {i j v : Fin 6} (hi : v ≠ i) (hj : v ≠ j) (a b c : Bool) :
    ∀ u ∈ insert (exceptionBit i j a b) stock,
      Av (insert (exceptionBit i j a b) stock) (rs v c u) := by
  intro u hu
  rcases Set.mem_insert_iff.mp hu with rfl | hu
  · rw [show rs v c (exceptionBit i j a b) = exceptionBit i j a b by
          funext x; exact except_ind hi hj a b x c]
    exact av_mem (Set.mem_insert _ _)
  · exact av_ins _ (stock_rs v c _ hu)

theorem free_one {n f} (i j v : Fin 6) (a b c : Bool) (hi : v ≠ i) (hj : v ≠ j)
    (good : ¬ Smp v c f) (lower : FreeLow n (rs v c f) i j a b) :
    FreeLow (n+1) f i j a b := by
  intro k p
  obtain ⟨t,ht,pr⟩ := strict p _ (except_rs hi hj a b c)
    (fun u hu => li_smp (except_li hi hj a b u hu)) good
  have := lower t pr
  omega

theorem free_two {n f} (i j v : Fin 6) (a b : Bool) (hi : v ≠ i) (hj : v ≠ j)
    (good0 : ¬ Smp v false f) (good1 : ¬ Smp v true f)
    (l0 : FreeLow n (rs v false f) i j a b) (l1 : FreeLow n (rs v true f) i j a b) :
    FreeLow (n+2) f i j a b := by
  intro k p
  obtain ⟨c,h⟩ := double p (except_li hi hj a b) (by intro c; cases c <;> assumption)
  obtain ⟨t,ht,pr⟩ := h _ (except_rs hi hj a b c)
  cases c
  · have := l0 t pr
    omega
  · have := l1 t pr
    omega

theorem free_endpoint {k f i j a b v c}
    (hit : (v = i ∧ c = a) ∨ (v = j ∧ c = b))
    (good : ¬ Smp v c f) (lower : Low k (rs v c f)) :
    FreeLow (k+1) f i j a b := by
  have killed : Cst (rs v c (exceptionBit i j a b)) := by
    refine ⟨false,?_⟩
    funext x
    rcases hit with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [rs,exceptionBit]
  intro m pr
  obtain ⟨n,hn,p⟩ := strict pr stock (by
    intro u hu
    rcases Set.mem_insert_iff.mp hu with rfl | hu
    · exact Or.inl killed
    · exact stock_rs v c u hu) (by
      intro u hu
      rcases Set.mem_insert_iff.mp hu with rfl | hu
      · exact Or.inr killed
      · exact li_smp (stock_li v u hu)) good
  have := lower n p
  omega

theorem free_glue {k f i j a b} (m : Fin 4) (ne : i ≠ j)
    (low : Low k (fun x => f (glue i j m x))) : FreeLow k f i j a b := by
  intro n pr
  apply low
  apply prog_pull (glue i j m) pr stock
  intro u hu
  rcases Set.mem_insert_iff.mp hu with rfl | hu
  · refine unary_av (i := j) ⟨fun z => (tune m z != a) && (z != b),?_⟩
    funext x; simp [glue,exceptionBit,ne.symm]
  · exact stock_glue i j m _ hu

theorem free_glue_rev {k f i j a b} (m : Fin 4) (ne : i ≠ j)
    (low : Low k (fun x => f (glue j i m x))) : FreeLow k f i j a b := by
  intro n pr
  apply low
  apply prog_pull (glue j i m) pr stock
  intro u hu
  rcases Set.mem_insert_iff.mp hu with rfl | hu
  · refine unary_av (i := i) ⟨fun z => (z != a) && (tune m z != b),?_⟩
    funext x; simp [glue,exceptionBit,ne]
  · exact stock_glue j i m _ hu

end FirstGate
namespace CoreSearch

set_option maxHeartbeats 0 in
set_option maxRecDepth 64000 in
theorem domain_lower {n : ℕ} {f : F} (i j : Fin 6) (a b : Bool) (columns roots : List W)
    (distinct : roots.Nodup)
    (valid : columns.all (fun w => w == 0 || w == ~~~0 || roots.contains w) = true)
    (sample : Rep (point columns) f goal)
    (inside : ∀ r, point columns r i = a ∨ point columns r j = b)
    (reject : replay n (roots.map BitVec.toNat) = false) :
    FirstGate.DomainLow (n+1) f i j a b := by
  let p := FirstGate.restrictPair i j a b
  have fixes (r) : p (point columns r) = point columns r := by
    simp [p,FirstGate.restrictPair,inside r]
  have target : Rep (point columns) (fun x => f (p x)) goal := by
    intro r
    simpa only [fixes] using sample r
  have repr : ∀ u ∈ FirstGate.vars p, ∃ w, Rep (point columns) u w ∧ holds roots.toFinset w := by
    rintro u ⟨v,rfl⟩
    refine ⟨columns.getD v.val 0,?_,root_at columns roots valid v.val⟩
    intro r
    simp only [fixes]
    rfl
  intro k pr
  by_contra! small
  have h := project_prog (queries := point columns) (g := goal)
    (by decide) (by decide) pr target roots.toFinset repr
  have bound : k ≤ n := by omega
  have yes : search n roots = true := by
    rcases h with h | h
    · exact search_complete (.inl rfl) n roots distinct (build_extend h bound)
    · exact search_complete (.inr rfl) n roots distinct (build_extend h bound)
  rw [← replay_eq,reject] at yes
  contradiction

set_option maxHeartbeats 0 in
set_option maxRecDepth 64000 in
theorem free_lower {n : ℕ} {f : F} (i j : Fin 6) (a b : Bool) (extra : W) (columns roots : List W)
    (distinct : roots.Nodup)
    (valid : columns.all (fun w => w == 0 || w == ~~~0 || roots.contains w) = true)
    (sample : Rep (point columns) f goal)
    (hextra : Rep (point columns) (FirstGate.exceptionBit i j a b) extra)
    (member : extra ∈ roots)
    (reject : replay n (roots.map BitVec.toNat) = false) :
    FirstGate.FreeLow (n+1) f i j a b := by
  intro k pr
  by_contra! small
  have repr : ∀ u ∈ insert (FirstGate.exceptionBit i j a b) stock,
      ∃ w, Rep (point columns) u w ∧ holds roots.toFinset w := by
    intro u hu
    rcases Set.mem_insert_iff.mp hu with rfl | ⟨v,rfl⟩
    · exact ⟨extra,hextra,Or.inr (Or.inr ⟨extra,List.mem_toFinset.mpr member,Or.inl rfl⟩)⟩
    · exact ⟨columns.getD v.val 0,fun _ => rfl,root_at columns roots valid v.val⟩
  have h := project_prog (queries := point columns) (g := goal)
    (by decide) (by decide) pr sample roots.toFinset repr
  have bound : k ≤ n := by omega
  have yes : search n roots = true := by
    rcases h with h | h
    · exact search_complete (.inl rfl) n roots distinct (build_extend h bound)
    · exact search_complete (.inr rfl) n roots distinct (build_extend h bound)
  rw [← replay_eq,reject] at yes
  contradiction

end CoreSearch
def searchRows0 : List Nat := [0x9d516582e84c0a7ae4f17ce2fbcd1e6a, 0xcc3de3ef3c1fdb2b4e1800a710198302, 0x956e9624d0ff66590136808090eb6619, 0xa7ebd893a3afbcec80217c00a3840068, 0x59d66f4cee46eb5611c127506e066854]

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part0Op0 : CoreSearch.replaySliceChoice 7 searchRows0 0 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part0Op1 : CoreSearch.replaySliceChoice 7 searchRows0 0 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part0Op2 : CoreSearch.replaySliceChoice 7 searchRows0 0 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part0Op3 : CoreSearch.replaySliceChoice 7 searchRows0 0 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part0 : CoreSearch.replaySlice 7 searchRows0 0 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay0Part0Op0
  · exact caseReplay0Part0Op1
  · exact caseReplay0Part0Op2
  · exact caseReplay0Part0Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part1Op0 : CoreSearch.replaySliceChoice 7 searchRows0 1 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part1Op1 : CoreSearch.replaySliceChoice 7 searchRows0 1 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part1Op2 : CoreSearch.replaySliceChoice 7 searchRows0 1 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part1Op3 : CoreSearch.replaySliceChoice 7 searchRows0 1 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part1 : CoreSearch.replaySlice 7 searchRows0 1 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay0Part1Op0
  · exact caseReplay0Part1Op1
  · exact caseReplay0Part1Op2
  · exact caseReplay0Part1Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part2Op0 : CoreSearch.replaySliceChoice 7 searchRows0 2 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part2Op1 : CoreSearch.replaySliceChoice 7 searchRows0 2 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part2Op2 : CoreSearch.replaySliceChoice 7 searchRows0 2 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part2Op3 : CoreSearch.replaySliceChoice 7 searchRows0 2 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part2 : CoreSearch.replaySlice 7 searchRows0 2 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay0Part2Op0
  · exact caseReplay0Part2Op1
  · exact caseReplay0Part2Op2
  · exact caseReplay0Part2Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part3Op0 : CoreSearch.replaySliceChoice 7 searchRows0 3 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part3Op1 : CoreSearch.replaySliceChoice 7 searchRows0 3 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part3Op2 : CoreSearch.replaySliceChoice 7 searchRows0 3 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part3Op3 : CoreSearch.replaySliceChoice 7 searchRows0 3 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part3 : CoreSearch.replaySlice 7 searchRows0 3 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay0Part3Op0
  · exact caseReplay0Part3Op1
  · exact caseReplay0Part3Op2
  · exact caseReplay0Part3Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part4Op0 : CoreSearch.replaySliceChoice 7 searchRows0 4 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part4Op1 : CoreSearch.replaySliceChoice 7 searchRows0 4 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part4Op2 : CoreSearch.replaySliceChoice 7 searchRows0 4 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part4Op3 : CoreSearch.replaySliceChoice 7 searchRows0 4 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part4 : CoreSearch.replaySlice 7 searchRows0 4 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay0Part4Op0
  · exact caseReplay0Part4Op1
  · exact caseReplay0Part4Op2
  · exact caseReplay0Part4Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part5Op0 : CoreSearch.replaySliceChoice 7 searchRows0 5 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part5Op1 : CoreSearch.replaySliceChoice 7 searchRows0 5 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part5Op2 : CoreSearch.replaySliceChoice 7 searchRows0 5 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part5Op3 : CoreSearch.replaySliceChoice 7 searchRows0 5 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part5 : CoreSearch.replaySlice 7 searchRows0 5 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay0Part5Op0
  · exact caseReplay0Part5Op1
  · exact caseReplay0Part5Op2
  · exact caseReplay0Part5Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part6Op0 : CoreSearch.replaySliceChoice 7 searchRows0 6 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part6Op1 : CoreSearch.replaySliceChoice 7 searchRows0 6 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part6Op2 : CoreSearch.replaySliceChoice 7 searchRows0 6 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part6Op3 : CoreSearch.replaySliceChoice 7 searchRows0 6 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part6 : CoreSearch.replaySlice 7 searchRows0 6 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay0Part6Op0
  · exact caseReplay0Part6Op1
  · exact caseReplay0Part6Op2
  · exact caseReplay0Part6Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part7Op0 : CoreSearch.replaySliceChoice 7 searchRows0 7 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part7Op1 : CoreSearch.replaySliceChoice 7 searchRows0 7 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part7Op2 : CoreSearch.replaySliceChoice 7 searchRows0 7 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part7Op3 : CoreSearch.replaySliceChoice 7 searchRows0 7 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part7 : CoreSearch.replaySlice 7 searchRows0 7 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay0Part7Op0
  · exact caseReplay0Part7Op1
  · exact caseReplay0Part7Op2
  · exact caseReplay0Part7Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part8Op0 : CoreSearch.replaySliceChoice 7 searchRows0 8 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part8Op1 : CoreSearch.replaySliceChoice 7 searchRows0 8 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part8Op2 : CoreSearch.replaySliceChoice 7 searchRows0 8 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part8Op3 : CoreSearch.replaySliceChoice 7 searchRows0 8 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part8 : CoreSearch.replaySlice 7 searchRows0 8 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay0Part8Op0
  · exact caseReplay0Part8Op1
  · exact caseReplay0Part8Op2
  · exact caseReplay0Part8Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part9Op0 : CoreSearch.replaySliceChoice 7 searchRows0 9 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part9Op1 : CoreSearch.replaySliceChoice 7 searchRows0 9 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part9Op2 : CoreSearch.replaySliceChoice 7 searchRows0 9 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part9Op3 : CoreSearch.replaySliceChoice 7 searchRows0 9 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0Part9 : CoreSearch.replaySlice 7 searchRows0 9 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay0Part9Op0
  · exact caseReplay0Part9Op1
  · exact caseReplay0Part9Op2
  · exact caseReplay0Part9Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay0 : CoreSearch.replay 7 searchRows0 = false := by
  apply CoreSearch.replay_split (m := 10) (by decide +kernel) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact caseReplay0Part0
  · exact caseReplay0Part1
  · exact caseReplay0Part2
  · exact caseReplay0Part3
  · exact caseReplay0Part4
  · exact caseReplay0Part5
  · exact caseReplay0Part6
  · exact caseReplay0Part7
  · exact caseReplay0Part8
  · exact caseReplay0Part9

def searchRows1 : List Nat := [0xf6a6fffffea7ff3e38c6814050da271c, 0xffffff3d557ffbed984860b486806ae4, 0x6fff69e3fffdf6fb20005a93110b846b, 0xffdfd6febfdfbdd742b415212210d993]

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay1Part0Op0 : CoreSearch.replaySliceChoice 6 searchRows1 0 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay1Part0Op1 : CoreSearch.replaySliceChoice 6 searchRows1 0 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay1Part0Op2 : CoreSearch.replaySliceChoice 6 searchRows1 0 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay1Part0Op3 : CoreSearch.replaySliceChoice 6 searchRows1 0 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay1Part0 : CoreSearch.replaySlice 6 searchRows1 0 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay1Part0Op0
  · exact caseReplay1Part0Op1
  · exact caseReplay1Part0Op2
  · exact caseReplay1Part0Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay1Part1Op0 : CoreSearch.replaySliceChoice 6 searchRows1 1 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay1Part1Op1 : CoreSearch.replaySliceChoice 6 searchRows1 1 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay1Part1Op2 : CoreSearch.replaySliceChoice 6 searchRows1 1 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay1Part1Op3 : CoreSearch.replaySliceChoice 6 searchRows1 1 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay1Part1 : CoreSearch.replaySlice 6 searchRows1 1 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay1Part1Op0
  · exact caseReplay1Part1Op1
  · exact caseReplay1Part1Op2
  · exact caseReplay1Part1Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay1Part2Op0 : CoreSearch.replaySliceChoice 6 searchRows1 2 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay1Part2Op1 : CoreSearch.replaySliceChoice 6 searchRows1 2 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay1Part2Op2 : CoreSearch.replaySliceChoice 6 searchRows1 2 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay1Part2Op3 : CoreSearch.replaySliceChoice 6 searchRows1 2 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay1Part2 : CoreSearch.replaySlice 6 searchRows1 2 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay1Part2Op0
  · exact caseReplay1Part2Op1
  · exact caseReplay1Part2Op2
  · exact caseReplay1Part2Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay1Part3Op0 : CoreSearch.replaySliceChoice 6 searchRows1 3 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay1Part3Op1 : CoreSearch.replaySliceChoice 6 searchRows1 3 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay1Part3Op2 : CoreSearch.replaySliceChoice 6 searchRows1 3 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay1Part3Op3 : CoreSearch.replaySliceChoice 6 searchRows1 3 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay1Part3 : CoreSearch.replaySlice 6 searchRows1 3 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay1Part3Op0
  · exact caseReplay1Part3Op1
  · exact caseReplay1Part3Op2
  · exact caseReplay1Part3Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay1Part4Op0 : CoreSearch.replaySliceChoice 6 searchRows1 4 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay1Part4Op1 : CoreSearch.replaySliceChoice 6 searchRows1 4 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay1Part4Op2 : CoreSearch.replaySliceChoice 6 searchRows1 4 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay1Part4Op3 : CoreSearch.replaySliceChoice 6 searchRows1 4 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay1Part4 : CoreSearch.replaySlice 6 searchRows1 4 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay1Part4Op0
  · exact caseReplay1Part4Op1
  · exact caseReplay1Part4Op2
  · exact caseReplay1Part4Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay1Part5Op0 : CoreSearch.replaySliceChoice 6 searchRows1 5 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay1Part5Op1 : CoreSearch.replaySliceChoice 6 searchRows1 5 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay1Part5Op2 : CoreSearch.replaySliceChoice 6 searchRows1 5 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay1Part5Op3 : CoreSearch.replaySliceChoice 6 searchRows1 5 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay1Part5 : CoreSearch.replaySlice 6 searchRows1 5 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay1Part5Op0
  · exact caseReplay1Part5Op1
  · exact caseReplay1Part5Op2
  · exact caseReplay1Part5Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay1 : CoreSearch.replay 6 searchRows1 = false := by
  apply CoreSearch.replay_split (m := 6) (by decide +kernel) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact caseReplay1Part0
  · exact caseReplay1Part1
  · exact caseReplay1Part2
  · exact caseReplay1Part3
  · exact caseReplay1Part4
  · exact caseReplay1Part5

def searchRows2 : List Nat := [0xe5661e6be87f71b1fe4a8c00e84570b1, 0xd0f1db9cdf262c771021780c0e220c33, 0x4f7d3c9363d2f60be90810010192740a, 0x2fbb31ffaaa99f9c003061f212288b04, 0xdbf6cf56fddd4a6602848232f1dd0244]

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part0Op0 : CoreSearch.replaySliceChoice 7 searchRows2 0 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part0Op1 : CoreSearch.replaySliceChoice 7 searchRows2 0 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part0Op2 : CoreSearch.replaySliceChoice 7 searchRows2 0 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part0Op3 : CoreSearch.replaySliceChoice 7 searchRows2 0 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part0 : CoreSearch.replaySlice 7 searchRows2 0 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay2Part0Op0
  · exact caseReplay2Part0Op1
  · exact caseReplay2Part0Op2
  · exact caseReplay2Part0Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part1Op0 : CoreSearch.replaySliceChoice 7 searchRows2 1 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part1Op1 : CoreSearch.replaySliceChoice 7 searchRows2 1 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part1Op2 : CoreSearch.replaySliceChoice 7 searchRows2 1 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part1Op3 : CoreSearch.replaySliceChoice 7 searchRows2 1 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part1 : CoreSearch.replaySlice 7 searchRows2 1 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay2Part1Op0
  · exact caseReplay2Part1Op1
  · exact caseReplay2Part1Op2
  · exact caseReplay2Part1Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part2Op0 : CoreSearch.replaySliceChoice 7 searchRows2 2 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part2Op1 : CoreSearch.replaySliceChoice 7 searchRows2 2 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part2Op2 : CoreSearch.replaySliceChoice 7 searchRows2 2 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part2Op3 : CoreSearch.replaySliceChoice 7 searchRows2 2 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part2 : CoreSearch.replaySlice 7 searchRows2 2 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay2Part2Op0
  · exact caseReplay2Part2Op1
  · exact caseReplay2Part2Op2
  · exact caseReplay2Part2Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part3Op0 : CoreSearch.replaySliceChoice 7 searchRows2 3 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part3Op1 : CoreSearch.replaySliceChoice 7 searchRows2 3 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part3Op2 : CoreSearch.replaySliceChoice 7 searchRows2 3 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part3Op3 : CoreSearch.replaySliceChoice 7 searchRows2 3 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part3 : CoreSearch.replaySlice 7 searchRows2 3 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay2Part3Op0
  · exact caseReplay2Part3Op1
  · exact caseReplay2Part3Op2
  · exact caseReplay2Part3Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part4Op0 : CoreSearch.replaySliceChoice 7 searchRows2 4 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part4Op1 : CoreSearch.replaySliceChoice 7 searchRows2 4 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part4Op2 : CoreSearch.replaySliceChoice 7 searchRows2 4 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part4Op3 : CoreSearch.replaySliceChoice 7 searchRows2 4 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part4 : CoreSearch.replaySlice 7 searchRows2 4 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay2Part4Op0
  · exact caseReplay2Part4Op1
  · exact caseReplay2Part4Op2
  · exact caseReplay2Part4Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part5Op0 : CoreSearch.replaySliceChoice 7 searchRows2 5 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part5Op1 : CoreSearch.replaySliceChoice 7 searchRows2 5 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part5Op2 : CoreSearch.replaySliceChoice 7 searchRows2 5 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part5Op3 : CoreSearch.replaySliceChoice 7 searchRows2 5 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part5 : CoreSearch.replaySlice 7 searchRows2 5 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay2Part5Op0
  · exact caseReplay2Part5Op1
  · exact caseReplay2Part5Op2
  · exact caseReplay2Part5Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part6Op0 : CoreSearch.replaySliceChoice 7 searchRows2 6 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part6Op1 : CoreSearch.replaySliceChoice 7 searchRows2 6 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part6Op2 : CoreSearch.replaySliceChoice 7 searchRows2 6 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part6Op3 : CoreSearch.replaySliceChoice 7 searchRows2 6 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part6 : CoreSearch.replaySlice 7 searchRows2 6 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay2Part6Op0
  · exact caseReplay2Part6Op1
  · exact caseReplay2Part6Op2
  · exact caseReplay2Part6Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part7Op0 : CoreSearch.replaySliceChoice 7 searchRows2 7 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part7Op1 : CoreSearch.replaySliceChoice 7 searchRows2 7 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part7Op2 : CoreSearch.replaySliceChoice 7 searchRows2 7 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part7Op3 : CoreSearch.replaySliceChoice 7 searchRows2 7 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part7 : CoreSearch.replaySlice 7 searchRows2 7 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay2Part7Op0
  · exact caseReplay2Part7Op1
  · exact caseReplay2Part7Op2
  · exact caseReplay2Part7Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part8Op0 : CoreSearch.replaySliceChoice 7 searchRows2 8 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part8Op1 : CoreSearch.replaySliceChoice 7 searchRows2 8 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part8Op2 : CoreSearch.replaySliceChoice 7 searchRows2 8 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part8Op3 : CoreSearch.replaySliceChoice 7 searchRows2 8 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part8 : CoreSearch.replaySlice 7 searchRows2 8 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay2Part8Op0
  · exact caseReplay2Part8Op1
  · exact caseReplay2Part8Op2
  · exact caseReplay2Part8Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part9Op0 : CoreSearch.replaySliceChoice 7 searchRows2 9 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part9Op1 : CoreSearch.replaySliceChoice 7 searchRows2 9 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part9Op2 : CoreSearch.replaySliceChoice 7 searchRows2 9 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part9Op3 : CoreSearch.replaySliceChoice 7 searchRows2 9 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2Part9 : CoreSearch.replaySlice 7 searchRows2 9 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay2Part9Op0
  · exact caseReplay2Part9Op1
  · exact caseReplay2Part9Op2
  · exact caseReplay2Part9Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay2 : CoreSearch.replay 7 searchRows2 = false := by
  apply CoreSearch.replay_split (m := 10) (by decide +kernel) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact caseReplay2Part0
  · exact caseReplay2Part1
  · exact caseReplay2Part2
  · exact caseReplay2Part3
  · exact caseReplay2Part4
  · exact caseReplay2Part5
  · exact caseReplay2Part6
  · exact caseReplay2Part7
  · exact caseReplay2Part8
  · exact caseReplay2Part9

def searchRows3 : List Nat := [0xfa7f4fe299775eba090599c28932009a, 0x1c5ecab745cfec37144a420044cc4425, 0x6ea9cdbdf43396c7420ea4fd74339642, 0x85a03749afaffb4907e00201a30d0a09, 0x62734ca395150ea137fa4e3bf70d3ea9]

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part0Op0 : CoreSearch.replaySliceChoice 7 searchRows3 0 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part0Op1 : CoreSearch.replaySliceChoice 7 searchRows3 0 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part0Op2 : CoreSearch.replaySliceChoice 7 searchRows3 0 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part0Op3 : CoreSearch.replaySliceChoice 7 searchRows3 0 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part0 : CoreSearch.replaySlice 7 searchRows3 0 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay3Part0Op0
  · exact caseReplay3Part0Op1
  · exact caseReplay3Part0Op2
  · exact caseReplay3Part0Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part1Op0 : CoreSearch.replaySliceChoice 7 searchRows3 1 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part1Op1 : CoreSearch.replaySliceChoice 7 searchRows3 1 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part1Op2 : CoreSearch.replaySliceChoice 7 searchRows3 1 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part1Op3 : CoreSearch.replaySliceChoice 7 searchRows3 1 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part1 : CoreSearch.replaySlice 7 searchRows3 1 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay3Part1Op0
  · exact caseReplay3Part1Op1
  · exact caseReplay3Part1Op2
  · exact caseReplay3Part1Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part2Op0 : CoreSearch.replaySliceChoice 7 searchRows3 2 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part2Op1 : CoreSearch.replaySliceChoice 7 searchRows3 2 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part2Op2 : CoreSearch.replaySliceChoice 7 searchRows3 2 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part2Op3 : CoreSearch.replaySliceChoice 7 searchRows3 2 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part2 : CoreSearch.replaySlice 7 searchRows3 2 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay3Part2Op0
  · exact caseReplay3Part2Op1
  · exact caseReplay3Part2Op2
  · exact caseReplay3Part2Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part3Op0 : CoreSearch.replaySliceChoice 7 searchRows3 3 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part3Op1 : CoreSearch.replaySliceChoice 7 searchRows3 3 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part3Op2 : CoreSearch.replaySliceChoice 7 searchRows3 3 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part3Op3 : CoreSearch.replaySliceChoice 7 searchRows3 3 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part3 : CoreSearch.replaySlice 7 searchRows3 3 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay3Part3Op0
  · exact caseReplay3Part3Op1
  · exact caseReplay3Part3Op2
  · exact caseReplay3Part3Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part4Op0 : CoreSearch.replaySliceChoice 7 searchRows3 4 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part4Op1 : CoreSearch.replaySliceChoice 7 searchRows3 4 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part4Op2 : CoreSearch.replaySliceChoice 7 searchRows3 4 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part4Op3 : CoreSearch.replaySliceChoice 7 searchRows3 4 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part4 : CoreSearch.replaySlice 7 searchRows3 4 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay3Part4Op0
  · exact caseReplay3Part4Op1
  · exact caseReplay3Part4Op2
  · exact caseReplay3Part4Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part5Op0 : CoreSearch.replaySliceChoice 7 searchRows3 5 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part5Op1 : CoreSearch.replaySliceChoice 7 searchRows3 5 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part5Op2 : CoreSearch.replaySliceChoice 7 searchRows3 5 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part5Op3 : CoreSearch.replaySliceChoice 7 searchRows3 5 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part5 : CoreSearch.replaySlice 7 searchRows3 5 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay3Part5Op0
  · exact caseReplay3Part5Op1
  · exact caseReplay3Part5Op2
  · exact caseReplay3Part5Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part6Op0 : CoreSearch.replaySliceChoice 7 searchRows3 6 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part6Op1 : CoreSearch.replaySliceChoice 7 searchRows3 6 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part6Op2 : CoreSearch.replaySliceChoice 7 searchRows3 6 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part6Op3 : CoreSearch.replaySliceChoice 7 searchRows3 6 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part6 : CoreSearch.replaySlice 7 searchRows3 6 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay3Part6Op0
  · exact caseReplay3Part6Op1
  · exact caseReplay3Part6Op2
  · exact caseReplay3Part6Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part7Op0 : CoreSearch.replaySliceChoice 7 searchRows3 7 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part7Op1 : CoreSearch.replaySliceChoice 7 searchRows3 7 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part7Op2 : CoreSearch.replaySliceChoice 7 searchRows3 7 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part7Op3 : CoreSearch.replaySliceChoice 7 searchRows3 7 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part7 : CoreSearch.replaySlice 7 searchRows3 7 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay3Part7Op0
  · exact caseReplay3Part7Op1
  · exact caseReplay3Part7Op2
  · exact caseReplay3Part7Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part8Op0 : CoreSearch.replaySliceChoice 7 searchRows3 8 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part8Op1 : CoreSearch.replaySliceChoice 7 searchRows3 8 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part8Op2 : CoreSearch.replaySliceChoice 7 searchRows3 8 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part8Op3 : CoreSearch.replaySliceChoice 7 searchRows3 8 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part8 : CoreSearch.replaySlice 7 searchRows3 8 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay3Part8Op0
  · exact caseReplay3Part8Op1
  · exact caseReplay3Part8Op2
  · exact caseReplay3Part8Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part9Op0 : CoreSearch.replaySliceChoice 7 searchRows3 9 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part9Op1 : CoreSearch.replaySliceChoice 7 searchRows3 9 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part9Op2 : CoreSearch.replaySliceChoice 7 searchRows3 9 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part9Op3 : CoreSearch.replaySliceChoice 7 searchRows3 9 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3Part9 : CoreSearch.replaySlice 7 searchRows3 9 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay3Part9Op0
  · exact caseReplay3Part9Op1
  · exact caseReplay3Part9Op2
  · exact caseReplay3Part9Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay3 : CoreSearch.replay 7 searchRows3 = false := by
  apply CoreSearch.replay_split (m := 10) (by decide +kernel) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact caseReplay3Part0
  · exact caseReplay3Part1
  · exact caseReplay3Part2
  · exact caseReplay3Part3
  · exact caseReplay3Part4
  · exact caseReplay3Part5
  · exact caseReplay3Part6
  · exact caseReplay3Part7
  · exact caseReplay3Part8
  · exact caseReplay3Part9

def searchRows4 : List Nat := [0xfff2670b033de8de0c20000b03050006, 0xf81db9e4f4bfb726a08000444038b120, 0x155e8ed1cddbde91111e8e2084c20891, 0x5121fa363d5745e3570a303a3d4744c2, 0x6be1c39a9a5e7869c2c5d7c498187869]

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part0Op0 : CoreSearch.replaySliceChoice 7 searchRows4 0 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part0Op1 : CoreSearch.replaySliceChoice 7 searchRows4 0 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part0Op2 : CoreSearch.replaySliceChoice 7 searchRows4 0 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part0Op3 : CoreSearch.replaySliceChoice 7 searchRows4 0 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part0 : CoreSearch.replaySlice 7 searchRows4 0 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay4Part0Op0
  · exact caseReplay4Part0Op1
  · exact caseReplay4Part0Op2
  · exact caseReplay4Part0Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part1Op0 : CoreSearch.replaySliceChoice 7 searchRows4 1 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part1Op1 : CoreSearch.replaySliceChoice 7 searchRows4 1 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part1Op2 : CoreSearch.replaySliceChoice 7 searchRows4 1 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part1Op3 : CoreSearch.replaySliceChoice 7 searchRows4 1 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part1 : CoreSearch.replaySlice 7 searchRows4 1 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay4Part1Op0
  · exact caseReplay4Part1Op1
  · exact caseReplay4Part1Op2
  · exact caseReplay4Part1Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part2Op0 : CoreSearch.replaySliceChoice 7 searchRows4 2 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part2Op1 : CoreSearch.replaySliceChoice 7 searchRows4 2 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part2Op2 : CoreSearch.replaySliceChoice 7 searchRows4 2 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part2Op3 : CoreSearch.replaySliceChoice 7 searchRows4 2 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part2 : CoreSearch.replaySlice 7 searchRows4 2 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay4Part2Op0
  · exact caseReplay4Part2Op1
  · exact caseReplay4Part2Op2
  · exact caseReplay4Part2Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part3Op0 : CoreSearch.replaySliceChoice 7 searchRows4 3 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part3Op1 : CoreSearch.replaySliceChoice 7 searchRows4 3 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part3Op2 : CoreSearch.replaySliceChoice 7 searchRows4 3 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part3Op3 : CoreSearch.replaySliceChoice 7 searchRows4 3 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part3 : CoreSearch.replaySlice 7 searchRows4 3 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay4Part3Op0
  · exact caseReplay4Part3Op1
  · exact caseReplay4Part3Op2
  · exact caseReplay4Part3Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part4Op0 : CoreSearch.replaySliceChoice 7 searchRows4 4 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part4Op1 : CoreSearch.replaySliceChoice 7 searchRows4 4 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part4Op2 : CoreSearch.replaySliceChoice 7 searchRows4 4 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part4Op3 : CoreSearch.replaySliceChoice 7 searchRows4 4 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part4 : CoreSearch.replaySlice 7 searchRows4 4 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay4Part4Op0
  · exact caseReplay4Part4Op1
  · exact caseReplay4Part4Op2
  · exact caseReplay4Part4Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part5Op0 : CoreSearch.replaySliceChoice 7 searchRows4 5 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part5Op1 : CoreSearch.replaySliceChoice 7 searchRows4 5 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part5Op2 : CoreSearch.replaySliceChoice 7 searchRows4 5 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part5Op3 : CoreSearch.replaySliceChoice 7 searchRows4 5 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part5 : CoreSearch.replaySlice 7 searchRows4 5 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay4Part5Op0
  · exact caseReplay4Part5Op1
  · exact caseReplay4Part5Op2
  · exact caseReplay4Part5Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part6Op0 : CoreSearch.replaySliceChoice 7 searchRows4 6 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part6Op1 : CoreSearch.replaySliceChoice 7 searchRows4 6 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part6Op2 : CoreSearch.replaySliceChoice 7 searchRows4 6 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part6Op3 : CoreSearch.replaySliceChoice 7 searchRows4 6 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part6 : CoreSearch.replaySlice 7 searchRows4 6 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay4Part6Op0
  · exact caseReplay4Part6Op1
  · exact caseReplay4Part6Op2
  · exact caseReplay4Part6Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part7Op0 : CoreSearch.replaySliceChoice 7 searchRows4 7 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part7Op1 : CoreSearch.replaySliceChoice 7 searchRows4 7 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part7Op2 : CoreSearch.replaySliceChoice 7 searchRows4 7 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part7Op3 : CoreSearch.replaySliceChoice 7 searchRows4 7 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part7 : CoreSearch.replaySlice 7 searchRows4 7 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay4Part7Op0
  · exact caseReplay4Part7Op1
  · exact caseReplay4Part7Op2
  · exact caseReplay4Part7Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part8Op0 : CoreSearch.replaySliceChoice 7 searchRows4 8 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part8Op1 : CoreSearch.replaySliceChoice 7 searchRows4 8 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part8Op2 : CoreSearch.replaySliceChoice 7 searchRows4 8 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part8Op3 : CoreSearch.replaySliceChoice 7 searchRows4 8 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part8 : CoreSearch.replaySlice 7 searchRows4 8 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay4Part8Op0
  · exact caseReplay4Part8Op1
  · exact caseReplay4Part8Op2
  · exact caseReplay4Part8Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part9Op0 : CoreSearch.replaySliceChoice 7 searchRows4 9 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part9Op1 : CoreSearch.replaySliceChoice 7 searchRows4 9 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part9Op2 : CoreSearch.replaySliceChoice 7 searchRows4 9 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part9Op3 : CoreSearch.replaySliceChoice 7 searchRows4 9 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4Part9 : CoreSearch.replaySlice 7 searchRows4 9 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay4Part9Op0
  · exact caseReplay4Part9Op1
  · exact caseReplay4Part9Op2
  · exact caseReplay4Part9Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay4 : CoreSearch.replay 7 searchRows4 = false := by
  apply CoreSearch.replay_split (m := 10) (by decide +kernel) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact caseReplay4Part0
  · exact caseReplay4Part1
  · exact caseReplay4Part2
  · exact caseReplay4Part3
  · exact caseReplay4Part4
  · exact caseReplay4Part5
  · exact caseReplay4Part6
  · exact caseReplay4Part7
  · exact caseReplay4Part8
  · exact caseReplay4Part9

def searchRows5 : List Nat := [0xfd6df3afc3cffd790029700b80c61021, 0x370e30cf1e4ad60bb6dfa4131a6ede0b, 0xd3936c707f37baa79d0a041257260a85, 0x64f4addeb279c9cf46d285c43239894a, 0x1b7e56651d9bf6560b5401640d198456]

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part0Op0 : CoreSearch.replaySliceChoice 7 searchRows5 0 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part0Op1 : CoreSearch.replaySliceChoice 7 searchRows5 0 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part0Op2 : CoreSearch.replaySliceChoice 7 searchRows5 0 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part0Op3 : CoreSearch.replaySliceChoice 7 searchRows5 0 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part0 : CoreSearch.replaySlice 7 searchRows5 0 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay5Part0Op0
  · exact caseReplay5Part0Op1
  · exact caseReplay5Part0Op2
  · exact caseReplay5Part0Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part1Op0 : CoreSearch.replaySliceChoice 7 searchRows5 1 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part1Op1 : CoreSearch.replaySliceChoice 7 searchRows5 1 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part1Op2 : CoreSearch.replaySliceChoice 7 searchRows5 1 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part1Op3 : CoreSearch.replaySliceChoice 7 searchRows5 1 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part1 : CoreSearch.replaySlice 7 searchRows5 1 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay5Part1Op0
  · exact caseReplay5Part1Op1
  · exact caseReplay5Part1Op2
  · exact caseReplay5Part1Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part2Op0 : CoreSearch.replaySliceChoice 7 searchRows5 2 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part2Op1 : CoreSearch.replaySliceChoice 7 searchRows5 2 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part2Op2 : CoreSearch.replaySliceChoice 7 searchRows5 2 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part2Op3 : CoreSearch.replaySliceChoice 7 searchRows5 2 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part2 : CoreSearch.replaySlice 7 searchRows5 2 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay5Part2Op0
  · exact caseReplay5Part2Op1
  · exact caseReplay5Part2Op2
  · exact caseReplay5Part2Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part3Op0 : CoreSearch.replaySliceChoice 7 searchRows5 3 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part3Op1 : CoreSearch.replaySliceChoice 7 searchRows5 3 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part3Op2 : CoreSearch.replaySliceChoice 7 searchRows5 3 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part3Op3 : CoreSearch.replaySliceChoice 7 searchRows5 3 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part3 : CoreSearch.replaySlice 7 searchRows5 3 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay5Part3Op0
  · exact caseReplay5Part3Op1
  · exact caseReplay5Part3Op2
  · exact caseReplay5Part3Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part4Op0 : CoreSearch.replaySliceChoice 7 searchRows5 4 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part4Op1 : CoreSearch.replaySliceChoice 7 searchRows5 4 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part4Op2 : CoreSearch.replaySliceChoice 7 searchRows5 4 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part4Op3 : CoreSearch.replaySliceChoice 7 searchRows5 4 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part4 : CoreSearch.replaySlice 7 searchRows5 4 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay5Part4Op0
  · exact caseReplay5Part4Op1
  · exact caseReplay5Part4Op2
  · exact caseReplay5Part4Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part5Op0 : CoreSearch.replaySliceChoice 7 searchRows5 5 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part5Op1 : CoreSearch.replaySliceChoice 7 searchRows5 5 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part5Op2 : CoreSearch.replaySliceChoice 7 searchRows5 5 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part5Op3 : CoreSearch.replaySliceChoice 7 searchRows5 5 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part5 : CoreSearch.replaySlice 7 searchRows5 5 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay5Part5Op0
  · exact caseReplay5Part5Op1
  · exact caseReplay5Part5Op2
  · exact caseReplay5Part5Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part6Op0 : CoreSearch.replaySliceChoice 7 searchRows5 6 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part6Op1 : CoreSearch.replaySliceChoice 7 searchRows5 6 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part6Op2 : CoreSearch.replaySliceChoice 7 searchRows5 6 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part6Op3 : CoreSearch.replaySliceChoice 7 searchRows5 6 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part6 : CoreSearch.replaySlice 7 searchRows5 6 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay5Part6Op0
  · exact caseReplay5Part6Op1
  · exact caseReplay5Part6Op2
  · exact caseReplay5Part6Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part7Op0 : CoreSearch.replaySliceChoice 7 searchRows5 7 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part7Op1 : CoreSearch.replaySliceChoice 7 searchRows5 7 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part7Op2 : CoreSearch.replaySliceChoice 7 searchRows5 7 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part7Op3 : CoreSearch.replaySliceChoice 7 searchRows5 7 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part7 : CoreSearch.replaySlice 7 searchRows5 7 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay5Part7Op0
  · exact caseReplay5Part7Op1
  · exact caseReplay5Part7Op2
  · exact caseReplay5Part7Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part8Op0 : CoreSearch.replaySliceChoice 7 searchRows5 8 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part8Op1 : CoreSearch.replaySliceChoice 7 searchRows5 8 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part8Op2 : CoreSearch.replaySliceChoice 7 searchRows5 8 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part8Op3 : CoreSearch.replaySliceChoice 7 searchRows5 8 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part8 : CoreSearch.replaySlice 7 searchRows5 8 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay5Part8Op0
  · exact caseReplay5Part8Op1
  · exact caseReplay5Part8Op2
  · exact caseReplay5Part8Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part9Op0 : CoreSearch.replaySliceChoice 7 searchRows5 9 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part9Op1 : CoreSearch.replaySliceChoice 7 searchRows5 9 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part9Op2 : CoreSearch.replaySliceChoice 7 searchRows5 9 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part9Op3 : CoreSearch.replaySliceChoice 7 searchRows5 9 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5Part9 : CoreSearch.replaySlice 7 searchRows5 9 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay5Part9Op0
  · exact caseReplay5Part9Op1
  · exact caseReplay5Part9Op2
  · exact caseReplay5Part9Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay5 : CoreSearch.replay 7 searchRows5 = false := by
  apply CoreSearch.replay_split (m := 10) (by decide +kernel) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact caseReplay5Part0
  · exact caseReplay5Part1
  · exact caseReplay5Part2
  · exact caseReplay5Part3
  · exact caseReplay5Part4
  · exact caseReplay5Part5
  · exact caseReplay5Part6
  · exact caseReplay5Part7
  · exact caseReplay5Part8
  · exact caseReplay5Part9

def searchRows6 : List Nat := [0xebf71ded9cf7edf122d1118584662091, 0xcf8c3abd65ddb4e66b0eee89619590e6, 0x169ce39a736ffa2f00a06008314a8229, 0x6573b6fcba99659f5c2a84701a99050e, 0xda9ff9134f33de5c985e90524e310c54]

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part0Op0 : CoreSearch.replaySliceChoice 7 searchRows6 0 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part0Op1 : CoreSearch.replaySliceChoice 7 searchRows6 0 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part0Op2 : CoreSearch.replaySliceChoice 7 searchRows6 0 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part0Op3 : CoreSearch.replaySliceChoice 7 searchRows6 0 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part0 : CoreSearch.replaySlice 7 searchRows6 0 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay6Part0Op0
  · exact caseReplay6Part0Op1
  · exact caseReplay6Part0Op2
  · exact caseReplay6Part0Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part1Op0 : CoreSearch.replaySliceChoice 7 searchRows6 1 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part1Op1 : CoreSearch.replaySliceChoice 7 searchRows6 1 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part1Op2 : CoreSearch.replaySliceChoice 7 searchRows6 1 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part1Op3 : CoreSearch.replaySliceChoice 7 searchRows6 1 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part1 : CoreSearch.replaySlice 7 searchRows6 1 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay6Part1Op0
  · exact caseReplay6Part1Op1
  · exact caseReplay6Part1Op2
  · exact caseReplay6Part1Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part2Op0 : CoreSearch.replaySliceChoice 7 searchRows6 2 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part2Op1 : CoreSearch.replaySliceChoice 7 searchRows6 2 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part2Op2 : CoreSearch.replaySliceChoice 7 searchRows6 2 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part2Op3 : CoreSearch.replaySliceChoice 7 searchRows6 2 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part2 : CoreSearch.replaySlice 7 searchRows6 2 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay6Part2Op0
  · exact caseReplay6Part2Op1
  · exact caseReplay6Part2Op2
  · exact caseReplay6Part2Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part3Op0 : CoreSearch.replaySliceChoice 7 searchRows6 3 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part3Op1 : CoreSearch.replaySliceChoice 7 searchRows6 3 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part3Op2 : CoreSearch.replaySliceChoice 7 searchRows6 3 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part3Op3 : CoreSearch.replaySliceChoice 7 searchRows6 3 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part3 : CoreSearch.replaySlice 7 searchRows6 3 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay6Part3Op0
  · exact caseReplay6Part3Op1
  · exact caseReplay6Part3Op2
  · exact caseReplay6Part3Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part4Op0 : CoreSearch.replaySliceChoice 7 searchRows6 4 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part4Op1 : CoreSearch.replaySliceChoice 7 searchRows6 4 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part4Op2 : CoreSearch.replaySliceChoice 7 searchRows6 4 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part4Op3 : CoreSearch.replaySliceChoice 7 searchRows6 4 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part4 : CoreSearch.replaySlice 7 searchRows6 4 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay6Part4Op0
  · exact caseReplay6Part4Op1
  · exact caseReplay6Part4Op2
  · exact caseReplay6Part4Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part5Op0 : CoreSearch.replaySliceChoice 7 searchRows6 5 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part5Op1 : CoreSearch.replaySliceChoice 7 searchRows6 5 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part5Op2 : CoreSearch.replaySliceChoice 7 searchRows6 5 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part5Op3 : CoreSearch.replaySliceChoice 7 searchRows6 5 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part5 : CoreSearch.replaySlice 7 searchRows6 5 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay6Part5Op0
  · exact caseReplay6Part5Op1
  · exact caseReplay6Part5Op2
  · exact caseReplay6Part5Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part6Op0 : CoreSearch.replaySliceChoice 7 searchRows6 6 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part6Op1 : CoreSearch.replaySliceChoice 7 searchRows6 6 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part6Op2 : CoreSearch.replaySliceChoice 7 searchRows6 6 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part6Op3 : CoreSearch.replaySliceChoice 7 searchRows6 6 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part6 : CoreSearch.replaySlice 7 searchRows6 6 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay6Part6Op0
  · exact caseReplay6Part6Op1
  · exact caseReplay6Part6Op2
  · exact caseReplay6Part6Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part7Op0 : CoreSearch.replaySliceChoice 7 searchRows6 7 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part7Op1 : CoreSearch.replaySliceChoice 7 searchRows6 7 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part7Op2 : CoreSearch.replaySliceChoice 7 searchRows6 7 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part7Op3 : CoreSearch.replaySliceChoice 7 searchRows6 7 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part7 : CoreSearch.replaySlice 7 searchRows6 7 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay6Part7Op0
  · exact caseReplay6Part7Op1
  · exact caseReplay6Part7Op2
  · exact caseReplay6Part7Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part8Op0 : CoreSearch.replaySliceChoice 7 searchRows6 8 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part8Op1 : CoreSearch.replaySliceChoice 7 searchRows6 8 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part8Op2 : CoreSearch.replaySliceChoice 7 searchRows6 8 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part8Op3 : CoreSearch.replaySliceChoice 7 searchRows6 8 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part8 : CoreSearch.replaySlice 7 searchRows6 8 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay6Part8Op0
  · exact caseReplay6Part8Op1
  · exact caseReplay6Part8Op2
  · exact caseReplay6Part8Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part9Op0 : CoreSearch.replaySliceChoice 7 searchRows6 9 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part9Op1 : CoreSearch.replaySliceChoice 7 searchRows6 9 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part9Op2 : CoreSearch.replaySliceChoice 7 searchRows6 9 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part9Op3 : CoreSearch.replaySliceChoice 7 searchRows6 9 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6Part9 : CoreSearch.replaySlice 7 searchRows6 9 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay6Part9Op0
  · exact caseReplay6Part9Op1
  · exact caseReplay6Part9Op2
  · exact caseReplay6Part9Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay6 : CoreSearch.replay 7 searchRows6 = false := by
  apply CoreSearch.replay_split (m := 10) (by decide +kernel) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact caseReplay6Part0
  · exact caseReplay6Part1
  · exact caseReplay6Part2
  · exact caseReplay6Part3
  · exact caseReplay6Part4
  · exact caseReplay6Part5
  · exact caseReplay6Part6
  · exact caseReplay6Part7
  · exact caseReplay6Part8
  · exact caseReplay6Part9

def searchRows7 : List Nat := [0x69b7d9aff436c7fb4205a18e6024c61b, 0xf7ecf657efdf3e9505601651855a2084, 0x9dd32dfe59e9d96b9094282210a15961, 0x36dbda9ad6ac28fe22f34060f28c08fe, 0xba5a1f39eb15eb265e0b18387b15ab22]

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part0Op0 : CoreSearch.replaySliceChoice 7 searchRows7 0 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part0Op1 : CoreSearch.replaySliceChoice 7 searchRows7 0 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part0Op2 : CoreSearch.replaySliceChoice 7 searchRows7 0 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part0Op3 : CoreSearch.replaySliceChoice 7 searchRows7 0 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part0 : CoreSearch.replaySlice 7 searchRows7 0 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay7Part0Op0
  · exact caseReplay7Part0Op1
  · exact caseReplay7Part0Op2
  · exact caseReplay7Part0Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part1Op0 : CoreSearch.replaySliceChoice 7 searchRows7 1 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part1Op1 : CoreSearch.replaySliceChoice 7 searchRows7 1 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part1Op2 : CoreSearch.replaySliceChoice 7 searchRows7 1 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part1Op3 : CoreSearch.replaySliceChoice 7 searchRows7 1 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part1 : CoreSearch.replaySlice 7 searchRows7 1 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay7Part1Op0
  · exact caseReplay7Part1Op1
  · exact caseReplay7Part1Op2
  · exact caseReplay7Part1Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part2Op0 : CoreSearch.replaySliceChoice 7 searchRows7 2 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part2Op1 : CoreSearch.replaySliceChoice 7 searchRows7 2 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part2Op2 : CoreSearch.replaySliceChoice 7 searchRows7 2 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part2Op3 : CoreSearch.replaySliceChoice 7 searchRows7 2 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part2 : CoreSearch.replaySlice 7 searchRows7 2 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay7Part2Op0
  · exact caseReplay7Part2Op1
  · exact caseReplay7Part2Op2
  · exact caseReplay7Part2Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part3Op0 : CoreSearch.replaySliceChoice 7 searchRows7 3 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part3Op1 : CoreSearch.replaySliceChoice 7 searchRows7 3 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part3Op2 : CoreSearch.replaySliceChoice 7 searchRows7 3 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part3Op3 : CoreSearch.replaySliceChoice 7 searchRows7 3 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part3 : CoreSearch.replaySlice 7 searchRows7 3 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay7Part3Op0
  · exact caseReplay7Part3Op1
  · exact caseReplay7Part3Op2
  · exact caseReplay7Part3Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part4Op0 : CoreSearch.replaySliceChoice 7 searchRows7 4 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part4Op1 : CoreSearch.replaySliceChoice 7 searchRows7 4 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part4Op2 : CoreSearch.replaySliceChoice 7 searchRows7 4 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part4Op3 : CoreSearch.replaySliceChoice 7 searchRows7 4 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part4 : CoreSearch.replaySlice 7 searchRows7 4 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay7Part4Op0
  · exact caseReplay7Part4Op1
  · exact caseReplay7Part4Op2
  · exact caseReplay7Part4Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part5Op0 : CoreSearch.replaySliceChoice 7 searchRows7 5 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part5Op1 : CoreSearch.replaySliceChoice 7 searchRows7 5 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part5Op2 : CoreSearch.replaySliceChoice 7 searchRows7 5 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part5Op3 : CoreSearch.replaySliceChoice 7 searchRows7 5 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part5 : CoreSearch.replaySlice 7 searchRows7 5 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay7Part5Op0
  · exact caseReplay7Part5Op1
  · exact caseReplay7Part5Op2
  · exact caseReplay7Part5Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part6Op0 : CoreSearch.replaySliceChoice 7 searchRows7 6 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part6Op1 : CoreSearch.replaySliceChoice 7 searchRows7 6 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part6Op2 : CoreSearch.replaySliceChoice 7 searchRows7 6 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part6Op3 : CoreSearch.replaySliceChoice 7 searchRows7 6 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part6 : CoreSearch.replaySlice 7 searchRows7 6 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay7Part6Op0
  · exact caseReplay7Part6Op1
  · exact caseReplay7Part6Op2
  · exact caseReplay7Part6Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part7Op0 : CoreSearch.replaySliceChoice 7 searchRows7 7 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part7Op1 : CoreSearch.replaySliceChoice 7 searchRows7 7 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part7Op2 : CoreSearch.replaySliceChoice 7 searchRows7 7 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part7Op3 : CoreSearch.replaySliceChoice 7 searchRows7 7 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part7 : CoreSearch.replaySlice 7 searchRows7 7 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay7Part7Op0
  · exact caseReplay7Part7Op1
  · exact caseReplay7Part7Op2
  · exact caseReplay7Part7Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part8Op0 : CoreSearch.replaySliceChoice 7 searchRows7 8 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part8Op1 : CoreSearch.replaySliceChoice 7 searchRows7 8 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part8Op2 : CoreSearch.replaySliceChoice 7 searchRows7 8 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part8Op3 : CoreSearch.replaySliceChoice 7 searchRows7 8 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part8 : CoreSearch.replaySlice 7 searchRows7 8 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay7Part8Op0
  · exact caseReplay7Part8Op1
  · exact caseReplay7Part8Op2
  · exact caseReplay7Part8Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part9Op0 : CoreSearch.replaySliceChoice 7 searchRows7 9 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part9Op1 : CoreSearch.replaySliceChoice 7 searchRows7 9 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part9Op2 : CoreSearch.replaySliceChoice 7 searchRows7 9 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part9Op3 : CoreSearch.replaySliceChoice 7 searchRows7 9 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7Part9 : CoreSearch.replaySlice 7 searchRows7 9 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay7Part9Op0
  · exact caseReplay7Part9Op1
  · exact caseReplay7Part9Op2
  · exact caseReplay7Part9Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay7 : CoreSearch.replay 7 searchRows7 = false := by
  apply CoreSearch.replay_split (m := 10) (by decide +kernel) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact caseReplay7Part0
  · exact caseReplay7Part1
  · exact caseReplay7Part2
  · exact caseReplay7Part3
  · exact caseReplay7Part4
  · exact caseReplay7Part5
  · exact caseReplay7Part6
  · exact caseReplay7Part7
  · exact caseReplay7Part8
  · exact caseReplay7Part9

def searchRows8 : List Nat := [0xefdfeffffbffedf50420000002820160, 0x5fba72ebb71e96ab0941850aed2c4683, 0x8ac0e0b74aff699128c6f75be540d893, 0x3fffbf0c0dd63a4fe24a643e6000980f]

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay8Part0 : CoreSearch.replaySlice 5 searchRows8 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay8Part1 : CoreSearch.replaySlice 5 searchRows8 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay8Part2 : CoreSearch.replaySlice 5 searchRows8 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay8Part3 : CoreSearch.replaySlice 5 searchRows8 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay8Part4 : CoreSearch.replaySlice 5 searchRows8 4 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay8Part5 : CoreSearch.replaySlice 5 searchRows8 5 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay8 : CoreSearch.replay 5 searchRows8 = false := by
  apply CoreSearch.replay_split (m := 6) (by decide +kernel) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact caseReplay8Part0
  · exact caseReplay8Part1
  · exact caseReplay8Part2
  · exact caseReplay8Part3
  · exact caseReplay8Part4
  · exact caseReplay8Part5

def searchRows9 : List Nat := [0x9eaf9bdc4bff9d384c4c400141002128, 0x7bdaed1eefd9e4e321030a2820040482, 0x4eefd44ce4d749d1928021429ef39a51, 0xfd9ffff33531ba0f0080000282839a01]

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay9Part0 : CoreSearch.replaySlice 5 searchRows9 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay9Part1 : CoreSearch.replaySlice 5 searchRows9 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay9Part2 : CoreSearch.replaySlice 5 searchRows9 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay9Part3 : CoreSearch.replaySlice 5 searchRows9 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay9Part4 : CoreSearch.replaySlice 5 searchRows9 4 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay9Part5 : CoreSearch.replaySlice 5 searchRows9 5 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay9 : CoreSearch.replay 5 searchRows9 = false := by
  apply CoreSearch.replay_split (m := 6) (by decide +kernel) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact caseReplay9Part0
  · exact caseReplay9Part1
  · exact caseReplay9Part2
  · exact caseReplay9Part3
  · exact caseReplay9Part4
  · exact caseReplay9Part5

def searchRows10 : List Nat := [0x7c26dfc911ff953b302412e10198910a, 0x8a4d621b669f69550221419126852115, 0x41db78678e3efa9232122c22063ed292, 0x189bbf8a3cebe64b8c8b851e38636641, 0xefff0074eb4ddfe4cc488004c8400060]

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part0Op0 : CoreSearch.replaySliceChoice 7 searchRows10 0 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part0Op1 : CoreSearch.replaySliceChoice 7 searchRows10 0 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part0Op2 : CoreSearch.replaySliceChoice 7 searchRows10 0 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part0Op3 : CoreSearch.replaySliceChoice 7 searchRows10 0 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part0 : CoreSearch.replaySlice 7 searchRows10 0 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay10Part0Op0
  · exact caseReplay10Part0Op1
  · exact caseReplay10Part0Op2
  · exact caseReplay10Part0Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part1Op0 : CoreSearch.replaySliceChoice 7 searchRows10 1 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part1Op1 : CoreSearch.replaySliceChoice 7 searchRows10 1 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part1Op2 : CoreSearch.replaySliceChoice 7 searchRows10 1 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part1Op3 : CoreSearch.replaySliceChoice 7 searchRows10 1 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part1 : CoreSearch.replaySlice 7 searchRows10 1 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay10Part1Op0
  · exact caseReplay10Part1Op1
  · exact caseReplay10Part1Op2
  · exact caseReplay10Part1Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part2Op0 : CoreSearch.replaySliceChoice 7 searchRows10 2 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part2Op1 : CoreSearch.replaySliceChoice 7 searchRows10 2 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part2Op2 : CoreSearch.replaySliceChoice 7 searchRows10 2 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part2Op3 : CoreSearch.replaySliceChoice 7 searchRows10 2 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part2 : CoreSearch.replaySlice 7 searchRows10 2 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay10Part2Op0
  · exact caseReplay10Part2Op1
  · exact caseReplay10Part2Op2
  · exact caseReplay10Part2Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part3Op0 : CoreSearch.replaySliceChoice 7 searchRows10 3 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part3Op1 : CoreSearch.replaySliceChoice 7 searchRows10 3 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part3Op2 : CoreSearch.replaySliceChoice 7 searchRows10 3 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part3Op3 : CoreSearch.replaySliceChoice 7 searchRows10 3 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part3 : CoreSearch.replaySlice 7 searchRows10 3 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay10Part3Op0
  · exact caseReplay10Part3Op1
  · exact caseReplay10Part3Op2
  · exact caseReplay10Part3Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part4Op0 : CoreSearch.replaySliceChoice 7 searchRows10 4 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part4Op1 : CoreSearch.replaySliceChoice 7 searchRows10 4 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part4Op2 : CoreSearch.replaySliceChoice 7 searchRows10 4 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part4Op3 : CoreSearch.replaySliceChoice 7 searchRows10 4 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part4 : CoreSearch.replaySlice 7 searchRows10 4 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay10Part4Op0
  · exact caseReplay10Part4Op1
  · exact caseReplay10Part4Op2
  · exact caseReplay10Part4Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part5Op0 : CoreSearch.replaySliceChoice 7 searchRows10 5 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part5Op1 : CoreSearch.replaySliceChoice 7 searchRows10 5 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part5Op2 : CoreSearch.replaySliceChoice 7 searchRows10 5 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part5Op3 : CoreSearch.replaySliceChoice 7 searchRows10 5 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part5 : CoreSearch.replaySlice 7 searchRows10 5 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay10Part5Op0
  · exact caseReplay10Part5Op1
  · exact caseReplay10Part5Op2
  · exact caseReplay10Part5Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part6Op0 : CoreSearch.replaySliceChoice 7 searchRows10 6 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part6Op1 : CoreSearch.replaySliceChoice 7 searchRows10 6 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part6Op2 : CoreSearch.replaySliceChoice 7 searchRows10 6 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part6Op3 : CoreSearch.replaySliceChoice 7 searchRows10 6 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part6 : CoreSearch.replaySlice 7 searchRows10 6 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay10Part6Op0
  · exact caseReplay10Part6Op1
  · exact caseReplay10Part6Op2
  · exact caseReplay10Part6Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part7Op0 : CoreSearch.replaySliceChoice 7 searchRows10 7 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part7Op1 : CoreSearch.replaySliceChoice 7 searchRows10 7 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part7Op2 : CoreSearch.replaySliceChoice 7 searchRows10 7 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part7Op3 : CoreSearch.replaySliceChoice 7 searchRows10 7 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part7 : CoreSearch.replaySlice 7 searchRows10 7 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay10Part7Op0
  · exact caseReplay10Part7Op1
  · exact caseReplay10Part7Op2
  · exact caseReplay10Part7Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part8Op0 : CoreSearch.replaySliceChoice 7 searchRows10 8 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part8Op1 : CoreSearch.replaySliceChoice 7 searchRows10 8 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part8Op2 : CoreSearch.replaySliceChoice 7 searchRows10 8 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part8Op3 : CoreSearch.replaySliceChoice 7 searchRows10 8 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part8 : CoreSearch.replaySlice 7 searchRows10 8 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay10Part8Op0
  · exact caseReplay10Part8Op1
  · exact caseReplay10Part8Op2
  · exact caseReplay10Part8Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part9Op0 : CoreSearch.replaySliceChoice 7 searchRows10 9 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part9Op1 : CoreSearch.replaySliceChoice 7 searchRows10 9 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part9Op2 : CoreSearch.replaySliceChoice 7 searchRows10 9 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part9Op3 : CoreSearch.replaySliceChoice 7 searchRows10 9 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10Part9 : CoreSearch.replaySlice 7 searchRows10 9 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay10Part9Op0
  · exact caseReplay10Part9Op1
  · exact caseReplay10Part9Op2
  · exact caseReplay10Part9Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay10 : CoreSearch.replay 7 searchRows10 = false := by
  apply CoreSearch.replay_split (m := 10) (by decide +kernel) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact caseReplay10Part0
  · exact caseReplay10Part1
  · exact caseReplay10Part2
  · exact caseReplay10Part3
  · exact caseReplay10Part4
  · exact caseReplay10Part5
  · exact caseReplay10Part6
  · exact caseReplay10Part7
  · exact caseReplay10Part8
  · exact caseReplay10Part9

def searchRows11 : List Nat := [0xacc389ba2f5fbe5d8cc98408264a004d, 0xff3cf7fdf4abf5b379102511e0a22411, 0xb3859a1d927f7a9ac2c49a10907d0a9a, 0x3fc3b377f911d7cc2312586559119780, 0xc9bf7eca57e5eb2702094a8a17058326]

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part0Op0 : CoreSearch.replaySliceChoice 7 searchRows11 0 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part0Op1 : CoreSearch.replaySliceChoice 7 searchRows11 0 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part0Op2 : CoreSearch.replaySliceChoice 7 searchRows11 0 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part0Op3 : CoreSearch.replaySliceChoice 7 searchRows11 0 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part0 : CoreSearch.replaySlice 7 searchRows11 0 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay11Part0Op0
  · exact caseReplay11Part0Op1
  · exact caseReplay11Part0Op2
  · exact caseReplay11Part0Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part1Op0 : CoreSearch.replaySliceChoice 7 searchRows11 1 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part1Op1 : CoreSearch.replaySliceChoice 7 searchRows11 1 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part1Op2 : CoreSearch.replaySliceChoice 7 searchRows11 1 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part1Op3 : CoreSearch.replaySliceChoice 7 searchRows11 1 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part1 : CoreSearch.replaySlice 7 searchRows11 1 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay11Part1Op0
  · exact caseReplay11Part1Op1
  · exact caseReplay11Part1Op2
  · exact caseReplay11Part1Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part2Op0 : CoreSearch.replaySliceChoice 7 searchRows11 2 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part2Op1 : CoreSearch.replaySliceChoice 7 searchRows11 2 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part2Op2 : CoreSearch.replaySliceChoice 7 searchRows11 2 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part2Op3 : CoreSearch.replaySliceChoice 7 searchRows11 2 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part2 : CoreSearch.replaySlice 7 searchRows11 2 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay11Part2Op0
  · exact caseReplay11Part2Op1
  · exact caseReplay11Part2Op2
  · exact caseReplay11Part2Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part3Op0 : CoreSearch.replaySliceChoice 7 searchRows11 3 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part3Op1 : CoreSearch.replaySliceChoice 7 searchRows11 3 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part3Op2 : CoreSearch.replaySliceChoice 7 searchRows11 3 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part3Op3 : CoreSearch.replaySliceChoice 7 searchRows11 3 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part3 : CoreSearch.replaySlice 7 searchRows11 3 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay11Part3Op0
  · exact caseReplay11Part3Op1
  · exact caseReplay11Part3Op2
  · exact caseReplay11Part3Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part4Op0 : CoreSearch.replaySliceChoice 7 searchRows11 4 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part4Op1 : CoreSearch.replaySliceChoice 7 searchRows11 4 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part4Op2 : CoreSearch.replaySliceChoice 7 searchRows11 4 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part4Op3 : CoreSearch.replaySliceChoice 7 searchRows11 4 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part4 : CoreSearch.replaySlice 7 searchRows11 4 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay11Part4Op0
  · exact caseReplay11Part4Op1
  · exact caseReplay11Part4Op2
  · exact caseReplay11Part4Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part5Op0 : CoreSearch.replaySliceChoice 7 searchRows11 5 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part5Op1 : CoreSearch.replaySliceChoice 7 searchRows11 5 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part5Op2 : CoreSearch.replaySliceChoice 7 searchRows11 5 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part5Op3 : CoreSearch.replaySliceChoice 7 searchRows11 5 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part5 : CoreSearch.replaySlice 7 searchRows11 5 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay11Part5Op0
  · exact caseReplay11Part5Op1
  · exact caseReplay11Part5Op2
  · exact caseReplay11Part5Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part6Op0 : CoreSearch.replaySliceChoice 7 searchRows11 6 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part6Op1 : CoreSearch.replaySliceChoice 7 searchRows11 6 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part6Op2 : CoreSearch.replaySliceChoice 7 searchRows11 6 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part6Op3 : CoreSearch.replaySliceChoice 7 searchRows11 6 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part6 : CoreSearch.replaySlice 7 searchRows11 6 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay11Part6Op0
  · exact caseReplay11Part6Op1
  · exact caseReplay11Part6Op2
  · exact caseReplay11Part6Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part7Op0 : CoreSearch.replaySliceChoice 7 searchRows11 7 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part7Op1 : CoreSearch.replaySliceChoice 7 searchRows11 7 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part7Op2 : CoreSearch.replaySliceChoice 7 searchRows11 7 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part7Op3 : CoreSearch.replaySliceChoice 7 searchRows11 7 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part7 : CoreSearch.replaySlice 7 searchRows11 7 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay11Part7Op0
  · exact caseReplay11Part7Op1
  · exact caseReplay11Part7Op2
  · exact caseReplay11Part7Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part8Op0 : CoreSearch.replaySliceChoice 7 searchRows11 8 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part8Op1 : CoreSearch.replaySliceChoice 7 searchRows11 8 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part8Op2 : CoreSearch.replaySliceChoice 7 searchRows11 8 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part8Op3 : CoreSearch.replaySliceChoice 7 searchRows11 8 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part8 : CoreSearch.replaySlice 7 searchRows11 8 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay11Part8Op0
  · exact caseReplay11Part8Op1
  · exact caseReplay11Part8Op2
  · exact caseReplay11Part8Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part9Op0 : CoreSearch.replaySliceChoice 7 searchRows11 9 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part9Op1 : CoreSearch.replaySliceChoice 7 searchRows11 9 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part9Op2 : CoreSearch.replaySliceChoice 7 searchRows11 9 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part9Op3 : CoreSearch.replaySliceChoice 7 searchRows11 9 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11Part9 : CoreSearch.replaySlice 7 searchRows11 9 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay11Part9Op0
  · exact caseReplay11Part9Op1
  · exact caseReplay11Part9Op2
  · exact caseReplay11Part9Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay11 : CoreSearch.replay 7 searchRows11 = false := by
  apply CoreSearch.replay_split (m := 10) (by decide +kernel) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact caseReplay11Part0
  · exact caseReplay11Part1
  · exact caseReplay11Part2
  · exact caseReplay11Part3
  · exact caseReplay11Part4
  · exact caseReplay11Part5
  · exact caseReplay11Part6
  · exact caseReplay11Part7
  · exact caseReplay11Part8
  · exact caseReplay11Part9

def searchRows12 : List Nat := [0xfedae8f3fdbf25eb0c00000220a12000, 0xb93db76d6248ff9cb3b9106c4048d788, 0xf0093b2fb3b2b3953d0e2b0f7bb33395, 0xc77e740ba7764b2cd31e6d8584164b2c, 0x21bf9f3f97dcda550086d961835c8855]

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part0Op0 : CoreSearch.replaySliceChoice 7 searchRows12 0 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part0Op1 : CoreSearch.replaySliceChoice 7 searchRows12 0 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part0Op2 : CoreSearch.replaySliceChoice 7 searchRows12 0 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part0Op3 : CoreSearch.replaySliceChoice 7 searchRows12 0 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part0 : CoreSearch.replaySlice 7 searchRows12 0 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay12Part0Op0
  · exact caseReplay12Part0Op1
  · exact caseReplay12Part0Op2
  · exact caseReplay12Part0Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part1Op0 : CoreSearch.replaySliceChoice 7 searchRows12 1 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part1Op1 : CoreSearch.replaySliceChoice 7 searchRows12 1 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part1Op2 : CoreSearch.replaySliceChoice 7 searchRows12 1 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part1Op3 : CoreSearch.replaySliceChoice 7 searchRows12 1 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part1 : CoreSearch.replaySlice 7 searchRows12 1 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay12Part1Op0
  · exact caseReplay12Part1Op1
  · exact caseReplay12Part1Op2
  · exact caseReplay12Part1Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part2Op0 : CoreSearch.replaySliceChoice 7 searchRows12 2 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part2Op1 : CoreSearch.replaySliceChoice 7 searchRows12 2 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part2Op2 : CoreSearch.replaySliceChoice 7 searchRows12 2 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part2Op3 : CoreSearch.replaySliceChoice 7 searchRows12 2 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part2 : CoreSearch.replaySlice 7 searchRows12 2 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay12Part2Op0
  · exact caseReplay12Part2Op1
  · exact caseReplay12Part2Op2
  · exact caseReplay12Part2Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part3Op0 : CoreSearch.replaySliceChoice 7 searchRows12 3 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part3Op1 : CoreSearch.replaySliceChoice 7 searchRows12 3 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part3Op2 : CoreSearch.replaySliceChoice 7 searchRows12 3 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part3Op3 : CoreSearch.replaySliceChoice 7 searchRows12 3 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part3 : CoreSearch.replaySlice 7 searchRows12 3 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay12Part3Op0
  · exact caseReplay12Part3Op1
  · exact caseReplay12Part3Op2
  · exact caseReplay12Part3Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part4Op0 : CoreSearch.replaySliceChoice 7 searchRows12 4 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part4Op1 : CoreSearch.replaySliceChoice 7 searchRows12 4 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part4Op2 : CoreSearch.replaySliceChoice 7 searchRows12 4 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part4Op3 : CoreSearch.replaySliceChoice 7 searchRows12 4 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part4 : CoreSearch.replaySlice 7 searchRows12 4 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay12Part4Op0
  · exact caseReplay12Part4Op1
  · exact caseReplay12Part4Op2
  · exact caseReplay12Part4Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part5Op0 : CoreSearch.replaySliceChoice 7 searchRows12 5 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part5Op1 : CoreSearch.replaySliceChoice 7 searchRows12 5 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part5Op2 : CoreSearch.replaySliceChoice 7 searchRows12 5 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part5Op3 : CoreSearch.replaySliceChoice 7 searchRows12 5 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part5 : CoreSearch.replaySlice 7 searchRows12 5 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay12Part5Op0
  · exact caseReplay12Part5Op1
  · exact caseReplay12Part5Op2
  · exact caseReplay12Part5Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part6Op0 : CoreSearch.replaySliceChoice 7 searchRows12 6 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part6Op1 : CoreSearch.replaySliceChoice 7 searchRows12 6 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part6Op2 : CoreSearch.replaySliceChoice 7 searchRows12 6 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part6Op3 : CoreSearch.replaySliceChoice 7 searchRows12 6 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part6 : CoreSearch.replaySlice 7 searchRows12 6 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay12Part6Op0
  · exact caseReplay12Part6Op1
  · exact caseReplay12Part6Op2
  · exact caseReplay12Part6Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part7Op0 : CoreSearch.replaySliceChoice 7 searchRows12 7 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part7Op1 : CoreSearch.replaySliceChoice 7 searchRows12 7 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part7Op2 : CoreSearch.replaySliceChoice 7 searchRows12 7 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part7Op3 : CoreSearch.replaySliceChoice 7 searchRows12 7 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part7 : CoreSearch.replaySlice 7 searchRows12 7 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay12Part7Op0
  · exact caseReplay12Part7Op1
  · exact caseReplay12Part7Op2
  · exact caseReplay12Part7Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part8Op0 : CoreSearch.replaySliceChoice 7 searchRows12 8 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part8Op1 : CoreSearch.replaySliceChoice 7 searchRows12 8 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part8Op2 : CoreSearch.replaySliceChoice 7 searchRows12 8 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part8Op3 : CoreSearch.replaySliceChoice 7 searchRows12 8 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part8 : CoreSearch.replaySlice 7 searchRows12 8 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay12Part8Op0
  · exact caseReplay12Part8Op1
  · exact caseReplay12Part8Op2
  · exact caseReplay12Part8Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part9Op0 : CoreSearch.replaySliceChoice 7 searchRows12 9 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part9Op1 : CoreSearch.replaySliceChoice 7 searchRows12 9 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part9Op2 : CoreSearch.replaySliceChoice 7 searchRows12 9 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part9Op3 : CoreSearch.replaySliceChoice 7 searchRows12 9 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12Part9 : CoreSearch.replaySlice 7 searchRows12 9 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay12Part9Op0
  · exact caseReplay12Part9Op1
  · exact caseReplay12Part9Op2
  · exact caseReplay12Part9Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay12 : CoreSearch.replay 7 searchRows12 = false := by
  apply CoreSearch.replay_split (m := 10) (by decide +kernel) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact caseReplay12Part0
  · exact caseReplay12Part1
  · exact caseReplay12Part2
  · exact caseReplay12Part3
  · exact caseReplay12Part4
  · exact caseReplay12Part5
  · exact caseReplay12Part6
  · exact caseReplay12Part7
  · exact caseReplay12Part8
  · exact caseReplay12Part9

def searchRows13 : List Nat := [0xead00b79a7cbb7e6a000092086890046, 0xd5ba97f2693edd3e07bc00982936c928, 0x5c55e88f3e2b1e695134509f323b1668, 0x1d6f766d74d7e45d386513cd64d2041d, 0xf675ee86dae3fb8946c8a6025840c381]

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part0Op0 : CoreSearch.replaySliceChoice 7 searchRows13 0 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part0Op1 : CoreSearch.replaySliceChoice 7 searchRows13 0 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part0Op2 : CoreSearch.replaySliceChoice 7 searchRows13 0 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part0Op3 : CoreSearch.replaySliceChoice 7 searchRows13 0 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part0 : CoreSearch.replaySlice 7 searchRows13 0 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay13Part0Op0
  · exact caseReplay13Part0Op1
  · exact caseReplay13Part0Op2
  · exact caseReplay13Part0Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part1Op0 : CoreSearch.replaySliceChoice 7 searchRows13 1 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part1Op1 : CoreSearch.replaySliceChoice 7 searchRows13 1 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part1Op2 : CoreSearch.replaySliceChoice 7 searchRows13 1 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part1Op3 : CoreSearch.replaySliceChoice 7 searchRows13 1 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part1 : CoreSearch.replaySlice 7 searchRows13 1 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay13Part1Op0
  · exact caseReplay13Part1Op1
  · exact caseReplay13Part1Op2
  · exact caseReplay13Part1Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part2Op0 : CoreSearch.replaySliceChoice 7 searchRows13 2 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part2Op1 : CoreSearch.replaySliceChoice 7 searchRows13 2 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part2Op2 : CoreSearch.replaySliceChoice 7 searchRows13 2 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part2Op3 : CoreSearch.replaySliceChoice 7 searchRows13 2 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part2 : CoreSearch.replaySlice 7 searchRows13 2 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay13Part2Op0
  · exact caseReplay13Part2Op1
  · exact caseReplay13Part2Op2
  · exact caseReplay13Part2Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part3Op0 : CoreSearch.replaySliceChoice 7 searchRows13 3 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part3Op1 : CoreSearch.replaySliceChoice 7 searchRows13 3 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part3Op2 : CoreSearch.replaySliceChoice 7 searchRows13 3 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part3Op3 : CoreSearch.replaySliceChoice 7 searchRows13 3 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part3 : CoreSearch.replaySlice 7 searchRows13 3 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay13Part3Op0
  · exact caseReplay13Part3Op1
  · exact caseReplay13Part3Op2
  · exact caseReplay13Part3Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part4Op0 : CoreSearch.replaySliceChoice 7 searchRows13 4 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part4Op1 : CoreSearch.replaySliceChoice 7 searchRows13 4 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part4Op2 : CoreSearch.replaySliceChoice 7 searchRows13 4 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part4Op3 : CoreSearch.replaySliceChoice 7 searchRows13 4 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part4 : CoreSearch.replaySlice 7 searchRows13 4 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay13Part4Op0
  · exact caseReplay13Part4Op1
  · exact caseReplay13Part4Op2
  · exact caseReplay13Part4Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part5Op0 : CoreSearch.replaySliceChoice 7 searchRows13 5 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part5Op1 : CoreSearch.replaySliceChoice 7 searchRows13 5 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part5Op2 : CoreSearch.replaySliceChoice 7 searchRows13 5 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part5Op3 : CoreSearch.replaySliceChoice 7 searchRows13 5 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part5 : CoreSearch.replaySlice 7 searchRows13 5 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay13Part5Op0
  · exact caseReplay13Part5Op1
  · exact caseReplay13Part5Op2
  · exact caseReplay13Part5Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part6Op0 : CoreSearch.replaySliceChoice 7 searchRows13 6 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part6Op1 : CoreSearch.replaySliceChoice 7 searchRows13 6 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part6Op2 : CoreSearch.replaySliceChoice 7 searchRows13 6 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part6Op3 : CoreSearch.replaySliceChoice 7 searchRows13 6 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part6 : CoreSearch.replaySlice 7 searchRows13 6 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay13Part6Op0
  · exact caseReplay13Part6Op1
  · exact caseReplay13Part6Op2
  · exact caseReplay13Part6Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part7Op0 : CoreSearch.replaySliceChoice 7 searchRows13 7 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part7Op1 : CoreSearch.replaySliceChoice 7 searchRows13 7 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part7Op2 : CoreSearch.replaySliceChoice 7 searchRows13 7 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part7Op3 : CoreSearch.replaySliceChoice 7 searchRows13 7 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part7 : CoreSearch.replaySlice 7 searchRows13 7 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay13Part7Op0
  · exact caseReplay13Part7Op1
  · exact caseReplay13Part7Op2
  · exact caseReplay13Part7Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part8Op0 : CoreSearch.replaySliceChoice 7 searchRows13 8 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part8Op1 : CoreSearch.replaySliceChoice 7 searchRows13 8 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part8Op2 : CoreSearch.replaySliceChoice 7 searchRows13 8 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part8Op3 : CoreSearch.replaySliceChoice 7 searchRows13 8 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part8 : CoreSearch.replaySlice 7 searchRows13 8 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay13Part8Op0
  · exact caseReplay13Part8Op1
  · exact caseReplay13Part8Op2
  · exact caseReplay13Part8Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part9Op0 : CoreSearch.replaySliceChoice 7 searchRows13 9 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part9Op1 : CoreSearch.replaySliceChoice 7 searchRows13 9 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part9Op2 : CoreSearch.replaySliceChoice 7 searchRows13 9 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part9Op3 : CoreSearch.replaySliceChoice 7 searchRows13 9 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13Part9 : CoreSearch.replaySlice 7 searchRows13 9 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay13Part9Op0
  · exact caseReplay13Part9Op1
  · exact caseReplay13Part9Op2
  · exact caseReplay13Part9Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay13 : CoreSearch.replay 7 searchRows13 = false := by
  apply CoreSearch.replay_split (m := 10) (by decide +kernel) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact caseReplay13Part0
  · exact caseReplay13Part1
  · exact caseReplay13Part2
  · exact caseReplay13Part3
  · exact caseReplay13Part4
  · exact caseReplay13Part5
  · exact caseReplay13Part6
  · exact caseReplay13Part7
  · exact caseReplay13Part8
  · exact caseReplay13Part9

def searchRows14 : List Nat := [0xb6647ed4feaefc2108004a1034ac3c01, 0xca9b97f168c5a75f0a011b400880a51e, 0x973be63ff7de8b8670982507d34e8a86, 0x756f7a6b9b3857f2252e20600b104370, 0x5ddee5de155338fd54c2c498045310e1]

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part0Op0 : CoreSearch.replaySliceChoice 7 searchRows14 0 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part0Op1 : CoreSearch.replaySliceChoice 7 searchRows14 0 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part0Op2 : CoreSearch.replaySliceChoice 7 searchRows14 0 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part0Op3 : CoreSearch.replaySliceChoice 7 searchRows14 0 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part0 : CoreSearch.replaySlice 7 searchRows14 0 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay14Part0Op0
  · exact caseReplay14Part0Op1
  · exact caseReplay14Part0Op2
  · exact caseReplay14Part0Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part1Op0 : CoreSearch.replaySliceChoice 7 searchRows14 1 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part1Op1 : CoreSearch.replaySliceChoice 7 searchRows14 1 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part1Op2 : CoreSearch.replaySliceChoice 7 searchRows14 1 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part1Op3 : CoreSearch.replaySliceChoice 7 searchRows14 1 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part1 : CoreSearch.replaySlice 7 searchRows14 1 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay14Part1Op0
  · exact caseReplay14Part1Op1
  · exact caseReplay14Part1Op2
  · exact caseReplay14Part1Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part2Op0 : CoreSearch.replaySliceChoice 7 searchRows14 2 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part2Op1 : CoreSearch.replaySliceChoice 7 searchRows14 2 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part2Op2 : CoreSearch.replaySliceChoice 7 searchRows14 2 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part2Op3 : CoreSearch.replaySliceChoice 7 searchRows14 2 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part2 : CoreSearch.replaySlice 7 searchRows14 2 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay14Part2Op0
  · exact caseReplay14Part2Op1
  · exact caseReplay14Part2Op2
  · exact caseReplay14Part2Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part3Op0 : CoreSearch.replaySliceChoice 7 searchRows14 3 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part3Op1 : CoreSearch.replaySliceChoice 7 searchRows14 3 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part3Op2 : CoreSearch.replaySliceChoice 7 searchRows14 3 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part3Op3 : CoreSearch.replaySliceChoice 7 searchRows14 3 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part3 : CoreSearch.replaySlice 7 searchRows14 3 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay14Part3Op0
  · exact caseReplay14Part3Op1
  · exact caseReplay14Part3Op2
  · exact caseReplay14Part3Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part4Op0 : CoreSearch.replaySliceChoice 7 searchRows14 4 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part4Op1 : CoreSearch.replaySliceChoice 7 searchRows14 4 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part4Op2 : CoreSearch.replaySliceChoice 7 searchRows14 4 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part4Op3 : CoreSearch.replaySliceChoice 7 searchRows14 4 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part4 : CoreSearch.replaySlice 7 searchRows14 4 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay14Part4Op0
  · exact caseReplay14Part4Op1
  · exact caseReplay14Part4Op2
  · exact caseReplay14Part4Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part5Op0 : CoreSearch.replaySliceChoice 7 searchRows14 5 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part5Op1 : CoreSearch.replaySliceChoice 7 searchRows14 5 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part5Op2 : CoreSearch.replaySliceChoice 7 searchRows14 5 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part5Op3 : CoreSearch.replaySliceChoice 7 searchRows14 5 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part5 : CoreSearch.replaySlice 7 searchRows14 5 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay14Part5Op0
  · exact caseReplay14Part5Op1
  · exact caseReplay14Part5Op2
  · exact caseReplay14Part5Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part6Op0 : CoreSearch.replaySliceChoice 7 searchRows14 6 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part6Op1 : CoreSearch.replaySliceChoice 7 searchRows14 6 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part6Op2 : CoreSearch.replaySliceChoice 7 searchRows14 6 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part6Op3 : CoreSearch.replaySliceChoice 7 searchRows14 6 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part6 : CoreSearch.replaySlice 7 searchRows14 6 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay14Part6Op0
  · exact caseReplay14Part6Op1
  · exact caseReplay14Part6Op2
  · exact caseReplay14Part6Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part7Op0 : CoreSearch.replaySliceChoice 7 searchRows14 7 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part7Op1 : CoreSearch.replaySliceChoice 7 searchRows14 7 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part7Op2 : CoreSearch.replaySliceChoice 7 searchRows14 7 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part7Op3 : CoreSearch.replaySliceChoice 7 searchRows14 7 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part7 : CoreSearch.replaySlice 7 searchRows14 7 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay14Part7Op0
  · exact caseReplay14Part7Op1
  · exact caseReplay14Part7Op2
  · exact caseReplay14Part7Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part8Op0 : CoreSearch.replaySliceChoice 7 searchRows14 8 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part8Op1 : CoreSearch.replaySliceChoice 7 searchRows14 8 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part8Op2 : CoreSearch.replaySliceChoice 7 searchRows14 8 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part8Op3 : CoreSearch.replaySliceChoice 7 searchRows14 8 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part8 : CoreSearch.replaySlice 7 searchRows14 8 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay14Part8Op0
  · exact caseReplay14Part8Op1
  · exact caseReplay14Part8Op2
  · exact caseReplay14Part8Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part9Op0 : CoreSearch.replaySliceChoice 7 searchRows14 9 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part9Op1 : CoreSearch.replaySliceChoice 7 searchRows14 9 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part9Op2 : CoreSearch.replaySliceChoice 7 searchRows14 9 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part9Op3 : CoreSearch.replaySliceChoice 7 searchRows14 9 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14Part9 : CoreSearch.replaySlice 7 searchRows14 9 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay14Part9Op0
  · exact caseReplay14Part9Op1
  · exact caseReplay14Part9Op2
  · exact caseReplay14Part9Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay14 : CoreSearch.replay 7 searchRows14 = false := by
  apply CoreSearch.replay_split (m := 10) (by decide +kernel) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact caseReplay14Part0
  · exact caseReplay14Part1
  · exact caseReplay14Part2
  · exact caseReplay14Part3
  · exact caseReplay14Part4
  · exact caseReplay14Part5
  · exact caseReplay14Part6
  · exact caseReplay14Part7
  · exact caseReplay14Part8
  · exact caseReplay14Part9

def searchRows15 : List Nat := [0x7377ffd2c7e7fc7b2a4142d202e61429, 0x4cfbe9ed915e6b999c72a274915c4b19, 0x85be7dffe9f27f0780aa7da1c9822706, 0xa9c3d67efc68deac8b81325af4608aac, 0xfffd9eef3e9df3fe51148c0d2c1800d2]

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part0Op0 : CoreSearch.replaySliceChoice 7 searchRows15 0 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part0Op1 : CoreSearch.replaySliceChoice 7 searchRows15 0 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part0Op2 : CoreSearch.replaySliceChoice 7 searchRows15 0 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part0Op3 : CoreSearch.replaySliceChoice 7 searchRows15 0 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part0 : CoreSearch.replaySlice 7 searchRows15 0 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay15Part0Op0
  · exact caseReplay15Part0Op1
  · exact caseReplay15Part0Op2
  · exact caseReplay15Part0Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part1Op0 : CoreSearch.replaySliceChoice 7 searchRows15 1 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part1Op1 : CoreSearch.replaySliceChoice 7 searchRows15 1 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part1Op2 : CoreSearch.replaySliceChoice 7 searchRows15 1 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part1Op3 : CoreSearch.replaySliceChoice 7 searchRows15 1 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part1 : CoreSearch.replaySlice 7 searchRows15 1 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay15Part1Op0
  · exact caseReplay15Part1Op1
  · exact caseReplay15Part1Op2
  · exact caseReplay15Part1Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part2Op0 : CoreSearch.replaySliceChoice 7 searchRows15 2 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part2Op1 : CoreSearch.replaySliceChoice 7 searchRows15 2 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part2Op2 : CoreSearch.replaySliceChoice 7 searchRows15 2 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part2Op3 : CoreSearch.replaySliceChoice 7 searchRows15 2 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part2 : CoreSearch.replaySlice 7 searchRows15 2 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay15Part2Op0
  · exact caseReplay15Part2Op1
  · exact caseReplay15Part2Op2
  · exact caseReplay15Part2Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part3Op0 : CoreSearch.replaySliceChoice 7 searchRows15 3 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part3Op1 : CoreSearch.replaySliceChoice 7 searchRows15 3 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part3Op2 : CoreSearch.replaySliceChoice 7 searchRows15 3 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part3Op3 : CoreSearch.replaySliceChoice 7 searchRows15 3 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part3 : CoreSearch.replaySlice 7 searchRows15 3 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay15Part3Op0
  · exact caseReplay15Part3Op1
  · exact caseReplay15Part3Op2
  · exact caseReplay15Part3Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part4Op0 : CoreSearch.replaySliceChoice 7 searchRows15 4 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part4Op1 : CoreSearch.replaySliceChoice 7 searchRows15 4 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part4Op2 : CoreSearch.replaySliceChoice 7 searchRows15 4 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part4Op3 : CoreSearch.replaySliceChoice 7 searchRows15 4 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part4 : CoreSearch.replaySlice 7 searchRows15 4 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay15Part4Op0
  · exact caseReplay15Part4Op1
  · exact caseReplay15Part4Op2
  · exact caseReplay15Part4Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part5Op0 : CoreSearch.replaySliceChoice 7 searchRows15 5 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part5Op1 : CoreSearch.replaySliceChoice 7 searchRows15 5 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part5Op2 : CoreSearch.replaySliceChoice 7 searchRows15 5 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part5Op3 : CoreSearch.replaySliceChoice 7 searchRows15 5 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part5 : CoreSearch.replaySlice 7 searchRows15 5 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay15Part5Op0
  · exact caseReplay15Part5Op1
  · exact caseReplay15Part5Op2
  · exact caseReplay15Part5Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part6Op0 : CoreSearch.replaySliceChoice 7 searchRows15 6 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part6Op1 : CoreSearch.replaySliceChoice 7 searchRows15 6 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part6Op2 : CoreSearch.replaySliceChoice 7 searchRows15 6 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part6Op3 : CoreSearch.replaySliceChoice 7 searchRows15 6 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part6 : CoreSearch.replaySlice 7 searchRows15 6 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay15Part6Op0
  · exact caseReplay15Part6Op1
  · exact caseReplay15Part6Op2
  · exact caseReplay15Part6Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part7Op0 : CoreSearch.replaySliceChoice 7 searchRows15 7 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part7Op1 : CoreSearch.replaySliceChoice 7 searchRows15 7 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part7Op2 : CoreSearch.replaySliceChoice 7 searchRows15 7 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part7Op3 : CoreSearch.replaySliceChoice 7 searchRows15 7 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part7 : CoreSearch.replaySlice 7 searchRows15 7 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay15Part7Op0
  · exact caseReplay15Part7Op1
  · exact caseReplay15Part7Op2
  · exact caseReplay15Part7Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part8Op0 : CoreSearch.replaySliceChoice 7 searchRows15 8 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part8Op1 : CoreSearch.replaySliceChoice 7 searchRows15 8 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part8Op2 : CoreSearch.replaySliceChoice 7 searchRows15 8 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part8Op3 : CoreSearch.replaySliceChoice 7 searchRows15 8 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part8 : CoreSearch.replaySlice 7 searchRows15 8 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay15Part8Op0
  · exact caseReplay15Part8Op1
  · exact caseReplay15Part8Op2
  · exact caseReplay15Part8Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part9Op0 : CoreSearch.replaySliceChoice 7 searchRows15 9 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part9Op1 : CoreSearch.replaySliceChoice 7 searchRows15 9 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part9Op2 : CoreSearch.replaySliceChoice 7 searchRows15 9 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part9Op3 : CoreSearch.replaySliceChoice 7 searchRows15 9 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15Part9 : CoreSearch.replaySlice 7 searchRows15 9 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay15Part9Op0
  · exact caseReplay15Part9Op1
  · exact caseReplay15Part9Op2
  · exact caseReplay15Part9Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay15 : CoreSearch.replay 7 searchRows15 = false := by
  apply CoreSearch.replay_split (m := 10) (by decide +kernel) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact caseReplay15Part0
  · exact caseReplay15Part1
  · exact caseReplay15Part2
  · exact caseReplay15Part3
  · exact caseReplay15Part4
  · exact caseReplay15Part5
  · exact caseReplay15Part6
  · exact caseReplay15Part7
  · exact caseReplay15Part8
  · exact caseReplay15Part9

def searchRows16 : List Nat := [0x89c83224bbbc9850884012240000084, 0xfcdfdb7fefffddffd8fc9b7eeb0119bd, 0x7fb3acfdd5eeb70b1622a8d50402a703, 0x9bf874f23ddc727506b4c4723d0c7255, 0x63733ec1b978bace21133681b938984a, 0xd7cd519eb7f74e72454b508896504e62]

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay16Part0 : CoreSearch.replaySlice 7 searchRows16 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay16Part1 : CoreSearch.replaySlice 7 searchRows16 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay16Part2 : CoreSearch.replaySlice 7 searchRows16 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay16Part3 : CoreSearch.replaySlice 7 searchRows16 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay16Part4 : CoreSearch.replaySlice 7 searchRows16 4 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay16Part5 : CoreSearch.replaySlice 7 searchRows16 5 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay16Part6 : CoreSearch.replaySlice 7 searchRows16 6 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay16Part7 : CoreSearch.replaySlice 7 searchRows16 7 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay16Part8 : CoreSearch.replaySlice 7 searchRows16 8 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay16Part9 : CoreSearch.replaySlice 7 searchRows16 9 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay16Part10 : CoreSearch.replaySlice 7 searchRows16 10 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay16Part11 : CoreSearch.replaySlice 7 searchRows16 11 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay16Part12 : CoreSearch.replaySlice 7 searchRows16 12 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay16Part13 : CoreSearch.replaySlice 7 searchRows16 13 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay16Part14 : CoreSearch.replaySlice 7 searchRows16 14 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay16 : CoreSearch.replay 7 searchRows16 = false := by
  apply CoreSearch.replay_split (m := 15) (by decide +kernel) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact caseReplay16Part0
  · exact caseReplay16Part1
  · exact caseReplay16Part2
  · exact caseReplay16Part3
  · exact caseReplay16Part4
  · exact caseReplay16Part5
  · exact caseReplay16Part6
  · exact caseReplay16Part7
  · exact caseReplay16Part8
  · exact caseReplay16Part9
  · exact caseReplay16Part10
  · exact caseReplay16Part11
  · exact caseReplay16Part12
  · exact caseReplay16Part13
  · exact caseReplay16Part14

def searchRows17 : List Nat := [0xffdffb97fffffb7fc58df295f142093e, 0x5901421447fd002e840140044040000e, 0xab3fafe8de7ee7920a220fa88e04e610, 0xf7ee6c7a6ccdcd95f5666c7268c9c985, 0x26e1d56ba7e3fcc92240014a068034c1, 0x531489f5379a47651372897137984761]

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay17Part0 : CoreSearch.replaySlice 7 searchRows17 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay17Part1 : CoreSearch.replaySlice 7 searchRows17 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay17Part2 : CoreSearch.replaySlice 7 searchRows17 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay17Part3 : CoreSearch.replaySlice 7 searchRows17 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay17Part4 : CoreSearch.replaySlice 7 searchRows17 4 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay17Part5 : CoreSearch.replaySlice 7 searchRows17 5 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay17Part6 : CoreSearch.replaySlice 7 searchRows17 6 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay17Part7 : CoreSearch.replaySlice 7 searchRows17 7 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay17Part8 : CoreSearch.replaySlice 7 searchRows17 8 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay17Part9 : CoreSearch.replaySlice 7 searchRows17 9 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay17Part10 : CoreSearch.replaySlice 7 searchRows17 10 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay17Part11 : CoreSearch.replaySlice 7 searchRows17 11 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay17Part12 : CoreSearch.replaySlice 7 searchRows17 12 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay17Part13 : CoreSearch.replaySlice 7 searchRows17 13 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay17Part14 : CoreSearch.replaySlice 7 searchRows17 14 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay17 : CoreSearch.replay 7 searchRows17 = false := by
  apply CoreSearch.replay_split (m := 15) (by decide +kernel) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact caseReplay17Part0
  · exact caseReplay17Part1
  · exact caseReplay17Part2
  · exact caseReplay17Part3
  · exact caseReplay17Part4
  · exact caseReplay17Part5
  · exact caseReplay17Part6
  · exact caseReplay17Part7
  · exact caseReplay17Part8
  · exact caseReplay17Part9
  · exact caseReplay17Part10
  · exact caseReplay17Part11
  · exact caseReplay17Part12
  · exact caseReplay17Part13
  · exact caseReplay17Part14

def searchRows18 : List Nat := [0xf134a0cd296c2bca810420c120442a08, 0x49e86fdee59f353f40ac6e9ca185113e, 0xe4b5f301292d42124c851301082d401, 0xce8b3837d65bf0dc1ba33817424b70cc, 0xbe7fdb2dfa7ddfe838738b2cc03185e0, 0xd7c2b5dbc59fa2b7d712954bc41aa2b3]

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay18Part0 : CoreSearch.replaySlice 7 searchRows18 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay18Part1 : CoreSearch.replaySlice 7 searchRows18 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay18Part2 : CoreSearch.replaySlice 7 searchRows18 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay18Part3 : CoreSearch.replaySlice 7 searchRows18 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay18Part4 : CoreSearch.replaySlice 7 searchRows18 4 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay18Part5 : CoreSearch.replaySlice 7 searchRows18 5 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay18Part6 : CoreSearch.replaySlice 7 searchRows18 6 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay18Part7 : CoreSearch.replaySlice 7 searchRows18 7 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay18Part8 : CoreSearch.replaySlice 7 searchRows18 8 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay18Part9 : CoreSearch.replaySlice 7 searchRows18 9 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay18Part10 : CoreSearch.replaySlice 7 searchRows18 10 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay18Part11 : CoreSearch.replaySlice 7 searchRows18 11 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay18Part12 : CoreSearch.replaySlice 7 searchRows18 12 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay18Part13 : CoreSearch.replaySlice 7 searchRows18 13 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay18Part14 : CoreSearch.replaySlice 7 searchRows18 14 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay18 : CoreSearch.replay 7 searchRows18 = false := by
  apply CoreSearch.replay_split (m := 15) (by decide +kernel) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact caseReplay18Part0
  · exact caseReplay18Part1
  · exact caseReplay18Part2
  · exact caseReplay18Part3
  · exact caseReplay18Part4
  · exact caseReplay18Part5
  · exact caseReplay18Part6
  · exact caseReplay18Part7
  · exact caseReplay18Part8
  · exact caseReplay18Part9
  · exact caseReplay18Part10
  · exact caseReplay18Part11
  · exact caseReplay18Part12
  · exact caseReplay18Part13
  · exact caseReplay18Part14

def searchRows19 : List Nat := [0x980a08911dbce640000000910000020, 0x377a1d67677d9b99113e952262218b89, 0xffeff7fddbffff7785f5f1fdd8081e76, 0xe9ddcb1eedf46ccb68b68b04cc446cc9, 0xf6af66f2cdeb712bb20a26d20483710b, 0x7cd11d96b7b7b0dcecc10c96a617b054]

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay19Part0 : CoreSearch.replaySlice 7 searchRows19 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay19Part1 : CoreSearch.replaySlice 7 searchRows19 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay19Part2 : CoreSearch.replaySlice 7 searchRows19 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay19Part3 : CoreSearch.replaySlice 7 searchRows19 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay19Part4 : CoreSearch.replaySlice 7 searchRows19 4 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay19Part5 : CoreSearch.replaySlice 7 searchRows19 5 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay19Part6 : CoreSearch.replaySlice 7 searchRows19 6 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay19Part7 : CoreSearch.replaySlice 7 searchRows19 7 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay19Part8 : CoreSearch.replaySlice 7 searchRows19 8 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay19Part9 : CoreSearch.replaySlice 7 searchRows19 9 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay19Part10 : CoreSearch.replaySlice 7 searchRows19 10 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay19Part11 : CoreSearch.replaySlice 7 searchRows19 11 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay19Part12 : CoreSearch.replaySlice 7 searchRows19 12 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay19Part13 : CoreSearch.replaySlice 7 searchRows19 13 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay19Part14 : CoreSearch.replaySlice 7 searchRows19 14 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay19 : CoreSearch.replay 7 searchRows19 = false := by
  apply CoreSearch.replay_split (m := 15) (by decide +kernel) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact caseReplay19Part0
  · exact caseReplay19Part1
  · exact caseReplay19Part2
  · exact caseReplay19Part3
  · exact caseReplay19Part4
  · exact caseReplay19Part5
  · exact caseReplay19Part6
  · exact caseReplay19Part7
  · exact caseReplay19Part8
  · exact caseReplay19Part9
  · exact caseReplay19Part10
  · exact caseReplay19Part11
  · exact caseReplay19Part12
  · exact caseReplay19Part13
  · exact caseReplay19Part14

def searchRows20 : List Nat := [0xdfff7affffffffd59bef3a5dd0a00ed1, 0x6ef9ed1bafcc662f0cd0ec0aafc46427, 0x908e1045cdf7c4908000004500000080, 0xbc34957a9ba7293b34e1913a91a3291b, 0xc75223a63f7a9967601001a22f429126, 0x392bcf187af873ba200b47107a685338]

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay20Part0 : CoreSearch.replaySlice 7 searchRows20 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay20Part1 : CoreSearch.replaySlice 7 searchRows20 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay20Part2 : CoreSearch.replaySlice 7 searchRows20 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay20Part3 : CoreSearch.replaySlice 7 searchRows20 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay20Part4 : CoreSearch.replaySlice 7 searchRows20 4 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay20Part5 : CoreSearch.replaySlice 7 searchRows20 5 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay20Part6 : CoreSearch.replaySlice 7 searchRows20 6 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay20Part7 : CoreSearch.replaySlice 7 searchRows20 7 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay20Part8 : CoreSearch.replaySlice 7 searchRows20 8 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay20Part9 : CoreSearch.replaySlice 7 searchRows20 9 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay20Part10 : CoreSearch.replaySlice 7 searchRows20 10 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay20Part11 : CoreSearch.replaySlice 7 searchRows20 11 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay20Part12 : CoreSearch.replaySlice 7 searchRows20 12 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay20Part13 : CoreSearch.replaySlice 7 searchRows20 13 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay20Part14 : CoreSearch.replaySlice 7 searchRows20 14 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay20 : CoreSearch.replay 7 searchRows20 = false := by
  apply CoreSearch.replay_split (m := 15) (by decide +kernel) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact caseReplay20Part0
  · exact caseReplay20Part1
  · exact caseReplay20Part2
  · exact caseReplay20Part3
  · exact caseReplay20Part4
  · exact caseReplay20Part5
  · exact caseReplay20Part6
  · exact caseReplay20Part7
  · exact caseReplay20Part8
  · exact caseReplay20Part9
  · exact caseReplay20Part10
  · exact caseReplay20Part11
  · exact caseReplay20Part12
  · exact caseReplay20Part13
  · exact caseReplay20Part14

def searchRows21 : List Nat := [0xbd4fbfaff7eb7f0cb804bda3b1a23f08, 0x72208e5fdaa6a2ee700086539226202c, 0x5ff377fe7e5dcaff47fb537c6e5dc2f7, 0xad96694b3d3e185d1c0668431d2e185c, 0xc3fd403fed17f59101e9000c40118081, 0xe3a8f8cd9ef911e28f4c688c0cd911c2]

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay21Part0 : CoreSearch.replaySlice 7 searchRows21 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay21Part1 : CoreSearch.replaySlice 7 searchRows21 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay21Part2 : CoreSearch.replaySlice 7 searchRows21 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay21Part3 : CoreSearch.replaySlice 7 searchRows21 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay21Part4 : CoreSearch.replaySlice 7 searchRows21 4 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay21Part5 : CoreSearch.replaySlice 7 searchRows21 5 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay21Part6 : CoreSearch.replaySlice 7 searchRows21 6 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay21Part7 : CoreSearch.replaySlice 7 searchRows21 7 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay21Part8 : CoreSearch.replaySlice 7 searchRows21 8 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay21Part9 : CoreSearch.replaySlice 7 searchRows21 9 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay21Part10 : CoreSearch.replaySlice 7 searchRows21 10 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay21Part11 : CoreSearch.replaySlice 7 searchRows21 11 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay21Part12 : CoreSearch.replaySlice 7 searchRows21 12 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay21Part13 : CoreSearch.replaySlice 7 searchRows21 13 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay21Part14 : CoreSearch.replaySlice 7 searchRows21 14 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay21 : CoreSearch.replay 7 searchRows21 = false := by
  apply CoreSearch.replay_split (m := 15) (by decide +kernel) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact caseReplay21Part0
  · exact caseReplay21Part1
  · exact caseReplay21Part2
  · exact caseReplay21Part3
  · exact caseReplay21Part4
  · exact caseReplay21Part5
  · exact caseReplay21Part6
  · exact caseReplay21Part7
  · exact caseReplay21Part8
  · exact caseReplay21Part9
  · exact caseReplay21Part10
  · exact caseReplay21Part11
  · exact caseReplay21Part12
  · exact caseReplay21Part13
  · exact caseReplay21Part14

def searchRows22 : List Nat := [0xf02b8638076fec22a008802806000c02, 0x6fd5f9bea8f3a7dca651b9b22841a4cc, 0x5eff21c5fafe16fb54e72005f02202b9, 0xf36ffe7f577ffd6fe42ffe7c46095d6b, 0xb2fc2ef37dfcfb5112900ed31884b350, 0x6d86dbce9457c38f491643ce9416c307]

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay22Part0 : CoreSearch.replaySlice 7 searchRows22 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay22Part1 : CoreSearch.replaySlice 7 searchRows22 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay22Part2 : CoreSearch.replaySlice 7 searchRows22 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay22Part3 : CoreSearch.replaySlice 7 searchRows22 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay22Part4 : CoreSearch.replaySlice 7 searchRows22 4 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay22Part5 : CoreSearch.replaySlice 7 searchRows22 5 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay22Part6 : CoreSearch.replaySlice 7 searchRows22 6 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay22Part7 : CoreSearch.replaySlice 7 searchRows22 7 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay22Part8 : CoreSearch.replaySlice 7 searchRows22 8 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay22Part9 : CoreSearch.replaySlice 7 searchRows22 9 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay22Part10 : CoreSearch.replaySlice 7 searchRows22 10 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay22Part11 : CoreSearch.replaySlice 7 searchRows22 11 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay22Part12 : CoreSearch.replaySlice 7 searchRows22 12 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay22Part13 : CoreSearch.replaySlice 7 searchRows22 13 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay22Part14 : CoreSearch.replaySlice 7 searchRows22 14 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay22 : CoreSearch.replay 7 searchRows22 = false := by
  apply CoreSearch.replay_split (m := 15) (by decide +kernel) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact caseReplay22Part0
  · exact caseReplay22Part1
  · exact caseReplay22Part2
  · exact caseReplay22Part3
  · exact caseReplay22Part4
  · exact caseReplay22Part5
  · exact caseReplay22Part6
  · exact caseReplay22Part7
  · exact caseReplay22Part8
  · exact caseReplay22Part9
  · exact caseReplay22Part10
  · exact caseReplay22Part11
  · exact caseReplay22Part12
  · exact caseReplay22Part13
  · exact caseReplay22Part14

def searchRows23 : List Nat := [0xdff6d1ffdf9ddfcec0e211fccb1ccb06, 0x6c08bb71eefb13b02c10bb01e4d81390, 0x236b2c2dff7e6443824904241a240442, 0x106707c1f1d4f139000603c0e1d0f129, 0xf9ddff87b7e3bcfd3f1dee0334e334f9, 0x77208edb7ca1473f5fa08cdb1421443d]

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay23Part0 : CoreSearch.replaySlice 7 searchRows23 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay23Part1 : CoreSearch.replaySlice 7 searchRows23 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay23Part2 : CoreSearch.replaySlice 7 searchRows23 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay23Part3 : CoreSearch.replaySlice 7 searchRows23 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay23Part4 : CoreSearch.replaySlice 7 searchRows23 4 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay23Part5 : CoreSearch.replaySlice 7 searchRows23 5 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay23Part6 : CoreSearch.replaySlice 7 searchRows23 6 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay23Part7 : CoreSearch.replaySlice 7 searchRows23 7 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay23Part8 : CoreSearch.replaySlice 7 searchRows23 8 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay23Part9 : CoreSearch.replaySlice 7 searchRows23 9 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay23Part10 : CoreSearch.replaySlice 7 searchRows23 10 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay23Part11 : CoreSearch.replaySlice 7 searchRows23 11 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay23Part12 : CoreSearch.replaySlice 7 searchRows23 12 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay23Part13 : CoreSearch.replaySlice 7 searchRows23 13 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay23Part14 : CoreSearch.replaySlice 7 searchRows23 14 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay23 : CoreSearch.replay 7 searchRows23 = false := by
  apply CoreSearch.replay_split (m := 15) (by decide +kernel) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact caseReplay23Part0
  · exact caseReplay23Part1
  · exact caseReplay23Part2
  · exact caseReplay23Part3
  · exact caseReplay23Part4
  · exact caseReplay23Part5
  · exact caseReplay23Part6
  · exact caseReplay23Part7
  · exact caseReplay23Part8
  · exact caseReplay23Part9
  · exact caseReplay23Part10
  · exact caseReplay23Part11
  · exact caseReplay23Part12
  · exact caseReplay23Part13
  · exact caseReplay23Part14

def searchRows24 : List Nat := [0xbdfffceeeffffd3f3dbfdc4a21003937, 0xd39d1f269ece839ed49919249aca839a, 0x47b1c3db9ff506f903204293968504a9, 0x9ce78c9d5b599b49840d8c9c5b591b48, 0x6a4a6b357dfafec2004023254c40c640, 0x913694402f2f51242002844021001004]

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay24Part0 : CoreSearch.replaySlice 7 searchRows24 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay24Part1 : CoreSearch.replaySlice 7 searchRows24 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay24Part2 : CoreSearch.replaySlice 7 searchRows24 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay24Part3 : CoreSearch.replaySlice 7 searchRows24 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay24Part4 : CoreSearch.replaySlice 7 searchRows24 4 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay24Part5 : CoreSearch.replaySlice 7 searchRows24 5 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay24Part6 : CoreSearch.replaySlice 7 searchRows24 6 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay24Part7 : CoreSearch.replaySlice 7 searchRows24 7 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay24Part8 : CoreSearch.replaySlice 7 searchRows24 8 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay24Part9 : CoreSearch.replaySlice 7 searchRows24 9 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay24Part10 : CoreSearch.replaySlice 7 searchRows24 10 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay24Part11 : CoreSearch.replaySlice 7 searchRows24 11 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay24Part12 : CoreSearch.replaySlice 7 searchRows24 12 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay24Part13 : CoreSearch.replaySlice 7 searchRows24 13 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay24Part14 : CoreSearch.replaySlice 7 searchRows24 14 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay24 : CoreSearch.replay 7 searchRows24 = false := by
  apply CoreSearch.replay_split (m := 15) (by decide +kernel) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact caseReplay24Part0
  · exact caseReplay24Part1
  · exact caseReplay24Part2
  · exact caseReplay24Part3
  · exact caseReplay24Part4
  · exact caseReplay24Part5
  · exact caseReplay24Part6
  · exact caseReplay24Part7
  · exact caseReplay24Part8
  · exact caseReplay24Part9
  · exact caseReplay24Part10
  · exact caseReplay24Part11
  · exact caseReplay24Part12
  · exact caseReplay24Part13
  · exact caseReplay24Part14

def searchRows25 : List Nat := [0x3dd5a897bfe67b6725c420132c441826, 0xb6285541c7df81181800504082800110, 0xfeefd77fdfffedfc9a1bd75ddbc16578, 0x4fc31aaec496f4b6dec31aa6c492f096, 0x41f6ffa82fb9f6c300308da8010086c1, 0xc66b8970756aae1ec4638920750aae0e]

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay25Part0 : CoreSearch.replaySlice 7 searchRows25 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay25Part1 : CoreSearch.replaySlice 7 searchRows25 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay25Part2 : CoreSearch.replaySlice 7 searchRows25 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay25Part3 : CoreSearch.replaySlice 7 searchRows25 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay25Part4 : CoreSearch.replaySlice 7 searchRows25 4 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay25Part5 : CoreSearch.replaySlice 7 searchRows25 5 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay25Part6 : CoreSearch.replaySlice 7 searchRows25 6 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay25Part7 : CoreSearch.replaySlice 7 searchRows25 7 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay25Part8 : CoreSearch.replaySlice 7 searchRows25 8 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay25Part9 : CoreSearch.replaySlice 7 searchRows25 9 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay25Part10 : CoreSearch.replaySlice 7 searchRows25 10 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay25Part11 : CoreSearch.replaySlice 7 searchRows25 11 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay25Part12 : CoreSearch.replaySlice 7 searchRows25 12 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay25Part13 : CoreSearch.replaySlice 7 searchRows25 13 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay25Part14 : CoreSearch.replaySlice 7 searchRows25 14 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay25 : CoreSearch.replay 7 searchRows25 = false := by
  apply CoreSearch.replay_split (m := 15) (by decide +kernel) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact caseReplay25Part0
  · exact caseReplay25Part1
  · exact caseReplay25Part2
  · exact caseReplay25Part3
  · exact caseReplay25Part4
  · exact caseReplay25Part5
  · exact caseReplay25Part6
  · exact caseReplay25Part7
  · exact caseReplay25Part8
  · exact caseReplay25Part9
  · exact caseReplay25Part10
  · exact caseReplay25Part11
  · exact caseReplay25Part12
  · exact caseReplay25Part13
  · exact caseReplay25Part14

def searchRows26 : List Nat := [0x2f29cbb65ffecd5a0829018245000d52, 0xffff75efbfffb6bfdfd975ef3a8334af, 0xd8de114b1bbf30a110900048180000a0, 0x732ae599eb696794a38ac599eb296790, 0xf7deee7542d8ffc3e546ee350298b201, 0x493136b8e7c5ea3d44603230c584ca1d]

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part0Op0 : CoreSearch.replaySliceChoice 7 searchRows26 0 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part0Op1 : CoreSearch.replaySliceChoice 7 searchRows26 0 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part0Op2 : CoreSearch.replaySliceChoice 7 searchRows26 0 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part0Op3 : CoreSearch.replaySliceChoice 7 searchRows26 0 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part0 : CoreSearch.replaySlice 7 searchRows26 0 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay26Part0Op0
  · exact caseReplay26Part0Op1
  · exact caseReplay26Part0Op2
  · exact caseReplay26Part0Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part1Op0 : CoreSearch.replaySliceChoice 7 searchRows26 1 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part1Op1 : CoreSearch.replaySliceChoice 7 searchRows26 1 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part1Op2 : CoreSearch.replaySliceChoice 7 searchRows26 1 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part1Op3 : CoreSearch.replaySliceChoice 7 searchRows26 1 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part1 : CoreSearch.replaySlice 7 searchRows26 1 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay26Part1Op0
  · exact caseReplay26Part1Op1
  · exact caseReplay26Part1Op2
  · exact caseReplay26Part1Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part2Op0 : CoreSearch.replaySliceChoice 7 searchRows26 2 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part2Op1 : CoreSearch.replaySliceChoice 7 searchRows26 2 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part2Op2 : CoreSearch.replaySliceChoice 7 searchRows26 2 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part2Op3 : CoreSearch.replaySliceChoice 7 searchRows26 2 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part2 : CoreSearch.replaySlice 7 searchRows26 2 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay26Part2Op0
  · exact caseReplay26Part2Op1
  · exact caseReplay26Part2Op2
  · exact caseReplay26Part2Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part3Op0 : CoreSearch.replaySliceChoice 7 searchRows26 3 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part3Op1 : CoreSearch.replaySliceChoice 7 searchRows26 3 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part3Op2 : CoreSearch.replaySliceChoice 7 searchRows26 3 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part3Op3 : CoreSearch.replaySliceChoice 7 searchRows26 3 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part3 : CoreSearch.replaySlice 7 searchRows26 3 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay26Part3Op0
  · exact caseReplay26Part3Op1
  · exact caseReplay26Part3Op2
  · exact caseReplay26Part3Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part4Op0 : CoreSearch.replaySliceChoice 7 searchRows26 4 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part4Op1 : CoreSearch.replaySliceChoice 7 searchRows26 4 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part4Op2 : CoreSearch.replaySliceChoice 7 searchRows26 4 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part4Op3 : CoreSearch.replaySliceChoice 7 searchRows26 4 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part4 : CoreSearch.replaySlice 7 searchRows26 4 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay26Part4Op0
  · exact caseReplay26Part4Op1
  · exact caseReplay26Part4Op2
  · exact caseReplay26Part4Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part5Op0 : CoreSearch.replaySliceChoice 7 searchRows26 5 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part5Op1 : CoreSearch.replaySliceChoice 7 searchRows26 5 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part5Op2 : CoreSearch.replaySliceChoice 7 searchRows26 5 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part5Op3 : CoreSearch.replaySliceChoice 7 searchRows26 5 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part5 : CoreSearch.replaySlice 7 searchRows26 5 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay26Part5Op0
  · exact caseReplay26Part5Op1
  · exact caseReplay26Part5Op2
  · exact caseReplay26Part5Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part6Op0 : CoreSearch.replaySliceChoice 7 searchRows26 6 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part6Op1 : CoreSearch.replaySliceChoice 7 searchRows26 6 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part6Op2 : CoreSearch.replaySliceChoice 7 searchRows26 6 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part6Op3 : CoreSearch.replaySliceChoice 7 searchRows26 6 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part6 : CoreSearch.replaySlice 7 searchRows26 6 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay26Part6Op0
  · exact caseReplay26Part6Op1
  · exact caseReplay26Part6Op2
  · exact caseReplay26Part6Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part7Op0 : CoreSearch.replaySliceChoice 7 searchRows26 7 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part7Op1 : CoreSearch.replaySliceChoice 7 searchRows26 7 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part7Op2 : CoreSearch.replaySliceChoice 7 searchRows26 7 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part7Op3 : CoreSearch.replaySliceChoice 7 searchRows26 7 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part7 : CoreSearch.replaySlice 7 searchRows26 7 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay26Part7Op0
  · exact caseReplay26Part7Op1
  · exact caseReplay26Part7Op2
  · exact caseReplay26Part7Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part8Op0 : CoreSearch.replaySliceChoice 7 searchRows26 8 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part8Op1 : CoreSearch.replaySliceChoice 7 searchRows26 8 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part8Op2 : CoreSearch.replaySliceChoice 7 searchRows26 8 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part8Op3 : CoreSearch.replaySliceChoice 7 searchRows26 8 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part8 : CoreSearch.replaySlice 7 searchRows26 8 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay26Part8Op0
  · exact caseReplay26Part8Op1
  · exact caseReplay26Part8Op2
  · exact caseReplay26Part8Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part9Op0 : CoreSearch.replaySliceChoice 7 searchRows26 9 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part9Op1 : CoreSearch.replaySliceChoice 7 searchRows26 9 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part9Op2 : CoreSearch.replaySliceChoice 7 searchRows26 9 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part9Op3 : CoreSearch.replaySliceChoice 7 searchRows26 9 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part9 : CoreSearch.replaySlice 7 searchRows26 9 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay26Part9Op0
  · exact caseReplay26Part9Op1
  · exact caseReplay26Part9Op2
  · exact caseReplay26Part9Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part10Op0 : CoreSearch.replaySliceChoice 7 searchRows26 10 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part10Op1 : CoreSearch.replaySliceChoice 7 searchRows26 10 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part10Op2 : CoreSearch.replaySliceChoice 7 searchRows26 10 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part10Op3 : CoreSearch.replaySliceChoice 7 searchRows26 10 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part10 : CoreSearch.replaySlice 7 searchRows26 10 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay26Part10Op0
  · exact caseReplay26Part10Op1
  · exact caseReplay26Part10Op2
  · exact caseReplay26Part10Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part11Op0 : CoreSearch.replaySliceChoice 7 searchRows26 11 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part11Op1 : CoreSearch.replaySliceChoice 7 searchRows26 11 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part11Op2 : CoreSearch.replaySliceChoice 7 searchRows26 11 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part11Op3 : CoreSearch.replaySliceChoice 7 searchRows26 11 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part11 : CoreSearch.replaySlice 7 searchRows26 11 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay26Part11Op0
  · exact caseReplay26Part11Op1
  · exact caseReplay26Part11Op2
  · exact caseReplay26Part11Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part12Op0 : CoreSearch.replaySliceChoice 7 searchRows26 12 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part12Op1 : CoreSearch.replaySliceChoice 7 searchRows26 12 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part12Op2 : CoreSearch.replaySliceChoice 7 searchRows26 12 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part12Op3 : CoreSearch.replaySliceChoice 7 searchRows26 12 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part12 : CoreSearch.replaySlice 7 searchRows26 12 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay26Part12Op0
  · exact caseReplay26Part12Op1
  · exact caseReplay26Part12Op2
  · exact caseReplay26Part12Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part13Op0 : CoreSearch.replaySliceChoice 7 searchRows26 13 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part13Op1 : CoreSearch.replaySliceChoice 7 searchRows26 13 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part13Op2 : CoreSearch.replaySliceChoice 7 searchRows26 13 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part13Op3 : CoreSearch.replaySliceChoice 7 searchRows26 13 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part13 : CoreSearch.replaySlice 7 searchRows26 13 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay26Part13Op0
  · exact caseReplay26Part13Op1
  · exact caseReplay26Part13Op2
  · exact caseReplay26Part13Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part14Op0 : CoreSearch.replaySliceChoice 7 searchRows26 14 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part14Op1 : CoreSearch.replaySliceChoice 7 searchRows26 14 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part14Op2 : CoreSearch.replaySliceChoice 7 searchRows26 14 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part14Op3 : CoreSearch.replaySliceChoice 7 searchRows26 14 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26Part14 : CoreSearch.replaySlice 7 searchRows26 14 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay26Part14Op0
  · exact caseReplay26Part14Op1
  · exact caseReplay26Part14Op2
  · exact caseReplay26Part14Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay26 : CoreSearch.replay 7 searchRows26 = false := by
  apply CoreSearch.replay_split (m := 15) (by decide +kernel) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact caseReplay26Part0
  · exact caseReplay26Part1
  · exact caseReplay26Part2
  · exact caseReplay26Part3
  · exact caseReplay26Part4
  · exact caseReplay26Part5
  · exact caseReplay26Part6
  · exact caseReplay26Part7
  · exact caseReplay26Part8
  · exact caseReplay26Part9
  · exact caseReplay26Part10
  · exact caseReplay26Part11
  · exact caseReplay26Part12
  · exact caseReplay26Part13
  · exact caseReplay26Part14

def searchRows27 : List Nat := [0xaa624bbf7f75b6c88822491011702640, 0xfdfdc753fcfaf1eff5bdc713bceaf0ed, 0x3395fbc86febdc15208192c840011805, 0xc76bbdeed3f75f722aebb9eed3775f52, 0x44eb43677ac4bd9504c242626884198, 0xddb92cc5fadb2b2e5d102cc56a980b2a]

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part0Op0 : CoreSearch.replaySliceChoice 7 searchRows27 0 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part0Op1 : CoreSearch.replaySliceChoice 7 searchRows27 0 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part0Op2 : CoreSearch.replaySliceChoice 7 searchRows27 0 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part0Op3 : CoreSearch.replaySliceChoice 7 searchRows27 0 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part0 : CoreSearch.replaySlice 7 searchRows27 0 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay27Part0Op0
  · exact caseReplay27Part0Op1
  · exact caseReplay27Part0Op2
  · exact caseReplay27Part0Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part1Op0 : CoreSearch.replaySliceChoice 7 searchRows27 1 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part1Op1 : CoreSearch.replaySliceChoice 7 searchRows27 1 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part1Op2 : CoreSearch.replaySliceChoice 7 searchRows27 1 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part1Op3 : CoreSearch.replaySliceChoice 7 searchRows27 1 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part1 : CoreSearch.replaySlice 7 searchRows27 1 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay27Part1Op0
  · exact caseReplay27Part1Op1
  · exact caseReplay27Part1Op2
  · exact caseReplay27Part1Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part2Op0 : CoreSearch.replaySliceChoice 7 searchRows27 2 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part2Op1 : CoreSearch.replaySliceChoice 7 searchRows27 2 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part2Op2 : CoreSearch.replaySliceChoice 7 searchRows27 2 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part2Op3 : CoreSearch.replaySliceChoice 7 searchRows27 2 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part2 : CoreSearch.replaySlice 7 searchRows27 2 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay27Part2Op0
  · exact caseReplay27Part2Op1
  · exact caseReplay27Part2Op2
  · exact caseReplay27Part2Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part3Op0 : CoreSearch.replaySliceChoice 7 searchRows27 3 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part3Op1 : CoreSearch.replaySliceChoice 7 searchRows27 3 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part3Op2 : CoreSearch.replaySliceChoice 7 searchRows27 3 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part3Op3 : CoreSearch.replaySliceChoice 7 searchRows27 3 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part3 : CoreSearch.replaySlice 7 searchRows27 3 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay27Part3Op0
  · exact caseReplay27Part3Op1
  · exact caseReplay27Part3Op2
  · exact caseReplay27Part3Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part4Op0 : CoreSearch.replaySliceChoice 7 searchRows27 4 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part4Op1 : CoreSearch.replaySliceChoice 7 searchRows27 4 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part4Op2 : CoreSearch.replaySliceChoice 7 searchRows27 4 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part4Op3 : CoreSearch.replaySliceChoice 7 searchRows27 4 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part4 : CoreSearch.replaySlice 7 searchRows27 4 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay27Part4Op0
  · exact caseReplay27Part4Op1
  · exact caseReplay27Part4Op2
  · exact caseReplay27Part4Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part5Op0 : CoreSearch.replaySliceChoice 7 searchRows27 5 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part5Op1 : CoreSearch.replaySliceChoice 7 searchRows27 5 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part5Op2 : CoreSearch.replaySliceChoice 7 searchRows27 5 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part5Op3 : CoreSearch.replaySliceChoice 7 searchRows27 5 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part5 : CoreSearch.replaySlice 7 searchRows27 5 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay27Part5Op0
  · exact caseReplay27Part5Op1
  · exact caseReplay27Part5Op2
  · exact caseReplay27Part5Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part6Op0 : CoreSearch.replaySliceChoice 7 searchRows27 6 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part6Op1 : CoreSearch.replaySliceChoice 7 searchRows27 6 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part6Op2 : CoreSearch.replaySliceChoice 7 searchRows27 6 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part6Op3 : CoreSearch.replaySliceChoice 7 searchRows27 6 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part6 : CoreSearch.replaySlice 7 searchRows27 6 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay27Part6Op0
  · exact caseReplay27Part6Op1
  · exact caseReplay27Part6Op2
  · exact caseReplay27Part6Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part7Op0 : CoreSearch.replaySliceChoice 7 searchRows27 7 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part7Op1 : CoreSearch.replaySliceChoice 7 searchRows27 7 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part7Op2 : CoreSearch.replaySliceChoice 7 searchRows27 7 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part7Op3 : CoreSearch.replaySliceChoice 7 searchRows27 7 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part7 : CoreSearch.replaySlice 7 searchRows27 7 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay27Part7Op0
  · exact caseReplay27Part7Op1
  · exact caseReplay27Part7Op2
  · exact caseReplay27Part7Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part8Op0 : CoreSearch.replaySliceChoice 7 searchRows27 8 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part8Op1 : CoreSearch.replaySliceChoice 7 searchRows27 8 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part8Op2 : CoreSearch.replaySliceChoice 7 searchRows27 8 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part8Op3 : CoreSearch.replaySliceChoice 7 searchRows27 8 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part8 : CoreSearch.replaySlice 7 searchRows27 8 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay27Part8Op0
  · exact caseReplay27Part8Op1
  · exact caseReplay27Part8Op2
  · exact caseReplay27Part8Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part9Op0 : CoreSearch.replaySliceChoice 7 searchRows27 9 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part9Op1 : CoreSearch.replaySliceChoice 7 searchRows27 9 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part9Op2 : CoreSearch.replaySliceChoice 7 searchRows27 9 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part9Op3 : CoreSearch.replaySliceChoice 7 searchRows27 9 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part9 : CoreSearch.replaySlice 7 searchRows27 9 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay27Part9Op0
  · exact caseReplay27Part9Op1
  · exact caseReplay27Part9Op2
  · exact caseReplay27Part9Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part10Op0 : CoreSearch.replaySliceChoice 7 searchRows27 10 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part10Op1 : CoreSearch.replaySliceChoice 7 searchRows27 10 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part10Op2 : CoreSearch.replaySliceChoice 7 searchRows27 10 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part10Op3 : CoreSearch.replaySliceChoice 7 searchRows27 10 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part10 : CoreSearch.replaySlice 7 searchRows27 10 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay27Part10Op0
  · exact caseReplay27Part10Op1
  · exact caseReplay27Part10Op2
  · exact caseReplay27Part10Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part11Op0 : CoreSearch.replaySliceChoice 7 searchRows27 11 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part11Op1 : CoreSearch.replaySliceChoice 7 searchRows27 11 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part11Op2 : CoreSearch.replaySliceChoice 7 searchRows27 11 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part11Op3 : CoreSearch.replaySliceChoice 7 searchRows27 11 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part11 : CoreSearch.replaySlice 7 searchRows27 11 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay27Part11Op0
  · exact caseReplay27Part11Op1
  · exact caseReplay27Part11Op2
  · exact caseReplay27Part11Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part12Op0 : CoreSearch.replaySliceChoice 7 searchRows27 12 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part12Op1 : CoreSearch.replaySliceChoice 7 searchRows27 12 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part12Op2 : CoreSearch.replaySliceChoice 7 searchRows27 12 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part12Op3 : CoreSearch.replaySliceChoice 7 searchRows27 12 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part12 : CoreSearch.replaySlice 7 searchRows27 12 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay27Part12Op0
  · exact caseReplay27Part12Op1
  · exact caseReplay27Part12Op2
  · exact caseReplay27Part12Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part13Op0 : CoreSearch.replaySliceChoice 7 searchRows27 13 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part13Op1 : CoreSearch.replaySliceChoice 7 searchRows27 13 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part13Op2 : CoreSearch.replaySliceChoice 7 searchRows27 13 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part13Op3 : CoreSearch.replaySliceChoice 7 searchRows27 13 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part13 : CoreSearch.replaySlice 7 searchRows27 13 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay27Part13Op0
  · exact caseReplay27Part13Op1
  · exact caseReplay27Part13Op2
  · exact caseReplay27Part13Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part14Op0 : CoreSearch.replaySliceChoice 7 searchRows27 14 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part14Op1 : CoreSearch.replaySliceChoice 7 searchRows27 14 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part14Op2 : CoreSearch.replaySliceChoice 7 searchRows27 14 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part14Op3 : CoreSearch.replaySliceChoice 7 searchRows27 14 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27Part14 : CoreSearch.replaySlice 7 searchRows27 14 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay27Part14Op0
  · exact caseReplay27Part14Op1
  · exact caseReplay27Part14Op2
  · exact caseReplay27Part14Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay27 : CoreSearch.replay 7 searchRows27 = false := by
  apply CoreSearch.replay_split (m := 15) (by decide +kernel) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact caseReplay27Part0
  · exact caseReplay27Part1
  · exact caseReplay27Part2
  · exact caseReplay27Part3
  · exact caseReplay27Part4
  · exact caseReplay27Part5
  · exact caseReplay27Part6
  · exact caseReplay27Part7
  · exact caseReplay27Part8
  · exact caseReplay27Part9
  · exact caseReplay27Part10
  · exact caseReplay27Part11
  · exact caseReplay27Part12
  · exact caseReplay27Part13
  · exact caseReplay27Part14

def searchRows28 : List Nat := [0xf58e7fa3bffff7a7c40e0d80a0406325, 0xa202615c0986c1102002611c0986c10, 0x7b778ffee61f8cfb39b10a76640c84eb, 0xf679d5cb6d17c65c4469d58b4913c654, 0xbefdf85d59fb7bde3bd0f04d0023189a, 0xd1cec1620a2601e49d96c1620a2601c4]

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part0Op0 : CoreSearch.replaySliceChoice 7 searchRows28 0 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part0Op1 : CoreSearch.replaySliceChoice 7 searchRows28 0 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part0Op2 : CoreSearch.replaySliceChoice 7 searchRows28 0 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part0Op3 : CoreSearch.replaySliceChoice 7 searchRows28 0 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part0 : CoreSearch.replaySlice 7 searchRows28 0 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay28Part0Op0
  · exact caseReplay28Part0Op1
  · exact caseReplay28Part0Op2
  · exact caseReplay28Part0Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part1Op0 : CoreSearch.replaySliceChoice 7 searchRows28 1 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part1Op1 : CoreSearch.replaySliceChoice 7 searchRows28 1 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part1Op2 : CoreSearch.replaySliceChoice 7 searchRows28 1 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part1Op3 : CoreSearch.replaySliceChoice 7 searchRows28 1 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part1 : CoreSearch.replaySlice 7 searchRows28 1 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay28Part1Op0
  · exact caseReplay28Part1Op1
  · exact caseReplay28Part1Op2
  · exact caseReplay28Part1Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part2Op0 : CoreSearch.replaySliceChoice 7 searchRows28 2 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part2Op1 : CoreSearch.replaySliceChoice 7 searchRows28 2 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part2Op2 : CoreSearch.replaySliceChoice 7 searchRows28 2 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part2Op3 : CoreSearch.replaySliceChoice 7 searchRows28 2 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part2 : CoreSearch.replaySlice 7 searchRows28 2 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay28Part2Op0
  · exact caseReplay28Part2Op1
  · exact caseReplay28Part2Op2
  · exact caseReplay28Part2Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part3Op0 : CoreSearch.replaySliceChoice 7 searchRows28 3 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part3Op1 : CoreSearch.replaySliceChoice 7 searchRows28 3 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part3Op2 : CoreSearch.replaySliceChoice 7 searchRows28 3 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part3Op3 : CoreSearch.replaySliceChoice 7 searchRows28 3 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part3 : CoreSearch.replaySlice 7 searchRows28 3 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay28Part3Op0
  · exact caseReplay28Part3Op1
  · exact caseReplay28Part3Op2
  · exact caseReplay28Part3Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part4Op0 : CoreSearch.replaySliceChoice 7 searchRows28 4 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part4Op1 : CoreSearch.replaySliceChoice 7 searchRows28 4 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part4Op2 : CoreSearch.replaySliceChoice 7 searchRows28 4 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part4Op3 : CoreSearch.replaySliceChoice 7 searchRows28 4 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part4 : CoreSearch.replaySlice 7 searchRows28 4 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay28Part4Op0
  · exact caseReplay28Part4Op1
  · exact caseReplay28Part4Op2
  · exact caseReplay28Part4Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part5Op0 : CoreSearch.replaySliceChoice 7 searchRows28 5 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part5Op1 : CoreSearch.replaySliceChoice 7 searchRows28 5 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part5Op2 : CoreSearch.replaySliceChoice 7 searchRows28 5 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part5Op3 : CoreSearch.replaySliceChoice 7 searchRows28 5 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part5 : CoreSearch.replaySlice 7 searchRows28 5 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay28Part5Op0
  · exact caseReplay28Part5Op1
  · exact caseReplay28Part5Op2
  · exact caseReplay28Part5Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part6Op0 : CoreSearch.replaySliceChoice 7 searchRows28 6 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part6Op1 : CoreSearch.replaySliceChoice 7 searchRows28 6 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part6Op2 : CoreSearch.replaySliceChoice 7 searchRows28 6 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part6Op3 : CoreSearch.replaySliceChoice 7 searchRows28 6 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part6 : CoreSearch.replaySlice 7 searchRows28 6 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay28Part6Op0
  · exact caseReplay28Part6Op1
  · exact caseReplay28Part6Op2
  · exact caseReplay28Part6Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part7Op0 : CoreSearch.replaySliceChoice 7 searchRows28 7 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part7Op1 : CoreSearch.replaySliceChoice 7 searchRows28 7 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part7Op2 : CoreSearch.replaySliceChoice 7 searchRows28 7 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part7Op3 : CoreSearch.replaySliceChoice 7 searchRows28 7 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part7 : CoreSearch.replaySlice 7 searchRows28 7 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay28Part7Op0
  · exact caseReplay28Part7Op1
  · exact caseReplay28Part7Op2
  · exact caseReplay28Part7Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part8Op0 : CoreSearch.replaySliceChoice 7 searchRows28 8 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part8Op1 : CoreSearch.replaySliceChoice 7 searchRows28 8 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part8Op2 : CoreSearch.replaySliceChoice 7 searchRows28 8 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part8Op3 : CoreSearch.replaySliceChoice 7 searchRows28 8 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part8 : CoreSearch.replaySlice 7 searchRows28 8 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay28Part8Op0
  · exact caseReplay28Part8Op1
  · exact caseReplay28Part8Op2
  · exact caseReplay28Part8Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part9Op0 : CoreSearch.replaySliceChoice 7 searchRows28 9 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part9Op1 : CoreSearch.replaySliceChoice 7 searchRows28 9 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part9Op2 : CoreSearch.replaySliceChoice 7 searchRows28 9 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part9Op3 : CoreSearch.replaySliceChoice 7 searchRows28 9 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part9 : CoreSearch.replaySlice 7 searchRows28 9 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay28Part9Op0
  · exact caseReplay28Part9Op1
  · exact caseReplay28Part9Op2
  · exact caseReplay28Part9Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part10Op0 : CoreSearch.replaySliceChoice 7 searchRows28 10 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part10Op1 : CoreSearch.replaySliceChoice 7 searchRows28 10 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part10Op2 : CoreSearch.replaySliceChoice 7 searchRows28 10 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part10Op3 : CoreSearch.replaySliceChoice 7 searchRows28 10 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part10 : CoreSearch.replaySlice 7 searchRows28 10 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay28Part10Op0
  · exact caseReplay28Part10Op1
  · exact caseReplay28Part10Op2
  · exact caseReplay28Part10Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part11Op0 : CoreSearch.replaySliceChoice 7 searchRows28 11 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part11Op1 : CoreSearch.replaySliceChoice 7 searchRows28 11 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part11Op2 : CoreSearch.replaySliceChoice 7 searchRows28 11 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part11Op3 : CoreSearch.replaySliceChoice 7 searchRows28 11 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part11 : CoreSearch.replaySlice 7 searchRows28 11 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay28Part11Op0
  · exact caseReplay28Part11Op1
  · exact caseReplay28Part11Op2
  · exact caseReplay28Part11Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part12Op0 : CoreSearch.replaySliceChoice 7 searchRows28 12 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part12Op1 : CoreSearch.replaySliceChoice 7 searchRows28 12 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part12Op2 : CoreSearch.replaySliceChoice 7 searchRows28 12 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part12Op3 : CoreSearch.replaySliceChoice 7 searchRows28 12 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part12 : CoreSearch.replaySlice 7 searchRows28 12 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay28Part12Op0
  · exact caseReplay28Part12Op1
  · exact caseReplay28Part12Op2
  · exact caseReplay28Part12Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part13Op0 : CoreSearch.replaySliceChoice 7 searchRows28 13 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part13Op1 : CoreSearch.replaySliceChoice 7 searchRows28 13 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part13Op2 : CoreSearch.replaySliceChoice 7 searchRows28 13 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part13Op3 : CoreSearch.replaySliceChoice 7 searchRows28 13 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part13 : CoreSearch.replaySlice 7 searchRows28 13 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay28Part13Op0
  · exact caseReplay28Part13Op1
  · exact caseReplay28Part13Op2
  · exact caseReplay28Part13Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part14Op0 : CoreSearch.replaySliceChoice 7 searchRows28 14 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part14Op1 : CoreSearch.replaySliceChoice 7 searchRows28 14 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part14Op2 : CoreSearch.replaySliceChoice 7 searchRows28 14 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part14Op3 : CoreSearch.replaySliceChoice 7 searchRows28 14 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28Part14 : CoreSearch.replaySlice 7 searchRows28 14 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay28Part14Op0
  · exact caseReplay28Part14Op1
  · exact caseReplay28Part14Op2
  · exact caseReplay28Part14Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay28 : CoreSearch.replay 7 searchRows28 = false := by
  apply CoreSearch.replay_split (m := 15) (by decide +kernel) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact caseReplay28Part0
  · exact caseReplay28Part1
  · exact caseReplay28Part2
  · exact caseReplay28Part3
  · exact caseReplay28Part4
  · exact caseReplay28Part5
  · exact caseReplay28Part6
  · exact caseReplay28Part7
  · exact caseReplay28Part8
  · exact caseReplay28Part9
  · exact caseReplay28Part10
  · exact caseReplay28Part11
  · exact caseReplay28Part12
  · exact caseReplay28Part13
  · exact caseReplay28Part14

def searchRows29 : List Nat := [0xf77fce7ce6fa7fc2e39f465480821d80, 0x6794e1af8dac8deb5608c1af84a884ea, 0x2c0a330657e5b0540000310241002050, 0xef8f3f8fffffb1fde4bd3f0fff85b1dd, 0xda619cdb37dbc697186088893608c207, 0x59f477e1bf3d692b99b036e03b116923]

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part0Op0 : CoreSearch.replaySliceChoice 7 searchRows29 0 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part0Op1 : CoreSearch.replaySliceChoice 7 searchRows29 0 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part0Op2 : CoreSearch.replaySliceChoice 7 searchRows29 0 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part0Op3 : CoreSearch.replaySliceChoice 7 searchRows29 0 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part0 : CoreSearch.replaySlice 7 searchRows29 0 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay29Part0Op0
  · exact caseReplay29Part0Op1
  · exact caseReplay29Part0Op2
  · exact caseReplay29Part0Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part1Op0 : CoreSearch.replaySliceChoice 7 searchRows29 1 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part1Op1 : CoreSearch.replaySliceChoice 7 searchRows29 1 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part1Op2 : CoreSearch.replaySliceChoice 7 searchRows29 1 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part1Op3 : CoreSearch.replaySliceChoice 7 searchRows29 1 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part1 : CoreSearch.replaySlice 7 searchRows29 1 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay29Part1Op0
  · exact caseReplay29Part1Op1
  · exact caseReplay29Part1Op2
  · exact caseReplay29Part1Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part2Op0 : CoreSearch.replaySliceChoice 7 searchRows29 2 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part2Op1 : CoreSearch.replaySliceChoice 7 searchRows29 2 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part2Op2 : CoreSearch.replaySliceChoice 7 searchRows29 2 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part2Op3 : CoreSearch.replaySliceChoice 7 searchRows29 2 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part2 : CoreSearch.replaySlice 7 searchRows29 2 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay29Part2Op0
  · exact caseReplay29Part2Op1
  · exact caseReplay29Part2Op2
  · exact caseReplay29Part2Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part3Op0 : CoreSearch.replaySliceChoice 7 searchRows29 3 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part3Op1 : CoreSearch.replaySliceChoice 7 searchRows29 3 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part3Op2 : CoreSearch.replaySliceChoice 7 searchRows29 3 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part3Op3 : CoreSearch.replaySliceChoice 7 searchRows29 3 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part3 : CoreSearch.replaySlice 7 searchRows29 3 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay29Part3Op0
  · exact caseReplay29Part3Op1
  · exact caseReplay29Part3Op2
  · exact caseReplay29Part3Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part4Op0 : CoreSearch.replaySliceChoice 7 searchRows29 4 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part4Op1 : CoreSearch.replaySliceChoice 7 searchRows29 4 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part4Op2 : CoreSearch.replaySliceChoice 7 searchRows29 4 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part4Op3 : CoreSearch.replaySliceChoice 7 searchRows29 4 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part4 : CoreSearch.replaySlice 7 searchRows29 4 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay29Part4Op0
  · exact caseReplay29Part4Op1
  · exact caseReplay29Part4Op2
  · exact caseReplay29Part4Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part5Op0 : CoreSearch.replaySliceChoice 7 searchRows29 5 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part5Op1 : CoreSearch.replaySliceChoice 7 searchRows29 5 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part5Op2 : CoreSearch.replaySliceChoice 7 searchRows29 5 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part5Op3 : CoreSearch.replaySliceChoice 7 searchRows29 5 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part5 : CoreSearch.replaySlice 7 searchRows29 5 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay29Part5Op0
  · exact caseReplay29Part5Op1
  · exact caseReplay29Part5Op2
  · exact caseReplay29Part5Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part6Op0 : CoreSearch.replaySliceChoice 7 searchRows29 6 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part6Op1 : CoreSearch.replaySliceChoice 7 searchRows29 6 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part6Op2 : CoreSearch.replaySliceChoice 7 searchRows29 6 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part6Op3 : CoreSearch.replaySliceChoice 7 searchRows29 6 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part6 : CoreSearch.replaySlice 7 searchRows29 6 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay29Part6Op0
  · exact caseReplay29Part6Op1
  · exact caseReplay29Part6Op2
  · exact caseReplay29Part6Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part7Op0 : CoreSearch.replaySliceChoice 7 searchRows29 7 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part7Op1 : CoreSearch.replaySliceChoice 7 searchRows29 7 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part7Op2 : CoreSearch.replaySliceChoice 7 searchRows29 7 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part7Op3 : CoreSearch.replaySliceChoice 7 searchRows29 7 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part7 : CoreSearch.replaySlice 7 searchRows29 7 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay29Part7Op0
  · exact caseReplay29Part7Op1
  · exact caseReplay29Part7Op2
  · exact caseReplay29Part7Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part8Op0 : CoreSearch.replaySliceChoice 7 searchRows29 8 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part8Op1 : CoreSearch.replaySliceChoice 7 searchRows29 8 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part8Op2 : CoreSearch.replaySliceChoice 7 searchRows29 8 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part8Op3 : CoreSearch.replaySliceChoice 7 searchRows29 8 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part8 : CoreSearch.replaySlice 7 searchRows29 8 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay29Part8Op0
  · exact caseReplay29Part8Op1
  · exact caseReplay29Part8Op2
  · exact caseReplay29Part8Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part9Op0 : CoreSearch.replaySliceChoice 7 searchRows29 9 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part9Op1 : CoreSearch.replaySliceChoice 7 searchRows29 9 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part9Op2 : CoreSearch.replaySliceChoice 7 searchRows29 9 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part9Op3 : CoreSearch.replaySliceChoice 7 searchRows29 9 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part9 : CoreSearch.replaySlice 7 searchRows29 9 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay29Part9Op0
  · exact caseReplay29Part9Op1
  · exact caseReplay29Part9Op2
  · exact caseReplay29Part9Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part10Op0 : CoreSearch.replaySliceChoice 7 searchRows29 10 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part10Op1 : CoreSearch.replaySliceChoice 7 searchRows29 10 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part10Op2 : CoreSearch.replaySliceChoice 7 searchRows29 10 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part10Op3 : CoreSearch.replaySliceChoice 7 searchRows29 10 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part10 : CoreSearch.replaySlice 7 searchRows29 10 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay29Part10Op0
  · exact caseReplay29Part10Op1
  · exact caseReplay29Part10Op2
  · exact caseReplay29Part10Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part11Op0 : CoreSearch.replaySliceChoice 7 searchRows29 11 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part11Op1 : CoreSearch.replaySliceChoice 7 searchRows29 11 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part11Op2 : CoreSearch.replaySliceChoice 7 searchRows29 11 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part11Op3 : CoreSearch.replaySliceChoice 7 searchRows29 11 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part11 : CoreSearch.replaySlice 7 searchRows29 11 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay29Part11Op0
  · exact caseReplay29Part11Op1
  · exact caseReplay29Part11Op2
  · exact caseReplay29Part11Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part12Op0 : CoreSearch.replaySliceChoice 7 searchRows29 12 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part12Op1 : CoreSearch.replaySliceChoice 7 searchRows29 12 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part12Op2 : CoreSearch.replaySliceChoice 7 searchRows29 12 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part12Op3 : CoreSearch.replaySliceChoice 7 searchRows29 12 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part12 : CoreSearch.replaySlice 7 searchRows29 12 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay29Part12Op0
  · exact caseReplay29Part12Op1
  · exact caseReplay29Part12Op2
  · exact caseReplay29Part12Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part13Op0 : CoreSearch.replaySliceChoice 7 searchRows29 13 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part13Op1 : CoreSearch.replaySliceChoice 7 searchRows29 13 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part13Op2 : CoreSearch.replaySliceChoice 7 searchRows29 13 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part13Op3 : CoreSearch.replaySliceChoice 7 searchRows29 13 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part13 : CoreSearch.replaySlice 7 searchRows29 13 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay29Part13Op0
  · exact caseReplay29Part13Op1
  · exact caseReplay29Part13Op2
  · exact caseReplay29Part13Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part14Op0 : CoreSearch.replaySliceChoice 7 searchRows29 14 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part14Op1 : CoreSearch.replaySliceChoice 7 searchRows29 14 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part14Op2 : CoreSearch.replaySliceChoice 7 searchRows29 14 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part14Op3 : CoreSearch.replaySliceChoice 7 searchRows29 14 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29Part14 : CoreSearch.replaySlice 7 searchRows29 14 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay29Part14Op0
  · exact caseReplay29Part14Op1
  · exact caseReplay29Part14Op2
  · exact caseReplay29Part14Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay29 : CoreSearch.replay 7 searchRows29 = false := by
  apply CoreSearch.replay_split (m := 15) (by decide +kernel) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact caseReplay29Part0
  · exact caseReplay29Part1
  · exact caseReplay29Part2
  · exact caseReplay29Part3
  · exact caseReplay29Part4
  · exact caseReplay29Part5
  · exact caseReplay29Part6
  · exact caseReplay29Part7
  · exact caseReplay29Part8
  · exact caseReplay29Part9
  · exact caseReplay29Part10
  · exact caseReplay29Part11
  · exact caseReplay29Part12
  · exact caseReplay29Part13
  · exact caseReplay29Part14

def searchRows30 : List Nat := [0xce1506c57ff38bcf820106802202814b, 0x6be2eabcef9f34d3516242b4cb0514d1, 0x3108912a177cc4342408900810000024, 0xb8eb7d96a6cafe6099a52d96268ade40, 0xf59f9fffd7ffefbc75ee997fd5902eb4, 0xcaeeed31bdacb8eb0844ed21bdaca8aa]

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part0Op0 : CoreSearch.replaySliceChoice 7 searchRows30 0 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part0Op1 : CoreSearch.replaySliceChoice 7 searchRows30 0 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part0Op2 : CoreSearch.replaySliceChoice 7 searchRows30 0 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part0Op3 : CoreSearch.replaySliceChoice 7 searchRows30 0 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part0 : CoreSearch.replaySlice 7 searchRows30 0 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay30Part0Op0
  · exact caseReplay30Part0Op1
  · exact caseReplay30Part0Op2
  · exact caseReplay30Part0Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part1Op0 : CoreSearch.replaySliceChoice 7 searchRows30 1 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part1Op1 : CoreSearch.replaySliceChoice 7 searchRows30 1 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part1Op2 : CoreSearch.replaySliceChoice 7 searchRows30 1 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part1Op3 : CoreSearch.replaySliceChoice 7 searchRows30 1 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part1 : CoreSearch.replaySlice 7 searchRows30 1 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay30Part1Op0
  · exact caseReplay30Part1Op1
  · exact caseReplay30Part1Op2
  · exact caseReplay30Part1Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part2Op0 : CoreSearch.replaySliceChoice 7 searchRows30 2 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part2Op1 : CoreSearch.replaySliceChoice 7 searchRows30 2 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part2Op2 : CoreSearch.replaySliceChoice 7 searchRows30 2 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part2Op3 : CoreSearch.replaySliceChoice 7 searchRows30 2 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part2 : CoreSearch.replaySlice 7 searchRows30 2 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay30Part2Op0
  · exact caseReplay30Part2Op1
  · exact caseReplay30Part2Op2
  · exact caseReplay30Part2Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part3Op0 : CoreSearch.replaySliceChoice 7 searchRows30 3 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part3Op1 : CoreSearch.replaySliceChoice 7 searchRows30 3 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part3Op2 : CoreSearch.replaySliceChoice 7 searchRows30 3 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part3Op3 : CoreSearch.replaySliceChoice 7 searchRows30 3 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part3 : CoreSearch.replaySlice 7 searchRows30 3 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay30Part3Op0
  · exact caseReplay30Part3Op1
  · exact caseReplay30Part3Op2
  · exact caseReplay30Part3Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part4Op0 : CoreSearch.replaySliceChoice 7 searchRows30 4 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part4Op1 : CoreSearch.replaySliceChoice 7 searchRows30 4 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part4Op2 : CoreSearch.replaySliceChoice 7 searchRows30 4 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part4Op3 : CoreSearch.replaySliceChoice 7 searchRows30 4 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part4 : CoreSearch.replaySlice 7 searchRows30 4 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay30Part4Op0
  · exact caseReplay30Part4Op1
  · exact caseReplay30Part4Op2
  · exact caseReplay30Part4Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part5Op0 : CoreSearch.replaySliceChoice 7 searchRows30 5 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part5Op1 : CoreSearch.replaySliceChoice 7 searchRows30 5 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part5Op2 : CoreSearch.replaySliceChoice 7 searchRows30 5 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part5Op3 : CoreSearch.replaySliceChoice 7 searchRows30 5 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part5 : CoreSearch.replaySlice 7 searchRows30 5 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay30Part5Op0
  · exact caseReplay30Part5Op1
  · exact caseReplay30Part5Op2
  · exact caseReplay30Part5Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part6Op0 : CoreSearch.replaySliceChoice 7 searchRows30 6 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part6Op1 : CoreSearch.replaySliceChoice 7 searchRows30 6 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part6Op2 : CoreSearch.replaySliceChoice 7 searchRows30 6 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part6Op3 : CoreSearch.replaySliceChoice 7 searchRows30 6 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part6 : CoreSearch.replaySlice 7 searchRows30 6 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay30Part6Op0
  · exact caseReplay30Part6Op1
  · exact caseReplay30Part6Op2
  · exact caseReplay30Part6Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part7Op0 : CoreSearch.replaySliceChoice 7 searchRows30 7 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part7Op1 : CoreSearch.replaySliceChoice 7 searchRows30 7 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part7Op2 : CoreSearch.replaySliceChoice 7 searchRows30 7 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part7Op3 : CoreSearch.replaySliceChoice 7 searchRows30 7 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part7 : CoreSearch.replaySlice 7 searchRows30 7 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay30Part7Op0
  · exact caseReplay30Part7Op1
  · exact caseReplay30Part7Op2
  · exact caseReplay30Part7Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part8Op0 : CoreSearch.replaySliceChoice 7 searchRows30 8 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part8Op1 : CoreSearch.replaySliceChoice 7 searchRows30 8 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part8Op2 : CoreSearch.replaySliceChoice 7 searchRows30 8 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part8Op3 : CoreSearch.replaySliceChoice 7 searchRows30 8 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part8 : CoreSearch.replaySlice 7 searchRows30 8 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay30Part8Op0
  · exact caseReplay30Part8Op1
  · exact caseReplay30Part8Op2
  · exact caseReplay30Part8Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part9Op0 : CoreSearch.replaySliceChoice 7 searchRows30 9 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part9Op1 : CoreSearch.replaySliceChoice 7 searchRows30 9 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part9Op2 : CoreSearch.replaySliceChoice 7 searchRows30 9 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part9Op3 : CoreSearch.replaySliceChoice 7 searchRows30 9 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part9 : CoreSearch.replaySlice 7 searchRows30 9 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay30Part9Op0
  · exact caseReplay30Part9Op1
  · exact caseReplay30Part9Op2
  · exact caseReplay30Part9Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part10Op0 : CoreSearch.replaySliceChoice 7 searchRows30 10 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part10Op1 : CoreSearch.replaySliceChoice 7 searchRows30 10 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part10Op2 : CoreSearch.replaySliceChoice 7 searchRows30 10 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part10Op3 : CoreSearch.replaySliceChoice 7 searchRows30 10 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part10 : CoreSearch.replaySlice 7 searchRows30 10 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay30Part10Op0
  · exact caseReplay30Part10Op1
  · exact caseReplay30Part10Op2
  · exact caseReplay30Part10Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part11Op0 : CoreSearch.replaySliceChoice 7 searchRows30 11 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part11Op1 : CoreSearch.replaySliceChoice 7 searchRows30 11 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part11Op2 : CoreSearch.replaySliceChoice 7 searchRows30 11 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part11Op3 : CoreSearch.replaySliceChoice 7 searchRows30 11 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part11 : CoreSearch.replaySlice 7 searchRows30 11 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay30Part11Op0
  · exact caseReplay30Part11Op1
  · exact caseReplay30Part11Op2
  · exact caseReplay30Part11Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part12Op0 : CoreSearch.replaySliceChoice 7 searchRows30 12 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part12Op1 : CoreSearch.replaySliceChoice 7 searchRows30 12 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part12Op2 : CoreSearch.replaySliceChoice 7 searchRows30 12 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part12Op3 : CoreSearch.replaySliceChoice 7 searchRows30 12 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part12 : CoreSearch.replaySlice 7 searchRows30 12 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay30Part12Op0
  · exact caseReplay30Part12Op1
  · exact caseReplay30Part12Op2
  · exact caseReplay30Part12Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part13Op0 : CoreSearch.replaySliceChoice 7 searchRows30 13 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part13Op1 : CoreSearch.replaySliceChoice 7 searchRows30 13 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part13Op2 : CoreSearch.replaySliceChoice 7 searchRows30 13 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part13Op3 : CoreSearch.replaySliceChoice 7 searchRows30 13 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part13 : CoreSearch.replaySlice 7 searchRows30 13 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay30Part13Op0
  · exact caseReplay30Part13Op1
  · exact caseReplay30Part13Op2
  · exact caseReplay30Part13Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part14Op0 : CoreSearch.replaySliceChoice 7 searchRows30 14 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part14Op1 : CoreSearch.replaySliceChoice 7 searchRows30 14 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part14Op2 : CoreSearch.replaySliceChoice 7 searchRows30 14 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part14Op3 : CoreSearch.replaySliceChoice 7 searchRows30 14 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30Part14 : CoreSearch.replaySlice 7 searchRows30 14 = false := by
  apply CoreSearch.replaySlice_split
  intro j hj
  interval_cases j
  · exact caseReplay30Part14Op0
  · exact caseReplay30Part14Op1
  · exact caseReplay30Part14Op2
  · exact caseReplay30Part14Op3

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay30 : CoreSearch.replay 7 searchRows30 = false := by
  apply CoreSearch.replay_split (m := 15) (by decide +kernel) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact caseReplay30Part0
  · exact caseReplay30Part1
  · exact caseReplay30Part2
  · exact caseReplay30Part3
  · exact caseReplay30Part4
  · exact caseReplay30Part5
  · exact caseReplay30Part6
  · exact caseReplay30Part7
  · exact caseReplay30Part8
  · exact caseReplay30Part9
  · exact caseReplay30Part10
  · exact caseReplay30Part11
  · exact caseReplay30Part12
  · exact caseReplay30Part13
  · exact caseReplay30Part14

def searchRows31 : List Nat := [0xfcb79bd48fbe4dbea8159a808612003a, 0x61ee5d1b6fd99372700e59130e891370, 0x2ffeedfff7ffbadf0ee265fde104aacf, 0x271f5e216e727918061d56216a32790, 0xffc9722bddedfd251788200a59805d05, 0xa0e244c2772aa480400244c2100a800]

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay31Part0 : CoreSearch.replaySlice 7 searchRows31 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay31Part1 : CoreSearch.replaySlice 7 searchRows31 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay31Part2 : CoreSearch.replaySlice 7 searchRows31 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay31Part3 : CoreSearch.replaySlice 7 searchRows31 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay31Part4 : CoreSearch.replaySlice 7 searchRows31 4 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay31Part5 : CoreSearch.replaySlice 7 searchRows31 5 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay31Part6 : CoreSearch.replaySlice 7 searchRows31 6 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay31Part7 : CoreSearch.replaySlice 7 searchRows31 7 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay31Part8 : CoreSearch.replaySlice 7 searchRows31 8 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay31Part9 : CoreSearch.replaySlice 7 searchRows31 9 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay31Part10 : CoreSearch.replaySlice 7 searchRows31 10 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay31Part11 : CoreSearch.replaySlice 7 searchRows31 11 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay31Part12 : CoreSearch.replaySlice 7 searchRows31 12 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay31Part13 : CoreSearch.replaySlice 7 searchRows31 13 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay31Part14 : CoreSearch.replaySlice 7 searchRows31 14 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay31 : CoreSearch.replay 7 searchRows31 = false := by
  apply CoreSearch.replay_split (m := 15) (by decide +kernel) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact caseReplay31Part0
  · exact caseReplay31Part1
  · exact caseReplay31Part2
  · exact caseReplay31Part3
  · exact caseReplay31Part4
  · exact caseReplay31Part5
  · exact caseReplay31Part6
  · exact caseReplay31Part7
  · exact caseReplay31Part8
  · exact caseReplay31Part9
  · exact caseReplay31Part10
  · exact caseReplay31Part11
  · exact caseReplay31Part12
  · exact caseReplay31Part13
  · exact caseReplay31Part14

def searchRows32 : List Nat := [0x179dd2943debe7991448929020000098, 0x6bda3b1df7d751c609f2111da5d051c2, 0xf92d05f7ff3fa82ee90505445a2c2826, 0xf16ffffe6ed3b8fbfdefffb66453b8db, 0xaeb6dd6bbffccf7502b0486b9ffcc765, 0xe74e6e8b728eb5f2361c6e8b528ea530]

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay32Part0 : CoreSearch.replaySlice 7 searchRows32 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay32Part1 : CoreSearch.replaySlice 7 searchRows32 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay32Part2 : CoreSearch.replaySlice 7 searchRows32 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay32Part3 : CoreSearch.replaySlice 7 searchRows32 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay32Part4 : CoreSearch.replaySlice 7 searchRows32 4 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay32Part5 : CoreSearch.replaySlice 7 searchRows32 5 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay32Part6 : CoreSearch.replaySlice 7 searchRows32 6 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay32Part7 : CoreSearch.replaySlice 7 searchRows32 7 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay32Part8 : CoreSearch.replaySlice 7 searchRows32 8 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay32Part9 : CoreSearch.replaySlice 7 searchRows32 9 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay32Part10 : CoreSearch.replaySlice 7 searchRows32 10 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay32Part11 : CoreSearch.replaySlice 7 searchRows32 11 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay32Part12 : CoreSearch.replaySlice 7 searchRows32 12 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay32Part13 : CoreSearch.replaySlice 7 searchRows32 13 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay32Part14 : CoreSearch.replaySlice 7 searchRows32 14 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay32 : CoreSearch.replay 7 searchRows32 = false := by
  apply CoreSearch.replay_split (m := 15) (by decide +kernel) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact caseReplay32Part0
  · exact caseReplay32Part1
  · exact caseReplay32Part2
  · exact caseReplay32Part3
  · exact caseReplay32Part4
  · exact caseReplay32Part5
  · exact caseReplay32Part6
  · exact caseReplay32Part7
  · exact caseReplay32Part8
  · exact caseReplay32Part9
  · exact caseReplay32Part10
  · exact caseReplay32Part11
  · exact caseReplay32Part12
  · exact caseReplay32Part13
  · exact caseReplay32Part14

def searchRows33 : List Nat := [0xd7f3d7f3d7f3afeb2091209120914121, 0xebedebedebedd7dd1228122812282444, 0xbf9ebf9ebf9e7f3e4106410641068212, 0x40614061406180c12091209120914121]

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay33Part0 : CoreSearch.replaySlice 3 searchRows33 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay33Part1 : CoreSearch.replaySlice 3 searchRows33 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay33Part2 : CoreSearch.replaySlice 3 searchRows33 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay33Part3 : CoreSearch.replaySlice 3 searchRows33 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay33Part4 : CoreSearch.replaySlice 3 searchRows33 4 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay33Part5 : CoreSearch.replaySlice 3 searchRows33 5 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay33 : CoreSearch.replay 3 searchRows33 = false := by
  apply CoreSearch.replay_split (m := 6) (by decide +kernel) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact caseReplay33Part0
  · exact caseReplay33Part1
  · exact caseReplay33Part2
  · exact caseReplay33Part3
  · exact caseReplay33Part4
  · exact caseReplay33Part5

def searchRows34 : List Nat := [0xeddbeddbeddbdbb71052105210522086, 0x7be77be77be777db80a180a180a18141, 0xdefcdefcdefcbdfc280c280c280c5028, 0x21032103210342031052105210522086]

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay34Part0 : CoreSearch.replaySlice 3 searchRows34 0 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay34Part1 : CoreSearch.replaySlice 3 searchRows34 1 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay34Part2 : CoreSearch.replaySlice 3 searchRows34 2 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay34Part3 : CoreSearch.replaySlice 3 searchRows34 3 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay34Part4 : CoreSearch.replaySlice 3 searchRows34 4 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay34Part5 : CoreSearch.replaySlice 3 searchRows34 5 = false := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem caseReplay34 : CoreSearch.replay 3 searchRows34 = false := by
  apply CoreSearch.replay_split (m := 6) (by decide +kernel) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact caseReplay34Part0
  · exact caseReplay34Part1
  · exact caseReplay34Part2
  · exact caseReplay34Part3
  · exact caseReplay34Part4
  · exact caseReplay34Part5

def sixTarget : F := fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4209680512) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def sixWitness : Circuit := ⟨[⟨.and, [1, 5]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [6, 8]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [3, 10]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [11, 12]⟩, ⟨.and, [9, 13]⟩, ⟨.and, [0, 4]⟩, ⟨.or, [14, 15]⟩], 16⟩
theorem basis : Monotone2 sixWitness := by simp [Monotone2, sixWitness]
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
theorem correct : ∀ x : X, sixWitness.eval (List.ofFn x) = sixTarget x := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 64000 in
theorem fgBase : Low 1 sixTarget := (one 0 false (good_at 6 22 0 (by decide +kernel)) (zero _))

set_option maxHeartbeats 0 in
set_option maxRecDepth 64000 in
theorem fgMinor0 : Low 8 (fun x => sixTarget (FirstGate.glue 0 1 3 x)) := (CoreSearch.lower (n := 7) (f := (fun x => sixTarget (FirstGate.glue 0 1 3 x))) [0, 0x9d516582e84c0a7ae4f17ce2fbcd1e6a, 0xcc3de3ef3c1fdb2b4e1800a710198302, 0x956e9624d0ff66590136808090eb6619, 0xa7ebd893a3afbcec80217c00a3840068, 0x59d66f4cee46eb5611c127506e066854] [0x9d516582e84c0a7ae4f17ce2fbcd1e6a, 0xcc3de3ef3c1fdb2b4e1800a710198302, 0x956e9624d0ff66590136808090eb6619, 0xa7ebd893a3afbcec80217c00a3840068, 0x59d66f4cee46eb5611c127506e066854] (by decide +kernel) (by decide +kernel) (by unfold CoreSearch.Rep; decide +kernel) caseReplay0)

set_option maxHeartbeats 0 in
set_option maxRecDepth 64000 in
theorem fgMinor1 : Low 8 (rs 3 false sixTarget) := (one 4 false (good_at 1 7 0 (by decide +kernel)) (CoreSearch.lower (n := 6) (f := (rs 4 false (rs 3 false sixTarget))) [0xf6a6fffffea7ff3e38c6814050da271c, 0xffffff3d557ffbed984860b486806ae4, 0x6fff69e3fffdf6fb20005a93110b846b, 0, 0, 0xffdfd6febfdfbdd742b415212210d993] [0xf6a6fffffea7ff3e38c6814050da271c, 0xffffff3d557ffbed984860b486806ae4, 0x6fff69e3fffdf6fb20005a93110b846b, 0xffdfd6febfdfbdd742b415212210d993] (by decide +kernel) (by decide +kernel) (by unfold CoreSearch.Rep; decide +kernel) caseReplay1))

set_option maxHeartbeats 0 in
set_option maxRecDepth 64000 in
theorem fgMinor2 : Low 8 (fun x => sixTarget (FirstGate.glue 3 0 3 x)) := (CoreSearch.lower (n := 7) (f := (fun x => sixTarget (FirstGate.glue 3 0 3 x))) [0xe5661e6be87f71b1fe4a8c00e84570b1, 0xd0f1db9cdf262c771021780c0e220c33, 0x4f7d3c9363d2f60be90810010192740a, 0, 0x2fbb31ffaaa99f9c003061f212288b04, 0xdbf6cf56fddd4a6602848232f1dd0244] [0xe5661e6be87f71b1fe4a8c00e84570b1, 0xd0f1db9cdf262c771021780c0e220c33, 0x4f7d3c9363d2f60be90810010192740a, 0x2fbb31ffaaa99f9c003061f212288b04, 0xdbf6cf56fddd4a6602848232f1dd0244] (by decide +kernel) (by decide +kernel) (by unfold CoreSearch.Rep; decide +kernel) caseReplay2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 64000 in
theorem fgMinor3 : Low 8 (rs 4 false sixTarget) := (one 3 false (good_at 5 7 0 (by decide +kernel)) (CoreSearch.lower (n := 6) (f := (rs 3 false (rs 4 false sixTarget))) [0xf6a6fffffea7ff3e38c6814050da271c, 0xffffff3d557ffbed984860b486806ae4, 0x6fff69e3fffdf6fb20005a93110b846b, 0, 0, 0xffdfd6febfdfbdd742b415212210d993] [0xf6a6fffffea7ff3e38c6814050da271c, 0xffffff3d557ffbed984860b486806ae4, 0x6fff69e3fffdf6fb20005a93110b846b, 0xffdfd6febfdfbdd742b415212210d993] (by decide +kernel) (by decide +kernel) (by unfold CoreSearch.Rep; decide +kernel) caseReplay1))

set_option maxHeartbeats 0 in
set_option maxRecDepth 64000 in
theorem fgMinor4 : Low 8 (fun x => sixTarget (FirstGate.glue 0 5 3 x)) := (CoreSearch.lower (n := 7) (f := (fun x => sixTarget (FirstGate.glue 0 5 3 x))) [0, 0xfa7f4fe299775eba090599c28932009a, 0x1c5ecab745cfec37144a420044cc4425, 0x6ea9cdbdf43396c7420ea4fd74339642, 0x85a03749afaffb4907e00201a30d0a09, 0x62734ca395150ea137fa4e3bf70d3ea9] [0xfa7f4fe299775eba090599c28932009a, 0x1c5ecab745cfec37144a420044cc4425, 0x6ea9cdbdf43396c7420ea4fd74339642, 0x85a03749afaffb4907e00201a30d0a09, 0x62734ca395150ea137fa4e3bf70d3ea9] (by decide +kernel) (by decide +kernel) (by unfold CoreSearch.Rep; decide +kernel) caseReplay3)

set_option maxHeartbeats 0 in
set_option maxRecDepth 64000 in
theorem fgMinor5 : Low 8 (rs 5 true sixTarget) := (CoreSearch.lower (n := 7) (f := (rs 5 true sixTarget)) [0xfff2670b033de8de0c20000b03050006, 0xf81db9e4f4bfb726a08000444038b120, 0x155e8ed1cddbde91111e8e2084c20891, 0x5121fa363d5745e3570a303a3d4744c2, 0x6be1c39a9a5e7869c2c5d7c498187869, 0] [0xfff2670b033de8de0c20000b03050006, 0xf81db9e4f4bfb726a08000444038b120, 0x155e8ed1cddbde91111e8e2084c20891, 0x5121fa363d5745e3570a303a3d4744c2, 0x6be1c39a9a5e7869c2c5d7c498187869] (by decide +kernel) (by decide +kernel) (by unfold CoreSearch.Rep; decide +kernel) caseReplay4)

set_option maxHeartbeats 0 in
set_option maxRecDepth 64000 in
theorem fgMinor6 : Low 8 (fun x => sixTarget (FirstGate.glue 2 1 3 x)) := (CoreSearch.lower (n := 7) (f := (fun x => sixTarget (FirstGate.glue 2 1 3 x))) [0xfd6df3afc3cffd790029700b80c61021, 0x370e30cf1e4ad60bb6dfa4131a6ede0b, 0, 0xd3936c707f37baa79d0a041257260a85, 0x64f4addeb279c9cf46d285c43239894a, 0x1b7e56651d9bf6560b5401640d198456] [0xfd6df3afc3cffd790029700b80c61021, 0x370e30cf1e4ad60bb6dfa4131a6ede0b, 0xd3936c707f37baa79d0a041257260a85, 0x64f4addeb279c9cf46d285c43239894a, 0x1b7e56651d9bf6560b5401640d198456] (by decide +kernel) (by decide +kernel) (by unfold CoreSearch.Rep; decide +kernel) caseReplay5)

set_option maxHeartbeats 0 in
set_option maxRecDepth 64000 in
theorem fgMinor7 : Low 8 (fun x => sixTarget (FirstGate.glue 1 3 2 x)) := (CoreSearch.lower (n := 7) (f := (fun x => sixTarget (FirstGate.glue 1 3 2 x))) [0xebf71ded9cf7edf122d1118584662091, 0, 0xcf8c3abd65ddb4e66b0eee89619590e6, 0x169ce39a736ffa2f00a06008314a8229, 0x6573b6fcba99659f5c2a84701a99050e, 0xda9ff9134f33de5c985e90524e310c54] [0xebf71ded9cf7edf122d1118584662091, 0xcf8c3abd65ddb4e66b0eee89619590e6, 0x169ce39a736ffa2f00a06008314a8229, 0x6573b6fcba99659f5c2a84701a99050e, 0xda9ff9134f33de5c985e90524e310c54] (by decide +kernel) (by decide +kernel) (by unfold CoreSearch.Rep; decide +kernel) caseReplay6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 64000 in
theorem fgMinor8 : Low 8 (fun x => sixTarget (FirstGate.glue 4 1 2 x)) := (CoreSearch.lower (n := 7) (f := (fun x => sixTarget (FirstGate.glue 4 1 2 x))) [0x69b7d9aff436c7fb4205a18e6024c61b, 0xf7ecf657efdf3e9505601651855a2084, 0x9dd32dfe59e9d96b9094282210a15961, 0x36dbda9ad6ac28fe22f34060f28c08fe, 0, 0xba5a1f39eb15eb265e0b18387b15ab22] [0x69b7d9aff436c7fb4205a18e6024c61b, 0xf7ecf657efdf3e9505601651855a2084, 0x9dd32dfe59e9d96b9094282210a15961, 0x36dbda9ad6ac28fe22f34060f28c08fe, 0xba5a1f39eb15eb265e0b18387b15ab22] (by decide +kernel) (by decide +kernel) (by unfold CoreSearch.Rep; decide +kernel) caseReplay7)

set_option maxHeartbeats 0 in
set_option maxRecDepth 64000 in
theorem fgMinor9 : Low 8 (fun x => sixTarget (FirstGate.glue 1 4 3 x)) := (two 3 (good_at 20 5 0 (by decide +kernel)) (good_at 20 5 0 (by decide +kernel)) (CoreSearch.lower (n := 5) (f := (rs 3 false (fun x => sixTarget (FirstGate.glue 1 4 3 x)))) [0xefdfeffffbffedf50420000002820160, 0, 0x5fba72ebb71e96ab0941850aed2c4683, 0, 0x8ac0e0b74aff699128c6f75be540d893, 0x3fffbf0c0dd63a4fe24a643e6000980f] [0xefdfeffffbffedf50420000002820160, 0x5fba72ebb71e96ab0941850aed2c4683, 0x8ac0e0b74aff699128c6f75be540d893, 0x3fffbf0c0dd63a4fe24a643e6000980f] (by decide +kernel) (by decide +kernel) (by unfold CoreSearch.Rep; decide +kernel) caseReplay8) (CoreSearch.lower (n := 5) (f := (rs 3 true (fun x => sixTarget (FirstGate.glue 1 4 3 x)))) [0x9eaf9bdc4bff9d384c4c400141002128, 0, 0x7bdaed1eefd9e4e321030a2820040482, 0, 0x4eefd44ce4d749d1928021429ef39a51, 0xfd9ffff33531ba0f0080000282839a01] [0x9eaf9bdc4bff9d384c4c400141002128, 0x7bdaed1eefd9e4e321030a2820040482, 0x4eefd44ce4d749d1928021429ef39a51, 0xfd9ffff33531ba0f0080000282839a01] (by decide +kernel) (by decide +kernel) (by unfold CoreSearch.Rep; decide +kernel) caseReplay9))

set_option maxHeartbeats 0 in
set_option maxRecDepth 64000 in
theorem fgMinor10 : Low 8 (fun x => sixTarget (FirstGate.glue 1 5 2 x)) := (CoreSearch.lower (n := 7) (f := (fun x => sixTarget (FirstGate.glue 1 5 2 x))) [0x7c26dfc911ff953b302412e10198910a, 0, 0x8a4d621b669f69550221419126852115, 0x41db78678e3efa9232122c22063ed292, 0x189bbf8a3cebe64b8c8b851e38636641, 0xefff0074eb4ddfe4cc488004c8400060] [0x7c26dfc911ff953b302412e10198910a, 0x8a4d621b669f69550221419126852115, 0x41db78678e3efa9232122c22063ed292, 0x189bbf8a3cebe64b8c8b851e38636641, 0xefff0074eb4ddfe4cc488004c8400060] (by decide +kernel) (by decide +kernel) (by unfold CoreSearch.Rep; decide +kernel) caseReplay10)

set_option maxHeartbeats 0 in
set_option maxRecDepth 64000 in
theorem fgMinor11 : Low 8 (fun x => sixTarget (FirstGate.glue 3 2 3 x)) := (CoreSearch.lower (n := 7) (f := (fun x => sixTarget (FirstGate.glue 3 2 3 x))) [0xacc389ba2f5fbe5d8cc98408264a004d, 0xff3cf7fdf4abf5b379102511e0a22411, 0xb3859a1d927f7a9ac2c49a10907d0a9a, 0, 0x3fc3b377f911d7cc2312586559119780, 0xc9bf7eca57e5eb2702094a8a17058326] [0xacc389ba2f5fbe5d8cc98408264a004d, 0xff3cf7fdf4abf5b379102511e0a22411, 0xb3859a1d927f7a9ac2c49a10907d0a9a, 0x3fc3b377f911d7cc2312586559119780, 0xc9bf7eca57e5eb2702094a8a17058326] (by decide +kernel) (by decide +kernel) (by unfold CoreSearch.Rep; decide +kernel) caseReplay11)

set_option maxHeartbeats 0 in
set_option maxRecDepth 64000 in
theorem fgMinor12 : Low 8 (fun x => sixTarget (FirstGate.glue 4 2 3 x)) := (CoreSearch.lower (n := 7) (f := (fun x => sixTarget (FirstGate.glue 4 2 3 x))) [0xfedae8f3fdbf25eb0c00000220a12000, 0xb93db76d6248ff9cb3b9106c4048d788, 0xf0093b2fb3b2b3953d0e2b0f7bb33395, 0xc77e740ba7764b2cd31e6d8584164b2c, 0, 0x21bf9f3f97dcda550086d961835c8855] [0xfedae8f3fdbf25eb0c00000220a12000, 0xb93db76d6248ff9cb3b9106c4048d788, 0xf0093b2fb3b2b3953d0e2b0f7bb33395, 0xc77e740ba7764b2cd31e6d8584164b2c, 0x21bf9f3f97dcda550086d961835c8855] (by decide +kernel) (by decide +kernel) (by unfold CoreSearch.Rep; decide +kernel) caseReplay12)

set_option maxHeartbeats 0 in
set_option maxRecDepth 64000 in
theorem fgMinor13 : Low 8 (fun x => sixTarget (FirstGate.glue 5 2 3 x)) := (CoreSearch.lower (n := 7) (f := (fun x => sixTarget (FirstGate.glue 5 2 3 x))) [0xead00b79a7cbb7e6a000092086890046, 0xd5ba97f2693edd3e07bc00982936c928, 0x5c55e88f3e2b1e695134509f323b1668, 0x1d6f766d74d7e45d386513cd64d2041d, 0xf675ee86dae3fb8946c8a6025840c381, 0] [0xead00b79a7cbb7e6a000092086890046, 0xd5ba97f2693edd3e07bc00982936c928, 0x5c55e88f3e2b1e695134509f323b1668, 0x1d6f766d74d7e45d386513cd64d2041d, 0xf675ee86dae3fb8946c8a6025840c381] (by decide +kernel) (by decide +kernel) (by unfold CoreSearch.Rep; decide +kernel) caseReplay13)

set_option maxHeartbeats 0 in
set_option maxRecDepth 64000 in
theorem fgMinor14 : Low 8 (fun x => sixTarget (FirstGate.glue 3 5 2 x)) := (CoreSearch.lower (n := 7) (f := (fun x => sixTarget (FirstGate.glue 3 5 2 x))) [0xb6647ed4feaefc2108004a1034ac3c01, 0xca9b97f168c5a75f0a011b400880a51e, 0x973be63ff7de8b8670982507d34e8a86, 0, 0x756f7a6b9b3857f2252e20600b104370, 0x5ddee5de155338fd54c2c498045310e1] [0xb6647ed4feaefc2108004a1034ac3c01, 0xca9b97f168c5a75f0a011b400880a51e, 0x973be63ff7de8b8670982507d34e8a86, 0x756f7a6b9b3857f2252e20600b104370, 0x5ddee5de155338fd54c2c498045310e1] (by decide +kernel) (by decide +kernel) (by unfold CoreSearch.Rep; decide +kernel) caseReplay14)

set_option maxHeartbeats 0 in
set_option maxRecDepth 64000 in
theorem fgMinor15 : Low 8 (fun x => sixTarget (FirstGate.glue 4 5 2 x)) := (CoreSearch.lower (n := 7) (f := (fun x => sixTarget (FirstGate.glue 4 5 2 x))) [0x7377ffd2c7e7fc7b2a4142d202e61429, 0x4cfbe9ed915e6b999c72a274915c4b19, 0x85be7dffe9f27f0780aa7da1c9822706, 0xa9c3d67efc68deac8b81325af4608aac, 0, 0xfffd9eef3e9df3fe51148c0d2c1800d2] [0x7377ffd2c7e7fc7b2a4142d202e61429, 0x4cfbe9ed915e6b999c72a274915c4b19, 0x85be7dffe9f27f0780aa7da1c9822706, 0xa9c3d67efc68deac8b81325af4608aac, 0xfffd9eef3e9df3fe51148c0d2c1800d2] (by decide +kernel) (by decide +kernel) (by unfold CoreSearch.Rep; decide +kernel) caseReplay15)

set_option maxHeartbeats 0 in
set_option maxRecDepth 64000 in
theorem fgDomain0101 : FirstGate.DomainLow 8 sixTarget 0 1 false true := CoreSearch.domain_lower (n := 7) (f := sixTarget) 0 1 false true [0x89c83224bbbc9850884012240000084, 0xfcdfdb7fefffddffd8fc9b7eeb0119bd, 0x7fb3acfdd5eeb70b1622a8d50402a703, 0x9bf874f23ddc727506b4c4723d0c7255, 0x63733ec1b978bace21133681b938984a, 0xd7cd519eb7f74e72454b508896504e62] [0x89c83224bbbc9850884012240000084, 0xfcdfdb7fefffddffd8fc9b7eeb0119bd, 0x7fb3acfdd5eeb70b1622a8d50402a703, 0x9bf874f23ddc727506b4c4723d0c7255, 0x63733ec1b978bace21133681b938984a, 0xd7cd519eb7f74e72454b508896504e62] (by decide +kernel) (by decide +kernel) (by unfold CoreSearch.Rep; decide +kernel) (by decide +kernel) caseReplay16

set_option maxHeartbeats 0 in
set_option maxRecDepth 64000 in
theorem fgDomain0110 : FirstGate.DomainLow 8 sixTarget 0 1 true false := CoreSearch.domain_lower (n := 7) (f := sixTarget) 0 1 true false [0xffdffb97fffffb7fc58df295f142093e, 0x5901421447fd002e840140044040000e, 0xab3fafe8de7ee7920a220fa88e04e610, 0xf7ee6c7a6ccdcd95f5666c7268c9c985, 0x26e1d56ba7e3fcc92240014a068034c1, 0x531489f5379a47651372897137984761] [0xffdffb97fffffb7fc58df295f142093e, 0x5901421447fd002e840140044040000e, 0xab3fafe8de7ee7920a220fa88e04e610, 0xf7ee6c7a6ccdcd95f5666c7268c9c985, 0x26e1d56ba7e3fcc92240014a068034c1, 0x531489f5379a47651372897137984761] (by decide +kernel) (by decide +kernel) (by unfold CoreSearch.Rep; decide +kernel) (by decide +kernel) caseReplay17

set_option maxHeartbeats 0 in
set_option maxRecDepth 64000 in
theorem fgDomain0200 : FirstGate.DomainLow 8 sixTarget 0 2 false false := CoreSearch.domain_lower (n := 7) (f := sixTarget) 0 2 false false [0xf134a0cd296c2bca810420c120442a08, 0x49e86fdee59f353f40ac6e9ca185113e, 0xe4b5f301292d42124c851301082d401, 0xce8b3837d65bf0dc1ba33817424b70cc, 0xbe7fdb2dfa7ddfe838738b2cc03185e0, 0xd7c2b5dbc59fa2b7d712954bc41aa2b3] [0xf134a0cd296c2bca810420c120442a08, 0x49e86fdee59f353f40ac6e9ca185113e, 0xe4b5f301292d42124c851301082d401, 0xce8b3837d65bf0dc1ba33817424b70cc, 0xbe7fdb2dfa7ddfe838738b2cc03185e0, 0xd7c2b5dbc59fa2b7d712954bc41aa2b3] (by decide +kernel) (by decide +kernel) (by unfold CoreSearch.Rep; decide +kernel) (by decide +kernel) caseReplay18

set_option maxHeartbeats 0 in
set_option maxRecDepth 64000 in
theorem fgDomain0201 : FirstGate.DomainLow 8 sixTarget 0 2 false true := CoreSearch.domain_lower (n := 7) (f := sixTarget) 0 2 false true [0x980a08911dbce640000000910000020, 0x377a1d67677d9b99113e952262218b89, 0xffeff7fddbffff7785f5f1fdd8081e76, 0xe9ddcb1eedf46ccb68b68b04cc446cc9, 0xf6af66f2cdeb712bb20a26d20483710b, 0x7cd11d96b7b7b0dcecc10c96a617b054] [0x980a08911dbce640000000910000020, 0x377a1d67677d9b99113e952262218b89, 0xffeff7fddbffff7785f5f1fdd8081e76, 0xe9ddcb1eedf46ccb68b68b04cc446cc9, 0xf6af66f2cdeb712bb20a26d20483710b, 0x7cd11d96b7b7b0dcecc10c96a617b054] (by decide +kernel) (by decide +kernel) (by unfold CoreSearch.Rep; decide +kernel) (by decide +kernel) caseReplay19

set_option maxHeartbeats 0 in
set_option maxRecDepth 64000 in
theorem fgDomain0210 : FirstGate.DomainLow 8 sixTarget 0 2 true false := CoreSearch.domain_lower (n := 7) (f := sixTarget) 0 2 true false [0xdfff7affffffffd59bef3a5dd0a00ed1, 0x6ef9ed1bafcc662f0cd0ec0aafc46427, 0x908e1045cdf7c4908000004500000080, 0xbc34957a9ba7293b34e1913a91a3291b, 0xc75223a63f7a9967601001a22f429126, 0x392bcf187af873ba200b47107a685338] [0xdfff7affffffffd59bef3a5dd0a00ed1, 0x6ef9ed1bafcc662f0cd0ec0aafc46427, 0x908e1045cdf7c4908000004500000080, 0xbc34957a9ba7293b34e1913a91a3291b, 0xc75223a63f7a9967601001a22f429126, 0x392bcf187af873ba200b47107a685338] (by decide +kernel) (by decide +kernel) (by unfold CoreSearch.Rep; decide +kernel) (by decide +kernel) caseReplay20

set_option maxHeartbeats 0 in
set_option maxRecDepth 64000 in
theorem fgDomain0211 : FirstGate.DomainLow 8 sixTarget 0 2 true true := CoreSearch.domain_lower (n := 7) (f := sixTarget) 0 2 true true [0xbd4fbfaff7eb7f0cb804bda3b1a23f08, 0x72208e5fdaa6a2ee700086539226202c, 0x5ff377fe7e5dcaff47fb537c6e5dc2f7, 0xad96694b3d3e185d1c0668431d2e185c, 0xc3fd403fed17f59101e9000c40118081, 0xe3a8f8cd9ef911e28f4c688c0cd911c2] [0xbd4fbfaff7eb7f0cb804bda3b1a23f08, 0x72208e5fdaa6a2ee700086539226202c, 0x5ff377fe7e5dcaff47fb537c6e5dc2f7, 0xad96694b3d3e185d1c0668431d2e185c, 0xc3fd403fed17f59101e9000c40118081, 0xe3a8f8cd9ef911e28f4c688c0cd911c2] (by decide +kernel) (by decide +kernel) (by unfold CoreSearch.Rep; decide +kernel) (by decide +kernel) caseReplay21

set_option maxHeartbeats 0 in
set_option maxRecDepth 64000 in
theorem fgDomain0301 : FirstGate.DomainLow 8 sixTarget 0 3 false true := CoreSearch.domain_lower (n := 7) (f := sixTarget) 0 3 false true [0xf02b8638076fec22a008802806000c02, 0x6fd5f9bea8f3a7dca651b9b22841a4cc, 0x5eff21c5fafe16fb54e72005f02202b9, 0xf36ffe7f577ffd6fe42ffe7c46095d6b, 0xb2fc2ef37dfcfb5112900ed31884b350, 0x6d86dbce9457c38f491643ce9416c307] [0xf02b8638076fec22a008802806000c02, 0x6fd5f9bea8f3a7dca651b9b22841a4cc, 0x5eff21c5fafe16fb54e72005f02202b9, 0xf36ffe7f577ffd6fe42ffe7c46095d6b, 0xb2fc2ef37dfcfb5112900ed31884b350, 0x6d86dbce9457c38f491643ce9416c307] (by decide +kernel) (by decide +kernel) (by unfold CoreSearch.Rep; decide +kernel) (by decide +kernel) caseReplay22

set_option maxHeartbeats 0 in
set_option maxRecDepth 64000 in
theorem fgFree0401 : FirstGate.FreeLow 9 sixTarget 0 4 false true := (FirstGate.free_two 0 4 1 false true (by decide) (by decide) (good_at 5 13 0 (by decide +kernel)) (good_at 5 5 0 (by decide +kernel)) (FirstGate.free_two 0 4 5 false true (by decide) (by decide) (good_at 5 13 0 (by decide +kernel)) (good_at 5 5 0 (by decide +kernel)) (FirstGate.free_one 0 4 2 false true true (by decide) (by decide) (good_at 9 9 0 (by decide +kernel)) (CoreSearch.free_lower (n := 3) (f := (rs 2 true (rs 5 false (rs 1 false sixTarget)))) 0 4 false true 0x40614061406180c12091209120914121 [0xd7f3d7f3d7f3afeb2091209120914121, 0, 0, 0xebedebedebedd7dd1228122812282444, 0xbf9ebf9ebf9e7f3e4106410641068212, 0] [0xd7f3d7f3d7f3afeb2091209120914121, 0xebedebedebedd7dd1228122812282444, 0xbf9ebf9ebf9e7f3e4106410641068212, 0x40614061406180c12091209120914121] (by decide +kernel) (by decide +kernel) (by unfold CoreSearch.Rep; decide +kernel) (by unfold CoreSearch.Rep; decide +kernel) (by decide +kernel) caseReplay33)) (FirstGate.free_one 0 4 3 false true true (by decide) (by decide) (good_at 20 5 0 (by decide +kernel)) (CoreSearch.free_lower (n := 3) (f := (rs 3 true (rs 5 true (rs 1 false sixTarget)))) 0 4 false true 0x21032103210342031052105210522086 [0xeddbeddbeddbdbb71052105210522086, 0, 0x7be77be77be777db80a180a180a18141, 0, 0xdefcdefcdefcbdfc280c280c280c5028, 0] [0xeddbeddbeddbdbb71052105210522086, 0x7be77be77be777db80a180a180a18141, 0xdefcdefcdefcbdfc280c280c280c5028, 0x21032103210342031052105210522086] (by decide +kernel) (by decide +kernel) (by unfold CoreSearch.Rep; decide +kernel) (by unfold CoreSearch.Rep; decide +kernel) (by decide +kernel) caseReplay34))) (FirstGate.free_two 0 4 3 false true (by decide) (by decide) (good_at 32 5 0 (by decide +kernel)) (good_at 32 5 0 (by decide +kernel)) (FirstGate.free_one 0 4 5 false true false (by decide) (by decide) (good_at 1 5 0 (by decide +kernel)) (CoreSearch.free_lower (n := 3) (f := (rs 5 false (rs 3 false (rs 1 true sixTarget)))) 0 4 false true 0x21032103210342031052105210522086 [0xeddbeddbeddbdbb71052105210522086, 0, 0x7be77be77be777db80a180a180a18141, 0, 0xdefcdefcdefcbdfc280c280c280c5028, 0] [0xeddbeddbeddbdbb71052105210522086, 0x7be77be77be777db80a180a180a18141, 0xdefcdefcdefcbdfc280c280c280c5028, 0x21032103210342031052105210522086] (by decide +kernel) (by decide +kernel) (by unfold CoreSearch.Rep; decide +kernel) (by unfold CoreSearch.Rep; decide +kernel) (by decide +kernel) caseReplay34)) (FirstGate.free_one 0 4 5 false true false (by decide) (by decide) (good_at 0 5 0 (by decide +kernel)) (CoreSearch.free_lower (n := 3) (f := (rs 5 false (rs 3 true (rs 1 true sixTarget)))) 0 4 false true 0x21032103210342031052105210522086 [0xeddbeddbeddbdbb71052105210522086, 0, 0x7be77be77be777db80a180a180a18141, 0, 0xdefcdefcdefcbdfc280c280c280c5028, 0] [0xeddbeddbeddbdbb71052105210522086, 0x7be77be77be777db80a180a180a18141, 0xdefcdefcdefcbdfc280c280c280c5028, 0x21032103210342031052105210522086] (by decide +kernel) (by decide +kernel) (by unfold CoreSearch.Rep; decide +kernel) (by unfold CoreSearch.Rep; decide +kernel) (by decide +kernel) caseReplay34))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 64000 in
theorem fgDomain0411 : FirstGate.DomainLow 8 sixTarget 0 4 true true := CoreSearch.domain_lower (n := 7) (f := sixTarget) 0 4 true true [0xdff6d1ffdf9ddfcec0e211fccb1ccb06, 0x6c08bb71eefb13b02c10bb01e4d81390, 0x236b2c2dff7e6443824904241a240442, 0x106707c1f1d4f139000603c0e1d0f129, 0xf9ddff87b7e3bcfd3f1dee0334e334f9, 0x77208edb7ca1473f5fa08cdb1421443d] [0xdff6d1ffdf9ddfcec0e211fccb1ccb06, 0x6c08bb71eefb13b02c10bb01e4d81390, 0x236b2c2dff7e6443824904241a240442, 0x106707c1f1d4f139000603c0e1d0f129, 0xf9ddff87b7e3bcfd3f1dee0334e334f9, 0x77208edb7ca1473f5fa08cdb1421443d] (by decide +kernel) (by decide +kernel) (by unfold CoreSearch.Rep; decide +kernel) (by decide +kernel) caseReplay23

set_option maxHeartbeats 0 in
set_option maxRecDepth 64000 in
theorem fgDomain0510 : FirstGate.DomainLow 8 sixTarget 0 5 true false := CoreSearch.domain_lower (n := 7) (f := sixTarget) 0 5 true false [0xbdfffceeeffffd3f3dbfdc4a21003937, 0xd39d1f269ece839ed49919249aca839a, 0x47b1c3db9ff506f903204293968504a9, 0x9ce78c9d5b599b49840d8c9c5b591b48, 0x6a4a6b357dfafec2004023254c40c640, 0x913694402f2f51242002844021001004] [0xbdfffceeeffffd3f3dbfdc4a21003937, 0xd39d1f269ece839ed49919249aca839a, 0x47b1c3db9ff506f903204293968504a9, 0x9ce78c9d5b599b49840d8c9c5b591b48, 0x6a4a6b357dfafec2004023254c40c640, 0x913694402f2f51242002844021001004] (by decide +kernel) (by decide +kernel) (by unfold CoreSearch.Rep; decide +kernel) (by decide +kernel) caseReplay24

set_option maxHeartbeats 0 in
set_option maxRecDepth 64000 in
theorem fgDomain1201 : FirstGate.DomainLow 8 sixTarget 1 2 false true := CoreSearch.domain_lower (n := 7) (f := sixTarget) 1 2 false true [0x3dd5a897bfe67b6725c420132c441826, 0xb6285541c7df81181800504082800110, 0xfeefd77fdfffedfc9a1bd75ddbc16578, 0x4fc31aaec496f4b6dec31aa6c492f096, 0x41f6ffa82fb9f6c300308da8010086c1, 0xc66b8970756aae1ec4638920750aae0e] [0x3dd5a897bfe67b6725c420132c441826, 0xb6285541c7df81181800504082800110, 0xfeefd77fdfffedfc9a1bd75ddbc16578, 0x4fc31aaec496f4b6dec31aa6c492f096, 0x41f6ffa82fb9f6c300308da8010086c1, 0xc66b8970756aae1ec4638920750aae0e] (by decide +kernel) (by decide +kernel) (by unfold CoreSearch.Rep; decide +kernel) (by decide +kernel) caseReplay25

set_option maxHeartbeats 0 in
set_option maxRecDepth 64000 in
theorem fgDomain1210 : FirstGate.DomainLow 8 sixTarget 1 2 true false := CoreSearch.domain_lower (n := 7) (f := sixTarget) 1 2 true false [0x2f29cbb65ffecd5a0829018245000d52, 0xffff75efbfffb6bfdfd975ef3a8334af, 0xd8de114b1bbf30a110900048180000a0, 0x732ae599eb696794a38ac599eb296790, 0xf7deee7542d8ffc3e546ee350298b201, 0x493136b8e7c5ea3d44603230c584ca1d] [0x2f29cbb65ffecd5a0829018245000d52, 0xffff75efbfffb6bfdfd975ef3a8334af, 0xd8de114b1bbf30a110900048180000a0, 0x732ae599eb696794a38ac599eb296790, 0xf7deee7542d8ffc3e546ee350298b201, 0x493136b8e7c5ea3d44603230c584ca1d] (by decide +kernel) (by decide +kernel) (by unfold CoreSearch.Rep; decide +kernel) (by decide +kernel) caseReplay26

set_option maxHeartbeats 0 in
set_option maxRecDepth 64000 in
theorem fgDomain1311 : FirstGate.DomainLow 8 sixTarget 1 3 true true := CoreSearch.domain_lower (n := 7) (f := sixTarget) 1 3 true true [0xaa624bbf7f75b6c88822491011702640, 0xfdfdc753fcfaf1eff5bdc713bceaf0ed, 0x3395fbc86febdc15208192c840011805, 0xc76bbdeed3f75f722aebb9eed3775f52, 0x44eb43677ac4bd9504c242626884198, 0xddb92cc5fadb2b2e5d102cc56a980b2a] [0xaa624bbf7f75b6c88822491011702640, 0xfdfdc753fcfaf1eff5bdc713bceaf0ed, 0x3395fbc86febdc15208192c840011805, 0xc76bbdeed3f75f722aebb9eed3775f52, 0x44eb43677ac4bd9504c242626884198, 0xddb92cc5fadb2b2e5d102cc56a980b2a] (by decide +kernel) (by decide +kernel) (by unfold CoreSearch.Rep; decide +kernel) (by decide +kernel) caseReplay27

set_option maxHeartbeats 0 in
set_option maxRecDepth 64000 in
theorem fgDomain1500 : FirstGate.DomainLow 8 sixTarget 1 5 false false := CoreSearch.domain_lower (n := 7) (f := sixTarget) 1 5 false false [0xf58e7fa3bffff7a7c40e0d80a0406325, 0xa202615c0986c1102002611c0986c10, 0x7b778ffee61f8cfb39b10a76640c84eb, 0xf679d5cb6d17c65c4469d58b4913c654, 0xbefdf85d59fb7bde3bd0f04d0023189a, 0xd1cec1620a2601e49d96c1620a2601c4] [0xf58e7fa3bffff7a7c40e0d80a0406325, 0xa202615c0986c1102002611c0986c10, 0x7b778ffee61f8cfb39b10a76640c84eb, 0xf679d5cb6d17c65c4469d58b4913c654, 0xbefdf85d59fb7bde3bd0f04d0023189a, 0xd1cec1620a2601e49d96c1620a2601c4] (by decide +kernel) (by decide +kernel) (by unfold CoreSearch.Rep; decide +kernel) (by decide +kernel) caseReplay28

set_option maxHeartbeats 0 in
set_option maxRecDepth 64000 in
theorem fgDomain2301 : FirstGate.DomainLow 8 sixTarget 2 3 false true := CoreSearch.domain_lower (n := 7) (f := sixTarget) 2 3 false true [0xf77fce7ce6fa7fc2e39f465480821d80, 0x6794e1af8dac8deb5608c1af84a884ea, 0x2c0a330657e5b0540000310241002050, 0xef8f3f8fffffb1fde4bd3f0fff85b1dd, 0xda619cdb37dbc697186088893608c207, 0x59f477e1bf3d692b99b036e03b116923] [0xf77fce7ce6fa7fc2e39f465480821d80, 0x6794e1af8dac8deb5608c1af84a884ea, 0x2c0a330657e5b0540000310241002050, 0xef8f3f8fffffb1fde4bd3f0fff85b1dd, 0xda619cdb37dbc697186088893608c207, 0x59f477e1bf3d692b99b036e03b116923] (by decide +kernel) (by decide +kernel) (by unfold CoreSearch.Rep; decide +kernel) (by decide +kernel) caseReplay29

set_option maxHeartbeats 0 in
set_option maxRecDepth 64000 in
theorem fgDomain2401 : FirstGate.DomainLow 8 sixTarget 2 4 false true := CoreSearch.domain_lower (n := 7) (f := sixTarget) 2 4 false true [0xce1506c57ff38bcf820106802202814b, 0x6be2eabcef9f34d3516242b4cb0514d1, 0x3108912a177cc4342408900810000024, 0xb8eb7d96a6cafe6099a52d96268ade40, 0xf59f9fffd7ffefbc75ee997fd5902eb4, 0xcaeeed31bdacb8eb0844ed21bdaca8aa] [0xce1506c57ff38bcf820106802202814b, 0x6be2eabcef9f34d3516242b4cb0514d1, 0x3108912a177cc4342408900810000024, 0xb8eb7d96a6cafe6099a52d96268ade40, 0xf59f9fffd7ffefbc75ee997fd5902eb4, 0xcaeeed31bdacb8eb0844ed21bdaca8aa] (by decide +kernel) (by decide +kernel) (by unfold CoreSearch.Rep; decide +kernel) (by decide +kernel) caseReplay30

set_option maxHeartbeats 0 in
set_option maxRecDepth 64000 in
theorem fgDomain2510 : FirstGate.DomainLow 8 sixTarget 2 5 true false := CoreSearch.domain_lower (n := 7) (f := sixTarget) 2 5 true false [0xfcb79bd48fbe4dbea8159a808612003a, 0x61ee5d1b6fd99372700e59130e891370, 0x2ffeedfff7ffbadf0ee265fde104aacf, 0x271f5e216e727918061d56216a32790, 0xffc9722bddedfd251788200a59805d05, 0xa0e244c2772aa480400244c2100a800] [0xfcb79bd48fbe4dbea8159a808612003a, 0x61ee5d1b6fd99372700e59130e891370, 0x2ffeedfff7ffbadf0ee265fde104aacf, 0x271f5e216e727918061d56216a32790, 0xffc9722bddedfd251788200a59805d05, 0xa0e244c2772aa480400244c2100a800] (by decide +kernel) (by decide +kernel) (by unfold CoreSearch.Rep; decide +kernel) (by decide +kernel) caseReplay31

set_option maxHeartbeats 0 in
set_option maxRecDepth 64000 in
theorem fgDomain3411 : FirstGate.DomainLow 8 sixTarget 3 4 true true := CoreSearch.domain_lower (n := 7) (f := sixTarget) 3 4 true true [0x179dd2943debe7991448929020000098, 0x6bda3b1df7d751c609f2111da5d051c2, 0xf92d05f7ff3fa82ee90505445a2c2826, 0xf16ffffe6ed3b8fbfdefffb66453b8db, 0xaeb6dd6bbffccf7502b0486b9ffcc765, 0xe74e6e8b728eb5f2361c6e8b528ea530] [0x179dd2943debe7991448929020000098, 0x6bda3b1df7d751c609f2111da5d051c2, 0xf92d05f7ff3fa82ee90505445a2c2826, 0xf16ffffe6ed3b8fbfdefffb66453b8db, 0xaeb6dd6bbffccf7502b0486b9ffcc765, 0xe74e6e8b728eb5f2361c6e8b528ea530] (by decide +kernel) (by decide +kernel) (by unfold CoreSearch.Rep; decide +kernel) (by decide +kernel) caseReplay32

theorem fgPair01 : FirstGate.PairLow 9 sixTarget 0 1 ∨ ∀ ci cj, FirstGate.PairKill 8 sixTarget 0 1 ci cj := by
  right
  intro a b
  cases a <;> cases b
  · exact (Or.inr (Or.inr (Or.inl fgMinor0)))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl fgDomain0101)))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl fgDomain0110)))))
  · exact (Or.inr (Or.inr (Or.inl fgMinor0)))

theorem fgPair02 : FirstGate.PairLow 9 sixTarget 0 2 ∨ ∀ ci cj, FirstGate.PairKill 8 sixTarget 0 2 ci cj := by
  right
  intro a b
  cases a <;> cases b
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl fgDomain0200)))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl fgDomain0201)))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl fgDomain0210)))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl fgDomain0211)))))

theorem fgPair03 : FirstGate.PairLow 9 sixTarget 0 3 ∨ ∀ ci cj, FirstGate.PairKill 8 sixTarget 0 3 ci cj := by
  right
  intro a b
  cases a <;> cases b
  · exact (Or.inr (Or.inl fgMinor1))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl fgDomain0301)))))
  · exact (Or.inr (Or.inl fgMinor1))
  · exact (Or.inr (Or.inr (Or.inr (Or.inl fgMinor2))))

theorem fgPair04 : FirstGate.PairLow 9 sixTarget 0 4 ∨ ∀ ci cj, FirstGate.PairKill 8 sixTarget 0 4 ci cj := by
  right
  intro a b
  cases a <;> cases b
  · exact (Or.inr (Or.inl fgMinor3))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr fgFree0401)))))
  · exact (Or.inr (Or.inl fgMinor3))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl fgDomain0411)))))

theorem fgPair05 : FirstGate.PairLow 9 sixTarget 0 5 ∨ ∀ ci cj, FirstGate.PairKill 8 sixTarget 0 5 ci cj := by
  right
  intro a b
  cases a <;> cases b
  · exact (Or.inr (Or.inr (Or.inl fgMinor4)))
  · exact (Or.inr (Or.inl fgMinor5))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl fgDomain0510)))))
  · exact (Or.inr (Or.inl fgMinor5))

theorem fgPair12 : FirstGate.PairLow 9 sixTarget 1 2 ∨ ∀ ci cj, FirstGate.PairKill 8 sixTarget 1 2 ci cj := by
  right
  intro a b
  cases a <;> cases b
  · exact (Or.inr (Or.inr (Or.inr (Or.inl fgMinor6))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl fgDomain1201)))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl fgDomain1210)))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inl fgMinor6))))

theorem fgPair13 : FirstGate.PairLow 9 sixTarget 1 3 ∨ ∀ ci cj, FirstGate.PairKill 8 sixTarget 1 3 ci cj := by
  right
  intro a b
  cases a <;> cases b
  · exact (Or.inr (Or.inl fgMinor1))
  · exact (Or.inr (Or.inr (Or.inl fgMinor7)))
  · exact (Or.inr (Or.inl fgMinor1))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl fgDomain1311)))))

theorem fgPair14 : FirstGate.PairLow 9 sixTarget 1 4 ∨ ∀ ci cj, FirstGate.PairKill 8 sixTarget 1 4 ci cj := by
  right
  intro a b
  cases a <;> cases b
  · exact (Or.inr (Or.inl fgMinor3))
  · exact (Or.inr (Or.inr (Or.inr (Or.inl fgMinor8))))
  · exact (Or.inr (Or.inl fgMinor3))
  · exact (Or.inr (Or.inr (Or.inl fgMinor9)))

theorem fgPair15 : FirstGate.PairLow 9 sixTarget 1 5 ∨ ∀ ci cj, FirstGate.PairKill 8 sixTarget 1 5 ci cj := by
  right
  intro a b
  cases a <;> cases b
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl fgDomain1500)))))
  · exact (Or.inr (Or.inl fgMinor5))
  · exact (Or.inr (Or.inr (Or.inl fgMinor10)))
  · exact (Or.inr (Or.inl fgMinor5))

theorem fgPair23 : FirstGate.PairLow 9 sixTarget 2 3 ∨ ∀ ci cj, FirstGate.PairKill 8 sixTarget 2 3 ci cj := by
  right
  intro a b
  cases a <;> cases b
  · exact (Or.inr (Or.inl fgMinor1))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl fgDomain2301)))))
  · exact (Or.inr (Or.inl fgMinor1))
  · exact (Or.inr (Or.inr (Or.inr (Or.inl fgMinor11))))

theorem fgPair24 : FirstGate.PairLow 9 sixTarget 2 4 ∨ ∀ ci cj, FirstGate.PairKill 8 sixTarget 2 4 ci cj := by
  right
  intro a b
  cases a <;> cases b
  · exact (Or.inr (Or.inl fgMinor3))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl fgDomain2401)))))
  · exact (Or.inr (Or.inl fgMinor3))
  · exact (Or.inr (Or.inr (Or.inr (Or.inl fgMinor12))))

theorem fgPair25 : FirstGate.PairLow 9 sixTarget 2 5 ∨ ∀ ci cj, FirstGate.PairKill 8 sixTarget 2 5 ci cj := by
  right
  intro a b
  cases a <;> cases b
  · exact (Or.inr (Or.inr (Or.inr (Or.inl fgMinor13))))
  · exact (Or.inr (Or.inl fgMinor5))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl fgDomain2510)))))
  · exact (Or.inr (Or.inl fgMinor5))

theorem fgPair34 : FirstGate.PairLow 9 sixTarget 3 4 ∨ ∀ ci cj, FirstGate.PairKill 8 sixTarget 3 4 ci cj := by
  right
  intro a b
  cases a <;> cases b
  · exact Or.inl fgMinor1
  · exact Or.inl fgMinor1
  · exact (Or.inr (Or.inl fgMinor3))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl fgDomain3411)))))

theorem fgPair35 : FirstGate.PairLow 9 sixTarget 3 5 ∨ ∀ ci cj, FirstGate.PairKill 8 sixTarget 3 5 ci cj := by
  right
  intro a b
  cases a <;> cases b
  · exact Or.inl fgMinor1
  · exact Or.inl fgMinor1
  · exact (Or.inr (Or.inr (Or.inl fgMinor14)))
  · exact (Or.inr (Or.inl fgMinor5))

theorem fgPair45 : FirstGate.PairLow 9 sixTarget 4 5 ∨ ∀ ci cj, FirstGate.PairKill 8 sixTarget 4 5 ci cj := by
  right
  intro a b
  cases a <;> cases b
  · exact Or.inl fgMinor3
  · exact Or.inl fgMinor3
  · exact (Or.inr (Or.inr (Or.inl fgMinor15)))
  · exact (Or.inr (Or.inl fgMinor5))

set_option maxHeartbeats 0 in
set_option maxRecDepth 64000 in
theorem sixLower : Low 10 sixTarget := by
  apply FirstGate.strongLower (n := 8) (by decide) fgBase
  intro i j h
  fin_cases i <;> fin_cases j <;> first | exact False.elim ((by decide : ¬ _) h) | exact fgPair01 | exact fgPair02 | exact fgPair03 | exact fgPair04 | exact fgPair05 | exact fgPair12 | exact fgPair13 | exact fgPair14 | exact fgPair15 | exact fgPair23 | exact fgPair24 | exact fgPair25 | exact fgPair34 | exact fgPair35 | exact fgPair45
end PEqualNP.Outside.L_meta_43584
open PEqualNP.Outside.L_meta_43584 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_43584 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4209680512) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808936 * 2 ^ 32 + 4209680512) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  by_cases enough : 11 ≤ s
  · exact ⟨sixWitness, basis, enough, correct⟩
  obtain ⟨⟨gs,o⟩, fit, size, computes⟩ := h
  have hf : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    exact ⟨by simpa using (fit g hg).1, (fit g hg).2⟩
  change gs.length ≤ s at size
  exact ⟨⟨gs,o⟩, all_not_not sixLower gs o hf (by omega) computes, size, computes⟩
