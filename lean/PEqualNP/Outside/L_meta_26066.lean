import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_26066

open PEqualNP.CircuitLowerBounds

abbrev X := Fin 8 → Bool
abbrev F := X → Bool

def K (b : Bool) : F := fun _ => b
def neg (f : F) : F := fun x => !f x
def gt (t : Bool) (a b : F) : F := fun x => bif t then (a x && b x) else (a x || b x)

def Av (S : List F) (f : F) : Prop := (∃ b, f = K b) ∨ ∃ u ∈ S, f = u ∨ f = neg u

inductive Cost : List F → F → ℕ → Prop
  | av {S : List F} {f : F} {k : ℕ} : Av S f → Cost S f k
  | gate {S : List F} {f a b : F} {k : ℕ} (t : Bool) :
      Av S a → Av S b → Cost (gt t a b :: S) f k → Cost S f (k + 1)

theorem av_cons {S : List F} {f : F} (g : F) (h : Av S f) : Av (g :: S) f := by
  rcases h with h | ⟨u, hu, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨u, List.mem_cons_of_mem g hu, h⟩

theorem av_head (S : List F) (g : F) : Av (g :: S) g := Or.inr ⟨g, by simp, Or.inl rfl⟩

theorem av_neg {S : List F} {f : F} (h : Av S f) : Av S (neg f) := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, h | h⟩ <;> (try rw [h])
  · exact Or.inl ⟨!b, rfl⟩
  · exact Or.inr ⟨u, hu, Or.inr rfl⟩
  · exact Or.inr ⟨u, hu, Or.inl (by funext x; simp [neg])⟩

theorem cost_mono {S : List F} {f : F} {k : ℕ} (h : Cost S f k) : ∀ {k' : ℕ}, k ≤ k' → Cost S f k' := by
  induction h with
  | av h => exact fun _ => Cost.av h
  | gate t ha hb _ ih =>
    intro k' hk
    obtain ⟨k'', rfl⟩ : ∃ k'', k' = k'' + 1 := ⟨k' - 1, by omega⟩
    exact Cost.gate t ha hb (ih (by omega))

def rs (i : Fin 8) (c : Bool) (f : F) : F := fun x => f (Function.update x i c)

def Cst (f : F) : Prop := ∃ b, f = K b
def Ind (i : Fin 8) (f : F) : Prop := ∀ x b, f (Function.update x i b) = f x
def Good (i : Fin 8) (c : Bool) (f : F) : Prop := Ind i f ∨ Cst (rs i c f)
def Lit (i : Fin 8) (f : F) : Prop := Ind i f ∨ ∃ e, f = fun x => xor (x i) e

theorem av_rs {S T : List F} {i : Fin 8} {c : Bool} (hs : ∀ u ∈ S, Av T (rs i c u)) {f : F}
    (h : Av S f) : Av T (rs i c f) := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, h | h⟩ <;> (try rw [h])
  · exact Or.inl ⟨b, rfl⟩
  · exact hs u hu
  · exact av_neg (hs u hu)

theorem av_gt_cst {S : List F} (t : Bool) {a b : F} (ha : Av S a) (hb : Av S b) (h : Cst a ∨ Cst b) :
    Av S (gt t a b) := by
  rcases h with ⟨e, rfl⟩ | ⟨e, rfl⟩
  · cases t <;> cases e
    · rw [show gt false (K false) b = b from funext fun x => by simp [gt, K]]; exact hb
    · exact Or.inl ⟨true, funext fun x => by simp [gt, K]⟩
    · exact Or.inl ⟨false, funext fun x => by simp [gt, K]⟩
    · rw [show gt true (K true) b = b from funext fun x => by simp [gt, K]]; exact hb
  · cases t <;> cases e
    · rw [show gt false a (K false) = a from funext fun x => by simp [gt, K]]; exact ha
    · exact Or.inl ⟨true, funext fun x => by simp [gt, K]⟩
    · exact Or.inl ⟨false, funext fun x => by simp [gt, K]⟩
    · rw [show gt true a (K true) = a from funext fun x => by simp [gt, K]]; exact ha

theorem good_av {S : List F} {i : Fin 8} {c : Bool} (hs : ∀ u ∈ S, Good i c u) {f : F} (h : Av S f) :
    Good i c f := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, h | h⟩ <;> (try rw [h])
  · exact Or.inl fun _ _ => rfl
  · exact hs u hu
  · rcases hs u hu with h | ⟨b, h⟩
    · exact Or.inl fun x e => by simp only [neg, h x e]
    · refine Or.inr ⟨!b, funext fun x => ?_⟩
      have hx := congrFun h x
      simp only [rs, K] at hx
      simp only [rs, neg, K, hx]

theorem lit_av {S : List F} {i : Fin 8} (hs : ∀ u ∈ S, Lit i u) {f : F} (h : Av S f) : Lit i f := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, h | h⟩ <;> (try rw [h])
  · exact Or.inl fun _ _ => rfl
  · exact hs u hu
  · rcases hs u hu with h | ⟨e, rfl⟩
    · exact Or.inl fun x e => by simp only [neg, h x e]
    · exact Or.inr ⟨!e, funext fun x => by simp only [neg]; cases x i <;> cases e <;> rfl⟩

theorem lit_good {i : Fin 8} {c : Bool} {f : F} (h : Lit i f) : Good i c f := by
  rcases h with h | ⟨e, rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨xor c e, funext fun x => by simp [rs, K]⟩

theorem restrict {i : Fin 8} {c : Bool} {S : List F} {f : F} {k : ℕ} (p : Cost S f k) :
    ∀ T : List F, (∀ u ∈ S, Av T (rs i c u)) → Cost T (rs i c f) k := by
  induction p with
  | av h => exact fun T hT => Cost.av (av_rs hT h)
  | @gate S f a b k t ha hb _ ih =>
    intro T hT
    refine Cost.gate t (av_rs hT ha) (av_rs hT hb) (ih _ ?_)
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact av_head _ _
    · exact av_cons _ (hT u hu)

theorem strict {i : Fin 8} {c : Bool} {S : List F} {f : F} {k : ℕ} (p : Cost S f k) :
    ∀ T : List F, (∀ u ∈ S, Av T (rs i c u)) → (∀ u ∈ S, Good i c u) → ¬ Good i c f →
    1 ≤ k ∧ Cost T (rs i c f) (k - 1) := by
  induction p with
  | av h => exact fun T _ hg hf => absurd (good_av hg h) hf
  | @gate S f a b k t ha hb tail ih =>
    intro T hT hg hf
    by_cases hc : Cst (rs i c a) ∨ Cst (rs i c b)
    · refine ⟨by omega, ?_⟩
      have := restrict tail T (by
        intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact av_gt_cst t (av_rs hT ha) (av_rs hT hb) hc
        · exact hT u hu)
      simpa using this
    · have ia : Ind i a := (good_av hg ha).resolve_right fun h => hc (Or.inl h)
      have ib : Ind i b := (good_av hg hb).resolve_right fun h => hc (Or.inr h)
      obtain ⟨hk, q⟩ := ih (gt t (rs i c a) (rs i c b) :: T) (by
        intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact av_head _ _
        · exact av_cons _ (hT u hu)) (by
        intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact Or.inl fun x e => by simp only [gt, ia x e, ib x e]
        · exact hg u hu) hf
      refine ⟨by omega, ?_⟩
      have := Cost.gate t (av_rs hT ha) (av_rs hT hb) q
      rwa [show k - 1 + 1 = k + 1 - 1 by omega] at this

theorem kill {i : Fin 8} (t : Bool) {a b : F}
    (h : (∃ e, a = fun x => xor (x i) e) ∨ ∃ e, b = fun x => xor (x i) e) :
    ∃ c, Cst (rs i c (gt t a b)) := by
  rcases h with ⟨e, rfl⟩ | ⟨e, rfl⟩
  · refine ⟨xor e (!t), !t, funext fun x => ?_⟩
    cases t <;> cases e <;> simp [rs, gt, K]
  · refine ⟨xor e (!t), !t, funext fun x => ?_⟩
    cases t <;> cases e <;> simp [rs, gt, K]

theorem double {i : Fin 8} {S : List F} {f : F} {k : ℕ} (p : Cost S f k) :
    (∀ u ∈ S, Lit i u) → (∀ c, ¬ Good i c f) →
    ∃ c, ∀ T : List F, (∀ u ∈ S, Av T (rs i c u)) → 2 ≤ k ∧ Cost T (rs i c f) (k - 2) := by
  induction p with
  | av h => exact fun hs hf => absurd (lit_good (lit_av hs h)) (hf true)
  | @gate S f a b k t ha hb tail ih =>
    intro hs hf
    by_cases hab : Ind i a ∧ Ind i b
    · obtain ⟨c, hc⟩ := ih (by
        intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact Or.inl fun x e => by simp only [gt, hab.1 x e, hab.2 x e]
        · exact hs u hu) hf
      refine ⟨c, fun T hT => ?_⟩
      obtain ⟨hk, q⟩ := hc (gt t (rs i c a) (rs i c b) :: T) (by
        intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact av_head _ _
        · exact av_cons _ (hT u hu))
      refine ⟨by omega, ?_⟩
      have := Cost.gate t (av_rs hT ha) (av_rs hT hb) q
      rwa [show k - 2 + 1 = k + 1 - 2 by omega] at this
    · have hl : (∃ e, a = fun x => xor (x i) e) ∨ ∃ e, b = fun x => xor (x i) e := by
        rcases lit_av hs ha with h1 | h1
        · rcases lit_av hs hb with h2 | h2
          · exact absurd ⟨h1, h2⟩ hab
          · exact Or.inr h2
        · exact Or.inl h1
      obtain ⟨c, hc⟩ := kill t hl
      refine ⟨c, fun T hT => ?_⟩
      obtain ⟨hk, q⟩ := strict tail T (by
        intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact Or.inl hc
        · exact hT u hu) (by
        intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact Or.inr hc
        · exact lit_good (hs u hu)) (hf c)
      exact ⟨by omega, by rwa [show k + 1 - 2 = k - 1 by omega]⟩

def stock : List F := List.ofFn fun (j : Fin 8) (x : X) => x j

theorem stock_lit (i : Fin 8) : ∀ u ∈ stock, Lit i u := by
  intro u hu
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hu
  by_cases h : j = i
  · subst h
    exact Or.inr ⟨false, funext fun x => by simp⟩
  · exact Or.inl fun x b => by simp [Function.update_of_ne h]

theorem stock_rs (i : Fin 8) (c : Bool) : ∀ u ∈ stock, Av stock (rs i c u) := by
  intro u hu
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hu
  by_cases h : j = i
  · subst h
    exact Or.inl ⟨c, funext fun x => by simp [rs, K]⟩
  · exact Or.inr ⟨fun x => x j, List.mem_ofFn.mpr ⟨j, rfl⟩,
      Or.inl (funext fun x => by simp [rs, Function.update_of_ne h])⟩

def Low (n : ℕ) (f : F) : Prop := ∀ k, Cost stock f k → n ≤ k

theorem low_zero (f : F) : Low 0 f := fun _ _ => Nat.zero_le _

theorem low_one {n : ℕ} {f : F} (i : Fin 8) (c : Bool) (h : ¬ Good i c f) (t : Low n (rs i c f)) :
    Low (n + 1) f := by
  intro k p
  obtain ⟨hk, q⟩ := strict p stock (stock_rs i c) (fun u hu => lit_good (stock_lit i u hu)) h
  have := t _ q
  omega

theorem low_two {n : ℕ} {f : F} (i : Fin 8) (h0 : ¬ Good i false f) (h1 : ¬ Good i true f)
    (t0 : Low n (rs i false f)) (t1 : Low n (rs i true f)) : Low (n + 2) f := by
  intro k p
  obtain ⟨c, hc⟩ := double p (stock_lit i) (fun c => by cases c; exact h0; exact h1)
  obtain ⟨hk, q⟩ := hc stock (stock_rs i c)
  cases c
  · have := t0 _ q
    omega
  · have := t1 _ q
    omega

def pt (n : ℕ) : X := fun j => n.testBit j

theorem not_good {i : Fin 8} {c : Bool} {f : F} (a b d : ℕ)
    (h : ((f (Function.update (pt a) i true) != f (Function.update (pt a) i false)) &&
      (rs i c f (pt b) != rs i c f (pt d))) = true) : ¬ Good i c f := by
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  rintro (hi | ⟨e, he⟩)
  · exact h.1 ((hi _ _).trans (hi _ _).symm)
  · exact h.2 (by rw [he]; rfl)

def rd (w : List F) (j : ℕ) : F := fun x => (w.map fun f => f x).getD j false

def gv (w : List F) (g : Gate) : F := fun x => g.op.eval (g.inputs.map fun j => rd w j x)

theorem rd_av {S : List F} {w : List F} (hw : ∀ u ∈ w, Av S u) (j : ℕ) : Av S (rd w j) := by
  by_cases h : j < w.length
  · have e : rd w j = w[j] := by funext x; simp [rd, h]
    rw [e]
    exact hw _ (List.getElem_mem h)
  · exact Or.inl ⟨false, by funext x; simp [rd, K, List.getD_eq_getElem?_getD, Nat.le_of_not_lt h]⟩

theorem gv_cases {S : List F} {w : List F} (hw : ∀ u ∈ w, Av S u) (g : Gate)
    (hop : g.op = .and ∨ g.op = .or ∨ g.op = .not) (hl : g.inputs.length ≤ 2) :
    Av S (gv w g) ∨ (g.op ≠ .not ∧ ∃ t a b, Av S a ∧ Av S b ∧ gv w g = gt t a b) := by
  obtain ⟨op, args⟩ := g
  simp only at hop hl
  match args, hl with
  | [], _ => exact Or.inl (Or.inl ⟨op.eval [], funext fun x => by simp [gv, K]⟩)
  | [j], _ =>
    left
    rcases hop with rfl | rfl | rfl
    · rw [show gv w ⟨.and, [j]⟩ = rd w j from funext fun x => by simp [gv, GateOp.eval]]
      exact rd_av hw j
    · rw [show gv w ⟨.or, [j]⟩ = rd w j from funext fun x => by simp [gv, GateOp.eval]]
      exact rd_av hw j
    · rw [show gv w ⟨.not, [j]⟩ = neg (rd w j) from funext fun x => by simp [gv, GateOp.eval, neg]]
      exact av_neg (rd_av hw j)
  | [j, l], _ =>
    rcases hop with rfl | rfl | rfl
    · exact Or.inr ⟨by simp, true, _, _, rd_av hw j, rd_av hw l,
        funext fun x => by simp [gv, GateOp.eval, gt]⟩
    · exact Or.inr ⟨by simp, false, _, _, rd_av hw j, rd_av hw l,
        funext fun x => by simp [gv, GateOp.eval, gt]⟩
    · left
      rw [show gv w ⟨.not, [j, l]⟩ = neg (rd w j) from funext fun x => by simp [gv, GateOp.eval, neg]]
      exact av_neg (rd_av hw j)
  | _ :: _ :: _ :: _, hl => simp at hl

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false

def stp (w : List F) (g : Gate) : List F := w ++ [gv w g]

theorem to_cost (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) (o : ℕ) :
    ∀ (w S : List F), (∀ u ∈ w, Av S u) →
    Cost S (rd (gs.foldl stp w) o) (gs.countP fun g => !isNot g) := by
  induction gs with
  | nil => exact fun w S hw => Cost.av (rd_av hw o)
  | cons g gs ih =>
    intro w S hw
    have hg' := hg g (by simp)
    have ih := ih fun v hv => hg v (by simp [hv])
    rcases gv_cases hw g hg'.1 hg'.2 with h | ⟨hn, t, a, b, ha, hb, e⟩
    · have q := ih (w ++ [gv w g]) S (by
        intro u hu
        rcases List.mem_append.mp hu with h' | h'
        · exact hw _ h'
        · rw [List.mem_singleton.mp h']
          exact h)
      refine cost_mono q ?_
      rw [List.countP_cons]
      omega
    · have q := ih (w ++ [gv w g]) (gt t a b :: S) (by
        intro u hu
        rcases List.mem_append.mp hu with h' | h'
        · exact av_cons _ (hw _ h')
        · rw [List.mem_singleton.mp h', e]
          exact av_head _ _)
      have hn' : (!isNot g) = true := by
        rcases hg'.1 with h | h | h
        · simp [isNot, h]
        · simp [isNot, h]
        · exact absurd h hn
      rw [List.countP_cons]
      simp only [hn', ↓reduceIte]
      exact Cost.gate t ha hb q

theorem fold_eval (gs : List Gate) (x : X) : ∀ w : List F,
    (gs.foldl stp w).map (fun f => f x) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (w.map fun f => f x) := by
  induction gs with
  | nil => exact fun _ => rfl
  | cons g gs ih =>
    intro w
    simp only [List.foldl_cons, ih, stp, List.map_append, List.map_cons, List.map_nil]
    rfl

theorem all_and_or {n : ℕ} {f : F} (hl : Low n f) (gs : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : gs.length ≤ n)
    (he : ∀ x : X, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = f x) :
    ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  have q := to_cost gs hg o stock stock (fun u hu => Or.inr ⟨u, hu, Or.inl rfl⟩)
  have e : rd (gs.foldl stp stock) o = f := by
    funext x
    rw [← he x, rd, fold_eval]
    simp only [stock, List.map_ofFn]
    rfl
  rw [e] at q
  have h := hl _ q
  have hle := List.countP_le_length (p := fun g => !isNot g) (l := gs)
  have hall : ∀ g ∈ gs, (!isNot g) = true := by
    rw [← List.countP_eq_length]
    omega
  intro g hm
  refine ⟨?_, (hg g hm).2⟩
  have h2 := hall g hm
  rcases (hg g hm).1 with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · simp [isNot, h] at h2

def Rep (N : ℕ) (pts : ℕ → X) (u : F) (w : ℕ) : Prop := ∀ j, w.testBit j = (decide (j < N) && u (pts j))

def wordOf (pts : ℕ → X) (u : F) : ℕ → ℕ
  | 0 => 0
  | n + 1 => wordOf pts u n ||| (bif u (pts n) then 2 ^ n else 0)

theorem rep_wordOf (pts : ℕ → X) (u : F) (N : ℕ) : Rep N pts u (wordOf pts u N) := by
  induction N with
  | zero => intro j; simp [wordOf]
  | succ n ih =>
    intro j
    rw [wordOf, Nat.testBit_or, ih j]
    by_cases hj : j = n
    · subst hj
      cases hu : u (pts j) <;> simp
    · have h0 : (bif u (pts n) then 2 ^ n else 0).testBit j = false := by
        cases u (pts n) <;> simp [Ne.symm hj]
      rw [h0, Bool.or_false]
      congr 1
      exact decide_eq_decide.mpr (by omega)

theorem rep_unique {N : ℕ} {pts : ℕ → X} {u : F} {w w' : ℕ} (h : Rep N pts u w) (h' : Rep N pts u w') :
    w = w' := Nat.eq_of_testBit_eq fun j => (h j).trans (h' j).symm

theorem testBit_M {N j : ℕ} : (2 ^ N - 1).testBit j = decide (j < N) := by
  rw [Nat.testBit_two_pow_sub_one]

theorem rep_neg {N : ℕ} {pts : ℕ → X} {u : F} {w : ℕ} (h : Rep N pts u w) :
    Rep N pts (neg u) (w ^^^ (2 ^ N - 1)) := by
  intro j
  rw [Nat.testBit_xor, h j, testBit_M]
  by_cases hj : j < N <;> simp [hj, neg]

theorem rep_gt {N : ℕ} {pts : ℕ → X} {a b : F} {wa wb : ℕ} (t : Bool) (ha : Rep N pts a wa)
    (hb : Rep N pts b wb) : Rep N pts (gt t a b) (bif t then wa &&& wb else wa ||| wb) := by
  intro j
  cases t
  · simp only [Bool.cond_false, Nat.testBit_or, ha j, hb j, gt]
    by_cases hj : j < N <;> simp [hj]
  · simp only [Bool.cond_true, Nat.testBit_and, ha j, hb j, gt]
    by_cases hj : j < N <;> simp [hj]

theorem rep_K {N : ℕ} {pts : ℕ → X} (b : Bool) :
    Rep N pts (K b) 0 ∨ Rep N pts (K b) (0 ^^^ (2 ^ N - 1)) := by
  cases b
  · left; intro j; simp [K]
  · right; intro j; simp [K]

def ops (M a b : ℕ) : List ℕ := [a &&& b, a ||| b, a &&& (b ^^^ M), (a ^^^ M) &&& b]

def drop1 (d : Bool) (a : ℕ) (S : Finset ℕ) : Finset ℕ := if d then S.erase a else S

inductive Reach (M tg : ℕ) : Finset ℕ → ℕ → Prop
  | done {k c : ℕ} : (c = tg ∨ c = tg ^^^ M) → Reach M tg {c} k
  | step {S : Finset ℕ} {k a b c : ℕ} (da db : Bool) : a ∈ S → b ∈ S → a ≠ b → c ∈ ops M a b →
      c ≠ 0 → c ≠ M → c ∉ S → c ^^^ M ∉ S →
      Reach M tg (insert c (drop1 db b (drop1 da a S))) k → Reach M tg S (k + 1)

theorem reach_mono {M tg : ℕ} {S : Finset ℕ} {k : ℕ} (h : Reach M tg S k) :
    ∀ {k'}, k ≤ k' → Reach M tg S k' := by
  induction h with
  | done hc => exact fun _ => Reach.done hc
  | step da db ha hb hab hc h0 hM hn hn' _ ih =>
    intro k' hk
    obtain ⟨k'', rfl⟩ : ∃ k'', k' = k'' + 1 := ⟨k' - 1, by omega⟩
    exact Reach.step da db ha hb hab hc h0 hM hn hn' (ih (by omega))

theorem card_drop1 (d : Bool) (a : ℕ) (T : Finset ℕ) : T.card ≤ (drop1 d a T).card + 1 := by
  cases d
  · simp [drop1]
  · simp only [drop1, ite_true]
    have := Finset.pred_card_le_card_erase (s := T) (a := a)
    omega

theorem reach_card {M tg : ℕ} {S : Finset ℕ} {k : ℕ} (h : Reach M tg S k) : S.card ≤ k + 1 := by
  induction h with
  | done => simp
  | @step S k a b c da db ha hb hab hc h0 hM hn hn' _ ih =>
    have h1 : c ∉ drop1 db b (drop1 da a S) := by
      intro hm
      apply hn
      cases da <;> cases db <;> simp only [drop1, Bool.false_eq_true, ite_false, ite_true,
        Finset.mem_erase] at hm
      · exact hm
      · exact hm.2
      · exact hm.2
      · exact hm.2.2
    rw [Finset.card_insert_of_notMem h1] at ih
    have := card_drop1 da a S
    have := card_drop1 db b (drop1 da a S)
    omega

def Sep (P w p : ℕ) : Prop := (w.testBit (P + p) != w.testBit p) = true

theorem sep_xor {P w p M : ℕ} (hM : ∀ j, M.testBit j = decide (j < 2 * P)) (hp : p < P) :
    Sep P (w ^^^ M) p ↔ Sep P w p := by
  unfold Sep
  rw [Nat.testBit_xor, Nat.testBit_xor, hM, hM]
  have h1 : P + p < 2 * P := by omega
  have h2 : p < 2 * P := by omega
  simp only [h1, h2, decide_true]
  cases w.testBit (P + p) <;> cases w.testBit p <;> simp

theorem sep_ops {P M a b c p : ℕ} (hM : ∀ j, M.testBit j = decide (j < 2 * P)) (hp : p < P)
    (hc : c ∈ ops M a b) (h : Sep P c p) : Sep P a p ∨ Sep P b p := by
  simp only [ops, List.mem_cons, List.mem_nil_iff, or_false] at hc
  unfold Sep at *
  have h1 : P + p < 2 * P := by omega
  have h2 : p < 2 * P := by omega
  rcases hc with rfl | rfl | rfl | rfl <;>
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, hM, h1, h2, decide_true] at h ⊢ <;>
  revert h <;> cases a.testBit (P + p) <;> cases a.testBit p <;> cases b.testBit (P + p) <;>
    cases b.testBit p <;> simp

theorem reach_sep {P M tg : ℕ} (hM : ∀ j, M.testBit j = decide (j < 2 * P))
    (htg : ∀ p < P, Sep P tg p) {S : Finset ℕ} {k : ℕ} (h : Reach M tg S k) :
    ∀ p < P, ∃ w ∈ S, Sep P w p := by
  induction h with
  | done hc =>
    intro p hp
    refine ⟨_, Finset.mem_singleton_self _, ?_⟩
    rcases hc with rfl | rfl
    · exact htg p hp
    · exact (sep_xor hM hp).mpr (htg p hp)
  | @step S k a b c da db ha hb hab hc h0 hMc hn hn' _ ih =>
    intro p hp
    obtain ⟨w, hw, hs⟩ := ih p hp
    rcases Finset.mem_insert.mp hw with rfl | hw
    · rcases sep_ops hM hp hc hs with h | h
      · exact ⟨a, ha, h⟩
      · exact ⟨b, hb, h⟩
    · refine ⟨w, ?_, hs⟩
      cases da <;> cases db <;> simp only [drop1, Bool.false_eq_true, ite_false, ite_true,
        Finset.mem_erase] at hw
      · exact hw
      · exact hw.2
      · exact hw.2
      · exact hw.2.2

def sepw (P w : ℕ) : ℕ := ((w >>> P) ^^^ w) &&& (2 ^ P - 1)

def orAll (P : ℕ) (L : List ℕ) : ℕ := L.foldr (fun w acc => sepw P w ||| acc) 0

def cov (P : ℕ) (L : List ℕ) : Bool := orAll P L == 2 ^ P - 1

theorem orAll_bit (P : ℕ) (L : List ℕ) (j : ℕ) :
    (orAll P L).testBit j = (decide (j < P) && L.any fun w => (w.testBit (P + j) != w.testBit j)) := by
  induction L with
  | nil => simp [orAll]
  | cons w L ih =>
    simp only [orAll, List.foldr_cons] at ih ⊢
    rw [Nat.testBit_or, ih]
    simp only [sepw, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftRight, testBit_M, List.any_cons]
    by_cases hj : j < P <;> simp only [hj, decide_true, decide_false, Bool.true_and, Bool.and_true,
      Bool.and_false, Bool.false_and, Bool.or_false]

theorem cov_iff (P : ℕ) (L : List ℕ) : cov P L = true ↔ ∀ p < P, ∃ w ∈ L, Sep P w p := by
  unfold cov
  rw [beq_iff_eq]
  constructor
  · intro h p hp
    have hb := orAll_bit P L p
    rw [h, testBit_M] at hb
    simp only [hp, decide_true, Bool.true_and] at hb
    exact List.any_eq_true.mp hb.symm
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    rw [orAll_bit, testBit_M]
    by_cases hj : j < P
    · obtain ⟨w, hw, hs⟩ := h j hj
      simp only [hj, decide_true, Bool.true_and, List.any_eq_true]
      exact ⟨w, hw, hs⟩
    · simp [hj]

def tryPairs (f : ℕ → ℕ → Bool) : List ℕ → Bool
  | [] => false
  | a :: rest => rest.any (f a) || tryPairs f rest

theorem tryPairs_of (f : ℕ → ℕ → Bool) (L : List ℕ) (a b : ℕ) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b)
    (h1 : f a b = true) (h2 : f b a = true) : tryPairs f L = true := by
  induction L with
  | nil => cases ha
  | cons y ys ih =>
    simp only [tryPairs, Bool.or_eq_true, List.any_eq_true]
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact absurd rfl hab
      · exact Or.inl ⟨b, hb, h1⟩
    · rcases hb with rfl | hb
      · exact Or.inl ⟨a, ha, h2⟩
      · exact Or.inr (ih ha hb)

def dropL (d : Bool) (a : ℕ) (L : List ℕ) : List ℕ := if d then L.erase a else L

def srch (P M tg : ℕ) : ℕ → List ℕ → Bool
  | 0, L => L == [tg] || L == [tg ^^^ M]
  | k + 1, L => (L == [tg] || L == [tg ^^^ M]) ||
      (decide (L.length ≤ k + 2) && cov P L && tryPairs (fun a b => (ops M a b).any fun c =>
        c != 0 && c != M && !L.contains c && !L.contains (c ^^^ M) &&
        (srch P M tg k (c :: dropL true b (dropL true a L)) ||
         srch P M tg k (c :: dropL false b (dropL true a L)) ||
         srch P M tg k (c :: dropL true b (dropL false a L)) ||
         srch P M tg k (c :: dropL false b (dropL false a L)))) L)

theorem toFinset_dropL (d : Bool) (a : ℕ) (L : List ℕ) (hnd : L.Nodup) :
    (dropL d a L).toFinset = drop1 d a L.toFinset := by
  cases d
  · rfl
  · ext z
    simp only [dropL, drop1, ite_true, List.mem_toFinset, Finset.mem_erase, hnd.mem_erase_iff]

theorem nodup_dropL (d : Bool) (a : ℕ) (L : List ℕ) (hnd : L.Nodup) : (dropL d a L).Nodup := by
  cases d
  · exact hnd
  · exact hnd.erase a

theorem singleton_list {c : ℕ} {L : List ℕ} (hnd : L.Nodup) (h : L.toFinset = {c}) : L = [c] := by
  have hl : L.length = 1 := by
    rw [← List.toFinset_card_of_nodup hnd, h]
    rfl
  match L, hl with
  | [d], _ =>
    have : d ∈ ({c} : Finset ℕ) := by rw [← h]; simp
    rw [Finset.mem_singleton.mp this]

theorem ops_swap (M a b c : ℕ) (h : c ∈ ops M a b) : c ∈ ops M b a := by
  simp only [ops, List.mem_cons, List.mem_nil_iff, or_false] at h ⊢
  rcases h with rfl | rfl | rfl | rfl
  · exact Or.inl (Nat.land_comm _ _)
  · exact Or.inr (Or.inl (Nat.lor_comm _ _))
  · exact Or.inr (Or.inr (Or.inr (Nat.land_comm _ _)))
  · exact Or.inr (Or.inr (Or.inl (Nat.land_comm _ _)))

theorem drop_swap (da db : Bool) (a b : ℕ) (S : Finset ℕ) :
    drop1 db b (drop1 da a S) = drop1 da a (drop1 db b S) := by
  cases da <;> cases db <;> simp only [drop1, Bool.false_eq_true, ite_false, ite_true]
  exact Finset.erase_right_comm

theorem pick_bool (srch1 : List ℕ → Bool) (c a b : ℕ) (L : List ℕ) (da db : Bool)
    (h : srch1 (c :: dropL db b (dropL da a L)) = true) :
    (srch1 (c :: dropL true b (dropL true a L)) ||
     srch1 (c :: dropL false b (dropL true a L)) ||
     srch1 (c :: dropL true b (dropL false a L)) ||
     srch1 (c :: dropL false b (dropL false a L))) = true := by
  cases da <;> cases db <;> simp [h]

theorem srch_complete {P M tg : ℕ} (hM : ∀ j, M.testBit j = decide (j < 2 * P))
    (htg : ∀ p < P, Sep P tg p) {S : Finset ℕ} {k : ℕ} (h : Reach M tg S k) :
    ∀ L : List ℕ, L.Nodup → L.toFinset = S → srch P M tg k L = true := by
  induction h with
  | @done k c hc =>
    intro L hnd hL
    rw [singleton_list hnd hL]
    cases k <;> rcases hc with rfl | rfl <;> simp [srch]
  | @step S k a b c da db ha hb hab hc h0 hMc hn hn' hr ih =>
    intro L hnd hL
    have hcard := reach_card (Reach.step da db ha hb hab hc h0 hMc hn hn' hr)
    have hsep := reach_sep hM htg (Reach.step da db ha hb hab hc h0 hMc hn hn' hr)
    rw [← hL, List.toFinset_card_of_nodup hnd] at hcard
    have hcov : cov P L = true := (cov_iff P L).mpr fun p hp => by
      obtain ⟨w, hw, hs⟩ := hsep p hp
      exact ⟨w, by rw [← hL] at hw; simpa using hw, hs⟩
    have haL : a ∈ L := by rw [← hL] at ha; simpa using ha
    have hbL : b ∈ L := by rw [← hL] at hb; simpa using hb
    have hcL : L.contains c = false := by
      rw [← hL] at hn; simpa using hn
    have hcL' : L.contains (c ^^^ M) = false := by
      rw [← hL] at hn'; simpa using hn'
    have key : ∀ (a' b' : ℕ) (da' db' : Bool), c ∈ ops M a' b' →
        drop1 db' b' (drop1 da' a' S) = drop1 db b (drop1 da a S) →
        ((ops M a' b').any fun c =>
          c != 0 && c != M && !L.contains c && !L.contains (c ^^^ M) &&
          (srch P M tg k (c :: dropL true b' (dropL true a' L)) ||
           srch P M tg k (c :: dropL false b' (dropL true a' L)) ||
           srch P M tg k (c :: dropL true b' (dropL false a' L)) ||
           srch P M tg k (c :: dropL false b' (dropL false a' L)))) = true := by
      intro a' b' da' db' hc' hd
      rw [List.any_eq_true]
      refine ⟨c, hc', ?_⟩
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, hcL, hcL', Bool.not_false, and_true]
      refine ⟨⟨h0, hMc⟩, pick_bool _ c a' b' L da' db' (ih _ ?_ ?_)⟩
      · refine List.nodup_cons.mpr ⟨?_, nodup_dropL _ _ _ (nodup_dropL _ _ _ hnd)⟩
        intro hm
        have : c ∈ L := by
          cases da' <;> cases db' <;> simp only [dropL, Bool.false_eq_true, ite_false, ite_true] at hm
          · exact hm
          · exact List.mem_of_mem_erase hm
          · exact List.mem_of_mem_erase hm
          · exact List.mem_of_mem_erase (List.mem_of_mem_erase hm)
        simp [this] at hcL
      · rw [List.toFinset_cons, toFinset_dropL _ _ _ (nodup_dropL _ _ _ hnd), toFinset_dropL _ _ _ hnd,
          hL, hd]
    simp only [srch, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    right
    refine ⟨⟨by omega, hcov⟩, tryPairs_of _ L a b haL hbL hab (key a b da db hc rfl)
      (key b a db da (ops_swap M a b c hc) (drop_swap da db a b S).symm)⟩

theorem bit_hi {P x j : ℕ} (hx : x < 2 ^ (2 * P)) (hj : ¬ j < 2 * P) : x.testBit j = false :=
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))

theorem bd_rep {P : ℕ} {pts : ℕ → X} {u : F} {w : ℕ} (h : Rep (2 * P) pts u w) : w < 2 ^ (2 * P) := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  rw [h j]
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt]
  exact Or.inl hj

theorem bd_xor {P x : ℕ} (hx : x < 2 ^ (2 * P)) : x ^^^ (2 ^ (2 * P) - 1) < 2 ^ (2 * P) := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  rw [Nat.testBit_xor, testBit_M, bit_hi hx (by omega)]
  simp
  omega

theorem id_and_M {P x : ℕ} (hx : x < 2 ^ (2 * P)) : (2 ^ (2 * P) - 1) &&& x = x := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, testBit_M]
  by_cases hj : j < 2 * P
  · simp [hj]
  · simp [hj, bit_hi hx hj]

theorem id_or_M {P x : ℕ} (hx : x < 2 ^ (2 * P)) : (2 ^ (2 * P) - 1) ||| x = 2 ^ (2 * P) - 1 := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_or, testBit_M]
  by_cases hj : j < 2 * P
  · simp [hj]
  · simp [hj, bit_hi hx hj]

theorem id_and_opp {P x : ℕ} (hx : x < 2 ^ (2 * P)) : x &&& (x ^^^ (2 ^ (2 * P) - 1)) = 0 := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, Nat.testBit_xor, testBit_M]
  by_cases hj : j < 2 * P
  · simp only [hj, decide_true, Nat.zero_testBit]; cases x.testBit j <;> rfl
  · simp [hj, bit_hi hx hj]

theorem id_or_opp {P x : ℕ} (hx : x < 2 ^ (2 * P)) : x ||| (x ^^^ (2 ^ (2 * P) - 1)) = 2 ^ (2 * P) - 1 := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_or, Nat.testBit_xor, testBit_M]
  by_cases hj : j < 2 * P
  · simp only [hj, decide_true]; cases x.testBit j <;> rfl
  · simp [hj, bit_hi hx hj]

theorem dm1 {P x y : ℕ} (hx : x < 2 ^ (2 * P)) (hy : y < 2 ^ (2 * P)) :
    (x ^^^ (2 ^ (2 * P) - 1)) &&& (y ^^^ (2 ^ (2 * P) - 1)) = (x ||| y) ^^^ (2 ^ (2 * P) - 1) := by
  apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, testBit_M]
  by_cases hj : j < 2 * P
  · simp only [hj, decide_true]; cases x.testBit j <;> cases y.testBit j <;> rfl
  · simp [hj, bit_hi hx hj, bit_hi hy hj]

theorem dm2 {P x y : ℕ} (hx : x < 2 ^ (2 * P)) (hy : y < 2 ^ (2 * P)) :
    x ||| (y ^^^ (2 ^ (2 * P) - 1)) = ((x ^^^ (2 ^ (2 * P) - 1)) &&& y) ^^^ (2 ^ (2 * P) - 1) := by
  apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, testBit_M]
  by_cases hj : j < 2 * P
  · simp only [hj, decide_true]; cases x.testBit j <;> cases y.testBit j <;> rfl
  · simp [hj, bit_hi hx hj, bit_hi hy hj]

theorem dm3 {P x y : ℕ} (hx : x < 2 ^ (2 * P)) (hy : y < 2 ^ (2 * P)) :
    (x ^^^ (2 ^ (2 * P) - 1)) ||| y = (x &&& (y ^^^ (2 ^ (2 * P) - 1))) ^^^ (2 ^ (2 * P) - 1) := by
  apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, testBit_M]
  by_cases hj : j < 2 * P
  · simp only [hj, decide_true]; cases x.testBit j <;> cases y.testBit j <;> rfl
  · simp [hj, bit_hi hx hj, bit_hi hy hj]

theorem dm4 {P x y : ℕ} (hx : x < 2 ^ (2 * P)) (hy : y < 2 ^ (2 * P)) :
    (x ^^^ (2 ^ (2 * P) - 1)) ||| (y ^^^ (2 ^ (2 * P) - 1)) = (x &&& y) ^^^ (2 ^ (2 * P) - 1) := by
  apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, testBit_M]
  by_cases hj : j < 2 * P
  · simp only [hj, decide_true]; cases x.testBit j <;> cases y.testBit j <;> rfl
  · simp [hj, bit_hi hx hj, bit_hi hy hj]

def sg (P : ℕ) (s : Bool) (x : ℕ) : ℕ := bif s then x ^^^ (2 ^ (2 * P) - 1) else x

def opT (t : Bool) (x y : ℕ) : ℕ := bif t then x &&& y else x ||| y

theorem op8 {P x y : ℕ} (hx : x < 2 ^ (2 * P)) (hy : y < 2 ^ (2 * P)) (t sx sy : Bool) :
    ∃ c ∈ ops (2 ^ (2 * P) - 1) x y, opT t (sg P sx x) (sg P sy y) = c ∨ opT t (sg P sx x) (sg P sy y) = c ^^^ (2 ^ (2 * P) - 1) := by
  cases t <;> cases sx <;> cases sy <;> simp only [opT, sg, Bool.cond_true, Bool.cond_false]
  · exact ⟨_, by simp [ops], Or.inl rfl⟩
  · exact ⟨_, by simp [ops], Or.inr (dm2 hx hy)⟩
  · exact ⟨_, by simp [ops], Or.inr (dm3 hx hy)⟩
  · exact ⟨_, by simp [ops], Or.inr (dm4 hx hy)⟩
  · exact ⟨_, by simp [ops], Or.inl rfl⟩
  · exact ⟨_, by simp [ops], Or.inl rfl⟩
  · exact ⟨_, by simp [ops], Or.inl rfl⟩
  · exact ⟨_, by simp [ops], Or.inr (dm1 hx hy)⟩

theorem xx (w M : ℕ) : (w ^^^ M) ^^^ M = w := by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

def W (P : ℕ) (pts : ℕ → X) (u : F) : ℕ := wordOf pts u (2 * P)

theorem W_bd (P : ℕ) (pts : ℕ → X) (u : F) : W P pts u < 2 ^ (2 * P) := bd_rep (rep_wordOf pts u _)

theorem W_neg (P : ℕ) (pts : ℕ → X) (u : F) : W P pts (neg u) = W P pts u ^^^ (2 ^ (2 * P) - 1) :=
  rep_unique (rep_wordOf pts _ _) (rep_neg (rep_wordOf pts u _))

theorem W_gt (P : ℕ) (pts : ℕ → X) (t : Bool) (a b : F) :
    W P pts (gt t a b) = opT t (W P pts a) (W P pts b) := by
  have := rep_gt t (rep_wordOf pts a (2 * P)) (rep_wordOf pts b (2 * P))
  exact rep_unique (rep_wordOf pts _ _) (by cases t <;> exact this)

theorem W_K (P : ℕ) (pts : ℕ → X) (b : Bool) : W P pts (K b) = 0 ∨ W P pts (K b) = 0 ^^^ (2 ^ (2 * P) - 1) := by
  rcases rep_K (N := 2 * P) (pts := pts) b with h | h
  · exact Or.inl (rep_unique (rep_wordOf pts _ _) h)
  · exact Or.inr (rep_unique (rep_wordOf pts _ _) h)

def Hd (P : ℕ) (pts : ℕ → X) (A : Finset ℕ) (u : F) : Prop :=
  ∃ n, (n = 0 ∨ n ∈ A) ∧ (W P pts u = n ∨ W P pts u = n ^^^ (2 ^ (2 * P) - 1))

theorem hd_av {P : ℕ} {pts : ℕ → X} {A : Finset ℕ} {S : List F} (hs : ∀ u ∈ S, Hd P pts A u) {f : F}
    (h : Av S f) : Hd P pts A f := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, h | h⟩
  · exact ⟨0, Or.inl rfl, W_K P pts b⟩
  · rw [h]; exact hs u hu
  · rw [h]
    obtain ⟨n, hn, e | e⟩ := hs u hu
    · exact ⟨n, hn, Or.inr (by rw [W_neg, e])⟩
    · exact ⟨n, hn, Or.inl (by rw [W_neg, e, xx])⟩

theorem hd_mono {P : ℕ} {pts : ℕ → X} {A A' : Finset ℕ} (hA : A ⊆ A') {u : F} (h : Hd P pts A u) :
    Hd P pts A' u := by
  obtain ⟨n, hn | hn, e⟩ := h
  · exact ⟨n, Or.inl hn, e⟩
  · exact ⟨n, Or.inr (hA hn), e⟩

theorem hd_flag {P : ℕ} {pts : ℕ → X} {A : Finset ℕ} {u : F} (h : Hd P pts A u) :
    ∃ n s, (n = 0 ∨ n ∈ A) ∧ W P pts u = sg P s n := by
  obtain ⟨n, hn, e | e⟩ := h
  · exact ⟨n, false, hn, e⟩
  · exact ⟨n, true, hn, e⟩

theorem hd_zero {P : ℕ} {pts : ℕ → X} {A : Finset ℕ} {u : F} (h : W P pts u = 0) : Hd P pts A u :=
  ⟨0, Or.inl rfl, Or.inl h⟩

theorem hd_M {P : ℕ} {pts : ℕ → X} {A : Finset ℕ} {u : F} (h : W P pts u = 2 ^ (2 * P) - 1) :
    Hd P pts A u := ⟨0, Or.inl rfl, Or.inr (by rw [h, Nat.zero_xor])⟩

theorem hd_eq {P : ℕ} {pts : ℕ → X} {A : Finset ℕ} {u v : F} (h : W P pts u = W P pts v)
    (hv : Hd P pts A v) : Hd P pts A u := by
  obtain ⟨n, hn, e⟩ := hv
  exact ⟨n, hn, by rw [h]; exact e⟩

theorem bd_sg {P n : ℕ} (s : Bool) {w : ℕ} (hw : w < 2 ^ (2 * P)) (e : w = sg P s n) : n < 2 ^ (2 * P) := by
  cases s
  · have : w = n := by simpa [sg] using e
    rw [← this]; exact hw
  · have : n = w ^^^ (2 ^ (2 * P) - 1) := by rw [e, sg, Bool.cond_true, xx]
    rw [this]; exact bd_xor hw

theorem deg_const {P : ℕ} {pts : ℕ → X} {A : Finset ℕ} (t : Bool) {a b : F} (hb : Hd P pts A b)
    (e : W P pts a = 0 ∨ W P pts a = 2 ^ (2 * P) - 1) : Hd P pts A (gt t a b) := by
  have bw := W_bd P pts b
  rcases e with e | e <;> cases t
  · exact hd_eq (by rw [W_gt, e]; simp [opT]) hb
  · exact hd_zero (by rw [W_gt, e]; simp [opT])
  · exact hd_M (by rw [W_gt, e]; simp only [opT, Bool.cond_false]; exact id_or_M bw)
  · exact hd_eq (by rw [W_gt, e]; simp only [opT, Bool.cond_true]; exact id_and_M bw) hb

theorem deg_const' {P : ℕ} {pts : ℕ → X} {A : Finset ℕ} (t : Bool) {a b : F} (ha : Hd P pts A a)
    (e : W P pts b = 0 ∨ W P pts b = 2 ^ (2 * P) - 1) : Hd P pts A (gt t a b) := by
  have h := deg_const (pts := pts) (A := A) t ha e
  obtain ⟨n, hn, h⟩ := h
  refine ⟨n, hn, ?_⟩
  rw [W_gt] at h ⊢
  cases t
  · simpa [opT, Nat.lor_comm] using h
  · simpa [opT, Nat.land_comm] using h

theorem deg_same {P : ℕ} {pts : ℕ → X} {A : Finset ℕ} (t : Bool) {a b : F} {n : ℕ} (hn : n ∈ A)
    (sa sb : Bool) (ea : W P pts a = sg P sa n) (eb : W P pts b = sg P sb n) : Hd P pts A (gt t a b) := by
  have bn : n < 2 ^ (2 * P) := bd_sg sa (W_bd P pts a) ea
  have g := W_gt P pts t a b
  rw [ea, eb] at g
  cases t <;> cases sa <;> cases sb <;> simp only [opT, sg, Bool.cond_true, Bool.cond_false] at g
  · exact ⟨n, Or.inr hn, Or.inl (by rw [g, Nat.or_self])⟩
  · exact hd_M (by rw [g]; exact id_or_opp bn)
  · exact hd_M (by rw [g, Nat.lor_comm]; exact id_or_opp bn)
  · exact ⟨n, Or.inr hn, Or.inr (by rw [g, Nat.or_self])⟩
  · exact ⟨n, Or.inr hn, Or.inl (by rw [g, Nat.and_self])⟩
  · exact hd_zero (by rw [g]; exact id_and_opp bn)
  · exact hd_zero (by rw [g, Nat.land_comm]; exact id_and_opp bn)
  · exact ⟨n, Or.inr hn, Or.inr (by rw [g, Nat.and_self])⟩

theorem extract {P tg : ℕ} {pts : ℕ → X} {S : List F} {f : F} {k : ℕ} (p : Cost S f k) :
    ∀ A : Finset ℕ, (∀ u ∈ S, Hd P pts A u) → W P pts f = tg → tg ≠ 0 → tg ≠ 2 ^ (2 * P) - 1 →
    ∃ L ⊆ A, Reach (2 ^ (2 * P) - 1) tg L k := by
  induction p with
  | av h =>
    intro A hA hf h0 hM
    obtain ⟨n, hn, hw⟩ := hd_av hA h
    rcases hn with rfl | hn
    · exfalso
      rcases hw with e | e <;> rw [hf] at e
      · exact h0 e
      · exact hM (by rw [e, Nat.zero_xor])
    · refine ⟨{n}, by simpa using hn, Reach.done ?_⟩
      rcases hw with e | e <;> rw [hf] at e
      · exact Or.inl e.symm
      · exact Or.inr (by rw [e, xx])
  | @gate S f a b k t ha hb tail ih =>
    intro A hA hf h0 hM
    by_cases hg : Hd P pts A (gt t a b)
    · obtain ⟨L, hL, hr⟩ := ih A (by
        intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact hg
        · exact hA u hu) hf h0 hM
      exact ⟨L, hL, reach_mono hr (by omega)⟩
    · have hda := hd_av hA ha
      have hdb := hd_av hA hb
      obtain ⟨na, sa, hna, ea⟩ := hd_flag hda
      obtain ⟨nb, sb, hnb, eb⟩ := hd_flag hdb
      have bna := bd_sg sa (W_bd P pts a) ea
      have bnb := bd_sg sb (W_bd P pts b) eb
      have hnaA : na ∈ A := by
        rcases hna with rfl | h
        · exfalso; apply hg; apply deg_const t hdb
          rw [ea]; cases sa
          · exact Or.inl rfl
          · exact Or.inr (by simp [sg])
        · exact h
      have hnbA : nb ∈ A := by
        rcases hnb with rfl | h
        · exfalso; apply hg; apply deg_const' t hda
          rw [eb]; cases sb
          · exact Or.inl rfl
          · exact Or.inr (by simp [sg])
        · exact h
      have hne : na ≠ nb := by
        rintro rfl
        exact hg (deg_same t hnaA sa sb ea eb)
      obtain ⟨c, hc, hcw⟩ := op8 bna bnb t sa sb
      have wg : W P pts (gt t a b) = opT t (sg P sa na) (sg P sb nb) := by rw [W_gt, ea, eb]
      rw [← wg] at hcw
      have hc0 : c ≠ 0 := by
        rintro rfl
        exact hg ⟨0, Or.inl rfl, hcw⟩
      have hcM : c ≠ 2 ^ (2 * P) - 1 := by
        rintro rfl
        refine hg ⟨0, Or.inl rfl, ?_⟩
        rcases hcw with e | e
        · exact Or.inr (by rw [e, Nat.zero_xor])
        · exact Or.inl (by rw [e, Nat.xor_self])
      have hcA : c ∉ A := fun h => hg ⟨c, Or.inr h, hcw⟩
      have hcA' : c ^^^ (2 ^ (2 * P) - 1) ∉ A := by
        intro h
        refine hg ⟨_, Or.inr h, ?_⟩
        rcases hcw with e | e
        · exact Or.inr (by rw [e, xx])
        · exact Or.inl e
      have hMne : c ^^^ (2 ^ (2 * P) - 1) ≠ c := by
        intro h
        have : 2 ^ (2 * P) - 1 = 0 := by
          have h2 := congrArg (· ^^^ c) h
          simp only [Nat.xor_self] at h2
          rw [Nat.xor_comm, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at h2
          exact h2
        have := W_bd P pts f
        rw [hf] at this
        omega
      obtain ⟨L', hL', hr⟩ := ih (insert c A) (by
        intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact ⟨c, Or.inr (Finset.mem_insert_self _ _), hcw⟩
        · exact hd_mono (Finset.subset_insert _ _) (hA u hu)) hf h0 hM
      by_cases hcL : c ∈ L'
      · have hsub : insert na (insert nb (L'.erase c)) ⊆ A := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_erase] at hz
          rcases hz with rfl | rfl | ⟨hzc, hz⟩
          · exact hnaA
          · exact hnbA
          · rcases Finset.mem_insert.mp (hL' hz) with h | h
            · exact absurd h hzc
            · exact h
        refine ⟨_, hsub, Reach.step (!decide (na ∈ L')) (!decide (nb ∈ L')) (by simp) (by simp) hne hc
          hc0 hcM (fun h => hcA (hsub h)) (fun h => hcA' (hsub h)) ?_⟩
        have hna' : na ≠ c := fun h => hcA (h ▸ hnaA)
        have hnb' : nb ≠ c := fun h => hcA (h ▸ hnbA)
        convert hr using 1
        ext z
        by_cases h1 : na ∈ L' <;> by_cases h2 : nb ∈ L' <;>
          simp only [drop1, h1, h2, decide_true, decide_false, Bool.not_true, Bool.not_false,
            Bool.false_eq_true, ite_true, ite_false, Finset.mem_insert, Finset.mem_erase] <;>
          by_cases hz : z = c <;> by_cases hza : z = na <;> by_cases hzb : z = nb <;> subst_vars <;>
          simp_all
      · refine ⟨L', ?_, reach_mono hr (by omega)⟩
        intro z hz
        rcases Finset.mem_insert.mp (hL' hz) with h | h
        · exact absurd (h ▸ hz) hcL
        · exact h

def ptsOf (pl : List ℕ) : ℕ → X := fun j => pt (pl.getD j 0)

theorem core_low (P M tg r : ℕ) (pl roots : List ℕ) (f : F)
    (hM : M = 2 ^ (2 * P) - 1)
    (htg : W P (ptsOf pl) f = tg)
    (hchk : (tg != 0 && tg != M && cov P [tg] && decide roots.Nodup &&
      (List.finRange 8).all fun j => (W P (ptsOf pl) (fun x => x j) == 0 ||
        W P (ptsOf pl) (fun x => x j) == M || roots.contains (W P (ptsOf pl) (fun x => x j)) ||
        roots.contains (W P (ptsOf pl) (fun x => x j) ^^^ M))) = true)
    (hs : roots.sublists.all (fun L => !srch P M tg r L) = true) : Low (r + 1) f := by
  subst hM
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at hchk
  obtain ⟨⟨⟨⟨h0, hM⟩, hcov⟩, hnd⟩, hcols⟩ := hchk
  have hsep : ∀ p < P, Sep P tg p := by
    intro p hp
    obtain ⟨w, hw, hs⟩ := (cov_iff P [tg]).mp hcov p hp
    rw [List.mem_singleton.mp hw] at hs
    exact hs
  intro k p
  by_contra hlt
  have q := cost_mono p (k' := r) (by omega)
  obtain ⟨L, hL, hr⟩ := extract q roots.toFinset (by
    intro u hu
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hu
    rcases hcols j (List.mem_finRange j) with ((h | h) | h) | h
    · exact hd_zero h
    · exact hd_M h
    · exact ⟨_, Or.inr (List.mem_toFinset.mpr h), Or.inl rfl⟩
    · exact ⟨_, Or.inr (List.mem_toFinset.mpr h), Or.inr (by rw [xx])⟩) htg h0 hM
  have hc := srch_complete (fun j => testBit_M) hsep hr (roots.filter fun z => decide (z ∈ L))
    (hnd.filter _) (by
      ext z
      simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨List.mem_toFinset.mp (hL h), h⟩)
  have hall := List.all_eq_true.mp hs (roots.filter fun z => decide (z ∈ L))
    (List.mem_sublists.mpr List.filter_sublist)
  rw [hc] at hall
  exact absurd hall (by decide)

def target : F := fun x => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 5 && x 7) || (x 6 && x 7)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem core_1 : Low 6 (rs 4 false (rs 3 false (rs 1 false (target)))) :=
  core_low 231 11908525658859223294760121268437066290850060053501019099651935423375594096449911575776314174894302258147533153997065059263030913083222523903 11908525658859223294760121268437066290850060053501019099651935423375590645576738180494420457516371119634806928442578974069753331821110624256 5 [0, 1, 4, 5, 32, 33, 36, 37, 64, 96, 128, 0, 1, 4, 5, 32, 33, 36, 37, 64, 96, 128, 0, 1, 4, 5, 32, 33, 36, 37, 64, 96, 128, 0, 1, 4, 5, 32, 33, 36, 37, 64, 96, 128, 0, 1, 4, 5, 32, 33, 36, 37, 64, 96, 128, 0, 1, 4, 5, 32, 33, 36, 37, 64, 96, 128, 0, 1, 4, 5, 32, 33, 36, 37, 64, 96, 128, 0, 1, 4, 5, 32, 33, 36, 37, 64, 96, 128, 0, 1, 4, 5, 32, 33, 36, 37, 64, 96, 128, 0, 1, 4, 5, 32, 33, 36, 37, 64, 96, 128, 0, 1, 4, 5, 32, 33, 36, 37, 64, 96, 128, 0, 1, 4, 5, 32, 33, 36, 37, 64, 96, 128, 0, 1, 4, 5, 32, 33, 36, 37, 64, 96, 128, 0, 1, 4, 5, 32, 33, 36, 37, 64, 96, 128, 0, 1, 4, 5, 32, 33, 36, 37, 64, 96, 128, 0, 1, 4, 5, 32, 33, 36, 37, 64, 96, 128, 0, 1, 4, 5, 32, 33, 36, 37, 64, 96, 128, 0, 1, 4, 5, 32, 33, 36, 37, 64, 96, 128, 0, 1, 4, 5, 32, 33, 36, 37, 64, 96, 128, 0, 1, 4, 5, 32, 33, 36, 37, 64, 96, 128, 0, 1, 4, 5, 32, 33, 36, 37, 64, 96, 128, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 132, 132, 132, 132, 132, 132, 132, 132, 132, 132, 132, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 164, 164, 164, 164, 164, 164, 164, 164, 164, 164, 164, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 192, 192, 192, 192, 192, 192, 192, 192, 192, 192, 192, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 196, 196, 196, 196, 196, 196, 196, 196, 196, 196, 196, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 224, 224, 224, 224, 224, 224, 224, 224, 224, 224, 224, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 228, 228, 228, 228, 228, 228, 228, 228, 228, 228, 228, 229, 229, 229, 229, 229, 229, 229, 229, 229, 229, 229] [11902713786892966963235104127749688513255696920239437941760697419453708365603321573688659265833579979296133675674210160988319630424078110890, 11908522819646133436196355695804349204928485239542810044997535023685547008917621962737064854494888389135321158724143658520493400394423492812, 11908525658858546373448080092350261205738930850972956528625717521689051946533638236150537236804170230062246912609308583707161817676808422128, 11908525658859223294760121229958544614683576447760023631352479377613192614683499047166884974471730453044167839811655964965317032361518957312, 11908525658859223294760121268437066290850060053500764470154893612614812267018357011600300555998245694590571811803765205292752114564760339456] _ (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem core_2 : Low 6 (rs 4 true (rs 3 false (rs 1 false (target)))) :=
  core_low 128 115792089237316195423570985008687907853269984665640564039457584007913129639935 115792089237316195423570985008687907852929702298719625575994209400481361428480 5 [0, 4, 32, 64, 96, 128, 4, 32, 36, 96, 128, 4, 32, 36, 96, 128, 0, 32, 36, 64, 128, 0, 32, 36, 64, 128, 0, 4, 36, 64, 128, 0, 4, 36, 64, 96, 0, 4, 32, 64, 96, 0, 4, 32, 64, 96, 128, 4, 32, 36, 96, 128, 4, 32, 36, 96, 128, 0, 32, 36, 96, 128, 0, 32, 36, 64, 128, 0, 4, 36, 64, 128, 0, 4, 36, 64, 96, 0, 4, 36, 64, 96, 0, 4, 32, 64, 96, 128, 4, 32, 64, 96, 128, 4, 32, 36, 96, 128, 0, 32, 36, 96, 128, 0, 32, 36, 64, 128, 0, 32, 36, 64, 128, 0, 4, 36, 64, 96, 0, 4, 36, 64, 96, 0, 4, 32, 64, 96, 1, 1, 1, 1, 1, 1, 5, 5, 5, 5, 5, 33, 33, 33, 33, 33, 37, 37, 37, 37, 37, 65, 65, 65, 65, 65, 68, 68, 68, 68, 68, 69, 69, 69, 69, 69, 97, 97, 97, 97, 97, 100, 100, 100, 100, 100, 100, 101, 101, 101, 101, 101, 129, 129, 129, 129, 129, 132, 132, 132, 132, 132, 133, 133, 133, 133, 133, 160, 160, 160, 160, 160, 161, 161, 161, 161, 161, 164, 164, 164, 164, 164, 165, 165, 165, 165, 165, 165, 192, 192, 192, 192, 192, 193, 193, 193, 193, 193, 196, 196, 196, 196, 196, 197, 197, 197, 197, 197, 224, 224, 224, 224, 224, 225, 225, 225, 225, 225, 228, 228, 228, 228, 228, 229, 229, 229, 229, 229] [112283238048308209384853129788267081057926026245577590832725768403185228054528, 115679121345377401726716140441474845312593217133150537687872591763534275422530, 115791978809479959016003661828356135956591609999897346375965142886813310284692, 115792089237210883131903960317530142090861758653719343788137740069125002641944, 115792089237316195423569452513147041964411631678403714325355806106175723832352] _ (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower : Low 10 target :=
  (low_one 1 false (not_good 32 17 0 (by decide +kernel)) (low_one 3 false (not_good 128 17 0 (by decide +kernel)) (low_two 4 (not_good 1 65 0 (by decide +kernel)) (not_good 1 1 0 (by decide +kernel)) core_1 core_2)))

def witness : List Gate := [⟨.or, [0, 2]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [9, 3]⟩, ⟨.or, [10, 8]⟩, ⟨.and, [8, 6]⟩, ⟨.and, [4, 0]⟩, ⟨.and, [1, 9]⟩, ⟨.and, [11, 7]⟩, ⟨.or, [15, 14]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [17, 16]⟩]

theorem witness_ok : ∀ g ∈ witness, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  simp [witness]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem witness_eval : ∀ x : X, Circuit.eval ⟨witness, 18⟩ (List.ofFn x) = target x := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem target_eq : ∀ x : X, target x = decide (∃ i < ([0, 4, 1, 5, 0, 6, 1, 6, 2, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 0, 6, 1, 6, 2, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 0, 6, 1, 6, 2, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide +kernel

end PEqualNP.Outside.L_meta_26066

open PEqualNP.Outside.L_meta_26066 in
theorem PEqualNP.Outside.L_meta_26066 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 0, 6, 1, 6, 2, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 0, 6, 1, 6, 2, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 0, 6, 1, 6, 2, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 0, 6, 1, 6, 2, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 0, 6, 1, 6, 2, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 0, 6, 1, 6, 2, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o hg _ he
  by_cases hs : 11 ≤ gates.length
  · exact ⟨witness, 18, witness_ok, by rw [show witness.length = 11 from rfl]; exact hs,
      fun x => (witness_eval x).trans (target_eq x)⟩
  · exact ⟨gates, o, all_and_or lower gates o hg (by omega)
      (fun x => (he x).trans (target_eq x).symm), le_rfl, he⟩
