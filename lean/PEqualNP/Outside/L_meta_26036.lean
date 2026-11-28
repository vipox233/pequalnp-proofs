import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_26036
open PEqualNP.CircuitLowerBounds

section AbstractReach
variable {α : Type} (opA opO opD : α → α → α)

def Step (L : List α) (s : α) : Prop :=
  ∃ x ∈ L, ∃ y ∈ L, s = opA x y ∨ s = opO x y ∨ s = opD x y

theorem Step.mono {L L' : List α} {s : α} (h : ∀ x ∈ L, x ∈ L') :
    Step opA opO opD L s → Step opA opO opD L' s := by
  rintro ⟨x, hx, y, hy, hop⟩
  exact ⟨x, h x hx, y, h y hy, hop⟩

def Reach (T : α) : ℕ → List α → Prop
  | 0, L => T ∈ L
  | k + 1, L => T ∈ L ∨ ∃ s, Step opA opO opD L s ∧ Reach T k (s :: L)

def ReachF (T : α) : ℕ → List α → List α → Prop
  | 0, L, _ => T ∈ L
  | k + 1, L, F => T ∈ L ∨ ∃ s, Step opA opO opD L s ∧ s ∉ F ∧ s ∉ L ∧ ReachF T k (s :: L) F

theorem Reach.monoL {T : α} : ∀ (k : ℕ) (L L' : List α), (∀ x ∈ L, x ∈ L') →
    Reach opA opO opD T k L → Reach opA opO opD T k L' := by
  intro k; induction k with
  | zero => intro L L' h hr; exact h _ hr
  | succ k ih =>
    intro L L' h hr
    rcases hr with h1 | ⟨s, hs, hr⟩
    · exact Or.inl (h _ h1)
    · refine Or.inr ⟨s, hs.mono opA opO opD h, ih _ _ ?_ hr⟩
      intro x hx; simp only [List.mem_cons] at hx ⊢; exact hx.imp id (h x)

theorem Reach.monoK {T : α} : ∀ (k : ℕ) (L : List α),
    Reach opA opO opD T k L → Reach opA opO opD T (k + 1) L := by
  intro k; induction k with
  | zero => intro L hr; exact Or.inl hr
  | succ k ih =>
    intro L hr
    rcases hr with h1 | ⟨s, hs, hr⟩
    · exact Or.inl h1
    · exact Or.inr ⟨s, hs, ih _ hr⟩

theorem Reach.monoLe {T : α} {k k' : ℕ} (h : k ≤ k') (L : List α)
    (hr : Reach opA opO opD T k L) : Reach opA opO opD T k' L := by
  induction h with
  | refl => exact hr
  | step _ ih => exact Reach.monoK opA opO opD _ L ih

theorem Reach.map {β : Type} (opA' opO' opD' : β → β → β) (φ : α → β)
    (hφ : ∀ x y s, (s = opA x y ∨ s = opO x y ∨ s = opD x y) → ∀ L' : List β,
      φ x ∈ L' → φ y ∈ L' → Step opA' opO' opD' L' (φ s))
    {T : α} : ∀ (k : ℕ) (L : List α),
    Reach opA opO opD T k L → Reach opA' opO' opD' (φ T) k (L.map φ) := by
  intro k; induction k with
  | zero => intro L hr; exact List.mem_map_of_mem hr
  | succ k ih =>
    intro L hr
    rcases hr with h1 | ⟨s, ⟨x, hx, y, hy, hs⟩, hr⟩
    · exact Or.inl (List.mem_map_of_mem h1)
    · exact Or.inr ⟨φ s, hφ x y s hs _ (List.mem_map_of_mem hx) (List.mem_map_of_mem hy), ih _ hr⟩

theorem ReachF.monoK {T : α} : ∀ (k : ℕ) (L F : List α),
    ReachF opA opO opD T k L F → ReachF opA opO opD T (k + 1) L F := by
  intro k; induction k with
  | zero => intro L F hr; exact Or.inl hr
  | succ k ih =>
    intro L F hr
    rcases hr with h1 | ⟨s, hs, hf, hl, hr⟩
    · exact Or.inl h1
    · exact Or.inr ⟨s, hs, hf, hl, ih _ _ hr⟩

theorem ReachF.congrL {T : α} : ∀ (k : ℕ) (L L' F : List α), (∀ x, x ∈ L ↔ x ∈ L') →
    ReachF opA opO opD T k L F → ReachF opA opO opD T k L' F := by
  intro k; induction k with
  | zero => intro L L' F h hr; exact (h _).1 hr
  | succ k ih =>
    intro L L' F h hr
    rcases hr with h1 | ⟨s, hs, hf, hl, hr⟩
    · exact Or.inl ((h _).1 h1)
    · refine Or.inr ⟨s, hs.mono opA opO opD (fun x hx => (h x).1 hx), hf,
        fun hx => hl ((h s).2 hx), ih _ _ _ (fun x => by simp only [List.mem_cons, h x]) hr⟩

theorem Reach.toF {T : α} : ∀ (k : ℕ) (L : List α),
    Reach opA opO opD T k L → ReachF opA opO opD T k L [] := by
  intro k; induction k with
  | zero => intro L hr; exact hr
  | succ k ih =>
    intro L hr
    rcases hr with h1 | ⟨s, hs, hr⟩
    · exact Or.inl h1
    · by_cases hsl : s ∈ L
      · refine ReachF.monoK opA opO opD _ _ _ (ih L (Reach.monoL opA opO opD _ _ _ ?_ hr))
        intro x hx; rcases List.mem_cons.mp hx with rfl | hx; exact hsl; exact hx
      · exact Or.inr ⟨s, hs, List.not_mem_nil, hsl, ih _ hr⟩

theorem ReachF.split {T c : α} : ∀ (k : ℕ) (L F : List α), Step opA opO opD L c → c ∉ L →
    ReachF opA opO opD T k L F →
    ReachF opA opO opD T k L (c :: F) ∨ ∃ k', k = k' + 1 ∧ ReachF opA opO opD T k' (c :: L) F := by
  intro k; induction k with
  | zero => intro L F _ _ hr; exact Or.inl hr
  | succ k ih =>
    intro L F hc hcL hr
    rcases hr with h1 | ⟨s, hs, hf, hl, hr⟩
    · exact Or.inl (Or.inl h1)
    · by_cases hsc : s = c
      · subst hsc; exact Or.inr ⟨k, rfl, hr⟩
      · have hc' : Step opA opO opD (s :: L) c := hc.mono opA opO opD (fun x hx => List.mem_cons_of_mem _ hx)
        have hcL' : c ∉ s :: L := fun hx => by
          rcases List.mem_cons.mp hx with h | h; exact hsc h.symm; exact hcL h
        rcases ih (s :: L) F hc' hcL' hr with h | ⟨k', hk, h⟩
        · refine Or.inl (Or.inr ⟨s, hs, fun hx => ?_, hl, h⟩)
          rcases List.mem_cons.mp hx with h | h; exact hsc h; exact hf h
        · refine Or.inr ⟨k, rfl, ?_⟩
          rw [hk]
          refine Or.inr ⟨s, hs.mono opA opO opD (fun x hx => List.mem_cons_of_mem _ hx), hf,
            fun hx => ?_, ReachF.congrL opA opO opD _ _ _ _ (fun x => by simp only [List.mem_cons]; tauto) h⟩
          rcases List.mem_cons.mp hx with h | h; exact hsc h; exact hl h
end AbstractReach

abbrev BF (n : ℕ) := (Fin n → Bool) → Bool
abbrev bSub (a b : Bool) : Bool := a && !b
def z0 (n : ℕ) : Fin n → Bool := fun _ => false
def f0 (n : ℕ) : BF n := fun _ => false
def fV {n : ℕ} (p : Fin n) : BF n := fun x => x p
def fBin {n : ℕ} (c : Bool → Bool → Bool) (a b : BF n) : BF n := fun x => c (a x) (b x)
abbrev fAnd {n : ℕ} : BF n → BF n → BF n := fBin and
abbrev fOr  {n : ℕ} : BF n → BF n → BF n := fBin or
abbrev fSub {n : ℕ} : BF n → BF n → BF n := fBin bSub
abbrev BR {n : ℕ} (f : BF n) (k : ℕ) (L : List (BF n)) : Prop := Reach fAnd fOr fSub f k L
def bank0 (n : ℕ) : List (BF n) := f0 n :: List.ofFn (fun p : Fin n => fV p)

def proj {n : ℕ} (u : (Fin n → Bool) → (Fin n → Bool)) (g : BF n) : BF n :=
  fun x => xor (g (u x)) (g (u (z0 n)))
abbrev norm {n : ℕ} (g : BF n) : BF n := proj id g

theorem xor_bin_cases (c : Bool → Bool → Bool) (hc : c = and ∨ c = or ∨ c = bSub) (a0 b0 : Bool) :
    (∀ a b : Bool, xor (c a b) (c a0 b0) = and (xor a a0) (xor b b0)) ∨
    (∀ a b : Bool, xor (c a b) (c a0 b0) = or (xor a a0) (xor b b0)) ∨
    (∀ a b : Bool, xor (c a b) (c a0 b0) = bSub (xor a a0) (xor b b0)) ∨
    (∀ a b : Bool, xor (c a b) (c a0 b0) = bSub (xor b b0) (xor a a0)) := by
  rcases hc with rfl | rfl | rfl <;> cases a0 <;> cases b0 <;> decide

theorem proj_step {n : ℕ} (u : (Fin n → Bool) → (Fin n → Bool)) (c : Bool → Bool → Bool)
    (hc : c = and ∨ c = or ∨ c = bSub) (X Y : BF n) (L : List (BF n))
    (hX : proj u X ∈ L) (hY : proj u Y ∈ L) : Step fAnd fOr fSub L (proj u (fBin c X Y)) := by
  rcases xor_bin_cases c hc (X (u (z0 n))) (Y (u (z0 n))) with h | h | h | h
  · exact ⟨_, hX, _, hY, Or.inl (funext fun z => h _ _)⟩
  · exact ⟨_, hX, _, hY, Or.inr (Or.inl (funext fun z => h _ _))⟩
  · exact ⟨_, hX, _, hY, Or.inr (Or.inr (funext fun z => h _ _))⟩
  · exact ⟨_, hY, _, hX, Or.inr (Or.inr (funext fun z => h _ _))⟩

theorem proj_pres {n : ℕ} (u : (Fin n → Bool) → (Fin n → Bool)) (x y s : BF n)
    (hs : s = fAnd x y ∨ s = fOr x y ∨ s = fSub x y) (L : List (BF n))
    (hX : proj u x ∈ L) (hY : proj u y ∈ L) : Step fAnd fOr fSub L (proj u s) := by
  rcases hs with rfl | rfl | rfl
  · exact proj_step u and (Or.inl rfl) x y L hX hY
  · exact proj_step u or (Or.inr (Or.inl rfl)) x y L hX hY
  · exact proj_step u bSub (Or.inr (Or.inr rfl)) x y L hX hY

def upd {n : ℕ} (p : Fin n) (b : Bool) (x : Fin n → Bool) : Fin n → Bool :=
  fun i => if i = p then b else x i
def subst {n : ℕ} (p : Fin n) (b : Bool) (g : BF n) : BF n := fun x => g (upd p b x)
def restr {n : ℕ} (p : Fin n) (b : Bool) (g : BF n) : BF n := proj (upd p b) g
def Indep {n : ℕ} (p : Fin n) (g : BF n) : Prop := (∀ b, subst p b g = g) ∧ g (z0 n) = false
def Clean {n : ℕ} (p : Fin n) (L : List (BF n)) : Prop :=
  f0 n ∈ L ∧ ∀ g ∈ L, g = fV p ∨ Indep p g

theorem indep_restr {n : ℕ} {p : Fin n} {g : BF n} (h : Indep p g) (b : Bool) :
    restr p b g = g := by
  funext x
  have h1 := congrFun (h.1 b) x
  have h2 := congrFun (h.1 b) (z0 n)
  simp only [subst] at h1 h2
  show xor (g (upd p b x)) (g (upd p b (z0 n))) = g x
  rw [h1, h2, h.2]; cases g x <;> rfl

theorem restr_var {n : ℕ} (p : Fin n) (b : Bool) : restr p b (fV p) = f0 n := by
  funext x; show xor (upd p b x p) (upd p b (z0 n) p) = false; simp [upd]

theorem indep_bin {n : ℕ} {p : Fin n} (c : Bool → Bool → Bool) (hc0 : c false false = false)
    {x y : BF n} (hx : Indep p x) (hy : Indep p y) : Indep p (fBin c x y) :=
  ⟨fun b => by show fBin c (subst p b x) (subst p b y) = _; rw [hx.1 b, hy.1 b],
   by show c (x (z0 n)) (y (z0 n)) = false; rw [hx.2, hy.2, hc0]⟩

theorem xor_eq_false_imp {a b : Bool} (h : xor a b = false) : a = b := by
  cases a <;> cases b <;> simp_all

theorem un_inj_xor (g : Bool → Bool) (h : g true ≠ g false) (a b : Bool) :
    xor (g a) (g b) = xor a b := by
  cases ha : g true <;> cases hb : g false <;> cases a <;> cases b <;> simp_all

theorem absorb_l {n : ℕ} (u : (Fin n → Bool) → (Fin n → Bool)) (c : Bool → Bool → Bool)
    (X Y : BF n) (h : proj u X = f0 n) :
    proj u (fBin c X Y) = f0 n ∨ proj u (fBin c X Y) = proj u Y := by
  have hX : ∀ z, X (u z) = X (u (z0 n)) := fun z => xor_eq_false_imp (congrFun h z)
  by_cases hcc : c (X (u (z0 n))) true = c (X (u (z0 n))) false
  · left; funext z
    show xor (c (X (u z)) (Y (u z))) (c (X (u (z0 n))) (Y (u (z0 n)))) = false
    rw [hX z]; cases Y (u z) <;> cases Y (u (z0 n)) <;> simp [hcc]
  · right; funext z
    show xor (c (X (u z)) (Y (u z))) (c (X (u (z0 n))) (Y (u (z0 n)))) = xor (Y (u z)) (Y (u (z0 n)))
    rw [hX z]; exact un_inj_xor (c (X (u (z0 n)))) hcc _ _

theorem absorb_r {n : ℕ} (u : (Fin n → Bool) → (Fin n → Bool)) (c : Bool → Bool → Bool)
    (X Y : BF n) (h : proj u Y = f0 n) :
    proj u (fBin c X Y) = f0 n ∨ proj u (fBin c X Y) = proj u X :=
  absorb_l u (fun a b => c b a) Y X h

theorem Clean.cons {n : ℕ} {p : Fin n} {L : List (BF n)} (h : Clean p L) {t : BF n}
    (ht : Indep p t) : Clean p (t :: L) :=
  ⟨List.mem_cons_of_mem _ h.1, fun g hg => by
    rcases List.mem_cons.mp hg with rfl | hg; exact Or.inr ht; exact h.2 g hg⟩

theorem elimDead {n : ℕ} (p : Fin n) (b : Bool) (f : BF n) (h1 : restr p b f ≠ f0 n)
    (h3 : ¬ ∀ b, subst p b f = f) : ∀ (k : ℕ) (L : List (BF n)) (s : BF n),
    Clean p L → restr p b s = f0 n → BR f k (s :: L) →
    ∃ k', k = k' + 1 ∧ BR (restr p b f) k' L := by
  have hno : ∀ (L : List (BF n)) (s : BF n), Clean p L → restr p b s = f0 n → f ∈ s :: L → False := by
    intro L s hC hs hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact h1 hs
    · rcases hC.2 f hf with rfl | h; exact h1 (restr_var p b); exact h3 h.1
  intro k; induction k with
  | zero => intro L s hC hs hr; exact (hno L s hC hs hr).elim
  | succ k ih =>
    intro L s hC hs hr
    rcases hr with hr | ⟨t, ⟨x, hx, y, hy, ht⟩, hr⟩
    · exact (hno L s hC hs hr).elim
    · have cls : ∀ z ∈ s :: L, restr p b z = f0 n ∨ (z ∈ L ∧ Indep p z) := by
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact Or.inl hs
        · rcases hC.2 z hz with rfl | hi; exact Or.inl (restr_var p b); exact Or.inr ⟨hz, hi⟩
      have rmem : ∀ z ∈ s :: L, restr p b z ∈ L := fun z hz => by
        rcases cls z hz with h | ⟨h, hi⟩
        · rw [h]; exact hC.1
        · rw [indep_restr hi b]; exact h
      have red : restr p b t ∈ L → ∃ k', k + 1 = k' + 1 ∧ BR (restr p b f) k' L := fun htL => by
        refine ⟨k, rfl, Reach.monoL fAnd fOr fSub _ _ _ ?_
          (Reach.map fAnd fOr fSub fAnd fOr fSub (restr p b) (proj_pres (upd p b)) k _ hr)⟩
        intro z hz; obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
        rcases List.mem_cons.mp hw with rfl | hw; exact htL; exact rmem w hw
      have step : ∀ c : Bool → Bool → Bool, c false false = false → t = fBin c x y →
          (x ∈ L → y ∈ L → Step fAnd fOr fSub L t) →
          ∃ k', k + 1 = k' + 1 ∧ BR (restr p b f) k' L := by
        intro c hc0 e hstep
        rcases cls x hx with hxc | ⟨hxL, hxi⟩
        · apply red; rw [e]; unfold restr
          rcases absorb_l (upd p b) c x y hxc with h | h
          · rw [h]; exact hC.1
          · rw [h]; exact rmem y hy
        · rcases cls y hy with hyc | ⟨hyL, hyi⟩
          · apply red; rw [e]; unfold restr
            rcases absorb_r (upd p b) c x y hyc with h | h
            · rw [h]; exact hC.1
            · rw [h]; exact rmem x hx
          · have hr' : BR f k (s :: t :: L) := Reach.monoL fAnd fOr fSub _ _ _
              (fun z hz => by simp only [List.mem_cons] at hz ⊢; tauto) hr
            obtain ⟨k', rfl, h⟩ := ih (t :: L) s (hC.cons (e ▸ indep_bin c hc0 hxi hyi)) hs hr'
            exact ⟨k' + 1, rfl, Or.inr ⟨t, hstep hxL hyL, h⟩⟩
      rcases ht with e | e | e
      · exact step and rfl e (fun a b => ⟨x, a, y, b, Or.inl e⟩)
      · exact step or rfl e (fun a b => ⟨x, a, y, b, Or.inr (Or.inl e)⟩)
      · exact step bSub rfl e (fun a b => ⟨x, a, y, b, Or.inr (Or.inr e)⟩)

theorem elim1 {n : ℕ} (p : Fin n) (b : Bool) (f : BF n) (h1 : restr p b f ≠ f0 n)
    (h3 : ¬ ∀ b, subst p b f = f) (k : ℕ) (L : List (BF n)) (hC : Clean p L)
    (hr : BR f k L) : ∃ k', k = k' + 1 ∧ BR (restr p b f) k' L :=
  elimDead p b f h1 h3 k L (f0 n) hC rfl
    (Reach.monoL fAnd fOr fSub _ _ _ (fun _ h => List.mem_cons_of_mem _ h) hr)

theorem kill_l {n : ℕ} (p : Fin n) (b : Bool) (c : Bool → Bool → Bool)
    (hc : c b true = c b false) (y : BF n) : restr p b (fBin c (fV p) y) = f0 n := by
  funext z; show xor (c (upd p b z p) (y (upd p b z))) (c (upd p b (z0 n) p) (y (upd p b (z0 n)))) = false
  simp only [upd, ite_true]; cases y (upd p b z) <;> cases y (upd p b (z0 n)) <;> simp [hc]

theorem kill_r {n : ℕ} (p : Fin n) (b : Bool) (c : Bool → Bool → Bool)
    (hc : c true b = c false b) (y : BF n) : restr p b (fBin c y (fV p)) = f0 n :=
  kill_l p b (fun a d => c d a) hc y

theorem elim2 {n : ℕ} (p : Fin n) (f : BF n) (h0 : restr p false f ≠ f0 n)
    (h1 : restr p true f ≠ f0 n) (h3 : ¬ ∀ b, subst p b f = f) :
    ∀ (k : ℕ) (L : List (BF n)), Clean p L → BR f k L →
    ∃ k', k = k' + 2 ∧ (BR (restr p false f) k' L ∨ BR (restr p true f) k' L) := by
  have hno : ∀ (L : List (BF n)), Clean p L → f ∈ L → False := fun L hC hf => by
    rcases hC.2 f hf with rfl | h; exact h0 (restr_var p false); exact h3 h.1
  intro k; induction k with
  | zero => intro L hC hr; exact (hno L hC hr).elim
  | succ k ih =>
    intro L hC hr
    rcases hr with hr | ⟨t, ⟨x, hx, y, hy, ht⟩, hr⟩
    · exact (hno L hC hr).elim
    · have kill : ∀ b : Bool, restr p b t = f0 n → ∃ k', k + 1 = k' + 2 ∧
          (BR (restr p false f) k' L ∨ BR (restr p true f) k' L) := by
        intro b hc; cases b
        · obtain ⟨k', rfl, h⟩ := elimDead p false f h0 h3 k L t hC hc hr; exact ⟨k', rfl, Or.inl h⟩
        · obtain ⟨k', rfl, h⟩ := elimDead p true f h1 h3 k L t hC hc hr; exact ⟨k', rfl, Or.inr h⟩
      have step : ∀ (c : Bool → Bool → Bool) (bl br : Bool), c false false = false →
          c bl true = c bl false → c true br = c false br → t = fBin c x y →
          ∃ k', k + 1 = k' + 2 ∧ (BR (restr p false f) k' L ∨ BR (restr p true f) k' L) := by
        intro c bl br hc0 hl hrr e
        rcases hC.2 x hx with rfl | hxi
        · exact kill bl (e ▸ kill_l p bl c hl y)
        · rcases hC.2 y hy with rfl | hyi
          · exact kill br (e ▸ kill_r p br c hrr x)
          · obtain ⟨k', rfl, h⟩ := ih (t :: L) (hC.cons (e ▸ indep_bin c hc0 hxi hyi)) hr
            refine ⟨k' + 1, rfl, ?_⟩
            rcases h with h | h
            · exact Or.inl (Or.inr ⟨t, ⟨x, hx, y, hy, ht⟩, h⟩)
            · exact Or.inr (Or.inr ⟨t, ⟨x, hx, y, hy, ht⟩, h⟩)
      rcases ht with e | e | e
      · exact step and false false rfl rfl rfl e
      · exact step or true true rfl rfl rfl e
      · exact step bSub false true rfl rfl rfl e

theorem clean_bank0 {n : ℕ} (p : Fin n) : Clean p (bank0 n) := by
  refine ⟨List.mem_cons_self, fun g hg => ?_⟩
  rcases List.mem_cons.mp hg with rfl | hg
  · exact Or.inr ⟨fun _ => rfl, rfl⟩
  · obtain ⟨q, rfl⟩ := (List.mem_ofFn' _ _).mp hg
    by_cases hq : q = p
    · exact Or.inl (hq ▸ rfl)
    · exact Or.inr ⟨fun b => funext fun z => by simp [subst, upd, fV, hq], rfl⟩

theorem ne_f0 {n : ℕ} (g : BF n) (x : Fin n → Bool) (h : g x = true) : g ≠ f0 n :=
  fun e => by rw [e] at h; exact Bool.noConfusion h

theorem dep_of {n : ℕ} (p : Fin n) (g : BF n) (x : Fin n → Bool)
    (h : (subst p false g x != subst p true g x) = true) : ¬ ∀ b, subst p b g = g :=
  fun hi => by rw [hi false, hi true] at h; simp at h

def pt {n : ℕ} (m : ℕ) : Fin n → Bool := fun i => m.testBit i.val

def encodeFin {n : ℕ} (x : Fin n → Bool) : ℕ :=
  Nat.rec (motive := fun k => (Fin k → Bool) → ℕ) (fun _ => 0)
    (fun k ih f => (if f ⟨0, Nat.zero_lt_succ k⟩ then 1 else 0) + 2 * ih (fun i => f i.succ)) n x

theorem testBit_encodeFin {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (encodeFin x).testBit i.val = x i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    cases i using Fin.cases with
    | zero =>
      change ((if x 0 then 1 else 0) + 2 * encodeFin (fun j => x j.succ)).testBit 0 = x 0
      cases x 0 <;> simp [Nat.testBit_zero]
    | succ j =>
      change ((if x 0 then 1 else 0) + 2 * encodeFin (fun j => x j.succ)).testBit (j.val + 1) = x j.succ
      have hdiv : ((if x 0 then 1 else 0) + 2 * encodeFin (fun j => x j.succ)) / 2 = encodeFin (fun j => x j.succ) := by
        cases x 0
        · simp only [Bool.false_eq_true, ite_false]; omega
        · simp only [ite_true]; omega
      rw [Nat.testBit_succ, hdiv, ih]

theorem encodeFin_lt {n : ℕ} (x : Fin n → Bool) : encodeFin x < 2 ^ n := by
  induction n with
  | zero => simp [encodeFin]
  | succ k ih =>
    change (if x 0 then 1 else 0) + 2 * encodeFin (fun j => x j.succ) < 2 ^ (k + 1)
    have h := ih (fun j => x j.succ)
    rw [Nat.pow_succ]; cases x 0
    · simp only [Bool.false_eq_true, ite_false]; omega
    · simp only [ite_true]; omega

theorem all_pts {n : ℕ} (P : (Fin n → Bool) → Prop) (h : ∀ m < 2 ^ n, P (pt m)) :
    ∀ x : Fin n → Bool, P x := fun x => by
  have e : x = pt (encodeFin x) := funext fun i => (testBit_encodeFin x i).symm
  rw [e]; exact h _ (encodeFin_lt x)

def bsub (FULL x y : ℕ) : ℕ := Nat.land x (Nat.xor FULL y)
abbrev NStep (FULL : ℕ) (L : List ℕ) (s : ℕ) : Prop := Step Nat.land Nat.lor (bsub FULL) L s
abbrev NReach (FULL T k : ℕ) (L : List ℕ) : Prop := Reach Nat.land Nat.lor (bsub FULL) T k L
abbrev NReachF (FULL T k : ℕ) (L F : List ℕ) : Prop := ReachF Nat.land Nat.lor (bsub FULL) T k L F

theorem land_comm (x y : ℕ) : Nat.land x y = Nat.land y x := Nat.and_comm x y
theorem land_self (x : ℕ) : Nat.land x x = x := Nat.and_self x
theorem lor_comm (x y : ℕ) : Nat.lor x y = Nat.lor y x := Nat.or_comm x y
theorem lor_self (x : ℕ) : Nat.lor x x = x := Nat.or_self x

def memb (a : ℕ) : List ℕ → Bool
  | [] => false
  | b :: l => cond (Nat.beq a b) true (memb a l)

theorem memb_iff {a : ℕ} {l : List ℕ} : memb a l = true ↔ a ∈ l := by
  induction l with
  | nil => simp [memb]
  | cons b l ih =>
    simp only [memb, List.mem_cons]
    by_cases h : a = b
    · subst h; rw [Nat.beq_refl]; simp
    · have hf : Nat.beq a b = false := by rw [← Bool.not_eq_true]; exact fun hb => h (Nat.eq_of_beq_eq_true hb)
      rw [hf]; simp [ih, h]

def cands2 (FULL : ℕ) : List ℕ → List ℕ
  | [] => []
  | x :: l => l.flatMap (fun y => [Nat.land x y, Nat.lor x y, bsub FULL x y, bsub FULL y x]) ++ cands2 FULL l

def cands (FULL : ℕ) (L : List ℕ) : List ℕ := L.map (fun x => bsub FULL x x) ++ cands2 FULL L

theorem cands2_sound {FULL : ℕ} : ∀ {L : List ℕ} {s : ℕ}, s ∈ cands2 FULL L → NStep FULL L s := by
  intro L; induction L with
  | nil => intro s hs; exact absurd hs List.not_mem_nil
  | cons x l ih =>
    intro s hs
    rcases List.mem_append.mp hs with h | h
    · obtain ⟨y, hy, h⟩ := List.mem_flatMap.mp h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      have hx' : x ∈ x :: l := List.mem_cons_self
      have hy' : y ∈ x :: l := List.mem_cons_of_mem _ hy
      rcases h with rfl | rfl | rfl | rfl
      · exact ⟨x, hx', y, hy', Or.inl rfl⟩
      · exact ⟨x, hx', y, hy', Or.inr (Or.inl rfl)⟩
      · exact ⟨x, hx', y, hy', Or.inr (Or.inr rfl)⟩
      · exact ⟨y, hy', x, hx', Or.inr (Or.inr rfl)⟩
    · exact (ih h).mono _ _ _ (fun _ hz => List.mem_cons_of_mem _ hz)

theorem cands_sound {FULL : ℕ} {L : List ℕ} {s : ℕ} (h : s ∈ cands FULL L) : NStep FULL L s := by
  rcases List.mem_append.mp h with h | h
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h; exact ⟨x, hx, x, hx, Or.inr (Or.inr rfl)⟩
  · exact cands2_sound h

theorem cands2_complete {FULL : ℕ} : ∀ {L : List ℕ} {x y s : ℕ}, x ∈ L → y ∈ L → x ≠ y →
    (s = Nat.land x y ∨ s = Nat.lor x y ∨ s = bsub FULL x y) → s ∈ cands2 FULL L := by
  intro L; induction L with
  | nil => intro _ _ _ hx; exact absurd hx List.not_mem_nil
  | cons a l ih =>
    intro x y s hx hy hne hop
    rcases List.mem_cons.mp hx with hxa | hxl
    · subst hxa
      rcases List.mem_cons.mp hy with hya | hyl
      · exact absurd hya.symm hne
      · refine List.mem_append_left _ (List.mem_flatMap.mpr ⟨y, hyl, ?_⟩)
        simp only [List.mem_cons, List.not_mem_nil, or_false]; rcases hop with rfl | rfl | rfl <;> tauto
    · rcases List.mem_cons.mp hy with hya | hyl
      · subst hya
        refine List.mem_append_left _ (List.mem_flatMap.mpr ⟨x, hxl, ?_⟩)
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rcases hop with rfl | rfl | rfl
        · left; exact land_comm x y
        · right; left; exact lor_comm x y
        · right; right; right; rfl
      · exact List.mem_append_right _ (ih hxl hyl hne hop)

theorem cands_complete {FULL : ℕ} {L : List ℕ} {s : ℕ} (h : NStep FULL L s) (hs : s ∉ L) :
    s ∈ cands FULL L := by
  obtain ⟨x, hx, y, hy, hop⟩ := h
  by_cases hxy : x = y
  · subst hxy
    rcases hop with rfl | rfl | rfl
    · rw [land_self] at hs; exact absurd hx hs
    · rw [lor_self] at hs; exact absurd hx hs
    · exact List.mem_append_left _ (List.mem_map.mpr ⟨x, hx, rfl⟩)
  · exact List.mem_append_right _ (cands2_complete hx hy hxy hop)

theorem nat_beq_eq_true {a b : ℕ} (h : a = b) : Nat.beq a b = true := by subst h; exact Nat.beq_refl _

theorem land_sub1 (x y : ℕ) : Nat.beq (Nat.land (Nat.land x y) x) (Nat.land x y) = true := by
  apply nat_beq_eq_true; apply Nat.eq_of_testBit_eq; intro i
  show ((x &&& y) &&& x).testBit i = (x &&& y).testBit i
  simp only [Nat.testBit_and]; cases x.testBit i <;> cases y.testBit i <;> rfl

theorem land_sub2 (x y : ℕ) : Nat.beq (Nat.land (Nat.land x y) y) (Nat.land x y) = true := by
  rw [land_comm x y]; exact land_sub1 y x

theorem lor_sub1 (x y : ℕ) : Nat.beq (Nat.lor (Nat.lor x y) x) (Nat.lor x y) = true := by
  apply nat_beq_eq_true; apply Nat.eq_of_testBit_eq; intro i
  show ((x ||| y) ||| x).testBit i = (x ||| y).testBit i
  simp only [Nat.testBit_or]; cases x.testBit i <;> cases y.testBit i <;> rfl

theorem lor_sub2 (x y : ℕ) : Nat.beq (Nat.lor (Nat.lor x y) y) (Nat.lor x y) = true := by
  rw [lor_comm x y]; exact lor_sub1 y x

theorem bsub_sub (FULL x y : ℕ) : Nat.beq (Nat.land (bsub FULL x y) x) (bsub FULL x y) = true := by
  apply nat_beq_eq_true; apply Nat.eq_of_testBit_eq; intro i
  show ((x &&& (FULL ^^^ y)) &&& x).testBit i = (x &&& (FULL ^^^ y)).testBit i
  simp only [Nat.testBit_and]; cases x.testBit i <;> cases (FULL ^^^ y).testBit i <;> rfl

def upOf (T : ℕ) (L : List ℕ) : List ℕ := L.filter (fun w => Nat.beq (Nat.land T w) T)
def dnOf (T : ℕ) (L : List ℕ) : List ℕ := L.filter (fun w => Nat.beq (Nat.lor T w) T)

def check1 (FULL T : ℕ) (L up dn : List ℕ) : Bool :=
  up.any (fun x => up.any (fun y => Nat.beq (Nat.land x y) T) || L.any (fun y => Nat.beq (bsub FULL x y) T)) ||
  dn.any (fun x => dn.any (fun y => Nat.beq (Nat.lor x y) T))

theorem check1_complete {FULL T : ℕ} {L : List ℕ} (h : NStep FULL L T) :
    check1 FULL T L (upOf T L) (dnOf T L) = true := by
  obtain ⟨x, hx, y, hy, hop⟩ := h
  unfold check1
  rcases hop with rfl | rfl | rfl
  · rw [Bool.or_eq_true]; left; rw [List.any_eq_true]
    refine ⟨x, List.mem_filter.mpr ⟨hx, land_sub1 x y⟩, ?_⟩
    rw [Bool.or_eq_true]; left; rw [List.any_eq_true]
    exact ⟨y, List.mem_filter.mpr ⟨hy, land_sub2 x y⟩, Nat.beq_refl _⟩
  · rw [Bool.or_eq_true]; right; rw [List.any_eq_true]
    refine ⟨x, List.mem_filter.mpr ⟨hx, lor_sub1 x y⟩, ?_⟩
    rw [List.any_eq_true]
    exact ⟨y, List.mem_filter.mpr ⟨hy, lor_sub2 x y⟩, Nat.beq_refl _⟩
  · rw [Bool.or_eq_true]; left; rw [List.any_eq_true]
    refine ⟨x, List.mem_filter.mpr ⟨hx, bsub_sub FULL x y⟩, ?_⟩
    rw [Bool.or_eq_true]; right; rw [List.any_eq_true]
    exact ⟨y, hy, Nat.beq_refl _⟩

def hitWith (FULL T : ℕ) (L up dn : List ℕ) (s : ℕ) : Bool :=
  (Nat.beq (Nat.land T s) T &&
    (up.any (fun y => Nat.beq (Nat.land s y) T) ||
     L.any (fun y => Nat.beq (bsub FULL s y) T) ||
     Nat.beq (bsub FULL s s) T)) ||
  (Nat.beq (Nat.lor T s) T && dn.any (fun y => Nat.beq (Nat.lor s y) T)) ||
  up.any (fun x => Nat.beq (bsub FULL x s) T)

def check2 (FULL T : ℕ) (L : List ℕ) : Bool :=
  let up := upOf T L; let dn := dnOf T L
  cond (check1 FULL T L up dn) true ((cands FULL L).any (hitWith FULL T L up dn))

theorem check2_complete {FULL T : ℕ} {L F : List ℕ} (hT : T ∉ L) (h : NReachF FULL T 2 L F) :
    check2 FULL T L = true := by
  rcases h with h | ⟨s, hc, _, hl, hr⟩
  · exact absurd h hT
  · have left : NStep FULL L T → check2 FULL T L = true := fun h => by
      unfold check2; dsimp only; rw [check1_complete h]; rfl
    have key : hitWith FULL T L (upOf T L) (dnOf T L) s = true → check2 FULL T L = true := fun h => by
      have ha : (cands FULL L).any (hitWith FULL T L (upOf T L) (dnOf T L)) = true :=
        List.any_eq_true.mpr ⟨s, cands_complete hc hl, h⟩
      unfold check2; dsimp only; rw [ha]; cases check1 FULL T L (upOf T L) (dnOf T L) <;> rfl
    have kA : ∀ y ∈ L, T = Nat.land s y → check2 FULL T L = true := fun y hy h => by
      apply key; subst h; unfold hitWith
      rw [Bool.or_eq_true, Bool.or_eq_true]; left; left
      rw [Bool.and_eq_true]; refine ⟨land_sub1 s y, ?_⟩
      rw [Bool.or_eq_true, Bool.or_eq_true]; left; left
      exact List.any_eq_true.mpr ⟨y, List.mem_filter.mpr ⟨hy, land_sub2 s y⟩, Nat.beq_refl _⟩
    have kO : ∀ y ∈ L, T = Nat.lor s y → check2 FULL T L = true := fun y hy h => by
      apply key; subst h; unfold hitWith
      rw [Bool.or_eq_true, Bool.or_eq_true]; left; right
      rw [Bool.and_eq_true]; refine ⟨lor_sub1 s y, ?_⟩
      exact List.any_eq_true.mpr ⟨y, List.mem_filter.mpr ⟨hy, lor_sub2 s y⟩, Nat.beq_refl _⟩
    have kD1 : ∀ y ∈ L, T = bsub FULL s y → check2 FULL T L = true := fun y hy h => by
      apply key; subst h; unfold hitWith
      rw [Bool.or_eq_true, Bool.or_eq_true]; left; left
      rw [Bool.and_eq_true]; refine ⟨bsub_sub FULL s y, ?_⟩
      rw [Bool.or_eq_true, Bool.or_eq_true]; left; right
      exact List.any_eq_true.mpr ⟨y, hy, Nat.beq_refl _⟩
    have kD2 : ∀ x ∈ L, T = bsub FULL x s → check2 FULL T L = true := fun x hx h => by
      apply key; subst h; unfold hitWith
      rw [Bool.or_eq_true]; right
      exact List.any_eq_true.mpr ⟨x, List.mem_filter.mpr ⟨hx, bsub_sub FULL x s⟩, Nat.beq_refl _⟩
    have kD3 : T = bsub FULL s s → check2 FULL T L = true := fun h => by
      apply key; subst h; unfold hitWith
      rw [Bool.or_eq_true, Bool.or_eq_true]; left; left
      rw [Bool.and_eq_true]; refine ⟨bsub_sub FULL s s, ?_⟩
      rw [Bool.or_eq_true]; right; exact Nat.beq_refl _
    rcases hr with h | ⟨s2, hc2, _, _, hr2⟩
    · rcases List.mem_cons.mp h with rfl | h; exact left hc; exact absurd h hT
    · rcases List.mem_cons.mp hr2 with rfl | h
      · obtain ⟨x, hx, y, hy, hop⟩ := hc2
        rcases hop with hop | hop | hop
        · rcases List.mem_cons.mp hx with hxs | hxL
          · subst hxs
            rcases List.mem_cons.mp hy with hys | hyL
            · subst hys; rw [land_self] at hop; exact left (hop ▸ hc)
            · exact kA y hyL hop
          · rcases List.mem_cons.mp hy with hys | hyL
            · subst hys; exact kA x hxL (hop.trans (land_comm x y))
            · exact left ⟨x, hxL, y, hyL, Or.inl hop⟩
        · rcases List.mem_cons.mp hx with hxs | hxL
          · subst hxs
            rcases List.mem_cons.mp hy with hys | hyL
            · subst hys; rw [lor_self] at hop; exact left (hop ▸ hc)
            · exact kO y hyL hop
          · rcases List.mem_cons.mp hy with hys | hyL
            · subst hys; exact kO x hxL (hop.trans (lor_comm x y))
            · exact left ⟨x, hxL, y, hyL, Or.inr (Or.inl hop)⟩
        · rcases List.mem_cons.mp hx with hxs | hxL
          · subst hxs
            rcases List.mem_cons.mp hy with hys | hyL
            · subst hys; exact kD3 hop
            · exact kD1 y hyL hop
          · rcases List.mem_cons.mp hy with hys | hyL
            · subst hys; exact kD2 x hxL hop
            · exact left ⟨x, hxL, y, hyL, Or.inr (Or.inr hop)⟩
      · rcases List.mem_cons.mp h with rfl | h; exact left hc; exact absurd h hT

def loop (f : ℕ → List ℕ → Bool) (L : List ℕ) : List ℕ → List ℕ → Bool
  | [], _ => false
  | c :: cs, F =>
    cond (memb c L) (loop f L cs F)
      (cond (memb c F) (loop f L cs F)
        (cond (f c F) true (loop f L cs (c :: F))))

def chk (FULL T : ℕ) : ℕ → List ℕ → List ℕ → Bool
  | 0, L, _ => memb T L
  | 1, L, _ => cond (memb T L) true (check1 FULL T L (upOf T L) (dnOf T L))
  | 2, L, _ => cond (memb T L) true (check2 FULL T L)
  | k + 3, L, F => cond (memb T L) true (loop (fun c F' => chk FULL T (k + 2) (c :: L) F') L (cands FULL L) F)

theorem loop_complete {FULL T : ℕ} (L : List ℕ) (f : ℕ → List ℕ → Bool) (k : ℕ)
    (ih : ∀ c F, NReachF FULL T k (c :: L) F → f c F = true) (hT : T ∉ L) :
    ∀ (cs F : List ℕ), (∀ c ∈ cs, NStep FULL L c) →
      (∀ s, NStep FULL L s → s ∉ L → s ∉ F → s ∈ cs) →
      NReachF FULL T (k + 1) L F → loop f L cs F = true := by
  intro cs; induction cs with
  | nil =>
    intro F _ hcpl hr
    rcases hr with h | ⟨s, hc, hf, hl, _⟩
    · exact absurd h hT
    · exact absurd (hcpl s hc hl hf) List.not_mem_nil
  | cons c cs ihc =>
    intro F hs hcpl hr
    have hs' : ∀ x ∈ cs, NStep FULL L x := fun x hx => hs x (List.mem_cons_of_mem _ hx)
    unfold loop
    have skip : c ∈ L ∨ c ∈ F → loop f L cs F = true := fun hin =>
      ihc F hs' (fun s hc hl hf => by
        rcases List.mem_cons.mp (hcpl s hc hl hf) with rfl | h
        · rcases hin with h | h; exact absurd h hl; exact absurd h hf
        · exact h) hr
    by_cases hcL : c ∈ L
    · rw [memb_iff.2 hcL]; exact skip (Or.inl hcL)
    · have hm : memb c L = false := by rw [← Bool.not_eq_true, memb_iff]; exact hcL
      rw [hm]
      by_cases hcF : c ∈ F
      · rw [memb_iff.2 hcF]; exact skip (Or.inr hcF)
      · have hm2 : memb c F = false := by rw [← Bool.not_eq_true, memb_iff]; exact hcF
        rw [hm2]
        rcases ReachF.split Nat.land Nat.lor (bsub FULL) _ _ _ (hs c List.mem_cons_self) hcL hr with h | ⟨k', hk, h⟩
        · have hl := ihc (c :: F) hs' (fun s hc hl hf => by
            rcases List.mem_cons.mp (hcpl s hc hl (fun hx => hf (List.mem_cons_of_mem _ hx))) with rfl | h
            · exact absurd List.mem_cons_self hf
            · exact h) h
          rw [hl]; cases f c F <;> rfl
        · have hk' : k' = k := by omega
          subst hk'; rw [ih c F h]; rfl

theorem chk_complete {FULL T : ℕ} : ∀ (k : ℕ) (L F : List ℕ),
    NReachF FULL T k L F → chk FULL T k L F = true := by
  intro k; induction k with
  | zero => intro L F h; exact memb_iff.2 h
  | succ k ih =>
    intro L F h
    by_cases hT : T ∈ L
    · have hm := memb_iff.2 hT
      rcases k with _ | _ | k <;> simp only [chk, hm, Bool.cond_true]
    · have hm : memb T L = false := by rw [← Bool.not_eq_true, memb_iff]; exact hT
      rcases k with _ | _ | k
      · simp only [chk, hm, Bool.cond_false]
        rcases h with h | ⟨s, hc, _, _, hr⟩
        · exact absurd h hT
        · rcases List.mem_cons.mp hr with rfl | h; exact check1_complete hc; exact absurd h hT
      · simp only [chk, hm, Bool.cond_false]; exact check2_complete hT h
      · simp only [chk, hm, Bool.cond_false]
        exact loop_complete L _ (k + 2) (fun c F' hr => ih (c :: L) F' hr) hT
          (cands FULL L) F (fun _ hc => cands_sound hc) (fun _ hc hl _ => cands_complete hc hl) h

def evalMask {n : ℕ} (N : ℕ) (e : ℕ → Fin n → Bool) (g : BF n) : ℕ :=
  Nat.rec 0 (fun j ih => ih ||| (if g (e j) then (1 <<< j) else 0)) N

theorem testBit_evalMask {n : ℕ} (N : ℕ) (e : ℕ → Fin n → Bool) (g : BF n) (i : ℕ) :
    (evalMask N e g).testBit i = (decide (i < N) && g (e i)) := by
  induction N with
  | zero => simp [evalMask]
  | succ m ih =>
    change (evalMask m e g ||| (if g (e m) then 1 <<< m else 0)).testBit i = _
    rw [Nat.testBit_or, ih]
    by_cases him : i = m
    · subst him
      have h1 : decide (i < i) = false := by simp
      have h2 : decide (i < i + 1) = true := by simp
      rw [h1, h2]; simp only [Bool.false_and, Bool.false_or, Bool.true_and]
      cases g (e i) <;> simp [Nat.testBit_shiftLeft]
    · have hbit : (if g (e m) then 1 <<< m else 0).testBit i = false := by
        cases g (e m)
        · simp
        · simp only [ite_true, Nat.testBit_shiftLeft]
          by_cases hle : m ≤ i
          · simp only [hle, decide_true, Bool.true_and]
            cases hd : i - m with
            | zero => omega
            | succ d => rw [Nat.testBit_succ]; simp
          · simp [hle]
      rw [hbit, Bool.or_false]
      by_cases hlt : i < m
      · have hlt2 : i < m + 1 := by omega
        simp [hlt, hlt2]
      · have hlt2 : ¬ i < m + 1 := by omega
        simp [hlt, hlt2]

theorem evalMask_and {n : ℕ} (N : ℕ) (e : ℕ → Fin n → Bool) (a b : BF n) :
    evalMask N e (fAnd a b) = Nat.land (evalMask N e a) (evalMask N e b) := by
  apply Nat.eq_of_testBit_eq; intro i
  show (evalMask N e (fAnd a b)).testBit i = (evalMask N e a &&& evalMask N e b).testBit i
  rw [Nat.testBit_and, testBit_evalMask, testBit_evalMask, testBit_evalMask]
  by_cases h : i < N <;> simp [h, fBin]

theorem evalMask_or {n : ℕ} (N : ℕ) (e : ℕ → Fin n → Bool) (a b : BF n) :
    evalMask N e (fOr a b) = Nat.lor (evalMask N e a) (evalMask N e b) := by
  apply Nat.eq_of_testBit_eq; intro i
  show (evalMask N e (fOr a b)).testBit i = (evalMask N e a ||| evalMask N e b).testBit i
  rw [Nat.testBit_or, testBit_evalMask, testBit_evalMask, testBit_evalMask]
  by_cases h : i < N <;> simp [h, fBin]

theorem evalMask_sub {n : ℕ} (N : ℕ) (e : ℕ → Fin n → Bool) (a b : BF n) :
    evalMask N e (fSub a b) = bsub (2 ^ N - 1) (evalMask N e a) (evalMask N e b) := by
  apply Nat.eq_of_testBit_eq; intro i
  show (evalMask N e (fSub a b)).testBit i = (evalMask N e a &&& ((2 ^ N - 1) ^^^ evalMask N e b)).testBit i
  rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, testBit_evalMask, testBit_evalMask, testBit_evalMask]
  by_cases h : i < N <;> simp [h, fBin]

theorem evalMask_pres {n : ℕ} (N : ℕ) (e : ℕ → Fin n → Bool) (x y s : BF n)
    (hs : s = fAnd x y ∨ s = fOr x y ∨ s = fSub x y) (L' : List ℕ)
    (hx : evalMask N e x ∈ L') (hy : evalMask N e y ∈ L') :
    NStep (2 ^ N - 1) L' (evalMask N e s) := by
  rcases hs with rfl | rfl | rfl
  · exact ⟨_, hx, _, hy, Or.inl (evalMask_and N e x y)⟩
  · exact ⟨_, hx, _, hy, Or.inr (Or.inl (evalMask_or N e x y))⟩
  · exact ⟨_, hx, _, hy, Or.inr (Or.inr (evalMask_sub N e x y))⟩

theorem leaf_lb {n : ℕ} (N : ℕ) (FULL : ℕ) (e : ℕ → Fin n → Bool) (f : BF n)
    (T m : ℕ) (L : List ℕ) (hF : FULL = 2 ^ N - 1) (hT : evalMask N e f = T)
    (h0 : memb 0 L = true) (hV : ∀ p : Fin n, memb (evalMask N e (fV p)) L = true)
    (hchk : chk FULL T m L [] = false) :
    ∀ k : ℕ, BR f k (bank0 n) → m + 1 ≤ k := by
  intro k hk
  by_contra hlt
  have hle : k ≤ m := by omega
  have h1 : NReach (2 ^ N - 1) (evalMask N e f) k ((bank0 n).map (evalMask N e)) :=
    Reach.map fAnd fOr fSub Nat.land Nat.lor (bsub (2 ^ N - 1)) (evalMask N e) (evalMask_pres N e) k _ hk
  have hsub : ∀ w ∈ (bank0 n).map (evalMask N e), w ∈ L := by
    intro w hw; obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hw
    rcases List.mem_cons.mp hg with rfl | hg
    · have hz : evalMask N e (f0 n) = 0 := by
        apply Nat.eq_of_testBit_eq; intro i; rw [testBit_evalMask]; simp [f0]
      rw [hz]; exact memb_iff.1 h0
    · obtain ⟨p, rfl⟩ := (List.mem_ofFn' _ _).mp hg; exact memb_iff.1 (hV p)
  have h2 : NReach FULL T k L := by
    rw [hF, ← hT]; exact Reach.monoL _ _ _ k _ _ hsub h1
  have h3 : NReach FULL T m L := Reach.monoLe _ _ _ hle L h2
  have h4 := chk_complete m L [] (Reach.toF _ _ _ m L h3)
  rw [hchk] at h4; exact Bool.noConfusion h4

-- Circuit bridge
def isBinOp : GateOp → Bool
  | GateOp.not => false
  | _ => true

def binCnt (gs : List Gate) : ℕ := (gs.filter (fun g => isBinOp g.op)).length

theorem binCnt_lt (gs : List Gate) (h : ∃ g ∈ gs, g.op = GateOp.not) : binCnt gs < gs.length := by
  induction gs with
  | nil => obtain ⟨_, h, _⟩ := h; exact absurd h List.not_mem_nil
  | cons a tl ih =>
    obtain ⟨g, hg, hop⟩ := h
    rcases List.mem_cons.mp hg with rfl | hg
    · unfold binCnt
      rw [List.filter_cons, hop]
      exact Nat.lt_succ_of_le (List.length_filter_le _ _)
    · have hlt := ih ⟨g, hg, hop⟩
      unfold binCnt at hlt ⊢
      simp only [List.filter_cons, List.length_cons]
      cases hba : isBinOp a.op
      · simp only [Bool.false_eq_true, ite_false]; omega
      · simp only [ite_true, List.length_cons]; omega

def foldWires (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem norm_const {n : ℕ} (b : Bool) : norm (fun _ : Fin n → Bool => b) = f0 n := by
  funext x; show xor b b = false; cases b <;> rfl

theorem norm_not {n : ℕ} (a : BF n) : norm (fun x => !(a x)) = norm a := by
  funext x; show xor (!(a x)) (!(a (z0 n))) = xor (a x) (a (z0 n))
  cases a x <;> cases a (z0 n) <;> rfl

theorem getD_append_cases {α : Type} (l : List α) (v d : α) (i : ℕ) :
    (l ++ [v]).getD i d = if i < l.length then l.getD i d else if i = l.length then v else d := by
  simp only [List.getD]
  by_cases h1 : i < l.length
  · simp [h1, List.getElem?_append_left h1]
  · simp only [h1, ite_false]
    rw [List.getElem?_append_right (Nat.le_of_not_gt h1)]
    by_cases h2 : i = l.length
    · subst h2; simp
    · have hgt : [v].length ≤ i - l.length := by simp; omega
      simp [h2, List.getElem?_eq_none hgt]

theorem foldWires_to_BR {n : ℕ} (T : BF n) :
    ∀ (gs : List Gate) (m : ℕ) (w : (Fin n → Bool) → List Bool) (o : ℕ) (L : List (BF n)),
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) →
      (∀ x, (w x).length = m) →
      (f0 n ∈ L) →
      (∀ i, norm (fun x => (w x).getD i false) ∈ L) →
      (∀ x, (foldWires gs (w x)).getD o false = T x) →
      BR (norm T) (binCnt gs) L := by
  intro gs; induction gs with
  | nil =>
    intro m w o L _ _ _ hmem hev
    have heq : norm T = norm (fun x => (w x).getD o false) := by
      funext x; show xor (T x) (T (z0 n)) = xor ((w x).getD o false) ((w (z0 n)).getD o false)
      rw [← hev x, ← hev (z0 n)]; rfl
    rw [heq]; exact hmem o
  | cons g rest ih =>
    intro m w o L hok hlen hf0 hmem hev
    have hg := hok g List.mem_cons_self
    have hrest : ∀ h ∈ rest, (h.op = GateOp.and ∨ h.op = GateOp.or ∨ h.op = GateOp.not) ∧ h.inputs.length ≤ 2 :=
      fun h hh => hok h (List.mem_cons_of_mem _ hh)
    let v : BF n := fun x => g.op.eval (g.inputs.map fun i => (w x).getD i false)
    let w' : (Fin n → Bool) → List Bool := fun x => w x ++ [v x]
    have hlen' : ∀ x, (w' x).length = m + 1 := fun x => by simp [w', hlen x]
    have hev' : ∀ x, (foldWires rest (w' x)).getD o false = T x := fun x => hev x
    have wire_mem : ∀ (L' : List (BF n)), (∀ z ∈ L, z ∈ L') → norm v ∈ L' →
        ∀ i, norm (fun x => (w' x).getD i false) ∈ L' := by
      intro L' hsub hv i
      by_cases h1 : i < m
      · have heq : (fun x => (w' x).getD i false) = (fun x => (w x).getD i false) := by
          funext x; dsimp only [w']; rw [getD_append_cases, hlen x]; simp [h1]
        rw [heq]; exact hsub _ (hmem i)
      · by_cases h2 : i = m
        · have heq : (fun x => (w' x).getD i false) = v := by
            funext x; dsimp only [w']; rw [getD_append_cases, hlen x]; simp [h2]
          rw [heq]; exact hv
        · have heq : (fun x => (w' x).getD i false) = f0 n := by
            funext x; dsimp only [w']; rw [getD_append_cases, hlen x]; simp [h1, h2, f0]
          rw [heq]; exact hsub _ hf0
    rcases hg.1 with hop | hop | hop
    · have hcnt : binCnt (g :: rest) = binCnt rest + 1 := by simp [binCnt, hop, isBinOp]
      rw [hcnt]
      cases hi : g.inputs with
      | nil =>
        have hv : norm v = f0 n := by
          have : v = fun _ => true := funext fun x => by simp [v, hop, hi, GateOp.eval]
          rw [this]; exact norm_const true
        exact Reach.monoK _ _ _ _ _ (ih (m + 1) w' o L hrest hlen' hf0 (wire_mem L (fun _ h => h) (hv ▸ hf0)) hev')
      | cons a tl =>
        cases tl with
        | nil =>
          have hv : v = fun x => (w x).getD a false := funext fun x => by simp [v, hop, hi, GateOp.eval]
          exact Reach.monoK _ _ _ _ _ (ih (m + 1) w' o L hrest hlen' hf0 (wire_mem L (fun _ h => h) (hv ▸ hmem a)) hev')
        | cons b tl2 =>
          cases tl2 with
          | nil =>
            have hv : v = fAnd (fun x => (w x).getD a false) (fun x => (w x).getD b false) :=
              funext fun x => by simp [v, hop, hi, GateOp.eval, fBin]
            have hstep : Step fAnd fOr fSub L (norm v) :=
              hv ▸ proj_step id and (Or.inl rfl) _ _ L (hmem a) (hmem b)
            have hr := ih (m + 1) w' o (norm v :: L) hrest hlen' (List.mem_cons_of_mem _ hf0)
              (wire_mem (norm v :: L) (fun _ h => List.mem_cons_of_mem _ h) List.mem_cons_self) hev'
            exact Or.inr ⟨norm v, hstep, hr⟩
          | cons _ _ => have := hg.2; rw [hi] at this; simp at this
    · have hcnt : binCnt (g :: rest) = binCnt rest + 1 := by simp [binCnt, hop, isBinOp]
      rw [hcnt]
      cases hi : g.inputs with
      | nil =>
        have hv : norm v = f0 n := by
          have : v = fun _ => false := funext fun x => by simp [v, hop, hi, GateOp.eval]
          rw [this]; exact norm_const false
        exact Reach.monoK _ _ _ _ _ (ih (m + 1) w' o L hrest hlen' hf0 (wire_mem L (fun _ h => h) (hv ▸ hf0)) hev')
      | cons a tl =>
        cases tl with
        | nil =>
          have hv : v = fun x => (w x).getD a false := funext fun x => by simp [v, hop, hi, GateOp.eval]
          exact Reach.monoK _ _ _ _ _ (ih (m + 1) w' o L hrest hlen' hf0 (wire_mem L (fun _ h => h) (hv ▸ hmem a)) hev')
        | cons b tl2 =>
          cases tl2 with
          | nil =>
            have hv : v = fOr (fun x => (w x).getD a false) (fun x => (w x).getD b false) :=
              funext fun x => by simp [v, hop, hi, GateOp.eval, fBin]
            have hstep : Step fAnd fOr fSub L (norm v) :=
              hv ▸ proj_step id or (Or.inr (Or.inl rfl)) _ _ L (hmem a) (hmem b)
            have hr := ih (m + 1) w' o (norm v :: L) hrest hlen' (List.mem_cons_of_mem _ hf0)
              (wire_mem (norm v :: L) (fun _ h => List.mem_cons_of_mem _ h) List.mem_cons_self) hev'
            exact Or.inr ⟨norm v, hstep, hr⟩
          | cons _ _ => have := hg.2; rw [hi] at this; simp at this
    · have hcnt : binCnt (g :: rest) = binCnt rest := by simp [binCnt, hop, isBinOp]
      rw [hcnt]
      have hv_in : norm v ∈ L := by
        cases hi : g.inputs with
        | nil =>
          have : v = fun _ => true := funext fun x => by simp [v, hop, hi, GateOp.eval]
          rw [this, norm_const]; exact hf0
        | cons a _ =>
          have : v = fun x => !((w x).getD a false) := funext fun x => by simp [v, hop, hi, GateOp.eval]
          rw [this, norm_not]; exact hmem a
      exact ih (m + 1) w' o L hrest hlen' hf0 (wire_mem L (fun _ h => h) hv_in) hev'

theorem circuit_to_BR {n : ℕ} (T : BF n) (gs : List Gate) (o : ℕ)
    (hok : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin n → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = T x) :
    BR (norm T) (binCnt gs) (bank0 n) := by
  refine foldWires_to_BR T gs n (fun x => List.ofFn x) o (bank0 n) hok
    (fun x => List.length_ofFn) List.mem_cons_self ?_ hev
  intro i
  by_cases hi : i < n
  · have heq : norm (fun x : Fin n → Bool => (List.ofFn x).getD i false) = fV ⟨i, hi⟩ := by
      funext x
      have h1 : (List.ofFn x).getD i false = x ⟨i, hi⟩ := by simp [List.getD, hi]
      have h2 : (List.ofFn (z0 n)).getD i false = false := by simp [List.getD, hi, z0]
      show xor ((List.ofFn x).getD i false) ((List.ofFn (z0 n)).getD i false) = x ⟨i, hi⟩
      rw [h1, h2]; cases x ⟨i, hi⟩ <;> rfl
    rw [heq]; exact List.mem_cons_of_mem _ ((List.mem_ofFn' _ _).mpr ⟨⟨i, hi⟩, rfl⟩)
  · have heq : norm (fun x : Fin n → Bool => (List.ofFn x).getD i false) = f0 n := by
      funext x
      have h1 : (List.ofFn x).getD i false = false := by
        simp [List.getD, List.getElem?_eq_none (show (List.ofFn x).length ≤ i by simp; omega)]
      have h2 : (List.ofFn (z0 n)).getD i false = false := by
        simp [List.getD, List.getElem?_eq_none (show (List.ofFn (z0 n)).length ≤ i by simp; omega)]
      show xor ((List.ofFn x).getD i false) ((List.ofFn (z0 n)).getD i false) = false
      rw [h1, h2]; rfl
    rw [heq]; exact List.mem_cons_self

def isMono2 (g : Gate) : Bool :=
  (match g.op with | GateOp.and => true | GateOp.or => true | _ => false) && decide (g.inputs.length ≤ 2)

theorem isMono2_sound (Wg : List Gate) (h : Wg.all isMono2 = true) :
    ∀ g ∈ Wg, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  have h1 := List.all_eq_true.mp h g hg
  obtain ⟨op, ins⟩ := g
  unfold isMono2 at h1; rw [Bool.and_eq_true] at h1
  refine ⟨?_, of_decide_eq_true h1.2⟩
  cases op <;> simp at h1 ⊢

theorem savesNothing {n : ℕ} (f : BF n) (B : ℕ) (hB : ∀ k, BR (norm f) k (bank0 n) → B ≤ k)
    (Wg : List Gate) (wo : ℕ) (hWm : Wg.all isMono2 = true) (hWl : Wg.length ≤ B + 1)
    (hWe : ∀ x : Fin n → Bool, Circuit.eval ⟨Wg, wo⟩ (List.ofFn x) = f x) :
    ∀ (gates : List Gate) (o : ℕ),
      (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) →
      (∀ i j : Fin gates.length, (gates.get i).op = GateOp.not → (gates.get j).op = GateOp.not → i = j) →
      (∀ x : Fin n → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = f x) →
      ∃ (gates' : List Gate) (o' : ℕ),
        (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
        gates'.length ≤ gates.length ∧
        ∀ x : Fin n → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = f x := by
  intro gates o hok _ hev
  by_cases hn : ∃ g ∈ gates, g.op = GateOp.not
  · have h1 := hB _ (circuit_to_BR f gates o hok hev)
    have h2 := binCnt_lt gates hn
    exact ⟨Wg, wo, isMono2_sound Wg hWm, by omega, hWe⟩
  · refine ⟨gates, o, ?_, Nat.le_refl _, hev⟩
    intro g hg; obtain ⟨ho, hl⟩ := hok g hg
    rcases ho with h | h | h
    · exact ⟨Or.inl h, hl⟩
    · exact ⟨Or.inr h, hl⟩
    · exact absurd ⟨g, hg, h⟩ hn


def ev3 (v0 v1 v2 : ℕ) (j : ℕ) : Fin 8 → Bool :=
  fun i => if i.val = v0 then j.testBit 0 else if i.val = v1 then j.testBit 1 else if i.val = v2 then j.testBit 2 else false

def F0 : BF 8 := fun x : Fin 8 → Bool => decide (∃ i < ([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)

def F1 : BF 8 := fun x => Nat.testBit 115792089237315784041154552971790309228684046205902700037756665751319544987648 (encodeFin x)

theorem F01 : F0 = F1 := funext (all_pts (fun x => F0 x = F1 x) (by decide +kernel))

theorem ck_232_3 : chk 255 232 3 [0, 170, 204, 240] [] = false := by decide +kernel

theorem nd1 : ∀ k : ℕ, BR (restr (6 : Fin 8) false (restr (2 : Fin 8) false (restr (4 : Fin 8) false (restr (3 : Fin 8) false (restr (1 : Fin 8) false (norm F1)))))) k (bank0 8) → 3 + 1 ≤ k :=
  leaf_lb 8 255 (ev3 0 5 7) _ 232 3 [0, 170, 204, 240] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ck_232_3

theorem nd2 : ∀ k : ℕ, BR (restr (2 : Fin 8) false (restr (4 : Fin 8) false (restr (3 : Fin 8) false (restr (1 : Fin 8) false (norm F1))))) k (bank0 8) → 5 ≤ k := by
  intro k h
  obtain ⟨k', rfl, h'⟩ := elim1 (6 : Fin 8) false (restr (2 : Fin 8) false (restr (4 : Fin 8) false (restr (3 : Fin 8) false (restr (1 : Fin 8) false (norm F1))))) (ne_f0 _ (pt 33) (by decide +kernel)) (dep_of (6 : Fin 8) _ (pt 1) (by decide +kernel)) k (bank0 8) (clean_bank0 _) h
  have := nd1 k' h'; omega

theorem nd3 : ∀ k : ℕ, BR (restr (6 : Fin 8) false (restr (2 : Fin 8) true (restr (4 : Fin 8) false (restr (3 : Fin 8) false (restr (1 : Fin 8) false (norm F1)))))) k (bank0 8) → 3 + 1 ≤ k :=
  leaf_lb 8 255 (ev3 0 5 7) _ 232 3 [0, 170, 204, 240] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ck_232_3

theorem nd4 : ∀ k : ℕ, BR (restr (2 : Fin 8) true (restr (4 : Fin 8) false (restr (3 : Fin 8) false (restr (1 : Fin 8) false (norm F1))))) k (bank0 8) → 5 ≤ k := by
  intro k h
  obtain ⟨k', rfl, h'⟩ := elim1 (6 : Fin 8) false (restr (2 : Fin 8) true (restr (4 : Fin 8) false (restr (3 : Fin 8) false (restr (1 : Fin 8) false (norm F1))))) (ne_f0 _ (pt 33) (by decide +kernel)) (dep_of (6 : Fin 8) _ (pt 0) (by decide +kernel)) k (bank0 8) (clean_bank0 _) h
  have := nd3 k' h'; omega

theorem nd5 : ∀ k : ℕ, BR (restr (4 : Fin 8) false (restr (3 : Fin 8) false (restr (1 : Fin 8) false (norm F1)))) k (bank0 8) → 7 ≤ k := by
  intro k h
  obtain ⟨k', rfl, h' | h'⟩ := elim2 (2 : Fin 8) (restr (4 : Fin 8) false (restr (3 : Fin 8) false (restr (1 : Fin 8) false (norm F1)))) (ne_f0 _ (pt 33) (by decide +kernel)) (ne_f0 _ (pt 33) (by decide +kernel)) (dep_of (2 : Fin 8) _ (pt 64) (by decide +kernel)) k (bank0 8) (clean_bank0 _) h
  · have := nd2 k' h'; omega
  · have := nd4 k' h'; omega

theorem nd6 : ∀ k : ℕ, BR (restr (3 : Fin 8) false (restr (1 : Fin 8) false (norm F1))) k (bank0 8) → 8 ≤ k := by
  intro k h
  obtain ⟨k', rfl, h'⟩ := elim1 (4 : Fin 8) false (restr (3 : Fin 8) false (restr (1 : Fin 8) false (norm F1))) (ne_f0 _ (pt 33) (by decide +kernel)) (dep_of (4 : Fin 8) _ (pt 1) (by decide +kernel)) k (bank0 8) (clean_bank0 _) h
  have := nd5 k' h'; omega

theorem nd7 : ∀ k : ℕ, BR (restr (1 : Fin 8) false (norm F1)) k (bank0 8) → 9 ≤ k := by
  intro k h
  obtain ⟨k', rfl, h'⟩ := elim1 (3 : Fin 8) false (restr (1 : Fin 8) false (norm F1)) (ne_f0 _ (pt 17) (by decide +kernel)) (dep_of (3 : Fin 8) _ (pt 128) (by decide +kernel)) k (bank0 8) (clean_bank0 _) h
  have := nd6 k' h'; omega

theorem nd8 : ∀ k : ℕ, BR (norm F1) k (bank0 8) → 10 ≤ k := by
  intro k h
  obtain ⟨k', rfl, h'⟩ := elim1 (1 : Fin 8) false (norm F1) (ne_f0 _ (pt 17) (by decide +kernel)) (dep_of (1 : Fin 8) _ (pt 32) (by decide +kernel)) k (bank0 8) (clean_bank0 _) h
  have := nd7 k' h'; omega

theorem root : ∀ k : ℕ, BR (norm F0) k (bank0 8) → 10 ≤ k := by
  intro k h; rw [F01] at h; exact nd8 k h

def Wg : List Gate := [⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 8]⟩, ⟨GateOp.or, [3, 8]⟩, ⟨GateOp.or, [5, 10]⟩, ⟨GateOp.and, [9, 6]⟩, ⟨GateOp.and, [0, 4]⟩, ⟨GateOp.and, [11, 7]⟩, ⟨GateOp.and, [8, 5]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.or, [16, 14]⟩, ⟨GateOp.or, [17, 15]⟩]

theorem hWe : ∀ x : Fin 8 → Bool, Circuit.eval ⟨Wg, 18⟩ (List.ofFn x) = F0 x := by
  rw [F01]; exact all_pts (fun x => Circuit.eval ⟨Wg, 18⟩ (List.ofFn x) = F1 x) (by decide +kernel)

end PEqualNP.Outside.L_meta_26036

theorem PEqualNP.Outside.L_meta_26036 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  PEqualNP.Outside.L_meta_26036.savesNothing PEqualNP.Outside.L_meta_26036.F0 10 PEqualNP.Outside.L_meta_26036.root PEqualNP.Outside.L_meta_26036.Wg 18 (by decide +kernel) (by decide +kernel) PEqualNP.Outside.L_meta_26036.hWe
