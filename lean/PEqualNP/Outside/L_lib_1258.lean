import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1258_aux

/-- The chain predicate of the statement, written with the same recursor. -/
def Named {n m : ℕ} (a b c d : Fin m → Finset (Fin n)) (x : Finset (Fin n))
    (js : List (Fin m)) : Prop :=
  List.rec (motive := fun _ => Finset (Fin n) → Prop) (fun _ => True)
    (fun j _ prev y => ∃ u v, prev u ∧ u ⊆ v ∧ v ⊆ y ∧
      a j ⊆ u ∧ u ⊆ b j ∧ c j ⊆ v ∧ v ⊆ d j) js x

theorem named_cons {n m : ℕ} (a b c d : Fin m → Finset (Fin n)) (x : Finset (Fin n)) (j : Fin m)
    (js : List (Fin m)) :
    Named a b c d x (j :: js) ↔ ∃ u v, Named a b c d u js ∧ u ⊆ v ∧ v ⊆ x ∧
      a j ⊆ u ∧ u ⊆ b j ∧ c j ⊆ v ∧ v ⊆ d j := Iff.rfl

theorem named_mono {n m : ℕ} (a b c d : Fin m → Finset (Fin n)) (js : List (Fin m)) :
    ∀ (x y : Finset (Fin n)), x ⊆ y → Named a b c d x js → Named a b c d y js := by
  induction js with
  | nil => intro _ _ _ _; trivial
  | cons j js _ =>
    intro x y hxy h
    obtain ⟨u, v, h1, h2, h3, h4⟩ := (named_cons a b c d x j js).1 h
    exact (named_cons a b c d y j js).2 ⟨u, v, h1, h2, h3.trans hxy, h4⟩

theorem named_tail {n m : ℕ} (a b c d : Fin m → Finset (Fin n)) (x : Finset (Fin n)) (j : Fin m)
    (js : List (Fin m)) (h : Named a b c d x (j :: js)) : Named a b c d x js := by
  obtain ⟨u, v, h1, h2, h3, -⟩ := (named_cons a b c d x j js).1 h
  exact named_mono a b c d js u x (h2.trans h3) h1

theorem named_drop {n m : ℕ} (a b c d : Fin m → Finset (Fin n)) (x : Finset (Fin n)) (k : ℕ) :
    ∀ js : List (Fin m), Named a b c d x js → Named a b c d x (js.drop k) := by
  induction k with
  | zero => intro js h; simpa using h
  | succ k ih =>
    intro js h
    cases js with
    | nil => simpa using h
    | cons j js => simpa using ih js (named_tail a b c d x j js h)

theorem chain_of_named {n m : ℕ} (a b c d : Fin m → Finset (Fin n)) (js : List (Fin m)) :
    ∀ y : Finset (Fin n), Named a b c d y js →
    ∃ U Z : ℕ → Finset (Fin n),
      (0 < js.length → Z 0 ⊆ y) ∧
      (∀ t, t + 1 < js.length → Z (t+1) ⊆ U t) ∧
      ∀ t (ht : t < js.length), U t ⊆ Z t ∧ a js[t] ⊆ U t ∧ U t ⊆ b js[t] ∧
        c js[t] ⊆ Z t ∧ Z t ⊆ d js[t] := by
  induction js with
  | nil => intro y _; exact ⟨fun _ => ∅, fun _ => ∅, by simp, by simp, by simp⟩
  | cons j js ih =>
    intro y h
    obtain ⟨u, v, h1, huv, hvy, ha, hb, hc, hd⟩ := (named_cons a b c d y j js).1 h
    obtain ⟨U, Z, h0, hs, hbx⟩ := ih u h1
    refine ⟨fun t => Nat.casesOn (motive := fun _ => Finset (Fin n)) t u U,
      fun t => Nat.casesOn (motive := fun _ => Finset (Fin n)) t v Z, fun _ => hvy, ?_, ?_⟩
    · intro t ht
      simp only [List.length_cons] at ht
      cases t with
      | zero => exact h0 (by omega)
      | succ t => exact hs t (by omega)
    · intro t ht
      cases t with
      | zero => exact ⟨huv, ha, hb, hc, hd⟩
      | succ t =>
        have := hbx t (by simp only [List.length_cons] at ht; omega)
        exact this

theorem named_of_chain {n m : ℕ} (a b c d : Fin m → Finset (Fin n)) (k : ℕ) :
    ∀ (g : Fin k → Fin m) (y : Finset (Fin n)) (U Z : ℕ → Finset (Fin n)),
      (0 < k → Z 0 ⊆ y) →
      (∀ t, t + 1 < k → Z (t+1) ⊆ U t) →
      (∀ t : Fin k, U t ⊆ Z t ∧ a (g t) ⊆ U t ∧ U t ⊆ b (g t) ∧ c (g t) ⊆ Z t ∧
        Z t ⊆ d (g t)) →
      Named a b c d y (List.ofFn g) := by
  induction k with
  | zero => intro g y U Z _ _ _; rw [List.ofFn_zero]; trivial
  | succ k ih =>
    intro g y U Z h0 hs hb
    rw [List.ofFn_succ, named_cons]
    have hb0 := hb 0
    simp only [Fin.val_zero] at hb0
    obtain ⟨h1, h2, h3, h4, h5⟩ := hb0
    refine ⟨U 0, Z 0, ?_, h1, h0 (Nat.succ_pos k), h2, h3, h4, h5⟩
    apply ih (fun i => g i.succ) (U 0) (fun t => U (t+1)) (fun t => Z (t+1))
    · intro _; exact hs 0 (by omega)
    · intro t ht; exact hs (t+1) (by omega)
    · intro t; exact hb t.succ

/-! The CNF template. -/

abbrev Var (n m : ℕ) : Type :=
  Fin n ⊕ (Fin m × Fin n) ⊕ (Fin m × Fin n) ⊕ (Fin m × Fin m) ⊕ Fin (m+1) ⊕ Fin (m+1) ⊕ Fin m

def vW {n m : ℕ} (k : Fin n) : Var n m := Sum.inl k
def vU {n m : ℕ} (t : Fin m) (k : Fin n) : Var n m := Sum.inr (Sum.inl (t, k))
def vZ {n m : ℕ} (t : Fin m) (k : Fin n) : Var n m := Sum.inr (Sum.inr (Sum.inl (t, k)))
def vP {n m : ℕ} (t j : Fin m) : Var n m := Sum.inr (Sum.inr (Sum.inr (Sum.inl (t, j))))
def vSel {n m : ℕ} (v : Fin (m+1)) : Var n m :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl v))))
def vLev {n m : ℕ} (l : Fin (m+1)) : Var n m :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl l)))))
def vAct {n m : ℕ} (t : Fin m) : Var n m :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr t)))))

abbrev C2 (n m : ℕ) : Type := Var n m × Bool × Var n m × Bool

abbrev Lit (n m : ℕ) : Type :=
  (C2 n m × Option Bool) ⊕ (Fin n × Bool) ⊕ Fin (m+1) ⊕ Fin (m+1) ⊕ (Fin m × Option (Fin m))

abbrev Cl (n m : ℕ) : Type := C2 n m ⊕ Fin n ⊕ Unit ⊕ Unit ⊕ Fin m

def capF {n m : ℕ} (b : Fin m → Finset (Fin n)) (v : Fin (m+1)) : Finset (Fin n) :=
  Fin.cases (motive := fun _ => Finset (Fin n)) Finset.univ b v

theorem capF_zero {n m : ℕ} (b : Fin m → Finset (Fin n)) : capF b 0 = Finset.univ := by
  simp [capF]

theorem capF_succ {n m : ℕ} (b : Fin m → Finset (Fin n)) (j : Fin m) : capF b j.succ = b j := by
  simp [capF]

/-- The two-literal clauses that are switched on. -/
def Want {n m : ℕ} (a b c d : Fin m → Finset (Fin n)) (e : C2 n m) : Prop :=
  (∃ (t j : Fin m) (k : Fin n), k ∈ a j ∧ e = (vP t j, false, vU t k, true)) ∨
  (∃ (t j : Fin m) (k : Fin n), k ∉ b j ∧ e = (vP t j, false, vU t k, false)) ∨
  (∃ (t j : Fin m) (k : Fin n), k ∈ c j ∧ e = (vP t j, false, vZ t k, true)) ∨
  (∃ (t j : Fin m) (k : Fin n), k ∉ d j ∧ e = (vP t j, false, vZ t k, false)) ∨
  (∃ (t : Fin m) (k : Fin n), e = (vU t k, false, vZ t k, true)) ∨
  (∃ (t : Fin m) (k : Fin n), (t : ℕ) = 0 ∧ e = (vZ t k, false, vW k, true)) ∨
  (∃ (t t' : Fin m) (k : Fin n), (t' : ℕ) = t + 1 ∧ e = (vZ t' k, false, vU t k, true)) ∨
  (∃ (v : Fin (m+1)) (k : Fin n), k ∉ capF b v ∧ e = (vSel v, false, vW k, false)) ∨
  (∃ (l : Fin (m+1)) (t : Fin m), (t : ℕ) < l ∧ e = (vLev l, false, vAct t, true))

def clF {n m : ℕ} : Lit n m → Cl n m
  | Sum.inl (e, _) => Sum.inl e
  | Sum.inr (Sum.inl (k, _)) => Sum.inr (Sum.inl k)
  | Sum.inr (Sum.inr (Sum.inl _)) => Sum.inr (Sum.inr (Sum.inl ()))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => Sum.inr (Sum.inr (Sum.inr (Sum.inl ())))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (t, _)))) => Sum.inr (Sum.inr (Sum.inr (Sum.inr t)))

def vrF {n m : ℕ} : Lit n m → Var n m
  | Sum.inl (e, none) => e.1
  | Sum.inl (e, some false) => e.1
  | Sum.inl (e, some true) => e.2.2.1
  | Sum.inr (Sum.inl (k, _)) => vW k
  | Sum.inr (Sum.inr (Sum.inl v)) => vSel v
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl l))) => vLev l
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (t, none)))) => vAct t
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (t, some j)))) => vP t j

def sgF {n m : ℕ} : Lit n m → Bool
  | Sum.inl (e, none) => !e.2.1
  | Sum.inl (e, some false) => e.2.1
  | Sum.inl (e, some true) => e.2.2.2
  | Sum.inr (Sum.inl (_, bb)) => bb
  | Sum.inr (Sum.inr (Sum.inl _)) => true
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => true
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (_, none)))) => false
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (_, some _)))) => true

def BaseP {n m : ℕ} (a b c d : Fin m → Finset (Fin n)) : Lit n m → Prop
  | Sum.inl (e, none) => ¬ Want a b c d e
  | Sum.inl (_, some _) => True
  | Sum.inr (Sum.inl (_, bb)) => bb = false
  | Sum.inr (Sum.inr (Sum.inl _)) => False
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => False
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) => True

def rawF {n m : ℕ} (k : Fin n) : Lit n m := Sum.inr (Sum.inl (k, true))
def modeF {n m : ℕ} (v : Fin (m+1)) : Lit n m := Sum.inr (Sum.inr (Sum.inl v))
def levelF {n m : ℕ} (l : Fin (m+1)) : Lit n m := Sum.inr (Sum.inr (Sum.inr (Sum.inl l)))

def Yp {n m : ℕ} (a b c d : Fin m → Finset (Fin n)) (x : Finset (Fin n)) (v l : Fin (m+1))
    (i : Lit n m) : Prop :=
  BaseP a b c d i ∨ (∃ k ∈ x, rawF k = i) ∨ i = modeF v ∨ i = levelF l

def SatA {n m : ℕ} (Y : Lit n m → Prop) : Prop :=
  ∃ s : Var n m → Bool, ∀ cc : Cl n m, ∃ i, clF i = cc ∧ Y i ∧ s (vrF i) = sgF i

theorem fam_two {n m : ℕ} (P : Lit n m → Prop) (e : C2 n m) :
    (∃ i, clF i = Sum.inl e ∧ P i) ↔ ∃ o, P (Sum.inl (e, o)) := by
  constructor
  · rintro ⟨i, hcl, hP⟩
    rcases i with ⟨e', o⟩ | ⟨k, bb⟩ | v | l | ⟨t, o⟩ <;> simp [clF] at hcl
    subst hcl; exact ⟨o, hP⟩
  · rintro ⟨o, hP⟩; exact ⟨_, rfl, hP⟩

theorem fam_raw {n m : ℕ} (P : Lit n m → Prop) (k : Fin n) :
    (∃ i, clF i = (Sum.inr (Sum.inl k) : Cl n m) ∧ P i) ↔
      ∃ bb, P (Sum.inr (Sum.inl (k, bb))) := by
  constructor
  · rintro ⟨i, hcl, hP⟩
    rcases i with ⟨e', o⟩ | ⟨k', bb⟩ | v | l | ⟨t, o⟩ <;> simp [clF] at hcl
    subst hcl; exact ⟨bb, hP⟩
  · rintro ⟨bb, hP⟩; exact ⟨_, rfl, hP⟩

theorem fam_mode {n m : ℕ} (P : Lit n m → Prop) :
    (∃ i, clF i = (Sum.inr (Sum.inr (Sum.inl ())) : Cl n m) ∧ P i) ↔ ∃ v, P (modeF v) := by
  constructor
  · rintro ⟨i, hcl, hP⟩
    rcases i with ⟨e', o⟩ | ⟨k', bb⟩ | v | l | ⟨t, o⟩ <;> simp [clF] at hcl
    exact ⟨v, hP⟩
  · rintro ⟨v, hP⟩; exact ⟨_, rfl, hP⟩

theorem fam_level {n m : ℕ} (P : Lit n m → Prop) :
    (∃ i, clF i = (Sum.inr (Sum.inr (Sum.inr (Sum.inl ()))) : Cl n m) ∧ P i) ↔
      ∃ l, P (levelF l) := by
  constructor
  · rintro ⟨i, hcl, hP⟩
    rcases i with ⟨e', o⟩ | ⟨k', bb⟩ | v | l | ⟨t, o⟩ <;> simp [clF] at hcl
    exact ⟨l, hP⟩
  · rintro ⟨l, hP⟩; exact ⟨_, rfl, hP⟩

theorem fam_slot {n m : ℕ} (P : Lit n m → Prop) (t : Fin m) :
    (∃ i, clF i = (Sum.inr (Sum.inr (Sum.inr (Sum.inr t))) : Cl n m) ∧ P i) ↔
      ∃ o, P (Sum.inr (Sum.inr (Sum.inr (Sum.inr (t, o))))) := by
  constructor
  · rintro ⟨i, hcl, hP⟩
    rcases i with ⟨e', o⟩ | ⟨k', bb⟩ | v | l | ⟨t', o⟩ <;> simp [clF] at hcl
    subst hcl; exact ⟨o, hP⟩
  · rintro ⟨o, hP⟩; exact ⟨_, rfl, hP⟩

section
variable {n m : ℕ} (a b c d : Fin m → Finset (Fin n)) (x : Finset (Fin n)) (v l : Fin (m+1))

theorem yp_two_none (e : C2 n m) : Yp a b c d x v l (Sum.inl (e, none)) ↔ ¬ Want a b c d e := by
  simp [Yp, BaseP, rawF, modeF, levelF]

theorem yp_two_some (e : C2 n m) (bb : Bool) : Yp a b c d x v l (Sum.inl (e, some bb)) :=
  Or.inl trivial

theorem yp_raw_false (k : Fin n) : Yp a b c d x v l (Sum.inr (Sum.inl (k, false))) :=
  Or.inl rfl

theorem yp_raw_true (k : Fin n) : Yp a b c d x v l (Sum.inr (Sum.inl (k, true))) ↔ k ∈ x := by
  simp [Yp, BaseP, rawF, modeF, levelF]

theorem yp_mode (v' : Fin (m+1)) : Yp a b c d x v l (modeF v') ↔ v' = v := by
  simp [Yp, BaseP, rawF, modeF, levelF]

theorem yp_level (l' : Fin (m+1)) : Yp a b c d x v l (levelF l') ↔ l' = l := by
  simp [Yp, BaseP, rawF, modeF, levelF]

theorem yp_slot (t : Fin m) (o : Option (Fin m)) :
    Yp a b c d x v l (Sum.inr (Sum.inr (Sum.inr (Sum.inr (t, o))))) :=
  Or.inl trivial

end

def Good {n m : ℕ} (a b c d : Fin m → Finset (Fin n)) (x : Finset (Fin n)) (v l : Fin (m+1))
    (s : Var n m → Bool) : Prop :=
  (∀ e, Want a b c d e → s e.1 = e.2.1 ∨ s e.2.2.1 = e.2.2.2) ∧
  (∀ k, s (vW k) = true → k ∈ x) ∧ s (vSel v) = true ∧ s (vLev l) = true ∧
  (∀ t, s (vAct t) = true → ∃ j, s (vP t j) = true)

theorem satA_iff {n m : ℕ} (a b c d : Fin m → Finset (Fin n)) (x : Finset (Fin n))
    (v l : Fin (m+1)) : SatA (Yp a b c d x v l) ↔ ∃ s, Good a b c d x v l s := by
  constructor
  · rintro ⟨s, h⟩
    refine ⟨s, ?_, ?_, ?_, ?_, ?_⟩
    · intro e he
      obtain ⟨o, hY, hs⟩ := (fam_two _ e).1 (h (Sum.inl e))
      rcases o with _ | _ | _
      · exact absurd he ((yp_two_none a b c d x v l e).1 hY)
      · exact Or.inl hs
      · exact Or.inr hs
    · intro k hk
      obtain ⟨bb, hY, hs⟩ := (fam_raw _ k).1 (h (Sum.inr (Sum.inl k)))
      cases bb
      · change s (vW k) = false at hs
        rw [hk] at hs; exact absurd hs (by decide)
      · exact (yp_raw_true a b c d x v l k).1 hY
    · obtain ⟨v', hY, hs⟩ := (fam_mode _).1 (h (Sum.inr (Sum.inr (Sum.inl ()))))
      have := (yp_mode a b c d x v l v').1 hY
      subst this
      exact hs
    · obtain ⟨l', hY, hs⟩ := (fam_level _).1 (h (Sum.inr (Sum.inr (Sum.inr (Sum.inl ())))))
      have := (yp_level a b c d x v l l').1 hY
      subst this
      exact hs
    · intro t ht
      obtain ⟨o, hY, hs⟩ := (fam_slot _ t).1 (h (Sum.inr (Sum.inr (Sum.inr (Sum.inr t)))))
      rcases o with _ | j
      · change s (vAct t) = false at hs
        rw [ht] at hs; exact absurd hs (by decide)
      · exact ⟨j, hs⟩
  · rintro ⟨s, h2, hraw, hsel, hlev, hact⟩
    refine ⟨s, ?_⟩
    rintro (e | k | ⟨⟩ | ⟨⟩ | t)
    · apply (fam_two _ e).2
      by_cases he : Want a b c d e
      · rcases h2 e he with h | h
        · exact ⟨some false, yp_two_some a b c d x v l e false, h⟩
        · exact ⟨some true, yp_two_some a b c d x v l e true, h⟩
      · by_cases h1 : s e.1 = e.2.1
        · exact ⟨some false, yp_two_some a b c d x v l e false, h1⟩
        · refine ⟨none, (yp_two_none a b c d x v l e).2 he, ?_⟩
          change s e.1 = !e.2.1
          revert h1
          cases s e.1 <;> cases e.2.1 <;> decide
    · apply (fam_raw _ k).2
      cases hk : s (vW k)
      · exact ⟨false, yp_raw_false a b c d x v l k, hk⟩
      · exact ⟨true, (yp_raw_true a b c d x v l k).2 (hraw k hk), hk⟩
    · apply (fam_mode _).2
      exact ⟨v, (yp_mode a b c d x v l v).2 rfl, hsel⟩
    · apply (fam_level _).2
      exact ⟨l, (yp_level a b c d x v l l).2 rfl, hlev⟩
    · apply (fam_slot _ t).2
      cases ht : s (vAct t)
      · exact ⟨none, yp_slot a b c d x v l t none, ht⟩
      · obtain ⟨j, hj⟩ := hact t ht
        exact ⟨some j, yp_slot a b c d x v l t (some j), hj⟩

/-- The assignment built from a chain. -/
def asg {n m : ℕ} (y : Finset (Fin n)) (U Z : ℕ → Finset (Fin n)) (js : List (Fin m))
    (v l : Fin (m+1)) : Var n m → Bool
  | Sum.inl k => decide (k ∈ y)
  | Sum.inr (Sum.inl (t, k)) => decide ((t : ℕ) < l ∧ k ∈ U t)
  | Sum.inr (Sum.inr (Sum.inl (t, k))) => decide ((t : ℕ) < l ∧ k ∈ Z t)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (t, j)))) =>
      decide (∃ h : (t : ℕ) < js.length, js[(t : ℕ)] = j)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl v')))) => decide (v' = v)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl l'))))) => decide (l' = l)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr t))))) => decide ((t : ℕ) < l)

section
variable {n m : ℕ} (y : Finset (Fin n)) (U Z : ℕ → Finset (Fin n)) (js : List (Fin m))
  (v l : Fin (m+1))

theorem asg_W (k : Fin n) : asg y U Z js v l (vW k) = decide (k ∈ y) := rfl
theorem asg_U (t : Fin m) (k : Fin n) :
    asg y U Z js v l (vU t k) = decide ((t : ℕ) < l ∧ k ∈ U t) := rfl
theorem asg_Z (t : Fin m) (k : Fin n) :
    asg y U Z js v l (vZ t k) = decide ((t : ℕ) < l ∧ k ∈ Z t) := rfl
theorem asg_P (t j : Fin m) :
    asg y U Z js v l (vP t j) = decide (∃ h : (t : ℕ) < js.length, js[(t : ℕ)] = j) := rfl
theorem asg_Sel (v' : Fin (m+1)) : asg y U Z js v l (vSel v') = decide (v' = v) := rfl
theorem asg_Lev (l' : Fin (m+1)) : asg y U Z js v l (vLev l') = decide (l' = l) := rfl
theorem asg_Act (t : Fin m) : asg y U Z js v l (vAct t) = decide ((t : ℕ) < l) := rfl

end

theorem ask_iff {n m : ℕ} (a b c d : Fin m → Finset (Fin n)) (x : Finset (Fin n))
    (v l : Fin (m+1)) (y : Finset (Fin n)) (hy : ∀ k, k ∈ y ↔ k ∈ x ∧ k ∈ capF b v) :
    SatA (Yp a b c d x v l) ↔ ∃ js : List (Fin m), js.length = l.val ∧ Named a b c d y js := by
  rw [satA_iff]
  constructor
  · rintro ⟨s, h2, hraw, hsel, hlev, hact⟩
    have hA : ∀ t j k, k ∈ a j → s (vP t j) = true → s (vU t k) = true := by
      intro t j k hk hp
      have h := h2 (vP t j, false, vU t k, true) (Or.inl ⟨t, j, k, hk, rfl⟩)
      exact h.resolve_left (by simp [hp])
    have hB : ∀ t j k, k ∉ b j → s (vP t j) = true → s (vU t k) = false := by
      intro t j k hk hp
      have h := h2 (vP t j, false, vU t k, false) (Or.inr (Or.inl ⟨t, j, k, hk, rfl⟩))
      exact h.resolve_left (by simp [hp])
    have hC : ∀ t j k, k ∈ c j → s (vP t j) = true → s (vZ t k) = true := by
      intro t j k hk hp
      have h := h2 (vP t j, false, vZ t k, true) (Or.inr (Or.inr (Or.inl ⟨t, j, k, hk, rfl⟩)))
      exact h.resolve_left (by simp [hp])
    have hD : ∀ t j k, k ∉ d j → s (vP t j) = true → s (vZ t k) = false := by
      intro t j k hk hp
      have h := h2 (vP t j, false, vZ t k, false)
        (Or.inr (Or.inr (Or.inr (Or.inl ⟨t, j, k, hk, rfl⟩))))
      exact h.resolve_left (by simp [hp])
    have hUZ : ∀ t k, s (vU t k) = true → s (vZ t k) = true := by
      intro t k hp
      have h := h2 (vU t k, false, vZ t k, true)
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨t, k, rfl⟩)))))
      exact h.resolve_left (by simp [hp])
    have hZW : ∀ (t : Fin m) (k : Fin n), (t : ℕ) = 0 → s (vZ t k) = true → s (vW k) = true := by
      intro t k ht hp
      have h := h2 (vZ t k, false, vW k, true)
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨t, k, ht, rfl⟩))))))
      exact h.resolve_left (by simp [hp])
    have hZU : ∀ (t t' : Fin m) (k : Fin n), (t' : ℕ) = t + 1 → s (vZ t' k) = true → s (vU t k) = true := by
      intro t t' k ht hp
      have h := h2 (vZ t' k, false, vU t k, true)
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨t, t', k, ht, rfl⟩)))))))
      exact h.resolve_left (by simp [hp])
    have hcap : ∀ k, s (vW k) = true → k ∈ capF b v := by
      intro k hw
      by_contra hk
      have h := h2 (vSel v, false, vW k, false)
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨v, k, hk, rfl⟩))))))))
      rcases h with h | h
      · change s (vSel v) = false at h
        rw [hsel] at h; exact absurd h (by decide)
      · change s (vW k) = false at h
        rw [hw] at h; exact absurd h (by decide)
    have hlv : ∀ t : Fin m, (t : ℕ) < l.val → s (vAct t) = true := by
      intro t ht
      have h := h2 (vLev l, false, vAct t, true)
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨l, t, ht, rfl⟩))))))))
      exact h.resolve_left (by simp [hlev])
    have hlm : l.val ≤ m := Nat.lt_succ_iff.mp l.isLt
    have hex : ∀ t : Fin l.val, ∃ j, s (vP ⟨t.val, lt_of_lt_of_le t.isLt hlm⟩ j) = true :=
      fun t => hact _ (hlv _ t.isLt)
    choose g hg using hex
    refine ⟨List.ofFn g, by simp, ?_⟩
    apply named_of_chain a b c d l.val g y
      (fun t => Finset.univ.filter (fun k => ∃ h : t < m, s (vU ⟨t, h⟩ k) = true))
      (fun t => Finset.univ.filter (fun k => ∃ h : t < m, s (vZ ⟨t, h⟩ k) = true))
    · intro _ k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      obtain ⟨h0, hk⟩ := hk
      have hw := hZW ⟨0, h0⟩ k rfl hk
      exact (hy k).2 ⟨hraw k hw, hcap k hw⟩
    · intro t _ k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      obtain ⟨h1, hk⟩ := hk
      exact ⟨by omega, hZU ⟨t, by omega⟩ ⟨t+1, h1⟩ k rfl hk⟩
    · intro t
      have hp := hg t
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
        obtain ⟨h1, hk⟩ := hk
        exact ⟨h1, hUZ _ _ hk⟩
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨_, hA _ _ _ hk hp⟩
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        obtain ⟨h1, hk⟩ := hk
        by_contra hb
        have := hB _ _ _ hb hp
        exact absurd (this.symm.trans hk) (by decide)
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨_, hC _ _ _ hk hp⟩
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        obtain ⟨h1, hk⟩ := hk
        by_contra hb
        have := hD _ _ _ hb hp
        exact absurd (this.symm.trans hk) (by decide)
  · rintro ⟨js, hlen, hN⟩
    obtain ⟨U, Z, h0, hs, hbx⟩ := chain_of_named a b c d js y hN
    refine ⟨asg y U Z js v l, ?_, ?_, ?_, ?_, ?_⟩
    · rintro e (⟨t, j, k, hk, rfl⟩ | ⟨t, j, k, hk, rfl⟩ | ⟨t, j, k, hk, rfl⟩ | ⟨t, j, k, hk, rfl⟩ |
        ⟨t, k, rfl⟩ | ⟨t, k, ht, rfl⟩ | ⟨t, t', k, ht, rfl⟩ | ⟨v', k, hk, rfl⟩ | ⟨l', t, ht, rfl⟩)
      · show asg y U Z js v l (vP t j) = false ∨ asg y U Z js v l (vU t k) = true
        simp only [asg_P, asg_U, decide_eq_false_iff_not, decide_eq_true_eq]
        by_cases hp : ∃ h : (t : ℕ) < js.length, js[(t : ℕ)] = j
        · obtain ⟨h, rfl⟩ := hp
          exact Or.inr ⟨by omega, (hbx t h).2.1 hk⟩
        · exact Or.inl hp
      · show asg y U Z js v l (vP t j) = false ∨ asg y U Z js v l (vU t k) = false
        simp only [asg_P, asg_U, decide_eq_false_iff_not]
        by_cases hp : ∃ h : (t : ℕ) < js.length, js[(t : ℕ)] = j
        · obtain ⟨h, rfl⟩ := hp
          exact Or.inr (fun hu => hk ((hbx t h).2.2.1 hu.2))
        · exact Or.inl hp
      · show asg y U Z js v l (vP t j) = false ∨ asg y U Z js v l (vZ t k) = true
        simp only [asg_P, asg_Z, decide_eq_false_iff_not, decide_eq_true_eq]
        by_cases hp : ∃ h : (t : ℕ) < js.length, js[(t : ℕ)] = j
        · obtain ⟨h, rfl⟩ := hp
          exact Or.inr ⟨by omega, (hbx t h).2.2.2.1 hk⟩
        · exact Or.inl hp
      · show asg y U Z js v l (vP t j) = false ∨ asg y U Z js v l (vZ t k) = false
        simp only [asg_P, asg_Z, decide_eq_false_iff_not]
        by_cases hp : ∃ h : (t : ℕ) < js.length, js[(t : ℕ)] = j
        · obtain ⟨h, rfl⟩ := hp
          exact Or.inr (fun hu => hk ((hbx t h).2.2.2.2 hu.2))
        · exact Or.inl hp
      · show asg y U Z js v l (vU t k) = false ∨ asg y U Z js v l (vZ t k) = true
        simp only [asg_U, asg_Z, decide_eq_false_iff_not, decide_eq_true_eq]
        by_cases hu : (t : ℕ) < l ∧ k ∈ U t
        · exact Or.inr ⟨hu.1, (hbx t (by omega)).1 hu.2⟩
        · exact Or.inl hu
      · show asg y U Z js v l (vZ t k) = false ∨ asg y U Z js v l (vW k) = true
        simp only [asg_Z, asg_W, decide_eq_false_iff_not, decide_eq_true_eq]
        by_cases hz : (t : ℕ) < l ∧ k ∈ Z t
        · obtain ⟨hz1, hz2⟩ := hz
          rw [ht] at hz2
          exact Or.inr (h0 (by omega) hz2)
        · exact Or.inl hz
      · show asg y U Z js v l (vZ t' k) = false ∨ asg y U Z js v l (vU t k) = true
        simp only [asg_Z, asg_U, decide_eq_false_iff_not, decide_eq_true_eq]
        by_cases hz : (t' : ℕ) < l ∧ k ∈ Z t'
        · obtain ⟨hz1, hz2⟩ := hz
          rw [ht] at hz2 hz1
          exact Or.inr ⟨by omega, hs t (by omega) hz2⟩
        · exact Or.inl hz
      · show asg y U Z js v l (vSel v') = false ∨ asg y U Z js v l (vW k) = false
        simp only [asg_Sel, asg_W, decide_eq_false_iff_not]
        by_cases hv : v' = v
        · subst hv
          exact Or.inr (fun hky => hk ((hy k).1 hky).2)
        · exact Or.inl hv
      · show asg y U Z js v l (vLev l') = false ∨ asg y U Z js v l (vAct t) = true
        simp only [asg_Lev, asg_Act, decide_eq_false_iff_not, decide_eq_true_eq]
        by_cases hv : l' = l
        · subst hv
          exact Or.inr ht
        · exact Or.inl hv
    · intro k hk
      simp only [asg_W, decide_eq_true_eq] at hk
      exact ((hy k).1 hk).1
    · simp [asg_Sel]
    · simp [asg_Lev]
    · intro t ht
      simp only [asg_Act, decide_eq_true_eq] at ht
      have h : (t : ℕ) < js.length := by omega
      refine ⟨js[(t : ℕ)], ?_⟩
      rw [asg_P, decide_eq_true_eq]
      exact ⟨h, rfl⟩

theorem rank_facts (m : ℕ) (P : ℕ → Prop) {inst : DecidablePred P} (h0 : P 0) :
    ((Finset.range (m+1)).filter P).sup id ≤ m ∧ P (((Finset.range (m+1)).filter P).sup id) ∧
      ∀ k, k ≤ m → P k → k ≤ ((Finset.range (m+1)).filter P).sup id := by
  refine ⟨?_, ?_, ?_⟩
  · apply Finset.sup_le
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    simp only [id]; omega
  · have hne : ((Finset.range (m+1)).filter P).Nonempty := ⟨0, by simp [h0]⟩
    obtain ⟨k, hk, hks⟩ := Finset.exists_mem_eq_sup _ hne id
    rw [hks]
    exact (Finset.mem_filter.1 hk).2
  · intro k hk hP
    exact Finset.le_sup (f := id) (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hP⟩)

theorem transport {L C V : Type} {T M N : ℕ} (eL : L ≃ Fin T) (eC : C ≃ Fin M) (eV : V ≃ Fin N)
    (cl : L → C) (vr : L → V) (sg : L → Bool) (Y : Finset (Fin T)) (Yq : L → Prop)
    (hY : ∀ i, eL i ∈ Y ↔ Yq i) :
    (∃ s : Fin N → Bool, ∀ j : Fin M, ∃ i ∈ Y, eC (cl (eL.symm i)) = j ∧
        s (eV (vr (eL.symm i))) = sg (eL.symm i)) ↔
    (∃ s : V → Bool, ∀ cc : C, ∃ i, cl i = cc ∧ Yq i ∧ s (vr i) = sg i) := by
  constructor
  · rintro ⟨s, h⟩
    refine ⟨fun z => s (eV z), fun cc => ?_⟩
    obtain ⟨i, hi, hcl, hs⟩ := h (eC cc)
    exact ⟨eL.symm i, eC.injective hcl, (hY _).1 (by simpa using hi), hs⟩
  · rintro ⟨s, h⟩
    refine ⟨fun z => s (eV.symm z), fun j => ?_⟩
    obtain ⟨i, hcl, hi, hs⟩ := h (eC.symm j)
    exact ⟨eL i, (hY i).2 hi, by simp [hcl], by simpa using hs⟩

theorem main : letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (n m : Nat) (a b c d : Fin m → Finset (Fin n)),
  (∀ j, ¬ ∃ y : Finset (Fin n), a j ⊆ y ∧ y ⊆ b j ∧ c j ⊆ y ∧ y ⊆ d j) →
  let named := fun (x : Finset (Fin n)) (js : List (Fin m)) =>
    List.rec (motive := fun _ => Finset (Fin n) → Prop) (fun _ => True)
      (fun j _ prev y => ∃ u v, prev u ∧ u ⊆ v ∧ v ⊆ y ∧
        a j ⊆ u ∧ u ⊆ b j ∧ c j ⊆ v ∧ v ⊆ d j) js x
  let rank := fun (x : Finset (Fin n)) => ((Finset.range (m+1)).filter (fun k =>
    ∃ js : List (Fin m), js.length=k ∧ named x js)).sup id
  let cap := fun v : Fin (m+1) => Fin.cases (motive := fun _ => Finset (Fin n)) Finset.univ b v
  ∃ (T M N : Nat) (cl : Fin T → Fin M) (vr : Fin T → Fin N) (sg : Fin T → Bool)
    (raw : Fin n ↪ Fin T) (mode level : Fin (m+1) ↪ Fin T) (base : Finset (Fin T)),
    T+M+N ≤ 128*(n+m+2)^4 ∧
    (∀ i, raw i ∉ base ∧ sg (raw i)=true) ∧
    (∀ v, mode v ∉ base ∧ level v ∉ base ∧ sg (mode v)=true ∧ sg (level v)=true) ∧
    (∀ i v, raw i ≠ mode v ∧ raw i ≠ level v) ∧ (∀ v l, mode v ≠ level l) ∧
    let sat := fun (Y : Finset (Fin T)) => ∃ s : Fin N → Bool, ∀ j : Fin M,
      ∃ i ∈ Y, cl i=j ∧ s (vr i)=sg i
    let ask := fun (x : Finset (Fin n)) (v l : Fin (m+1)) =>
      sat (insert (mode v) (insert (level l) (base ∪ x.map raw)))
    (∀ x v l, ask x v l ↔ ∃ js : List (Fin m), js.length=l.val ∧ named (x ∩ cap v) js) ∧
    ∀ (x : Finset (Fin n)) (j : Fin m),
      (∃ u : Finset (Fin n), u ⊆ x ∧ a j ⊆ u ∧ u ⊆ b j ∧ rank u=rank x) ↔
        a j ⊆ x ∧ a j ⊆ b j ∧ ∀ l : Fin (m+1), ask x 0 l → ask x j.succ l := by
  intro n m a b c d _ named rank cap
  classical
  obtain ⟨eL⟩ : Nonempty (Lit n m ≃ Fin (Fintype.card (Lit n m))) := ⟨Fintype.equivFin _⟩
  obtain ⟨eC⟩ : Nonempty (Cl n m ≃ Fin (Fintype.card (Cl n m))) := ⟨Fintype.equivFin _⟩
  obtain ⟨eV⟩ : Nonempty (Var n m ≃ Fin (Fintype.card (Var n m))) := ⟨Fintype.equivFin _⟩
  refine ⟨Fintype.card (Lit n m), Fintype.card (Cl n m), Fintype.card (Var n m),
    fun i => eC (clF (eL.symm i)), fun i => eV (vrF (eL.symm i)), fun i => sgF (eL.symm i),
    ⟨fun k => eL (rawF k), ?_⟩, ⟨fun v => eL (modeF v), ?_⟩, ⟨fun l => eL (levelF l), ?_⟩,
    (Finset.univ.filter (BaseP a b c d)).map eL.toEmbedding, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k k' h; simpa [rawF] using h
  · intro v v' h; simpa [modeF] using h
  · intro l l' h; simpa [levelF] using h
  · have hV : Fintype.card (Var n m) ≤ (n+m+2)^2 := by
      simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
      nlinarith
    have hL : Fintype.card (Lit n m) =
        12 * Fintype.card (Var n m) ^ 2 + 2*n + 2*(m+1) + m*(m+1) := by
      simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_option,
        Fintype.card_bool]
      ring
    have hC : Fintype.card (Cl n m) = 4 * Fintype.card (Var n m) ^ 2 + n + 2 + m := by
      simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
        Fintype.card_unit]
      ring
    rw [hL, hC]
    have hS1 : 1 ≤ n + m + 2 := by omega
    have hSS : (n+m+2) ≤ (n+m+2)^4 := Nat.le_self_pow (by norm_num) _
    have hS24 : (n+m+2)^2 ≤ (n+m+2)^4 := Nat.pow_le_pow_right hS1 (by norm_num)
    have hV2 : Fintype.card (Var n m) ^ 2 ≤ (n+m+2)^4 := by
      calc Fintype.card (Var n m) ^ 2 ≤ ((n+m+2)^2)^2 := Nat.pow_le_pow_left hV 2
        _ = (n+m+2)^4 := by ring
    have hmm : m*(m+1) ≤ (n+m+2)^2 := by nlinarith
    have hQ : 1 ≤ (n+m+2)^4 := Nat.one_le_pow _ _ (by omega)
    linarith
  · intro i; simp [rawF, BaseP, sgF]
  · intro v; simp [modeF, levelF, BaseP, sgF]
  · intro i v; simp [rawF, modeF, levelF]
  · intro v l; simp [modeF, levelF]
  · intro sat ask
    have hc0 : cap 0 = Finset.univ := capF_zero b
    have hcs : ∀ j : Fin m, cap j.succ = b j := capF_succ b
    have key : ∀ x v l (y : Finset (Fin n)), (∀ k, k ∈ y ↔ k ∈ x ∧ k ∈ cap v) →
        (ask x v l ↔ ∃ js : List (Fin m), js.length = l.val ∧ named y js) := by
      intro x v l y hy
      refine Iff.trans ?_ (ask_iff a b c d x v l y hy)
      refine transport eL eC eV clF vrF sgF _ (Yp a b c d x v l) ?_
      intro i
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_map, Finset.mem_filter,
        Finset.mem_univ, true_and]
      show (eL i = eL (modeF v) ∨ eL i = eL (levelF l) ∨
        (∃ a_1, BaseP a b c d a_1 ∧ eL a_1 = eL i) ∨ ∃ a ∈ x, eL (rawF a) = eL i) ↔ _
      simp only [Yp, EmbeddingLike.apply_eq_iff_eq, exists_eq_right]
      constructor
      · rintro (h | h | h | h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · rintro (h | h | h | h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
    refine ⟨fun x v l => key x v l _ (fun k => by simp only [Finset.mem_inter]), ?_⟩
    intro x j
    have P0 : ∀ y : Finset (Fin n), ∃ js : List (Fin m), js.length = 0 ∧ named y js :=
      fun y => ⟨[], rfl, trivial⟩
    have Pmono : ∀ (y y' : Finset (Fin n)) (k : ℕ), y ⊆ y' →
        (∃ js : List (Fin m), js.length = k ∧ named y js) →
        ∃ js : List (Fin m), js.length = k ∧ named y' js := by
      rintro y y' k hyy ⟨js, hl, hn⟩
      exact ⟨js, hl, named_mono a b c d js y y' hyy hn⟩
    have Pdown : ∀ (y : Finset (Fin n)) (k k' : ℕ), k ≤ k' →
        (∃ js : List (Fin m), js.length = k' ∧ named y js) →
        ∃ js : List (Fin m), js.length = k ∧ named y js := by
      rintro y k k' hkk ⟨js, hl, hn⟩
      exact ⟨js.drop (k' - k), by rw [List.length_drop, hl]; omega,
        named_drop a b c d y (k' - k) js hn⟩
    have hr : ∀ y : Finset (Fin n), rank y ≤ m ∧
        (∃ js : List (Fin m), js.length = rank y ∧ named y js) ∧
        ∀ k, k ≤ m → (∃ js : List (Fin m), js.length = k ∧ named y js) → k ≤ rank y :=
      fun y => rank_facts m _ (P0 y)
    have hi0 : ∀ l : Fin (m+1), ask x 0 l ↔ ∃ js : List (Fin m), js.length = l.val ∧ named x js :=
      fun l => key x 0 l x (fun k => by rw [hc0]; simp)
    have hij : ∀ l : Fin (m+1), ask x j.succ l ↔
        ∃ js : List (Fin m), js.length = l.val ∧ named (x ∩ b j) js :=
      fun l => key x j.succ l (x ∩ b j) (fun k => by rw [hcs, Finset.mem_inter])
    constructor
    · rintro ⟨u, hux, hau, hub, hru⟩
      refine ⟨hau.trans hux, hau.trans hub, fun l hl => ?_⟩
      have h2 := (hi0 l).1 hl
      have h3 : l.val ≤ rank u := by
        rw [hru]; exact (hr x).2.2 _ (Nat.lt_succ_iff.mp l.isLt) h2
      have h4 := Pdown u l.val (rank u) h3 (hr u).2.1
      exact (hij l).2 (Pmono _ _ _ (fun k hk => Finset.mem_inter.2 ⟨hux hk, hub hk⟩) h4)
    · rintro ⟨hax, hab, hl⟩
      refine ⟨x ∩ b j, Finset.inter_subset_left, Finset.subset_inter hax hab,
        Finset.inter_subset_right, ?_⟩
      apply le_antisymm
      · exact (hr x).2.2 _ (hr _).1 (Pmono _ _ _ Finset.inter_subset_left (hr _).2.1)
      · have h5 := (hi0 ⟨rank x, Nat.lt_succ_of_le (hr x).1⟩).2 (hr x).2.1
        exact (hr _).2.2 _ (hr x).1 ((hij _).1 (hl _ h5))

end PEqualNP.Outside.L_lib_1258_aux

theorem PEqualNP.Outside.L_lib_1258 : letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (n m : Nat) (a b c d : Fin m → Finset (Fin n)),
  (∀ j, ¬ ∃ y : Finset (Fin n), a j ⊆ y ∧ y ⊆ b j ∧ c j ⊆ y ∧ y ⊆ d j) →
  let named := fun (x : Finset (Fin n)) (js : List (Fin m)) =>
    List.rec (motive := fun _ => Finset (Fin n) → Prop) (fun _ => True)
      (fun j _ prev y => ∃ u v, prev u ∧ u ⊆ v ∧ v ⊆ y ∧
        a j ⊆ u ∧ u ⊆ b j ∧ c j ⊆ v ∧ v ⊆ d j) js x
  let rank := fun (x : Finset (Fin n)) => ((Finset.range (m+1)).filter (fun k =>
    ∃ js : List (Fin m), js.length=k ∧ named x js)).sup id
  let cap := fun v : Fin (m+1) => Fin.cases (motive := fun _ => Finset (Fin n)) Finset.univ b v
  ∃ (T M N : Nat) (cl : Fin T → Fin M) (vr : Fin T → Fin N) (sg : Fin T → Bool)
    (raw : Fin n ↪ Fin T) (mode level : Fin (m+1) ↪ Fin T) (base : Finset (Fin T)),
    T+M+N ≤ 128*(n+m+2)^4 ∧
    (∀ i, raw i ∉ base ∧ sg (raw i)=true) ∧
    (∀ v, mode v ∉ base ∧ level v ∉ base ∧ sg (mode v)=true ∧ sg (level v)=true) ∧
    (∀ i v, raw i ≠ mode v ∧ raw i ≠ level v) ∧ (∀ v l, mode v ≠ level l) ∧
    let sat := fun (Y : Finset (Fin T)) => ∃ s : Fin N → Bool, ∀ j : Fin M,
      ∃ i ∈ Y, cl i=j ∧ s (vr i)=sg i
    let ask := fun (x : Finset (Fin n)) (v l : Fin (m+1)) =>
      sat (insert (mode v) (insert (level l) (base ∪ x.map raw)))
    (∀ x v l, ask x v l ↔ ∃ js : List (Fin m), js.length=l.val ∧ named (x ∩ cap v) js) ∧
    ∀ (x : Finset (Fin n)) (j : Fin m),
      (∃ u : Finset (Fin n), u ⊆ x ∧ a j ⊆ u ∧ u ⊆ b j ∧ rank u=rank x) ↔
        a j ⊆ x ∧ a j ⊆ b j ∧ ∀ l : Fin (m+1), ask x 0 l → ask x j.succ l :=
  L_lib_1258_aux.main
