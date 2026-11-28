import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38075_aux

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def mask256 : Nat := 2 ^ 256 - 1

def negD (d w : Nat) : Nat := (w ^^^ mask256) &&& d
def andD (d a b : Nat) : Nat := (a &&& b) &&& d
def orD (d a b : Nat) : Nat := (a ||| b) &&& d
def binD (d : Nat) (isOr : Bool) (a b : Nat) : Nat := if isOr then orD d a b else andD d a b

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

def RunD (d y : Nat) (t : ℕ) (ws : List Nat) : Prop :=
  ∀ P : ℕ → List Nat → Prop, P 0 [y] →
    (∀ {s xs zs}, List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a r} (save : Bool),
      negD d a ≠ 0 → negD d a ≠ d → negD d a ∉ (a :: r) →
      P s (negD d a :: kept save a r) → P (s + 1) (a :: r)) →
    (∀ {s a b r} (c ka kb : Bool),
      (if c then andD d a b else orD d a b) ≠ 0 →
      (if c then andD d a b else orD d a b) ≠ d →
      (if c then andD d a b else orD d a b) ∉ (a :: b :: r) →
      P s ((if c then andD d a b else orD d a b) :: kept ka a (kept kb b r)) →
      P (s + 1) (a :: b :: r)) → P t ws

section RunFacts
variable {d y : Nat}

theorem Run.done : RunD d y 0 [y] := fun _ dn _ _ _ => dn
theorem Run.perm {s xs zs} (p : List.Perm xs zs) (h : RunD d y s xs) :
    RunD d y s zs := fun P dn q u b => q p (h P dn q u b)
theorem Run.one {s a r} (save : Bool)
    (h0 : negD d a ≠ 0) (hd : negD d a ≠ d) (hm : negD d a ∉ (a :: r))
    (h : RunD d y s (negD d a :: kept save a r)) :
    RunD d y (s + 1) (a :: r) := fun P dn q u b => u save h0 hd hm (h P dn q u b)
theorem Run.two {s a b r} (c ka kb : Bool)
    (h0 : (if c then andD d a b else orD d a b) ≠ 0)
    (hd : (if c then andD d a b else orD d a b) ≠ d)
    (hm : (if c then andD d a b else orD d a b) ∉ (a :: b :: r))
    (h : RunD d y s ((if c then andD d a b else orD d a b) :: kept ka a (kept kb b r))) :
    RunD d y (s + 1) (a :: b :: r) := fun P dn q u v => v c ka kb h0 hd hm (h P dn q u v)

theorem Run.fold {P : ∀ t ws, RunD d y t ws → Prop}
    (done : P 0 [y] Run.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : RunD d y s xs),
      P s xs h → P s zs (Run.perm hp h))
    (one : ∀ {s a r} (save : Bool)
      (h0 : negD d a ≠ 0) (hd : negD d a ≠ d) (hm : negD d a ∉ (a :: r))
      (h : RunD d y s (negD d a :: kept save a r)),
      P _ _ h → P _ _ (Run.one save h0 hd hm h))
    (two : ∀ {s a b r} (c ka kb : Bool)
      (h0 : (if c then andD d a b else orD d a b) ≠ 0)
      (hd : (if c then andD d a b else orD d a b) ≠ d)
      (hm : (if c then andD d a b else orD d a b) ∉ (a :: b :: r))
      (h : RunD d y s ((if c then andD d a b else orD d a b) :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (Run.two c ka kb h0 hd hm h))
    {t ws} (h : RunD d y t ws) : P t ws h := by
  have hex := h (fun s xs => ∃ h' : RunD d y s xs, P s xs h')
    ⟨Run.done, done⟩
    (fun hp ⟨h', ih⟩ => ⟨Run.perm hp h', perm hp h' ih⟩)
    (fun k h0 hd hm ⟨h', ih⟩ => ⟨Run.one k h0 hd hm h', one k h0 hd hm h' ih⟩)
    (fun c a b h0 hd hm ⟨h', ih⟩ => ⟨Run.two c a b h0 hd hm h', two c a b h0 hd hm h' ih⟩)
  exact hex.elim fun _ hp => hp
end RunFacts

theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by cases b <;> simp [kept]

theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by cases b <;> simp [kept]

theorem nodup_kept {α : Type} (b : Bool) (x : α) (xs : List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup := by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h

theorem keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

theorem run_len {d y s xs} (h : RunD d y s xs) :
    xs.length ≤ s + 1 := by
  induction h using Run.fold with
  | done => simp
  | perm hp _ ih => rwa [← hp.length_eq]
  | one save _ _ _ _ ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb _ _ _ _ ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

theorem zero_done {d y t ws} (h : RunD d y t ws) :
    t = 0 → ws = [y] := by
  induction h using Run.fold with
  | done => simp
  | perm p _ ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

def IsConst (d w : Nat) : Prop := (w &&& d) = 0 ∨ (w &&& d) = d
def isConstB (d w : Nat) : Bool := (w &&& d == 0) || (w &&& d == d)

theorem isConstB_iff (d w : Nat) : isConstB d w = true ↔ IsConst d w := by
  simp [isConstB, IsConst]

def Avail (d : Nat) (bank : List Nat) (w : Nat) : Prop :=
  IsConst d w ∨ ∃ v ∈ bank, (v &&& d) = (w &&& d)

def availB (d : Nat) (bank : List Nat) (w : Nat) : Bool :=
  let m := w &&& d
  m == 0 || m == d || bank.any (fun v => (v &&& d) == m)

theorem availB_iff (d : Nat) (bank : List Nat) (w : Nat) :
    availB d bank w = true ↔ Avail d bank w := by
  simp [availB, Avail, IsConst, or_assoc]

def NatReach (d : Nat) (roots : List Nat) : Nat → List Nat → Prop
  | 0, bank => bank = roots
  | p + 1, bank =>
    (∃ b a, bank = negD d a :: b ∧ NatReach d roots p b ∧ Avail d b a) ∨
    (∃ b a c op, bank = binD d op a c :: b ∧ NatReach d roots p b ∧ Avail d b a ∧ Avail d b c)

def Lower (d : Nat) (roots : List Nat) (T : Nat) (L : Nat) : Prop :=
  ∀ p bank, NatReach d roots p bank → Avail d bank T → L ≤ p

theorem mask256_bit (i : Nat) : mask256.testBit i = decide (i < 256) := by
  rw [mask256, Nat.testBit_two_pow_sub_one]

theorem negD_and_sub {d d1 : Nat} (hd : d &&& mask256 = d) (hsub : d &&& d1 = d) (a : Nat) :
    negD d1 a &&& d = negD d a := by
  apply Nat.eq_of_testBit_eq; intro i
  have h1 := congrArg (fun v => v.testBit i) hd
  have h2 := congrArg (fun v => v.testBit i) hsub
  simp only [negD, Nat.testBit_and, Nat.testBit_xor] at *
  cases hi : d.testBit i <;> simp_all

theorem andD_and_sub {d d1 : Nat} (hsub : d &&& d1 = d) (a b : Nat) :
    andD d1 a b &&& d = andD d a b := by
  apply Nat.eq_of_testBit_eq; intro i
  have h2 := congrArg (fun v => v.testBit i) hsub
  simp only [andD, Nat.testBit_and] at *
  cases hi : d.testBit i <;> simp_all

theorem orD_and_sub {d d1 : Nat} (hsub : d &&& d1 = d) (a b : Nat) :
    orD d1 a b &&& d = orD d a b := by
  apply Nat.eq_of_testBit_eq; intro i
  have h2 := congrArg (fun v => v.testBit i) hsub
  simp only [orD, Nat.testBit_and, Nat.testBit_or] at *
  cases hi : d.testBit i <;> simp_all

theorem negD_const {d : Nat} (hd : d &&& mask256 = d) {a : Nat} (hc : IsConst d a) :
    IsConst d (negD d a) := by
  rcases hc with h0 | h1
  · right; apply Nat.eq_of_testBit_eq; intro i
    have h0i := congrArg (fun v => v.testBit i) h0
    have hdi := congrArg (fun v => v.testBit i) hd
    simp only [negD, Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit] at *
    cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
  · left; apply Nat.eq_of_testBit_eq; intro i
    have h1i := congrArg (fun v => v.testBit i) h1
    have hdi := congrArg (fun v => v.testBit i) hd
    simp only [negD, Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit] at *
    cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all

theorem binD_const_left {d : Nat} {a b : Nat} (op : Bool) (hc : IsConst d a) :
    (binD d op a b &&& d = 0) ∨ (binD d op a b &&& d = d) ∨ (binD d op a b &&& d = b &&& d) := by
  rcases hc with h0 | h1
  · cases op
    · left; apply Nat.eq_of_testBit_eq; intro i
      have h0i := congrArg (fun v => v.testBit i) h0
      simp only [binD, andD, Nat.testBit_and, Nat.zero_testBit, ite_false] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
    · right; right; apply Nat.eq_of_testBit_eq; intro i
      have h0i := congrArg (fun v => v.testBit i) h0
      simp only [binD, orD, Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit, ite_true] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
  · cases op
    · right; right; apply Nat.eq_of_testBit_eq; intro i
      have h1i := congrArg (fun v => v.testBit i) h1
      simp only [binD, andD, Nat.testBit_and, ite_false] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
    · right; left; apply Nat.eq_of_testBit_eq; intro i
      have h1i := congrArg (fun v => v.testBit i) h1
      simp only [binD, orD, Nat.testBit_and, Nat.testBit_or, ite_true] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all

theorem binD_comm (d : Nat) (op : Bool) (a b : Nat) : binD d op a b = binD d op b a := by
  cases op <;> simp [binD, andD, orD, Nat.and_comm, Nat.or_comm]

theorem avail_cons {d : Nat} {bank : List Nat} (z w : Nat) (h : Avail d bank w) :
    Avail d (z :: bank) w := by
  rcases h with hc | ⟨v, hv, he⟩
  · exact Or.inl hc
  · exact Or.inr ⟨v, List.mem_cons_of_mem _ hv, he⟩

theorem avail_of_eq {d : Nat} {bank : List Nat} {v w : Nat}
    (he : v &&& d = w &&& d) (h : Avail d bank v) : Avail d bank w := by
  rcases h with (h0 | h1) | ⟨u, hu, hue⟩
  · exact Or.inl (Or.inl (he.symm.trans h0))
  · exact Or.inl (Or.inr (he.symm.trans h1))
  · exact Or.inr ⟨u, hu, hue.trans he⟩

theorem countP_kept_ge {α : Type} (p : α → Bool) (b : Bool) (a : α) (xs : List α) :
    xs.countP p ≤ (kept b a xs).countP p := by
  cases b <;> simp [kept, List.countP_cons] <;> split <;> omega

theorem contraction {d d1 T : Nat} (hd : d &&& mask256 = d) (hsub : d &&& d1 = d)
    (hnc : ¬ IsConst d T) {s ws} (h : RunD d1 T s ws) {roots p bank}
    (hp : NatReach d roots p bank) (hs : ∀ w ∈ ws, Avail d bank w) :
    ∃ q next, NatReach d roots q next ∧ Avail d next T ∧
      q + ws.countP (isConstB d) ≤ p + s := by
  induction h using Run.fold generalizing p bank with
  | done =>
    have hfalse : isConstB d T = false := by
      cases hc : isConstB d T with
      | false => rfl
      | true => exact absurd ((isConstB_iff d T).1 hc) hnc
    exact ⟨p, bank, hp, hs T (by simp), by simp [hfalse]⟩
  | perm eq _ ih =>
    obtain ⟨q, next, hq, ht, hle⟩ := ih hp (fun w hw => hs w (eq.mem_iff.1 hw))
    rw [eq.countP_eq] at hle
    exact ⟨q, next, hq, ht, hle⟩
  | @one s a r save _ _ _ _ ih =>
    have ha := hs a List.mem_cons_self
    by_cases hca : IsConst d a
    · have hc_neg : IsConst d (negD d1 a) := by
        have e := negD_and_sub hd hsub a
        rcases negD_const hd hca with h0 | h1
        · exact Or.inl (e.trans (by simpa [negD, Nat.and_assoc, Nat.and_self] using h0))
        · exact Or.inr (e.trans (by simpa [negD, Nat.and_assoc, Nat.and_self] using h1))
      have hs' : ∀ w ∈ negD d1 a :: kept save a r, Avail d bank w := by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact Or.inl hc_neg
        · exact hs w (by rw [mem_kept] at hw; rcases hw with ⟨_, rfl⟩ | hw <;> simp [hw])
      obtain ⟨q, next, hq, ht, hle⟩ := ih hp hs'
      have h1 : isConstB d (negD d1 a) = true := (isConstB_iff _ _).2 hc_neg
      have h2 : isConstB d a = true := (isConstB_iff _ _).2 hca
      have hk := countP_kept_ge (isConstB d) save a r
      simp only [List.countP_cons, h1, h2, ite_true] at hle ⊢
      exact ⟨q, next, hq, ht, by omega⟩
    · have hreach' : NatReach d roots (p + 1) (negD d a :: bank) := Or.inl ⟨bank, a, rfl, hp, ha⟩
      have hneg_av : Avail d (negD d a :: bank) (negD d1 a) :=
        Or.inr ⟨negD d a, List.mem_cons_self, by rw [negD_and_sub hd hsub a]; simp [negD, Nat.and_assoc, Nat.and_self]⟩
      have hs' : ∀ w ∈ negD d1 a :: kept save a r, Avail d (negD d a :: bank) w := by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact hneg_av
        · exact avail_cons _ _ (hs w (by rw [mem_kept] at hw; rcases hw with ⟨_, rfl⟩ | hw <;> simp [hw]))
      obtain ⟨q, next, hq, ht, hle⟩ := ih hreach' hs'
      have h2 : isConstB d a = false := by
        cases h : isConstB d a with | false => rfl | true => exact absurd ((isConstB_iff _ _).1 h) hca
      have hk := countP_kept_ge (isConstB d) save a r
      simp only [List.countP_cons, h2, Bool.false_eq_true, ite_false] at hle ⊢
      exact ⟨q, next, hq, ht, by omega⟩
  | @two s a b r conj ka kb _ _ _ _ ih =>
    have ha := hs a List.mem_cons_self
    have hb := hs b (List.mem_cons_of_mem _ List.mem_cons_self)
    set z1 := if conj then andD d1 a b else orD d1 a b
    set z0 := binD d (!conj) a b
    have hz_eq : z1 &&& d = z0 &&& d := by
      cases conj
      · simp only [z1, z0, Bool.false_eq_true, ite_false, Bool.not_false, binD, ite_true]
        rw [orD_and_sub hsub]; simp [orD, Nat.and_assoc, Nat.and_self]
      · simp only [z1, z0, ite_true, Bool.not_true, Bool.false_eq_true, binD, ite_false]
        rw [andD_and_sub hsub]; simp [andD, Nat.and_assoc, Nat.and_self]
    by_cases hcab : IsConst d a ∨ IsConst d b
    · have hz_av : Avail d bank z1 := by
        apply avail_of_eq hz_eq.symm
        rcases hcab with hca | hcb
        · rcases binD_const_left (!conj) hca with h0 | h1 | he
          · exact Or.inl (Or.inl h0)
          · exact Or.inl (Or.inr h1)
          · exact avail_of_eq he.symm hb
        · dsimp only [z0]; rw [binD_comm]
          rcases binD_const_left (!conj) hcb with h0 | h1 | he
          · exact Or.inl (Or.inl h0)
          · exact Or.inl (Or.inr h1)
          · exact avail_of_eq he.symm ha
      have hs' : ∀ w ∈ z1 :: kept ka a (kept kb b r), Avail d bank w := by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact hz_av
        · rw [mem_kept, mem_kept] at hw
          rcases hw with ⟨_, rfl⟩ | ⟨_, rfl⟩ | hw
          · exact ha
          · exact hb
          · exact hs w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw))
      obtain ⟨q, next, hq, ht, hle⟩ := ih hp hs'
      have hkr : r.countP (isConstB d) ≤ (kept ka a (kept kb b r)).countP (isConstB d) :=
        le_trans (countP_kept_ge _ kb b r) (countP_kept_ge _ ka a _)
      have hcost : (if isConstB d a = true then 1 else 0) + (if isConstB d b = true then 1 else 0)
          ≤ 1 + (if isConstB d z1 = true then 1 else 0) := by
        rcases hcab with hca | hcb
        · have ha1 : isConstB d a = true := (isConstB_iff _ _).2 hca
          rcases binD_const_left (!conj) hca with h0 | h1 | he
          · have hz1 : isConstB d z1 = true := (isConstB_iff _ _).2 (Or.inl (hz_eq.trans h0))
            simp [ha1, hz1]; split <;> omega
          · have hz1 : isConstB d z1 = true := (isConstB_iff _ _).2 (Or.inr (hz_eq.trans h1))
            simp [ha1, hz1]; split <;> omega
          · have hzb : isConstB d z1 = isConstB d b := by
              simp only [isConstB, hz_eq.trans he]
            simp [ha1, hzb]
        · have hb1 : isConstB d b = true := (isConstB_iff _ _).2 hcb
          have hz_eq' : z1 &&& d = binD d (!conj) b a &&& d := by rw [hz_eq, binD_comm]
          rcases binD_const_left (!conj) hcb with h0 | h1 | he
          · have hz1 : isConstB d z1 = true := (isConstB_iff _ _).2 (Or.inl (hz_eq'.trans h0))
            simp [hb1, hz1]; split <;> omega
          · have hz1 : isConstB d z1 = true := (isConstB_iff _ _).2 (Or.inr (hz_eq'.trans h1))
            simp [hb1, hz1]; split <;> omega
          · have hza : isConstB d z1 = isConstB d a := by
              simp only [isConstB, hz_eq'.trans he]
            simp [hb1, hza]
      simp only [List.countP_cons] at hle ⊢
      exact ⟨q, next, hq, ht, by omega⟩
    · have hna : isConstB d a = false := by
        cases h : isConstB d a with | false => rfl | true => exact absurd (Or.inl ((isConstB_iff _ _).1 h)) hcab
      have hnb : isConstB d b = false := by
        cases h : isConstB d b with | false => rfl | true => exact absurd (Or.inr ((isConstB_iff _ _).1 h)) hcab
      have hreach' : NatReach d roots (p + 1) (z0 :: bank) := Or.inr ⟨bank, a, b, !conj, rfl, hp, ha, hb⟩
      have hz_av : Avail d (z0 :: bank) z1 := Or.inr ⟨z0, List.mem_cons_self, hz_eq.symm⟩
      have hs' : ∀ w ∈ z1 :: kept ka a (kept kb b r), Avail d (z0 :: bank) w := by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact hz_av
        · rw [mem_kept, mem_kept] at hw
          rcases hw with ⟨_, rfl⟩ | ⟨_, rfl⟩ | hw
          · exact avail_cons _ _ ha
          · exact avail_cons _ _ hb
          · exact avail_cons _ _ (hs w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)))
      obtain ⟨q, next, hq, ht, hle⟩ := ih hreach' hs'
      have hkr : r.countP (isConstB d) ≤ (kept ka a (kept kb b r)).countP (isConstB d) :=
        le_trans (countP_kept_ge _ kb b r) (countP_kept_ge _ ka a _)
      simp only [List.countP_cons, hna, hnb, Bool.false_eq_true, ite_false] at hle ⊢
      exact ⟨q, next, hq, ht, by omega⟩

theorem mask_idemp (d w : Nat) : (w &&& d) &&& d = w &&& d := by
  simp [Nat.and_assoc, Nat.and_self]

theorem negD_mask (d a : Nat) : negD d (a &&& d) = negD d a := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [negD, Nat.testBit_and, Nat.testBit_xor]
  cases d.testBit i <;> simp

theorem andD_mask (d a b : Nat) : andD d (a &&& d) (b &&& d) = andD d a b := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [andD, Nat.testBit_and]
  cases d.testBit i <;> simp

theorem orD_mask (d a b : Nat) : orD d (a &&& d) (b &&& d) = orD d a b := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [orD, Nat.testBit_and, Nat.testBit_or]
  cases d.testBit i <;> simp

theorem pull_one {d Y k ws} (hd : d &&& mask256 = d) (hnd : ws.Nodup)
    (hprop : ∀ w ∈ ws, w ≠ 0 ∧ w ≠ d) (h : RunD d Y k ws)
    {b : List Nat} {a : Nat} (ha : Avail d b a) (hsub : ∀ w ∈ ws, w ∈ negD d a :: b.map (· &&& d)) :
    ∃ k' ws', k' ≤ k + 1 ∧ ws'.Nodup ∧ (∀ w ∈ ws', w ≠ 0 ∧ w ≠ d) ∧
      (∀ w ∈ ws', w ∈ b.map (· &&& d)) ∧ RunD d Y k' ws' := by
  set z := negD d a
  by_cases hzm : z ∈ ws
  · by_cases hzb : z ∈ b.map (· &&& d)
    · exact ⟨k, ws, by omega, hnd, hprop, fun w hw => by
        rcases List.mem_cons.1 (hsub w hw) with rfl | hm
        · exact hzb
        · exact hm, h⟩
    · have hzp := hprop z hzm
      have ha_nc : ¬ IsConst d a := by
        intro hc
        rcases negD_const hd hc with h0 | h1
        · exact hzp.1 (by simpa [z, negD, Nat.and_assoc, Nat.and_self] using h0)
        · exact hzp.2 (by simpa [z, negD, Nat.and_assoc, Nat.and_self] using h1)
      obtain ⟨v, hv, hve⟩ := ha.resolve_left ha_nc
      set a' := a &&& d
      have ha'_mem : a' ∈ b.map (· &&& d) := List.mem_map.2 ⟨v, hv, hve⟩
      have ha'_prop : a' ≠ 0 ∧ a' ≠ d := ⟨fun e => ha_nc (Or.inl e), fun e => ha_nc (Or.inr e)⟩
      set rest := ws.erase z
      have hrest_nd : rest.Nodup := hnd.erase z
      have hrest_sub : ∀ w ∈ rest, w ∈ b.map (· &&& d) := by
        intro w hw
        have ⟨hne, hm⟩ := hnd.mem_erase_iff.1 hw
        rcases List.mem_cons.1 (hsub w hm) with rfl | hmb
        · exact absurd rfl hne
        · exact hmb
      have hrest_prop : ∀ w ∈ rest, w ≠ 0 ∧ w ≠ d := fun w hw => hprop w (List.mem_of_mem_erase hw)
      have hp1 : ws.Perm (z :: rest) := List.perm_cons_erase hzm
      have ez : negD d a' = z := negD_mask d a
      have h1 : RunD d Y k (negD d a' :: rest) := by
        rw [ez]; exact Run.perm hp1 h
      have hne0 : negD d a' ≠ 0 := ez.symm ▸ hzp.1
      have hned : negD d a' ≠ d := ez.symm ▸ hzp.2
      by_cases ham : a' ∈ rest
      · have hp2 : rest.Perm (a' :: rest.erase a') := List.perm_cons_erase ham
        have h2 : RunD d Y k (negD d a' :: kept true a' (rest.erase a')) :=
          Run.perm (hp2.cons _) h1
        have hnm : negD d a' ∉ (a' :: rest.erase a') := by
          rw [ez, List.mem_cons]; rintro (e | hm)
          · exact hzb (e ▸ ha'_mem)
          · exact hnd.not_mem_erase (List.mem_of_mem_erase hm)
        refine ⟨k + 1, rest, le_rfl, hrest_nd, hrest_prop, hrest_sub, ?_⟩
        exact Run.perm hp2.symm (Run.one true hne0 hned hnm h2)
      · have h2 : RunD d Y k (negD d a' :: kept false a' rest) := h1
        have hnm : negD d a' ∉ (a' :: rest) := by
          rw [ez, List.mem_cons]; rintro (e | hm)
          · exact hzb (e ▸ ha'_mem)
          · exact hnd.not_mem_erase hm
        refine ⟨k + 1, a' :: rest, le_rfl, List.nodup_cons.2 ⟨ham, hrest_nd⟩, ?_, ?_, Run.one false hne0 hned hnm h2⟩
        · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
          · exact ha'_prop
          · exact hrest_prop w hw
        · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
          · exact ha'_mem
          · exact hrest_sub w hw
  · exact ⟨k, ws, by omega, hnd, hprop, fun w hw => by
      rcases List.mem_cons.1 (hsub w hw) with rfl | hm
      · exact absurd hw hzm
      · exact hm, h⟩

theorem pull_two {d Y k ws} (hnd : ws.Nodup)
    (hprop : ∀ w ∈ ws, w ≠ 0 ∧ w ≠ d) (h : RunD d Y k ws)
    {b : List Nat} {a c : Nat} (op : Bool) (ha : Avail d b a) (hc : Avail d b c)
    (hsub : ∀ w ∈ ws, w ∈ binD d op a c :: b.map (· &&& d)) :
    ∃ k' ws', k' ≤ k + 1 ∧ ws'.Nodup ∧ (∀ w ∈ ws', w ≠ 0 ∧ w ≠ d) ∧
      (∀ w ∈ ws', w ∈ b.map (· &&& d)) ∧ RunD d Y k' ws' := by
  set z := binD d op a c
  have hz_mask : z &&& d = z := by cases op <;> simp [z, binD, andD, orD, Nat.and_assoc, Nat.and_self]
  by_cases hzm : z ∈ ws
  · by_cases hzb : z ∈ b.map (· &&& d)
    · exact ⟨k, ws, by omega, hnd, hprop, fun w hw => by
        rcases List.mem_cons.1 (hsub w hw) with rfl | hm
        · exact hzb
        · exact hm, h⟩
    · have hzp := hprop z hzm
      have ha_nc : ¬ IsConst d a := by
        intro hca
        rcases binD_const_left op hca with h0 | h1 | he
        · exact hzp.1 (hz_mask.symm.trans h0)
        · exact hzp.2 (hz_mask.symm.trans h1)
        · rcases hc with hcc | ⟨v, hv, hve⟩
          · rcases hcc with h0 | h1
            · exact hzp.1 (hz_mask.symm.trans (he.trans h0))
            · exact hzp.2 (hz_mask.symm.trans (he.trans h1))
          · exact hzb (List.mem_map.2 ⟨v, hv, hve.trans (he.symm.trans hz_mask)⟩)
      have hc_nc : ¬ IsConst d c := by
        intro hcc
        have hz' : z = binD d op c a := binD_comm d op a c
        rcases binD_const_left op hcc with h0 | h1 | he
        · exact hzp.1 (hz_mask.symm.trans (by rw [hz']; exact h0))
        · exact hzp.2 (hz_mask.symm.trans (by rw [hz']; exact h1))
        · rcases ha with hca | ⟨v, hv, hve⟩
          · exact absurd hca ha_nc
          · have he' : z &&& d = a &&& d := hz'.symm ▸ he
            exact hzb (List.mem_map.2 ⟨v, hv, hve.trans (he'.symm.trans hz_mask)⟩)
      obtain ⟨va, hva, hvae⟩ := ha.resolve_left ha_nc
      obtain ⟨vc, hvc, hvce⟩ := hc.resolve_left hc_nc
      set a' := a &&& d
      set c' := c &&& d
      have ha'_mem : a' ∈ b.map (· &&& d) := List.mem_map.2 ⟨va, hva, hvae⟩
      have hc'_mem : c' ∈ b.map (· &&& d) := List.mem_map.2 ⟨vc, hvc, hvce⟩
      have ha'_prop : a' ≠ 0 ∧ a' ≠ d := ⟨fun e => ha_nc (Or.inl e), fun e => ha_nc (Or.inr e)⟩
      have hc'_prop : c' ≠ 0 ∧ c' ≠ d := ⟨fun e => hc_nc (Or.inl e), fun e => hc_nc (Or.inr e)⟩
      have hne_ac : a' ≠ c' := by
        intro heq
        dsimp only [a', c'] at heq
        have hz_eq : z = a' := by
          cases op
          · simp only [z, binD, Bool.false_eq_true, ite_false]; rw [← andD_mask, ← heq]; simp [andD, a', Nat.and_assoc, Nat.and_self]
          · simp only [z, binD, ite_true]; rw [← orD_mask, ← heq]; simp [orD, a', Nat.and_assoc, Nat.and_self]
        exact hzb (hz_eq ▸ ha'_mem)
      set rest := ws.erase z
      have hrest_nd : rest.Nodup := hnd.erase z
      have hrest_sub : ∀ w ∈ rest, w ∈ b.map (· &&& d) := by
        intro w hw
        have ⟨hne, hm⟩ := hnd.mem_erase_iff.1 hw
        rcases List.mem_cons.1 (hsub w hm) with rfl | hmb
        · exact absurd rfl hne
        · exact hmb
      have hrest_prop : ∀ w ∈ rest, w ≠ 0 ∧ w ≠ d := fun w hw => hprop w (List.mem_of_mem_erase hw)
      have hp1 : ws.Perm (z :: rest) := List.perm_cons_erase hzm
      have ez : (if !op then andD d a' c' else orD d a' c') = z := by
        cases op
        · simp [z, binD, a', c', andD_mask]
        · simp [z, binD, a', c', orD_mask]
      have h1 : RunD d Y k ((if !op then andD d a' c' else orD d a' c') :: rest) := by
        rw [ez]; exact Run.perm hp1 h
      set ka := decide (a' ∈ rest)
      set kb := decide (c' ∈ rest)
      set tail := (rest.erase a').erase c'
      have htail_nd : tail.Nodup := (hrest_nd.erase a').erase c'
      have hna_tail : a' ∉ tail := by
        intro hm; exact hrest_nd.not_mem_erase (List.mem_of_mem_erase hm)
      have hnc_tail : c' ∉ tail := (hrest_nd.erase a').not_mem_erase
      have hna_mid : a' ∉ kept kb c' tail := by
        rw [mem_kept]; rintro (⟨_, h⟩ | h)
        · exact hne_ac h
        · exact hna_tail h
      have hrest_perm : rest.Perm (kept ka a' (kept kb c' tail)) := by
        refine (List.perm_ext_iff_of_nodup hrest_nd (nodup_kept ka a' _ (nodup_kept kb c' _ htail_nd hnc_tail) hna_mid)).2 ?_
        intro x
        rw [mem_kept, mem_kept, (hrest_nd.erase a').mem_erase_iff, hrest_nd.mem_erase_iff]
        by_cases hxa : x = a' <;> by_cases hxc : x = c' <;> by_cases hxr : x ∈ rest <;>
          simp_all [ka, kb]
      have h2 := Run.perm (hrest_perm.cons _) h1
      have hne0 : (if !op then andD d a' c' else orD d a' c') ≠ 0 := ez.symm ▸ hzp.1
      have hned : (if !op then andD d a' c' else orD d a' c') ≠ d := ez.symm ▸ hzp.2
      have hnm : (if !op then andD d a' c' else orD d a' c') ∉ (a' :: c' :: tail) := by
        rw [ez, List.mem_cons, List.mem_cons]; rintro (e | e | hm)
        · exact hzb (e ▸ ha'_mem)
        · exact hzb (e ▸ hc'_mem)
        · exact hnd.not_mem_erase (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
      have h3 : RunD d Y (k + 1) (a' :: c' :: tail) := Run.two (!op) ka kb hne0 hned hnm h2
      have hnd3 : (a' :: c' :: tail).Nodup :=
        List.nodup_cons.2 ⟨by simp [hne_ac, hna_tail], List.nodup_cons.2 ⟨hnc_tail, htail_nd⟩⟩
      refine ⟨k + 1, a' :: c' :: tail, le_rfl, hnd3, ?_, ?_, h3⟩
      · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact ha'_prop
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact hc'_prop
          · exact hrest_prop w (List.mem_of_mem_erase (List.mem_of_mem_erase hw))
      · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact ha'_mem
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact hc'_mem
          · exact hrest_sub w (List.mem_of_mem_erase (List.mem_of_mem_erase hw))
  · exact ⟨k, ws, by omega, hnd, hprop, fun w hw => by
      rcases List.mem_cons.1 (hsub w hw) with rfl | hm
      · exact absurd hw hzm
      · exact hm, h⟩

theorem reach_to_run_aux {d : Nat} {roots : List Nat} {p bank} (hd : d &&& mask256 = d)
    (hr : NatReach d roots p bank) :
    ∀ {Y k ws}, ws.Nodup → (∀ w ∈ ws, w ≠ 0 ∧ w ≠ d) →
      (∀ w ∈ ws, w ∈ bank.map (· &&& d)) → RunD d Y k ws →
      ∃ k' ws', k' ≤ p + k ∧ ws'.Nodup ∧ (∀ w ∈ ws', w ≠ 0 ∧ w ≠ d) ∧
        (∀ w ∈ ws', w ∈ roots.map (· &&& d)) ∧ RunD d Y k' ws' := by
  induction p generalizing bank with
  | zero =>
    intro Y k ws hnd hprop hsub hrun
    subst hr
    exact ⟨k, ws, by omega, hnd, hprop, hsub, hrun⟩
  | succ p ih =>
    intro Y k ws hnd hprop hsub hrun
    rcases hr with ⟨b, a, rfl, hrb, ha⟩ | ⟨b, a, c, op, rfl, hrb, ha, hc⟩
    · have hsub' : ∀ w ∈ ws, w ∈ negD d a :: b.map (· &&& d) := by
        intro w hw; have := hsub w hw; simp only [List.map_cons, negD, Nat.and_assoc, Nat.and_self] at this; exact this
      obtain ⟨k1, ws1, hk1, hnd1, hprop1, hsub1, hrun1⟩ := pull_one hd hnd hprop hrun ha hsub'
      obtain ⟨k2, ws2, hk2, hnd2, hprop2, hsub2, hrun2⟩ := ih hrb hnd1 hprop1 hsub1 hrun1
      exact ⟨k2, ws2, by omega, hnd2, hprop2, hsub2, hrun2⟩
    · have hsub' : ∀ w ∈ ws, w ∈ binD d op a c :: b.map (· &&& d) := by
        intro w hw; have := hsub w hw
        have ez : binD d op a c &&& d = binD d op a c := by cases op <;> simp [binD, andD, orD, Nat.and_assoc, Nat.and_self]
        simpa [List.map_cons, ez] using this
      obtain ⟨k1, ws1, hk1, hnd1, hprop1, hsub1, hrun1⟩ := pull_two hnd hprop hrun op ha hc hsub'
      obtain ⟨k2, ws2, hk2, hnd2, hprop2, hsub2, hrun2⟩ := ih hrb hnd1 hprop1 hsub1 hrun1
      exact ⟨k2, ws2, by omega, hnd2, hprop2, hsub2, hrun2⟩

theorem reach_to_run {d : Nat} {roots : List Nat} {T : Nat} {p bank} (hd : d &&& mask256 = d)
    (hnc : ¬ IsConst d T) (hr : NatReach d roots p bank) (ha : Avail d bank T) :
    ∃ s ws, s ≤ p ∧ ws.Nodup ∧ (∀ w ∈ ws, w ∈ roots.map (· &&& d)) ∧ RunD d (T &&& d) s ws := by
  obtain ⟨v, hv, hve⟩ := ha.resolve_left hnc
  have hprop : ∀ w ∈ [T &&& d], w ≠ 0 ∧ w ≠ d := by
    intro w hw; rw [List.mem_singleton.1 hw]
    exact ⟨fun e => hnc (Or.inl e), fun e => hnc (Or.inr e)⟩
  have hsub : ∀ w ∈ [T &&& d], w ∈ bank.map (· &&& d) := by
    intro w hw; rw [List.mem_singleton.1 hw]; exact List.mem_map.2 ⟨v, hv, hve⟩
  obtain ⟨s, ws, hs, hnd, _, hsub', hrun⟩ := reach_to_run_aux hd hr (List.nodup_singleton _) hprop hsub Run.done
  exact ⟨s, ws, by omega, hnd, hsub', hrun⟩

theorem runD_bits {d y s ws} (hd : d &&& mask256 = d) (h : RunD d y s ws) (i j : Nat)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (hw : ∀ w ∈ ws, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  have hmi : mask256.testBit i = true := by
    have := congrArg (fun v => v.testBit i) hd; simp [Nat.testBit_and, hi] at this; exact this
  have hmj : mask256.testBit j = true := by
    have := congrArg (fun v => v.testBit j) hd; simp [Nat.testBit_and, hj] at this; exact this
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one save _ _ _ _ ih =>
    apply ih; have ha := hw _ List.mem_cons_self
    intro w hm; cases save <;> simp only [kept, Bool.false_eq_true, ite_false, ite_true, List.mem_cons] at hm
    · rcases hm with rfl | hr
      · simp [negD, ha, hi, hj, hmi, hmj]
      · exact hw _ (by simp [hr])
    · rcases hm with rfl | rfl | hr
      · simp [negD, ha, hi, hj, hmi, hmj]
      · exact ha
      · exact hw _ (by simp [hr])
  | two conj ka kb _ _ _ _ ih =>
    apply ih; have ha := hw _ List.mem_cons_self; have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hm; cases conj <;> cases ka <;> cases kb <;>
      simp only [kept, Bool.false_eq_true, ite_false, ite_true, List.mem_cons] at hm <;>
      rcases hm with rfl | hr <;>
      first | simp [andD, orD, ha, hb, hi, hj] | exact hw _ (by simp only [List.mem_cons]; tauto)

theorem runD_bits_le {d y s ws} (h : RunD d y s ws) (hl : ws.length = s + 1) (i j : Nat)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (hw : ∀ w ∈ ws, w.testBit i ≤ w.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (hp.length_eq.trans hl) (fun w h => hw w (hp.mem_iff.1 h))
  | one save _ _ _ h _ => have hh := run_len h; cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb _ _ _ h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    apply ih (by simp [kept]; omega)
    have ha := hw _ List.mem_cons_self; have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hm; simp only [kept, Bool.false_eq_true, ite_false, List.mem_cons] at hm
    rcases hm with rfl | hr
    · cases conj <;> simp only [andD, orD, ite_true, Bool.false_eq_true, ite_false, Nat.testBit_and, Nat.testBit_or, hi, hj, Bool.and_true] <;> grind
    · exact hw _ (by simp [hr])

theorem lower_base {d : Nat} {roots : List Nat} {T : Nat} (h : availB d roots T = false) :
    Lower d roots T 1 := by
  intro p bank hr ha
  cases p with
  | zero =>
    dsimp only [NatReach] at hr; rw [hr] at ha
    have ht := (availB_iff d roots T).2 ha
    rw [h] at ht; contradiction
  | succ p => omega

def moveBits (tag d w : Nat) : Nat :=
  ((w &&& tag) <<< d) ||| ((w >>> d) &&& tag) |||
    (w ^^^ ((w &&& tag) ||| (w &&& (tag <<< d))))

theorem moved (tag d i w : Nat) (h : (tag &&& (tag <<< d)) = 0) :
    (moveBits tag d w).testBit i =
      (if tag.testBit i then w.testBit (d + i)
       else if (tag <<< d).testBit i then w.testBit (i - d) else w.testBit i) := by
  have ht := congrArg (fun v : Nat => v.testBit i) h
  simp only [Nat.testBit_and, Nat.zero_testBit] at ht
  simp only [moveBits, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_and,
    Nat.testBit_shiftRight, Nat.testBit_xor] at *
  by_cases hi : d ≤ i <;> simp [hi] at * <;> grind

theorem move_hom (tag d : Nat) (h : (tag &&& (tag <<< d)) = 0) (a b : Nat) :
    moveBits tag d (a &&& b) = (moveBits tag d a &&& moveBits tag d b) ∧
    moveBits tag d (a ||| b) = (moveBits tag d a ||| moveBits tag d b) ∧
    moveBits tag d (a ^^^ b) = (moveBits tag d a ^^^ moveBits tag d b) := by
  refine ⟨?_, ?_, ?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, moved tag d i _ h] <;>
    split_ifs <;> simp

theorem move_zero (tag d : Nat) (h : (tag &&& (tag <<< d)) = 0) : moveBits tag d 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro i; rw [moved tag d i 0 h]; split_ifs <;> simp

def applyMoves (ms : List (Nat × Nat)) (w : Nat) : Nat :=
  ms.foldl (fun acc p => moveBits p.1 p.2 acc) w

def moveOK256 (p : Nat × Nat) : Bool :=
  (p.1 &&& (p.1 <<< p.2) == 0) && (moveBits p.1 p.2 mask256 == mask256)

theorem applyMoves_hom (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true) :
    (∀ a b, applyMoves ms (a &&& b) = applyMoves ms a &&& applyMoves ms b) ∧
    (∀ a b, applyMoves ms (a ||| b) = applyMoves ms a ||| applyMoves ms b) ∧
    (∀ a b, applyMoves ms (a ^^^ b) = applyMoves ms a ^^^ applyMoves ms b) ∧
    applyMoves ms 0 = 0 ∧ applyMoves ms mask256 = mask256 := by
  induction ms with
  | nil => exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩
  | cons p ps ih =>
    simp only [List.all_cons, Bool.and_eq_true, moveOK256, beq_iff_eq] at hok
    obtain ⟨⟨hz, hm⟩, hps⟩ := hok
    obtain ⟨hand, hor, hxor, h0, h256⟩ := ih hps
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro a b; simp only [applyMoves, List.foldl_cons, (move_hom p.1 p.2 hz a b).1]; exact hand _ _
    · intro a b; simp only [applyMoves, List.foldl_cons, (move_hom p.1 p.2 hz a b).2.1]; exact hor _ _
    · intro a b; simp only [applyMoves, List.foldl_cons, (move_hom p.1 p.2 hz a b).2.2]; exact hxor _ _
    · simp only [applyMoves, List.foldl_cons, move_zero p.1 p.2 hz]; exact h0
    · simp only [applyMoves, List.foldl_cons, hm]; exact h256

theorem move_invol (tag d w : Nat) (h : (tag &&& (tag <<< d)) = 0) :
    moveBits tag d (moveBits tag d w) = w := by
  apply Nat.eq_of_testBit_eq; intro i
  have ht := congrArg (fun v : Nat => v.testBit i) h
  simp only [Nat.testBit_and, Nat.zero_testBit] at ht
  rw [moved tag d i _ h]
  by_cases h1 : tag.testBit i = true
  · simp only [h1, ite_true, moved tag d (d + i) w h]
    have h2 : tag.testBit (d + i) = false := by
      have htd := congrArg (fun v : Nat => v.testBit (d + i)) h
      simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.zero_testBit] at htd
      have hge : d ≤ d + i := Nat.le_add_right d i
      have hsub : d + i - d = i := Nat.add_sub_cancel_left d i
      simp [hge, hsub, h1] at htd; exact htd
    have h3 : (tag <<< d).testBit (d + i) = true := by
      simp [Nat.testBit_shiftLeft, Nat.le_add_right, Nat.add_sub_cancel_left, h1]
    simp [h2, h3, Nat.add_sub_cancel_left]
  · simp only [h1, ite_false]
    by_cases h2 : (tag <<< d).testBit i = true
    · simp only [h2, ite_true, moved tag d (i - d) w h]
      rw [Nat.testBit_shiftLeft] at h2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
      simp [h2.2, Nat.add_sub_of_le h2.1]
    · simp [h1, h2, moved tag d i w h]

theorem applyMoves_inj (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true) :
    Function.Injective (applyMoves ms) := by
  induction ms with
  | nil => intro a b h; exact h
  | cons p ps ih =>
    simp only [List.all_cons, Bool.and_eq_true, moveOK256, beq_iff_eq] at hok
    intro a b h
    simp only [applyMoves, List.foldl_cons] at h
    have h1 := ih hok.2 h
    have := congrArg (moveBits p.1 p.2) h1
    rwa [move_invol p.1 p.2 a hok.1.1, move_invol p.1 p.2 b hok.1.1] at this

theorem applyMoves_runD {d Y s} (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    (hd : applyMoves ms d = d) (hY : applyMoves ms Y = Y) {ws} (h : RunD d Y s ws) :
    RunD d Y s (ws.map (applyMoves ms)) := by
  obtain ⟨hand, hor, hxor, h0, h256⟩ := applyMoves_hom ms hok
  have hinj := applyMoves_inj ms hok
  have hneg : ∀ a, applyMoves ms (negD d a) = negD d (applyMoves ms a) := fun a => by
    simp only [negD, hand, hxor, h256, hd]
  have hand' : ∀ a b, applyMoves ms (andD d a b) = andD d (applyMoves ms a) (applyMoves ms b) := fun a b => by
    simp only [andD, hand, hd]
  have hor' : ∀ a b, applyMoves ms (orD d a b) = orD d (applyMoves ms a) (applyMoves ms b) := fun a b => by
    simp only [orD, hand, hor, hd]
  rw [← hY]
  induction h using Run.fold with
  | done => exact Run.done
  | perm hp _ ih => exact Run.perm (hp.map _) ih
  | @one s a r save hne0 hned hnm _ ih =>
    have e1 : (negD d a :: kept save a r).map (applyMoves ms) =
        negD d (applyMoves ms a) :: kept save (applyMoves ms a) (r.map (applyMoves ms)) := by
      simp [kept_map, hneg]
    rw [e1] at ih
    refine Run.one save ?_ ?_ ?_ ih
    · intro e; rw [← hneg] at e; exact hne0 (hinj (e.trans h0.symm))
    · intro e; rw [← hneg] at e; exact hned (hinj (e.trans hd.symm))
    · rw [← hneg, ← List.map_cons, List.mem_map]; rintro ⟨x, hx, he⟩; exact hnm (hinj he ▸ hx)
  | @two s a b r conj ka kb hne0 hned hnm _ ih =>
    have eop : applyMoves ms (if conj then andD d a b else orD d a b) =
        (if conj then andD d (applyMoves ms a) (applyMoves ms b) else orD d (applyMoves ms a) (applyMoves ms b)) := by
      cases conj <;> simp [hand', hor']
    have e1 : ((if conj then andD d a b else orD d a b) :: kept ka a (kept kb b r)).map (applyMoves ms) =
        (if conj then andD d (applyMoves ms a) (applyMoves ms b) else orD d (applyMoves ms a) (applyMoves ms b)) ::
          kept ka (applyMoves ms a) (kept kb (applyMoves ms b) (r.map (applyMoves ms))) := by
      simp [kept_map, eop]
    rw [e1] at ih
    refine Run.two conj ka kb ?_ ?_ ?_ ih
    · intro e; rw [← eop] at e; exact hne0 (hinj (e.trans h0.symm))
    · intro e; rw [← eop] at e; exact hned (hinj (e.trans hd.symm))
    · rw [← eop, ← List.map_cons, ← List.map_cons, List.mem_map]; rintro ⟨x, hx, he⟩; exact hnm (hinj he ▸ hx)

theorem reach_map_moves (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    {d1 d2 : Nat} (hd : applyMoves ms d2 = d1)
    {roots1 roots2 : List Nat} (hroots : ∀ r ∈ roots2, Avail d1 roots1 (applyMoves ms r)) :
    ∀ {p bank}, NatReach d2 roots2 p bank →
      ∃ bank', NatReach d1 roots1 p bank' ∧ ∀ v ∈ bank, Avail d1 bank' (applyMoves ms v) := by
  obtain ⟨hand, hor, hxor, h0, h256⟩ := applyMoves_hom ms hok
  have hav : ∀ {b b' w}, (∀ v ∈ b, Avail d1 b' (applyMoves ms v)) →
      Avail d2 b w → Avail d1 b' (applyMoves ms w) := by
    intro b b' w hbb hw
    rcases hw with (hz | h1) | ⟨v, hv, he⟩
    · exact Or.inl (Or.inl (by rw [← hd, ← hand, hz, h0]))
    · exact Or.inl (Or.inr (by rw [← hd, ← hand, h1]))
    · have hve : applyMoves ms v &&& d1 = applyMoves ms w &&& d1 := by rw [← hd, ← hand, ← hand, he]
      exact avail_of_eq hve (hbb v hv)
  intro p
  induction p with
  | zero =>
    intro bank hr; subst hr
    exact ⟨roots1, rfl, hroots⟩
  | succ p ih =>
    intro bank hr
    rcases hr with ⟨b, a, rfl, hrb, ha⟩ | ⟨b, a, c, op, rfl, hrb, ha, hc⟩
    · obtain ⟨b', hrb', hbb⟩ := ih hrb
      have ha' := hav hbb ha
      refine ⟨negD d1 (applyMoves ms a) :: b', Or.inl ⟨b', applyMoves ms a, rfl, hrb', ha'⟩, ?_⟩
      intro v hv; rcases List.mem_cons.1 hv with rfl | hv
      · exact Or.inr ⟨negD d1 (applyMoves ms a), List.mem_cons_self, by simp only [negD, hand, hxor, h256, hd]⟩
      · exact avail_cons _ _ (hbb v hv)
    · obtain ⟨b', hrb', hbb⟩ := ih hrb
      have ha' := hav hbb ha; have hc' := hav hbb hc
      refine ⟨binD d1 op (applyMoves ms a) (applyMoves ms c) :: b',
        Or.inr ⟨b', applyMoves ms a, applyMoves ms c, op, rfl, hrb', ha', hc'⟩, ?_⟩
      intro v hv; rcases List.mem_cons.1 hv with rfl | hv
      · exact Or.inr ⟨binD d1 op (applyMoves ms a) (applyMoves ms c), List.mem_cons_self, by
          cases op <;> simp only [binD, andD, orD, hand, hor, hd, ite_true, ite_false, Bool.false_eq_true]⟩
      · exact avail_cons _ _ (hbb v hv)

theorem lower_iso {d1 d2 T1 T2 L : Nat} {roots1 roots2 : List Nat}
    (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    (hd : applyMoves ms d2 = d1) (hT : applyMoves ms T2 = T1)
    (hroots : roots2.all (fun r => availB d1 roots1 (applyMoves ms r)) = true)
    (h1 : Lower d1 roots1 T1 L) : Lower d2 roots2 T2 L := by
  obtain ⟨hand, _, _, h0, _⟩ := applyMoves_hom ms hok
  have hr : ∀ r ∈ roots2, Avail d1 roots1 (applyMoves ms r) := fun r hr =>
    (availB_iff _ _ _).1 (List.all_eq_true.1 hroots r hr)
  intro p bank hreach ha
  obtain ⟨bank', hrb', hbb⟩ := reach_map_moves ms hok hd hr hreach
  apply h1 p bank' hrb'
  rcases ha with (hz | ho) | ⟨v, hv, he⟩
  · exact Or.inl (Or.inl (by rw [← hT, ← hd, ← hand, hz, h0]))
  · exact Or.inl (Or.inr (by rw [← hT, ← hd, ← hand, ho]))
  · have hve : applyMoves ms v &&& d1 = T1 &&& d1 := by rw [← hT, ← hd, ← hand, ← hand, he]
    exact avail_of_eq hve (hbb v hv)

def pairOK (d T : Nat) (p : Nat × Nat) : Bool :=
  d.testBit p.1 && d.testBit p.2 && (T.testBit p.1 != T.testBit p.2)

def essOK (d T : Nat) (roots : List Nat) (a : Nat) (p : Nat × Nat) : Bool :=
  pairOK d T p && roots.all (fun v => (v == a) || (v.testBit p.1 == v.testBit p.2))

theorem countP_ge_sublist (p : Nat → Bool) {xs ys : List Nat}
    (hnd : xs.Nodup) (hsub : ∀ a ∈ xs, a ∈ ys) (hall : ∀ a ∈ xs, p a = true) :
    xs.length ≤ ys.countP p := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    have ⟨hna, hnd'⟩ := List.nodup_cons.1 hnd
    have ham : a ∈ ys := hsub a List.mem_cons_self
    have hperm : ys.Perm (a :: ys.erase a) := List.perm_cons_erase ham
    rw [hperm.countP_eq, List.countP_cons, hall a List.mem_cons_self]
    have ih' := ih hnd' (fun x hx => by
      have hne : x ≠ a := fun e => hna (e ▸ hx)
      exact (List.mem_erase_of_ne hne).2 (hsub x (List.mem_cons_of_mem _ hx)))
      (fun x hx => hall x (List.mem_cons_of_mem _ hx))
    simp only [ite_true, List.length_cons]
    omega

theorem lower_slice {d dSub T TSub L : Nat} {roots rootsSub : List Nat}
    (hd : d &&& mask256 = d) (hdSub : dSub &&& mask256 = dSub) (hsub : dSub &&& d = dSub)
    (hT : T &&& dSub = TSub &&& dSub)
    (hnc : isConstB d T = false) (hncSub : isConstB dSub TSub = false)
    (hcov : roots.all (availB dSub rootsSub) = true)
    (singles : List (Nat × Nat × Nat))
    (hs_nd : (singles.map Prod.fst).Nodup)
    (hs_ok : singles.all (fun e => isConstB dSub e.1 && essOK d (T &&& d) (roots.map (· &&& d)) e.1 e.2) = true)
    (hprior : Lower dSub rootsSub TSub L) :
    Lower d roots T (L + singles.length) := by
  have hnc' : ¬ IsConst d T := fun h => by rw [(isConstB_iff _ _).2 h] at hnc; contradiction
  have hncSub' : ¬ IsConst dSub (T &&& d) := by
    intro h
    have e : (T &&& d) &&& dSub = TSub &&& dSub := by
      rw [Nat.and_assoc, Nat.and_comm d dSub, hsub, hT]
    rcases h with h0 | h1
    · exact absurd ((isConstB_iff _ _).2 (Or.inl (e.symm.trans h0))) (by simp [hncSub])
    · exact absurd ((isConstB_iff _ _).2 (Or.inr (e.symm.trans h1))) (by simp [hncSub])
  intro p bank hr ha
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run hd hnc' hr ha
  have hws_av : ∀ w ∈ ws, Avail dSub rootsSub w := by
    intro w hw
    obtain ⟨r, hr_m, rfl⟩ := List.mem_map.1 (hws_sub w hw)
    have hav := (availB_iff _ _ _).1 (List.all_eq_true.1 hcov r hr_m)
    exact avail_of_eq (by rw [Nat.and_assoc, Nat.and_comm d dSub, hsub]) hav
  obtain ⟨q, next, hq, ht, hle⟩ := contraction hdSub hsub hncSub' hrun (p := 0) (bank := rootsSub) rfl hws_av
  have hTSub_av : Avail dSub next TSub := avail_of_eq (by
    rw [Nat.and_assoc, Nat.and_comm d dSub, hsub, hT]) ht
  have hL : L ≤ q := hprior q next hq hTSub_av
  have hsin_mem : ∀ a ∈ singles.map Prod.fst, a ∈ ws := by
    intro a ha
    obtain ⟨⟨a', r1, r2⟩, hm, rfl⟩ := List.mem_map.1 ha
    have hok := List.all_eq_true.1 hs_ok (a', r1, r2) hm
    simp only [Bool.and_eq_true, essOK, pairOK, bne_iff_ne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at hok
    obtain ⟨_, ⟨⟨hr1, hr2⟩, hdiff⟩, hiso⟩ := hok
    by_contra hnot
    apply hdiff
    apply runD_bits hd hrun r1 r2 hr1 hr2
    intro w hw
    rcases hiso w (hws_sub w hw) with rfl | heq
    · exact absurd hw hnot
    · exact heq
  have hsin_const : ∀ a ∈ singles.map Prod.fst, isConstB dSub a = true := by
    intro a ha
    obtain ⟨⟨a', r1, r2⟩, hm, rfl⟩ := List.mem_map.1 ha
    have hok := List.all_eq_true.1 hs_ok _ hm
    simp only [Bool.and_eq_true] at hok
    exact hok.1
  have hcnt := countP_ge_sublist (isConstB dSub) hs_nd hsin_mem hsin_const
  simp only [List.length_map] at hcnt
  omega

def runChoices (d : Nat) (pool : List Nat) : Nat → Nat → Option (List Nat)
  | 0, _ => some pool
  | p + 1, bits =>
    let code := bits &&& 1023
    let op := code &&& 3
    let ia := (code >>> 2) &&& 15
    let ib := (code >>> 6) &&& 15
    if ia < pool.length && (op == 2 || ib < pool.length) then
      let a := pool.getD ia 0
      let b := pool.getD ib 0
      let w := if op == 2 then negD d a else binD d (op == 1) a b
      runChoices d (pool ++ [w]) p (bits >>> 10)
    else none

theorem getD_mem {xs : List Nat} {i : Nat} (hi : i < xs.length) : xs.getD i 0 ∈ xs := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem hi

theorem runChoices_sound {d : Nat} {roots : List Nat} :
    ∀ (p bits q : Nat) (bank pool result : List Nat),
      NatReach d roots q bank →
      (∀ v ∈ pool, Avail d bank v) →
      runChoices d pool p bits = some result →
      ∃ bank', NatReach d roots (q + p) bank' ∧ ∀ v ∈ result, Avail d bank' v
  | 0, _, q, bank, pool, result, hr, hsup, hok => by
    simp only [runChoices, Option.some.injEq] at hok; subst hok; exact ⟨bank, hr, hsup⟩
  | p + 1, bits, q, bank, pool, result, hr, hsup, hok => by
    simp only [runChoices] at hok
    split at hok
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at hcond
      obtain ⟨hia, hopb⟩ := hcond
      set code := bits &&& 1023
      set op := code &&& 3
      set ia := (code >>> 2) &&& 15
      set ib := (code >>> 6) &&& 15
      set a := pool.getD ia 0
      set b := pool.getD ib 0
      set w := if op == 2 then negD d a else binD d (op == 1) a b
      have ha : Avail d bank a := hsup a (getD_mem hia)
      have hr1 : NatReach d roots (q + 1) (w :: bank) := by
        by_cases h2 : op = 2
        · simp only [w, h2, beq_self_eq_true, ite_true]
          exact Or.inl ⟨bank, a, rfl, hr, ha⟩
        · have hib : ib < pool.length := hopb.resolve_left h2
          have hb : Avail d bank b := hsup b (getD_mem hib)
          simp only [w, h2, beq_iff_eq, ite_false]
          exact Or.inr ⟨bank, a, b, (op == 1), rfl, hr, ha, hb⟩
      have hsup1 : ∀ v ∈ pool ++ [w], Avail d (w :: bank) v := by
        intro v hv; rcases List.mem_append.1 hv with hv | hv
        · exact avail_cons _ _ (hsup v hv)
        · rw [List.mem_singleton.1 hv]; exact Or.inr ⟨w, List.mem_cons_self, rfl⟩
      obtain ⟨bank', hrb', hsb'⟩ := runChoices_sound p (bits >>> 10) (q + 1) (w :: bank) (pool ++ [w]) result hr1 hsup1 hok
      exact ⟨bank', by simpa [Nat.add_assoc, Nat.add_comm 1] using hrb', hsb'⟩
    · contradiction

def checkCutEntry (dSub : Nat) (rootsSub : List Nat) (LSub s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  let p := (hint >>> 8) &&& 15
  decide (s + p < LSub + ws.countP (isConstB dSub)) &&
  match runChoices dSub rootsSub p (hint >>> 12) with
  | none => false
  | some pool => ws.all (availB dSub pool)

theorem checkCutEntry_sound {d dSub T TSub LSub s : Nat} {rootsSub ws : List Nat}
    (hdSub : dSub &&& mask256 = dSub) (hsub : dSub &&& d = dSub)
    (hT : T &&& dSub = TSub &&& dSub) (hncSub : isConstB dSub TSub = false)
    (hprior : Lower dSub rootsSub TSub LSub) (hint : Nat)
    (hchk : checkCutEntry dSub rootsSub LSub s ws hint = true) :
    ¬ RunD d (T &&& d) s ws := by
  intro hrun
  simp only [checkCutEntry, Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨hineq, hmatch⟩ := hchk
  cases hrc : runChoices dSub rootsSub ((hint >>> 8) &&& 15) (hint >>> 12) with
  | none => rw [hrc] at hmatch; contradiction
  | some pool =>
    rw [hrc] at hmatch
    have hsup0 : ∀ v ∈ rootsSub, Avail dSub rootsSub v := fun v hv => Or.inr ⟨v, hv, rfl⟩
    obtain ⟨bank, hrb, hsb⟩ := runChoices_sound _ _ 0 rootsSub rootsSub pool rfl hsup0 hrc
    simp only [Nat.zero_add] at hrb
    have hws_av : ∀ w ∈ ws, Avail dSub bank w := by
      intro w hw
      have hav := (availB_iff _ _ _).1 (List.all_eq_true.1 hmatch w hw)
      rcases hav with hc | ⟨v, hv, he⟩
      · exact Or.inl hc
      · exact avail_of_eq he (hsb v hv)
    have hnc' : ¬ IsConst dSub (T &&& d) := by
      intro h; have e : (T &&& d) &&& dSub = TSub &&& dSub := by rw [Nat.and_assoc, Nat.and_comm d dSub, hsub, hT]
      rcases h with h0 | h1
      · exact absurd ((isConstB_iff _ _).2 (Or.inl (e.symm.trans h0))) (by simp [hncSub])
      · exact absurd ((isConstB_iff _ _).2 (Or.inr (e.symm.trans h1))) (by simp [hncSub])
    obtain ⟨q, next, hq, ht, hle⟩ := contraction hdSub hsub hnc' hrun hrb hws_av
    have hL := hprior q next hq (avail_of_eq (by rw [Nat.and_assoc, Nat.and_comm d dSub, hsub, hT]) ht)
    omega

def coversP (pairs : List (Nat × Nat)) (s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s + 1 then
    pairs.all (fun p => ws.any (fun w => !w.testBit p.1 && w.testBit p.2))
  else
    pairs.all (fun p => ws.any (fun w => w.testBit p.1 != w.testBit p.2))

theorem coversP_ok {d T s : Nat} (hd : d &&& mask256 = d)
    (pairs : List (Nat × Nat))
    (hpairs : pairs.all (fun p => d.testBit p.1 && d.testBit p.2 && !(T &&& d).testBit p.1 && (T &&& d).testBit p.2) = true)
    {ws : List Nat} (h : RunD d (T &&& d) s ws) : coversP pairs s ws = true := by
  unfold coversP
  by_cases hl : ws.length = s + 1
  · simp only [hl, beq_self_eq_true, ite_true, List.all_eq_true, List.any_eq_true]
    intro ⟨u, v⟩ hm
    have hp := List.all_eq_true.1 hpairs (u, v) hm
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
    by_contra! hall
    have hle := runD_bits_le h hl v u hp.1.1.2 hp.1.1.1 (fun w hw => by
      have hbad := hall w hw
      cases hu : w.testBit u <;> cases hv : w.testBit v <;> simp_all)
    rw [hp.1.2, hp.2] at hle; contradiction
  · simp only [hl, beq_iff_eq, ite_false, List.all_eq_true, List.any_eq_true, bne_iff_ne]
    intro ⟨u, v⟩ hm
    have hp := List.all_eq_true.1 hpairs (u, v) hm
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
    by_contra! hall
    have heq := runD_bits hd h u v hp.1.1.1 hp.1.1.2 hall
    rw [hp.1.2, hp.2] at heq; contradiction

def unorientedCov (pairs : List (Nat × Nat)) (ws : List Nat) : Bool :=
  pairs.all (fun p => ws.any (fun w => w.testBit p.1 != w.testBit p.2))

theorem unorientedCov_ok {d T s : Nat} (hd : d &&& mask256 = d)
    (pairs : List (Nat × Nat))
    (hpairs : pairs.all (fun p => d.testBit p.1 && d.testBit p.2 && !(T &&& d).testBit p.1 && (T &&& d).testBit p.2) = true)
    {ws : List Nat} (h : RunD d (T &&& d) s ws) : unorientedCov pairs ws = true := by
  simp only [unorientedCov, List.all_eq_true, List.any_eq_true, bne_iff_ne]
  intro ⟨u, v⟩ hm
  have hp := List.all_eq_true.1 hpairs (u, v) hm
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
  by_contra! hall
  have heq := runD_bits hd h u v hp.1.1.1 hp.1.1.2 hall
  rw [hp.1.2, hp.2] at heq; contradiction

def maskP (m : Nat) : Nat := 2 ^ m - 1

def projBit (rs : List Nat) (w : Nat) : Nat :=
  rs.foldr (fun r acc => (acc <<< 1) ||| (if w.testBit r then 1 else 0)) 0

theorem projBit_testBit (rs : List Nat) (w : Nat) (i : Nat) :
    (projBit rs w).testBit i = if h : i < rs.length then w.testBit rs[i] else false := by
  induction rs generalizing i with
  | nil => simp [projBit]
  | cons r rs ih =>
    cases i with
    | zero =>
      simp only [projBit, List.foldr_cons, Nat.testBit_or, Nat.testBit_shiftLeft,
        Nat.not_le.2 Nat.zero_lt_one, decide_false, Bool.false_and, Bool.false_or,
        List.length_cons, Nat.zero_lt_succ, dite_true, List.getElem_cons_zero]
      cases w.testBit r <;> simp
    | succ i =>
      simp only [projBit, List.foldr_cons, Nat.testBit_or, Nat.testBit_shiftLeft,
        Nat.succ_le_succ (Nat.zero_le i), decide_true, Bool.true_and, Nat.add_sub_cancel,
        List.length_cons, Nat.succ_lt_succ_iff, List.getElem_cons_succ]
      have h1 : (if w.testBit r = true then 1 else 0).testBit (i + 1) = false := by
        cases w.testBit r <;> simp [Nat.testBit_succ]
      rw [h1, Bool.or_false]; exact ih i

theorem projBit_negD {dm : Nat} (hd : dm &&& mask256 = dm) {rs : List Nat}
    (hrs : ∀ r ∈ rs, dm.testBit r = true) (w : Nat) :
    projBit rs (negD dm w) = projBit rs w ^^^ maskP rs.length := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [projBit_testBit, Nat.testBit_xor, projBit_testBit, maskP, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < rs.length
  · have hdr := hrs rs[i] (List.getElem_mem hi)
    have hmr : mask256.testBit rs[i] = true := by
      have := congrArg (fun v => v.testBit rs[i]) hd; simp [Nat.testBit_and, hdr] at this; exact this
    simp [hi, negD, hdr, hmr]
  · simp [hi]

theorem projBit_andD {dm : Nat} {rs : List Nat} (hrs : ∀ r ∈ rs, dm.testBit r = true) (a b : Nat) :
    projBit rs (andD dm a b) = projBit rs a &&& projBit rs b := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [projBit_testBit, Nat.testBit_and, projBit_testBit, projBit_testBit]
  by_cases hi : i < rs.length
  · simp [hi, andD, hrs rs[i] (List.getElem_mem hi)]
  · simp [hi]

theorem projBit_orD {dm : Nat} {rs : List Nat} (hrs : ∀ r ∈ rs, dm.testBit r = true) (a b : Nat) :
    projBit rs (orD dm a b) = projBit rs a ||| projBit rs b := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [projBit_testBit, Nat.testBit_or, projBit_testBit, projBit_testBit]
  by_cases hi : i < rs.length
  · simp [hi, orD, hrs rs[i] (List.getElem_mem hi)]
  · simp [hi]

theorem foldl_or_testBit {α : Type} (g : α → Nat) (xs : List α) (acc i : Nat) :
    (xs.foldl (fun a x => a ||| g x) acc).testBit i = (acc.testBit i || xs.any (fun x => (g x).testBit i)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, Nat.testBit_or, List.any_cons, Bool.or_assoc]

def coversD (mp s : Nat) (dws : List (Nat × Nat × Nat)) : Bool :=
  if dws.length == s + 1 then
    dws.foldl (fun acc d => acc ||| ((d.2.1 ^^^ mp) &&& d.2.2)) 0 == mp
  else
    dws.foldl (fun acc d => acc ||| (d.2.1 ^^^ d.2.2)) 0 == mp

theorem coversD_eq (pairs : List (Nat × Nat)) (s : Nat) (ws : List Nat) :
    coversD (maskP pairs.length) s (ws.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))) =
      coversP pairs s ws := by
  set r1s := pairs.map Prod.fst
  set r2s := pairs.map Prod.snd
  set mp := maskP pairs.length
  have hr1 : r1s.length = pairs.length := List.length_map _
  have hr2 : r2s.length = pairs.length := List.length_map _
  unfold coversD coversP
  simp only [List.length_map]
  split
  · apply Bool.eq_iff_iff.2
    rw [beq_iff_eq, List.all_eq_true]
    constructor
    · intro heq pr hpr
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hpr
      have hb := congrArg (fun v => v.testBit i) heq
      rw [foldl_or_testBit, Nat.zero_testBit, Bool.false_or, List.any_map] at hb
      simp only [mp, maskP, Nat.testBit_two_pow_sub_one, hi, decide_true] at hb
      obtain ⟨w, hw, hwt⟩ := List.any_eq_true.1 hb
      simp only [Function.comp_def, Nat.testBit_and, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_true,
        Nat.testBit_two_pow_sub_one, decide_true, Bool.xor_true] at hwt
      exact List.any_eq_true.2 ⟨w, hw, by simpa [r1s, r2s] using hwt⟩
    · intro hall
      apply Nat.eq_of_testBit_eq; intro i
      rw [foldl_or_testBit, Nat.zero_testBit, Bool.false_or, List.any_map]
      simp only [mp, maskP, Nat.testBit_two_pow_sub_one]
      by_cases hi : i < pairs.length
      · simp only [hi, decide_true]
        obtain ⟨w, hw, hwt⟩ := List.any_eq_true.1 (hall pairs[i] (List.getElem_mem hi))
        exact List.any_eq_true.2 ⟨w, hw, by
          simp only [Function.comp_def, Nat.testBit_and, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_true,
            Nat.testBit_two_pow_sub_one, decide_true, Bool.xor_true, r1s, r2s, List.getElem_map]
          exact hwt⟩
      · simp only [hi, decide_false, List.any_eq_false]
        intro w _
        simp only [Function.comp_def, Nat.testBit_and, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_false,
          Nat.testBit_two_pow_sub_one, decide_false, Bool.xor_false, Bool.and_false, not_false_eq_true, Bool.false_eq_true]
  · apply Bool.eq_iff_iff.2
    rw [beq_iff_eq, List.all_eq_true]
    constructor
    · intro heq pr hpr
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hpr
      have hb := congrArg (fun v => v.testBit i) heq
      rw [foldl_or_testBit, Nat.zero_testBit, Bool.false_or, List.any_map] at hb
      simp only [mp, maskP, Nat.testBit_two_pow_sub_one, hi, decide_true] at hb
      obtain ⟨w, hw, hwt⟩ := List.any_eq_true.1 hb
      simp only [Function.comp_def, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_true] at hwt
      exact List.any_eq_true.2 ⟨w, hw, by simpa [r1s, r2s, bne] using hwt⟩
    · intro hall
      apply Nat.eq_of_testBit_eq; intro i
      rw [foldl_or_testBit, Nat.zero_testBit, Bool.false_or, List.any_map]
      simp only [mp, maskP, Nat.testBit_two_pow_sub_one]
      by_cases hi : i < pairs.length
      · simp only [hi, decide_true]
        obtain ⟨w, hw, hwt⟩ := List.any_eq_true.1 (hall pairs[i] (List.getElem_mem hi))
        exact List.any_eq_true.2 ⟨w, hw, by
          simp only [Function.comp_def, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_true, r1s, r2s, List.getElem_map]
          simpa [bne] using hwt⟩
      · simp only [hi, decide_false, List.any_eq_false]
        intro w _
        simp only [Function.comp_def, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_false,
          Bool.xor_false, Bool.false_eq_true, not_false_eq_true]

theorem erase_map_inj {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (hinj : Function.Injective f) (xs : List α) (a : α) :
    (xs.map f).erase (f a) = (xs.erase a).map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.erase_cons]
    by_cases h : x = a
    · subst h; simp
    · have hf : (f x == f a) = false := beq_false_of_ne (fun e => h (hinj e))
      have hx : (x == a) = false := beq_false_of_ne h
      simp [hf, hx, ih]

def value6 (a b c d e f : Bool) : Nat :=
  let x := b.toNat + c.toNat
  let y := (!e).toNat + (!f).toNat
  if a then (if d then y else max x (max y (x + y - 1))) else (if d then 0 else x)

theorem value6_and : ∀ a b c d e f g h i j l m : Bool,
    value6 (a && g) (b && h) (c && i) (d && j) (e && l) (f && m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem value6_or : ∀ a b c d e f g h i j l m : Bool,
    value6 (a || g) (b || h) (c || i) (d || j) (e || l) (f || m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem score_bound {d y s ws} (h : RunD d y s ws) (hl : ws.length = s + 1)
    (v : Nat → Nat) (hand : ∀ a b, v (andD d a b) ≤ v a + v b)
    (hor : ∀ a b, v (orD d a b) ≤ v a + v b) : v y ≤ (ws.map v).sum := by
  induction h using Run.fold with
  | done => simp
  | perm p _ ih => rw [← (p.map v).sum_eq]; exact ih (p.length_eq.trans hl)
  | one save _ _ _ h _ => have hh := run_len h; cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb _ _ _ h ih =>
    have hh := run_len h; cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih' := ih (by simp [kept]; omega)
    cases conj <;> simp [kept] at ih' ⊢ <;>
      first | grw [← Nat.add_assoc, ← hand]; exact ih' | grw [← Nat.add_assoc, ← hor]; exact ih'

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

theorem eval6_bound {dm y s ws} (h : RunD dm y s ws) (hl : ws.length = s + 1)
    (a b c d e f : Nat)
    (ha : dm.testBit a = true) (hb : dm.testBit b = true) (hc : dm.testBit c = true)
    (hd : dm.testBit d = true) (he : dm.testBit e = true) (hf : dm.testBit f = true) :
    eval6 a b c d e f y ≤ (ws.map (eval6 a b c d e f)).sum := by
  apply score_bound h hl
  · intro v w
    simpa only [eval6, andD, Nat.testBit_and, ha, hb, hc, hd, he, hf, Bool.and_true] using value6_and
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
  · intro v w
    simpa only [eval6, orD, Nat.testBit_and, Nat.testBit_or, ha, hb, hc, hd, he, hf, Bool.and_true] using value6_or
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)

def sumBelow (v : Nat → Nat) : List Nat → Nat → Bool
  | [], n => n != 0
  | w :: ws, n => decide (v w < n) && sumBelow v ws (n - v w)

theorem sumBelow_iff (v : Nat → Nat) (ws : List Nat) (n : Nat) :
    sumBelow v ws n = true ↔ (ws.map v).sum < n := by
  induction ws generalizing n with
  | nil => simp [sumBelow]
  | cons w ws ih => rw [sumBelow, Bool.and_eq_true, decide_eq_true_eq, ih, List.map_cons, List.sum_cons]; omega

def scoreCheck (dm y s : Nat) (ws : List Nat) (code : Nat) : Bool :=
  let a := code &&& 255
  let b := (code >>> 8) &&& 255
  let c := (code >>> 16) &&& 255
  let d := (code >>> 24) &&& 255
  let e := (code >>> 32) &&& 255
  let f := (code >>> 40) &&& 255
  dm.testBit a && dm.testBit b && dm.testBit c && dm.testBit d && dm.testBit e && dm.testBit f &&
    ws.length == s + 1 && sumBelow (eval6 a b c d e f) ws (eval6 a b c d e f y)

theorem scoreCheck_no {dm y s ws} (h : RunD dm y s ws) (code : Nat) :
    scoreCheck dm y s ws code = false := by
  unfold scoreCheck
  by_cases hok : dm.testBit (code &&& 255) = true ∧ dm.testBit ((code >>> 8) &&& 255) = true ∧
      dm.testBit ((code >>> 16) &&& 255) = true ∧ dm.testBit ((code >>> 24) &&& 255) = true ∧
      dm.testBit ((code >>> 32) &&& 255) = true ∧ dm.testBit ((code >>> 40) &&& 255) = true ∧
      ws.length = s + 1
  · obtain ⟨ha, hb, hc, hd, he, hf, hl⟩ := hok
    simp only [ha, hb, hc, hd, he, hf, hl, beq_self_eq_true, Bool.true_and]
    by_contra hbad
    have hsum := (sumBelow_iff _ _ _).1 (Bool.eq_true_of_not_eq_false hbad)
    exact (Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _ ha hb hc hd he hf)) hsum
  · by_contra hbad
    have ht := Bool.eq_true_of_not_eq_false hbad
    simp only [Bool.and_eq_true, beq_iff_eq] at ht
    exact hok ⟨ht.1.1.1.1.1.1.1, ht.1.1.1.1.1.1.2, ht.1.1.1.1.1.2, ht.1.1.1.1.2, ht.1.1.1.2, ht.1.1.2, ht.1.2⟩

def scr (dm y s : Nat) (pool : List Nat) (zs : List Nat) : Bool :=
  zs.length == s + 1 && pool.any (scoreCheck dm y s zs)

theorem scr_no {dm y s : Nat} (pool : List Nat) {zs : List Nat}
    (h : RunD dm y s zs) : scr dm y s pool zs = false := by
  unfold scr; rw [Bool.and_eq_false_iff]; right; rw [List.any_eq_false]
  intro x _; rw [scoreCheck_no h x]; simp

def nextD (dm : Nat) (slack : Nat) (ws : List Nat) (f : List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 &&
      (let w := negD dm a
       w != 0 && w != dm && !(ws.contains w) &&
         (f (w :: ra) || (slack ≥ 2 && f (w :: a :: ra))))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false, true].any fun conj =>
          let w := if conj then andD dm a b else orD dm a b
          w != 0 && w != dm && !(ws.contains w) &&
            (f (w :: r) || (slack ≥ 1 && (f (w :: a :: r) || f (w :: b :: r))) ||
              (slack ≥ 2 && f (w :: a :: b :: r))))

theorem nextD_one {dm y a rest} {save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h0 : negD dm a ≠ 0) (hd : negD dm a ≠ dm) (hnm : negD dm a ∉ (a :: rest))
    (h : RunD dm y s (negD dm a :: kept save a rest))
    (f : List Nat → Bool) (hf : ∀ ys, RunD dm y s ys → f ys = true) :
    nextD dm (s + 2 - ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h; have hl := p.length_eq; simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s + 2 - ws.length := by cases save <;> simp [kept] at hh <;> omega
  have hnc : ws.contains (negD dm a) = false := by
    cases h : ws.contains (negD dm a) with
    | false => rfl
    | true => exact absurd (p.mem_iff.2 (by simpa using h)) hnm
  have h0b : (negD dm a != 0) = true := bne_iff_ne.2 h0
  have hdb : (negD dm a != dm) = true := bne_iff_ne.2 hd
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; left; rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl, ?_⟩
  simp only [h0b, hdb, hnc, Bool.not_false, Bool.true_and]
  have ht := hf _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true => simp [kept] at ht hh; simp [ht, show 2 ≤ s + 2 - ws.length by omega]

theorem nextD_two_sorted {dm y a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h0 : (if conj then andD dm a b else orD dm a b) ≠ 0)
    (hd : (if conj then andD dm a b else orD dm a b) ≠ dm)
    (hnm : (if conj then andD dm a b else orD dm a b) ∉ (a :: b :: rest))
    (h : RunD dm y s ((if conj then andD dm a b else orD dm a b) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool) (hf : ∀ ys, RunD dm y s ys → f ys = true) :
    nextD dm (s + 2 - ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := run_len h; have hl := p.length_eq; simp only [List.length_cons] at hl hh
  have hnc : ws.contains (if conj then andD dm a b else orD dm a b) = false := by
    cases h : ws.contains (if conj then andD dm a b else orD dm a b) with
    | false => rfl
    | true => exact absurd (p.mem_iff.2 (by simpa using h)) hnm
  have h0b : ((if conj then andD dm a b else orD dm a b) != 0) = true := bne_iff_ne.2 h0
  have hdb : ((if conj then andD dm a b else orD dm a b) != dm) = true := bne_iff_ne.2 hd
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; right; apply List.any_eq_true.2 ⟨b, hb, ?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab, ?_⟩
  apply List.any_eq_true.2 ⟨conj, by cases conj <;> simp, ?_⟩
  simp only [h0b, hdb, hnc, Bool.not_false, Bool.true_and]
  have ht := hf _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true] <;>
    first | (simp [show 2 ≤ s + 2 - ws.length by omega]) | (simp [show 1 ≤ s + 2 - ws.length by omega])

theorem nextD_two {dm y a b rest} {conj ka kb : Bool} {s ws} (p : (a :: b :: rest).Perm ws)
    (h0 : (if conj then andD dm a b else orD dm a b) ≠ 0)
    (hd : (if conj then andD dm a b else orD dm a b) ≠ dm)
    (hnm : (if conj then andD dm a b else orD dm a b) ∉ (a :: b :: rest))
    (h : RunD dm y s ((if conj then andD dm a b else orD dm a b) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool) (hf : ∀ ys, RunD dm y s ys → f ys = true) :
    nextD dm (s + 2 - ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact nextD_two_sorted hab p h0 hd hnm h f hf
  · have he : (if conj then andD dm a b else orD dm a b) = (if conj then andD dm b a else orD dm b a) := by
      cases conj <;> simp [andD, orD, Nat.and_comm, Nat.or_comm]
    have hnm' : (if conj then andD dm b a else orD dm b a) ∉ (b :: a :: rest) := by
      rw [← he]; intro hm; exact hnm ((List.Perm.swap _ _ _).mem_iff.1 hm)
    apply nextD_two_sorted (conj := conj) (ka := kb) (kb := ka) hba ((List.Perm.swap _ _ _).trans p)
      (he ▸ h0) (he ▸ hd) hnm' _ f hf
    rw [he] at h; apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]; exact List.Perm.swap _ _ _

theorem nextD_complete {dm y t ws} (h : RunD dm y t ws) :
    ∀ s, t = s + 1 → ∀ zs, ws.Perm zs → ∀ f : List Nat → Bool,
      (∀ ys, RunD dm y s ys → f ys = true) →
      nextD dm (s + 2 - zs.length) zs f = true := by
  induction h using Run.fold with
  | done => simp
  | perm p _ ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one save h0 hd hnm h _ => intro s he zs p f hf; cases he; exact nextD_one p h0 hd hnm h f hf
  | two conj ka kb h0 hd hnm h _ => intro s he zs p f hf; cases he; exact nextD_two p h0 hd hnm h f hf

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, i => f i && span f n (i + 1)

theorem span_ok {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o + n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h; intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

theorem range_split {P : Nat → Prop} {lo mid hi : Nat}
    (h1 : ∀ i, lo ≤ i → i < mid → P i) (h2 : ∀ i, mid ≤ i → i < hi → P i) :
    ∀ i, lo ≤ i → i < hi → P i := fun i hlo hhi =>
  if h : i < mid then h1 i hlo h else h2 i (Nat.le_of_not_lt h) hhi

def fld (T w i : Nat) : Nat :=
  (T >>> (w * i)) &&& (if w == 32 then 4294967295 else if w == 52 then 4503599627370495 else if w == 256 then mask256 else 2 ^ w - 1)

def bsr (read : Nat → Nat) (h : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo + 1 < hi then
      (if read ((lo + hi) / 2) ≤ h then bsr read h f ((lo + hi) / 2) hi
       else bsr read h f lo ((lo + hi) / 2))
    else lo

def hw256 (seed w : Nat) : Nat :=
  let x := (((w % 170141183460469231731687303715884105727) ^^^ seed) * 0x9e3779b97f4a7c15f39cc0605cedc835) &&& 0xffffffffffffffffffffffffffffffff
  let y := ((x ^^^ (x >>> 61)) * 0xc2b2ae3d27d4eb4f165667b19e3779f9) &&& 0xffffffffffffffffffffffffffffffff
  y >>> 96

def hz (seed : Nat) : List Nat → Nat
  | [] => 0
  | w :: t => hw256 seed w + hz seed t

def hk (seed : Nat) (zs : List Nat) : Nat := hz seed zs &&& 4294967295

def found (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (s : Nat) (zs : List Nat) : Bool :=
  decide (idx s zs < N s) && zs.isPerm (S s (idx s zs))

def foundH (S : Nat → Nat → List Nat) (N : Nat → Nat) (htAt : Nat → Nat → Nat)
    (idxH : Nat → Nat → Nat) (s h : Nat) (zs : List Nat) : Bool :=
  let i := idxH s h
  decide (i < N s) && (htAt s i == h) && zs.isPerm (S s i)

def nextD_decor (dm mp : Nat) (slack : Nat) (dws : List (Nat × Nat × Nat))
    (f : List (Nat × Nat × Nat) → Bool) : Bool :=
  dws.any fun da =>
    let a := da.1
    let ra := dws.erase da
    (slack ≥ 1 &&
      (let w := negD dm a
       w != 0 && w != dm && !(dws.any (fun x => x.1 == w)) &&
         let dw := (w, da.2.1 ^^^ mp, da.2.2 ^^^ mp)
         (f (dw :: ra) || (slack ≥ 2 && f (dw :: da :: ra))))) ||
    ra.any fun db =>
      let b := db.1
      a ≤ b && (let r := ra.erase db
        [false, true].any fun conj =>
          let w := if conj then andD dm a b else orD dm a b
          w != 0 && w != dm && !(dws.any (fun x => x.1 == w)) &&
            let dw := if conj then (w, da.2.1 &&& db.2.1, da.2.2 &&& db.2.2)
                      else (w, da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)
            (f (dw :: r) || (slack ≥ 1 && (f (dw :: da :: r) || f (dw :: db :: r))) ||
              (slack ≥ 2 && f (dw :: da :: db :: r))))

theorem nextD_decor_gen (dm mp : Nat) (dec : Nat → Nat × Nat × Nat)
    (hfst : ∀ w, (dec w).1 = w)
    (hneg : ∀ a, (negD dm a, (dec a).2.1 ^^^ mp, (dec a).2.2 ^^^ mp) = dec (negD dm a))
    (hbin : ∀ (c : Bool) a b,
      (if c then (if c then andD dm a b else orD dm a b, (dec a).2.1 &&& (dec b).2.1, (dec a).2.2 &&& (dec b).2.2)
       else (if c then andD dm a b else orD dm a b, (dec a).2.1 ||| (dec b).2.1, (dec a).2.2 ||| (dec b).2.2)) =
      dec (if c then andD dm a b else orD dm a b))
    (slack : Nat) (ws : List Nat) (g : List (Nat × Nat × Nat) → Bool) :
    nextD_decor dm mp slack (ws.map dec) g = nextD dm slack ws (fun zs => g (zs.map dec)) := by
  have hinj : Function.Injective dec := fun x y h => by rw [← hfst x, ← hfst y, h]
  have herase : ∀ (l : List Nat) x, (l.map dec).erase (dec x) = (l.erase x).map dec :=
    fun l x => erase_map_inj dec hinj l x
  have hcont : ∀ (l : List Nat) w, (l.map dec).any (fun x => x.1 == w) = l.contains w := by
    intro l w; apply Bool.eq_iff_iff.2; simp [hfst]
  unfold nextD_decor nextD
  simp only [List.any_map, Function.comp_def, hfst, herase, hcont, hneg, hbin, List.map_cons]

theorem nextD_decor_eq {dm : Nat} (hd : dm &&& mask256 = dm)
    (pairs : List (Nat × Nat))
    (hr1 : ∀ r ∈ pairs.map Prod.fst, dm.testBit r = true)
    (hr2 : ∀ r ∈ pairs.map Prod.snd, dm.testBit r = true)
    (slack : Nat) (ws : List Nat) (g : List (Nat × Nat × Nat) → Bool) :
    let dec := fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w)
    nextD_decor dm (maskP pairs.length) slack (ws.map dec) g =
      nextD dm slack ws (fun zs => g (zs.map dec)) := by
  intro dec
  apply nextD_decor_gen
  · intro w; rfl
  · intro a
    simp only [dec, projBit_negD hd hr1, projBit_negD hd hr2, List.length_map]
  · intro c a b
    cases c <;> simp only [dec, ↓reduceIte, Bool.false_eq_true, projBit_andD hr1, projBit_andD hr2,
      projBit_orD hr1, projBit_orD hr2]

def colB (mp : Nat) (d : Bool) (p : Nat × Nat) : Nat :=
  if d then (p.1 ^^^ mp) &&& p.2 else p.1 ^^^ p.2

def addC (x : Nat) (c : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (c.1 ||| x, c.2.1 ||| (c.1 &&& x), c.2.2 ||| (c.2.1 &&& x))

def cov3 (mp : Nat) (d : Bool) (dws : List (Nat × Nat × Nat)) : Nat × Nat × Nat :=
  dws.foldl (fun c dw => addC (colB mp d dw.2) c) (0, 0, 0)

def takeOne (c : Nat × Nat × Nat) (x : Nat) : Nat := (c.1 ^^^ x) ||| c.2.1
def takeTwo (c : Nat × Nat × Nat) (x y : Nat) : Nat :=
  (c.1 ^^^ (x ||| y)) ||| (c.2.1 &&& (x ^^^ y)) ||| c.2.2

theorem cov3_bit (mp : Nat) (d : Bool) (dws : List (Nat × Nat × Nat)) (i : Nat) :
    let k := dws.countP (fun dw => (colB mp d dw.2).testBit i)
    (cov3 mp d dws).1.testBit i = decide (1 ≤ k) ∧
    (cov3 mp d dws).2.1.testBit i = decide (2 ≤ k) ∧
    (cov3 mp d dws).2.2.testBit i = decide (3 ≤ k) := by
  have hgen : ∀ (xs : List (Nat × Nat × Nat)) (c : Nat × Nat × Nat) (k0 : Nat),
      (c.1.testBit i = decide (1 ≤ k0) ∧ c.2.1.testBit i = decide (2 ≤ k0) ∧ c.2.2.testBit i = decide (3 ≤ k0)) →
      let k := k0 + xs.countP (fun dw => (colB mp d dw.2).testBit i)
      (xs.foldl (fun acc dw => addC (colB mp d dw.2) acc) c).1.testBit i = decide (1 ≤ k) ∧
      (xs.foldl (fun acc dw => addC (colB mp d dw.2) acc) c).2.1.testBit i = decide (2 ≤ k) ∧
      (xs.foldl (fun acc dw => addC (colB mp d dw.2) acc) c).2.2.testBit i = decide (3 ≤ k) := by
    intro xs
    induction xs with
    | nil => intro c k0 ⟨h1, h2, h3⟩; simp [h1, h2, h3]
    | cons dw xs ih =>
      intro c k0 ⟨h1, h2, h3⟩
      simp only [List.foldl_cons, List.countP_cons]
      have hc : (addC (colB mp d dw.2) c).1.testBit i =
            decide (1 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) ∧
          (addC (colB mp d dw.2) c).2.1.testBit i =
            decide (2 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) ∧
          (addC (colB mp d dw.2) c).2.2.testBit i =
            decide (3 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) := by
        simp only [addC, Nat.testBit_or, Nat.testBit_and, h1, h2, h3]
        cases hb : (colB mp d dw.2).testBit i <;>
          rcases k0 with _ | _ | _ | k0 <;>
          simp [hb, Nat.le_add_left]
      have ih' := ih (addC (colB mp d dw.2) c) (k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) hc
      cases hb : (colB mp d dw.2).testBit i <;> simp only [hb, ↓reduceIte, Bool.false_eq_true, Nat.add_zero] at ih' ⊢
      · exact ih'
      · simpa only [Nat.add_assoc, Nat.add_comm 1] using ih'
  simpa only [cov3, Nat.zero_testBit, Nat.zero_add] using hgen dws (0, 0, 0) 0 (by simp)

theorem cov3_perm (mp : Nat) (d : Bool) {xs ys : List (Nat × Nat × Nat)} (p : xs.Perm ys) :
    cov3 mp d xs = cov3 mp d ys := by
  have heq : ∀ i, (cov3 mp d xs).1.testBit i = (cov3 mp d ys).1.testBit i ∧
      (cov3 mp d xs).2.1.testBit i = (cov3 mp d ys).2.1.testBit i ∧
      (cov3 mp d xs).2.2.testBit i = (cov3 mp d ys).2.2.testBit i := by
    intro i
    obtain ⟨a1, a2, a3⟩ := cov3_bit mp d xs i
    obtain ⟨b1, b2, b3⟩ := cov3_bit mp d ys i
    rw [p.countP_eq] at a1 a2 a3
    exact ⟨a1.trans b1.symm, a2.trans b2.symm, a3.trans b3.symm⟩
  apply Prod.ext
  · exact Nat.eq_of_testBit_eq (fun i => (heq i).1)
  · apply Prod.ext
    · exact Nat.eq_of_testBit_eq (fun i => (heq i).2.1)
    · exact Nat.eq_of_testBit_eq (fun i => (heq i).2.2)

theorem takeOne_eq (mp : Nat) (d : Bool) (a : Nat × Nat × Nat) (rest : List (Nat × Nat × Nat)) :
    takeOne (cov3 mp d (a :: rest)) (colB mp d a.2) = (cov3 mp d rest).1 := by
  apply Nat.eq_of_testBit_eq; intro i
  obtain ⟨h1, h2, _⟩ := cov3_bit mp d (a :: rest) i
  obtain ⟨r1, _, _⟩ := cov3_bit mp d rest i
  simp only [takeOne, Nat.testBit_or, Nat.testBit_xor, h1, h2, r1, List.countP_cons]
  set k := rest.countP (fun dw => (colB mp d dw.2).testBit i)
  cases ha : (colB mp d a.2).testBit i <;> simp only [ha, Bool.false_eq_true, ↓reduceIte] <;>
    rcases k with _ | _ | _ | k
  · decide
  · decide
  · decide
  · simp only [show 1 ≤ k + 3 by omega, show 2 ≤ k + 3 by omega, decide_true, Bool.xor_false, Bool.or_true]
  · decide
  · decide
  · decide
  · simp only [show 1 ≤ k + 3 + 1 by omega, show 2 ≤ k + 3 + 1 by omega, show 1 ≤ k + 3 by omega,
      decide_true, Bool.xor_true, Bool.or_true, Bool.or_false]

theorem takeTwo_eq (mp : Nat) (d : Bool) (a b : Nat × Nat × Nat) (rest : List (Nat × Nat × Nat)) :
    takeTwo (cov3 mp d (a :: b :: rest)) (colB mp d a.2) (colB mp d b.2) = (cov3 mp d rest).1 := by
  apply Nat.eq_of_testBit_eq; intro i
  obtain ⟨h1, h2, h3⟩ := cov3_bit mp d (a :: b :: rest) i
  obtain ⟨r1, _, _⟩ := cov3_bit mp d rest i
  simp only [takeTwo, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, h1, h2, h3, r1, List.countP_cons]
  set k := rest.countP (fun dw => (colB mp d dw.2).testBit i)
  cases ha : (colB mp d a.2).testBit i <;> cases hb : (colB mp d b.2).testBit i <;>
    simp only [ha, hb, Bool.false_eq_true, ↓reduceIte] <;>
    rcases k with _ | _ | _ | k <;>
    (first | decide | simp only [
      show 1 ≤ k + 3 by omega, show 2 ≤ k + 3 by omega, show 3 ≤ k + 3 by omega,
      show 1 ≤ k + 3 + 1 by omega, show 2 ≤ k + 3 + 1 by omega, show 3 ≤ k + 3 + 1 by omega,
      show 1 ≤ k + 3 + 1 + 1 by omega, show 2 ≤ k + 3 + 1 + 1 by omega, show 3 ≤ k + 3 + 1 + 1 by omega,
      decide_true, Bool.xor_true, Bool.xor_false, Bool.or_true, Bool.or_false, Bool.and_true, Bool.and_false])

theorem cov3_coversD (mp s : Nat) (dw : Nat × Nat × Nat) (rest : List (Nat × Nat × Nat)) :
    let d := (dw :: rest).length == s + 1
    ((cov3 mp d rest).1 ||| colB mp d dw.2 == mp) = coversD mp s (dw :: rest) := by
  intro d
  have e : ∀ b : Bool, ((cov3 mp b rest).1 ||| colB mp b dw.2) =
      (dw :: rest).foldl (fun acc x => acc ||| colB mp b x.2) 0 := by
    intro b; apply Nat.eq_of_testBit_eq; intro i
    obtain ⟨h1, _, _⟩ := cov3_bit mp b rest i
    rw [foldl_or_testBit, Nat.zero_testBit, Bool.false_or, Nat.testBit_or, h1, List.any_cons]
    have hp : decide (1 ≤ rest.countP (fun dw => (colB mp b dw.2).testBit i)) =
        rest.any (fun x => (colB mp b x.2).testBit i) := by
      rw [Bool.eq_iff_iff, decide_eq_true_eq, Nat.succ_le_iff, List.countP_pos_iff, List.any_eq_true]
    rw [hp, Bool.or_comm]
  have hf : ∀ b : Bool, (cov3 mp b rest).1 ||| colB mp b dw.2 =
      (dw :: rest).foldl (fun acc x => acc ||| (if b then (x.2.1 ^^^ mp) &&& x.2.2 else x.2.1 ^^^ x.2.2)) 0 := by
    intro b; simpa only [colB] using e b
  unfold coversD
  dsimp only [d]
  cases (dw :: rest).length == s + 1
  · simpa only [Bool.false_eq_true, ↓reduceIte] using congrArg (· == mp) (hf false)
  · simpa only [↓reduceIte] using congrArg (· == mp) (hf true)

def nextD_cov (dm mp s slack : Nat) (dws : List (Nat × Nat × Nat))
    (f : List (Nat × Nat × Nat) → Bool) : Bool :=
  let len := dws.length
  let covF := cov3 mp false dws
  let covT := cov3 mp true dws
  let du0 := len == s + 1
  let du1 := len + 1 == s + 1
  let db0 := len - 1 == s + 1
  let db1 := len == s + 1
  let db2 := len + 1 == s + 1
  dws.any fun da =>
    let a := da.1
    (slack ≥ 1 &&
      (let pneg := (da.2.1 ^^^ mp, da.2.2 ^^^ mp)
       let uok0 := (takeOne (if du0 then covT else covF) (colB mp du0 da.2) ||| colB mp du0 pneg) == mp
       let uok1 := slack ≥ 2 && (((if du1 then covT.1 else covF.1) ||| colB mp du1 pneg) == mp)
       (uok0 || uok1) &&
       (let w := negD dm a
        w != 0 && w != dm && !(dws.any (fun x => x.1 == w)) &&
          let dw := (w, pneg)
          let ra := dws.erase da
          ((uok0 && f (dw :: ra)) || (uok1 && f (dw :: da :: ra)))))) ||
    (dws.erase da).any fun db =>
      let b := db.1
      a ≤ b &&
        [false, true].any fun conj =>
          let pz := if conj then (da.2.1 &&& db.2.1, da.2.2 &&& db.2.2)
                    else (da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)
          let ok0 := (takeTwo (if db0 then covT else covF) (colB mp db0 da.2) (colB mp db0 db.2) ||| colB mp db0 pz) == mp
          let ok1a := slack ≥ 1 && ((takeOne (if db1 then covT else covF) (colB mp db1 db.2) ||| colB mp db1 pz) == mp)
          let ok1b := slack ≥ 1 && ((takeOne (if db1 then covT else covF) (colB mp db1 da.2) ||| colB mp db1 pz) == mp)
          let ok2 := slack ≥ 2 && (((if db2 then covT.1 else covF.1) ||| colB mp db2 pz) == mp)
          (ok0 || ok1a || ok1b || ok2) &&
          (let w := if conj then andD dm a b else orD dm a b
           w != 0 && w != dm && !(dws.any (fun x => x.1 == w)) &&
             let dw := (w, pz)
             let r := (dws.erase da).erase db
             ((ok0 && f (dw :: r)) || (ok1a && f (dw :: da :: r)) || (ok1b && f (dw :: db :: r)) || (ok2 && f (dw :: da :: db :: r))))

theorem nextD_cov_eq (dm mp s slack : Nat) (dws : List (Nat × Nat × Nat))
    (g : List (Nat × Nat × Nat) → Bool) :
    nextD_cov dm mp s slack dws g =
      nextD_decor dm mp slack dws (fun dzs => coversD mp s dzs && g dzs) := by
  unfold nextD_cov nextD_decor
  dsimp only
  apply Bool.eq_iff_iff.2; simp only [List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨da, hda, hrest⟩
    refine ⟨da, hda, ?_⟩
    rcases hrest with ⟨hsl, _, ⟨⟨hw0, hwdm⟩, hnw⟩, hfx⟩ | ⟨db, hdb, hab, conj, hcj, _, ⟨⟨hw0, hwdm⟩, hnw⟩, hfx⟩
    · left
      refine ⟨hsl, ⟨⟨hw0, hwdm⟩, hnw⟩, ?_⟩
      set dw := (negD dm da.1, da.2.1 ^^^ mp, da.2.2 ^^^ mp)
      set ra := dws.erase da
      have hp : dws.Perm (da :: ra) := List.perm_cons_erase hda
      have hcov0 : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) da.2) ||| colB mp (dws.length == s + 1) (da.2.1 ^^^ mp, da.2.2 ^^^ mp)) == mp) =
          coversD mp s (dw :: ra) := by
        have hl : (dw :: ra).length = dws.length := by simp [hp.length_eq]
        have hc : ∀ d, cov3 mp d dws = cov3 mp d (da :: ra) := fun d => cov3_perm mp d hp
        have hc0 := cov3_coversD mp s dw ra
        rw [hl] at hc0
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hc0 ⊢
        · rw [hc false, takeOne_eq, hc0]
        · rw [hc true, takeOne_eq, hc0]
      have hcov1 :
          (((if dws.length + 1 == s + 1 then (cov3 mp true dws).1 else (cov3 mp false dws).1) |||
            colB mp (dws.length + 1 == s + 1) (da.2.1 ^^^ mp, da.2.2 ^^^ mp)) == mp) =
          coversD mp s (dw :: da :: ra) := by
        have hl : (dw :: da :: ra).length = dws.length + 1 := by simp [hp.length_eq]
        have hc : ∀ d, cov3 mp d dws = cov3 mp d (da :: ra) := fun d => cov3_perm mp d hp
        have hc1 := cov3_coversD mp s dw (da :: ra)
        rw [hl] at hc1
        cases hd : (dws.length + 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hc1 ⊢
        · rw [hc false, hc1]
        · rw [hc true, hc1]
      rcases hfx with ⟨hu0, hf0⟩ | ⟨⟨hsl2, hu1⟩, hf1⟩
      · left; exact ⟨hcov0 ▸ hu0, hf0⟩
      · right; exact ⟨hsl2, hcov1 ▸ hu1, hf1⟩
    · right
      refine ⟨db, hdb, hab, conj, hcj, ⟨⟨hw0, hwdm⟩, hnw⟩, ?_⟩
      set pz := if conj then (da.2.1 &&& db.2.1, da.2.2 &&& db.2.2) else (da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)
      set w := if conj then andD dm da.1 db.1 else orD dm da.1 db.1
      set dw := (w, pz)
      have hdw : (if conj = true then (w, da.2.1 &&& db.2.1, da.2.2 &&& db.2.2)
                  else (w, da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)) = dw := by cases conj <;> rfl
      simp only [hdw]
      set ra := dws.erase da
      set r := ra.erase db
      have hp : dws.Perm (da :: db :: r) := (List.perm_cons_erase hda).trans (List.Perm.cons _ (List.perm_cons_erase hdb))
      have hlen_r : (dw :: r).length = dws.length - 1 := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_a : (dw :: da :: r).length = dws.length := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_b : (dw :: db :: r).length = dws.length := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_ab : (dw :: da :: db :: r).length = dws.length + 1 := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hc2 : ∀ d, cov3 mp d dws = cov3 mp d (da :: db :: r) := fun d => cov3_perm mp d hp
      have hcov0 := cov3_coversD mp s dw r
      rw [hlen_r] at hcov0
      have hcov0' : ((takeTwo (if dws.length - 1 == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length - 1 == s + 1) da.2) (colB mp (dws.length - 1 == s + 1) db.2) |||
          colB mp (dws.length - 1 == s + 1) pz) == mp) = coversD mp s (dw :: r) := by
        cases hd : (dws.length - 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov0 ⊢
        · rw [hc2 false, takeTwo_eq, hcov0]
        · rw [hc2 true, takeTwo_eq, hcov0]
      have hc_a : ∀ d, cov3 mp d dws = cov3 mp d (db :: da :: r) :=
        fun d => cov3_perm mp d (hp.trans (List.Perm.swap _ _ _))
      have hcov1a := cov3_coversD mp s dw (da :: r)
      rw [hlen_a] at hcov1a
      have hcov1a' : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) db.2) ||| colB mp (dws.length == s + 1) pz) == mp) = coversD mp s (dw :: da :: r) := by
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov1a ⊢
        · rw [hc_a false, takeOne_eq, hcov1a]
        · rw [hc_a true, takeOne_eq, hcov1a]
      have hcov1b := cov3_coversD mp s dw (db :: r)
      rw [hlen_b] at hcov1b
      have hcov1b' : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) da.2) ||| colB mp (dws.length == s + 1) pz) == mp) = coversD mp s (dw :: db :: r) := by
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov1b ⊢
        · rw [hc2 false, takeOne_eq, hcov1b]
        · rw [hc2 true, takeOne_eq, hcov1b]
      have hcov2 := cov3_coversD mp s dw (da :: db :: r)
      rw [hlen_ab] at hcov2
      have hcov2' : (((if dws.length + 1 == s + 1 then (cov3 mp true dws).1 else (cov3 mp false dws).1) |||
          colB mp (dws.length + 1 == s + 1) pz) == mp) = coversD mp s (dw :: da :: db :: r) := by
        cases hd : (dws.length + 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov2 ⊢
        · rw [hc2 false, hcov2]
        · rw [hc2 true, hcov2]
      rcases hfx with ((⟨hu0, hf0⟩ | ⟨⟨hsl1, hu1a⟩, hf1a⟩) | ⟨⟨hsl1, hu1b⟩, hf1b⟩) | ⟨⟨hsl2, hu2⟩, hf2⟩
      · left; left; exact ⟨hcov0' ▸ hu0, hf0⟩
      · left; right; exact ⟨hsl1, Or.inl ⟨hcov1a' ▸ hu1a, hf1a⟩⟩
      · left; right; exact ⟨hsl1, Or.inr ⟨hcov1b' ▸ hu1b, hf1b⟩⟩
      · right; exact ⟨hsl2, hcov2' ▸ hu2, hf2⟩
  · rintro ⟨da, hda, hrest⟩
    refine ⟨da, hda, ?_⟩
    rcases hrest with ⟨hsl, ⟨⟨hw0, hwdm⟩, hnw⟩, hfx⟩ | ⟨db, hdb, hab, conj, hcj, ⟨⟨hw0, hwdm⟩, hnw⟩, hfx⟩
    · left
      set dw := (negD dm da.1, da.2.1 ^^^ mp, da.2.2 ^^^ mp)
      set ra := dws.erase da
      have hp : dws.Perm (da :: ra) := List.perm_cons_erase hda
      have hcov0 : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) da.2) ||| colB mp (dws.length == s + 1) (da.2.1 ^^^ mp, da.2.2 ^^^ mp)) == mp) =
          coversD mp s (dw :: ra) := by
        have hl : (dw :: ra).length = dws.length := by simp [hp.length_eq]
        have hc : ∀ d, cov3 mp d dws = cov3 mp d (da :: ra) := fun d => cov3_perm mp d hp
        have hc0 := cov3_coversD mp s dw ra; rw [hl] at hc0
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hc0 ⊢
        · rw [hc false, takeOne_eq, hc0]
        · rw [hc true, takeOne_eq, hc0]
      have hcov1 : (((if dws.length + 1 == s + 1 then (cov3 mp true dws).1 else (cov3 mp false dws).1) |||
            colB mp (dws.length + 1 == s + 1) (da.2.1 ^^^ mp, da.2.2 ^^^ mp)) == mp) =
          coversD mp s (dw :: da :: ra) := by
        have hl : (dw :: da :: ra).length = dws.length + 1 := by simp [hp.length_eq]
        have hc : ∀ d, cov3 mp d dws = cov3 mp d (da :: ra) := fun d => cov3_perm mp d hp
        have hc1 := cov3_coversD mp s dw (da :: ra); rw [hl] at hc1
        cases hd : (dws.length + 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hc1 ⊢
        · rw [hc false, hc1]
        · rw [hc true, hc1]
      rcases hfx with ⟨hc0, hg0⟩ | ⟨hsl2, hc1, hg1⟩
      · have hu0 : ((takeOne _ _ ||| _) == mp) = true := hcov0.symm ▸ hc0
        exact ⟨hsl, Or.inl hu0, ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inl ⟨hu0, hg0⟩⟩
      · have hu1 : ((_ ||| _) == mp) = true := hcov1.symm ▸ hc1
        exact ⟨hsl, Or.inr ⟨hsl2, hu1⟩, ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inr ⟨⟨hsl2, hu1⟩, hg1⟩⟩
    · right
      refine ⟨db, hdb, hab, conj, hcj, ?_⟩
      set pz := if conj then (da.2.1 &&& db.2.1, da.2.2 &&& db.2.2) else (da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)
      set w := if conj then andD dm da.1 db.1 else orD dm da.1 db.1
      set dw := (w, pz)
      have hdw : (if conj = true then (w, da.2.1 &&& db.2.1, da.2.2 &&& db.2.2)
                  else (w, da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)) = dw := by cases conj <;> rfl
      simp only [hdw] at hfx
      set ra := dws.erase da
      set r := ra.erase db
      have hp : dws.Perm (da :: db :: r) := (List.perm_cons_erase hda).trans (List.Perm.cons _ (List.perm_cons_erase hdb))
      have hlen_r : (dw :: r).length = dws.length - 1 := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_a : (dw :: da :: r).length = dws.length := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_b : (dw :: db :: r).length = dws.length := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_ab : (dw :: da :: db :: r).length = dws.length + 1 := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hc2 : ∀ d, cov3 mp d dws = cov3 mp d (da :: db :: r) := fun d => cov3_perm mp d hp
      have hcov0 := cov3_coversD mp s dw r; rw [hlen_r] at hcov0
      have hcov0' : ((takeTwo (if dws.length - 1 == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length - 1 == s + 1) da.2) (colB mp (dws.length - 1 == s + 1) db.2) |||
          colB mp (dws.length - 1 == s + 1) pz) == mp) = coversD mp s (dw :: r) := by
        cases hd : (dws.length - 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov0 ⊢
        · rw [hc2 false, takeTwo_eq, hcov0]
        · rw [hc2 true, takeTwo_eq, hcov0]
      have hc_a : ∀ d, cov3 mp d dws = cov3 mp d (db :: da :: r) :=
        fun d => cov3_perm mp d (hp.trans (List.Perm.swap _ _ _))
      have hcov1a := cov3_coversD mp s dw (da :: r); rw [hlen_a] at hcov1a
      have hcov1a' : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) db.2) ||| colB mp (dws.length == s + 1) pz) == mp) = coversD mp s (dw :: da :: r) := by
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov1a ⊢
        · rw [hc_a false, takeOne_eq, hcov1a]
        · rw [hc_a true, takeOne_eq, hcov1a]
      have hcov1b := cov3_coversD mp s dw (db :: r); rw [hlen_b] at hcov1b
      have hcov1b' : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) da.2) ||| colB mp (dws.length == s + 1) pz) == mp) = coversD mp s (dw :: db :: r) := by
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov1b ⊢
        · rw [hc2 false, takeOne_eq, hcov1b]
        · rw [hc2 true, takeOne_eq, hcov1b]
      have hcov2 := cov3_coversD mp s dw (da :: db :: r); rw [hlen_ab] at hcov2
      have hcov2' : (((if dws.length + 1 == s + 1 then (cov3 mp true dws).1 else (cov3 mp false dws).1) |||
          colB mp (dws.length + 1 == s + 1) pz) == mp) = coversD mp s (dw :: da :: db :: r) := by
        cases hd : (dws.length + 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov2 ⊢
        · rw [hc2 false, hcov2]
        · rw [hc2 true, hcov2]
      rcases hfx with (⟨hc0, hg0⟩ | ⟨hsl1, ⟨hc1a, hg1a⟩ | ⟨hc1b, hg1b⟩⟩) | ⟨hsl2, hc2', hg2⟩
      · have u0 : ((takeTwo _ _ _ ||| _) == mp) = true := hcov0'.symm ▸ hc0
        exact ⟨Or.inl (Or.inl (Or.inl u0)), ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inl (Or.inl (Or.inl ⟨u0, hg0⟩))⟩
      · have u1a : ((takeOne _ _ ||| _) == mp) = true := hcov1a'.symm ▸ hc1a
        exact ⟨Or.inl (Or.inl (Or.inr ⟨hsl1, u1a⟩)), ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inl (Or.inl (Or.inr ⟨⟨hsl1, u1a⟩, hg1a⟩))⟩
      · have u1b : ((takeOne _ _ ||| _) == mp) = true := hcov1b'.symm ▸ hc1b
        exact ⟨Or.inl (Or.inr ⟨hsl1, u1b⟩), ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inl (Or.inr ⟨⟨hsl1, u1b⟩, hg1b⟩)⟩
      · have u2 : ((_ ||| _) == mp) = true := hcov2'.symm ▸ hc2'
        exact ⟨Or.inr ⟨hsl2, u2⟩, ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inr ⟨⟨hsl2, u2⟩, hg2⟩⟩

def bar (dm Y : Nat) (pairs : List (Nat × Nat)) (r1s r2s : List Nat) (mp : Nat)
    (SD : Nat → Nat → List (Nat × Nat × Nat)) (S : Nat → Nat → List Nat)
    (N : Nat → Nat) (htAt idxH : Nat → Nat → Nat)
    (ori : List Nat → List Nat) (seed : Nat) (pool : List Nat) (cutHitH : Nat → Nat → List Nat → Bool) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [Y])
  | s + 1, i =>
    let dws := SD (s + 1) i
    !(nextD_cov dm mp s (s + 2 - dws.length) dws fun dzs =>
        let zs := dzs.map Prod.fst
        !(scr dm Y s pool zs) &&
        (let cz := ori zs
         let h := hk seed cz
         !(cutHitH s h cz) && !(foundH S N htAt idxH s h cz)))

theorem bar_all {dm T : Nat} {pairs r1s r2s mp SD S N htAt idxH ori seed pool cutHitH cap}
    (hd : dm &&& mask256 = dm)
    (hr1_eq : r1s = pairs.map Prod.fst) (hr2_eq : r2s = pairs.map Prod.snd) (hmp_eq : mp = maskP pairs.length)
    (hSD : ∀ s j, SD s j = (S s j).map (fun w => (w, projBit r1s w, projBit r2s w)))
    (hpairs : pairs.all (fun p => dm.testBit p.1 && dm.testBit p.2 && !(T &&& dm).testBit p.1 && (T &&& dm).testBit p.2) = true)
    (hr : ∀ {u ys}, RunD dm (T &&& dm) u ys → RunD dm (T &&& dm) u (ori ys))
    (hcut : ∀ {u ys}, cutHitH u (hk seed ys) ys = true → ¬ RunD dm (T &&& dm) u ys)
    (hc : ∀ s ≤ cap, ∀ i < N s, bar dm (T &&& dm) pairs r1s r2s mp SD S N htAt idxH ori seed pool cutHitH s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ RunD dm (T &&& dm) s (S s i) := by
  subst hr1_eq hr2_eq hmp_eq
  have hr1 : ∀ r ∈ pairs.map Prod.fst, dm.testBit r = true := by
    intro r hr'; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr'
    have h := List.all_eq_true.1 hpairs p hp; simp only [Bool.and_eq_true] at h; exact h.1.1.1
  have hr2 : ∀ r ∈ pairs.map Prod.snd, dm.testBit r = true := by
    intro r hr'; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr'
    have h := List.all_eq_true.1 hpairs p hp; simp only [Bool.and_eq_true] at h; exact h.1.1.2
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    have hb := hc s hs i hi
    cases s with
    | zero => simp [bar, zero_done hh rfl] at hb
    | succ s =>
      by_contra! hn
      let F (zs : List Nat) :=
        coversP pairs s zs && !(scr dm (T &&& dm) s pool zs) &&
        (let cz := ori zs
         let h := hk seed cz
         !(cutHitH s h cz) && !(foundH S N htAt idxH s h cz))
      have hF (zs) (hz : RunD dm (T &&& dm) s zs) : F zs = true := by
        have hcz := hr hz
        have hcutf : cutHitH s (hk seed (ori zs)) (ori zs) = false := by
          cases h : cutHitH s (hk seed (ori zs)) (ori zs) with
          | false => rfl
          | true => exact absurd hcz (hcut h)
        simp only [F, coversP_ok hd pairs hpairs hz, scr_no pool hz, hcutf, Bool.not_false, Bool.true_and, foundH]
        simp only [Bool.not_eq_true', Bool.and_eq_false_imp, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
        rintro ⟨hj, _⟩
        by_contra! hp
        have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
        exact ih s (by omega) (by omega) _ hj (Run.perm p hcz)
      have hN := nextD_complete hh s rfl _ (List.Perm.refl _) F hF
      dsimp only [bar] at hb
      rw [hSD, List.length_map, nextD_cov_eq, nextD_decor_eq hd pairs hr1 hr2] at hb
      have hFeq : (fun zs => coversD (maskP pairs.length) s (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))) &&
          (let zs' := (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))).map Prod.fst
           !(scr dm (T &&& dm) s pool zs') &&
           (let cz := ori zs'
            let h := hk seed cz
            !(cutHitH s h cz) && !(foundH S N htAt idxH s h cz)))) = F := by
        funext zs
        have hfst : (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))).map Prod.fst = zs := by
          simp [List.map_map, Function.comp_def]
        rw [coversD_eq, hfst]
        simp only [F, Bool.and_assoc]
      rw [hFeq, hN] at hb
      contradiction

def pickMin (seed : Nat) (orig : List Nat) : List (List (Nat × Nat)) → List Nat → Nat → List Nat
  | [], best, _ => best
  | ms :: rest, best, bestH =>
    let img := orig.map (applyMoves ms)
    let h := hk seed img
    if h < bestH then pickMin seed orig rest img h else pickMin seed orig rest best bestH

theorem pickMin_runD {dm Y u} (seed : Nat) (orig : List Nat) (h0 : RunD dm Y u orig) :
    ∀ (syms : List (List (Nat × Nat))) (best : List Nat) (bestH : Nat),
      syms.all (fun ms => ms.all moveOK256 && (applyMoves ms dm == dm) && (applyMoves ms Y == Y)) = true →
      RunD dm Y u best →
      RunD dm Y u (pickMin seed orig syms best bestH)
  | [], _, _, _, hb => hb
  | ms :: rest, best, bestH, hok, hb => by
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at hok
    unfold pickMin; dsimp only; split
    · exact pickMin_runD seed orig h0 rest _ _ hok.2 (applyMoves_runD ms hok.1.1.1 hok.1.1.2 hok.1.2 h0)
    · exact pickMin_runD seed orig h0 rest best bestH hok.2 hb

def gvN (w : List Nat) (g : Gate) : Nat :=
  match g.op with
  | .and => g.inputs.foldr (fun i acc => andD mask256 (w.getD i 0) acc) mask256
  | .or  => g.inputs.foldr (fun i acc => orD mask256 (w.getD i 0) acc) 0
  | .not => match g.inputs with | [] => mask256 | i :: _ => negD mask256 (w.getD i 0)
  | _ => 0

def execN (gs : List Gate) (w : List Nat) : List Nat :=
  gs.foldl (fun l g => l ++ [gvN l g]) w

theorem gvN_bit (w : List Nat) (g : Gate) (r : Nat) (hr : r < 256)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (gvN w g).testBit r = g.op.eval (g.inputs.map fun i => (w.map (·.testBit r)).getD i false) := by
  have hm : mask256.testBit r = true := by simp [mask256_bit, hr]
  have hgd : ∀ i, (w.map (·.testBit r)).getD i false = (w.getD i 0).testBit r := by
    intro i; simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases w[i]? with | none => simp | some v => rfl
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with h | h | h
  · simp only [gvN, GateOp.eval, h]
    induction g.inputs with
    | nil => simp [hm]
    | cons i l ih =>
      rw [List.foldr_cons, List.map_cons, List.all_cons, id_eq, andD, Nat.testBit_and, Nat.testBit_and, hm, Bool.and_true, hgd, ih]
  · simp only [gvN, GateOp.eval, h]
    induction g.inputs with
    | nil => simp
    | cons i l ih =>
      rw [List.foldr_cons, List.map_cons, List.any_cons, id_eq, orD, Nat.testBit_and, Nat.testBit_or, hm, Bool.and_true, hgd, ih]
  · simp only [gvN, GateOp.eval, h]
    cases g.inputs with
    | nil => simp [hm]
    | cons i l => simp only [List.map_cons, List.headD_cons, negD, Nat.testBit_and, Nat.testBit_xor, hm, Bool.and_true, Bool.xor_true, hgd]

theorem execN_bit (gs : List Gate) (w : List Nat) (r : Nat) (hr : r < 256)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (execN gs w).map (·.testBit r) =
      gs.foldl (fun l g => l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]) (w.map (·.testBit r)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [execN, List.foldl_cons] at ih ⊢
    rw [ih _ (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))]
    simp [gvN_bit w g r hr (hfan g List.mem_cons_self)]

theorem execN_reach (gs : List Gate) (roots : List Nat)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ (p : Nat) (w bank : List Nat), NatReach mask256 roots p bank →
      (∀ v ∈ w, Avail mask256 bank v) →
      ∃ p' bank', p' ≤ p + gs.length ∧ NatReach mask256 roots p' bank' ∧
        ∀ v ∈ execN gs w, Avail mask256 bank' v := by
  induction gs with
  | nil => intro p w bank hr hsup; exact ⟨p, bank, by omega, hr, hsup⟩
  | cons g gs ih =>
    intro p w bank hr hsup
    have hav_gd : ∀ i, Avail mask256 bank (w.getD i 0) := by
      intro i; by_cases hi : i < w.length
      · exact hsup _ (getD_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))

    have hstep : ∃ p1 bank1, p1 ≤ p + 1 ∧ NatReach mask256 roots p1 bank1 ∧
        (∀ v ∈ w ++ [gvN w g], Avail mask256 bank1 v) := by
      have hg := hfan g List.mem_cons_self
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      obtain ⟨hop, hlen⟩ := hg
      have hand_m : ∀ a, andD mask256 a mask256 &&& mask256 = a &&& mask256 := fun a => by
        simp [andD, Nat.and_assoc, Nat.and_self]
      have hor_0 : ∀ a, orD mask256 a 0 &&& mask256 = a &&& mask256 := fun a => by
        simp [orD, Nat.and_assoc, Nat.and_self]
      have lift_w : ∀ z, (∀ v ∈ w, Avail mask256 (z :: bank) v) := fun z v hv => avail_cons z v (hsup v hv)
      rcases hop with h | h | h
      · rcases hgi : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inr (by simp [gvN, h, hgi]))⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi, List.foldr_cons, List.foldr_nil]
              exact avail_of_eq (hand_m _).symm (hav_gd i)⟩
        · refine ⟨p + 1, binD mask256 false (w.getD i 0) (w.getD j 0) :: bank, le_rfl,
            Or.inr ⟨bank, _, _, false, rfl, hr, hav_gd i, hav_gd j⟩, fun v hv => ?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi, List.foldr_cons, List.foldr_nil]
            exact Or.inr ⟨_, List.mem_cons_self, by simp [binD, andD, Nat.and_assoc, Nat.and_self]⟩
        · rw [hgi] at hlen; simp at hlen
      · rcases hgi : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inl (by simp [gvN, h, hgi]))⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi, List.foldr_cons, List.foldr_nil]
              exact avail_of_eq (hor_0 _).symm (hav_gd i)⟩
        · refine ⟨p + 1, binD mask256 true (w.getD i 0) (w.getD j 0) :: bank, le_rfl,
            Or.inr ⟨bank, _, _, true, rfl, hr, hav_gd i, hav_gd j⟩, fun v hv => ?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi, List.foldr_cons, List.foldr_nil]
            exact Or.inr ⟨_, List.mem_cons_self, by apply Nat.eq_of_testBit_eq; intro r; simp [binD, orD]; cases mask256.testBit r <;> simp⟩
        · rw [hgi] at hlen; simp at hlen
      · rcases hgi : g.inputs with _ | ⟨i, l⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inr (by simp [gvN, h, hgi]))⟩
        · refine ⟨p + 1, negD mask256 (w.getD i 0) :: bank, le_rfl,
            Or.inl ⟨bank, _, rfl, hr, hav_gd i⟩, fun v hv => ?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi]; exact Or.inr ⟨_, List.mem_cons_self, rfl⟩
    obtain ⟨p1, bank1, hp1, hr1, hsup1⟩ := hstep
    obtain ⟨p2, bank2, hp2, hr2, hsup2⟩ := ih (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')) p1 _ bank1 hr1 hsup1
    exact ⟨p2, bank2, by simp; omega, hr2, hsup2⟩

def xs256 : List Nat :=
  [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
   0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
   0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
   0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
   0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
   0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,
   0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
   0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]

def pt8 (r : Nat) : Fin 8 → Bool := fun i => r.testBit i.val

theorem xs256_bits : ∀ r : Fin 256, xs256.map (·.testBit r.val) = List.ofFn (pt8 r.val) := by
  decide +kernel

theorem lower_to_circuit (f : (Fin 8 → Bool) → Bool) (T lb : Nat)
    (hT : ∀ r : Fin 256, T.testBit r.val = f (pt8 r.val))
    (hlow : Lower mask256 xs256 T lb) :
    ∀ t : ℕ, HasCircuitSize 8 f t → lb ≤ t := by
  rintro t ⟨C, hfan, hsz, hev⟩
  have hsup0 : ∀ v ∈ xs256, Avail mask256 xs256 v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates xs256 hfan 0 xs256 xs256 rfl hsup0
  have hout : (execN C.gates xs256).getD C.output 0 &&& mask256 = T &&& mask256 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and, mask256_bit]
    by_cases hlt : r < 256
    · simp only [hlt, decide_true, Bool.and_true]
      have h1 := execN_bit C.gates xs256 r hlt (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [xs256_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN C.gates xs256).map (·.testBit r)).getD C.output false =
          ((execN C.gates xs256).getD C.output 0).testBit r := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates xs256)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      have h3 : (C.wires (List.ofFn (pt8 r))).getD C.output false = f (pt8 r) := hev (pt8 r)
      exact h2.trans (h3.trans (hT ⟨r, hlt⟩).symm)
    · simp [hlt]
  have hav_out : Avail mask256 bank ((execN C.gates xs256).getD C.output 0) := by
    by_cases hi : C.output < (execN C.gates xs256).length
    · exact hsup _ (getD_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hL := hlow p bank hr (avail_of_eq hout hav_out)
  show lb ≤ t
  have : C.gates.length ≤ t := hsz
  omega

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xfefeaaaaeaeaa8a8fefeaaaaeaeaa8a8fefeaaaaeaeaa8a8fefeaaaaeaeaa8a8
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_31 : Nat := 0xffffffff
def goal_31 : Nat := 0xfeeafea8feeafea8feeafea8feeafea8feeafea8feeafea8feeafea8feeafea8
def roots_31 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xeeeeeeaaeeaaee88eeeeeeaaeeaaee88eeeeeeaaeeaaee88eeeeeeaaeeaaee88
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_62 : Nat := 0x5555555555555555
def goal_62 : Nat := 0xfcfcfc00fcc0fc00fcfcfc00fcc0fc00fcfcfc00fcc0fc00fcfcfc00fcc0fc00
def roots_62 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xfeaafeaafea8fea8feaafeaafea8fea8feaafeaafea8fea8feaafeaafea8fea8
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_47_16 : Nat := 0xffff0000ffff0000
def goal_47_16 : Nat := 0xfefefefefeeafeeafefefefefeeafeeafefefefefeeafeeafefefefefeeafeea
def roots_47_16 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_15_16 : Nat := 0xffff0000
def goal_15_16 : Nat := 0xfeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeea
def roots_15_16 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0]

def dom_27 : Nat := 0xf0f0f0f
def goal_27 : Nat := 0xeeaaee88eeaaee88eeaaee88eeaaee88eeaaee88eeaaee88eeaaee88eeaaee88
def roots_27 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_30 : Nat := 0x55555555
def goal_30 : Nat := 0xfcc0fc00fcc0fc00fcc0fc00fcc0fc00fcc0fc00fcc0fc00fcc0fc00fcc0fc00
def roots_30 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_54 : Nat := 0x55005500550055
def goal_54 : Nat := 0xfcfc0000c0c00000fcfc0000c0c00000fcfc0000c0c00000fcfc0000c0c00000
def roots_54 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_15 : Nat := 0xffff
def goal_15 : Nat := 0xfea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8
def roots_15 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0]

def dom_46_16 : Nat := 0x5555000055550000
def goal_46_16 : Nat := 0xfcfcfcfcfcc0fcc0fcfcfcfcfcc0fcc0fcfcfcfcfcc0fcc0fcfcfcfcfcc0fcc0
def roots_46_16 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfafafaaafaaafaa0fafafaaafaaafaa0fafafaaafaaafaa0fafafaaafaaafaa0
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_43 : Nat := 0xf0f00000f0f
def goal_43 : Nat := 0xeeaaeeaaee88ee88eeaaeeaaee88ee88eeaaeeaaee88ee88eeaaeeaaee88ee88
def roots_43 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_29 : Nat := 0x33333333
def goal_29 : Nat := 0xfaaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0
def roots_29 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_45 : Nat := 0x333300003333
def goal_45 : Nat := 0xfaaafaaafaa0faa0faaafaaafaa0faa0faaafaaafaa0faa0faaafaaafaa0faa0
def roots_45 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfefefeaafeeafea8fefefeaafeeafea8fefefeaafeeafea8fefefeaafeeafea8
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

namespace S_55
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 17), (1, 33), (2, 3), (4, 5), (6, 7), (6, 22), (16, 17), (18, 19), (18, 22), (18, 50), (20, 21), (20, 22), (20, 52), (32, 33), (34, 35), (34, 50), (36, 37), (36, 52), (38, 39), (38, 54), (48, 49), (48, 50), (48, 52)]
def r1sG : List Nat := [1, 1, 1, 1, 2, 4, 6, 6, 16, 18, 18, 18, 20, 20, 20, 32, 34, 34, 36, 36, 38, 38, 48, 48, 48]
def r2sG : List Nat := [3, 5, 17, 33, 3, 5, 7, 22, 17, 19, 22, 50, 21, 22, 52, 33, 35, 50, 37, 52, 39, 54, 49, 50, 52]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := [2203655210243, 6601668166405, 4402644914437, 6601701721347, 2203655213315, 19795841254659, 37388498899203, 17596583117585, 6601668169989, 19795606373137, 6601701724419, 21994830955269, 4403150196997, 22067559072534, 22068350693910, 17597088400145, 17597054714641, 21994629628689, 52922604913458, 52931194848564, 35188972323617, 37460723700018, 52862476420404, 21995134911249, 37387995579169, 17596583118097, 21995134911761, 52853886485298, 52781158368033, 52781426803473, 35189006009633]
def xsM : List Nat := roots_55.map (· &&& dom_55)
def goalM : Nat := goal_55 &&& dom_55
def NN : Nat → Nat
  | 4 => 20
  | 5 => 121
  | 6 => 144
  | 7 => 15
  | 8 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xb00b934a7d414d685b106f735af8acbf4a40666547baa0704389ff42371e630b2ee4c90124e221ab218651701d3bec3b19098f5a171cbb43114c3ca20f8093d806586eb80524062904b3ae5b02df085f
  | 5, 0 => 0x2d4141602a39e88529e4be9329b795cc297c0a1c2935d46028f822c2287ef6c428206f83276fc72a26f6989b26753f32257cdd7f2141f54620d129b420aa54de1fae080d1e7a89a81de775f81dba49061d802f7e1d671d1e1be6777d1bcc86811bb096731b58f0ed19df3a9a19cd95d7189d97b717bcb3cf177be419177b303d158b9ac2151fe504149143ec13f47b5b13d29a9013d1d3841396b3791367dbd5128b973c12294ab811c6c4521078ab760f9b718d0dcb40af0cc205f20c7ae7be0c1819bd0b7afc640b6d28d80ab1732e09e217a0080f99a4066ead810643ee5805c7a2b1057b960c030c43e401da968201b1a27b01753823012766cc006274db
  | 5, 1 => 0xdfc6b085cfa17660c8c371c7b4c0e045ac328943a783bd4fa4f836c39849bb019533824d9429f1ac8e96f06189ec9b4581fc7e887912806e73ea86206bdf8b716b85db746a0c2e8564987ff46493f5be63ac43d4628184da5de0c3745d71a0645ca2e0a65b64c5585b25d34e5b106f735a43850354cb4c3c54707b6354505533531f08515204c84d4ea33d014d85ccc74d010f644cda37244bebaa8747baa07044e04b334477485344466f8342444a3e41b3d7413ea88a323d25ca603d0687ed3a3975823a376cfa39ea7a6d3591ff5634cc1f433356184f321c56e231e376752f3e2585
  | 6, 0 => 0x3438ed2133b9b5f331beac4c317ce67630dc46d4302842c52f17f7c42ef3d89a2e15ce162935d4602931da2d28206f8327ca5be02712cb8d2697947020d129b41fd216d91fb2e99a1f650f8c1ef8e0511a4f9c3e19cd95d719a50ddf1814479f17c303b017bdcd44171aa0eb15dbc3151583be6015521a2e137f415e133a4b1a130eb0aa11c6c452102bb0080ef7856d0e8266d30d0426e90c7eec4b0c2759300c15df230b37344e0ae15b910ab1732e095964b709309ea2092cf2ae080123b5074cd068066ead81063a014f05d35636059d97a0053e379705029cf8049f7c3d035c2d68032b3c7e02f7ca3202d28481014e820700c8480200168dd500054b51
  | 6, 1 => 0xa1cffb639d0a65aa9980c81795b94f7691b066eb9034ec5b8f7d5c088d78cd158bd94c16830c511d82f7c9657994985a793f2aa674fb639773ea86207319596872723ce771c1aed56c995e5e6b85db7469ad9211680e111266a23aee65848d20628184da620ec69d617a1fc05e33f31e5a4385035661a37c553a144c5471a15853fa419050eeb30f508dcd715067bf944f053df24b9596e449dedc2e4861c84547baa0704642573745803a9b435ffda042d6ffea42735259420ba8c54181ffde3daee4bc3d3e009d3d0687ed3bec66c13b8908483ab3329d3a3aa35139ea7a6d39a6fe19391d553239017e81387bb923382b87b23816ecbc3793056234e7a833
  | 6, 2 => 0xeda0703eed7282aee4b5cb55c9d5353ac8c371c7c6eb2864c6df0060c27b70aeb57ba1efb4c0e045b400275fb144d080a90f92f2a4f836c3a37fed8aa299b735
  | 7, 0 => 0xc9d5353aa4f836c39034ec5b73ea86206b85db7469ad921150eeb30f47baa070464257373daee4bc2f17f7c427ca5be017bdcd4415dbc31515521a2e
  | 8, 0 => 0x47baa070
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x33000000330000000000000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000aa00aa000000000000000000000000000000000000000000000000000000000033003300000000000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000000ff
  | 0, 1 => 0x30003000f000f0000000000000000000000000000000000000000000000000003000300030003000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000aa000000aa00000000000000000000000000000000000000000000000000000077000000770000000000000000000000000000000000000000000000000000005500ff00ff0000000000000000000000000000000000000000000000000000005500000055
  | 0, 2 => 0x11001100110011000000000000000000000000000000000000000000000000000f00ff000f00ff000000000000000000000000000000000000000000000000000f000f00ff00ff000000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000f000a000f000a000000000000000000000000000000000000000000000000000f0000000f0000000000000000000000000000000000000000000000000000000a000a000a000a0000000000000000000000000000000000000000000000000005000500050005
  | 0, 3 => 0x33003300cc00cc0000000000000000000000000000000000000000000000000033003300330033000000000000000000000000000000000000000000000000003300330000000000000000000000000000000000000000000000000000000000330000003300000000000000000000000000000000000000000000000000000030003000300030000000000000000000000000000000000000000000000000002200220022002200000000000000000000000000000000000000000000000000110033001100330000000000000000000000000000000000000000000000000011001100330033
  | 0, 4 => 0x550000005500000000000000000000000000000000000000000000000000000050005000f000f00000000000000000000000000000000000000000000000000050005000500050000000000000000000000000000000000000000000000000004400cc004400cc000000000000000000000000000000000000000000000000003f003f00000000000000000000000000000000000000000000000000000000003300ff003300ff000000000000000000000000000000000000000000000000003300cc003300cc0000000000000000000000000000000000000000000000000033003300ff00ff
  | 0, 5 => 0x66006600660066000000000000000000000000000000000000000000000000005f005f005f005f000000000000000000000000000000000000000000000000005500ff005500ff000000000000000000000000000000000000000000000000005500aa005500aa0000000000000000000000000000000000000000000000000055005500ff00ff000000000000000000000000000000000000000000000000005500550055005500000000000000000000000000000000000000000000000000550055000000000000000000000000000000000000000000000000000000000055000000ff0000
  | 0, 6 => 0xaa000000aa000000000000000000000000000000000000000000000000000000a800a800a800a800000000000000000000000000000000000000000000000000a000ff00a000ff00000000000000000000000000000000000000000000000000a000a000a000a000000000000000000000000000000000000000000000000000a000a000000000000000000000000000000000000000000000000000000000009900990099009900000000000000000000000000000000000000000000000000880088008800880000000000000000000000000000000000000000000000000088000000880000
  | 0, 7 => 0xaf000f00af000f00000000000000000000000000000000000000000000000000aa00ff00aa00ff00000000000000000000000000000000000000000000000000aa00aa00aa00aa00000000000000000000000000000000000000000000000000aa00aa0088008800000000000000000000000000000000000000000000000000aa00aa0000000000000000000000000000000000000000000000000000000000aa00a000aa00a000000000000000000000000000000000000000000000000000aa008800aa008800000000000000000000000000000000000000000000000000aa005500aa0055
  | 0, 8 => 0xcc000000cc00cc00000000000000000000000000000000000000000000000000cc000000cc000000000000000000000000000000000000000000000000000000c300c300c300c300000000000000000000000000000000000000000000000000c000c000c000c000000000000000000000000000000000000000000000000000c000c00000000000000000000000000000000000000000000000000000000000c0000000c0000000000000000000000000000000000000000000000000000000bb00bb0033003300000000000000000000000000000000000000000000000000af00af00af00af
  | 0, 9 => 0xdd00dd00dd00dd00000000000000000000000000000000000000000000000000cc00ff00cc00ff00000000000000000000000000000000000000000000000000cc00fc00cc00fc00000000000000000000000000000000000000000000000000cc00cc00cc00cc00000000000000000000000000000000000000000000000000cc00cc00cc008800000000000000000000000000000000000000000000000000cc00cc0000000000000000000000000000000000000000000000000000000000cc008800cc008800000000000000000000000000000000000000000000000000cc000c00cc000c
  | 0, 10 => 0xee00ee00aa00aa00000000000000000000000000000000000000000000000000ee00ec00ee00ec00000000000000000000000000000000000000000000000000ee00cc00ee00cc00000000000000000000000000000000000000000000000000ee00aa00aa00aa00000000000000000000000000000000000000000000000000ee000000ee000000000000000000000000000000000000000000000000000000ec00ec00ec00ec00000000000000000000000000000000000000000000000000ec00cc00ec00cc00000000000000000000000000000000000000000000000000e000e000e000e0
  | 0, 11 => 0xf000f000c000c000000000000000000000000000000000000000000000000000f000f000a000a000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000f000a000f000a000000000000000000000000000000000000000000000000000f0000000f0000000000000000000000000000000000000000000000000000000f000000000000000000000000000000000000000000000000000000000000000ee00ee00ee00ee00000000000000000000000000000000000000000000000000ee00ee00cc00cc
  | 0, 12 => 0xfa00aa00aa00aa00000000000000000000000000000000000000000000000000f800f800f800f800000000000000000000000000000000000000000000000000f800f800f000f000000000000000000000000000000000000000000000000000f500f500f500f500000000000000000000000000000000000000000000000000f300f30033003300000000000000000000000000000000000000000000000000f000f500f000f500000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000f000f000f00000
  | 0, 13 => 0xfc00f000f000f000000000000000000000000000000000000000000000000000fc00cc00fc00cc00000000000000000000000000000000000000000000000000fa00fa00fa00fa00000000000000000000000000000000000000000000000000fa00fa00f800f800000000000000000000000000000000000000000000000000fa00fa00f000f000000000000000000000000000000000000000000000000000fa00fa00aa00aa00000000000000000000000000000000000000000000000000fa00f000fa00f000000000000000000000000000000000000000000000000000fa00aa00fa00aa
  | 0, 14 => 0xfe00fe00f000f000000000000000000000000000000000000000000000000000fe00fe0000000000000000000000000000000000000000000000000000000000fe000000fe000000000000000000000000000000000000000000000000000000fc00fc00fc00fc00000000000000000000000000000000000000000000000000fc00fc00f800f800000000000000000000000000000000000000000000000000fc00fc00f000f000000000000000000000000000000000000000000000000000fc00fc00cc00cc00000000000000000000000000000000000000000000000000fc00fc00000000
  | 0, 15 => 0xff005500ff005500000000000000000000000000000000000000000000000000ff003300ff003300000000000000000000000000000000000000000000000000ff000000ff00ff00000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000ff000000f0000000000000000000000000000000000000000000000000000000ff0000000000ff00000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000fe00fe00fe00fe
  | 1, 0 => 0xff00aa00ff00aa00000000000000000000000000000000000000000000000000ff00aa00ff008800000000000000000000000000000000000000000000000000ff00aa00ff000000000000000000000000000000000000000000000000000000ff00aa00aa00aa00000000000000000000000000000000000000000000000000ff00aa0000000000000000000000000000000000000000000000000000000000ff00a000ff00a000000000000000000000000000000000000000000000000000ff008800ff008800000000000000000000000000000000000000000000000000ff008000ff0080
  | 1, 1 => 0xff00ff00a000a000000000000000000000000000000000000000000000000000ff00ff0088008800000000000000000000000000000000000000000000000000ff00ff0033003300000000000000000000000000000000000000000000000000ff00ff000000ff00000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000ff00f000ff00f000000000000000000000000000000000000000000000000000ff00f000ff000000000000000000000000000000000000000000000000000000ff00cc00ff00cc
  | 1, 2 => 0xff00ff00ff00aa00000000000000000000000000000000000000000000000000ff00ff00ff000000000000000000000000000000000000000000000000000000ff00ff00fc00fc00000000000000000000000000000000000000000000000000ff00ff00f000f000000000000000000000000000000000000000000000000000ff00ff00cc00cc00000000000000000000000000000000000000000000000000ff00ff00c000c000000000000000000000000000000000000000000000000000ff00ff00aa00aa00000000000000000000000000000000000000000000000000ff00ff00aa0000
  | 1, 3 => 0xff00ff00ff00f0
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x8b613d2148b7c614c3d5007c613d1f400937c733d4008b7c61324008b7c612f40092743d0d4008b614c384007a614c3d400947c674c400847c61584008b7c453d400908761554008b8166594007c723d02400937c6f3d4
  | 4, 0, 1 => 0x8b614c2c400937c3d0f400947c713d400927c742a4
  | 5, 0, 0 => 0x82614c3d0658c614c3d0c58b612a1e0d58f7c614c3d59185614c3b58b7c61513d5947c5d4c3d5928b7c743d58b7c4c3d2658b614c3d2858b7c774c3d58b7c4c3f3d58b7c614d3d58f7c6d4c3d58b87614c3a58b8261523d5
  | 5, 0, 1 => 0x8b7c61544c58b664c3d0d5947c5e4c3d5947c5f4c3d58a5b4c3d0657c612a1e0658b7c613d2458b61553d0d58b7c684c3458b86614c3d5927c614c3d58b7c583d145947c5a4c3d58b75614c3d58b7c61483d58e7c614c2a5
  | 5, 0, 2 => 0x927c74443d57c5d4c3d0158b7c6f4c3d58b7c654c3d58b7c523d1458b7c6c4c3d58b7c614b3d57c61553d0658b825c4c3d583614c3d0d5937c4a3d1458b7c61493d58b7c613d1858f7c6d4c3458b8a684c3d58d7c613d1d5
  | 5, 0, 3 => 0x7c76614c3d5945d4c3d0d58b7c61593958b7c6b583d58b7c69553d57c4c3d140658b87694c3d58b7c4c401158b7c61593158b7c61413d58b7c71612a59185614c3d58b614d3d0d58b7c61563d58b4c3d140d58b614c3d355
  | 5, 0, 4 => 0x8b7f614c2758b7c624c3d58b61463d0758b7c61593c58b7c613d1958b82614c2a58b8861463d58b8861533d5837c613d1e5907c614c3d592614c3d0d58b7c63613d5837c5c4c3d58b7c66463d58b80614c3d58b614c3e0b5
  | 5, 0, 5 => 0x7c614c3d2358b614c3d0a500947c713d48b7c4c2a145837c614c2a5927c613d1e57c6159310657d614c3d055927c74613d5917c614c2b5937c61573d54c3d140d0658b7c61552a58b6159310d58b7c614c3d58b8a5b4c2a5
  | 5, 0, 6 => 0x94937c743d58b7c4c3d1358b8a4c3d1657c61473d0658b7c4c341057c614c3d0657c3d1e140658b614c3d0d58b874c371458b825b4c3d58783614c375947c5d4c2a58b81614c3d59683614c3d58b7c644c2558b876155375
  | 5, 0, 7 => 0x7c614c3d0958b614c370858b614c2a0d58b87614c375937c613d2058b87614c2d58b7c614c2a58b7c4c3d0f58b824c3d145
  | 6, 0, 0 => 0x8b7c614c3d1760000947c5d4c3d5008b7c594c3d146008b7c70614c3d6008b877c5c4c3d600938b7c613d1e6008b7c7b614c3d6008b614c3d340d600938b7c61463d600887c614c3d066008b7c614c3d36600938b7c74613d6008b7c61523d34600918b614c3d0d6008b837c614c3d6007c614c3d06036
  | 6, 0, 1 => 0x8b7c61534c3d60000927c614c3d5008b7c614c2a25600948b7c5d4c3d6008b7c614c2a276007c614c3d34066008b877c613d1e6008b7c614c3d336008b7c746d4c3d6008b7c614c3b2a6008b7c613d1e1b600008f7c614c3d5008b7c61504c3d6008b7c614c3d2e600917c614c3d066008b7c6e614c3d6
  | 6, 0, 2 => 0x938b7c614c2a6008b7c6a614c3d6008d8b7c614c3d6008b7c4c443d14600928b7c614c3d600008b7c61493d5008b887c613d1e6008b7c78614c3d6008b887c61463d6008b7c614c3d1e6008b7c614c433d6008b7c614c463d60096917c614c3d6008b7c74614c3d6008b7c4c403d146008f8b7c614c3d6
  | 6, 0, 3 => 0x8b887c614c2a600927c614c443d6008b7c4c3d14066008b897c614c3d6008b7c614c3d39600968b87614c3d6008b7c614c3d316008b7c614c3d126008b7c614c3d0e600007c4c3d14065008b7e7c613d1e600008b7c6159315008b7c614c3d2a6008b877c614c2a6008b7c64614c2a600008b4c3d140d5
  | 6, 0, 4 => 0x8b8a7c614c3d6008b817c614c3d600008b8861463d5008b8a615b4c3d6008b614c3d1e0d600917c614c3d3b600918b7c614c2a60000907c614c3d5008b614c463d0d6008b74614c3d0d600978b7c614c3d6008b7f7c614c3d6008b7c614c423d6008b7c61553d376008b87614c3d376008b7c4c4a3d146
  | 6, 0, 5 => 0x7c614c3d2a066008b7c61594c3d6008b7c68614c3d6008b7c614c3d156008b7c614c3d306008b614c3d2a0d6008b81614c3d316008b7c614c3d04600008b7c614c3d5008b7c614c3d0d6008b7c4c3d37146008b7c61604c3d6008b7c614c3e3d600908b7c614c3d6007c614c463d066007c74614c3d066
  | 6, 0, 6 => 0x7c614c3d0d066008b7c613d311e6008b7c614c3d22600008b614c3d0d5008b7c614c443d6008b7c614c3d0c6008b614c3e3d0d6008b7c5b4c3d34600008b81614c3d5008d8b7c613d1e6008b8a614c3d0d6008b7c614c403d600008b7c4c2a145968b7c74614c3d7007c79614c3d066008b7c614f4c3d6
  | 6, 0, 7 => 0x8b7c614c3d006008b614e4c3d0d6008b7c614c3d296008b7f7c614c2a6008b7c614c3d0b6008b7c614c3d376008b877c614c376008b614c443d0d6008b614c3d0d0c600988b7c614c3d6008b7c614c3d2d600958b7c614c3d6008b7c614e4c3d6008b7c614c2a1e600007c614c3d065008b7c614c462a6
  | 6, 0, 8 => 0x8b87614c3d0d6008b7c614c372a6008b7c614c3d086008b877c614c3d600008b614c2a0d5008b7c614c442a6008b7c614c3d1a6008b7d7c614c3d6008b614c3d0d0b600008b87614c375008b614c3d370d6008b7c614c3d276008b7c6d614c34600008b7c614c2a5008b7c614c2a0d6008b7c613d1e1c6
  | 7, 0, 0 => 0x8b877c614c3d6008b7c614c2a58b7c614c3d376007c614c3d065008b614c3d0d58b7c614c443d68b7c61594c3d6008b7c614c3d58b7c614c3d0d68b8a7c614c3d68b7c614c3d3168b7c614c3d2a68b7c614c3d1e68b7c614c463d68b7c74614c3d6
  | 8, 0, 0 => 0x8b7c614c3d5
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 44
  | 5 => 44
  | 6 => 60
  | 7 => 52
  | 8 => 44
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 8 0) :: stateWires n (ids >>> 8)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xc802f0000000000000000000000000000000000000000000000000000000000007fff0000000000000000000000000000000000000000000000000000000000007f0000000000000000000000000000000000000000000000000000000000000070e0000000000000000000000000000000000000000000000000000000000000000f000000000000000000000000000000000000000000000000000000000000712f0000000000000000000000000000000000000000000000000000000000000f1f00000000000000000000000000000000000000000000000000000000000000ff
  | 0, 1 => 0x1c08f1f0000000000000000000000000000000000000000000000000000000001c0810f00000000000000000000000000000000000000000000000000000000003f80ff00000000000000000000000000000000000000000000000000000000003f8000000000000000000000000000000000000000000000000000000000000000000f00000000000000000000000000000000000000000000000000000000003f80ff00000000000000000000000000000000000000000000000000000000003fffff00000000000000000000000000000000000000000000000000000000003f80f0
  | 0, 2 => 0x1ccf1200000000000000000000000000000000000000000000000000000000001ff8fff0000000000000000000000000000000000000000000000000000000001c3ffff0000000000000000000000000000000000000000000000000000000001c38f1f0000000000000000000000000000000000000000000000000000000001c00f0f0000000000000000000000000000000000000000000000000000000001c00f00000000000000000000000000000000000000000000000000000000000000000f0000000000000000000000000000000000000000000000000000000001c38f10
  | 0, 3 => 0x1cc8ed00000000000000000000000000000000000000000000000000000000001ccf12f0000000000000000000000000000000000000000000000000000000001cc80000000000000000000000000000000000000000000000000000000000001c0710000000000000000000000000000000000000000000000000000000000000c7020000000000000000000000000000000000000000000000000000000000000000f0000000000000000000000000000000000000000000000000000000001ccf12f0000000000000000000000000000000000000000000000000000000001ccf12f
  | 0, 4 => 0x1c07f0000000000000000000000000000000000000000000000000000000000003c70e000000000000000000000000000000000000000000000000000000000003c70e00000000000000000000000000000000000000000000000000000000000330ed00000000000000000000000000000000000000000000000000000000001cf80000000000000000000000000000000000000000000000000000000000001fff1ff0000000000000000000000000000000000000000000000000000000001f371d00000000000000000000000000000000000000000000000000000000001ccffff
  | 0, 5 => 0x330edf0000000000000000000000000000000000000000000000000000000001ffffff0000000000000000000000000000000000000000000000000000000001ffffff0000000000000000000000000000000000000000000000000000000001c07f0f0000000000000000000000000000000000000000000000000000000001ffffff0000000000000000000000000000000000000000000000000000000001fffff00000000000000000000000000000000000000000000000000000000001ff80000000000000000000000000000000000000000000000000000000000001c07f00
  | 0, 6 => 0x3f80ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001ccf12000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 0, 7 => 0x1c38f1f00000000000000000000000000000000000000000000000000000000003f80ff000000000000000000000000000000000000000000000000000000000000000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003f80f0
  | 0, 8 => 0xed00000000000000000000000000000000000000000000000000000000000000e000000000000000000000000000000000000000000000000000000000001f081cf00000000000000000000000000000000000000000000000000000000003000c0000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001ccf12f0000000000000000000000000000000000000000000000000000000001c38f1f
  | 0, 9 => 0x1fffff000000000000000000000000000000000000000000000000000000000003f8eff00000000000000000000000000000000000000000000000000000000003f0ef00000000000000000000000000000000000000000000000000000000000330ed00000000000000000000000000000000000000000000000000000000000330e0000000000000000000000000000000000000000000000000000000000003300000000000000000000000000000000000000000000000000000000000000000e000000000000000000000000000000000000000000000000000000000000030e10
  | 0, 10 => 0x33000f0000000000000000000000000000000000000000000000000000000000330ed00000000000000000000000000000000000000000000000000000000000330ed0000000000000000000000000000000000000000000000000000000000000000f0000000000000000000000000000000000000000000000000000000000000e000000000000000000000000000000000000000000000000000000000000330ed00000000000000000000000000000000000000000000000000000000000330ed000000000000000000000000000000000000000000000000000000000003000c0
  | 0, 11 => 0x3c00c000000000000000000000000000000000000000000000000000000000003c000000000000000000000000000000000000000000000000000000000000003c00000000000000000000000000000000000000000000000000000000000000007000000000000000000000000000000000000000000000000000000000000000700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000330edf0000000000000000000000000000000000000000000000000000000000330ed0
  | 0, 12 => 0xf00000000000000000000000000000000000000000000000000000000003c70e000000000000000000000000000000000000000000000000000000000003c70e00000000000000000000000000000000000000000000000000000000001fffff00000000000000000000000000000000000000000000000000000000001fcf12f00000000000000000000000000000000000000000000000000000000003ff0f000000000000000000000000000000000000000000000000000000000003c70e000000000000000000000000000000000000000000000000000000000003c7000
  | 0, 13 => 0x3c70e00000000000000000000000000000000000000000000000000000000000337ed000000000000000000000000000000000000000000000000000000000003c70ef00000000000000000000000000000000000000000000000000000000003c70e000000000000000000000000000000000000000000000000000000000003c70e000000000000000000000000000000000000000000000000000000000003c000f00000000000000000000000000000000000000000000000000000000003c70e0000000000000000000000000000000000000000000000000000000000000700f
  | 0, 14 => 0x3f70e000000000000000000000000000000000000000000000000000000000003f00000000000000000000000000000000000000000000000000000000000000007e0000000000000000000000000000000000000000000000000000000000003f7ef000000000000000000000000000000000000000000000000000000000003f70e000000000000000000000000000000000000000000000000000000000003f70e000000000000000000000000000000000000000000000000000000000003f0ed000000000000000000000000000000000000000000000000000000000003f0000
  | 0, 15 => 0x1fffff00000000000000000000000000000000000000000000000000000000001ccff2f0000000000000000000000000000000000000000000000000000000001c07fff0000000000000000000000000000000000000000000000000000000001c07f000000000000000000000000000000000000000000000000000000000001c070000000000000000000000000000000000000000000000000000000000001c000ff0000000000000000000000000000000000000000000000000000000001c0000000000000000000000000000000000000000000000000000000000000003f7eff
  | 1, 0 => 0x1c07f0f0000000000000000000000000000000000000000000000000000000001c07f000000000000000000000000000000000000000000000000000000000001c07f000000000000000000000000000000000000000000000000000000000001c0000f0000000000000000000000000000000000000000000000000000000001c000000000000000000000000000000000000000000000000000000000000001c07f000000000000000000000000000000000000000000000000000000000001c07f000000000000000000000000000000000000000000000000000000000001c07f00
  | 1, 1 => 0x1ff80000000000000000000000000000000000000000000000000000000000001ff80000000000000000000000000000000000000000000000000000000000001fff12f0000000000000000000000000000000000000000000000000000000001ff80ff0000000000000000000000000000000000000000000000000000000001ff80000000000000000000000000000000000000000000000000000000000001fc7fe00000000000000000000000000000000000000000000000000000000001fc7f000000000000000000000000000000000000000000000000000000000001f37fd0
  | 1, 2 => 0x1ffff0f0000000000000000000000000000000000000000000000000000000001ffff000000000000000000000000000000000000000000000000000000000001fffef00000000000000000000000000000000000000000000000000000000001fff0e00000000000000000000000000000000000000000000000000000000001ff8ed00000000000000000000000000000000000000000000000000000000001ff80c00000000000000000000000000000000000000000000000000000000001ff800f0000000000000000000000000000000000000000000000000000000001ff8000
  | 1, 3 => 0x1ffffe0
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x4802a00000000000000000000000000000000000000000000000000000000000037f7000000000000000000000000000000000000000000000000000000000000378400000000000000000000000000000000000000000000000000000000000034e20000000000000000000000000000000000000000000000000000000000001377000000000000000000000000000000000000000000000000000000000000112600000000000000000000000000000000000000000000000000000000000003150000000000000000000000000000000000000000000000000000000000000073
  | 0, 1 => 0x40831d000000000000000000000000000000000000000000000000000000000040810c000000000000000000000000000000000000000000000000000000000015807b0000000000000000000000000000000000000000000000000000000000158008000000000000000000000000000000000000000000000000000000000015807b000000000000000000000000000000000000000000000000000000000004802a00000000000000000000000000000000000000000000000000000000000037f70000000000000000000000000000000000000000000000000000000000000000
  | 0, 2 => 0x10840000000000000000000000000000000000000000000000000000000000000d78b7f0000000000000000000000000000000000000000000000000000000000c3bfff0000000000000000000000000000000000000000000000000000000000c38b1d0000000000000000000000000000000000000000000000000000000000c38b1d0000000000000000000000000000000000000000000000000000000000c20b04000000000000000000000000000000000000000000000000000000000041831d0000000000000000000000000000000000000000000000000000000000820800
  | 0, 3 => 0x14ce6d900000000000000000000000000000000000000000000000000000000014cd12e00000000000000000000000000000000000000000000000000000000014cc008000000000000000000000000000000000000000000000000000000000148510400000000000000000000000000000000000000000000000000000000010c5022000000000000000000000000000000000000000000000000000000000044912e00000000000000000000000000000000000000000000000000000000010cc02a0000000000000000000000000000000000000000000000000000000001085126
  | 0, 4 => 0x1aa6c8000000000000000000000000000000000000000000000000000000000012874e200000000000000000000000000000000000000000000000000000000012864800000000000000000000000000000000000000000000000000000000000b32cd10000000000000000000000000000000000000000000000000000000001cfc80800000000000000000000000000000000000000000000000000000000015dd17f000000000000000000000000000000000000000000000000000000000159515500000000000000000000000000000000000000000000000000000000014cf7ff
  | 0, 5 => 0xe6bdae0000000000000000000000000000000000000000000000000000000001ebef9d0000000000000000000000000000000000000000000000000000000001bfecfb0000000000000000000000000000000000000000000000000000000001bfecfb0000000000000000000000000000000000000000000000000000000001aa7ff70000000000000000000000000000000000000000000000000000000001aa6c800000000000000000000000000000000000000000000000000000000001aa48000000000000000000000000000000000000000000000000000000000001aa7f84
  | 0, 6 => 0x4013040000000000000000000000000000000000000000000000000000000000151273000000000000000000000000000000000000000000000000000000000015907b00000000000000000000000000000000000000000000000000000000001410620000000000000000000000000000000000000000000000000000000000140000000000000000000000000000000000000000000000000000000000000119425100000000000000000000000000000000000000000000000000000000001102510000000000000000000000000000000000000000000000000000000000000200
  | 0, 7 => 0xc39b1d000000000000000000000000000000000000000000000000000000000055937f000000000000000000000000000000000000000000000000000000000055937f00000000000000000000000000000000000000000000000000000000005582590000000000000000000000000000000000000000000000000000000000558008000000000000000000000000000000000000000000000000000000000054136600000000000000000000000000000000000000000000000000000000005113550000000000000000000000000000000000000000000000000000000000401304
  | 0, 8 => 0xa22ed10000000000000000000000000000000000000000000000000000000000a22e80000000000000000000000000000000000000000000000000000000000070a5cc00000000000000000000000000000000000000000000000000000000003024c00000000000000000000000000000000000000000000000000000000000300000000000000000000000000000000000000000000000000000000000000020248000000000000000000000000000000000000000000000000000000000015dd12e0000000000000000000000000000000000000000000000000000000000d79b7f
  | 0, 9 => 0x1bb6ed10000000000000000000000000000000000000000000000000000000000b7aefb0000000000000000000000000000000000000000000000000000000000b72ef30000000000000000000000000000000000000000000000000000000000b32ed10000000000000000000000000000000000000000000000000000000000b32ed10000000000000000000000000000000000000000000000000000000000b308000000000000000000000000000000000000000000000000000000000000b32ed10000000000000000000000000000000000000000000000000000000000a32e91
  | 0, 10 => 0xf79b7f0000000000000000000000000000000000000000000000000000000000f73ff70000000000000000000000000000000000000000000000000000000000f33fd50000000000000000000000000000000000000000000000000000000000f79b7f0000000000000000000000000000000000000000000000000000000000e23f840000000000000000000000000000000000000000000000000000000000b73ef30000000000000000000000000000000000000000000000000000000000b33ed100000000000000000000000000000000000000000000000000000000003434e2
  | 0, 11 => 0x13c64c000000000000000000000000000000000000000000000000000000000013c506200000000000000000000000000000000000000000000000000000000013c400000000000000000000000000000000000000000000000000000000000013c74e2000000000000000000000000000000000000000000000000000000000128748000000000000000000000000000000000000000000000000000000000012840000000000000000000000000000000000000000000000000000000000000f7bfff0000000000000000000000000000000000000000000000000000000000f7aed9
  | 0, 12 => 0x17dd37f00000000000000000000000000000000000000000000000000000000013d76f300000000000000000000000000000000000000000000000000000000013d74e20000000000000000000000000000000000000000000000000000000001be7ce200000000000000000000000000000000000000000000000000000000017cd12e00000000000000000000000000000000000000000000000000000000013c74e200000000000000000000000000000000000000000000000000000000013c74e200000000000000000000000000000000000000000000000000000000013c7480
  | 0, 13 => 0x1be7ce20000000000000000000000000000000000000000000000000000000001bb7ed100000000000000000000000000000000000000000000000000000000017df7ff00000000000000000000000000000000000000000000000000000000017df6fb00000000000000000000000000000000000000000000000000000000017df4ea00000000000000000000000000000000000000000000000000000000017dd37f00000000000000000000000000000000000000000000000000000000017c77e600000000000000000000000000000000000000000000000000000000017df7ff
  | 0, 14 => 0x1fffcea0000000000000000000000000000000000000000000000000000000001ffc8080000000000000000000000000000000000000000000000000000000001ea7f840000000000000000000000000000000000000000000000000000000001bf7ef30000000000000000000000000000000000000000000000000000000001bf7ef30000000000000000000000000000000000000000000000000000000001bf7ce20000000000000000000000000000000000000000000000000000000001bf6ed10000000000000000000000000000000000000000000000000000000001bf4800
  | 0, 15 => 0x1ea7f840000000000000000000000000000000000000000000000000000000001eeffae0000000000000000000000000000000000000000000000000000000001ea7ff70000000000000000000000000000000000000000000000000000000001ea7f840000000000000000000000000000000000000000000000000000000001ea7c800000000000000000000000000000000000000000000000000000000001ea48730000000000000000000000000000000000000000000000000000000001ea48000000000000000000000000000000000000000000000000000000000001ffffff
  | 1, 0 => 0x1ffffff0000000000000000000000000000000000000000000000000000000001ffffdd0000000000000000000000000000000000000000000000000000000001ffff8c0000000000000000000000000000000000000000000000000000000001ffdb7f0000000000000000000000000000000000000000000000000000000001ffc8080000000000000000000000000000000000000000000000000000000001fe7fe60000000000000000000000000000000000000000000000000000000001fb7fd50000000000000000000000000000000000000000000000000000000001fa7fc4
  | 1, 1 => 0x1ffd86a0000000000000000000000000000000000000000000000000000000001ffca590000000000000000000000000000000000000000000000000000000001ffd92e0000000000000000000000000000000000000000000000000000000001ffc87b0000000000000000000000000000000000000000000000000000000001ffc8080000000000000000000000000000000000000000000000000000000001fe7fe60000000000000000000000000000000000000000000000000000000001fe7f840000000000000000000000000000000000000000000000000000000001fb7fd5
  | 1, 2 => 0x1ffffff0000000000000000000000000000000000000000000000000000000001ffff8c0000000000000000000000000000000000000000000000000000000001fffefb0000000000000000000000000000000000000000000000000000000001fffcea0000000000000000000000000000000000000000000000000000000001ffeed90000000000000000000000000000000000000000000000000000000001ffecc80000000000000000000000000000000000000000000000000000000001ffdb7f0000000000000000000000000000000000000000000000000000000001ffdb0c
  | 1, 3 => 0x1ffffee
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 153 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 153 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 153 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 153 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 8 0) :: stateWiresD n (ids >>> 8)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 8 0) :: stateWiresS n (ids >>> 8)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 9 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_55 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_55 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_55 == dom_55) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_55 goalM u ys) : RunD dom_55 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_55 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 16 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_16 : ∀ i, 16 ≤ i → i < 20 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 16 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 20 → Z 4 i = true := (range_split z4_0 z4_16)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_16 : ∀ i, 16 ≤ i → i < 32 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_32 : ∀ i, 32 ≤ i → i < 48 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_48 : ∀ i, 48 ≤ i → i < 64 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_64 : ∀ i, 64 ≤ i → i < 80 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_80 : ∀ i, 80 ≤ i → i < 96 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_96 : ∀ i, 96 ≤ i → i < 112 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_112 : ∀ i, 112 ≤ i → i < 121 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 9 112 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 121 → Z 5 i = true := (range_split (range_split (range_split z5_0 z5_16) (range_split z5_32 z5_48)) (range_split (range_split z5_64 z5_80) (range_split z5_96 z5_112)))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 16 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_16 : ∀ i, 16 ≤ i → i < 32 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_32 : ∀ i, 32 ≤ i → i < 48 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_48 : ∀ i, 48 ≤ i → i < 64 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_64 : ∀ i, 64 ≤ i → i < 80 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_80 : ∀ i, 80 ≤ i → i < 96 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_96 : ∀ i, 96 ≤ i → i < 112 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_112 : ∀ i, 112 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_128 : ∀ i, 128 ≤ i → i < 144 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 144 → Z 6 i = true := (range_split (range_split (range_split (range_split z6_0 z6_16) (range_split z6_32 z6_48)) (range_split (range_split z6_64 z6_80) (range_split z6_96 z6_112))) z6_128)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : ∀ i, 0 ≤ i → i < 15 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 15 0 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 15 → Z 7 i = true := z7_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_0 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := z8_0
theorem checked (s : Nat) (hs : s ≤ 8) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
  · exact fun i hi => z7 i (Nat.zero_le i) hi
  · exact fun i hi => z8 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_55 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 8) (h : RunD dom_55 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_55 roots_55 goal_55 9 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_55 goal_55 := by
    have h0 : isConstB dom_55 goal_55 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_55

theorem low_55 : Lower dom_55 roots_55 goal_55 9 := S_55.noCircuit

namespace S_31
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 9), (1, 17), (2, 3), (2, 10), (4, 5), (4, 12), (6, 7), (6, 14), (6, 22), (8, 9), (8, 10), (8, 12), (16, 17), (18, 19), (18, 22), (18, 26), (20, 21), (20, 22), (20, 28), (24, 25), (24, 26), (24, 28)]
def r1sG : List Nat := [1, 1, 1, 1, 2, 2, 4, 4, 6, 6, 6, 8, 8, 8, 16, 18, 18, 18, 20, 20, 20, 24, 24, 24]
def r2sG : List Nat := [3, 5, 9, 17, 3, 10, 5, 12, 7, 14, 22, 9, 10, 12, 17, 19, 22, 26, 21, 22, 28, 25, 26, 28]
def mpG : Nat := 0xffffff
def pool6G : List Nat := [2203453098243, 6601668166405, 4402476484869, 6601701721347, 22067559072534, 8800422200073, 6601701724419, 21994629628689, 6601668169987, 6601668169989, 8822166260236, 8822199815178, 8804700324618, 19795606373137]
def xsM : List Nat := roots_31.map (· &&& dom_31)
def goalM : Nat := goal_31 &&& dom_31
def NN : Nat → Nat
  | 4 => 4
  | 5 => 39
  | 6 => 24
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xac05225e6a067ca66837143741914924
  | 5, 0 => 0xf0b2ef13e457f490de66a692d591247cca558791c9791fc3c56e12e7c5159104b5aa084fafa58f64aef4429fac05225ea9d56a51a571db929df29cfa8c616cec8aac6f2a6baa581364d4803364ae694e6112f50b5e1d4aa85455cc28537bfbe75299e96d4ca62407419de0e53a6b8d413649f21e32f633fb32c86e8232bc99002637312d208dd7bc1ac7d7cf18c3dfb0153162e908a43bb300ea224a
  | 6, 0 => 0xe0bddffad051f507c5159104c1afdc6dbe3a6442ac05225eaa294541a0508cfd93c0f7228c616cec818360617ecfa1837702c5a9744473ec554c825e5299e96d3a6b8d4130706e42276bea43208dd7bc206585ea1b8a7ef1126b25b70241d3e1
  | 7, 0 => 0xac05225e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x8888888800000000000000000000000000000000000000000000000000000000555555550000000000000000000000000000000000000000000000000000000033333333000000000000000000000000000000000000000000000000000000000f0f0f0f0000000000000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000ff0000000000000000000000000000000000000000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000ff
  | 0, 1 => 0xcccccccc00000000000000000000000000000000000000000000000000000000cccc000000000000000000000000000000000000000000000000000000000000cc00cc0000000000000000000000000000000000000000000000000000000000c0c0c0c000000000000000000000000000000000000000000000000000000000aaaaaaaa00000000000000000000000000000000000000000000000000000000aaaa000000000000000000000000000000000000000000000000000000000000aa00aa0000000000000000000000000000000000000000000000000000000000a0a0a0a0
  | 0, 2 => 0xfafaf0f000000000000000000000000000000000000000000000000000000000fafa000000000000000000000000000000000000000000000000000000000000faaafaaa00000000000000000000000000000000000000000000000000000000f8f8f8f800000000000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000eecceecc
  | 0, 3 => 0xffaaff0000000000000000000000000000000000000000000000000000000000ffa0ffa000000000000000000000000000000000000000000000000000000000ff00ffff00000000000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000fcfcfcfc00000000000000000000000000000000000000000000000000000000fcf0fcf000000000000000000000000000000000000000000000000000000000fafafafa
  | 0, 4 => 0xffffcccc00000000000000000000000000000000000000000000000000000000ffffaaaa00000000000000000000000000000000000000000000000000000000ffffaa0000000000000000000000000000000000000000000000000000000000ffff888800000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000fff0fff000000000000000000000000000000000000000000000000000000000ffccffcc00000000000000000000000000000000000000000000000000000000ffaaffaa
  | 0, 5 => 0xffffff0000000000000000000000000000000000000000000000000000000000fffff0f000000000000000000000000000000000000000000000000000000000fffff000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x8dc4cf2d408de60f402381341008e254f4
  | 5, 0, 0 => 0x7133c6056370f2c458dc4c615687133cb58dc4cf19637933cb58cf2c40d6a7132c558dc5cf2d637183c85a9c4cf2d634cf18358dc64f2d5d7133cb58dc5533d6a4cf2c35
  | 5, 0, 1 => 0x7133cb05647133cb57133cb016a7133c658dc4cf2d533cb0c254cf2c3055c5933cb58d33cb0d637d33cb570f2c4056370b14458dc50f2d657133cb58e244f2d6371340b5
  | 5, 0, 2 => 0x2371a30b599c4cf296a6d33cb58e04cf256a8133cb57133cb096771338b5
  | 6, 0, 0 => 0x8dc6933cb60234cf2c35a637133cb68dc4cf2c56aa37133cb68dc4cf30b68dc4cf2ca602370f2c450237133c658e17133cb69a37133cb602a7133cb58dc6133cb68dc4cf2c168dc4cf34b68dc4d23cb6
  | 6, 0, 1 => 0x8dc4cf2c368dc4cf2c6601c4cf2c158dc4cf2c968dc6d33cb60237133cb58e07133cb68dc4cf2c76
  | 7, 0, 0 => 0x237133cb5
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 34
  | 5 => 34
  | 6 => 40
  | 7 => 34
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 6 0) :: stateWires n (ids >>> 6)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xfffff00000000000000000000000000000000000000000000000000000000000fc78cf0000000000000000000000000000000000000000000000000000000000e3f83f00000000000000000000000000000000000000000000000000000000001fc7ff00000000000000000000000000000000000000000000000000000000001fc0000000000000000000000000000000000000000000000000000000000000003fff00000000000000000000000000000000000000000000000000000000000007ff
  | 0, 1 => 0x38730000000000000000000000000000000000000000000000000000000000003800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000700000000000000000000000000000000000000000000000000000000000000000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 0, 2 => 0x1c07c000000000000000000000000000000000000000000000000000000000001c0000000000000000000000000000000000000000000000000000000000000000000f00000000000000000000000000000000000000000000000000000000001c07c000000000000000000000000000000000000000000000000000000000001c07c000000000000000000000000000000000000000000000000000000000001c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000038730
  | 0, 3 => 0xe038000000000000000000000000000000000000000000000000000000000000e038000000000000000000000000000000000000000000000000000000000000e03fff0000000000000000000000000000000000000000000000000000000000e038000000000000000000000000000000000000000000000000000000000000e0000000000000000000000000000000000000000000000000000000000000001f87f000000000000000000000000000000000000000000000000000000000001c07c000000000000000000000000000000000000000000000000000000000001c07cf
  | 0, 4 => 0xffc7300000000000000000000000000000000000000000000000000000000000ffc00f0000000000000000000000000000000000000000000000000000000000ffc0000000000000000000000000000000000000000000000000000000000000ffc0000000000000000000000000000000000000000000000000000000000000ffc0000000000000000000000000000000000000000000000000000000000000fc3fc00000000000000000000000000000000000000000000000000000000000e3bf300000000000000000000000000000000000000000000000000000000000e0380f
  | 0, 5 => 0xfff8000000000000000000000000000000000000000000000000000000000000ffc7c00000000000000000000000000000000000000000000000000000000000ffc000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x81110000000000000000000000000000000000000000000000000000000000db36a00000000000000000000000000000000000000000000000000000000000b468ce000000000000000000000000000000000000000000000000000000000062d83d00000000000000000000000000000000000000000000000000000000000dc55b00000000000000000000000000000000000000000000000000000000000dc4080000000000000000000000000000000000000000000000000000000000003bf70000000000000000000000000000000000000000000000000000000000000153
  | 0, 1 => 0x4b973100000000000000000000000000000000000000000000000000000000004b840000000000000000000000000000000000000000000000000000000000004212200000000000000000000000000000000000000000000000000000000000090700000000000000000000000000000000000000000000000000000000000024c95f000000000000000000000000000000000000000000000000000000000024c00800000000000000000000000000000000000000000000000000000000002008040000000000000000000000000000000000000000000000000000000000040142
  | 0, 2 => 0xbde7ca0000000000000000000000000000000000000000000000000000000000bdc4080000000000000000000000000000000000000000000000000000000000b4ebdf00000000000000000000000000000000000000000000000000000000009da7d300000000000000000000000000000000000000000000000000000000009d27c200000000000000000000000000000000000000000000000000000000009d0400000000000000000000000000000000000000000000000000000000000090228000000000000000000000000000000000000000000000000000000000006b9f35
  | 0, 3 => 0xf6faac0000000000000000000000000000000000000000000000000000000000f63be60000000000000000000000000000000000000000000000000000000000f23bf70000000000000000000000000000000000000000000000000000000000f23aa40000000000000000000000000000000000000000000000000000000000f200000000000000000000000000000000000000000000000000000000000000dfb7f30000000000000000000000000000000000000000000000000000000000df37e20000000000000000000000000000000000000000000000000000000000bdefdf
  | 0, 4 => 0xffd7390000000000000000000000000000000000000000000000000000000000ffcd5f0000000000000000000000000000000000000000000000000000000000ffcc0c0000000000000000000000000000000000000000000000000000000000ffc5190000000000000000000000000000000000000000000000000000000000ffc4080000000000000000000000000000000000000000000000000000000000ff3fe60000000000000000000000000000000000000000000000000000000000fbbfb50000000000000000000000000000000000000000000000000000000000f6fbff
  | 0, 5 => 0xfffeac0000000000000000000000000000000000000000000000000000000000ffe7ca0000000000000000000000000000000000000000000000000000000000ffe688
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 43 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 43 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 43 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 43 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 6 0) :: stateWiresD n (ids >>> 6)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 6 0) :: stateWiresS n (ids >>> 6)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 7 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_31 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_31 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_31 == dom_31) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_31 goalM u ys) : RunD dom_31 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_31 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_16 : ∀ i, 16 ≤ i → i < 32 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_32 : ∀ i, 32 ≤ i → i < 39 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 7 32 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 39 → Z 5 i = true := (range_split (range_split z5_0 z5_16) z5_32)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 16 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_16 : ∀ i, 16 ≤ i → i < 24 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 16 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 24 → Z 6 i = true := (range_split z6_0 z6_16)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := z7_0
theorem checked (s : Nat) (hs : s ≤ 7) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
  · exact fun i hi => z7 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_31 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_31 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_31 roots_31 goal_31 8 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_31 goal_31 := by
    have h0 : isConstB dom_31 goal_31 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_31

theorem low_31 : Lower dom_31 roots_31 goal_31 8 := S_31.noCircuit

namespace S_59
def pairsG : List (Nat × Nat) := [(1, 3), (1, 9), (1, 17), (1, 33), (2, 3), (2, 10), (8, 9), (8, 10), (16, 17), (18, 19), (18, 26), (18, 50), (24, 25), (24, 26), (32, 33), (34, 35), (34, 42), (34, 50), (40, 41), (40, 42), (48, 49), (48, 50), (56, 57), (56, 58)]
def r1sG : List Nat := [1, 1, 1, 1, 2, 2, 8, 8, 16, 18, 18, 18, 24, 24, 32, 34, 34, 34, 40, 40, 48, 48, 56, 56]
def r2sG : List Nat := [3, 9, 17, 33, 3, 10, 9, 10, 17, 19, 26, 50, 25, 26, 33, 35, 42, 50, 41, 42, 49, 50, 57, 58]
def mpG : Nat := 0xffffff
def pool6G : List Nat := [2203453098243, 19796077970193, 8800691096073, 52922604913458, 19795907578115, 19860063585041, 19796077977873, 37387995579169, 52853886485298, 37460723700018, 26392876679945, 19796446546435, 8800960580105, 8804700324618]
def xsM : List Nat := roots_59.map (· &&& dom_59)
def goalM : Nat := goal_59 &&& dom_59
def NN : Nat → Nat
  | 4 => 13
  | 5 => 47
  | 6 => 24
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xffee2e23f4e2abe9ea6850c2c6ddf785c3827481bbe5e99c7369a05b6916d4c1487adbbe3db436a90c911e900b67488901b590a4
  | 5, 0 => 0xcec2c468ce5b8369c54abd37c532a7bfc3827481b1602efaa706c306a08d83c8997a51f793b906c5925f5c688c5020338bda1b5f85f28ed37c437918772c936873d477266db003546cc145556a3e48a06936924567de2d2d674a875b5f210ebd4cac355d4599038c410d737d402e413b3db436a93d69d27337f8ccf43552b34f34305f502fd455da26f145cd26bc2b5e24dba13223e936b21ba5db2b1b891d441763c2ec1475eb730f49a64c0b59138309710d2b06d5b4db061f7558
  | 6, 0 => 0xe017dec6cd1774a2c6eafbb0c3827481afe09bc3a48636c1a17346f2a052ac9e92fd4275925f5c6887084d0272783b7e6e9b733a6c35459f5a3c9a365878c3dd4cac355d4599038c418db97037f8ccf42a5942f41763c2ec14d4acce006bb7a1
  | 7, 0 => 0xc3827481
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x5050505050505050000000000000000000000000000000000000000000000000303030303030303000000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000f0000000f000000000000000000000000000000000000000000000000000000000f0f00000f0f0000000000000000000000000000000000000000000000000000000f0000000f000000000000000000000000000000000000000000000000000000000f0f0f0f
  | 0, 1 => 0xc0c0c0c0c0c0c0c0000000000000000000000000000000000000000000000000c0c0c0c000000000000000000000000000000000000000000000000000000000c0c00000c0c00000000000000000000000000000000000000000000000000000c000c000c000c000000000000000000000000000000000000000000000000000a0a0a0a0a0a0a0a0000000000000000000000000000000000000000000000000a0a00000a0a00000000000000000000000000000000000000000000000000000a000a000a000a000000000000000000000000000000000000000000000000000808080808080808
  | 0, 2 => 0xf000f000f000f000000000000000000000000000000000000000000000000000f0000000f0000000000000000000000000000000000000000000000000000000e0e0e0e0e0e0e0e0000000000000000000000000000000000000000000000000e0e0e0e000000000000000000000000000000000000000000000000000000000e0e0c0c0e0e0c0c0000000000000000000000000000000000000000000000000e0c0e0c0e0c0e0c0000000000000000000000000000000000000000000000000e0a0e0a0e0a0e0a0000000000000000000000000000000000000000000000000e000e000e000e00
  | 0, 3 => 0xf0f08080f0f08080000000000000000000000000000000000000000000000000f0f00000f0f00000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000f0c0f0c0f0c0f0c0000000000000000000000000000000000000000000000000f0a0f0a0f0a0f0a0000000000000000000000000000000000000000000000000f0a0f000f0a0f000000000000000000000000000000000000000000000000000f080f080f080f080000000000000000000000000000000000000000000000000f000f000f0f0f0f
  | 0, 4 => 0xf0f0f0a0f000f000000000000000000000000000000000000000000000000000f0f0f000f0f0f000000000000000000000000000000000000000000000000000f0f0f000f0f00000000000000000000000000000000000000000000000000000f0f0f000f000f000000000000000000000000000000000000000000000000000f0f0c0c0f0f0c0c0000000000000000000000000000000000000000000000000f0f0c000f0f0c000000000000000000000000000000000000000000000000000f0f0a0a0f0f0a0a0000000000000000000000000000000000000000000000000f0f0a0a00000000
  | 0, 5 => 0xf0f0f0f0f0f00000000000000000000000000000000000000000000000000000f0f0f0f0f000f000000000000000000000000000000000000000000000000000f0f0f0f0f0000000000000000000000000000000000000000000000000000000f0f0f0f0c000c000000000000000000000000000000000000000000000000000f0f0f0f0a0a00000000000000000000000000000000000000000000000000000f0f0f0f0a000a000000000000000000000000000000000000000000000000000f0f0f0f00000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0xa1e711402879b4900a1e655402d98f1d287973cb502d94f2d00b5e44f402d88f2d009de3cb402d98f2d00b662c6402e90f2d00b4f2c14
  | 5, 0, 0 => 0xa173cb05697973cb5a9e5cf2d688573ca5a2658f2d6d78f30b57985cf2d5e5d43cb5a1e5c7196d7973cb5a1e2c615687d73cb581e5cf2d688d734b5a172c6096e7573cb5
  | 5, 0, 1 => 0xa173cb0d5e5cf1c05a1e5d22d5e3cb1405a1e68f2d687903cb5b6898f2d6879b3c955cf2c201687973c75a1e3cb15687974cb5a265cb1940b663cb478f2c511685cf2c25
  | 5, 0, 2 => 0x2878f1c55b1e5cf2d687993cb5b665cf2d687973cb5a1e70c2d6879744f5b5e5cf1d6d78f2c55a1e5d521687972c65a2478f2d6d5cf2c25ade5cf2d6d79b3cb5
  | 6, 0, 0 => 0xa1e5cf2c660287972c65a1e7573cb6a237973cb6a1e5cf2c86a1e5cf38b6a217973cb6a1e5cf30b60287973c7502878f2c55b687973cb60285cf2c25a1e5cf2c7602d7973cb5a1e5cf2c06a1e5d63cb6
  | 6, 0, 1 => 0xa1e5cf2c96a1e5cf2c56a1e5d53cb60287973cb5a1e6d73cb6a1e7173cb6a1e5cf2ca6ba87973cb6
  | 7, 0, 0 => 0x287973cb5
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 34
  | 5 => 34
  | 6 => 40
  | 7 => 34
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 6 0) :: stateWires n (ids >>> 6)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xfffff00000000000000000000000000000000000000000000000000000000000fc71cf000000000000000000000000000000000000000000000000000000000033cf3f000000000000000000000000000000000000000000000000000000000033c0000000000000000000000000000000000000000000000000000000000000300f0000000000000000000000000000000000000000000000000000000000000fc0ff000000000000000000000000000000000000000000000000000000000003c03f0000000000000000000000000000000000000000000000000000000000003fff
  | 0, 1 => 0x38e3000000000000000000000000000000000000000000000000000000000000380000000000000000000000000000000000000000000000000000000000000000e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 0, 2 => 0xcc30c00000000000000000000000000000000000000000000000000000000000c030000000000000000000000000000000000000000000000000000000000000038e3f00000000000000000000000000000000000000000000000000000000000380000000000000000000000000000000000000000000000000000000000000038e300000000000000000000000000000000000000000000000000000000000038e30000000000000000000000000000000000000000000000000000000000000000f0000000000000000000000000000000000000000000000000000000000000000
  | 0, 3 => 0xf03f000000000000000000000000000000000000000000000000000000000000f03f000000000000000000000000000000000000000000000000000000000000f000000000000000000000000000000000000000000000000000000000000000cfbef00000000000000000000000000000000000000000000000000000000000cc30cf0000000000000000000000000000000000000000000000000000000000cc30c00000000000000000000000000000000000000000000000000000000000cc30c00000000000000000000000000000000000000000000000000000000000cc3fff
  | 0, 4 => 0xfc30c00000000000000000000000000000000000000000000000000000000000fc3fc00000000000000000000000000000000000000000000000000000000000fc3f000000000000000000000000000000000000000000000000000000000000fc30c00000000000000000000000000000000000000000000000000000000000f3bf300000000000000000000000000000000000000000000000000000000000f03f000000000000000000000000000000000000000000000000000000000000f03f0f0000000000000000000000000000000000000000000000000000000000f00000
  | 0, 5 => 0xffff000000000000000000000000000000000000000000000000000000000000fff0c00000000000000000000000000000000000000000000000000000000000fff0000000000000000000000000000000000000000000000000000000000000ffc0000000000000000000000000000000000000000000000000000000000000ffc0000000000000000000000000000000000000000000000000000000000000ffc0000000000000000000000000000000000000000000000000000000000000ffc000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xab2ca0000000000000000000000000000000000000000000000000000000000054514e000000000000000000000000000000000000000000000000000000000032cb1d000000000000000000000000000000000000000000000000000000000032c8080000000000000000000000000000000000000000000000000000000000320b0400000000000000000000000000000000000000000000000000000000000dc0fb000000000000000000000000000000000000000000000000000000000000c01900000000000000000000000000000000000000000000000000000000000037f7
  | 0, 1 => 0xabaeb10000000000000000000000000000000000000000000000000000000000ab88000000000000000000000000000000000000000000000000000000000000a22e0000000000000000000000000000000000000000000000000000000000008924a0000000000000000000000000000000000000000000000000000000000054d35f000000000000000000000000000000000000000000000000000000000050130400000000000000000000000000000000000000000000000000000000004410420000000000000000000000000000000000000000000000000000000000008211
  | 0, 2 => 0xcd34e20000000000000000000000000000000000000000000000000000000000c034000000000000000000000000000000000000000000000000000000000000ffffff0000000000000000000000000000000000000000000000000000000000ffc8080000000000000000000000000000000000000000000000000000000000fbbfb50000000000000000000000000000000000000000000000000000000000efbef30000000000000000000000000000000000000000000000000000000000ddf7ff0000000000000000000000000000000000000000000000000000000000cd34e2
  | 0, 3 => 0xf2bf150000000000000000000000000000000000000000000000000000000000f23f040000000000000000000000000000000000000000000000000000000000f208000000000000000000000000000000000000000000000000000000000000efbef30000000000000000000000000000000000000000000000000000000000ddf7ff0000000000000000000000000000000000000000000000000000000000dd37e60000000000000000000000000000000000000000000000000000000000cdb6f30000000000000000000000000000000000000000000000000000000000cd37f7
  | 0, 4 => 0xfffcea0000000000000000000000000000000000000000000000000000000000ff3fe60000000000000000000000000000000000000000000000000000000000ff3f040000000000000000000000000000000000000000000000000000000000ff3ce20000000000000000000000000000000000000000000000000000000000fbbfb50000000000000000000000000000000000000000000000000000000000fb3fa40000000000000000000000000000000000000000000000000000000000f6ff5f0000000000000000000000000000000000000000000000000000000000f6c808
  | 0, 5 => 0xffff0c0000000000000000000000000000000000000000000000000000000000fffcea0000000000000000000000000000000000000000000000000000000000fffc080000000000000000000000000000000000000000000000000000000000ffeca80000000000000000000000000000000000000000000000000000000000ffdb0c0000000000000000000000000000000000000000000000000000000000ffd84a0000000000000000000000000000000000000000000000000000000000ffc808
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 47 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 47 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 47 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 47 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 6 0) :: stateWiresD n (ids >>> 6)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 6 0) :: stateWiresS n (ids >>> 6)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 7 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_59 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_59 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_59 == dom_59) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_59 goalM u ys) : RunD dom_59 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_59 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 13 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 13 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 13 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_16 : ∀ i, 16 ≤ i → i < 32 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_32 : ∀ i, 32 ≤ i → i < 47 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 15 32 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 47 → Z 5 i = true := (range_split (range_split z5_0 z5_16) z5_32)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 16 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_16 : ∀ i, 16 ≤ i → i < 24 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 16 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 24 → Z 6 i = true := (range_split z6_0 z6_16)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := z7_0
theorem checked (s : Nat) (hs : s ≤ 7) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
  · exact fun i hi => z7 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_59 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_59 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_59 roots_59 goal_59 8 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_59 goal_59 := by
    have h0 : isConstB dom_59 goal_59 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_59

theorem low_59 : Lower dom_59 roots_59 goal_59 8 := S_59.noCircuit

namespace S_62
def pairsG : List (Nat × Nat) := [(2, 10), (4, 12), (6, 14), (6, 22), (8, 10), (8, 12), (18, 22), (18, 26), (18, 50), (20, 22), (20, 28), (20, 52), (24, 26), (24, 28), (34, 42), (34, 50), (36, 44), (36, 52), (38, 46), (38, 54), (40, 42), (40, 44), (48, 50), (48, 52), (56, 58), (56, 60)]
def r1sG : List Nat := [2, 4, 6, 6, 8, 8, 18, 18, 18, 20, 20, 20, 24, 24, 34, 34, 36, 36, 38, 38, 40, 40, 48, 48, 56, 56]
def r2sG : List Nat := [10, 12, 14, 22, 10, 12, 22, 26, 50, 22, 28, 52, 26, 28, 42, 50, 44, 52, 46, 54, 42, 44, 50, 52, 58, 60]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [19825906027530, 22067676973590]
def xsM : List Nat := roots_62.map (· &&& dom_62)
def goalM : Nat := goal_62 &&& dom_62
def NN : Nat → Nat
  | 4 => 1
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xa91103de
  | 5, 0 => 0xa91103de
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x55555555000000000000000000000000000000000000000000000000000000005555000055550000000000000000000000000000000000000000000000000000550055005500550000000000000000000000000000000000000000000000000050505050505050500000000000000000000000000000000000000000000000004444444444444444
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x46885
  | 5, 0, 0 => 0x46885
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 19
  | 5 => 19
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 3 0) :: stateWires n (ids >>> 3)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x3ffc0000000000000000000000000000000000000000000000000000000000003c03fc0000000000000000000000000000000000000000000000000000000000330303000000000000000000000000000000000000000000000000000000000000f0e0e00000000000000000000000000000000000000000000000000000000000cc1cd
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3ffc9000000000000000000000000000000000000000000000000000000000003cabfc800000000000000000000000000000000000000000000000000000000033574b70000000000000000000000000000000000000000000000000000000002af2e6e00000000000000000000000000000000000000000000000000000000015cd3dd
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 5 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 5 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 5 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 5 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 3 0) :: stateWiresD n (ids >>> 3)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 3 0) :: stateWiresS n (ids >>> 3)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_62 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_62 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_62 == dom_62) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_62 goalM u ys) : RunD dom_62 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_62 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := z5_0
theorem checked (s : Nat) (hs : s ≤ 5) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_62 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_62 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_62 roots_62 goal_62 6 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_62 goal_62 := by
    have h0 : isConstB dom_62 goal_62 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_62

theorem low_62 : Lower dom_62 roots_62 goal_62 6 := S_62.noCircuit

namespace S_47
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 9), (1, 33), (2, 3), (2, 10), (4, 5), (4, 12), (6, 7), (6, 14), (8, 9), (8, 10), (8, 12), (32, 33), (34, 35), (34, 42), (36, 37), (36, 44), (38, 39), (38, 46), (40, 41), (40, 42), (40, 44)]
def r1sG : List Nat := [1, 1, 1, 1, 2, 2, 4, 4, 6, 6, 8, 8, 8, 32, 34, 34, 36, 36, 38, 38, 40, 40, 40]
def r2sG : List Nat := [3, 5, 9, 33, 3, 10, 5, 12, 7, 14, 9, 10, 12, 33, 35, 42, 37, 44, 39, 46, 41, 42, 44]
def mpG : Nat := 0x7fffff
def pool6G : List Nat := [2203453098243, 8800422200073]
def xsM : List Nat := roots_47.map (· &&& dom_47)
def goalM : Nat := goal_47 &&& dom_47
def NN : Nat → Nat
  | 4 => 2
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x6d3e56560f1fce07
  | 5, 0 => 0xf1fce07
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffff000000000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000fcfc0000fcfc0000000000000000000000000000000000000000000000000000f0f00000f0f00000000000000000000000000000000000000000000000000000cccc0000cccc0000000000000000000000000000000000000000000000000000aaaa0000aaaa
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x58c258885
  | 5, 0, 0 => 0x58885
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 19
  | 5 => 19
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 3 0) :: stateWires n (ids >>> 3)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x7fe0000000000000000000000000000000000000000000000000000000000000701c0000000000000000000000000000000000000000000000000000000000000fc3f000000000000000000000000000000000000000000000000000000000000f03c000000000000000000000000000000000000000000000000000000000000cc330000000000000000000000000000000000000000000000000000000000000000f
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x7fe00800000000000000000000000000000000000000000000000000000000007a9ea400000000000000000000000000000000000000000000000000000000006fdbf300000000000000000000000000000000000000000000000000000000004f13c200000000000000000000000000000000000000000000000000000000002ccb31000000000000000000000000000000000000000000000000000000000015655f
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 6 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 6 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 6 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 6 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 3 0) :: stateWiresD n (ids >>> 3)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 3 0) :: stateWiresS n (ids >>> 3)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 3 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_47 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_47 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_47 == dom_47) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_47 goalM u ys) : RunD dom_47 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_47 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := z5_0
theorem checked (s : Nat) (hs : s ≤ 5) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_47 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_47 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_47 roots_47 goal_47 6 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_47 goal_47 := by
    have h0 : isConstB dom_47 goal_47 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_47

theorem low_47 : Lower dom_47 roots_47 goal_47 6 := S_47.noCircuit

namespace S_47_16
def pairsG : List (Nat × Nat) := [(16, 17), (18, 19), (18, 22), (18, 26), (18, 50), (20, 21), (20, 22), (20, 28), (20, 52), (24, 25), (24, 26), (24, 28), (48, 49), (48, 50), (48, 52), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [16, 18, 18, 18, 18, 20, 20, 20, 20, 24, 24, 24, 48, 48, 48, 56, 56, 56]
def r2sG : List Nat := [17, 19, 22, 26, 50, 21, 22, 28, 52, 25, 26, 28, 49, 50, 52, 57, 58, 60]
def mpG : Nat := 0x3ffff
def pool6G : List Nat := [22067946461718]
def xsM : List Nat := roots_47_16.map (· &&& dom_47_16)
def goalM : Nat := goal_47_16 &&& dom_47_16
def NN : Nat → Nat
  | 4 => 2
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x73240d52201cf257
  | 5, 0 => 0x73240d52
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffff0000ff000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000f0f00000f0f00000000000000000000000000000000000000000000000000000cccc0000cccc0000000000000000000000000000000000000000000000000000aaaa0000aaaa0000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x234428a884
  | 5, 0, 0 => 0x46885
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 19
  | 5 => 19
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 3 0) :: stateWires n (ids >>> 3)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x3fe00000000000000000000000000000000000000000000000000000000000003f0000000000000000000000000000000000000000000000000000000000000038e0000000000000000000000000000000000000000000000000000000000000001e0000000000000000000000000000000000000000000000000000000000000001e0000000000000000000000000000000000000000000000000000000000000000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3ff98000000000000000000000000000000000000000000000000000000000003f1100000000000000000000000000000000000000000000000000000000000038e8800000000000000000000000000000000000000000000000000000000000249e4000000000000000000000000000000000000000000000000000000000001245e0000000000000000000000000000000000000000000000000000000000009223
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 6 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 6 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 6 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 6 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 3 0) :: stateWiresD n (ids >>> 3)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 3 0) :: stateWiresS n (ids >>> 3)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 3 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_47_16 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_47_16 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_47_16 == dom_47_16) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_47_16 goalM u ys) : RunD dom_47_16 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_47_16 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := z5_0
theorem checked (s : Nat) (hs : s ≤ 5) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_47_16 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_47_16 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_47_16 roots_47_16 goal_47_16 6 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_47_16 goal_47_16 := by
    have h0 : isConstB dom_47_16 goal_47_16 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_47_16

theorem low_47_16 : Lower dom_47_16 roots_47_16 goal_47_16 6 := S_47_16.noCircuit

namespace S_15_16
def pairsG : List (Nat × Nat) := [(16, 17), (18, 19), (18, 22), (18, 26), (20, 21), (20, 22), (20, 28), (24, 25), (24, 26), (24, 28)]
def r1sG : List Nat := [16, 18, 18, 18, 20, 20, 20, 24, 24, 24]
def r2sG : List Nat := [17, 19, 22, 26, 21, 22, 28, 25, 26, 28]
def mpG : Nat := 0x3ff
def pool6G : List Nat := [22067946461718]
def xsM : List Nat := roots_15_16.map (· &&& dom_15_16)
def goalM : Nat := goal_15_16 &&& dom_15_16
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x202b72e1
  | 4, 0 => 0x202b72e1
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00000000000000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000cccc000000000000000000000000000000000000000000000000000000000000aaaa0000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xe44
  | 4, 0, 0 => 0xe44
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 12
  | 4 => 12
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 2 0) :: stateWires n (ids >>> 2)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x3800000000000000000000000000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000000000000000000e0000000000000000000000000000000000000000000000000000000000000000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3c80000000000000000000000000000000000000000000000000000000000000274000000000000000000000000000000000000000000000000000000000000012e0000000000000000000000000000000000000000000000000000000000000093
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 4 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 4 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 4 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 4 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 2 0) :: stateWiresD n (ids >>> 2)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 2 0) :: stateWiresS n (ids >>> 2)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_15_16 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_15_16 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_15_16 == dom_15_16) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_15_16 goalM u ys) : RunD dom_15_16 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_15_16 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := z4_0
theorem checked (s : Nat) (hs : s ≤ 4) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_15_16 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_15_16 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_15_16 roots_15_16 goal_15_16 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_15_16 goal_15_16 := by
    have h0 : isConstB dom_15_16 goal_15_16 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_15_16

theorem low_15_16 : Lower dom_15_16 roots_15_16 goal_15_16 5 := S_15_16.noCircuit

namespace S_27
def pairsG : List (Nat × Nat) := [(1, 3), (1, 9), (1, 17), (2, 3), (2, 10), (8, 9), (8, 10), (16, 17), (18, 19), (18, 26), (24, 25), (24, 26)]
def r1sG : List Nat := [1, 1, 1, 2, 2, 8, 8, 16, 18, 18, 24, 24]
def r2sG : List Nat := [3, 9, 17, 3, 10, 9, 10, 17, 19, 26, 25, 26]
def mpG : Nat := 0xfff
def pool6G : List Nat := [2203453098243, 8800422200073]
def xsM : List Nat := roots_27.map (· &&& dom_27)
def goalM : Nat := goal_27 &&& dom_27
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x317f6efe
  | 4, 0 => 0x317f6efe
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f0000000000000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000c0c0c0c000000000000000000000000000000000000000000000000000000000a0a0a0a
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xe44
  | 4, 0, 0 => 0xe44
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 12
  | 4 => 12
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 2 0) :: stateWires n (ids >>> 2)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xf800000000000000000000000000000000000000000000000000000000000000c6000000000000000000000000000000000000000000000000000000000000003180000000000000000000000000000000000000000000000000000000000000007
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xf840000000000000000000000000000000000000000000000000000000000000e720000000000000000000000000000000000000000000000000000000000000b5900000000000000000000000000000000000000000000000000000000000005af
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 4 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 4 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 4 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 4 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 2 0) :: stateWiresD n (ids >>> 2)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 2 0) :: stateWiresS n (ids >>> 2)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_27 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_27 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_27 == dom_27) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_27 goalM u ys) : RunD dom_27 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_27 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := z4_0
theorem checked (s : Nat) (hs : s ≤ 4) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_27 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_27 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_27 roots_27 goal_27 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_27 goal_27 := by
    have h0 : isConstB dom_27 goal_27 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_27

theorem low_27 : Lower dom_27 roots_27 goal_27 5 := S_27.noCircuit

namespace S_30
def pairsG : List (Nat × Nat) := [(2, 10), (4, 12), (6, 14), (6, 22), (8, 10), (8, 12), (18, 22), (18, 26), (20, 22), (20, 28), (24, 26), (24, 28)]
def r1sG : List Nat := [2, 4, 6, 6, 8, 8, 18, 18, 20, 20, 24, 24]
def r2sG : List Nat := [10, 12, 14, 22, 10, 12, 22, 26, 22, 28, 26, 28]
def mpG : Nat := 0xfff
def pool6G : List Nat := [8813576325644, 8805019945994, 19825906027530]
def xsM : List Nat := roots_30.map (· &&& dom_30)
def goalM : Nat := goal_30 &&& dom_30
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xe0cd3775
  | 4, 0 => 0xe0cd3775
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x55550000000000000000000000000000000000000000000000000000000000005500550000000000000000000000000000000000000000000000000000000000505050500000000000000000000000000000000000000000000000000000000044444444
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xe44
  | 4, 0, 0 => 0xe44
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 12
  | 4 => 12
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 2 0) :: stateWires n (ids >>> 2)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xfc00000000000000000000000000000000000000000000000000000000000000c30000000000000000000000000000000000000000000000000000000000000030e00000000000000000000000000000000000000000000000000000000000000cd
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfc80000000000000000000000000000000000000000000000000000000000000eb70000000000000000000000000000000000000000000000000000000000000b6e00000000000000000000000000000000000000000000000000000000000005dd
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 4 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 4 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 4 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 4 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 2 0) :: stateWiresD n (ids >>> 2)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 2 0) :: stateWiresS n (ids >>> 2)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_30 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_30 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_30 == dom_30) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_30 goalM u ys) : RunD dom_30 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_30 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := z4_0
theorem checked (s : Nat) (hs : s ≤ 4) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_30 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_30 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_30 roots_30 goal_30 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_30 goal_30 := by
    have h0 : isConstB dom_30 goal_30 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_30

theorem low_30 : Lower dom_30 roots_30 goal_30 5 := S_30.noCircuit

namespace S_54
def pairsG : List (Nat × Nat) := [(6, 22), (18, 22), (18, 50), (20, 22), (20, 52), (34, 50), (36, 52), (38, 54), (48, 50), (48, 52)]
def r1sG : List Nat := [6, 18, 18, 20, 20, 34, 36, 38, 48, 48]
def r2sG : List Nat := [22, 22, 50, 22, 52, 50, 52, 54, 50, 52]
def mpG : Nat := 0x3ff
def pool6G : List Nat := [22068350693910]
def xsM : List Nat := roots_54.map (· &&& dom_54)
def goalM : Nat := goal_54 &&& dom_54
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x9a327ca6
  | 4, 0 => 0x9a327ca6
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x55005500000000000000000000000000000000000000000000000000000000005500000055000000000000000000000000000000000000000000000000000000500050005000500000000000000000000000000000000000000000000000000044004400440044
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xe44
  | 4, 0, 0 => 0xe44
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 12
  | 4 => 12
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 2 0) :: stateWires n (ids >>> 2)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x3e0000000000000000000000000000000000000000000000000000000000000031e00000000000000000000000000000000000000000000000000000000000000d900000000000000000000000000000000000000000000000000000000000000a7
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3f400000000000000000000000000000000000000000000000000000000000003ff00000000000000000000000000000000000000000000000000000000000002db00000000000000000000000000000000000000000000000000000000000001af
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 4 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 4 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 4 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 4 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 2 0) :: stateWiresD n (ids >>> 2)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 2 0) :: stateWiresS n (ids >>> 2)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_54 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_54 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_54 == dom_54) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_54 goalM u ys) : RunD dom_54 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_54 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := z4_0
theorem checked (s : Nat) (hs : s ≤ 4) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_54 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_54 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_54 roots_54 goal_54 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_54 goal_54 := by
    have h0 : isConstB dom_54 goal_54 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_54

theorem low_54 : Lower dom_54 roots_54 goal_54 5 := S_54.noCircuit

namespace S_15
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 9), (2, 3), (2, 10), (4, 5), (4, 12), (6, 7), (6, 14), (8, 9), (8, 10), (8, 12)]
def r1sG : List Nat := [1, 1, 1, 2, 2, 4, 4, 6, 6, 8, 8, 8]
def r2sG : List Nat := [3, 5, 9, 3, 10, 5, 12, 7, 14, 9, 10, 12]
def mpG : Nat := 0xfff
def pool6G : List Nat := [2203453098243, 2203453229317]
def xsM : List Nat := roots_15.map (· &&& dom_15)
def goalM : Nat := goal_15 &&& dom_15
def NN : Nat → Nat
  | 3 => 2
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xa8d115120bc039e3
  | 4, 0 => 0xa8d11512
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00000000000000000000000000000000000000000000000000000000000000fcfc000000000000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000cccc000000000000000000000000000000000000000000000000000000000000aaaa
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x88841183
  | 4, 0, 0 => 0x8884
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 16
  | 4 => 16
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 3 0) :: stateWires n (ids >>> 3)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xe0000000000000000000000000000000000000000000000000000000000000001f800000000000000000000000000000000000000000000000000000000000001e000000000000000000000000000000000000000000000000000000000000001980000000000000000000000000000000000000000000000000000000000000007
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xf540000000000000000000000000000000000000000000000000000000000000dfb00000000000000000000000000000000000000000000000000000000000009e2000000000000000000000000000000000000000000000000000000000000059900000000000000000000000000000000000000000000000000000000000002af
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 5 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 5 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 5 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 5 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 3 0) :: stateWiresD n (ids >>> 3)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 3 0) :: stateWiresS n (ids >>> 3)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 3 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_15 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_15 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_15 == dom_15) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_15 goalM u ys) : RunD dom_15 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_15 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 2 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 2 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 2 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := z4_0
theorem checked (s : Nat) (hs : s ≤ 4) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_15 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_15 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_15 roots_15 goal_15 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_15 goal_15 := by
    have h0 : isConstB dom_15 goal_15 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_15

theorem low_15 : Lower dom_15 roots_15 goal_15 5 := S_15.noCircuit

namespace S_46_16
def pairsG : List (Nat × Nat) := [(18, 22), (18, 26), (18, 50), (20, 22), (20, 28), (20, 52), (24, 26), (24, 28), (48, 50), (48, 52), (56, 58), (56, 60)]
def r1sG : List Nat := [18, 18, 18, 20, 20, 20, 24, 24, 48, 48, 56, 56]
def r2sG : List Nat := [22, 26, 50, 22, 28, 52, 26, 28, 50, 52, 58, 60]
def mpG : Nat := 0xfff
def pool6G : List Nat := [22067946461718]
def xsM : List Nat := roots_46_16.map (· &&& dom_46_16)
def goalM : Nat := goal_46_16 &&& dom_46_16
def NN : Nat → Nat
  | 3 => 2
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xc770cbf16ed45346
  | 4, 0 => 0xc770cbf1
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x55550000550000000000000000000000000000000000000000000000000000005555000000000000000000000000000000000000000000000000000000000000550000005500000000000000000000000000000000000000000000000000000050500000505000000000000000000000000000000000000000000000000000004444000044440000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x68841083
  | 4, 0, 0 => 0x6884
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 16
  | 4 => 16
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 3 0) :: stateWires n (ids >>> 3)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xfc00000000000000000000000000000000000000000000000000000000000000f000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000380000000000000000000000000000000000000000000000000000000000000007
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xff60000000000000000000000000000000000000000000000000000000000000f240000000000000000000000000000000000000000000000000000000000000cd20000000000000000000000000000000000000000000000000000000000000ab9000000000000000000000000000000000000000000000000000000000000054f
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 5 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 5 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 5 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 5 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 3 0) :: stateWiresD n (ids >>> 3)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 3 0) :: stateWiresS n (ids >>> 3)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 3 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_46_16 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_46_16 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_46_16 == dom_46_16) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_46_16 goalM u ys) : RunD dom_46_16 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_46_16 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 2 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 2 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 2 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := z4_0
theorem checked (s : Nat) (hs : s ≤ 4) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_46_16 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_46_16 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_46_16 roots_46_16 goal_46_16 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_46_16 goal_46_16 := by
    have h0 : isConstB dom_46_16 goal_46_16 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_46_16

theorem low_46_16 : Lower dom_46_16 roots_46_16 goal_46_16 5 := S_46_16.noCircuit

def isoMv_61 : List (Nat × Nat) := [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem low_61 : Lower dom_61 roots_61 goal_61 8 :=
  lower_iso isoMv_61 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_59

def isoMv_43 : List (Nat × Nat) := [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]
theorem low_43 : Lower dom_43 roots_43 goal_43 5 :=
  lower_iso isoMv_43 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_27

def isoMv_29 : List (Nat × Nat) := [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem low_29 : Lower dom_29 roots_29 goal_29 5 :=
  lower_iso isoMv_29 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_27

def isoMv_45 : List (Nat × Nat) := [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]
theorem low_45 : Lower dom_45 roots_45 goal_45 5 :=
  lower_iso isoMv_45 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_27

namespace S_63
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 9), (1, 17), (1, 33), (2, 3), (2, 10), (4, 5), (4, 12), (6, 7), (6, 14), (6, 22), (8, 9), (8, 10), (8, 12), (16, 17), (18, 19), (18, 22), (18, 26), (18, 50), (20, 21), (20, 22), (20, 28), (20, 52), (24, 25), (24, 26), (24, 28), (32, 33), (34, 35), (34, 42), (34, 50), (36, 37), (36, 44), (36, 52), (38, 39), (38, 46), (38, 54), (40, 41), (40, 42), (40, 44), (48, 49), (48, 50), (48, 52), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [1, 1, 1, 1, 1, 2, 2, 4, 4, 6, 6, 6, 8, 8, 8, 16, 18, 18, 18, 18, 20, 20, 20, 20, 24, 24, 24, 32, 34, 34, 34, 36, 36, 36, 38, 38, 38, 40, 40, 40, 48, 48, 48, 56, 56, 56]
def r2sG : List Nat := [3, 5, 9, 17, 33, 3, 10, 5, 12, 7, 14, 22, 9, 10, 12, 17, 19, 22, 26, 50, 21, 22, 28, 52, 25, 26, 28, 33, 35, 42, 50, 37, 44, 52, 39, 46, 54, 41, 42, 44, 49, 50, 52, 57, 58, 60]
def mpG : Nat := 0x3fffffffffff
def pool6G : List Nat := [4402476484869, 8800422200073, 8804700324618, 2203453098243, 8813576325644, 22016020251414, 8822166260236, 22067559072534, 21994629628689, 19795606373137, 4402644914437, 19799900357891, 19795841254659, 19795907709189, 8813290259724, 52853886485298, 26392708909315, 39587052520737, 43997662348556, 37460723700018, 26397205332746, 26405761581836, 26397205990410, 43989392034826, 19816996996402, 26405762370060, 6601668166405, 37387995579169, 19816996996374, 43997662348044, 43989072413962, 22067945409046, 6601701721347, 26392876679945, 21994830955269, 26414352304652, 52781158368033, 52862476420404, 37388362057987, 8800457264137, 52781424968465, 43985331159817, 41928076887299, 44058111511562, 52781426803473, 39587385444613, 8800960580105, 22068213844502]
def xsM : List Nat := roots_63.map (· &&& dom_63)
def goalM : Nat := goal_63 &&& dom_63
def NN : Nat → Nat
  | 5 => 9
  | 6 => 83
  | 7 => 264
  | 8 => 140
  | 9 => 14
  | 10 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0xe1011018dac7954bd776e767c75f2c1cbf764b5e6d96dfc53636f93b2d9dc0e02d8e92fd
  | 6, 0 => 0xa84e6079a80baefb9bdc250d9ad02c5b9aacdfa09a84967399008a4d972eb7d7905081248c61d8ac89595cfb85a480e1854243ba81556ecc7f3c0b367df630b07d5bffbb7c27811e79bf06b07982a2c1734bd9946f8cf604697e86fd64683a6a62ad8252617ae3b95f7599dc5ae716de5967c8f75766e5cc57530f6056e194995404da6a4fcffd714d7c2d524d59122b462e666f458219853f439e5d3e8f6e5c3b2526c2392dd35437ca88eb34330fe033255a0b2a359c3b29074255270b4bd625afa38e234ad42922e782b61f759d8919f7890918d06a1e170619d11367ffd21246f66b0d4473350c236eef08f317a506165d760289dcf6025b7418024b4220
  | 6, 1 => 0xff2b818cfe7e79b3f9f4a199f8dc0f96e9ac187be93f704ae518a2f5e23be8c6d4de3103d3cc0ee5cb9173a2c6da7cedc619a842c3582c45c2074af1c0a10220bd9854fdb22bdbebb0a652f6
  | 7, 0 => 0x2e3b996a2e3a69332d98c7d02d618f3b2d3e70562c009a592b5b865a2ad9fd9b29af2b6427b671de275dc42024b0e3c1221f487121eaa96f20d56179203a91681fd3c25f1f0740291efda3231ed8ca961d85da9b1cd038361c0dd5381b16f5ed1a4dc7a419f37e071860cf55181431aa18103f8817bd8d8e166385a014e0d35f14393d8813af4bd913a79d19119fba6110bf6ca6108161dd0f06017a0eed14a20ee0af2a0e7db3450db432850d7f85ab0ccdc9130c825c970c13a5aa0c0bf6ea0b80dabe0af197a609bdf0a009695d4008df9739083843fe07f1b6d6054f0a5e047e05410423234202e8a90d01cde881014ecf6800d76e0200979151002f1772
  | 7, 1 => 0x5fd04d605f9873855d48a8d45bb357745b6b678f5b00c4075a4badc85a38516e595c1952593f584358ca2eae58b56100576d478156488c3a55a5888d54e7b9da54dccf5d516b0265504513214fbdd0064f57f3d24ef54bfc4c54b7244c16af5f4b48acc94a4249ab4a20e91b4754508e465893254606ca5745a7f598441784af440fd5ef43c1fcc940e5429a40c083b33f2afc363e791ea93decda2b3d0f7e103cd1bc7e3bd82cc93bcc8c933a9a85bd3a8cc1993a8512d93a4fc20639fa66b039de473f399f4d1238eeefa6388012b137b0076a37a858aa3748575a3727f4ba364691d835099e5633b85c4333907baf3285462230dba2142fa88bf32f3594f1
  | 7, 2 => 0x9caba4cf9b36b6809a0a4b6f997632ef98a19efa9891027896f60d7996bae4c8967fbfcb95b44849954c87d99515305d947d9aae92b8eaa091581840913e5b3c8fb5d0938fadecf38e27cd4e8e2522c88e1260558cd916648a91658a8a293c5387de9c8a87ab2db7878343c2840799a68355d815821853fe81b591e2817ebe35812adf7780f3a1e880b2da9b80ab0b5c805e03487eff2d3a7cd727a77a67caff79c02f7279135b88761880e674ae2b3472dc20f4719e52c170b68b1c6f63d0f66f5e8b526ed9b33e6e1154bf6c3e88df6bf899566be5d2566b7dedb66a08bb05680f7993672edba163cf9d8563bad2eb63b3242b63020dca62381e255fd7fc20
  | 7, 3 => 0xfad9fd75f6281cb5f4ae73bcf3ef218bf03745e0ee5bfb02ed2c9fa5e9bbe516e86349cbe4a3126fe3af474de28853e8e15e97d0ddf8e307dbc499a7db4f33a9d91b4e74d872797ad67aeb44d52fb620d1879d90d173caa4cf527d16ce540370cc636961cb7281a8c823f470c815559bc79122a7c6919570c5eadd1ec3bf146cc228c216c20018d3c1eeb825bebb555abe0cd55bba951fd0b9a57bbab81bcc44b4efd615b374d00fb2131be6b16ae077b0b15514ae1abeb8acbf5c17ac54c35babfd546aaa9f6be5aa881170aa00aaa3a8cca005a7853e24a72c89ada6246bc4a5ed1e7ba4ae7b11a48c4c1ba46ef71ea3c65a94a371c1d2a04d10569da9d51f
  | 7, 4 => 0xffc703bffed1b51bfeb6d93cfe88ed5bfddbe582fd9b65b0fcdf86a6fc6afe7d
  | 8, 0 => 0x645092fc640159025ec6f1c75e1657ce58905d13568ff7f154ed1c7554b47b9852f2fea451d2062b51bf3f2b4f490be64ec05ebd4bb222f34b0c2c3947e101a945d91ef1433f660a40455b7a3c39fd5e3950034037dd7e80355e29ce34ceb8d132ba82ac3122199e2f1362052d014b912b81626d29f0f18429e942c428a4a83e26beaf6f26bb2fef2310763b2219ec0a21a5f9682081cc61203e530f1fd3d3851d89743f1d81c57f1c1ffead1b61a0cd183e830516b50ee91581f8c8141a4f1c1415063f1413d6081317dd2b12b8884a123247971187183a0ffdfe370f8898390f6b9a140d4d98860cabde0a05ad2f34059e8b1703e36454033b05b500273479
  | 8, 1 => 0xd7ab2662d3c1c38ed2f3ad55d0e5095fd0dd3a20c7554d2ec73804a5c577bfccbef4bb49be4be64fbc18011abbe49247b7610a65b559ed2fb4e46fecb37ef559b23cd636ad85a160aa2867c5a98e4816a8e78fc4a8d9852aa5d7b7519c48de239ab0be7a97ec88bb968ac1e9967182b593f42b8d928df768926d751e9117715e8a81f0ca8958e8bc89211e6a877c8a9f85f48e9f828511a4811023557cd372a07b8db51e7b25f4ae7ae97d0f79e15a287952d274791d9b4178493a7f72b283397005f1236ec13cc56ebe77696db8095f6d5cb0976c4b6e046bed6d236be1bd3a6b46b4d16a7ff668688d1b5567f1c0d367044c4c668c4770651506a464e30e64
  | 8, 2 => 0xffabe638fcf8d17ffc3cf275f6657479f34c8d5aef94b1afe7283c3de575a6eadfdba1afdede789bde7f8515d8e7dfa1
  | 9, 0 => 0xf2854adfb6be7634a1f16def7f4590c976f0de335fbac6fd5e22a7545cde0cce55df5df851bb2a0f5059633d4aee73790e7e151305169eb0
  | 10, 0 => 0x42b779a3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x5555ffff000000000000000000000000000000000000000000000000000000005555555500000000000000000000000000000000000000000000000000000000333333330000000000000000000000000000000000000000000000000000000011111111000000000000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000303030300000000000000000000000000000000000000000000000000000000005500ff000000000000000000000000000000000000000000000000000000000000ffff
  | 0, 1 => 0x555500005555000000000000000000000000000000000000000000000000000033330000333300000000000000000000000000000000000000000000000000000f0f00000f0f000000000000000000000000000000000000000000000000000000ff005500ff0000000000000000000000000000000000000000000000000000005500ff00ff00000000000000000000000000000000000000000000000000000000ffffffff00000000000000000000000000000000000000000000000000000000ffffaaaa00000000000000000000000000000000000000000000000000000000fefefefe
  | 0, 2 => 0x5050707050507070000000000000000000000000000000000000000000000000505050507070707000000000000000000000000000000000000000000000000050505050505050500000000000000000000000000000000000000000000000003030303030303030000000000000000000000000000000000000000000000000101010101010101000000000000000000000000000000000000000000000000005500ff005500ff0000000000000000000000000000000000000000000000000000ffff0000ffff0000000000000000000000000000000000000000000000000000aaaa0000aaaa
  | 0, 3 => 0x5555000055550000000000000000000000000000000000000000000000000000545454545454545400000000000000000000000000000000000000000000000033333333333333330000000000000000000000000000000000000000000000001111333311113333000000000000000000000000000000000000000000000000111111111111333300000000000000000000000000000000000000000000000011111111111111110000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f00000000000000000000000000000000000000000000000005050f0f05050f0f
  | 0, 4 => 0xaaaa8888aaaa8888000000000000000000000000000000000000000000000000aaaa5555aaaa5555000000000000000000000000000000000000000000000000aaaa0000aaaa0000000000000000000000000000000000000000000000000000a8a8a8a8a8a8a8a80000000000000000000000000000000000000000000000005555ffff5555ffff0000000000000000000000000000000000000000000000005555aaaa5555aaaa00000000000000000000000000000000000000000000000055555555555555550000000000000000000000000000000000000000000000005555555550505050
  | 0, 5 => 0xabababababababab000000000000000000000000000000000000000000000000aaaaffffaaaaffff000000000000000000000000000000000000000000000000aaaaaaaaaaaaaaaa000000000000000000000000000000000000000000000000aaaaaaaaaaaa0000000000000000000000000000000000000000000000000000aaaaaaaaa8a8a8a8000000000000000000000000000000000000000000000000aaaaaaaaa0a0a0a0000000000000000000000000000000000000000000000000aaaaaaaa88888888000000000000000000000000000000000000000000000000aaaaa0a0aaaaa0a0
  | 0, 6 => 0xeeeeececeeeeecec000000000000000000000000000000000000000000000000eeeecccceeeecccc000000000000000000000000000000000000000000000000eeee0000eeee0000000000000000000000000000000000000000000000000000dddddddddddddddd000000000000000000000000000000000000000000000000cdcdcdcdcdcdcdcd000000000000000000000000000000000000000000000000ccccffffccccffff000000000000000000000000000000000000000000000000ccccddddccccdddd000000000000000000000000000000000000000000000000cccccccccccccccc
  | 0, 7 => 0xfafa0000fafa0000000000000000000000000000000000000000000000000000f5f5f5f5f5f5f5f5000000000000000000000000000000000000000000000000f0f0fffff0f0ffff000000000000000000000000000000000000000000000000f0f0fafaf0f0fafa000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000000eeeeeeeeeeeeeeee000000000000000000000000000000000000000000000000eeeeeeeeeeeecccc000000000000000000000000000000000000000000000000eeeeeeeeecececec
  | 0, 8 => 0xfcfcfcfcfcfcfcfc000000000000000000000000000000000000000000000000fcfca8a8fcfca8a8000000000000000000000000000000000000000000000000fcfc0000fcfc0000000000000000000000000000000000000000000000000000fafafafafafafafa000000000000000000000000000000000000000000000000fafafafafafaf0f0000000000000000000000000000000000000000000000000fafafafaf8f8f8f8000000000000000000000000000000000000000000000000fafaf8f8fafaf8f8000000000000000000000000000000000000000000000000fafaf0f0fafaf0f0
  | 0, 9 => 0xffa8ffa8ffa8ffa8000000000000000000000000000000000000000000000000ff01ff01ff01ff01000000000000000000000000000000000000000000000000ff00ff00ff00ff00000000000000000000000000000000000000000000000000fefefefefefefefe000000000000000000000000000000000000000000000000fefefefe00000000000000000000000000000000000000000000000000000000fefefcfcfefefcfc000000000000000000000000000000000000000000000000fefeaaaafefeaaaa000000000000000000000000000000000000000000000000fefe0000fefe0000
  | 0, 10 => 0xffeeffccffeeffcc000000000000000000000000000000000000000000000000ffaaffaaffaaff00000000000000000000000000000000000000000000000000ffaaffaaffa8ffa8000000000000000000000000000000000000000000000000ffaaffaaffa0ffa0000000000000000000000000000000000000000000000000ffaaffaaff88ff88000000000000000000000000000000000000000000000000ffaaffa0ffaaffa0000000000000000000000000000000000000000000000000ffaaff88ffaaff88000000000000000000000000000000000000000000000000ffaaff00ffaaff00
  | 0, 11 => 0xffffaaaa00000000000000000000000000000000000000000000000000000000ffffa8a8ffffa8a8000000000000000000000000000000000000000000000000ffff5555ffff5555000000000000000000000000000000000000000000000000ffff0000ffff0000000000000000000000000000000000000000000000000000ffff0000fafa0000000000000000000000000000000000000000000000000000ffff0000f0f00000000000000000000000000000000000000000000000000000ffff0000eeee0000000000000000000000000000000000000000000000000000ffff0000aaaa0000
  | 0, 12 => 0xfffffcfcfffffcfc000000000000000000000000000000000000000000000000fffffafafffffafa000000000000000000000000000000000000000000000000fffff0f0fffff0f0000000000000000000000000000000000000000000000000ffffeeeeffffeeee000000000000000000000000000000000000000000000000ffffccccffffcccc000000000000000000000000000000000000000000000000ffffaaaaffffaaaa000000000000000000000000000000000000000000000000ffffaaaaffff8888000000000000000000000000000000000000000000000000ffffaaaaeeeeaaaa
  | 0, 13 => 0xffffffff11111111000000000000000000000000000000000000000000000000ffffffff03030303000000000000000000000000000000000000000000000000ffffffff01010101000000000000000000000000000000000000000000000000ffffffff0000ffff000000000000000000000000000000000000000000000000ffffffff00005555000000000000000000000000000000000000000000000000ffffffff00000000000000000000000000000000000000000000000000000000ffffffaaff00ff00000000000000000000000000000000000000000000000000ffffff00ffaaff00
  | 0, 14 => 0xffffffffeeeeeeee000000000000000000000000000000000000000000000000ffffffffeeeecccc000000000000000000000000000000000000000000000000ffffffffcccccccc000000000000000000000000000000000000000000000000ffffffffaaaaaaaa000000000000000000000000000000000000000000000000ffffffffaaaa8888000000000000000000000000000000000000000000000000ffffffffaaaa0000000000000000000000000000000000000000000000000000ffffffffa8a8a8a8000000000000000000000000000000000000000000000000ffffffff55555555
  | 0, 15 => 0xffffffffffffaaaa000000000000000000000000000000000000000000000000ffffffffffff0000000000000000000000000000000000000000000000000000ffffffffffaaff00000000000000000000000000000000000000000000000000fffffffffefefefe000000000000000000000000000000000000000000000000fffffffffcfcfcfc000000000000000000000000000000000000000000000000fffffffffafafafa000000000000000000000000000000000000000000000000fffffffffafaf0f0000000000000000000000000000000000000000000000000fffffffff0f0f0f0
  | 1, 0 => 0xfffffffffffff0f0000000000000000000000000000000000000000000000000ffffffffffffcccc
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x696230251956a4d3026195623b30250b56a5c4f301556a5c513a1956a5c54301557e3b302d0c56a5c513b1a56a5c533a195
  | 6, 0, 0 => 0x7e683b302d5005c4d402d1d0a600006a5c4f4430500725c4d2d1d19600745c4d3b2a1d6006a624d3b2d1c6006a624d302c19600006a5c533b3a5006a62503b2d1d6006a5c4d3b2d1b6006a624d3027196004d3b211d110a6005c4d211d190a600625f4d3025196006a5c4d302d1760078755c4d2d146
  | 6, 0, 1 => 0x6a5c302d19126006a5c53302d196005c4d3b3021096006a5c3b302d0c6006a5c4d3021186005c50302d190a6006a5c4d40211d6006a6250443b3060078755c4d4721600735c4d302d196006a624d403a30600006a62503b36500785c4d472d056005c4d302d180a6006a5c4d3a29196006a5c523b2d1d6
  | 6, 0, 2 => 0x7a755c4d472d6005c503b302d01600745c4d302c196006a5c4d302d166006a4d211d19116006a594d3b30216006a614d302d196006a4d483b30216006a5c4d432d1d6006a5c503021196006a5c4f47443060072624d302d196006a5c4e3b302d6006a5c4d3b271a6004d2d1d19110a6006a3b302d12116
  | 6, 0, 3 => 0x6a5d4d301f196006a5c4d2d1d186005c4d302d1909600006a5c52443050072624d443b306006a5c56302d1960078755c4d4c2d6006a5c4d3b291a6000072624d3b3650078754d472d116007d685c3b302d6006b5c4d302d19600006a4d3b3022500624d3025190a6006a5c4f4c3b306006a624d362d196
  | 6, 0, 4 => 0x5c4d3b302d086005c3b302d120a6006a5c4d3a27196007d503b302d116007d5c50302d196006d5c4d3b302d6005c4d302d190760069625c302d196000069623b302556a625c4d47443a7006a5c502d1d19600625c3b302d0b600006a4d3b3026500725c4d3021196006a5c4d3024156006a4d3025190f6
  | 6, 0, 5 => 0x6a624d251d19600006a624d403656a5c55473b302d7
  | 7, 0, 0 => 0x6a5c4d302d27197006a5c4d3e3b211d700756a5c4d3b362d7006a5c4d3b39302d7006a4d3d3b3021117006a5c4d4440302d7006a5c4d3b31302d70000725c4d3b2d1d6007d6a5c503b302d700776a5c4d473b2d7006a5c4d4a40302d7006a645c4d302d197006a5c4d30211f197004d3b3a302d110a700625f5c4d3b2d1d700756a4d473b2d117
  | 7, 0, 1 => 0x725c4d473b302d70078745c4d47302d700786a5c4d473021700006a5c4d4030216006a644d3b35302d70000725c503b302d6006a5c4d3f3b30217006a624d3b36302d700006a5c4d3b3a29600786a4d3b2d1d11700006a5c4d4430246006a5d5c4d3b211d700756a5c4d4c3b2d700706a5c4d3b211d7007b745c4d3b302d7007b6a5c4d3b30217
  | 7, 0, 2 => 0x5c4d302d19110a70000735c4d3b302d600796a5c4d3b302d7006a635c4d3b2d1a700625c4d3b30210a7006a4d3b3a3021117006a5c4d44302d147006a5c4d463b302d700635c4d302d190a7006a5c4d3a3021197006a5c4d3b2d1d0d7006a5c4d47302d037006e6a5c4d3b302d700006a4d3b362d116006a5c4d302d2c19700006a5c4d362d196
  | 7, 0, 3 => 0x6a5d5c4d302d19700726a5c4d302d197006a5c4d47302d157006f6a5c4d3b302d700706a5c4d302d197006a5c4d403b2d1d700005c503b302d0a6006a5c4d3b302f2d700004d302d19110a600006a5c543b302d600006a624d3b302866a625c4d473b3a2d800796a5c4d40302d700655c4d3b30210a7006a5c4d3b33302d700756a5c4d3b2d1a7
  | 7, 0, 4 => 0x6a5c3b302d12600755c4d3b302d067005c4d4744302d0a700786a624d3b302570075745c4d302d19700756a5c4d3021197006a5c4d473b362d7006a5c4d403a302d7006a635c4d302119700006a5c4d43302d600746a4d3b302111700006a5c503b362d6006a4d3b302d1105700746a5c4d3021197006a5c4d302d19057006a4d3b302d14117
  | 7, 0, 5 => 0x7e6a5c4d3021197004d3b302d21110a7005c4d302d21190a7000072624d3b302d6006a5c4d3e3b2d1d700776a5c4d3b30217006a5c50443b302d7006a65624d3b2d1d700006a685c3b302d600006a5c4d3b372d6006a5c4d302119117006a5c4d3b302d0470075744d3b302d11700756a4d3b302111700005c4d2d1d190a6006a624d302d25197
  | 7, 0, 6 => 0x756a5c4d40302d700007e584d3b302d6006a5c4d3b3021207006a4d443b2d1d11700006a614d3b302d6006a5c4d302d19107000072624d3b30256004d473b302d110a7006a5c4d302d29197006a5c4d474430247007b6a5c4d44302d700006a5c503b3021600635c4d3b3a2d0a7007e5c4d3b302d06700006a4d302119116007e745c4d302d197
  | 7, 0, 7 => 0x6a5c4d3b30210370000745c4d3b302c6007b6a4d3b302d117006a5c4d3b3a2d0570078745c4d3b30217006a4d48443b302d7756a5c4d443b3a2d800785c4d3b302d057005c4d3b302d150a7006a5c4d413b302d70078725c4d3b302d7005c4d4c3b302d0a7006a5c4d3b342d1a700006a5c4d211d196005c4d3b36302d0a7006a5c4d474430217
  | 7, 0, 8 => 0x78755c4d472d600786a5b4d3b302d7006a5c4d493b302d70000715c4d3b302d6006a4d302d191110700625c4d302d190a700006b5c4d3b302d6006a5c4d4c3b30247006a4d473b30211170000624d3b30250a600006a624d3b362d60075745c4d3b3a2d700756a5c4d3b3a21700816a5c4d3b2d1d70078755c4d3b3021700745c4d3b302d037
  | 7, 0, 9 => 0x6a5c4d302d1906778745c4d3b3a302d8005c4d302d25190a7005c4d443b30210a700006a5c563b302d6006a5c4d3b302d027007a6a5b4d3b302d700006a5c4d302d186006a624d443b30257006a624d3b32302d700756a5c4d3b2d147006a5c4d4c3b30217006a605c4d3b302d7006a5c4d3b3630217007f6a5c4d302d19700006a624d3b36256
  | 7, 0, 10 => 0x776a4d3b302d1170000725c4d3b362d600006a5d4d3b301f6006a674d453b302d700786a5c4d473a2d700776a5c4d302d19700756a5c503b302d7006a5c4d3c3b302d7006a625c4d3021197006c6a5c4d3b30217006a634d302d19117006a4d3b302d110670076725c4d3b302d700746a4d302d1911700005c4d3b302d09600006a5c4f3b302d6
  | 7, 0, 11 => 0x6a5c4d302521197006a5c4d302d190f700725c4d443b302d7006a5c4d3b38302d700006a4d483b302d600006a503b302d116005c4d3b30211f0a700006a4d3b302e10600006a4d3b30250f600006a5c50302d196007e6a4d302d19117006a594d3b3a302d70000745c4d3b3029600746a5c4d2d1d197746a5c4d4744302d8006a5c5a4d3b30217
  | 7, 0, 12 => 0x746a594d3b302d76a5c4d49473b302d800005c4d3b362d0a6007c6a5c4d3b302d700715c4d473b302d700006a4d2d1d19116006a4d3c3b302d117006a4d4744302d117007e6a5c4d2d1d197006c6a4d3b30211177e6a5c4d4744302d8007a755c4d3b302d700006a594d3b302d60000725c4d3b302160078755c4d44302d7006a5c4d2d1d19117
  | 7, 0, 13 => 0x6a5e4d3b302d6005c4d3b302d140a7006a5c4d3b30211e7006a5c4d2d211d197006a5c4f473b302d7006a654d443f302d700005c4d3b302d076006a5c50473b302d700756a4d3b3a2d1170078754d3b302d11700756a5c4d3a2d197000069625c3b302d6006a635c4d3a2d197006a4d302d2119117006a5c57503b302d7006a624d3f3b302d7
  | 7, 0, 14 => 0x6a624d302d1911700005c4d3021190a6006a5c4d302d1a197006a4d48473b302d700006a624d3025196005c4d3b3021110a7006a5c4d47443a2d700006a634d3b352d6006a5c4d302d19007006a5c4d453b3021700006a5c4d443028600007d5c503b302d600006a5c513b302d6006a4d3b302d15117006a4d4c3b302d1176a5c4d473b302d2b8
  | 7, 0, 15 => 0x5c4d473b30210a7006a5c4d3b302d1e70000724d3b302d116006a624d473b3025700006a62503b30256005c4d4c4b3b302d76a625c4d443b3a308006a625c4d2d1d1970000625f4d3b3025600006a62503b302d600006a5c4d42302d6005c4d443b2d1d0a7007e6a624d302d197006a5c4d3b3021147006a5c4d3b323021700004d3b3021110a6
  | 7, 1, 0 => 0x6a5c4d4a3b302d7006a4d4c483b302d7006a5e4d473b302d7006a5c4d2d251d19700006a5c4d40362d600006a624d3b3023600006a624d3b302c6006a5c4d3b302d137
  | 8, 0, 0 => 0x6a5d5c4d3b302d700726a5c4d3b302d700706a5c4d3b302d76a635c4d443b302d8006a5c4d3b302d147006a5c4d3e3b302d7006a5c4d3b32302d700004d3b302d110a6006a65624d3b302d7746a5c4d443b302d800005c4d302d190a6005c4d3b302d110a76a5c4d443f3b302d86a675c4d473b302d8006a5c4d3b302e2d700635c4d3b302d0a7
  | 8, 0, 1 => 0x5c4d3b302d210a7006a5c4d3b302d287786a625c4d3b302d8006a4d443b302d117006a5c4d3b30211177e6a5c4d443b302d8006a4d3b302e2d117006a624d3b302d2570075745c4d3b302d700756a5c4d3b30217006a635c4d3b30217006a5c4d3b302d1f76a5c4d443b302d11800746a5c4d3b30217006a5c4d3b302d057756a5c4d443b302d8
  | 8, 0, 2 => 0x6a5c4d40302d6006a5c4d3f3b302d7007b6a5c4d3b302d76a5c4d47453b302d86a5c4d443b302d218786a5c4d3b302d25800816a5c4d3b302d7006a5c4d3b302d107006a5c4d443b2d1d7006a5c4d3b302d297005c4d473b302d0a7006a4d3b32302d11700006a4d3b3021116007e745c4d3b302d7007e6a5c4d3b3021700006a5c4d3021196
  | 8, 0, 3 => 0x6a625c4d443b302d8776a5c4d3b3a302d87f746a5c4d3b302d8746a5c4d3b302d118746a635c4d3b302d8007f6a5c4d3b302d76a665c4d443b302d8006a5c4d3b34302177a786a5c4d3b302d8006a4d3b302d1110700625c4d3b302d0a77b756a5c4d3b302d86a5c4d473b302d14800725c4d3b302d257006a5c4d473b3021700786a5c4d47302d7
  | 8, 0, 4 => 0x6a5c4d302d19117006a5c4d3b362d25700756a4d3b302d117006a625c4d3b30217006a634d3b302d117006a5c4d3b302d2476a5c4d443b302d15800756a5c4d302d1976a5c4d4c443b302d8006a635c4d302d197006a5c584d3b302d700746a4d3b302d117006a5c4d3b302d067005c4d3b302d250a700746a5c4d302d197756a5c4d3b302d118
  | 8, 0, 5 => 0x6a5c4d2d1d196006a5c4d3b302d0e7006a5c4d4744302d7746a5c4d473b302d8756a5c4d3b302d218006a5c4d3b3025217006a5c4d3b302d0f77b6a5c4d473b302d800006a5c503b302d6007e6a4d3b302d11777746a5c4d3b302d800006a4d302d1911680756a5c4d3b302d86a5c4d443b302d258007e6a5c4d302d19700776a5c4d3b302d7
  | 8, 0, 6 => 0x6a5c4d3b302d007006a625c4d3b30257746a625c4d3b302d8006a5c4d3b302d157006a5c4d4c3b302d76a5c4d473b302d248006a5c4d3b36302d7006a4d473b302d1177e6a5c4d473b302d800756a5c4d3b3a2d7006a635c4d3b3a2d70078755c4d3b302d7006a4d3b302d21117006a665c4d3b302d76a5c4d473b302d118006a5c4d302d21197
  | 8, 0, 7 => 0x725c4d3b302d6006a4d3b302d2511700625f5c4d3b302d7006a5c4d302d25197006a5c4d443b30217006a675c4d3b302d7007e6a624d3b302d7006a5c5a4d3b302d7006a624d3b302d11700005c4d3b30210a6006a625c4d302d197006c6a5c4d3b302d700006a624d3b30256756a655c4d3b302d8005c4d443b302d0a76a5c4d473b302d218
  | 8, 0, 8 => 0x6a5c4d453b302d7006a5c4d3b302d237006a5c4d3b302d2c76a5c4d443b3a302d86a5c4d473b302d258006a5c503b302d257006a5c4d3b30211f76a5c4d4c473b302d8006a5d5c4d3b3021700706a5c4d3b302176a625c4d473b302d8006c6a4d3b302d117
  | 9, 0, 0 => 0x5c4d3b302d0a66a5c4d3b302d2576a625c4d3b302d76a5c4d473b302d76a5c4d3b302d217006a4d3b302d1167e6a5c4d3b302d7006a5c4d302d1966a5c4d3b302d117756a5c4d3b302d76a635c4d3b302d7746a5c4d3b302d7006a5c4d3b302166a5c4d443b302d7
  | 10, 0, 0 => 0x6a5c4d3b302d6
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 44
  | 6 => 60
  | 7 => 68
  | 8 => 68
  | 9 => 60
  | 10 => 52
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 8 0) :: stateWires n (ids >>> 8)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x7ffffff0000000000000000000000000000000000000000000000000000000007ffffe00000000000000000000000000000000000000000000000000000000007f0f19f0000000000000000000000000000000000000000000000000000000007f0f18000000000000000000000000000000000000000000000000000000000070ff07f000000000000000000000000000000000000000000000000000000000700f01f0000000000000000000000000000000000000000000000000000000000ff8fff0000000000000000000000000000000000000000000000000000000000007fff
  | 0, 1 => 0xfff8007fe0000000000000000000000000000000000000000000000000000000e38800719f000000000000000000000000000000000000000000000000000000e07800707f0000000000000000000000000000000000000000000000000000001ff8ff8fff0000000000000000000000000000000000000000000000000000001ff8ff8fff0000000000000000000000000000000000000000000000000000000007ffffff0000000000000000000000000000000000000000000000000000000007ff801f0000000000000000000000000000000000000000000000000000000000ff0fff
  | 0, 2 => 0x3fe07f0ff07f00000000000000000000000000000000000000000000000000003fe07f0ff07f00000000000000000000000000000000000000000000000000003fe07f0ff06000000000000000000000000000000000000000000000000000003fe00f00f01f00000000000000000000000000000000000000000000000000003fe00f00f0000000000000000000000000000000000000000000000000000000071ff8ff8fff000000000000000000000000000000000000000000000000000000fff8007fff000000000000000000000000000000000000000000000000000000000000001f
  | 0, 3 => 0x3f0007ff80000000000000000000000000000000000000000000000000000000001ff0ff0fe000000000000000000000000000000000000000000000000000003fe38ff0f19f00000000000000000000000000000000000000000000000000003fe38ff0f19f00000000000000000000000000000000000000000000000000003fe38ff0f19f00000000000000000000000000000000000000000000000000003fe38ff0f18000000000000000000000000000000000000000000000000000003fe07f0ff07f00000000000000000000000000000000000000000000000000003fe07f0ff07f
  | 0, 4 => 0xfff8007fe00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003fffffffffff00000000000000000000000000000000000000000000000000003f0007ff801f00000000000000000000000000000000000000000000000000003fffffffffe000000000000000000000000000000000000000000000000000003ffff8f00f80
  | 0, 5 => 0x3fe00f00f01f000000000000000000000000000000000000000000000000000000fff8007fff000000000000000000000000000000000000000000000000000000000000001f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 0, 6 => 0x1c700f0e600000000000000000000000000000000000000000000000000000001c700f0e6000000000000000000000000000000000000000000000000000000000000f000000000000000000000000000000000000000000000000000000003fffffffffe000000000000000000000000000000000000000000000000000003ffc7f0ffe60000000000000000000000000000000000000000000000000000000fff80f7fff000000000000000000000000000000000000000000000000000000fff80f7fe00000000000000000000000000000000000000000000000000000001c700f0e60
  | 0, 7 => 0xf0000000000000000000000000000000000000000000000000000000003fffffffffe0000000000000000000000000000000000000000000000000000000fff8f07fff0000000000000000000000000000000000000000000000000000001f80f00f9f0000000000000000000000000000000000000000000000000000001f80f00f800000000000000000000000000000000000000000000000000000001c700f0e7f0000000000000000000000000000000000000000000000000000001c700f0e600000000000000000000000000000000000000000000000000000001c700f0e60
  | 0, 8 => 0x1ff0ff0fe00000000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000001f80f00f9f0000000000000000000000000000000000000000000000000000001f80f00f800000000000000000000000000000000000000000000000000000001f80f00f800000000000000000000000000000000000000000000000000000001f80f00f800000000000000000000000000000000000000000000000000000001f80f00f80
  | 0, 9 => 0x38e00700700000000000000000000000000000000000000000000000000000003fe00f00f000000000000000000000000000000000000000000000000000000038e0070070000000000000000000000000000000000000000000000000000000001ff0ff0fff0000000000000000000000000000000000000000000000000000001ff00000000000000000000000000000000000000000000000000000000000001ff0ff0fe00000000000000000000000000000000000000000000000000000000000ff001f0000000000000000000000000000000000000000000000000000000000ff0000
  | 0, 10 => 0x38fc770f7e60000000000000000000000000000000000000000000000000000038e007007000000000000000000000000000000000000000000000000000000038e007007000000000000000000000000000000000000000000000000000000038e007007000000000000000000000000000000000000000000000000000000038e007007000000000000000000000000000000000000000000000000000000038e007007000000000000000000000000000000000000000000000000000000038e007007000000000000000000000000000000000000000000000000000000038e007007000
  | 0, 11 => 0x3f000000000000000000000000000000000000000000000000000000000000003f0007ff800000000000000000000000000000000000000000000000000000003fffffffffe000000000000000000000000000000000000000000000000000003f0007ff800000000000000000000000000000000000000000000000000000003f0000f0000000000000000000000000000000000000000000000000000000003f0000f0000000000000000000000000000000000000000000000000000000003f00000f000000000000000000000000000000000000000000000000000000003f0000000000
  | 0, 12 => 0x3f1ff7ff8fe000000000000000000000000000000000000000000000000000003f1f87ff8f9f00000000000000000000000000000000000000000000000000003f1f87ff8f8000000000000000000000000000000000000000000000000000003f1c77ff8e7f00000000000000000000000000000000000000000000000000003f1c77ff8e6000000000000000000000000000000000000000000000000000003f0007ff801f00000000000000000000000000000000000000000000000000003f0007ff800000000000000000000000000000000000000000000000000000003f00000f001f
  | 0, 13 => 0x3ffffff0f18000000000000000000000000000000000000000000000000000003fffff00f01f00000000000000000000000000000000000000000000000000003fffff00f00000000000000000000000000000000000000000000000000000003ffff8007fff00000000000000000000000000000000000000000000000000003ffff8007fe000000000000000000000000000000000000000000000000000003ffff800000000000000000000000000000000000000000000000000000000003fe00700700000000000000000000000000000000000000000000000000000003fe007007000
  | 0, 14 => 0x3ffff80f0e7f00000000000000000000000000000000000000000000000000003ffff80f0e6000000000000000000000000000000000000000000000000000003ffff80f0e6000000000000000000000000000000000000000000000000000003ffff800001f00000000000000000000000000000000000000000000000000003ffff800000000000000000000000000000000000000000000000000000000003ffff800000000000000000000000000000000000000000000000000000000003ffff800000000000000000000000000000000000000000000000000000000003fffffffffe0
  | 0, 15 => 0x3fffffff801f00000000000000000000000000000000000000000000000000003fffffff800000000000000000000000000000000000000000000000000000003fffff00700000000000000000000000000000000000000000000000000000003ffff8ff0fff00000000000000000000000000000000000000000000000000003ffff8ff0fe000000000000000000000000000000000000000000000000000003ffff8f00f9f00000000000000000000000000000000000000000000000000003ffff8f00f8000000000000000000000000000000000000000000000000000003ffff8f00f80
  | 1, 0 => 0x3fffffff8f8000000000000000000000000000000000000000000000000000003fffffff8e60
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x6667fe70000000000000000000000000000000000000000000000000000000006666d40000000000000000000000000000000000000000000000000000000000550d18e0000000000000000000000000000000000000000000000000000000004404100000000000000000000000000000000000000000000000000000000000305b06d000000000000000000000000000000000000000000000000000000000100900c0000000000000000000000000000000000000000000000000000000000220aa300000000000000000000000000000000000000000000000000000000000077e7
  | 0, 1 => 0xc920006540000000000000000000000000000000000000000000000000000000a18800519600000000000000000000000000000000000000000000000000000060380030750000000000000000000000000000000000000000000000000000000498220ab30000000000000000000000000000000000000000000000000000000000338aab000000000000000000000000000000000000000000000000000000000777ffef0000000000000000000000000000000000000000000000000000000007779aaf000000000000000000000000000000000000000000000000000000000777ffef
  | 0, 2 => 0x12606a0c305400000000000000000000000000000000000000000000000000001240630cb04c00000000000000000000000000000000000000000000000000001240620c2040000000000000000000000000000000000000000000000000000009200900901c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000616d8aa0ab3000000000000000000000000000000000000000000000000000000edb80077f700000000000000000000000000000000000000000000000000000024980012b7
  | 0, 3 => 0x361246ee0800000000000000000000000000000000000000000000000000000036db66ee6d4000000000000000000000000000000000000000000000000000002da38dd0d19e000000000000000000000000000000000000000000000000000024a38cc051960000000000000000000000000000000000000000000000000000248304c051860000000000000000000000000000000000000000000000000000248304c0410000000000000000000000000000000000000000000000000000001b607b0db07d000000000000000000000000000000000000000000000000000012607a0c3075
  | 0, 4 => 0x90411118229000000000000000000000000000000000000000000000000000009c92111e548000000000000000000000000000000000000000000000000000009000111800800000000000000000000000000000000000000000000000000000004901102a3000000000000000000000000000000000000000000000000000036fffeee7ff700000000000000000000000000000000000000000000000000003636deee1ab7000000000000000000000000000000000000000000000000000036db66ee6d40000000000000000000000000000000000000000000000000000036db64ea4d00
  | 0, 5 => 0x924991192bf000000000000000000000000000000000000000000000000000009edb911f7ff00000000000000000000000000000000000000000000000000000924991192bf000000000000000000000000000000000000000000000000000009249911801800000000000000000000000000000000000000000000000000000924981102b300000000000000000000000000000000000000000000000000000924981002920000000000000000000000000000000000000000000000000000092498010231000000000000000000000000000000000000000000000000000009048111828a
  | 0, 6 => 0x1b5cf33faeeb00000000000000000000000000000000000000000000000000001b5c733fae6900000000000000000000000000000000000000000000000000001b10433f8808000000000000000000000000000000000000000000000000000036df76ef6f610000000000000000000000000000000000000000000000000000125c722f2e61000000000000000000000000000000000000000000000000000012fdfa2f7ff7000000000000000000000000000000000000000000000000000012dd722f6f610000000000000000000000000000000000000000000000000000125c722f2e61
  | 0, 7 => 0x2d1205f38808000000000000000000000000000000000000000000000000000036dfe6fe6fc2000000000000000000000000000000000000000000000000000024ffbcf27ff7000000000000000000000000000000000000000000000000000024bf9cf25fb70000000000000000000000000000000000000000000000000000249f84f24f8200000000000000000000000000000000000000000000000000001b7cfb3fbeff00000000000000000000000000000000000000000000000000001b7cfb3fae7900000000000000000000000000000000000000000000000000001b7cfa3f2ef3
  | 0, 8 => 0x36dff6ff6fe300000000000000000000000000000000000000000000000000003616d6ff0aa30000000000000000000000000000000000000000000000000000361246ff080000000000000000000000000000000000000000000000000000002dbf9df3dfbf00000000000000000000000000000000000000000000000000002dbf9df3cf9a00000000000000000000000000000000000000000000000000002dbf9cf34fb300000000000000000000000000000000000000000000000000002d9f95f3cfab00000000000000000000000000000000000000000000000000002d9f85f3cf8a
  | 0, 9 => 0x38edb75577e7000000000000000000000000000000000000000000000000000038e927447544000000000000000000000000000000000000000000000000000038e92744754400000000000000000000000000000000000000000000000000003fffffffffff00000000000000000000000000000000000000000000000000003ffff888001000000000000000000000000000000000000000000000000000003fdff7ffefeb00000000000000000000000000000000000000000000000000003f36dfff9abf00000000000000000000000000000000000000000000000000003f1247ff8808
  | 0, 10 => 0x3bfd777fff6d000000000000000000000000000000000000000000000000000039edbf55f55c000000000000000000000000000000000000000000000000000039edbf5577f7000000000000000000000000000000000000000000000000000039edbf5477d6000000000000000000000000000000000000000000000000000039edbf457775000000000000000000000000000000000000000000000000000039eda755f7ce000000000000000000000000000000000000000000000000000039ed3755f76d000000000000000000000000000000000000000000000000000039e92755f54c
  | 0, 11 => 0x3f36d888001000000000000000000000000000000000000000000000000000003f16d7ff8aab00000000000000000000000000000000000000000000000000003fdb67ffed4800000000000000000000000000000000000000000000000000003f1247ff880800000000000000000000000000000000000000000000000000003f1245fb880800000000000000000000000000000000000000000000000000003f1244fa080000000000000000000000000000000000000000000000000000003f1243bf880800000000000000000000000000000000000000000000000000003f1241998008
  | 0, 12 => 0x3fdff7ffefeb00000000000000000000000000000000000000000000000000003fbfdfffdfbf00000000000000000000000000000000000000000000000000003f9fc7ffcf8a00000000000000000000000000000000000000000000000000003f7effffbeff00000000000000000000000000000000000000000000000000003f5e77ffae6900000000000000000000000000000000000000000000000000003f36dfff9abf00000000000000000000000000000000000000000000000000003f36dfff8a3900000000000000000000000000000000000000000000000000003f36dbbf9abf
  | 0, 13 => 0x3ffffcc8411000000000000000000000000000000000000000000000000000003ffff988901c00000000000000000000000000000000000000000000000000003ffff888001000000000000000000000000000000000000000000000000000003ffff88877f700000000000000000000000000000000000000000000000000003ffff888655000000000000000000000000000000000000000000000000000003ffff888001000000000000000000000000000000000000000000000000000003fffffcc755400000000000000000000000000000000000000000000000000003ffb67ddf54c
  | 0, 14 => 0x3ffffbbfbeff00000000000000000000000000000000000000000000000000003ffffbbfae7900000000000000000000000000000000000000000000000000003ffffaaf2e7100000000000000000000000000000000000000000000000000003ffff99992bf00000000000000000000000000000000000000000000000000003ffff999823900000000000000000000000000000000000000000000000000003ffff999801800000000000000000000000000000000000000000000000000003ffff89902b300000000000000000000000000000000000000000000000000003ffffeee6d50
  | 0, 15 => 0x3fffffff9abf00000000000000000000000000000000000000000000000000003fffffff881800000000000000000000000000000000000000000000000000003fffffddf55c00000000000000000000000000000000000000000000000000003fffffffffff00000000000000000000000000000000000000000000000000003ffffeff6ff300000000000000000000000000000000000000000000000000003ffffdfbdfbf00000000000000000000000000000000000000000000000000003ffffdfbcf9a00000000000000000000000000000000000000000000000000003ffffcfa4f92
  | 1, 0 => 0x3fffffffcf9a00000000000000000000000000000000000000000000000000003fffffffae79
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 130 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 130 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 130 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 130 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 8 0) :: stateWiresD n (ids >>> 8)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 8 0) :: stateWiresS n (ids >>> 8)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 10 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 5 => 72
  | 6 => 657
  | 7 => 1742
  | 8 => 479
  | 9 => 21
  | _ => 0
def CH : Nat → Nat → Nat
  | 5, 0 => 0xb7d379b5b6e80d6ab3e09aabae4c4aefa5f932539f68d6e5997aaed29942b45598659ba98db6b9038d09c92d8a3e8d90854243ba80bab05d7fa858d67edd437e7e0e28c87d13b58479c9d27078ed079b7513e8cd724c9f05724ad67c706ed35c6f6f368a6872670365354f46635d18025cc9165d576788dd56daf89952b3b88e508b66b24fd941704e59a30b4a9dfd9747e474e246a2c3c444499a7042b779a33fead0103fd636b93da280be351014f6330d25c1306b4d2c2f80b9192f1fbfd926a687d42588d1671faea1241f88c0741809c6db147a830a1351c5460ffe0bef0f0b24fd0d14d8380b42f5b109b1822a091343dd0824bf5405880df905323e3c
  | 5, 1 => 0xf1763efede15ae65dd9d2f19ce50676ec0a10220bd85d069bb9956bcb99a397c
  | 6, 0 => 0xe1cb4fc0e19b75f0dd0a1c90d5677280d4ae8920d3591b80d1e5eea0cabde0a0ca8f48b0c871f230af0d8460a6c0c690a5dd90b0a5acade0a1efef009d11e2809a00a4f096e94380956f26709115a46089857ee087f4efd0870afac08697de0085a20c20841179d0829644c07e13e1d07bb8581079efbf7079ec839075388ef06f6939e067c7986067a383806322e480612708805ca702105b8649705a4e2af05880df9054f0a5e04af4c4e046952c204577db503e8aae20393ce3b0363eadf0342f57b02b5423d0285dcee01d29fcd01b39fc00177b476017005b600f6a84d00e3021600d7e88600d039c600c447de00bd0afe00bbc06900b294a7004eda24
  | 6, 1 => 0x1ee50c9c1e94ffdd1e06e3f41d600c9e1d533cd91d319dd51bd43a891ba9ade81b8129591b5e8eee1b289f481b263e021b1e8f421ae75a9a1ae2b9091ae1c6821adf32dc1a6f9aca1a0f2ada1a0dbb1919f7c2b719aec20d197c445219108315190a1b2718ab3555188a098e1873f32617ea453517d80f8717c1f8db173c6c161734bd5617016561169ab8ce166ab534161c81b315e64b2715a551d5154fe2f01538a62114e4822514e0d35f14e03b2014d3d5ff139d6ec1138dfb051356a1bd12ee29ce12aa3d87119fba6110edd13210aa310210a7db6c103814080f8898390f73afd90f6cbd440f5b77be0f124bee0ed506e70eb903040e9afcc10e5f4a88
  | 6, 2 => 0x3037bc2b3031bd6b302bd4842ff400272f9638f52f4d460d2f37b6b72ea307bb2e9da5162e7d2ba82e6b27ac2e4f0c7c2de1c60c2ddc521f2d84af372d1d24532c45359f2be3fc842b81626d2b736c8a2b3720452ab77fdf2aa7f5082a7f696e2a57a6db2a2f77ad29e0a5f929d9e0bd29bdda842986ccde28a4a83e2899c1c727d9de4a275dc420269dd81125f3241825dd3ce825d9debf25b7ff1b258843ee25758e502473f9f324649d8f23de44f823b5d9fe237a0e0c22ff1b2a22d6f43b22bad90b22b5ff3021e3c30121d36b4121398546211cf30c2102ffee20d8cb39207e77461fe2717f1fdf39191fbb085b1fb133ec1fa0bfc01f31a2321ee62c43
  | 6, 3 => 0x4688b604464d910745ecaa3545e914fa45d91ef145b3ba6a4558c85444de008544b9bf3844b3865943e2290143330dc842ee52eb42b779a3425d8ab841f0bd9f41dd05094166a3813f839b963e30959e3e26bb923df59e8a3cffec8d3cbee65d3c3ae0643c14e1143c0a8d833b6df8413b5816813a86104b39c050c0396f21b5390ea99e38ba07533805244f37d5860937809ff03779f0383761c3f337448926373b41c136bd7d743671a12b358f6bef357568583536fa9d34c71a3134a7feb13496001934456bf9335bf75432fe99e432fa2f9532aa0122328459a3326c2260326a919032048d4b32025cf831e420b93191ff7f314c8f71312ab2ec30a67ff8
  | 6, 4 => 0x5dc92b4d5db7f7b65d8c42c05d71535d5bc921255b7488635b1b10095b05b59059d509d859a6e7a458db7a2357a8f5b0575c33c05707220b56fbf48f56f84fa955febff455c23b7e55b91af4559c04495587168154fb57fa54addcc05469d1a953f2862353f2805153e5913153942bd0529a8d7a520cebb051ea9838516907d05161016650c755c150a4658b5093c90950899213506d2f505013977b4f1bb8244edce9e04e82865c4e29c7d14db70eda4d4559a54d2f24044cab24254c7b77174c6742094c30865f4c2c4d784c249eb84b8545404a75f5dc4a75e4464a0d3c2549eaddd449baef0348ddbb0a48d59e38486f7036485ed3b447992a174741e0b1
  | 6, 5 => 0x782963b877f1c5ac779b891b777cb77e775ef3e376d684c8764eace0761a16807601323675a5bb057592030a7573b11d74f5230274c572677404caec73b9b90972e7869d729c03867285764472462f9472157d2371f6935271a8424b70de2b656eec7d016e861e126e09c3cf6c407a466c3e88df6b9195906b7dedb66a8772f96a3b852c6a1e602969c5fee76926f71f68e42e3868716f4067de5e2e67aab8ca67a7b8ad6759339d66fdde0f66f142d3668c94da667b4a4f661528fe65b7c46d65389ed564e760a2647c796e64579de86446d59063cf9d8563496cf2633c95a7633b241c62cdb14a6218533460bfdce0606836f35fc3178d5dd111045dca4c07
  | 6, 6 => 0x8d1424d28cedacd18cd3a5008c17c5f68b5a4bd68a81f0ca898a64218941d63988813b10884bbd6a876f8b518755ef628744a6f8872b4b268675181f8665e7bc86651c0a85f7520185e097ab8588325a856c172a853dc35385353ca2852af29f8436e17f84200ce683e6b30c8380f13583345206830277f182f377b082eed990828343a28274a4cd82074cbe81b591e281a2cdcb816e6f5581351b14813018cc8109f8dd80f4c63780e02ad6805a333880181c2c7f9f74017ef965147ef4d80b7e21d4ac7e1d0e757d317be77c9bc0df7c2f9e497bae4c587b8db51e7b85fd8579e15a2879d5388879c7a1517996bf2e791c630d791205e278496b397829da41
  | 6, 7 => 0xa99bf0d0a97672a3a965ad4ba9066bd3a83a0c71a7e02138a6f5ccdea63809e4a621259fa5e719cfa5853147a52f323ba3c65a94a2f3a490a2b69e03a22de227a20a1b79a20769f0a1d961dfa1caad00a066105ca0156c74a005171c9eb8df3c9e820b8f9e7afbfc9e1efba79e18ee7a9e0e967f9e07fddc9de855ae9d6150a29d3efd2a9cec71d59ca5d9009c5f57449c3cd9109ba551609a1a9ee09961619898d5dc0198a19efa976b185996ced8529614e43394d1dceb948c00259470e3ab944972d693dbf10b937d18899357be1792d1c8ac928f126f92879af991d3336590e2f04490be3c9b908ef446908995dd8e7151b78def5d868d5b5a268d257af8
  | 6, 8 => 0xc441dda6c3c1c7d5c24f89c6c228c216c219efd3c0d13c78c0750f2cc055abb8bf4633debeb20894beae8066be4be64fbd8203c1bcff13e8bce33c38bcd62099bca2bc66bc0e36a8bbe6dd5cbbb787aabb843030b950c2ecb8e76ab4b83b34b4b7610a65b74795c1b6d8a086b6accc0db6aa3dffb48af682b39e38ccb33e067ab326e2eab3088cf5b2c83225b2b795a3b1d08fcbb1aef324b14d1a14b104327ab0e177f3b0c17e9db069addfafd87cd4af813213af7d917daf75e2bdaee17fe0ae88153cae87d801ae33dfceada9b6bead6936ecad64f2d1ad43e054acd9c01aacb13a4dacad57e2ac42677aac3108bfabaf30b1aae3998eaa881170aa4d3edb
  | 6, 9 => 0xf4af1138f4a310aef27bb735eed0b2d5ee49a450ec9f8dbaec484d69eba104aceb2171faea8c7e56e9736099e5bad58ce580cb8ae52741cae47c3806e3e8108be3af474de2d7e608e1faee85e1de3ec8e1151f08e0a341b5defb0a41dee687b4de903322de160a38ddfb04cddcba1b16dc4f5541dc47fd4ddbfe3c0cdbbce545db8cf674daaef95ad9adc4b4d8102e57d7ab2662d784431ad6a8c914d6558c3ed4e034e8d4db24c4d45ccefad343e014d1f57ef8d1912261cff8c303cf55fb46ced1f3fece6e2dd1cde805e0cce5a3c5ccbf28abcae0b10fc9a280f2c9880156c93ffe5cc8d1092fc823f470c815559bc781ff31c709a282c6a7786dc467b698
  | 6, 10 => 0xfef9abd2fe96caa2fe186c62fdf00cfdfd49d10afbaca4f4fb76c82ffb57dab3fab62d06f85a4a54f8547771f811ea51f7310bb0f72221caf6671af1f65f22a4f5049fde
  | 7, 0 => 0x651b5d5064cb80906117225060e91e7060e01a405ad2f34058f9a1705725c9f056b7b6b05169eb00509fa1f04e37e8404e075a704ccdfdc04bca65904aaa2b004824cd4046088880442bd8604427d3b042b899703f1b95203d31bcd03b4e9840375c6cf0355cd58034616b1033b05b5030a418d02f13a0a029bda2f0295a270028de01e0246bcc0024050db023e907d02363de2020b934d01eac28901a6e4da01a5e674019fd767019f361a019186980185b851016603570165a78a015fcb3e01551783014268c7012c73fe0124c53e00f9b8fb00f5a3d200ea38dd00c4d48b009aeaed0096839b009554410054141c00386e23002d875e0029bfef001a76cd
  | 7, 1 => 0xd49c4170d34394d0cf439bf0c97ff090c7bcab90c6ed2f30c498d8c0c2ad96d0c232aad0c1e8e5d0c03b9010be48af20bd3d3cb0bb8a2180bb6718b0ba77e000ba1b2440ba0f9160b8ad6cc0b420c200b34edde0b2179b20aee98b70ae34fac0ab8b2690aad79ad0aa03d900a7677f50a5e33fe0a53c4d60a1382ef09eb9e2109ea0c3209cc529509bb44da09a252ac09a18f54093e735609199978090dfc8408b46af10899ab53088c31c9086d870f0865d84f085c29ce0856ca260844bf83083fa81e07ca96c507c038b307a99a0b078f1e53078179cf073d42b70737882a07073daf06fb5c5206e8585f06dc6cc306cd9ad4068bc39d065dc92d06540181
  | 7, 2 => 0x1413d60813e90d2b13d5001c13bbd24e13a2becb1368a9861362ec4213346ed11317dd2b12ddb43412db4a7b12bb814412a8595d126ef838125d0b7e124d6d63124888761234695d1228cbf912245a68120061e011ddbdec11c1f92a11bd50f4118eca211187183a117804a41142fa411103719910ef472310d95ce110c52777109bbfbb109410fb108bef5710835d31104862a5102c960a1015aee71010f37c0ffdfe370fde41e30fb1a7760f9788b90f808c130f7093b80f56ffe60f53334a0f1a8f2b0f1986a90f13caca0ed4a4ff0e7e15130e5d94ed0e4ddd170e11a80d0de224890de1cc4b0dcd46f30db5a5fb0d9cbe430d92daa50d86abda0d570f57
  | 7, 3 => 0x19d2796319cd069919c7c79119ba301a19a917ce198916cb1980bc291966b800194727b519403fcf19399e181927b99a18ef4baf18a994bc189d69961891280c18834988185aec9118595dba184ab4571830634d18261f7817e7c6aa17e4d13d17d15ef517c5c22e17bf920f17bba65117b7e34f17b0da98179c6b231778be63177154d6175c2c7517357b561729918f172938d7171f64aa17057e3b16d77b9d16d21d8816c91dcd168bc85d16741ef1165a143316573f0016256de51612f341160c7aef15c40ccc15ba6e63159e488915974ea7155cba4e154b395214e9d80214e907ff14e2d7e014db292014c37a0914c0d43c1480f23a146b28301415063f
  | 7, 4 => 0x2064873a2062e284205b0a2a204fb0ae203e530f1fed21a51fecb1011fdbe3151fb72b911fac1ffd1fabf81c1fa939b01f7455d61f6d41b71f129f391f0c9a181f0286b71efe2b8f1edd0b6f1edb86661ed5cf831ed55caf1e9a7a0a1e8f0e011e8c48a51e7359ed1e5ad6651e0576261de45f961d9e38471d9945271d98a19b1d825b1b1d6198e01d4653921d2a81d31d1067761d07cbc61ceeb9671ccc0bd21caf33921ca481c01ca0b1831c5d76581c5377201c193f401bf5be811baf8e761b933b9e1b62a5db1b61a0cd1b6003b71b5233871b25678b1affcd851ab858541a90e4691a8148131a7c026f1a4b36dd1a1cf34419fc1ed919f6ee7f19e220af
  | 7, 5 => 0x2724c80b2707a0fd26f9178926f168c926eeeb7b26d16b4626d0c80326beaf6f26bb2fef26b48b0426ae455b26ad119126ac92fa26aabd3626410c6c262a32f4260ba302260a164f25e4685525d992dc25c3013925a9c205258a599a253ef9ad250b3e6a250aba5724f9ef9824f9d1c424f59d0824f27cee24df459a24cbf97124ae713a24a1966824429b14243971d5241c5d5a2414ae9a24140a41240b208923fade1623d165c223c2095e2341f140232c6add22f578d322ec6a8722be9cac22baad2d228054752256936121e6cbde21d562ba21c636b821a5f96821997fae2194ff3b2177d42821639b7e214f0d11214d3bd72145ca59213819c920eb96a2
  | 7, 6 => 0x2dcb18752dc8937b2dc874d12dc5ce1f2dac784b2d7296ec2d70ced82d2567eb2d11d26b2d014b912cf3c0ef2cc795ae2cbf60152c97836b2c7c27652c64074d2c611b6b2c58dac22c119b4b2bebe72d2bc2b7902bbea46f2badab652b87620c2b811d732b52c4ba2b27b74c2b13e5c22af3c5ea2ae913f02aa00b9d2a8ae2d82a6540552a2491622a1706c029f9c57229dcd53d29d4eeb92992b93229922d3f29874d1e296b38aa295678be29428e4b292576e329208bf7290cb43028d6af5928bc54b328b96dc828b64d0b28a4ff9e28819c6b284b54a1284514cc283a30c92817589128170bbb27fd4ed027e6305227d25737279f070c279976182794720b
  | 7, 7 => 0x35239d6d350ff6a135009d3534ecd7be34ceb8d13499662c3466ebee345ddff53453b6c53451cc6e344da13933dbf576339be8303398d1853389f6ab335ce2943327d92c32f1ebf132eb626b32e16b8932def36c32d045d132cae7bc32b9632332a889b1329f13283264f194326007a83252e2e0321d7eb2320f9fd331ffed8331f43daa31b9d9ef3177ea883157996e31389c993130272031242ee9311853993117236230ff3b4730ddf4913096bd90306aaa7f301b2a85301052cd30010ce22ff7be3e2ff5d29c2fd3b15e2f98f4ff2f7e6ae62f6e640f2f2d39052f1d2f5b2f0d47d92ef3a4c42ef04e032eba05a82e9b5e9e2e8a65942e5125f22e3ae349
  | 7, 8 => 0x3cda06bb3cbde0b03c9f3cdf3c7a7c2d3c78ad2f3c6b32503c407f353c1c522c3bf4ea113bbe60cd3b6f72873b5dab7f3b49e9823b40a23f3b3af5c13b34c0e23b3477b43b281c1b3b13a8a83b0f10343b0c2ead3b08dcd23b05d6f73acedf3f3acb64103a97b4d03a87d8353a64e63a3a5b11913a3c419a3a2d4b643a03d4b139e37c1a39c282b0396f572d394f14203926b9f839234c0738e8b0de38e1a69e38c6876638c5f53938bbb1643864ee273856408c383a0cba381fcf143812097437596ec3375091353743a61d373fb95f3732f1d836e51aae3644f7dd361d50e73618de163601d28435ed045035cf0cfa35a0b6f0359f67e735974020358833f8
  | 7, 9 => 0x44e2863b44e13ffc44df840d44d46f7844578d0c441caf3c43eb0c0643df582343d7832c43b837ee4397d14043806d9c435a25624357732f434d2f5a434ac032433f660a4325dcc4431f7df742f2e46442e7b5af42d61d4c42bb11ee42b779a3428dbbfe4288da78427c5b8942794e1f425bc8a4418c685a418c5819417515864149254d410d769640fe085a40f404f840a83783406dd97a4062ec42404b3013403af74d4022ca1740177a0b3fdba9f43fd3ef6d3fc11baf3fb101cf3f8ddd6d3f8054793f6aee9b3f5789763f39b76f3f291ad13f15457d3ef9b7083e444aad3e3a3ac43dc293cd3dbf16b33d6d79af3d2562093d0b3b903ce460d63ce437ac
  | 7, 10 => 0x4b6e21e64b5e75fd4b50406a4b2d583b4b25a97b4b1cd1974aee73794a9428d24a8b09ee4a8a40314a8291714a55e6434a3f5f3c4a1935bc4a041b5149fc6c9149f3d2f349c3e2a949bb2fc3498effba498947804987e82849823f86496f92e0496885e54939f5304931ec38492acee949185ad249148db048f0ff0048a6ffde48603f7248360ca148287520480eeebd47ff7ab347f536de47d8b1d947ba59f747b76ea3478f9960476a5be94727debc471a541a471718c4470caff646f568e246f43ede46ec901e46de759446c93225469949b54667f2b7466764c54612bc4045f5ff6d45f28fa645f126ed45d91ef1457c8acd456daacd451b4b374519cf8c
  | 7, 11 => 0x53514afd533777b2531108a652fb824352dbe80452adfd1052a2b5415291c96d528ce019526177285257aedf524bd7ed524a17a8523dc21151d2062b51bb2a0f51954e1e519006da51761d5f5136a9a3512f757250eca9cc50ea111b50dc89c550d612eb50d0d1e75059633d502b2686501ec8144fffcd0a4fff2dd54ff820184fc886e34fc559f74fa260824f84bcf94f1cce664f0494734ea474154e8c86004e6901224e5713ad4e5372144e3b68614e37dfb54e2cfa994e2566f84e0a16a24d8cd6aa4d84259f4d2ff4d14d2abf2e4cfd734b4ced469a4cea11834ce115d74cd6bec54c23a9c54bf147df4bf088724bb67d884bb222f34ba1260e4b76c090
  | 7, 12 => 0x59b8153059a3041859a1fc3b59a0c2fc597bfa895936765a592f019858d7b5fd58aa0f00589a10735875705b580f558b5808a35357a38ac0578e67bf578969f3575675b3574ab38e574995685744b4ce573f8ef45727b7f4571462ac5707fb6756f411bd56f3df7156c5d00a568ff7f1568d8c7e568d4d92567043f55659605e5621d24155f9c36e55e93b6a55df5df8559d3a725592189f557f4cd9551f842c55122fc955100dac55067f9c54de0ffe54d391cb54c66e2d54bebf6d54b8020854b47b9854afff1c54acafc454a2686254a00c235497bd3654927f42546b222054324e1553edfa8d53d248aa53ca920853c3fb8e538c2b2c537b088b5372efcc
  | 7, 13 => 0x62a75e3062515d5962346637622beca5621d1ce66212b35a620aa77261de9b7b61cf8f7361a45f8b6114156b6108511860f47f6c60d0e7fb60afae3b609b7685604693fd6042b36460370683602e455b601d48af601579705fbac6fd5f878d095f18482b5f03cb625ef408b65ee200285edbff035ec5fd9a5e56e6485e5492d85e441ef45e3f186a5e22a7545e0e53495dfe16575debf6475de083ce5dd41be55dd08b735d6dd96d5d66399c5d65f9355d5fdc975d53729c5cde0cce5c4918f65c33c1815c0bbbc75bea2b975bccb9a15b6fefcf5b6b6fdf5b5034d95b1f7a795aa2af7a5a9f5dfd5a8322685a6fa4e45a6beea559fcbebe59f4348059f11cdb
  | 7, 14 => 0x6bba04806bb263836ba44eea6b9d976b6b846d316b5a61076b3934176b0d63fc6afc1fc26ae5c9b86ac5c8b56a41599e6a02e0d669da0c1f69b0c44b69900de6693c91ca6909bb466909578d68b5704d68959ecc688d1b55682efe6168201ef168090f8967eee67a67e4f09267d9415267c436006771e1d8675e86876733942566e5ae6b66e365b266c97e4e663dd114663bc188661f8dfe6617db0a660e2ed065fd862665d8b61e65b3f9f7658867f165524fc665438d016532bf64650aa1d364df0e0764b8ff5c646b21fb643ac406643a3fff642e54a06413866e6407b8f163ed974863e50b476387900b6346def66332600f6320cbf762fa02de62d73fc8
  | 7, 15 => 0x7626fba57584e5a57554e38675516084754591087512a2e574d3dfd174d08031746a0e0a746143e5746114027444601073ea5b6e73e9209c73d647297393454b73823427734eaa0d73437dc273251f9b72d7a0b572b28339728270b4727dbd767264096871ffefc671e2e21371b7c8f271a6de3f71a2624171442cec70f147e770e34a0670d6da3270a579f870656d63701838507015ade170120e997005f1236fb93c616f71e1b36f4de5166f43bf1e6f410f6b6f13e0ff6ecfcc7c6ec28c856ec13cc56e16b7eb6df00ee76dec12c46db030c46d748c516d72ad596d65318d6d3b7e216cbe1d396c9c25686c8cf8166c85f2fa6c7eacb26bd670bc6bcccd37
  | 7, 16 => 0x7ef20d5d7ed1cb467eaf48d67e7a0a4c7e704a887e5243da7e4b58517e31a93f7e0b20667e05acff7e0371a67dfc11ff7dd765af7dbf1e687da0a7537d8e4bce7d2a63907d2933597cf889057cea112d7c9e1f737c4faf817c4bfba17c0718bc7bf0b2df7be9041f7bd28ea77ba3c0797b665f577b1f57d07b03a1367aebe8fd7ae369547a7f40357a36543c79717a8d7963a5dd795acc8c78d1319678ab3581787617447847c1c277cf974077ad688677a6d70877a5fcd47753784a7746c83977231e6a7705d5e176fcecf676f0de3376e32c7a76b871ac768e81ea768decfb76863e3b7677504c766c84577668611b76607b8d764692e67643e1797633f097
  | 7, 17 => 0x894ebb5e893fe42c8934bc8a892f9eb888e7cff088d9be1688bd66ca88b5b0dd88b1c0eb882f0c8f882be4e18826fc3987f03d1a87b2ceb48756c6388730fd4687062e3086d3f20a869d478d8680741c8672012f865ca3e48643875e864102a8863f5b5b85f1f72685ec8b03859068af8575e3378542378385355bfe84fb0b2c84dc22b084885e6e847f1682847e8567847e77b1844c644983c4aef4838f94ca8323a63b830562c282fee33982cfc52182bd697582b3ae80827efabc82585f9481b726b381b49c60818ddd4e814d04b781303d8c811d6b4b80e817d780b2a53b809286e38069eaef805e0fe9805c90737fd70efe7f4590c97f172bf77f0df4cc
  | 7, 18 => 0x92904ad8928df76892734505920a759491ec7e3e919a80f891889d86917adf6f916bb6609147ad6a91309f349117715e90f610e690c7888690bd06639049058a8fec60158fe490d68fa972eb8f85be0e8f810ad08f80fc978f7b76b18f76ecae8f6057d08f5f73c98f3f1a208ee425888ec635f58eb599738eac49d78e9fcbf58e5d90ed8e1426838de04c348dd3b20b8dce939b8dacf6f48d52fc878d4595e98d18fb3b8cfa91f68cd766ed8caed4eb8ca456c68c73f3678c3110cf8bd322518bc48a1f8b7531c58b6aabe78b4458918b3c89528b01d81f8afc87408abb56b98aafa50e8aa701598aa3b04f8a59f2ae8a2917998a0b34fc89f27f8489e77a5d
  | 7, 19 => 0x9c625b659c01232b9be41d5a9bd769ee9bccaadf9b9023199b8101a69b6512559b0094939ae710529ae5da449aa07b839a6914bc9a3af0e199f128fd99eaf18f99be6db899440663993dc7cd992c679099004fbf98f4ca5a98f4208d98e97715988d75f4984961e09823da6497ef365797d41f8597a9fca097a4a4a197a00225979939bb97885ff9977488ac96f8e2cf96e560fb969aeb72965ae5939608f40395e5600c95d4c56f95d27d4095a0aa07956ca7b1954d79fb951cbb3294e8477894e56e8494de200194d4832a94aba5ca942a4f209405ef3093f42b8d93afb0459349a86693342c27931ceaaf931be89e93064ed592fea01592f99b5492c91a44
  | 7, 20 => 0xa649b5c6a636a700a6332d68a62f92f3a5f8bd8ca5ed4e39a5d7b751a5b66d6ea57519cca56effffa514615ea4eede4aa4647cd9a43fb431a3c1ab4ba3ad5187a39ec2eea3978b47a3744415a34d458fa34c1558a2cd8bc3a2a4712ea29245d0a284b47ea26534afa2501c7ba2487bd3a1feca93a1f16defa1878b6fa17bdb96a170cb80a16e9e40a16a86e7a12818cfa0c208bfa0a6ac70a0a52996a0566735a0363e9fa0219339a0092fe0a008b01c9f885efe9f7298a79f6282eb9f4a44a19f363d879f3584529f1c706f9ee2f8659ec0d7899eba48c59e73871f9e3a12a29e1370af9dff764d9de5cf519de416229d45ceeb9d2d3a5c9d0504429c9b27e7
  | 7, 21 => 0xb2d110c1b26b0dcfb250c755b21262bbb20f961db1976043b1522b5ab110e951b0de38b8b0a47233b09815e0b0619e49b047d02fb0377981b0231954afc719aeafc49eb7afa1d792af80d0deaf79b774af76925faf0c12d5aed94acbae5e2b50adf1a5e6ade543d0adcdd0feacc6a2bbaca416afac4853ecac41cfbeac38c2aaac1d3e4eac0ac3b1abc73af8abb996c5ab3f45e1ab3e2661ab193334ab12b296aaf9c10baaacc2cbaa99e01daa5550f9aa26b057a9f400e1a9e2c91da9d69768a99868aba994b72fa8f95c9fa8e78fc4a8a73885a893279da88166b8a827e4dca7e69d5ca7b5ef13a7977840a75d4008a71e49bea6bc62c7a6a209e6a656ba0b
  | 7, 22 => 0xc2425c6bc22bf79cc2138c1cc1f2c1fcc1e22be2c0e5efc8c00c7e66bff5be0ebfcbcf73bf98043bbefa2055beb33ceebe71eb9abe51e5eebe4ba155bde1cfb5bdce499fbd9a54e7bd2fc437bd20e303bcbbca35bc398ae1bc002835bbe49247bb80d0edbb5b4d1fbb44492bbb02c3a7bad03517bab9a1bdba9cdb19ba7a222cba460977ba0b356ab9fe2647b92930d4b9218214b91d4ce9b84d5911b7ea5dacb7dce78eb75820b1b71329c5b6cade13b6c50266b6be7634b69c41a7b66f714eb62fb4eab5f6eebfb5c04ca8b584491ab5446adbb5378037b4c78044b44008a2b432738eb413f1b2b38e0f43b36706acb35f854ab322ff62b3152a51b308d6f1
  | 7, 23 => 0xcf01a125ce745571ce73253ace1436abcd772c5dcd25b609ccb4b64fcc9196c9cc82dea7cc375d6acbaeeccfcba7c9c6cb67cfd6cb6178aacb3988b3cb2f7209cae6a019ca88eebaca5d4d69ca48fbdaca0e29ffc9b0660ac996b3b6c993c7a7c93c7368c8bf6cefc8465139c80b3ca5c8038de5c7c2f025c7ac8334c7ac348bc749e5c4c72863d7c70b2d3cc682e025c63e6ab8c637c9f1c61f7a8bc5d1834fc59d6c30c595198ec52f7576c4f7a12bc4f0f67cc4e635f6c4cfc905c4b9fc07c496691ec4949487c4789a6bc4745ea1c4232d1ac406f821c3e2d77bc3e1a744c3b4db41c34fd073c32e9198c30e22efc2e5ae67c2dde247c2a091e1c26131de
  | 7, 24 => 0xdccf1ccddca75dd1dc05489adbe3b343db7ed8a7daea6243dac7a96adab03a9fda68f783da5cf34eda4ab022da446b89da411fa3d9caa3a2d9bf06ebd9b71400d9288e6bd920e647d906f914d8e7dfa1d89de169d7b99f14d7ab2662d7799b21d76d9a26d6a5bda7d67f4dd9d673d0cad65cc42ed6382f23d612c66fd60b2572d5c0efffd5bc659fd5b2f80dd568ff65d4c1c33fd3f10f9fd31c5cf5d31b2cbed317dc6dd3039b18d2d1a5eed2cc3816d2b422bed282c284d277a55ad26d319fd2290b9fd221ba3ed21f33e1d1a278a6d1399e4dd1145e1bd1145570d0cf7350d027ba97d00c244bcfca0951cfa1a4c1cf8a4768cf7d9acacf402390cf0554ed
  | 7, 25 => 0xeaf7f023ead30ab7eac92227ea88b923e972b137e967135fe8f0997ae8623c33e8047120e7abfef4e75d0324e74db9f1e7283c3de6971501e65bdcdbe5c83741e5c2ba49e56d3923e5499e93e49c8a0de4858affe4589a88e45040b6e44891f6e43f1b6de3e1419be3cc7821e3a70da7e303f770e2eb09aae2d77514e2d732e2e2aad18ce29f438ce298b8f8e26a8d37e232c2d0e17be059e1283faae11dfea1e1151f08e10a457be0f77e7be0ef862ee0ad501ee08a1579dffa78b3dfe22038dfdba1afdfda7178dfbea839dfafa89bdf988c1edf7e61aedf6d6743df66edf2df45a9c5dee6275bdede789bdedb2a3bdea3b271de87e0c6dd5eacb4dcf90b68
  | 7, 26 => 0xfd7e81a8fd177528fcf048affcdeef09fc465d48fc3cf275fbe1c5f5fbc067ddfb83ad54fafc002efab495f5faa4aaacfa0230e1f8b72109f83a440bf7c55aa5f7b6a164f72a0023f71746d7f6e3f0ecf6bdecc7f6875a6cf6535463f63c8b9cf61da697f60e2b60f5c486c0f5b9b417f5b78cf4f5813bd0f3d60f87f3bffcabf3a1e699f33384e5f3165413f3041da1f2854adff1e2cc0df1c51099f105951df0886534f0132cb6eff6faafefefa548efd4f348ef9a6d96ef94b1afef2e0803ef013f34eed63fa9ee1a8472edd2c0aaeda7101fed56b179ecbba0bdecb660fdec0c1396ec08a247ec04ee7febbcb677eba5c6a6eb9a6ef5eb6a39b5eb628af5
  | 7, 27 => 0xfffb2919fff37a59ffee5704ff9fd7dbff6dda91ff61dc1fff4cb230ff2dade8ff2325baff0db492fef288ebfecffd16fdd723f5fd80c814
  | 8, 0 => 0x1979f417196672e11881f68618787ffd181aa94117a82026175a929b173d5c0016d8a81c1662ea0a15f86a801561a43a1528ba3c14e6b4ae13b5da6d131bfefa11ed84b711d748061198114410c280c5103ead2a0ff073950fc22fb60f8b2a5f0f60b9f30f5c5cfb0f3badb20ea68d810e8414b20e7dd0190df078900d9cbe430d61f2fb0cc7aa850c867e660c1a79410bd753a90bb2ffb10b989d440b41c7720acf09dd0ab8b26f0a9628be0a172c4909f5ca2f09ee1b6f0878675807d82e3c0754ea15075140fd06b07a030663442506291d8305c61dd60590310f054dc2ab040745c602e9d44b0291d00a023f103c0188fb4b00dd496a0086a50c00649915
  | 8, 1 => 0x2d90db782d770a592cf3c0ef2cf085992cb7e2692cae27f22c1543872baacaed2ba064522b0f56702af4104e2a7c85282a5175e42964176b292df8a1291abe562889888f2882e2b22775450f2774c4602727707326aa53c3265363bb264ea121262d41fb261c309d258a6ea42509c4b824cb7b29246ade96246554a62429651523a7fde62325e28c231857ea23038dd422d85c9a22543c1c2253e90221e9d24d204aaf2d2046aaad203cd04e1f9bef851f608b651f3d31db1ee4e3db1ec21db31ebb13731e739d441e3d0e221e08e1531d989e101d29fe0a1d094b741c53b96d1be563841b70b1901b52f3321a5d39541a4058c31a2bfa9c1a0ece7019deb3e2
  | 8, 2 => 0x4214fad141d622d341a8390641a4b5d6413ca69640db2d8b40bb28344079af63405c8f3d3f49363a3f086e6d3ee6de3d3e4ce77f3e1c8eb63dff89d03df1aaf13d6d0b963cedcf813c9f3cdf3c9d75a23c8fe41f3bf3e2703b76a7473a8b1a653a861c993a4766343a305add39de879e39a4dffb38ad846e3899ed18378f31e83732d33a3724f45b36c744ae36b6da92366fa27235f834e935d89aaa359f67e7359aee6d358e7c13357bcd57342cdee933d93c6b33ab0d08330961a632e7627a32c3d3da3294bf403264f1943243d5cd319b3e42317141fd31502d65315024ba31381b073129ad3f30ccd1eb302ca7772fc976f62eedfa852edbd6b52e46479b
  | 8, 3 => 0x5e90082e5d93d62e5d7bf2db5d2e415c5c50bd215b2acd595b0171135a437adf5a1dcce559f223e55992adb0584e132a56abec62567ee6cd5640306855df5df853b7a8b55314eaf6530ec13f52e996fb52acbe7d52942b725275541c523dc21151efbb60514f645450c9577f4f9b055d4e79bd534e5bae794de27c5e4dd111674dc27b5b4d2b306b4d17706a4cd8ba054bff26be4bf147df4bc969994b62f61f4a6707154a5928364a3f78dc499b08ca49226c8f49148db048fa38cc48b0ac9d484e6acf47f69d26475141bb46e1bded46e149a24696c818465e79d545f6b58445c07cca457c5ed143b9f0a34309ffd842b779a342815d8a4223bdb94215deda
  | 8, 4 => 0x7f97da8d7f5f0e0b7f27d8097ecd8d627e8559377dfd47397dad4e397d356db97d33ff317bf0d3337b4614867ab597257aa157477a85129f7a2bf43677f10ba277d135d077211a3f76f0de3376db0b2e766385db75c5ccea7540089874f2245d749b988673b9b9097341d2fd727daf3d72739f547260e48f71fb25a2714a8ba9711dc56670ffce1070cdf07470c4152b707cee8d706753916f6c29a26f3b46226e8018a76d45b13a6d2657c06bc490ee6b89f08a6b7c11ab6b6909ce6a0139de69d0a4b067425c616709aa616659a12a6449b75d6381479263669d9563353df46329b29363275f1561abfb7c6129ea2960f8c4a56001a2b65fd513de5ebcebc2
  | 8, 5 => 0xa77ce252a623790ea5e4c2a9a5103ec2a4dede88a309310ca2f4f716a141bf779ffd08839e58572e9de02fb29db654639da1794d9d61744b9d42bc1d9c27c3cd9ab47d5a99ed5e87996c23f4985a34f798553ede98411d81981b7e929710a4589603a49895a996be954d79fb944ede009351acbb92ef453392b08ece929a9c84927d8384927a567e925c0be491b98d129011f5828e7679718e27eed18dbfa66d8d1e3ac28ce77a638bbc73f08b8fda438b7e195e8b308e208a8bfac78a59f30f8a18c2888a0d10dd897643b68968a0cb886bb2a5881ad299869b759485520fcd8549f6d285210b038492c7cd83f048fb81bd8a2f804281918029ed027fb9fc42
  | 8, 6 => 0xdc240579da8008d2da26b2c9d7d8277ed69e993fd64007d5d62ad27fd5d13c99d58853add2da325bd229a3e5d17f337bcfe713d2cf0c769ccea2794ccdfcbe79cda803e7cd856bc9c9e65a89c8dd6445c7a3ca76c7466283c707ac1ec62ad07cc5d3e588c52f7576c41df566c30bd3fac110cb7dc1043454bfa41077bf75ede2bf01fb40bef5700abef1afedbee065e9beb2f988bd5c9ba0bcb2dff7bbec3344bbb69bf5b9782853b6edc245b5c9ec3db59a84ddb5195244b3feb3cab3f8265db2dc7687b22e7c90b210ca3fb12375bdb02268afb01ae1b0af01b67aace49a11ab962e79aabfa2cbaaa935daaa87c3f1aa38618da909e4c1a8d69abba7bb98b7
  | 8, 7 => 0xffa13466febf47eefe809189fd75d7f8fbe5e7c4fb7259a6fabc44b5fab495f5fa4dc81bf8b72109f5493ef0f20a7ebff109fd47eef3064ded5ae6a4ec164c1eeaf7dac4ea555bf2ea39f55de9f23fa9e9b38944e8b54ab1e7199440e606f433e5179d48e2f7dbbfe2f02cffe1ccafbce1283faae07b344ee04a17a1
  | 9, 0 => 0xfd16c8d5f33b5fd0dee29a6ad1efb8f3bad4da24b47be6218ab84b5d8a7994f87cea112d764e5f6161ca400842b779a33e277fff2efbd9642eedfa851e7359ed1729918f1606144c1561a43a1142fa4101bed059
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 5, 0 => 0x149104403037541a304c04000000000000009000000000000c54545304c0400000000000000d76016304c04000000000000000000000000000f0000000000009000000000000d000000000000c0000000000009000000000000f000000000000c000000000000c000000000000d000000000000d0000a544c030054545304c0400425855408140076016304c0400000000000000f0000000000009000000000000c000000000000c000000000000d6250551101400000000000000b039512148440000000544c02006448552041400
  | 5, 1 => 0x900951214844000000000000009000000000000c000000010d1060000000000009000000000000d000000000000b000000000000c52545304c0400000000000000d000000000000c76016304c0400000000000000d7541a304c0400000000000000c06951214844000094941504400000000000000e0014d2048030106949415044000010d53101300000000000000c0000000000007000000000000f0014d20480301000000000000c0014910440302000000000000d000000000000c000000000000d000000000000d
  | 5, 2 => 0xc0018950105302000000000000f03949415044007541a304c040052545304c0400000000000000f0001a544c0300
  | 6, 0 => 0x8000000000000600000405002020000040500201000000000000900000028022010015110440300000000000000d00000544c020000006544c03000000e028023000018021441300000000000000400151304c0300000000000000c0000000000004000000000000400006524c03000000053500201000000000000400000008c02000000000000004000000000000400016304c0300001895304030000000000000040000000000004001895404130000000000000040000001802201000000000000f0000000000004
  | 6, 1 => 0x121030000051500201000005448020100000544c0203000000000e10300180424813000000000000004000000480a2000000000000005000000000000400190304c0300001905244130000000000000090000052440203000000000a10100000000000040001a524c0300000000480e202000000000000f0018021441300000000000000c0000051500202000000000000b000000000000c00000000000040000e0280230000000000000050000053101202000000380220300000000000040000000000004000000000000b
  | 6, 2 => 0x25250030000012524403000000000000006000000000000900000000021030018d50109300000000000000c0000a01802300001895310130200000000851010000a514c030000000524c02030000054081201000000000000c00000524c020200000038062020010950508300000000000000e00002524c030000194048c130000000000000030000a018023000000000000005000000480e2000000000002102000000000000b000000000000900000038062030000000000009000000180220200000000000060018d50105300
  | 6, 3 => 0x10d10600191058c130000000000c01020014d53002300001855010d300000000000000c000000000000500000000121010000000000004000000000000b0000053500201000000000000400000000000040018c5244130000185540c03000018c52441300000000000000500145304c03000000004806202000000000e103001804350130000012514c0300000000480a20100000540412010000000006102001855010d300000005250020100000000000040000251508300000000000000c00000000000090014940500300
  | 6, 4 => 0x18c5244130000180324c13000019150085300001415000e30000191058c1300000000000000b0001a304c030000000540812010000e524c03000000000000004000000000000b000000000000400180415013000000000000005000000000000600145304c0300000000000000c00185521013000000e524c03000000051500201000000000000c00000000061010000000006103000000000210100000000000040010941485300000000000000f0000000000004000005350020100000304c0203000000000000c00151514c0300
  | 6, 5 => 0x480e2020000000002102000005350020100189500c53000000000000004000000000000c0000e54484300000000000000f000000000000c000000000000c00145304c0300000000000000c000004050020100006524c0300000000000000500000000000040019152041300000000000000f0000003802200000000000000f0000000000003000000000000f0000000000009000000000000400000000000050018c5448130000000000000040000000000004001094148530000191500c930000000028022000000000000004
  | 6, 6 => 0x524c02000000000000005000000000000400000000000090000004802203000005408120100000304c0203000000000000f00000000000040000e02806300000000000000400000304c0203000000000000400000000000090001a524c0300000000000000f000000000000c000004050020100000000000040018c54441300000025244030000002544c030000006524c030000000000000010000000000009000000000000d000000480220100000000000090000000000004000000000000c000000000000d0000000000004
  | 6, 7 => 0x70000000000007000000000000500189540c130200000524c020000000000000040018d500853000000040500201000000000000f000000000000500000000000040000000000001000000000000f0000000000000000000000000500000544c0200000005250020200000000061030000000000004000000000000200149304c0300000000000000c000000000000d000000000000d00191500c530000194048c1300000000000000b000000000000b0000010440203000000000000400012514c03000001a524c0300
  | 6, 8 => 0x18d50085300000000000000100000000000050000000000005000000000000c00000524c020300000028c020000000028062010018041501300000000000000f0000010440202000000000000900000000000040014d5300230000000544c0203000000000000400000540c120000000038022020000000000004000000000000400000000000050000000000004000120380230000151514c030000149304c030000149304c03000001a544c0300000000000000c000000000000e000000000000e000120280230000151514c0300
  | 6, 9 => 0xa0000000006101000c5530413000000a534403000000000000005000000000000400189500c530000002544c03000000000000005000000280220100000000000090018c524413000018032481300000000480a2010000040500201000000000000900000514c0202001415000e30000002514c03000010d5050c3000001a304c0300000025448030000191500c9300000000000000c00000000000040000000002101000000000000400000540412010000004802201000000000000e0000000000004000000000000d
  | 6, 10 => 0x544c02000000e028063000010d531013000000e51508300000000000000d0000e52500300000000000000400012028023000000002806201000000000e103001802148130000000000000040000e02806300000000000000900000000000040000000002101000000000000400012514c03000000000006103000000000000f000000000000500145304c03000000000000000000000000000d00000018022010018c5444130000000535002010000a304c0300000000000000300189500c530000002544c030000000514c0203
  | 6, 11 => 0x53500202000000000000c00190304c0300000000000a101000000000000c0000000000004000000000000c000000000000400000000000060000000000005000000480a20100000524c0202000000000000d00000000121000001a544c030000000540c120000189501053000000002802201000000000000400000314c420200000000121010000000000007000000000000c000000010010200000000000020000000040103000000000000a00000000000020019150085300000000000000900191058c13000001203802300
  | 6, 12 => 0x1803248130000000544c0200000000000000d00194048c13000000052500202000000000e10200180314c13000018d500853000000a544c0300000000000000400002514c03000000054440201000000000000d00000304c020000000515002010000000000004000000000000e000005408120100000000c910f000000000000e0019153040300000000000000c00000000c010000000304c0203000000380a200000000000000c00000000000030000000000004000000000000d000065250030000145304c0300000c9504c8300
  | 6, 13 => 0x149514c0300000005444020200016304c030000180434c1300000000000000400000028062000000000000009000000000000f0000000000006000000000000500000000000040000000000005000000380620200180324813000000000000005000000000000d00000544402020000000000004000000480620300002514c0300000000000000c000000000000d000000000000400000000000040000e52440300000000000000d0000e544c030000000000000050000000006103000005244020100000000000060018d50105300
  | 6, 14 => 0x400180214813000000000000004001094148530000000524c02020000052440202000000000000f00000540c1200000120380a3000018c52441300000000000000900085504843000000000000004000000000000c0000053500201000000000000c000000010d106000000000000d000005244020100000000000040001202802300000000000000400000530412020000000000004000000480220200000000021000000a304c0300000000010d10600109414853000000000000004000c5530413000000000000004
  | 6, 15 => 0xb00012028063000000a544c03000000000000004000000000000400000501052020000e514c03000000e544803000000004806202000000000000c000000000000e00000000121010018c54441300000000000000d001895010530000000524402020000000000005000000010d10600000018022030000000000007000000000000c0000000012103000000000000c0000000000007000000000000f00000000000050000000000004001804144130000189501053000010d531013000001203802300000000000000e
  | 6, 16 => 0xa1010000000002103000005304120200000000000090000a53500300000000480a201001494150430000180314c1300000000000000900000028022010000000000004000000000000400000000000010000000000004000000000000400000000000040000000000005000000000000d0000010440201000000000000c000000000000c0014910440300000000000000d0019150085300000000000000500000405002010000e544c03000000a544c0300000000000a101000000480a20100012514c03000000000000005
  | 6, 17 => 0x1895010d300000000000000f00000028062010018d5008530000000018022020000000012103000000000000f000000000000b000000000000600000514c020200000104402010000004802200000000000000c000000010d10600149514c0300000000000000600016304c0300000000000210300180434c1300000005310120300000028062010000053041202000120380a30000149514c030000000304c02000000e544c0300000065448030000000000401010000000012103000000010010100000048022010000000000009
  | 6, 18 => 0x151304c03000000000000004000000000000300000304c020200000544c02000000053480201000000000000e00012304c03000000e02802300000005350020100000525002010000001802203000000000000d00000544c020200151304c0300000000000000f000000000000d000000010d1060018041441300000000000000d000000000000500000544c02000000000000004000120280630000180414413000000000002103001803248130000000544c0200000000000000600000534802010000000000005000000000000c
  | 6, 19 => 0x12028063000000000000005000000000000c001804350130000000304c02000000053500201000120380a300000000000000d00151214843000000000000004000000000000400000048c02000000a018023000000000000009000000000000f00000514c020200189501053000000053440202000000000e10000000000000060001a204803000010d53101300000000480220200180324813000018d50105300000000000000e0000254484300000000000000f00000534402020000000000004000000000000600151304c0300
  | 6, 20 => 0x60010941485300000000380220200194048c13000001a544c030000000544c02000019150085300000000000000400191058c130000000544c020200151304c0300000000000000d0000053101200000000000000c00012304c030000000000000070000000000006
  | 7, 0 => 0x21020000053081200000004248520000000414852000000000002102000000480220300000544412000000000000001000000000000900000000000070000000002101000000000210200000000851000000001802203000000000000b000000380a20000000008c92000000003802200000000000000f000000000000f00000018c920000000505042000000000002102000000000e10200000000000090000000100101000000000000400000058c020000000524c0200000000280220000000000121030000000000004
  | 7, 1 => 0x2102000000480220000000544c0200000000000000a0000004802202000000480e20000000001001010000000000005000000088520000000000811000000000006102000000000e10200000524c0200000000284120000000000000000000000000006000000000000c000000280220100000038022030000000006101000000000000f00000525002000000042505200000000000000400000544c1200000000000210200000544c0200000005040e2000000003802200000000000000c00000000000000000000000009
  | 7, 2 => 0x10510100000000000040000000000009000000010510100000000811010000000000003000000380a200000000000000000000008c12000000000006102000000284120000000000121010000004802201000000000000b0000000000000000000000a10000000000000050000001901200000000000e102000000384120000000000c0103000000290d200000000480220100000000000060000001802202000000000000400000424852000000000000003000005250c200000000000000b00000001011010000000000005
  | 7, 3 => 0x12102000000284120000000058c120000000000000050000000000004000000000000f00000059092000000000006101000000180220100000048c12000000000000006000000000000400000000c510200000524c0203000000000000200000500c520000000000000020000000006102000000000000100000544c0200000000000a101000000000e100000000000000100000544c520000000514022000000001802202000000000e1020000000012103000000390d200000000000000200000008852000000000012100
  | 7, 4 => 0x61010000001802201000000000a10000000048c920000000058c1200000004148520000000000000010000003841200000005140e20000000304c02020000000002102000000000000600000000021010000001802200000000000000300000000000030000000105102000000010d103000005140220000000524c02000000000002100000000000000b00000000000070000000012101000000000000500000000000000000000081101000000010410100000520022000000000000002000000000000f0000003806200
  | 7, 5 => 0x544c0200000000000000400000434c120000000514022000000003841200000000000e100000000000e102000000001210200000544022000000002802201000000000000b00000038062000000004802200000000000000400000000000000000000041101000000000000600000544842000000000000005000000000e102000000280620000000544c0203000000000000e00000008c020000000058412000000052402200000000001210300000000c810000000524c020000000544c1200000005000e200000005000e200
  | 7, 6 => 0x811010000003885200000000000000c000000010010000000000c4103000000000000900000000000050000000012103000000000210100000048022020000000002101000005350020100000000411020000000000002000000000000e000000010c103000000380a20000000434852000000004802201000000000000300000544c1200000000000000500000000c1103000000000e1030000002802200000000000a1010000002802201000005300220000000000021010000000105101000005000e2000000053402200
  | 7, 7 => 0xc410200000514c0200000000290120000000028062000000004802200000000000210200000048062030000021481200000000000000f000000000000e000000000e10300000524c020000000534852000000000000006000000000000600000058c520000000000c01020000000100101000002148120000000000000060000050109200000005140220000000000000030000000002102000000000000400000038022000000000012101000000000000500000048022010000000000002000000000a1010000000000004
  | 7, 8 => 0x6000000000000900000514c02020000000000007000000000a10000000000411030000000000002000005140220000000000000050000003901200000005140a200000000480e2030000053041200000000000000c00000000c1103000000000a1010000000081101000000000000400000530022000000000000009000000000000600000000000040000000000006000000000000b0000052412200000000000000b00000001051030000052500201000000010510100000000000050000000000005000000000000a
  | 7, 9 => 0x5000a200000000000000400000000c41020000002802200000005040e200000000000e100000000000610300000000000040000052440200000000000000200000544c02000000000000004000000290120000000544c0202000000000000b0000053041200000000000000000000000c0103000004250120000000000021030000000101101000000090920000000514c0203000000000000c0000000012101000000010c10000000000021000000000000002000000000000a00000000000090000000000004000000000000f
  | 7, 10 => 0x544c5200000000588120000000000000010000000000003000000290120000000028022000000000000004000000488120000000524412000000000000004000000000000b0000005909200000000380220000000000000040000053101200000000000000b00000000021000000000041101000000000000f000000000e102000000000000900000534812000000003802200000000000000e0000052500201000000000a1010000005901200000000000000b00000000851010000000000006000000010510200000048c0200
  | 7, 11 => 0x41441200000000000000300000039012000000003802200000000480e20000000000000000000050412200000000480220000000500c92000000000105102000000000e10300000028062000000021441200000005008520000000029052000000000000000000000590120000000000021010000000002100000000000a100000003144120000000425052000000000000003000000000000100000000000020000054441200000000000000700000000000030000002802200000000000000e00000028c52000000040500201
  | 7, 12 => 0x380a20000000000000090000000006103000000001210200000000000040000000002102000000004110300000000c110200000028c5200000000000000300000544c5200000000000210200000304c020000000514c020000000000c51030000054081201000000008010100000304c0200000000000e100000000000e102000000000000e00000000801010000004806201000000000610200000008c1200000000000a101000000010510300000001011010000003802200000000488120000000000121010000053101200
  | 7, 13 => 0x1210300000514c0200000005000e2000000003905200000000000000c0000004802200000000000210300000000000090000054441200000005140e200000005100e200000000000000200000008c1200000000000000f00000008c920000000038c52000000000000001000000000610200000000c010000000514c02000000000000009000000480a2000000000002102000000000e102000000388520000000500852000000052441200000000001210000000000121010000002905200000000000e1020000003901200
  | 7, 14 => 0x531092000000054441200000000000000000000039052000000000000002000000000000100000008c92000000000000006000000000000e000000000a100000000000000700000000000040000000000006000000000000f00000048022000000000000000000000488120000000038c5200000000008110100000001051030000040500201000000010110100000000021020000000006101000000380a200000000000000400000000021010000000000000000000480e200000000000000f00000514c02000000000000003
  | 7, 15 => 0x200000514c0200000000000000a00000000c0103000005000e2000000000000004000000000a100000000000e103000000000000c000005250020100000304c0200000000000e100000005040a20000000000851010000040500201000000000a1010000000000005000000010c10200000000000090000000006102000000000000b000000000210300000000021010000000000004000000290d200000000380a200000000380a2000000000000005000000000000c00000524c020000000525002010000000002102
  | 7, 16 => 0x4000000000a101000005344020000000000000010000000000007000000000000f000000380a200000000000a10100000058812000000000080101000000000000c0000000000005000000380220300000000061010000052441200000000000000400000304c0200000000290d200000000000e10000000000411010000000000009000000000000f000000001210300000514c02000000000081101000000000000500000000c010000000000000040000000000006000000280620000000000021010000000000009
  | 7, 17 => 0xa00000304c0200000005400e200000000380a200000000000000200000324c1200000000000e102000000000000d000000000e103000000001210100000058c1200000000001210300000000000090000000006102000000000000000000000000040000000085101000000000000b0000042481200000000000000100000038c52000000000000002000000280620000000000c0102000000000000b0000000000000000000000000400000000000090000053041202000000000e102000000390d200000000000a101
  | 7, 18 => 0x524c020000000504c420000000000061020000053101202000000000000e000000000000600000000000040000000000002000000001210200000514c020300000058c1200000000000e1030000004806200000002148120000000000061030000051402200000000000210100000000021010000000012101000000000000f000000000000f00000534022000000000000000000000480220000000000021010000000000004000000390d200000000000210100000000c0102000000010510300000008c02000000000081101
  | 7, 19 => 0x10000002806200000000000000300000001011020000042501200000000488120000000000000020000000085101000000000a10100000058c520000000008812000000021481200000000000000500000501092000000051402200000005344020000000530812000000000006101000000480e20000000000021030000003802200000000000000200000514c02000000000000000000000000e103000000000000100000514c02020000000000005000000000000700000008c02000000000101101000000590d200
  | 7, 20 => 0x58c5200000000000e1020000021481200000000480a20000000501092000000051402200000000000000e000000004110100000028022000000000000005000000000000400000000000090000003806203000000000a10100000000021000000042505200000000000000f000000000000f0000004806203000000000000100000304c02000000000002103000000380a200000000000000000000000000010000000002102000000010910100000524c0200000000000000600000000000000000000012102000005240e200
  | 7, 21 => 0x52500200000000000210100000028c120000000001011030000000002103000005440e20000000001011000000003802200000000008110100000415012000000000905200000000000000300000000c510200000524c02020000042501200000000090920000000000121010000000002103000000480e203000005344120000000028062000000000002102000000000000b00000544c0200000000000000400000000121020000000000003000000001210100000524c0200000000480a200000000000000400000314c1200
  | 7, 22 => 0x100101000000000e102000000380a200000000010d102000000000e10300000000021030000000909200000004144120000000059092000000000000004000000480a201000000390920000000524c020200000038c1200000000000000f000000001210200000000000000000004802200000000380a200000003144120000000544062000000053481200000000000000c0000000006102000000000000f0000051508200000000480e2000000000881200000002144120000000544c020000000001051020000002802200
  | 7, 23 => 0x4010100000514c020200000059092000000003802200000000001210100000514c0203000000380620300000038c920000000001011030000000000006000000000000c000004144120000000000000030000051002200000005000e20000000001051000000053481200000000001210100000000000010000000006101000000010010100000000000030000031441200000000000e100000000000000c000004250520000000000c5100000000000000500000028022000000053500201000000000a1010000000006101
  | 7, 24 => 0x300000000000020000000000009000000000e100000000480a201000003144120000000544c4200000000000000f0000000000001000004348520000000000021020000000012102000005308520000000000000040000000000004000000000000400000514022000000053109200000000480a200000000000000f000000590120000000544c0200000000000e10200000314c1200000000000210100000000121010000000000006000000000e10200000058c520000000304c0200000000000000b000000000e102
  | 7, 25 => 0x43485200000000000a101000000000000c000000000e102000000000e1020000000002101000000280220000000000121000000000000004000000000000600000000021010000000000000000000010d10200000544c0200000000000e102000000480e2000000000002103000000480e20200000535002010000000002102000000000e102000000000610300000028c1200000000280620000000000000000000041441200000000480a20100000544c12000000053485200000000380220000000434c12000000000100101
  | 7, 26 => 0x21000000041485200000000010d1000000000000002000000000a1010000053406200000000000a101000000001210300000028062000000000002102000000000000500000000c010200000048062010000000000007000000000a10000000000000060000000002102000000380220000000038062020000001802200000000000000c000000001210100000038852000000000041101000000000000600000000000030000002806201000000000000400000001051020000000006102000000000000f00000038c1200
  | 7, 27 => 0x5000000000000f00000434c120000000540c1200000005240e200000000000000000000000121010000000012103000000000000f00000000000040000000002102000000480a20000000001051020000000000005000000001210300000544c02000000000041102000000000000500000514c0200000000588120000000028c02000000000881200000000000e10000000524412000000003802200000000000000000000028062010000003885200000000190920000000001001030000000002101000000000000f
  | 7, 28 => 0x8110100000544c02000000000000002000000280620100000000121010000000000000000000480a20100000000000040000000012101000000000000900000038022030000000000005000000000000400000000000020000000002102000000000000400000514c020000000501052000000000000002000000000210300000314412000000054485200000000000610200000028022000000005881200000000480e2000000000006102000005244120000000018c9200000000000a10100000038c02000000001802203
  | 7, 29 => 0x12103000000001210100000000000000000000101102000000488120000000000000070000000002101000000480e2020000000002100000000480e200000000000e10200000000061020000000002102000000000000f000000010110300000000000010000000000007000000000000300000000021010000000000005000000588120000000531012000000000006102000005440e200000000480a200000005244120000000304c02000000000000003000005350020100000540c120200000000851010000052440200
  | 7, 30 => 0xb0000000002102000000280220000000524c0202000000000e10300000000000010000003909200000000380a200000003250520000000048c020000000048c52000000004881200000000380220300000534022000000004802200000000000000700000514c0200000005440220000000540c12000000000101101000000010010300000000000010000000000008000000000000e0000000006103000005050c200000000590d20000000304c0200000005240220000000514c0200000005040e2000000050109200
  | 7, 31 => 0x400000001051030000000002102000000380a2000000000108101000000000e100000000480e2000000000002100000000000a101000003250520000000544c0200000000000a100000000000000100000514c020000000544c02000000000000006000000380220000000534022000000003802202000000000e1030000051500201000005444120000000000000050000000000002000004148520000000000021010000000000004000000000000f00000000000010000000000004000000590d2000000000012101
  | 7, 32 => 0xc0103000000000e10200000000c010300000000c0103000000001210100000000000020000000000004000000480220000000314c1200000000000000c000000000000100000544c020200000514c0200000000000000600000000000040000000012101000000000000700000001011010000000000005000000000210000000515002010000002806201000000000e1020000043501200000000090d20000000028c1200000000000a10100000304c02000000053002200000005300a200000005440e2000000000000004
  | 7, 33 => 0x10d102000000480e200000000000000e000000480a200000000000000400000000411030000000002101000000000000f00000524c4200000000000000f00000038c120000000000021030000000000001000000001210300000000000050000000000004000000000000c0000000012101000000004010000000000c010200000000000010000000006102000000000e10000000000000010000000002101000000480a2000000000000004000000000610200000028c1200000000000000e000005440e200
  | 7, 34 => 0xa0000000000004000005310920000000000021020000000000008000000000000f000000000000c000000000000e00000048c92000000000000004000000000000f000000000000900000000000010000000000009000000008510100000000021030000000000008000005348520000000038c1200000000480e200000000000610300000000000050000053101200000000190920000000500c5200000000000e102000000000000e00000304c02000000053109200000000008510000000000021010000000012101
  | 7, 35 => 0xf00000000000020000054480200000000000000b0000000000009000005040e200000000000000c0000000012101000000008510100000544c02000000000000001000000010510100000000000000000000002103000000008110000000000000040000003802202000000001210100000000000040000000000004000000004010200000534852000000000000005000000000000c00000434c1200000000280620000000304c02020000000000005000000000e1020000000000006000000000000f0000000000003
  | 7, 36 => 0x1011010000000002103000000000a10100000001001010000053500200000000001210100000540c120000000058852000000000012101000000004010200000048022020000000002101000000000000600000000c110200000058c020000000405002010000000000005000005010d20000000008c020000000028c02000000000881200000000000000c0000000000006000000000000f00000304c0200000000000210100000001011030000000000000000000000000000000304c020200000514c0200000000000000f
  | 7, 37 => 0x10000053481200000005040e20000000544c020000000000000040000004802200000000000000100000000000010000000101102000000380a20000000000000040000002802200000000480220200000000401030000000012101000000488520000000028c02000000000881200000000000000c0000000000005000000000e102000000480e20000000000021020000000012101000000000000600000048c520000000544c0200000005308520000000000000050000000000005000000000210100000000c1103
  | 7, 38 => 0xc010000000000121010000000006101000000000000e00000514c0200000000000210100000038c0200000000000000e0000004802200000000480220000000000000040000051500201000000000a10000000214c8200000000000000a0000000000006000000480e20000000000021010000003881200000000000a101000000480a200000000000000400000038022000000041485200000000000000500000000000050000040500201000000000000f000000000000f000000000000f000000008510100000038c0200
  | 7, 39 => 0xe1030000000100101000000480a20000000000c110200000001001010000000100101000005440e2000000000000003000000000e1030000000000005000000000000400000000c01000000002802200000005340220000000000000010000000000005000000000a10100000000000040000054402200000005301220000000000000010000000881200000000380a20000000000000020000000000006000000000e1000000000006103000005440e20000000000121010000053500200000000000e1030000000002102
  | 7, 40 => 0x610200000000000090000005885200000000000000c000000280220100000544c02000000000000001000000010110300000000000010000004806200000000000e103000000000000f000000000000f0000000000001000000000000c0000000002100000005140e200000000000000000000008c92000000053402200000000480e200000000000000f0000000000006000000488520000000000000060000000000001000005440220000000000000040000003802200000000388120000000000000020000000012101
  | 7, 41 => 0x544c0202000000001210000000530022000000000000001000000090120000000514c0200000000000610300000018812000000000012101000000000000b00000000121020000000002101000000000000900000000000030000000041102000000480220100000405002010000000002102000005340220000000544c020000000000411020000000012101000000000a10100000000c1103000000000210100000544022000000000000001000000000210200000000c110000000530022000000000012101
  | 7, 42 => 0x1001010000000100101000000008510100000500c5200000000000000200000514c020000000304c0202000000000000400000544c02000000000000004000005300220000000544c0202000000488520000000000c01000000000000005000000000000600000001051030000002806200000000000000b0000052441200000000000000c000000000e103000000000e1020000000000003000000000000700000001011030000000000004000000000e1000000000081101000000000210200000000000000000000000006
  | 7, 43 => 0x304c02000000000002101000000000e1020000000000006000000010110100000304c020000000038812000000000000005000000380220000000000c0102000000010510200000500c5200000000008510100000000000050000002802200000000000000400000000c11030000000000008000000000e100000000000000e000005040e20000000304c02000000000000006000005440e2000000000100103000000000000d0000001881200000000000000c000000000a10000000540c1200000000088520000000304c0202
  | 7, 44 => 0x12101000005308520000000001001030000043501200000000090d200000000000210300000000000060000000000005000000280220000000058c02000000000085101000000000000d000000004110300000000c0100000005010d200000000000e1020000000012101000000480220000000524c02030000042505200000000380a20000000000000050000000000004000000000000f00000000000030000003806203000000000000f0000000100101000000000a10100000000000030000000000001000000000000e
  | 7, 45 => 0x5040e2000000000002100000000000e1020000001881200000000380a20000000048c1200000000480e2000000000000001000000000000e000000000000c0000000002101000005308520000000000000090000000012102000000488520000000504842000000000000006000005040e200000000480a20000000000000040000000000003000005140e20000000058c0200000005440e20000000000121000000000000004000005010d200000000001210100000304c0200000000380220000000048022000000000000002
  | 7, 46 => 0xb0000000012103000000480a200000000000210100000524412000000000040102000000088520000000524c020000000544802000000050085200000000480a20000000000000000000053500201000000290d2000000002802200000000008510100000544c920000000000000010000000000005000005010d2000000000101103000005000e20000000000000070000000100101000000000210200000524c0202000000000000500000000411020000000002101000005440220000000000c11020000000000004
  | 7, 47 => 0xf000005340220000000544c02000000000000005000005440220000000000121010000000000001000000588520000000544c02020000000006103000000000000e00000544c02000000000901200000005440e2000000000000006000000000000e00000000061010000000000005000005140e200000000000a101000000001210000000000811010000000041102000000000000600000000021010000000000004000000480e20000000000000040000000000004000000390d20000000038022000000000000009
  | 7, 48 => 0x53002200000000090120000000048c0200000000000000100000000000060000000012101000005340220000000544c0200000000000210100000000021010000000000003000000000000600000000061020000002806200000005308120000000000411030000000012102000000480e2000000054402200000000000000c00000058852000000000901200000000000a10100000000000070000000000005000000000000e0000053412200000000000000c000000000000f00000544852000000000012101000005140e200
  | 7, 49 => 0xe00000038c020000000038022000000000012101000000004110200000544c0200000000000000f00000000000010000053002200000000000000500000000021020000000885200000000008510100000028c02000000000101101000000000210100000028022000000000000006000000000a101000005440e2000000050012200000000000210100000544c0200000000000210000000000c01020000005885200000005140220000000304c02000000000002101000000000000200000000061030000000000009
  | 7, 50 => 0x2101000000000210000000000021010000000000001000000480e20200000000c5102000000280220000000048022000000000002102000005000e20000000048c1200000000000000700000038022000000053002200000000480a200000000000000c0000053402200000000000000c000000000000200000000000040000000085101000000000000400000000000000000000000006000005040e2000000000000004000005440220000000304c02000000043501200000000000000600000048022000000000012101
  | 7, 51 => 0x304c02000000000000005000000000210000000038022000000004885200000000590d200000000090d200000000000000400000000c510200000028022000000000012102000004348520000000530022000000000000006000000000000500000544c1200000000000000f0000004806203000000480e2000000000000007000000000000300000000000060000043501200000000090d200000000380220000000000000050000000000004000000001210000000028022000000000000000000005040e200000000480e200
  | 7, 52 => 0x121010000000000001000000000000e0000000000006000000001210000000048022000000000000006000000000210100000000000030000000085101000000000000600000304c0200000000000e103000005140e20000000000c0100000005000e200000000000000600000048022000000003802200000000000000700000000c0100000000000210300000048c120000000000000060000000000006000005140e200000000000000f0000000000004000000380a200000000000000400000000000010000000002101
  | 7, 53 => 0x3885200000000000000400000008c1200000000000000f0000002806200000005010d200000000000000f00000000000000000050085200000000000000c000000480220000000544852000000000000005000005400220000000001011010000053101200000005350020100000039012000000054402200000000010110100000544c02000000000000001000000000610200000059012000000000000004000000000000c00000048c02000000000000006000000000000f00000540c1200000005000e2000000000000005
  | 7, 54 => 0x121010000004802201000000000e1000000000002100000000001210100000304c02000000054485200000000000000f00000304c02020000000002101000000000000f000000380220000000058c02000000000000005
  | 8, 0 => 0xa1000000000000003000000000610000000001051000000000109100000000000000000000000000020000000006101000000000210000000000c5100000000000000100000000000080000000101100000000000210000000000411010000000101100000000004110000000000000010000000041102000000000e100000000000210000000000000030000000000006000000010110000000000c5100000000000000000000000411020000000105100000000000000100000000c510000000000811000000000000002
  | 8, 1 => 0x1011020000000006100000000010d100000000000e10000000000c9100000000000000e0000000000003000000000a10000000000000000000000000005000000000000f000000000a1000000000000008000000000e10000000000c110000000000021000000000105100000000000210100000000121000000000105100000000000e10000000000000030000000041101000000008510000000000c5100000000010110100000000c0102000000010d1000000000000002000000008510000000000000010000000000002
  | 8, 2 => 0xc51000000000000005000000000e10300000000c510200000000000030000000000001000000000e10000000000c110000000000411000000000105102000000004110100000000000010000000000001000000000000200000000c5102000000000e10000000000000010000000109101000000010110000000000c51000000000101102000000010d10000000000851000000000000002000000000a100000000008510000000000021030000000000009000000000000000000000851010000000101101000000000000b
  | 8, 3 => 0x21000000000000001000000000e10300000000000010000000012103000000010d102000000010510100000000c5100000000000e1000000000101103000000000000600000000000030000000012101000000000a100000000000e1000000000000003000000000e10200000000c01000000000000002000000000210000000000411010000000000001000000000000000000000c910000000000000010000000012100000000000000300000001051000000000105101000000000e10200000001051020000000081100
  | 8, 4 => 0x1011000000000000001000000000000200000000c01000000000000002000000000210000000000000010000000006103000000010910000000000c9100000000000e1000000000012101000000000000000000000c0100000000000e100000000010010100000000121010000000000001000000000e102000000010d1000000000012101000000010d1000000000002100000000000a101000000010910000000000c1100000000010d102000000000a100000000008510000000000121000000000100101000000000e102
  | 8, 5 => 0x210000000000021020000000000003000000000000200000001091010000000000003000000010510100000000811000000000006101000000004110300000000021000000000006102000000008510000000000c110000000001051000000000000001000000004110200000000c1100000000001210100000000000020000000105101000000000000100000000121010000000000002000000001210000000000121020000000081100000000000000100000000851000000000081100000000000a1010000000000002
  | 8, 6 => 0x2000000010510000000000811000000000000002000000000e100000000001210100000000c51000000000002101000000010d100000000000000100000000021000000000002102000000000a100000000000a10100000000000010000000002103000000000000400000000000060000000000004000000001210000000000000060000000000008000000010110000000000c01000000000000004000000000210200000000000010000000000003000000000000000000000c9100000000000e1000000000012101
  | 8, 7 => 0x300000000000020000000000002000000000000300000000c1100000000000e1000000000085101000000000000100000000000000000000000001000000010d100000000000a100000000010510300000000021000000000002102000000000e10000000000851010000000000003000000010910000000000c01000000000002101000000008510000000000c110000000000021030000000000002000000000e1000000000000006000000000000f0000000002100000000000000600000000121000000000000002
  | 8, 8 => 0xc010000000000000040000000105100000000000000c00000000c1102000000008510000000000c5100000000000000c000000010d103000000000e100000000000000100000000000060000000085100000000008510100000000811000000000101100000000000000100000000c0100000000000000300000000000010000000012100000000000000600000000000020000000002100000000000000100000000021010000000012100000000000210100000000c1100000000010910000000000c51030000000000001
  | 8, 9 => 0x10000000000003000000000000c000000000e100000000010110000000000000030000000101101000000010d1000000000081101000000000a1000000000000000000000008510000000000000030000000000001000000000000200000000000060000000081100000000000e10000000000021000000000081100000000010110100000000c010000000000c1100000000000e10000000000c11020000000000001000000000210000000000121000000000000001000000000210000000000000060000000000006
  | 8, 10 => 0x100101000000000000f000000010d100000000000e1030000000002100000000010110100000001051000000000105100000000000000300000000c510000000000000030000000000002000000010010100000000000030000000000009000000000000f00000000c0100000000000e10000000000c01020000000000001000000000000c0000000002101000000010510000000000c01020000000101103000000000000f00000000c510000000000121000000000002100000000008110000000000c0100
  | 8, 11 => 0xe102000000010d100000000010d1020000000000002000000000a10000000000121000000000100101000000008110000000000811010000000085100000000000e1000000000002100000000000e10200000000c1100000000000000100000000c11000000000101100000000000e103000000000000200000000c5100000000010d103000000000a10000000000c51020000000006103000000000210000000000c110200000000000020000000081100000000000e1000000000101100000000010110200000000c9100
  | 8, 12 => 0x2100000000000000c00000000021000000000000001000000000210200000000000060000000101100000000000000300000000811000000000000003000000000000100000000000060000000081100000000000000600000000411000000000000006000000008510000000000c010000000000000030000000002103000000000000100000001091000000000085101000000001210000000000c0102000000010d100000000000210000000000021000000000105102000000000000000000000c5102000000000e100
  | 8, 13 => 0xc110300000000c11000000000101100000000001210100000000000010000000000001000000000000f00000000c010000000000c11000000000000001000000000000e000000000e100000000010d1000000000000005000000000a10000000000121010000000000006000000000210000000000000050000000002100000000000e10000000000851000000000000002000000010d1000000000012100000000001210200000000811000000000000001000000001210200000000c110000000000c01000000000081100
  | 8, 14 => 0x10110000000000c010000000000c01020000000000001000000000e100000000010110000000000000010000000002101000000010d10000000000021010000000000006000000000e1000000000085100000000000e100000000010d100000000000a100000000000000400000000c0100000000000210100000000c110000000000c1102000000000210000000001011000000000002100000000000e100000000000000100000000021010000000002100000000000210200000000851000000000000006
  | 9, 0 => 0x10000000000000000000000000000000000000020000000000003000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000100000000000010000000000000000000000000200000000000020000000000000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 12 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_55 roots_55 9 s ws hint
  | 1 => checkCutEntry dom_31 roots_31 8 s ws hint
  | 2 => checkCutEntry dom_59 roots_59 8 s ws hint
  | 3 => checkCutEntry dom_61 roots_61 8 s ws hint
  | 4 => checkCutEntry dom_62 roots_62 6 s ws hint
  | 5 => checkCutEntry dom_47 roots_47 6 s ws hint
  | 6 => checkCutEntry dom_47_16 roots_47_16 6 s ws hint
  | 7 => checkCutEntry dom_15_16 roots_15_16 5 s ws hint
  | 8 => checkCutEntry dom_27 roots_27 5 s ws hint
  | 9 => checkCutEntry dom_43 roots_43 5 s ws hint
  | 10 => checkCutEntry dom_29 roots_29 5 s ws hint
  | 11 => checkCutEntry dom_45 roots_45 5 s ws hint
  | 12 => checkCutEntry dom_30 roots_30 5 s ws hint
  | 13 => checkCutEntry dom_54 roots_54 5 s ws hint
  | 14 => checkCutEntry dom_15 roots_15 5 s ws hint
  | 15 => checkCutEntry dom_46_16 roots_46_16 5 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_63 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_55 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_59 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_61 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_62 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_27 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_43 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_29 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_45 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_30 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_54 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_46_16 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_63 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_63 == dom_63) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_63 goalM u ys) : RunD dom_63 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_63 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 9 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 9 0 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 9 → Z 5 i = true := z5_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 16 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_16 : ∀ i, 16 ≤ i → i < 32 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_32 : ∀ i, 32 ≤ i → i < 48 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_48 : ∀ i, 48 ≤ i → i < 64 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_64 : ∀ i, 64 ≤ i → i < 80 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_80 : ∀ i, 80 ≤ i → i < 83 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 3 80 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 83 → Z 6 i = true := (range_split (range_split (range_split z6_0 z6_16) (range_split z6_32 z6_48)) (range_split z6_64 z6_80))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : ∀ i, 0 ≤ i → i < 16 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_16 : ∀ i, 16 ≤ i → i < 32 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_32 : ∀ i, 32 ≤ i → i < 48 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_48 : ∀ i, 48 ≤ i → i < 64 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_64 : ∀ i, 64 ≤ i → i < 80 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_80 : ∀ i, 80 ≤ i → i < 96 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_96 : ∀ i, 96 ≤ i → i < 112 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_112 : ∀ i, 112 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_128 : ∀ i, 128 ≤ i → i < 144 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_144 : ∀ i, 144 ≤ i → i < 160 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_160 : ∀ i, 160 ≤ i → i < 176 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 160 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_176 : ∀ i, 176 ≤ i → i < 192 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 176 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_192 : ∀ i, 192 ≤ i → i < 208 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 192 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_208 : ∀ i, 208 ≤ i → i < 224 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 208 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_224 : ∀ i, 224 ≤ i → i < 240 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 224 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_240 : ∀ i, 240 ≤ i → i < 256 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 240 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_256 : ∀ i, 256 ≤ i → i < 264 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 256 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 264 → Z 7 i = true := (range_split (range_split (range_split (range_split (range_split z7_0 z7_16) (range_split z7_32 z7_48)) (range_split (range_split z7_64 z7_80) (range_split z7_96 z7_112))) (range_split (range_split (range_split z7_128 z7_144) (range_split z7_160 z7_176)) (range_split (range_split z7_192 z7_208) (range_split z7_224 z7_240)))) z7_256)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_0 : ∀ i, 0 ≤ i → i < 16 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_16 : ∀ i, 16 ≤ i → i < 32 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_32 : ∀ i, 32 ≤ i → i < 48 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_48 : ∀ i, 48 ≤ i → i < 64 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_64 : ∀ i, 64 ≤ i → i < 80 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_80 : ∀ i, 80 ≤ i → i < 96 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_96 : ∀ i, 96 ≤ i → i < 112 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_112 : ∀ i, 112 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_128 : ∀ i, 128 ≤ i → i < 140 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 128 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 140 → Z 8 i = true := (range_split (range_split (range_split (range_split z8_0 z8_16) (range_split z8_32 z8_48)) (range_split (range_split z8_64 z8_80) (range_split z8_96 z8_112))) z8_128)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_0 : ∀ i, 0 ≤ i → i < 14 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 14 0 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 14 → Z 9 i = true := z9_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_0 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := z10_0
theorem checked (s : Nat) (hs : s ≤ 10) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
  · exact fun i hi => z7 i (Nat.zero_le i) hi
  · exact fun i hi => z8 i (Nat.zero_le i) hi
  · exact fun i hi => z9 i (Nat.zero_le i) hi
  · exact fun i hi => z10 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_63 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 6 5 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 10) (h : RunD dom_63 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_63 roots_63 goal_63 11 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_63 goal_63 := by
    have h0 : isConstB dom_63 goal_63 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_63

theorem low_63 : Lower dom_63 roots_63 goal_63 11 := S_63.noCircuit

def pt6 (r : Nat) : Fin 6 → Bool := fun i => r.testBit i.val
theorem roots_63_bits : ∀ r : Fin 64, roots_63.map (·.testBit r.val) = List.ofFn (pt6 r.val) := by decide +kernel
theorem dom_63_lt : ∀ r : Fin 64, dom_63.testBit r.val = true := by decide +kernel
theorem lower_to_circuit6 (f : (Fin 6 → Bool) → Bool) (T lb : Nat)
    (hT : ∀ r : Fin 64, T.testBit r.val = f (pt6 r.val))
    (hncT : ¬ IsConst dom_63 T)
    (hlow : Lower dom_63 roots_63 T lb) :
    ∀ t : ℕ, HasCircuitSize 6 f t → lb ≤ t := by
  rintro t ⟨C, hfan, hsz, hev⟩
  have hsup0 : ∀ v ∈ roots_63, Avail mask256 roots_63 v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates roots_63 hfan 0 roots_63 roots_63 rfl hsup0
  set out := (execN C.gates roots_63).getD C.output 0
  have hout : out &&& dom_63 = T &&& dom_63 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and]
    by_cases hlt : r < 64
    · rw [dom_63_lt ⟨r, hlt⟩, Bool.and_true, Bool.and_true]
      have h1 := execN_bit C.gates roots_63 r (by omega) (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [roots_63_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN C.gates roots_63).map (·.testBit r)).getD C.output false =
          out.testBit r := by
        simp only [out, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates roots_63)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      exact h2.trans ((hev (pt6 r)).trans (hT ⟨r, hlt⟩).symm)
    · have hd : dom_63.testBit r = false := by
        apply Nat.testBit_lt_two_pow
        have h64 : dom_63 < 2 ^ 64 := by decide
        exact lt_of_lt_of_le h64 (Nat.pow_le_pow_right (by omega) (by omega))
      rw [hd, Bool.and_false, Bool.and_false]
  have hav_out : Avail mask256 bank out := by
    by_cases hi : C.output < (execN C.gates roots_63).length
    · exact hsup _ (getD_mem hi)
    · rw [show out = 0 from List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hd63 : dom_63 &&& mask256 = dom_63 := by decide
  have hm256 : mask256 &&& mask256 = mask256 := by decide
  have houtm : (out &&& mask256) &&& dom_63 = T &&& dom_63 := by
    rw [Nat.and_assoc, Nat.and_comm mask256 dom_63, hd63, hout]
  have hnc_m : ¬ IsConst dom_63 (out &&& mask256) := fun hc => hncT (by rcases hc with h0 | h1; exact Or.inl (houtm.symm.trans h0); exact Or.inr (houtm.symm.trans h1))
  have hnc_256 : ¬ IsConst mask256 out := fun hc => hnc_m (by
    rcases hc with h0 | h1
    · exact Or.inl (by rw [h0]; simp)
    · exact Or.inr (by rw [h1, Nat.and_comm, hd63]))
  obtain ⟨s, ws, hs, _, hws, hrun⟩ := reach_to_run hm256 hnc_256 hr hav_out
  have hws63 : ∀ w ∈ ws, Avail dom_63 roots_63 w := fun w hw => by
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (hws w hw)
    exact Or.inr ⟨u, hu, by rw [Nat.and_assoc, Nat.and_comm mask256 dom_63, hd63]⟩
  obtain ⟨q, next, hq, hav_q, hqp⟩ := contraction hd63 hd63 hnc_m hrun (show NatReach dom_63 roots_63 0 roots_63 from rfl) hws63
  have hL := hlow q next hq (avail_of_eq houtm hav_q)
  show lb ≤ t
  have : C.gates.length ≤ t := hsz
  omega

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 15]⟩], 16⟩

theorem wit_mono : PEqualNP.MetaComplexity.Monotone2 wit := by
  simp [wit, PEqualNP.MetaComplexity.Monotone2]

theorem wit_sz : wit.size ≤ 11 := by decide

set_option maxRecDepth 40000 in
theorem wit_ev : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = Nat.testBit (4278124202 * 2 ^ 32 + 4276813480) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel

set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_63.testBit r.val = (fun x : Fin 6 → Bool => Nat.testBit (4278124202 * 2 ^ 32 + 4276813480) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) (pt6 r.val) := by decide +kernel

theorem lower : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124202 * 2 ^ 32 + 4276813480) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) t → 11 ≤ t :=
  lower_to_circuit6 (fun x : Fin 6 → Bool => Nat.testBit (4278124202 * 2 ^ 32 + 4276813480) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) goal_63 11 hT6 (by unfold IsConst; decide) low_63

end PEqualNP.Outside.L_meta_38075_aux

theorem PEqualNP.Outside.L_meta_38075 :
  ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124202 * 2 ^ 32 + 4276813480) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124202 * 2 ^ 32 + 4276813480) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  exact ⟨PEqualNP.Outside.L_meta_38075_aux.wit, PEqualNP.Outside.L_meta_38075_aux.wit_mono, le_trans PEqualNP.Outside.L_meta_38075_aux.wit_sz (PEqualNP.Outside.L_meta_38075_aux.lower s hs), PEqualNP.Outside.L_meta_38075_aux.wit_ev⟩
