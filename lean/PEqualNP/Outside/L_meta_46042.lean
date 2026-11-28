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

namespace PEqualNP.Outside.L_meta_46042_aux

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

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfaaafaa0f000a000faaafaa0f000a000faaafaa0f000a000faaafaa0f000a000
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_31_32 : Nat := 0xffffffff00000000
def goal_31_32 : Nat := 0xfeeefaa8feeefaa8feeefaa8feeefaa8feeefaa8feeefaa8feeefaa8feeefaa8
def roots_31_32 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xfaa8faa8e888e888faa8faa8e888e888faa8faa8e888e888faa8faa8e888e888
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_45 : Nat := 0x333300003333
def goal_45 : Nat := 0xfaa0faa0a000a000faa0faa0a000a000faa0faa0a000a000faa0faa0a000a000
def roots_45 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_55_8 : Nat := 0xff00ff00ff00ff00
def goal_55_8 : Nat := 0xfefefafafcfce8e8fefefafafcfce8e8fefefafafcfce8e8fefefafafcfce8e8
def roots_55_8 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xeeeea8a8cccc8888eeeea8a8cccc8888eeeea8a8cccc8888eeeea8a8cccc8888
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_62_1 : Nat := 0xaaaaaaaaaaaaaaaa
def goal_62_1 : Nat := 0xfffffffcfcccfcccfffffffcfcccfcccfffffffcfcccfcccfffffffcfcccfccc
def roots_62_1 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_62 : Nat := 0x5555555555555555
def goal_62 : Nat := 0xfcccf000fcccc000fcccf000fcccc000fcccf000fcccc000fcccf000fcccc000
def roots_62 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_31 : Nat := 0xffffffff
def goal_31 : Nat := 0xfccce888fccce888fccce888fccce888fccce888fccce888fccce888fccce888
def roots_31 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_23_32 : Nat := 0xff00ff00000000
def goal_23_32 : Nat := 0xeeeea8a8eeeea8a8eeeea8a8eeeea8a8eeeea8a8eeeea8a8eeeea8a8eeeea8a8
def roots_23_32 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0]

def dom_51 : Nat := 0xf000f000f000f
def goal_51 : Nat := 0xeeee8888cccc8888eeee8888cccc8888eeee8888cccc8888eeee8888cccc8888
def roots_51 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_46_1 : Nat := 0xaaaa0000aaaa
def goal_46_1 : Nat := 0xfffcfffcfcccfcccfffcfffcfcccfcccfffcfffcfcccfcccfffcfffcfcccfccc
def roots_46_1 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_15 : Nat := 0xffff
def goal_15 : Nat := 0xe888e888e888e888e888e888e888e888e888e888e888e888e888e888e888e888
def roots_15 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0]

def dom_23_8 : Nat := 0xff00ff00
def goal_23_8 : Nat := 0xfcfce8e8fcfce8e8fcfce8e8fcfce8e8fcfce8e8fcfce8e8fcfce8e8fcfce8e8
def roots_23_8 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0]

def dom_59_4 : Nat := 0xf0f0f0f0f0f0f0f0
def goal_59_4 : Nat := 0xffeeffaaffccee88ffeeffaaffccee88ffeeffaaffccee88ffeeffaaffccee88
def roots_59_4 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xeeeeaa88cccc8888eeeeaa88cccc8888eeeeaa88cccc8888eeeeaa88cccc8888
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_27_32 : Nat := 0xf0f0f0f00000000
def goal_27_32 : Nat := 0xeeeeaa88eeeeaa88eeeeaa88eeeeaa88eeeeaa88eeeeaa88eeeeaa88eeeeaa88
def roots_27_32 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_29_32 : Nat := 0x3333333300000000
def goal_29_32 : Nat := 0xfaaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0
def roots_29_32 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_53_8 : Nat := 0x3300330033003300
def goal_53_8 : Nat := 0xfafafafaf0f0a0a0fafafafaf0f0a0a0fafafafaf0f0a0a0fafafafaf0f0a0a0
def roots_53_8 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_54_8 : Nat := 0x5500550055005500
def goal_54_8 : Nat := 0xfcfcf0f0fcfcc0c0fcfcf0f0fcfcc0c0fcfcf0f0fcfcc0c0fcfcf0f0fcfcc0c0
def roots_54_8 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_58_4 : Nat := 0x5050505050505050
def goal_58_4 : Nat := 0xffccff00ffcccc00ffccff00ffcccc00ffccff00ffcccc00ffccff00ffcccc00
def roots_58_4 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_60_1 : Nat := 0x2222222222222222
def goal_60_1 : Nat := 0xfffffff0f000f000fffffff0f000f000fffffff0f000f000fffffff0f000f000
def roots_60_1 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfeeefaa8fccce888feeefaa8fccce888feeefaa8fccce888feeefaa8fccce888
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

namespace S_61
def pairsG : List (Nat × Nat) := [(5, 13), (5, 37), (9, 13), (9, 41), (12, 13), (12, 28), (12, 44), (17, 49), (20, 28), (21, 29), (21, 53), (24, 28), (25, 29), (25, 57), (33, 37), (33, 41), (33, 49), (36, 37), (36, 44), (40, 41), (40, 44), (48, 49), (52, 53), (52, 60), (56, 57), (56, 60)]
def r1sG : List Nat := [5, 5, 9, 9, 12, 12, 12, 17, 20, 21, 21, 24, 25, 25, 33, 33, 33, 36, 36, 40, 40, 48, 52, 52, 56, 56]
def r2sG : List Nat := [13, 37, 13, 41, 13, 28, 44, 49, 28, 29, 53, 28, 29, 57, 37, 41, 49, 37, 44, 41, 44, 49, 53, 60, 57, 60]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [9917635831053, 22042329032988, 26440375543068, 13216221242637, 39604097649957, 23141840660764, 13233468221709, 13233736195085, 36322624736553, 44032426843180]
def xsM : List Nat := roots_61.map (· &&& dom_61)
def goalM : Nat := goal_61 &&& dom_61
def NN : Nat → Nat
  | 4 => 1
  | 5 => 12
  | 6 => 11
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x995298d1
  | 5, 0 => 0x995298d186fec3496534bccb4ea5ebb34105f2c03e3ca53936664f9c323655422d8e446c2ac4f6e50f92b19f0a2d231c
  | 6, 0 => 0xdff407ea9e310d9b995298d151db27f540cd85c33e3ca5393810c1db2ac4f6e51dce88e912ef7747086941f4
  | 7, 0 => 0x995298d1
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x22222222000000000000000000000000000000000000000000000000000000002222000022220000000000000000000000000000000000000000000000000000202020202020202000000000000000000000000000000000000000000000000011111111111111110000000000000000000000000000000000000000000000000303030303030303000000000000000000000000000000000000000000000000003300330033003300000000000000000000000000000000000000000000000000003333000033330000000000000000000000000000000000000000000000000000000033333333
  | 0, 1 => 0x33330000000000000000000000000000000000000000000000000000000000003330333033303330000000000000000000000000000000000000000000000000332233223322332200000000000000000000000000000000000000000000000033003300330033000000000000000000000000000000000000000000000000003300330030003000000000000000000000000000000000000000000000000000303030303030303000000000000000000000000000000000000000000000000030303030000000000000000000000000000000000000000000000000000000002222222222222222
  | 0, 2 => 0x33333333333300000000000000000000000000000000000000000000000000003333333330303030000000000000000000000000000000000000000000000000333333332222222200000000000000000000000000000000000000000000000033333333000000000000000000000000000000000000000000000000000000003333303033330000000000000000000000000000000000000000000000000000333322223333222200000000000000000000000000000000000000000000000033330000333300000000000000000000000000000000000000000000000000003333000033000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x148b1485
  | 5, 0, 0 => 0xa458a42d62c51d69140c4b48314858b10302d22c40d6d16250b49b14856290102d18a405692628cb48ad485
  | 6, 0, 0 => 0x291629016a458a41d8148b1485a45ec521a916b14860522c40d6f48b14860518a405691731486a458a411a91629056
  | 7, 0, 0 => 0x148b1485
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 29
  | 5 => 29
  | 6 => 34
  | 7 => 29
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 5 0) :: stateWires n (ids >>> 5)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x1c000000000000000000000000000000000000000000000000000000000000000368000000000000000000000000000000000000000000000000000000000000006030000000000000000000000000000000000000000000000000000000003fe0970000000000000000000000000000000000000000000000000000000000339f88c0000000000000000000000000000000000000000000000000000000000e7c78300000000000000000000000000000000000000000000000000000000001fc07f0000000000000000000000000000000000000000000000000000000000003fff
  | 0, 1 => 0x3e000000000000000000000000000000000000000000000000000000000000003de3f7f000000000000000000000000000000000000000000000000000000000319feff000000000000000000000000000000000000000000000000000000000318387c00000000000000000000000000000000000000000000000000000000031800700000000000000000000000000000000000000000000000000000000000c607730000000000000000000000000000000000000000000000000000000000c60000000000000000000000000000000000000000000000000000000000000001f68f
  | 0, 2 => 0x3ffff800000000000000000000000000000000000000000000000000000000003ffc7730000000000000000000000000000000000000000000000000000000003fff68f0000000000000000000000000000000000000000000000000000000003ffc0000000000000000000000000000000000000000000000000000000000003e63f800000000000000000000000000000000000000000000000000000000003e1ff8f0000000000000000000000000000000000000000000000000000000003e03f800000000000000000000000000000000000000000000000000000000003e03800
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x16be48a000000000000000000000000000000000000000000000000000000000161368000000000000000000000000000000000000000000000000000000000004256170000000000000000000000000000000000000000000000000000000002940960000000000000000000000000000000000000000000000000000000000129a088000000000000000000000000000000000000000000000000000000000063448200000000000000000000000000000000000000000000000000000000001ec05f0000000000000000000000000000000000000000000000000000000000001b35
  | 0, 1 => 0x3e124800000000000000000000000000000000000000000000000000000000003deff7f0000000000000000000000000000000000000000000000000000000003ffffff00000000000000000000000000000000000000000000000000000000039cbb7d00000000000000000000000000000000000000000000000000000000039cbb7d0000000000000000000000000000000000000000000000000000000002d65f770000000000000000000000000000000000000000000000000000000002d6444200000000000000000000000000000000000000000000000000000000016bf69f
  | 0, 2 => 0x3ffffea0000000000000000000000000000000000000000000000000000000003ffffff0000000000000000000000000000000000000000000000000000000003fff6df0000000000000000000000000000000000000000000000000000000003ffe4ca0000000000000000000000000000000000000000000000000000000003f77fe20000000000000000000000000000000000000000000000000000000003ebffbf0000000000000000000000000000000000000000000000000000000003e13fa00000000000000000000000000000000000000000000000000000000003e13fa0
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 24 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 24 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 24 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 24 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 5 0) :: stateWiresD n (ids >>> 5)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 5 0) :: stateWiresS n (ids >>> 5)
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 5 0 (NN s)
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_61 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_61 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_61 == dom_61) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_61 goalM u ys) : RunD dom_61 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_61 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
private theorem z5_0 : ∀ i, 0 ≤ i → i < 12 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 0 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 12 → Z 5 i = true := z5_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 11 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 11 0 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 11 → Z 6 i = true := z6_0
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
  scr dom_61 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_61 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_61 roots_61 goal_61 8 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_61 goal_61 := by
    have h0 : isConstB dom_61 goal_61 = false := by decide +kernel
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

end S_61

theorem low_61 : Lower dom_61 roots_61 goal_61 8 := S_61.noCircuit

namespace S_31_32
def pairsG : List (Nat × Nat) := [(33, 35), (33, 37), (33, 41), (33, 49), (34, 35), (34, 50), (36, 37), (36, 44), (38, 39), (38, 46), (38, 54), (40, 41), (40, 44), (42, 43), (42, 46), (42, 58), (48, 49), (48, 50), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [33, 33, 33, 33, 34, 34, 36, 36, 38, 38, 38, 40, 40, 42, 42, 42, 48, 48, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [35, 37, 41, 49, 35, 50, 37, 44, 39, 46, 54, 41, 44, 43, 46, 58, 49, 50, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0xffffff
def pool6G : List Nat := [37525937860899, 41923883311909, 39724826503461, 41924051477795, 46322165098787, 57317280983333, 44122805904681, 41923883313445, 46321862714153, 46322165100835, 44135640278316, 61715260384553, 52923143889714, 52918865765169]
def xsM : List Nat := roots_31_32.map (· &&& dom_31_32)
def goalM : Nat := goal_31_32 &&& dom_31_32
def NN : Nat → Nat
  | 4 => 3
  | 5 => 14
  | 6 => 11
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x912d5ca15f5ce3510b343e51
  | 5, 0 => 0x7523d75b6eabba25636d008b608578e95f5ce3515afe27273a877c60239e6b931ace269f0e094e0c0c9503e80c70127509f3bf120467640c
  | 6, 0 => 0x7523d75b6b1890e0608578e95f5ce351527e04584fbea8484995ef47358964b82f5e14ef273b926c059706fd
  | 7, 0 => 0x5f5ce351
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xaaaaaaaa00000000000000000000000000000000000000000000000000000000aa00aa00000000000000000000000000000000000000000000000000000000008888888800000000000000000000000000000000000000000000000000000000555555550000000000000000000000000000000000000000000000000000000033333333000000000000000000000000000000000000000000000000000000000f0f0f0f0000000000000000000000000000000000000000000000000000000000ff00ff000000000000000000000000000000000000000000000000000000000000ffff00000000
  | 0, 1 => 0xf0f0f0f000000000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000eeeeeeee00000000000000000000000000000000000000000000000000000000eeeeaaaa00000000000000000000000000000000000000000000000000000000cccccccc00000000000000000000000000000000000000000000000000000000cccc888800000000000000000000000000000000000000000000000000000000cccc000000000000000000000000000000000000000000000000000000000000c0c0c0c000000000
  | 0, 2 => 0xffffcccc00000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000ffaaffaa00000000000000000000000000000000000000000000000000000000ffaaff0000000000000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000fcfcfcfc00000000000000000000000000000000000000000000000000000000faf0faf000000000
  | 0, 3 => 0xfffff0f000000000000000000000000000000000000000000000000000000000fffff00000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x2d582d2d37acea0bcdec4
  | 5, 0, 0 => 0x2d37ac8b69bd8b5bcde93acdeb3816d37aceb659c415b4e283ad9e71856d37a8eb69c1675b51eb3ae26f59d6d57accb69ac825
  | 6, 0, 0 => 0x169bd645b4dee59d8137ace0505a6f59d6d37b5676bda6f59dad37ace46b4deb395ad37ace36cda6f59dad393d676
  | 7, 0, 0 => 0x169bd675
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 29
  | 5 => 29
  | 6 => 34
  | 7 => 29
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 5 0) :: stateWires n (ids >>> 5)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000fffff00000000000000000000000000000000000000000000000000000000000ff18cf0000000000000000000000000000000000000000000000000000000000e3f83f00000000000000000000000000000000000000000000000000000000001f07ff000000000000000000000000000000000000000000000000000000000000ffff
  | 0, 1 => 0x1c07c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e73f000000000000000000000000000000000000000000000000000000000000000f000000000000000000000000000000000000000000000000000000000000e730000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000700
  | 0, 2 => 0xffe7300000000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000e0f80f0000000000000000000000000000000000000000000000000000000000e0f8000000000000000000000000000000000000000000000000000000000000e0f8000000000000000000000000000000000000000000000000000000000000e0000000000000000000000000000000000000000000000000000000000000001ce7f000000000000000000000000000000000000000000000000000000000001c07c0
  | 0, 3 => 0xff07c00000000000000000000000000000000000000000000000000000000000ff0000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x25295f000000000000000000000000000000000000000000000000000000000020280400000000000000000000000000000000000000000000000000000000000021110000000000000000000000000000000000000000000000000000000000dad6a00000000000000000000000000000000000000000000000000000000000b518ce000000000000000000000000000000000000000000000000000000000063a83d00000000000000000000000000000000000000000000000000000000000f057b0000000000000000000000000000000000000000000000000000000000007bd7
  | 0, 1 => 0x9c57c2000000000000000000000000000000000000000000000000000000000090528000000000000000000000000000000000000000000000000000000000006fef7f00000000000000000000000000000000000000000000000000000000006fad7f00000000000000000000000000000000000000000000000000000000004ae73100000000000000000000000000000000000000000000000000000000004aa53100000000000000000000000000000000000000000000000000000000004a84200000000000000000000000000000000000000000000000000000000000084700
  | 0, 2 => 0xffe7390000000000000000000000000000000000000000000000000000000000ff84280000000000000000000000000000000000000000000000000000000000f5fbdf0000000000000000000000000000000000000000000000000000000000f5fa8c0000000000000000000000000000000000000000000000000000000000f0fa840000000000000000000000000000000000000000000000000000000000f080000000000000000000000000000000000000000000000000000000000000def7f30000000000000000000000000000000000000000000000000000000000bc7fc6
  | 0, 3 => 0xffd7ea0000000000000000000000000000000000000000000000000000000000ffd6a8
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 26 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 26 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 26 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 26 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 5 0) :: stateWiresD n (ids >>> 5)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 5 0) :: stateWiresS n (ids >>> 5)
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 5 0 (NN s)
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_31_32 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_31_32 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_31_32 == dom_31_32) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_31_32 goalM u ys) : RunD dom_31_32 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_31_32 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 14 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 14 0 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 14 → Z 5 i = true := z5_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 11 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 11 0 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 11 → Z 6 i = true := z6_0
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
  scr dom_31_32 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_31_32 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_31_32 roots_31_32 goal_31_32 8 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_31_32 goal_31_32 := by
    have h0 : isConstB dom_31_32 goal_31_32 = false := by decide +kernel
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

end S_31_32

theorem low_31_32 : Lower dom_31_32 roots_31_32 goal_31_32 8 := S_31_32.noCircuit

namespace S_47
def pairsG : List (Nat × Nat) := [(1, 3), (2, 3), (5, 7), (5, 13), (5, 37), (6, 7), (6, 14), (9, 11), (9, 13), (9, 41), (10, 11), (10, 14), (12, 13), (12, 14), (12, 44), (33, 35), (33, 37), (33, 41), (34, 35), (36, 37), (36, 44), (38, 39), (38, 46), (40, 41), (40, 44), (42, 43), (42, 46)]
def r1sG : List Nat := [1, 2, 5, 5, 5, 6, 6, 9, 9, 9, 10, 10, 12, 12, 12, 33, 33, 33, 34, 36, 36, 38, 38, 40, 40, 42, 42]
def r2sG : List Nat := [3, 3, 7, 13, 37, 7, 14, 11, 13, 41, 11, 14, 13, 14, 44, 35, 37, 41, 35, 37, 44, 39, 46, 41, 44, 43, 46]
def mpG : Nat := 0x7ffffff
def pool6G : List Nat := [13215715951373, 9917635831053, 13219994075918, 13237241053966, 2203520470275, 36322624736553, 36305512238373, 13237645280014, 36322624736515, 9904396832003, 5506350320899, 6618748816677, 13232962929421, 11021442426126]
def xsM : List Nat := roots_47.map (· &&& dom_47)
def goalM : Nat := goal_47 &&& dom_47
def NN : Nat → Nat
  | 3 => 1
  | 4 => 5
  | 5 => 39
  | 6 => 24
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x2d5edff1
  | 4, 0 => 0xa01735d87ae1bc6c46fb31232efe58360f1fce07
  | 5, 0 => 0xfb879783ee021f3cd54d9339d4c9adb2cb027a71a3750db9a1c0b4b89f3b309b947e0d9e915d400188e2183d8888432e87d8949b8189bd3f71f40ace6fa9a6b367ae8f75666ec8955ba073fa5b61388b54e97e2454a1ee0b5462b29c4fada6a442c1d77f42829c103b21efc1286448961b2929df14d0ad7313645f700f1fce070afba44c08214818040f1dd303b0c7d70335d817029f811a014109c2
  | 6, 0 => 0xe505bdfaa1c0b4b8a1712e8ba12a17a39f39fa5295fc1c0b8c5e12728888432e7ea52a9a7445a6b56b7180a36949f7d6686e9bda6594bfe25ba073fa5b61388b55c13d204d7877b92fef2b28270b03de160058940f1fce070da784ce08214818
  | 7, 0 => 0xf1fce07
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x88880000888800000000000000000000000000000000000000000000000000005555000055550000000000000000000000000000000000000000000000000000333300003333000000000000000000000000000000000000000000000000000033330000000000000000000000000000000000000000000000000000000000000f0f00000f0f000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000000000000000000000000000000000003333
  | 0, 1 => 0xcccc000000000000000000000000000000000000000000000000000000000000cc000000cc000000000000000000000000000000000000000000000000000000c8c80000c8c80000000000000000000000000000000000000000000000000000c0c00000c0c00000000000000000000000000000000000000000000000000000aaaa0000aaaa0000000000000000000000000000000000000000000000000000aaaa000000000000000000000000000000000000000000000000000000000000aa000000aa000000000000000000000000000000000000000000000000000000a0a00000a0a0
  | 0, 2 => 0xfa000000fa000000000000000000000000000000000000000000000000000000f8f80000f8f80000000000000000000000000000000000000000000000000000f0f00000f0f00000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000f0000000f0000000000000000000000000000000000000000000000000000000eeee0000eeee0000000000000000000000000000000000000000000000000000cccc0000ffff0000000000000000000000000000000000000000000000000000cccc0000cccc
  | 0, 3 => 0xffcc0000ffcc0000000000000000000000000000000000000000000000000000ffaa0000ffaa0000000000000000000000000000000000000000000000000000ffaa000000000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000ff000000f0000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000fcfc0000fcfc0000000000000000000000000000000000000000000000000000fcfc0000cccc
  | 0, 4 => 0xffff0000cccc0000000000000000000000000000000000000000000000000000ffff0000c0c00000000000000000000000000000000000000000000000000000ffff0000aaaa0000000000000000000000000000000000000000000000000000ffff000088880000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000fffc0000cccc0000000000000000000000000000000000000000000000000000fff00000fff00000000000000000000000000000000000000000000000000000fff000000000
  | 0, 5 => 0xffff0000ff000000000000000000000000000000000000000000000000000000ffff0000f0f0
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x224cb3
  | 4, 0, 0 => 0x6d440b40204d02d0089c54b40277162d2371540b5
  | 5, 0, 0 => 0x2385340b502340b0c25023550182502371534b502471540b501c54b14150277dc54b50235d540b502371540b5023795409502771540b501d71540b502969540b502371640b502671540b501c54b1445
  | 5, 0, 1 => 0x8dc4d02c8602071540b50277153cb501540b08150237152c5501c5502c450277152c55023715487502354b14250237d538b501c55140b50237102c3502371540650236d540b50277102c350277154065
  | 5, 0, 2 => 0x1c5502c0501c550181502571540a502371518550277152c7502371854b501c5502c15
  | 6, 0, 0 => 0x8dc5502c168de71540b68dc55030b68e171540b68dc55340b68dc5503cb60237102c3502371540658dc5502c568dc5502c66a2371540b696371540b68dc69540b602371540b58dc5502c2602771540b5
  | 6, 0, 1 => 0x9e371540b601c5502c158dc5502c868dc55240b68dc5502c768dc65540b68dc5502ca60237152c55
  | 7, 0, 0 => 0x2371540b5
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 22
  | 4 => 34
  | 5 => 40
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
  | 0, 0 => 0x7fc7c6200000000000000000000000000000000000000000000000000000000019bf39d00000000000000000000000000000000000000000000000000000000019b80000000000000000000000000000000000000000000000000000000000007878f8300000000000000000000000000000000000000000000000000000000007f807f0000000000000000000000000000000000000000000000000000000000007fff000000000000000000000000000000000000000000000000000000000000739d
  | 0, 1 => 0x66400000000000000000000000000000000000000000000000000000000000006000c0000000000000000000000000000000000000000000000000000000000006000600000000000000000000000000000000000000000000000000000000000600060000000000000000000000000000000000000000000000000000000000003839d00000000000000000000000000000000000000000000000000000000000380000000000000000000000000000000000000000000000000000000000000000380000000000000000000000000000000000000000000000000000000000000001c
  | 0, 2 => 0x7380000000000000000000000000000000000000000000000000000000000078707c000000000000000000000000000000000000000000000000000000000078707c000000000000000000000000000000000000000000000000000000000078000000000000000000000000000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000000000000006678fff0000000000000000000000000000000000000000000000000000000006647fff0000000000000000000000000000000000000000000000000000000006640c62
  | 0, 3 => 0x7e47fe2000000000000000000000000000000000000000000000000000000000783ff9d00000000000000000000000000000000000000000000000000000000078380000000000000000000000000000000000000000000000000000000000007807f800000000000000000000000000000000000000000000000000000000007807000000000000000000000000000000000000000000000000000000000000780000000000000000000000000000000000000000000000000000000000000067c7c7e00000000000000000000000000000000000000000000000000000000067c0c62
  | 0, 4 => 0x7ff8c620000000000000000000000000000000000000000000000000000000007ff80600000000000000000000000000000000000000000000000000000000007ff839d0000000000000000000000000000000000000000000000000000000007ff80000000000000000000000000000000000000000000000000000000000007ff80000000000000000000000000000000000000000000000000000000000007fc0c620000000000000000000000000000000000000000000000000000000007f87ffc0000000000000000000000000000000000000000000000000000000007f80000
  | 0, 5 => 0x7ffff800000000000000000000000000000000000000000000000000000000007fff07c
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x22484a7000000000000000000000000000000000000000000000000000000000550684000000000000000000000000000000000000000000000000000000000019b531800000000000000000000000000000000000000000000000000000000019b4210000000000000000000000000000000000000000000000000000000000286868300000000000000000000000000000000000000000000000000000000002d80370000000000000000000000000000000000000000000000000000000000003def0000000000000000000000000000000000000000000000000000000000001108
  | 0, 1 => 0x66480000000000000000000000000000000000000000000000000000000000006402cc0000000000000000000000000000000000000000000000000000000000664ace700000000000000000000000000000000000000000000000000000000046028640000000000000000000000000000000000000000000000000000000002af97bf0000000000000000000000000000000000000000000000000000000002af82100000000000000000000000000000000000000000000000000000000002821788000000000000000000000000000000000000000000000000000000000029113c
  | 0, 2 => 0x7d27fc800000000000000000000000000000000000000000000000000000000077dfdff000000000000000000000000000000000000000000000000000000000579797c000000000000000000000000000000000000000000000000000000000579401000000000000000000000000000000000000000000000000000000000055079480000000000000000000000000000000000000000000000000000000006efbfff000000000000000000000000000000000000000000000000000000000664bdef000000000000000000000000000000000000000000000000000000000664ace7
  | 0, 3 => 0x7f6ffef0000000000000000000000000000000000000000000000000000000007ffffff0000000000000000000000000000000000000000000000000000000007ffc2100000000000000000000000000000000000000000000000000000000007d27fc80000000000000000000000000000000000000000000000000000000007d27b480000000000000000000000000000000000000000000000000000000007d2420000000000000000000000000000000000000000000000000000000000077dfdff00000000000000000000000000000000000000000000000000000000077decf7
  | 0, 4 => 0x7ffeef70000000000000000000000000000000000000000000000000000000007ffea740000000000000000000000000000000000000000000000000000000007ffd7bf0000000000000000000000000000000000000000000000000000000007ffc6b70000000000000000000000000000000000000000000000000000000007ffc2100000000000000000000000000000000000000000000000000000000007ffeef70000000000000000000000000000000000000000000000000000000007fb7ffc0000000000000000000000000000000000000000000000000000000007fb4210
  | 0, 5 => 0x7ffffd80000000000000000000000000000000000000000000000000000000007fffb7c
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 42 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 42 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 42 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 42 then wireAt i else 0
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_47 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_47 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
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
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := z4_0
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
  scr dom_47 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_47 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_47 roots_47 goal_47 8 := by
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

theorem low_47 : Lower dom_47 roots_47 goal_47 8 := S_47.noCircuit

namespace S_45
def pairsG : List (Nat × Nat) := [(5, 13), (5, 37), (9, 13), (9, 41), (12, 13), (12, 44), (33, 37), (33, 41), (36, 37), (36, 44), (40, 41), (40, 44)]
def r1sG : List Nat := [5, 5, 9, 9, 12, 12, 33, 33, 36, 36, 40, 40]
def r2sG : List Nat := [13, 37, 13, 41, 13, 44, 37, 41, 37, 44, 41, 44]
def mpG : Nat := 0xfff
def pool6G : List Nat := [9917635831053, 36322624736553, 36305512238373, 13216221242637, 39604097649957, 13233468221709, 39634044521772, 39724826503461]
def xsM : List Nat := roots_45.map (· &&& dom_45)
def goalM : Nat := goal_45 &&& dom_45
def NN : Nat → Nat
  | 3 => 3
  | 4 => 6
  | 5 => 5
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x96d781171e5672ca00c7ba44
  | 4, 0 => 0x96d781172b8cc4241fe7c84a1ba39e6d18fb680e0a8683ff
  | 5, 0 => 0x96d7811740f14df32b55f9c60a8683ff01745ddd
  | 6, 0 => 0x96d78117
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x3030000030300000000000000000000000000000000000000000000000000000300000003000000000000000000000000000000000000000000000000000000022220000222200000000000000000000000000000000000000000000000000002222000000000000000000000000000000000000000000000000000000000000220000002200000000000000000000000000000000000000000000000000000020200000202000000000000000000000000000000000000000000000000000000033000000330000000000000000000000000000000000000000000000000000000000003333
  | 0, 1 => 0x3333000030300000000000000000000000000000000000000000000000000000333300002222000000000000000000000000000000000000000000000000000033330000000000000000000000000000000000000000000000000000000000003322000000000000000000000000000000000000000000000000000000000000330000003300
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xa8754a632409733
  | 4, 0, 0 => 0xa8754075104a874350987540b8744087504
  | 5, 0, 0 => 0xa8754ca8755a87515087504a87535
  | 6, 0, 0 => 0xa8754
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 20
  | 4 => 24
  | 5 => 24
  | 6 => 20
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 4 0) :: stateWires n (ids >>> 4)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x333000000000000000000000000000000000000000000000000000000000000003000000000000000000000000000000000000000000000000000000000000000cf00000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000000c000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000000000000000000000000000000000003c3000000000000000000000000000000000000000000000000000000000000003f
  | 0, 1 => 0xff30000000000000000000000000000000000000000000000000000000000000fcf0000000000000000000000000000000000000000000000000000000000000fc00000000000000000000000000000000000000000000000000000000000000cc00000000000000000000000000000000000000000000000000000000000000c3c
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xb770000000000000000000000000000000000000000000000000000000000000a3500000000000000000000000000000000000000000000000000000000000005df00000000000000000000000000000000000000000000000000000000000005ca000000000000000000000000000000000000000000000000000000000000049d000000000000000000000000000000000000000000000000000000000000015700000000000000000000000000000000000000000000000000000000000001420000000000000000000000000000000000000000000000000000000000000015
  | 0, 1 => 0xfff0000000000000000000000000000000000000000000000000000000000000fff0000000000000000000000000000000000000000000000000000000000000fea0000000000000000000000000000000000000000000000000000000000000fea0000000000000000000000000000000000000000000000000000000000000ebd
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 13 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 13 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 13 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 13 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 4 0) :: stateWiresD n (ids >>> 4)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 4 0) :: stateWiresS n (ids >>> 4)
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 4 0 (NN s)
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_45 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_45 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_45 == dom_45) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_45 goalM u ys) : RunD dom_45 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_45 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 3 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 3 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 3 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 6 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 6 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 6 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 5 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 5 0 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 5 → Z 5 i = true := z5_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := z6_0
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_45 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_45 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_45 roots_45 goal_45 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_45 goal_45 := by
    have h0 : isConstB dom_45 goal_45 = false := by decide +kernel
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

end S_45

theorem low_45 : Lower dom_45 roots_45 goal_45 7 := S_45.noCircuit

namespace S_55_8
def pairsG : List (Nat × Nat) := [(9, 11), (9, 13), (9, 41), (10, 11), (10, 14), (10, 26), (12, 13), (12, 14), (12, 28), (12, 44), (24, 26), (24, 28), (25, 27), (25, 29), (25, 57), (40, 41), (40, 44), (42, 43), (42, 46), (42, 58), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [9, 9, 9, 10, 10, 10, 12, 12, 12, 12, 24, 24, 25, 25, 25, 40, 40, 42, 42, 42, 56, 56, 56]
def r2sG : List Nat := [11, 13, 41, 11, 14, 26, 13, 14, 28, 44, 26, 28, 27, 29, 57, 41, 44, 43, 46, 58, 57, 58, 60]
def mpG : Nat := 0x7fffff
def pool6G : List Nat := [13237241056014, 13232962931469, 26439988153884, 26431431904794, 44019324030249]
def xsM : List Nat := roots_55_8.map (· &&& dom_55_8)
def goalM : Nat := goal_55_8 &&& dom_55_8
def NN : Nat → Nat
  | 4 => 1
  | 5 => 5
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xc22d231e
  | 5, 0 => 0xc9b32fd6c22d231eb2baec477a5e756527f195c0
  | 6, 0 => 0xc22d231e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00aa00ff00aa00000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000cc00cc00cc00cc00000000000000000000000000000000000000000000000000aa00aa00aa00aa0000000000000000000000000000000000000000000000000055005500550055000000000000000000000000000000000000000000000000000f000f000f000f0000000000000000000000000000000000000000000000000000000000ff00ff00
  | 0, 1 => 0xff00ff0000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x865435
  | 5, 0, 0 => 0x864315865435875435654305865425
  | 6, 0, 0 => 0x865435
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 24
  | 5 => 24
  | 6 => 24
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 4 0) :: stateWires n (ids >>> 4)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x707c070000000000000000000000000000000000000000000000000000000000707c0000000000000000000000000000000000000000000000000000000000000003c000000000000000000000000000000000000000000000000000000000000e0038000000000000000000000000000000000000000000000000000000000000700700000000000000000000000000000000000000000000000000000000007f8ff800000000000000000000000000000000000000000000000000000000007ffc3f0000000000000000000000000000000000000000000000000000000000007fff
  | 0, 1 => 0x7f8000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x7afd6f0000000000000000000000000000000000000000000000000000000000787d200000000000000000000000000000000000000000000000000000000000452bd200000000000000000000000000000000000000000000000000000000002e14b9000000000000000000000000000000000000000000000000000000000012f04f00000000000000000000000000000000000000000000000000000000006d0fb000000000000000000000000000000000000000000000000000000000003ad42d0000000000000000000000000000000000000000000000000000000000003dfb
  | 0, 1 => 0x7fc204
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 9 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 9 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 9 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 9 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 4 0) :: stateWiresD n (ids >>> 4)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 4 0) :: stateWiresS n (ids >>> 4)
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 4 0 (NN s)
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_55_8 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_55_8 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_55_8 == dom_55_8) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_55_8 goalM u ys) : RunD dom_55_8 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_55_8 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
private theorem z5_0 : ∀ i, 0 ≤ i → i < 5 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 5 0 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 5 → Z 5 i = true := z5_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := z6_0
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_55_8 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_55_8 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_55_8 roots_55_8 goal_55_8 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_55_8 goal_55_8 := by
    have h0 : isConstB dom_55_8 goal_55_8 = false := by decide +kernel
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

end S_55_8

theorem low_55_8 : Lower dom_55_8 roots_55_8 goal_55_8 7 := S_55_8.noCircuit

namespace S_55
def pairsG : List (Nat × Nat) := [(1, 3), (2, 3), (2, 18), (5, 7), (5, 37), (6, 7), (6, 22), (16, 18), (17, 19), (17, 49), (20, 22), (21, 23), (21, 53), (33, 35), (33, 37), (33, 49), (34, 35), (34, 50), (36, 37), (38, 39), (38, 54), (48, 49), (48, 50), (52, 53), (52, 54)]
def r1sG : List Nat := [1, 2, 2, 5, 5, 6, 6, 16, 17, 17, 20, 21, 21, 33, 33, 33, 34, 34, 36, 38, 38, 48, 48, 52, 52]
def r2sG : List Nat := [3, 3, 18, 7, 37, 7, 22, 18, 19, 49, 22, 23, 53, 35, 37, 49, 35, 50, 37, 39, 54, 49, 50, 53, 54]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := [2204126745091, 17601332839186, 5507022918147, 36293282173443]
def xsM : List Nat := roots_55.map (· &&& dom_55)
def goalM : Nat := goal_55 &&& dom_55
def NN : Nat → Nat
  | 4 => 1
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x47baa070
  | 5, 0 => 0x47baa070
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00ff0000000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000cc00cc00cc00cc00000000000000000000000000000000000000000000000000aa00aa00aa00aa
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
  | 0, 0 => 0x1ffe0000000000000000000000000000000000000000000000000000000000001e01f8000000000000000000000000000000000000000000000000000000000019c1c7800000000000000000000000000000000000000000000000000000000001b0066000000000000000000000000000000000000000000000000000000000000fb19
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x1fff2100000000000000000000000000000000000000000000000000000000001f29fc400000000000000000000000000000000000000000000000000000000019c5c7800000000000000000000000000000000000000000000000000000000015b2def0000000000000000000000000000000000000000000000000000000000adfb3b
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_55 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_55 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := []
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
  scr dom_55 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_55 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_55 roots_55 goal_55 6 := by
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

theorem low_55 : Lower dom_55 roots_55 goal_55 6 := S_55.noCircuit

namespace S_62_1
def pairsG : List (Nat × Nat) := [(1, 3), (5, 7), (5, 13), (5, 37), (9, 11), (9, 13), (9, 41), (17, 19), (17, 49), (21, 23), (21, 29), (21, 53), (25, 27), (25, 29), (25, 57), (33, 35), (33, 37), (33, 41), (33, 49)]
def r1sG : List Nat := [1, 5, 5, 5, 9, 9, 9, 17, 17, 21, 21, 21, 25, 25, 25, 33, 33, 33, 33]
def r2sG : List Nat := [3, 7, 13, 37, 11, 13, 41, 19, 49, 23, 29, 53, 27, 29, 57, 35, 37, 41, 49]
def mpG : Nat := 0x7ffff
def pool6G : List Nat := [9917635831053, 36322624736553, 36305512238373]
def xsM : List Nat := roots_62_1.map (· &&& dom_62_1)
def goalM : Nat := goal_62_1 &&& dom_62_1
def NN : Nat → Nat
  | 4 => 1
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x4ced5003
  | 5, 0 => 0x4ced5003
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xaaaaaaaa00000000000000000000000000000000000000000000000000000000aaaa0000aaaa0000000000000000000000000000000000000000000000000000aa00aa00aa00aa00000000000000000000000000000000000000000000000000a0a0a0a0a0a0a0a00000000000000000000000000000000000000000000000008888888888888888
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
  | 0, 0 => 0x780000000000000000000000000000000000000000000000000000000000000007f8000000000000000000000000000000000000000000000000000000000000070700000000000000000000000000000000000000000000000000000000000000e0e0000000000000000000000000000000000000000000000000000000000000000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x7c9480000000000000000000000000000000000000000000000000000000000047f8000000000000000000000000000000000000000000000000000000000000274740000000000000000000000000000000000000000000000000000000000012e2e0000000000000000000000000000000000000000000000000000000000009293
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_62_1 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_62_1 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_62_1 == dom_62_1) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_62_1 goalM u ys) : RunD dom_62_1 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_62_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_62_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_62_1 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_62_1 roots_62_1 goal_62_1 6 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_62_1 goal_62_1 := by
    have h0 : isConstB dom_62_1 goal_62_1 = false := by decide +kernel
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

end S_62_1

theorem low_62_1 : Lower dom_62_1 roots_62_1 goal_62_1 6 := S_62_1.noCircuit

namespace S_62
def pairsG : List (Nat × Nat) := [(2, 18), (6, 14), (6, 22), (10, 14), (10, 26), (12, 14), (12, 28), (12, 44), (16, 18), (20, 22), (20, 28), (24, 26), (24, 28), (34, 50), (36, 44), (38, 46), (38, 54), (40, 44), (42, 46), (42, 58), (48, 50), (52, 54), (52, 60), (56, 58), (56, 60)]
def r1sG : List Nat := [2, 6, 6, 10, 10, 12, 12, 12, 16, 20, 20, 24, 24, 34, 36, 38, 38, 40, 42, 42, 48, 52, 52, 56, 56]
def r2sG : List Nat := [18, 14, 22, 14, 26, 14, 28, 44, 18, 22, 28, 26, 28, 50, 44, 46, 54, 44, 46, 58, 50, 54, 60, 58, 60]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := [13202999742990, 22041874009628, 13237493699086]
def xsM : List Nat := roots_62.map (· &&& dom_62)
def goalM : Nat := goal_62 &&& dom_62
def NN : Nat → Nat
  | 4 => 2
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xf0e4337fa91103de
  | 5, 0 => 0xa91103de
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x555555550000000000000000000000000000000000000000000000000000000055550000555500000000000000000000000000000000000000000000000000005500550055005500000000000000000000000000000000000000000000000000505050505050505000000000000000000000000000000000000000000000000050005000500050000000000000000000000000000000000000000000000000004444444444444444
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x584258d05
  | 5, 0, 0 => 0x58d05
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
  | 0, 0 => 0x1ffe0000000000000000000000000000000000000000000000000000000000001f01f0000000000000000000000000000000000000000000000000000000000018e18f8000000000000000000000000000000000000000000000000000000000061c6e600000000000000000000000000000000000000000000000000000000000000e000000000000000000000000000000000000000000000000000000000000da01f
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x1ffe0800000000000000000000000000000000000000000000000000000000001f93f550000000000000000000000000000000000000000000000000000000001cedcfa000000000000000000000000000000000000000000000000000000000167d6ee000000000000000000000000000000000000000000000000000000000146d4ea0000000000000000000000000000000000000000000000000000000000bdab3f
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_62 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_62 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
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

namespace S_31
def pairsG : List (Nat × Nat) := [(1, 3), (2, 3), (2, 18), (5, 7), (5, 13), (6, 7), (6, 14), (6, 22), (9, 11), (9, 13), (10, 11), (10, 14), (10, 26), (12, 13), (12, 14), (12, 28), (16, 18), (17, 19), (20, 22), (20, 28), (21, 23), (21, 29), (24, 26), (24, 28), (25, 27), (25, 29)]
def r1sG : List Nat := [1, 2, 2, 5, 5, 6, 6, 6, 9, 9, 10, 10, 10, 12, 12, 12, 16, 17, 20, 20, 21, 21, 24, 24, 25, 25]
def r2sG : List Nat := [3, 3, 18, 7, 13, 7, 14, 22, 11, 13, 11, 14, 26, 13, 14, 28, 18, 19, 22, 28, 23, 29, 26, 28, 27, 29]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [2203520470275, 13219994075918]
def xsM : List Nat := roots_31.map (· &&& dom_31)
def goalM : Nat := goal_31 &&& dom_31
def NN : Nat → Nat
  | 3 => 1
  | 4 => 3
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xb521cb1d
  | 4, 0 => 0xac05225e3b109490261658eb
  | 5, 0 => 0xac05225e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffffaaaa00000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000cccccccc00000000000000000000000000000000000000000000000000000000aaaaaaaa
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x1913
  | 4, 0, 0 => 0x16321468ca0a884
  | 5, 0, 0 => 0x58c85
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 13
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
  | 0, 0 => 0x3ff03190000000000000000000000000000000000000000000000000000000003ff00000000000000000000000000000000000000000000000000000000000003c0ff0000000000000000000000000000000000000000000000000000000000003ce0f8000000000000000000000000000000000000000000000000000000000000e0000000000000000000000000000000000000000000000000000000000000001ce60000000000000000000000000000000000000000000000000000000003320319
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3ffb7bf0000000000000000000000000000000000000000000000000000000003ff90840000000000000000000000000000000000000000000000000000000003e8ff500000000000000000000000000000000000000000000000000000000002bceaf80000000000000000000000000000000000000000000000000000000002a8ea500000000000000000000000000000000000000000000000000000000001575def000000000000000000000000000000000000000000000000000000000332273b
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 7 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 7 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 7 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 7 then wireAt i else 0
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_31 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_31 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
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
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := z4_0
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
  scr dom_31 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_31 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_31 roots_31 goal_31 6 := by
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

theorem low_31 : Lower dom_31 roots_31 goal_31 6 := S_31.noCircuit

namespace S_23_32
def pairsG : List (Nat × Nat) := [(33, 35), (33, 37), (33, 49), (34, 35), (34, 50), (36, 37), (38, 39), (38, 54), (48, 49), (48, 50), (52, 53), (52, 54)]
def r1sG : List Nat := [33, 33, 33, 34, 34, 36, 38, 38, 48, 48, 52, 52]
def r2sG : List Nat := [35, 37, 49, 35, 50, 37, 39, 54, 49, 50, 53, 54]
def mpG : Nat := 0xfff
def pool6G : List Nat := [37525937860899, 52918865765169]
def xsM : List Nat := roots_23_32.map (· &&& dom_23_32)
def goalM : Nat := goal_23_32 &&& dom_23_32
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xaccce520
  | 4, 0 => 0xaccce520
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00000000000000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000cc00cc0000000000000000000000000000000000000000000000000000000000aa00aa00000000
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
  | 0, 0 => 0xf000000000000000000000000000000000000000000000000000000000000000ce000000000000000000000000000000000000000000000000000000000000000d80000000000000000000000000000000000000000000000000000000000000007
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xf940000000000000000000000000000000000000000000000000000000000000ce20000000000000000000000000000000000000000000000000000000000000ad9000000000000000000000000000000000000000000000000000000000000056f
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_23_32 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_23_32 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_23_32 == dom_23_32) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_23_32 goalM u ys) : RunD dom_23_32 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_23_32 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_23_32 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_23_32 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_23_32 roots_23_32 goal_23_32 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_23_32 goal_23_32 := by
    have h0 : isConstB dom_23_32 goal_23_32 = false := by decide +kernel
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

end S_23_32

theorem low_23_32 : Lower dom_23_32 roots_23_32 goal_23_32 5 := S_23_32.noCircuit

namespace S_51
def pairsG : List (Nat × Nat) := [(1, 3), (2, 3), (2, 18), (16, 18), (17, 19), (17, 49), (33, 35), (33, 49), (34, 35), (34, 50), (48, 49), (48, 50)]
def r1sG : List Nat := [1, 2, 2, 16, 17, 17, 33, 33, 34, 34, 48, 48]
def r2sG : List Nat := [3, 3, 18, 18, 19, 49, 35, 49, 35, 50, 49, 50]
def mpG : Nat := 0xfff
def pool6G : List Nat := [17601332839186, 36293282173443]
def xsM : List Nat := roots_51.map (· &&& dom_51)
def goalM : Nat := goal_51 &&& dom_51
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x6ba3d11
  | 4, 0 => 0x6ba3d11
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf000f00000000000000000000000000000000000000000000000000000000000f0000000f0000000000000000000000000000000000000000000000000000000c000c000c000c000000000000000000000000000000000000000000000000000a000a000a000a
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
  | 0, 0 => 0xfc00000000000000000000000000000000000000000000000000000000000000c38000000000000000000000000000000000000000000000000000000000000030600000000000000000000000000000000000000000000000000000000000000f1
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfe00000000000000000000000000000000000000000000000000000000000000ebc0000000000000000000000000000000000000000000000000000000000000b5f00000000000000000000000000000000000000000000000000000000000005f3
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_51 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_51 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_51 == dom_51) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_51 goalM u ys) : RunD dom_51 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_51 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_51 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_51 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_51 roots_51 goal_51 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_51 goal_51 := by
    have h0 : isConstB dom_51 goal_51 = false := by decide +kernel
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

end S_51

theorem low_51 : Lower dom_51 roots_51 goal_51 5 := S_51.noCircuit

namespace S_46_1
def pairsG : List (Nat × Nat) := [(1, 3), (5, 7), (5, 13), (5, 37), (9, 11), (9, 13), (9, 41), (33, 35), (33, 37), (33, 41)]
def r1sG : List Nat := [1, 5, 5, 5, 9, 9, 9, 33, 33, 33]
def r2sG : List Nat := [3, 7, 13, 37, 11, 13, 41, 35, 37, 41]
def mpG : Nat := 0x3ff
def pool6G : List Nat := [9917635831053]
def xsM : List Nat := roots_46_1.map (· &&& dom_46_1)
def goalM : Nat := goal_46_1 &&& dom_46_1
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x3fdd6141
  | 4, 0 => 0x3fdd6141
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xaaaa000000000000000000000000000000000000000000000000000000000000aa000000aa000000000000000000000000000000000000000000000000000000a0a00000a0a00000000000000000000000000000000000000000000000000000888800008888
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_46_1 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_46_1 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_46_1 == dom_46_1) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_46_1 goalM u ys) : RunD dom_46_1 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_46_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_46_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_46_1 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_46_1 roots_46_1 goal_46_1 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_46_1 goal_46_1 := by
    have h0 : isConstB dom_46_1 goal_46_1 = false := by decide +kernel
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

end S_46_1

theorem low_46_1 : Lower dom_46_1 roots_46_1 goal_46_1 5 := S_46_1.noCircuit

namespace S_15
def pairsG : List (Nat × Nat) := [(1, 3), (2, 3), (5, 7), (5, 13), (6, 7), (6, 14), (9, 11), (9, 13), (10, 11), (10, 14), (12, 13), (12, 14)]
def r1sG : List Nat := [1, 2, 5, 5, 6, 6, 9, 9, 10, 10, 12, 12]
def r2sG : List Nat := [3, 3, 7, 13, 7, 14, 11, 13, 11, 14, 13, 14]
def mpG : Nat := 0xfff
def pool6G : List Nat := [2203520470275]
def xsM : List Nat := roots_15.map (· &&& dom_15)
def goalM : Nat := goal_15 &&& dom_15
def NN : Nat → Nat
  | 3 => 2
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xe00b4f86a8d11512
  | 4, 0 => 0xa8d11512
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00000000000000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000f000000000000000000000000000000000000000000000000000000000000000cccc000000000000000000000000000000000000000000000000000000000000aaaa
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x8838c84
  | 4, 0, 0 => 0x8c84
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
  | 0, 0 => 0xfc00000000000000000000000000000000000000000000000000000000000000c3c0000000000000000000000000000000000000000000000000000000000000c00000000000000000000000000000000000000000000000000000000000000033200000000000000000000000000000000000000000000000000000000000000cd
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfe80000000000000000000000000000000000000000000000000000000000000ebc0000000000000000000000000000000000000000000000000000000000000ea80000000000000000000000000000000000000000000000000000000000000b7700000000000000000000000000000000000000000000000000000000000005df
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

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
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

namespace S_23_8
def pairsG : List (Nat × Nat) := [(9, 11), (9, 13), (10, 11), (10, 14), (10, 26), (12, 13), (12, 14), (12, 28), (24, 26), (24, 28), (25, 27), (25, 29)]
def r1sG : List Nat := [9, 9, 10, 10, 10, 12, 12, 12, 24, 24, 25, 25]
def r2sG : List Nat := [11, 13, 11, 14, 26, 13, 14, 28, 26, 28, 27, 29]
def mpG : Nat := 0xfff
def pool6G : List Nat := [11033973230859, 13237241056014]
def xsM : List Nat := roots_23_8.map (· &&& dom_23_8)
def goalM : Nat := goal_23_8 &&& dom_23_8
def NN : Nat → Nat
  | 3 => 2
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x7711a2500526018
  | 4, 0 => 0x7711a25
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00aa0000000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000cc00cc0000000000000000000000000000000000000000000000000000000000aa00aa00
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x68841113
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
  | 0, 0 => 0xf030000000000000000000000000000000000000000000000000000000000000f0000000000000000000000000000000000000000000000000000000000000000e0000000000000000000000000000000000000000000000000000000000000001c0000000000000000000000000000000000000000000000000000000000000c03
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfb70000000000000000000000000000000000000000000000000000000000000f900000000000000000000000000000000000000000000000000000000000000aea000000000000000000000000000000000000000000000000000000000000055d0000000000000000000000000000000000000000000000000000000000000c27
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_23_8 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_23_8 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_23_8 == dom_23_8) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_23_8 goalM u ys) : RunD dom_23_8 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_23_8 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_23_8 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_23_8 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_23_8 roots_23_8 goal_23_8 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_23_8 goal_23_8 := by
    have h0 : isConstB dom_23_8 goal_23_8 = false := by decide +kernel
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

end S_23_8

theorem low_23_8 : Lower dom_23_8 roots_23_8 goal_23_8 5 := S_23_8.noCircuit

def isoMv_59_4 : List (Nat × Nat) := [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem low_59_4 : Lower dom_59_4 roots_59_4 goal_59_4 7 :=
  lower_iso isoMv_59_4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_55_8

def isoMv_59 : List (Nat × Nat) := [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem low_59 : Lower dom_59 roots_59 goal_59 6 :=
  lower_iso isoMv_59 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_55

def isoMv_27_32 : List (Nat × Nat) := [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem low_27_32 : Lower dom_27_32 roots_27_32 goal_27_32 5 :=
  lower_iso isoMv_27_32 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23_32

def isoMv_29_32 : List (Nat × Nat) := [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)]
theorem low_29_32 : Lower dom_29_32 roots_29_32 goal_29_32 5 :=
  lower_iso isoMv_29_32 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23_32

def isoMv_53_8 : List (Nat × Nat) := [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)]
theorem low_53_8 : Lower dom_53_8 roots_53_8 goal_53_8 5 :=
  lower_iso isoMv_53_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23_32

def isoMv_54_8 : List (Nat × Nat) := [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)]
theorem low_54_8 : Lower dom_54_8 roots_54_8 goal_54_8 5 :=
  lower_iso isoMv_54_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23_32

def isoMv_58_4 : List (Nat × Nat) := [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)]
theorem low_58_4 : Lower dom_58_4 roots_58_4 goal_58_4 5 :=
  lower_iso isoMv_58_4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23_32

def isoMv_60_1 : List (Nat × Nat) := [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)]
theorem low_60_1 : Lower dom_60_1 roots_60_1 goal_60_1 5 :=
  lower_iso isoMv_60_1 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23_32

namespace S_63
def pairsG : List (Nat × Nat) := [(1, 3), (2, 3), (2, 18), (5, 7), (5, 13), (5, 37), (6, 7), (6, 14), (6, 22), (9, 11), (9, 13), (9, 41), (10, 11), (10, 14), (10, 26), (12, 13), (12, 14), (12, 28), (12, 44), (16, 18), (17, 19), (17, 49), (20, 22), (20, 28), (21, 23), (21, 29), (21, 53), (24, 26), (24, 28), (25, 27), (25, 29), (25, 57), (33, 35), (33, 37), (33, 41), (33, 49), (34, 35), (34, 50), (36, 37), (36, 44), (38, 39), (38, 46), (38, 54), (40, 41), (40, 44), (42, 43), (42, 46), (42, 58), (48, 49), (48, 50), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [1, 2, 2, 5, 5, 5, 6, 6, 6, 9, 9, 9, 10, 10, 10, 12, 12, 12, 12, 16, 17, 17, 20, 20, 21, 21, 21, 24, 24, 25, 25, 25, 33, 33, 33, 33, 34, 34, 36, 36, 38, 38, 38, 40, 40, 42, 42, 42, 48, 48, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [3, 3, 18, 7, 13, 37, 7, 14, 22, 11, 13, 41, 11, 14, 26, 13, 14, 28, 44, 18, 19, 49, 22, 28, 23, 29, 53, 26, 28, 27, 29, 57, 35, 37, 41, 49, 35, 50, 37, 44, 39, 46, 54, 41, 44, 43, 46, 58, 49, 50, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0xffffffffffffff
def pool6G : List Nat := [2203520470275, 13215715951373, 9917635831053, 2204126745091, 9904396832003, 22041874009628, 13237241053966, 9905003106819, 11000353460739, 13219994075918, 9905136800259, 18701096129027, 17600979144210, 18700844466962, 39604097649957, 36293282173443, 36322624736553, 36305512238373, 39634044521772, 27578541352205, 61624612621612, 57226499001644, 11021442426126, 36357102378033, 46321323868969, 36293348495875, 9921576701187, 36327775605251, 26439987629596, 39724321211173, 13220246721038, 13237493699086, 13238031618574, 11033973230866, 6618747768338, 26414252035602, 13220784640526, 46231584047886, 11033974148626, 37388498833923, 36322893172009, 36322893958441, 5506350320899, 52785704928018, 52918326788913, 37405745025539, 17635338882578, 36305780673829]
def xsM : List Nat := roots_63.map (· &&& dom_63)
def goalM : Nat := goal_63 &&& dom_63
def NN : Nat → Nat
  | 5 => 10
  | 6 => 108
  | 7 => 326
  | 8 => 171
  | 9 => 19
  | 10 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0xf5707479f28fe9bce4cfddd7d8a96787cfc2ba32c808d0e580193ab97fc330b676cc1efb4d98ccf2
  | 6, 0 => 0x6d71c6146ab2acb36a8772f969c67e6067aab8ca65413a11619ad28a610c61d95e2f68925b952b3e5925e7be589bb1105671018655768c7353fa289852718a374c644899494215ee43455e59432c804e42653ea041da886c3dbcc4c837994153378f09b936fc055d353a12a933f5780531d5f76d31c4a7fe3139f1ca2e790bb12d14afcc29c8f25a25e633af21ff61ca207676cd1ff4e8f61fc96eb01f11ce591ea1a8681e5a8e021e58a69c1e3b020619d5fa50176bcc7816197ff11549c839142ed5d313c71bfe12cc6ac611417f601089a571105e20a00f5271a70babdc27096e943807e935d4067c798606165d76049893e504773d450432137103190425
  | 6, 1 => 0xfcbac920fc64bf1df8cefd33f3175066e580cb8ae276b9c4e07d350ddffd3fe0d7a079b3d71e8632d5b1c12dd4e034e8d4b32340d2182f79cdf450dacdd148c7ca3a5b59c9880156c7cc907dc67def90b8e76ab4b7dce78eb4bafab6ab05838b9c7654239b848855980e6d3093733e7e919f4e7b8f2d3bee8a77e8548981eee78282f480815cecf580feb7d97e2b284f7ba3862e78e15845760c1e5f75413da6723b692c723aa6b46f3178236ecfff34
  | 7, 0 => 0x1d5319ea1d06d2eb1c193f401bc7d4b01a39c2a219f37e0719ba301a198e7f101962cf2818fdbc2117e4d13d17d6fff4176aac0017135e9f16c91dcd16b01e54160c7aef15f3a7e415776f9514c7c3fb14c15aa414affb971436a47012ddb4341280f92b1167b40d1144e41f109d1e43109410fb104862a50f3876680ecc23a60e7515ed0d613c800d50aa5b0c1e8e5d0b3c22580af197a60a81a3e10a7a552809eb25bd09b1e6820925d5bd09199978088078d607ff7b8107962ead0790b29f06519409062e761d06237d4e04ed297a04e7479104824cd4047b153d043213710389d21f02c7a83d028de01e023f5c5b02363de2019f361a01551783002d875e
  | 7, 1 => 0x416e9813412c1b3840e5429a40b724943f4622693f3bf5403e8cd15e3e444aad3e3a3ac43d727f8e3d0ec8b73c229a643b6f72873b3e76333a4fc2063a3b596f39e1752a39d3956d39964d573991a52538bbb164389cbe3637c7f0c9378e8a2e3778a28c36f47cbe36c5746f369e286b344f47aa33cd017f3380f3e431357ac630ddf49130ba24d830a485e0306c1f0a2e9b5e9e2bbea46f2a9ddf912a2ab54a29af2b6428a4a83e28174fe627d2a87727d2573727b3f541276fb0f9275dc4202750b4f626ad119125685a9d2520bf9123e65826232c6add21eaa96f204fb0ae1f15ac8f1ebb84a11e8f50351e01d3221df73f721daeb8c11d98daf11d85da9b
  | 7, 2 => 0x63fb6a7f63b27224624cd0cb621bcd5661117a3760b772cb5f35ba935f26c7b65f18482b5ef408b65e394d3c5dd08b735caf4aef5c3f74815bde0aeb5a859b9259952f0b59737dfd58e6c54658b40b8c583d5a595810d46d580e3478579b9d365707fb67565f733c56488c3a54a96c095467b4c65462936b53c0149953b908f952534f94509f54164fff2dd54e9a87094e8bd3f94e5372144d84259f4d2ff4d14b8c97694b83bc6a4b50406a4abd1d0b4aa02b774a95df4149dd9ff449a0b8ec496fc9e44943fc004868876b48683a63480eeebd47b76ea347703dcb471718c44705cf56466764c545a7f598457ae3f0449785304408d56743c1fcc9431f7df7
  | 7, 3 => 0x96d455ce949f308d92bb0e589280652690f610e68ffc867d8fa972eb8f80fc978f4a89288e7679718d1b84e689312aef88a4fc21884d6a8e88338d288816e94987de9c8a83fe99eb83e740ff81f6d6c280b3c20480ab0b5c7e704a887c170b2e7c140d477be9041f7b665f577a081d0b78a66659781ae916777ec2e97710f4407677504c751532dd74f8ca7a7406feac73170721730c5ff87158096d710997a570d94bd870607efa705155296fb8decd6eeb6aab6e8cbcc66e81dc4c6d32e2006c53f26c6c2229556be5d2566bba30316b3569ed6ac5c8b56a27cc6b6a08291469ca64976805cfb7657fa726649ea5e064610497641cb567641ca4e76407b8f1
  | 7, 4 => 0xf2d35972f2234673f1e2cc0dee71c1e8ee055e5bed0f7221ec164c1eebefca4beb66372beafba6c3e232c2d0dd6521e7dc37d8dfdbcabd8fdb4f33a9d9612da7d70a1d9bd70862e2d6d35949d53d3f77d4232686cfe29780cfbdece5ceddfab4cc47d1c0c68a317bc667cc40c5736c6ac3e2d77bc166fc71c1041042c088640abef0b2a0beb14ce4bd2fc437bc1a5d6dbc042ef7b7dce78eb436aa11b4309820b3c34070b2d95111b06379a0afe8b470af9abc18ab79c6cbab1a9a18aa1f6e87a994b72fa97aa236a8fde80ca70f3f44a34b2fb8a2f7e86ca27f4475a2465e8da13d7a12a02193399d33d63f9c96775d9c6afd179be41d5a98f4208d9832c626
  | 7, 5 => 0xfff37a59fe2b8d04fa8bcd18f9aef702f6f01bfdf582e6ac
  | 8, 0 => 0x3c38e0113c21f90f36c744ae3678c0eb366fa27235d89aaa34746a9f346540ce342cdee933d93c6b339be83032ba82ac3264f194315024ba3129ad3f302ca7772f790d942f1d68d52de85b922d90db782cf085992bcf9a012b81626d2a6cf07129c478db2964176b28a4a83e2838c79a272770732705880d26beaf6f26bb2fef265363bb261c309d2219ec0a21e9d24d21a1d26720292edb2014c6441ca0b1831ac4a36f17d6fff41415063f13b5da6d11d74806119811441004221f0f8898390f6b9a140f5c5cfb0e7e15130e7dd0190dfb96ef0df0bcbb0d9cbe430d9a92370d61f2fb0cabde0a0b41c7720acf09dd0a9628be0878675806b07a0306291d83
  | 8, 1 => 0x93f42b8d93602c469351acbb92278ab58f78512d8e7679718dce939b8c8386ea8c76bee98a81f0ca899b6c7288ede02886bb6894868cb42482d3eb99811023557fc0036d7bf0d33379e15a2879a4d76c76f0de33766385db75a74bbc749b988673227b8e727daf3d72739f54721cd8336e1ad9ba6e0cf9fd6dcfb1e76db8095f6cd622c66c4b6e04679d352a66fb4c9164f3896862a97e135cde0cce5a73054d56240dff54b47b9851e81d5151bf3f2b50c4b4ed500139404e7327324e2ce2974dc27b5b4c1e35cd4b02825d49e125c6498bdef948e9602746ba5dbb44cd758b43b425714365b3a94305883642815d8a4214fad14079af633d6d0b963cd7d7c2
  | 8, 2 => 0xffcceadcfaa130d0f9acd0faf8b72109f6e94291f32a1730f053c1fdec164c1ee7fca500e4763a0be3d420a8e2f02cffe1283faae11915d9dfdba1afdfb32b5bd9eccea3d96359b3d87f9952d58853adceecb93fc8d8951dc52f7576c2afde01c1c5a5bebe4be64fbc545819b837fe7bb59a84ddb3feb3cab02268afa9647ee6a840633ca494c22fa3f2435da16c4690a141bf77a00d2aa29b34b1219721f5ed965531e695a996be954adec7
  | 9, 0 => 0xf2854adfdd9de376c2afde01a6563cc3a1f16def9b34b1217e1a8a5676f0de33764e5f61705b5d9f5fbac6fd5cde0cce42b779a334064f6c1729918f1561a43a15527a690e7e151305169eb0
  | 10, 0 => 0x42b779a3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x5fff00005fff00000000000000000000000000000000000000000000000000005f5f00005f5f000000000000000000000000000000000000000000000000000055ff000055ff00000000000000000000000000000000000000000000000000005577000055770000000000000000000000000000000000000000000000000000555f0000555f000000000000000000000000000000000000000000000000000055550000555500000000000000000000000000000000000000000000000000000fff00000fff00000000000000000000000000000000000000000000000000000000ffffffff
  | 0, 1 => 0x333033303330333000000000000000000000000000000000000000000000000010101013333333300000000000000000000000000000000000000000000000000ff00ffffffffff00000000000000000000000000000000000000000000000000ff00ff00ff00ff00000000000000000000000000000000000000000000000000550055ffffffff000000000000000000000000000000000000000000000000005500553377337700000000000000000000000000000000000000000000000000330033333333330000000000000000000000000000000000000000000000000000ffff0000ffff
  | 0, 2 => 0x11111111111111110000000000000000000000000000000000000000000000000fff0fff0fff0fff0000000000000000000000000000000000000000000000000ff00ff00ff00ff00000000000000000000000000000000000000000000000000f5f0f5f0f5f0f5f0000000000000000000000000000000000000000000000000f0f0f0fffffffff0000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f00000000000000000000000000000000000000000000000005050505ffffffff0000000000000000000000000000000000000000000000000333033333333333
  | 0, 3 => 0x55555555000000000000000000000000000000000000000000000000000000005500550055005500000000000000000000000000000000000000000000000000505050505050505000000000000000000000000000000000000000000000000033333333333333330000000000000000000000000000000000000000000000001333133313331333000000000000000000000000000000000000000000000000113311333333333300000000000000000000000000000000000000000000000011331133113311330000000000000000000000000000000000000000000000001111111133333333
  | 0, 4 => 0xa0a0a0a0a0a0a0a0000000000000000000000000000000000000000000000000a0a0a0a000000000000000000000000000000000000000000000000000000000a000a000a000a0000000000000000000000000000000000000000000000000005f5f5f5f5f5f5f5f0000000000000000000000000000000000000000000000005a5a5a5a5a5a5a5a00000000000000000000000000000000000000000000000055ff55ff55ff55ff00000000000000000000000000000000000000000000000055555555ffffffff0000000000000000000000000000000000000000000000005555555555555555
  | 0, 5 => 0xafafafafafafafaf000000000000000000000000000000000000000000000000aaaaaaaaaaaaaaaa000000000000000000000000000000000000000000000000aaaaaaaa00000000000000000000000000000000000000000000000000000000aaaaaa00aaaaaa00000000000000000000000000000000000000000000000000aaaaa0a0aaaaa0a0000000000000000000000000000000000000000000000000aaa0aaa0aaa0aaa0000000000000000000000000000000000000000000000000aa00aa00aa00aa00000000000000000000000000000000000000000000000000a8a8a8a8a8a8a8a8
  | 0, 6 => 0xececececcccccccc000000000000000000000000000000000000000000000000eccceccceccceccc000000000000000000000000000000000000000000000000e0e0e0e0e0e0e0e0000000000000000000000000000000000000000000000000dddddddddddddddd000000000000000000000000000000000000000000000000cfcfcfcfcfcfcfcf000000000000000000000000000000000000000000000000ccffccffccffccff000000000000000000000000000000000000000000000000ccccccccffffffff000000000000000000000000000000000000000000000000cccccccccccccccc
  | 0, 7 => 0xf000f00000000000000000000000000000000000000000000000000000000000eeeeeeeeeeeeeeee000000000000000000000000000000000000000000000000eeeeeeeecccccccc000000000000000000000000000000000000000000000000eeeeeeee00000000000000000000000000000000000000000000000000000000eeeceeeceeeceeec000000000000000000000000000000000000000000000000eecceecceecceecc000000000000000000000000000000000000000000000000eecceecccccccccc000000000000000000000000000000000000000000000000ecececececececec
  | 0, 8 => 0xf0fff0fff0fff0ff000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000f0f0f000f0f0f000000000000000000000000000000000000000000000000000f0f0a0a0f0f0a0a0000000000000000000000000000000000000000000000000f0c0f0c0f0c0f0c0000000000000000000000000000000000000000000000000f0a0f0a0f0a0f0a0000000000000000000000000000000000000000000000000f000f000f000f000
  | 0, 9 => 0xfafafafaaaaaaaaa000000000000000000000000000000000000000000000000fafafafa00000000000000000000000000000000000000000000000000000000faaafaaafaaafaaa000000000000000000000000000000000000000000000000faaafaaaf000f000000000000000000000000000000000000000000000000000faaafaaaaaaaaaaa000000000000000000000000000000000000000000000000faaafaaa00000000000000000000000000000000000000000000000000000000fa00fa00fa00fa00000000000000000000000000000000000000000000000000f5f5f5f5f5f5f5f5
  | 0, 10 => 0xfcfcfcfccccccccc000000000000000000000000000000000000000000000000fcfcfcfc00000000000000000000000000000000000000000000000000000000fcccfcccfcccfccc000000000000000000000000000000000000000000000000fcccfccccccccccc000000000000000000000000000000000000000000000000fca8fca8fca8fca8000000000000000000000000000000000000000000000000fc00fc00fc00fc00000000000000000000000000000000000000000000000000fafafafafafafafa000000000000000000000000000000000000000000000000fafafafac8c8c8c8
  | 0, 11 => 0xff55ff5500000000000000000000000000000000000000000000000000000000ff0fff0fff0fff0f000000000000000000000000000000000000000000000000ff00ff00ff00ff00000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000ff00f000ff00f000000000000000000000000000000000000000000000000000fefefefecccccccc000000000000000000000000000000000000000000000000feccfeccfeccfecc000000000000000000000000000000000000000000000000fcfcfcfcfcfcfcfc
  | 0, 12 => 0xffccffccffccffcc000000000000000000000000000000000000000000000000ffccffcccccccccc000000000000000000000000000000000000000000000000ffaaffaaffaaffaa000000000000000000000000000000000000000000000000ffaaffaacc88cc88000000000000000000000000000000000000000000000000ffaaffaaaaaaaaaa000000000000000000000000000000000000000000000000ffaaffaa00000000000000000000000000000000000000000000000000000000ffaaf0a0ffaaf0a0000000000000000000000000000000000000000000000000ff55ff55ff55ff55
  | 0, 13 => 0xffff5555ffff5555000000000000000000000000000000000000000000000000ffff0f0fffff0f0f000000000000000000000000000000000000000000000000ffff00ffffff00ff000000000000000000000000000000000000000000000000ffff0000ffff0000000000000000000000000000000000000000000000000000fffcfffccccccccc000000000000000000000000000000000000000000000000fff0fff0fff0fff0000000000000000000000000000000000000000000000000fff0fff000000000000000000000000000000000000000000000000000000000ffeeffeecccccccc
  | 0, 14 => 0xffffaaaa00000000000000000000000000000000000000000000000000000000ffffaaa0ffffaaa0000000000000000000000000000000000000000000000000ffffaa88ffffaa88000000000000000000000000000000000000000000000000ffffaa00ffffaa00000000000000000000000000000000000000000000000000ffffaa0000000000000000000000000000000000000000000000000000000000ffffa0a0ffffa0a0000000000000000000000000000000000000000000000000ffffa0a0ffff0000000000000000000000000000000000000000000000000000ffffa000ffffa000
  | 0, 15 => 0xfffff0f0ffff0000000000000000000000000000000000000000000000000000fffff0f000000000000000000000000000000000000000000000000000000000fffff0a0fffff0a0000000000000000000000000000000000000000000000000fffff000fffff000000000000000000000000000000000000000000000000000fffff000ffff0000000000000000000000000000000000000000000000000000ffffeeccffffeecc000000000000000000000000000000000000000000000000ffffaaaaffffaaaa000000000000000000000000000000000000000000000000ffffaaaaffff0000
  | 1, 0 => 0xffffffffcccccccc000000000000000000000000000000000000000000000000ffffffff00000000000000000000000000000000000000000000000000000000ffffff00ffffff00000000000000000000000000000000000000000000000000ffffff00ffff0000000000000000000000000000000000000000000000000000ffffff0000000000000000000000000000000000000000000000000000000000fffff0f0fffff0f0
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x846c5d231c5857640302e5845d3023085846c2e1c1557640302e00584302e15085856c403b2e58440302e035846c30201558476402e1c5
  | 6, 0, 0 => 0x725d46302000600856c65302912600846c5d54462060084745d46201c600846c5d462e10600846c6a302016600845d46302e076006c40302e2a006005d5130270800600846c5d302014600845d46302b026006c5d201c120060085745d302e126006c6546291c00600845d46302e066005d46302e05006
  | 6, 0, 1 => 0x846c5d462e1a60084746546291c600855d46302e056006c665d463d2e600856c46382e0c60000847640302e500846c6b40302e600845d463020056006c635d302d12600755d46302e00600845d302e1206600846c5d462e1b6006c6046301e006006c31302e120c60084766c40302e6006c685d302e126
  | 6, 0, 2 => 0x765d46302e00600845d46302e04600856c5d463a20600745d4631302e6006c49462e1c006006c625d2e1c126006c5d46302e0a600846546302905600846c69402e1c60085725d4630206006c5d462e1c11600847b5d462e1c600845d462e1c066004946302e0800600625d302e1208600856c40302e2a6
  | 6, 0, 3 => 0x845d302e120560084715d462e1c6004630200c0800600846c5d2e1c146006c3020120c00600795d46302c00600846a302e160860084725d5138306008465302912086006c5d4a302e12600845d302e1408600846c403b302e6006c5d413020006008472462e1c0c6006c5d313020126006c5c4c46302e6
  | 6, 0, 4 => 0x846c6546221c600844640302e05600856c3020120c600846c402e2a1c600845d46362e08600847446402e1c6008465463022086006c5d4630200b6006c5130270c006008440302e2a08600725d462e1c006006c6a40302000600846c6a2e1c16600856c5d462e1960085765d46302e600846c65291c126
  | 6, 0, 5 => 0x8474462e1c0c600847b5d46302060084828040302e684796c6a4d403070084765d462e1c6006c2e1c120c0060000846c5d30235006a40302e0800600302e120c0800600846c3020120c6006c49302e270060000846c302e15500856c5d462e0f600856c5d554620600856c6a4030206006c645d302e126
  | 6, 0, 6 => 0x856c5d463b2e600845d46302e036006c5d46302e0e600846c6a40201c600846c201c120c600846a4030200860084705d462e1c6006c625d3020126007246302e0c006006c6a402e1c00600846c69403020600843020120c086
  | 7, 0, 0 => 0x847b5d46302e600846c5d46323020700846c5d462e2a1c70000846c49302e27600846c6746302e167006c5d4634302000700006c635d46302d60000845d46302e06600846c5d46302e09700856c5d302e120c700846c5d33302012700846c625d463020700846c5d46433020700846c5d463c302070084806c4630200c700846c5d30201e127
  | 7, 0, 1 => 0x845d46302e2208700844640302e2908700847c6c5d302e1270083795d46302e00700847d6c5d41302e700846c5d4846201c700847f795d46302e700846c5d402e1c1270000846c6940302e600847a745d46302e70084745d463e302e7000084302e120c0860000846c5d412e1c600846c665d463020700006c5d46302e11600846c5d462e251c7
  | 7, 0, 2 => 0x845d5c302e1208700846c4f46302e0c70084836c4946302e700845d45302e1208700006c4946302e00600856c6a5d463020700006c625d302e12600846c5d30201f12700846c5d58403020700846c5d57302e12700846c5d5946302e700846c5d4636302e700846c5d462d201c700846c46302e0c0270000856c5d513027600846c5d46201c127
  | 7, 0, 3 => 0x8474735d46302e70084786c46302e0c7006c5d46302e2800700846c5d463a3020700846c5d463f3020700846c5d3e30201270000846c2e1c120c6006c5d4638302e007008481795d46302e70084826c4640302e700846c5d463530207000084745d46302e600846c5d5841302e70000625d46302e086006c5d463027200070000846a40302e086
  | 7, 0, 4 => 0x846c6a402e1c600846c5d5c2e1c12700846c5d452e1c1270084745d463a302e700846c5d5346302e7008446302e200c08700806c5d46302000700846c302e20120c700846c5d462e221c70084725d462e271c70084745d46302e05700846c46402e291c70084726c46302e0c700846c464030200c700806c5d40302e00700796c5d463020007
  | 7, 0, 5 => 0x6c5d46302e020070000846c49463020600847f6c46302e0c7006c5d514631302e700655d46302e08007006c655d302e1200700845d46302e1608700846c5d3d302e12700005d302e12080060000846c5d30201260084796c5d302d1270000847246302e0c60084605d46302008700006c625d462e1c600846c5d464430207000084795d46302b6
  | 7, 0, 6 => 0x846c5c4630200c700006c5d46313020600856c5d4630272070084806c5d4030207006c5d4634302e00700846c464530200c700845c4640302e0870000856c4946302e600846c5546302e0c700846c5d5a46302e700846c5d4c46302e7006c625d5846302e700846c65463a3029700846c462e201c0c700846c594946302e700846c5d4038302e7
  | 7, 0, 7 => 0x6c5d4a46302e60000846c653029126006c5d302e2012007006c5d4631302e127006c6546302e29007006c655d462e1c00700726c5d46302e007006c5d4640302000700846c5d56463020700846c5d57463e2e7000084715d46302e60000846c5d302e1460084835d46302e02700846c5d462e1c16700006c5d2e1c1200600846c5d4d302e127
  | 7, 0, 8 => 0x846c5d46302e0570084836c40302e12700846c5c46402e1c70000725d46302e006006c675d302e1200700846c655d3020127008446302e270c08700846c5d302e1f1270000846c5d54462e600845e5d302e120870000845d302012086000084745d462e1c60000846c6a302e16600008465463029086005d46302e2008007006a5d46302e08007
  | 7, 0, 9 => 0x846c695d463020700846c625d302e12700846c5d3c302e12700846d6c4630200c700856c655d302e12700845d302e2d1208700006c4630200c00600845d302e120c08700846c46302e170c700846c5d4630200d70084796c302e120c700846c5d46302e197008480795d43302e7008482805d46302e70084746c4640302e70000846c5d46372e6
  | 7, 0, 10 => 0x84786c5d463020700846c5d462e1c1370084796c6a40302e700006c5d5046302e600006c5d4e463020600846c462e271c0c7006c5d5546302e0070000846c5d4d3027600846c5e5d2e1c12700846c665d302e1270000846c5d201c1260000846c6546291c6006c46302e120c007006c5d462e201c007006c6a5d462e1c007000084744640302e6
  | 7, 0, 11 => 0x846c65463022600856c5d302e2012700846c5d4639302e700846e6c5d463020700856c5d464030207008446302e290c08700846c6a5540302e700846c5d46413020700846a5d46302008700846c5d2e2d1c12700846c474630200c700846c5d2e1c120c700845d46302e2706700847c795d46302e70000846c40302e2a60084726c5d4630207
  | 7, 0, 12 => 0x84826c46302e0c7006c5d46302e1700700796c5d302e1200700846c5f5d4630207000085725d46302e600845d302f2e1208700846c5d3a302e1270000846c6046301e6006c674640302e007005d46302e27080070000846c5d46362e6006c5d46302e2c007000084725d463020600846c6346302e0c700846c625d462e1c700846c675d3020127
  | 7, 0, 13 => 0x8483795d302e12700846c615d46302e700846c5d46302e0f700846c5d55463020700847d6c5d46302e7006c463e302e0c00700846c462e291c0c700846c5d462e211c700846c5d45403020700846c463020120c70000856c4630200c600846c6a5d46201c700844640302e0c087000084755d46302e6006c5d46453d302e700847f6c5d4630207
  | 7, 0, 14 => 0x84796c5d302012700845d4630272008700846c5d38302e1270000844946302e086006c5d5a4e46302e7006c5d51463020007006c5d302e291200700846c5d463f2e1c70084816c5d46302070084776c5d463020700846c5d2f2e1c1270084836c46302e167006c5d462e271c00700846c664640302e70000856c5d463a2e6008479745d46302e7
  | 7, 0, 15 => 0x84796c5d4d464030800846c5d4627201c70084766c5d46302e7000084725d5130276006c5d46302012007846c5d46403d302e8006f6c5d463020007005d4640302e08007006c5d5746302e2d700846c5d464030207006c5d48463020007006c5d4630201d0070084726c5d5130277006c5d46302e2a00700006c5d31302e12600846c5d462e261c7
  | 7, 1, 0 => 0x846c655d2e1c12700006c6a40302e0060084706c5d46302e70000847446302e0c6006c5d46452e2d1c7007c6c5d46302e00700846c5d46302e017006c5d4631302e20700856c5d302e29127006c5d46402e1c0070084746c46302e0c7000084765d46302e600846c6b5d46302e700006c302e120c0060084655d302e12087008483794640302e7
  | 7, 1, 1 => 0x847c6c5d46302070000856c302e120c600836c5d302e1200700846c5d4640201c700846c5d4642302070000846c3020120c60000846c5d4b4630600846c695d462e1c700856c5d463020127000084705d46302e600845d4641302e08700856c5d484630207006c5d463e302000700845d4640302008700856c5d46302e2a700847c6c6a40302e7
  | 7, 1, 2 => 0x846c6a4d40302e700846c5d4645201c700006c6546302900600846c5d463b302e700846c6740302e127006c5d4d46302e0070000856c5d55462e600846c5d46302e1870000856c6a40302e6006c5d4631302e27700845d464530200870000846c6a4030206006f6c5d46302e007006c5d4a4640302e700846c5d46412e1c700846c302e2d120c7
  | 7, 1, 3 => 0x6c5d462e1c1200700846c5d5446302e7006c6a5d46302000700846c5d55463e2e7006c5d464031302e700846c5d46302d0270000846c302e120c600006c5d46201c006000084805d43302e600846c6a403e302e7005d46302e120800700846c3e302e120c7847c795d4640302e800846c5d463d3020700005d4630200800600846c5d463020167
  | 7, 1, 4 => 0x845d46302d2008700845d4630201208700006c5d5a46302e6006c675d46302000700845d46302e2508700845d46302e2a087
  | 8, 0, 0 => 0x8480795d46302e78479776c5d46302e80000846c5d463020600846c5846302e0c70084746c5d46302e70084796c5d46302d700846c5d46302e1d700846c5d46302e1670084836c5d302e12700006c5d302e1200600846c5d46452e1c700846c605d463020700847e6c5d46302e7846c5d463e302e2d8846c5d463e302e12800846c46302e200c7
  | 8, 0, 1 => 0x846c5d5b46302e7006c6a5d46302e00700845d5146302e08784796c5d4640302e8846c5d4f4645302e800006c5d462e1c00600846c5d4d46302e700846c5d4633302e700846c5c4640302e7000084745d46302e600846f6c5d46302e784796c5d46302e298846c5d4645302e208006c655d46302e00700846c5d463d302e700005d46302e08006
  | 8, 0, 2 => 0x856c5d302e1260084836c4640302e7006c675d46302e00700846c655d463020700846c5d46302e1f700846c5d46302e1370000845d46302008600846c46302e270c700846c5d46302e24700846c5e5d302e1270000846c5d3020126846c5d554640302e8846c5d463e3c302e80000846c654630296006c5d46302e2000700846c5d46302e2b7
  | 8, 0, 3 => 0x846c665d46302e70000846c5d46201c600846c5d33302e12700846c625d46302e700846c5d4643302e700846c5d463c302e7846c655d46302e12800856c655d46302e700845d46302e2d08700846c5d5246302e700846c5d46302f2e700846c5d51462e1c700845d46302e1208700846c5d302e2d1270084796c46302e0c700846c5d302e120c7
  | 8, 0, 4 => 0x846c5d302f2e12700846c5d4635302e7006c5d46302e2700700846c675d463020700856c5d46302e20700856c6a5d46302e700846c5d5840302e700846c5d462e2d1c700846c46302e290c700846c5d46302e21700846c5d462e1c12784806c5d5c46302e800846c6a5d4630207846c675d5146302e8846c5d463e35302e884796c5d4645302e8
  | 8, 0, 5 => 0x846c4645302e0c700846c5d46302e287846c6a5d463e302e800846c5d4630272070000846c4946302e600846c5d40302e2770000846c5d302e12600846c5d46302e26700806c5d46302e00700846c5d46343020700846c4640302e0c700796c5d46302e007846c675d46302e12800846c5d463a302e700846c5d463f302e700846c5d3e302e127
  | 8, 0, 6 => 0x84746c5d46302e29800846c655d302e1270000845d302e1208684806c5d46302e0c800846c5d46302e20784796c5d46302e2d8006c5d4645302e2d784796c5d46302e128847c6c5d4640302e8006c5d4640302e00700846c5d5646302e70084806c5d463020700846c5c46302e0c700006c5d4631302e600856c5d46302e2770084796c5d4630207
  | 8, 0, 7 => 0x845d46302e2008700846c5d4641302e700846a5d46302e087846c5d574645302e800846c6546302e29700846c5d4640302070084786c5d46302e7846c5d463e302e27800006c5d4e46302e60000846c5d2e1c1260084745d46302e29700846c5d4634302e700846c5d4f46302e700846c695d46302e700846d6c46302e0c700846c5d46302e027
  | 8, 0, 8 => 0x845d46302e2708784836c5d5146302e8846c5d46403e302e80084776c5d46302e700846c5d46453020700846c5d5546302e700846c5d462e201c700846c6a5d462e1c700847f6c5d46302e7846c5d5c5146302e8846c5d4d4640302e800846c5d46302e277846c5d4640302e2d800846e6c5d46302e784796c5d4643302e800856c5d4640302e7
  | 8, 0, 9 => 0x846c5d46302d20700846c5d4630201270000856c5d463020600846f6c5d463020700845d4640302e08700846c5d46302e25700846c5d4630201d700846c5d46302e2a784796c6a5d46302e8846c5d46453e302e800846c5d462e271c7006c5d46302e1200700846c5d4640302e7846c5d463a302e29800006c5d46302000600846c5d46302e177
  | 8, 0, 10 => 0x846c5d463e3020700845d4645302e0870000846c6a40302e600846c5d4630201f7846c5d4640302e20800847c6c5d46302e700846c5d46402e1c70000846c302e120c600856c5d46302e127846c5d463d302e2d8006c5d463e302e007
  | 9, 0, 0 => 0x84806c5d46302e784796c5d46302e7846c5d46302e277846c675d46302e7846c5d46302e207846c6a5d46302e700846c5d462e1c600845d46302e08600846c5d302e12600846c5d46302e6846c5d463e302e7846c5d46302e2d7846c5d46302e12700856c5d46302e600846c5d4630206846c5d5146302e7
  | 9, 0, 1 => 0x6c5d46302e006846c5d4645302e7846c5d4640302e7
  | 10, 0, 0 => 0x846c5d46302e6
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
  | 0, 0 => 0xffff0007ffff0000000000000000000000000000000000000000000000000000ffff0007ffc70000000000000000000000000000000000000000000000000000ffff0007f1ff0000000000000000000000000000000000000000000000000000ffff0007f1ff0000000000000000000000000000000000000000000000000000ffff0007f1c70000000000000000000000000000000000000000000000000000fff00007f1c60000000000000000000000000000000000000000000000000000ffff00007fff00000000000000000000000000000000000000000000000000000000ffffffff
  | 0, 1 => 0xff18cffff80e3900000000000000000000000000000000000000000000000000e31800ffff8e39000000000000000000000000000000000000000000000000001f07ffffffffff000000000000000000000000000000000000000000000000001f07ff07f801ff000000000000000000000000000000000000000000000000001f07f0ffffffff000000000000000000000000000000000000000000000000001f07f0ffff8fff000000000000000000000000000000000000000000000000001f00cfffff8e390000000000000000000000000000000000000000000000000000ffff0007ffff
  | 0, 2 => 0xff18c018cf800000000000000000000000000000000000000000000000000000fffffffff87fff00000000000000000000000000000000000000000000000000fcffc0ffc07ff800000000000000000000000000000000000000000000000000fffffff8f87fc700000000000000000000000000000000000000000000000000e3f83fffffffff00000000000000000000000000000000000000000000000000e3f83ff8387e0700000000000000000000000000000000000000000000000000e3f830ffffffff00000000000000000000000000000000000000000000000000ff18cfffff8e39
  | 0, 3 => 0xfffff00000000000000000000000000000000000000000000000000000000000e0f8001807f000000000000000000000000000000000000000000000000000001c07c000c781c000000000000000000000000000000000000000000000000000ff18cfffff8e3900000000000000000000000000000000000000000000000000ff18cfffff8e3900000000000000000000000000000000000000000000000000ff18cfffff8e3900000000000000000000000000000000000000000000000000ff18cf1fff803900000000000000000000000000000000000000000000000000ff18c0ffff8e39
  | 0, 4 => 0x70000380000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000fffffff8ffffc7000000000000000000000000000000000000000000000000001c07cfe0f78fc100000000000000000000000000000000000000000000000000ffffff1ffff1ff00000000000000000000000000000000000000000000000000fffff0ffffffff00000000000000000000000000000000000000000000000000fffff018cff1c6
  | 0, 5 => 0xe3f83fff387e3f0000000000000000000000000000000000000000000000000000000fe7300e390000000000000000000000000000000000000000000000000000000f0000000000000000000000000000000000000000000000000000000000000000e7300e0000000000000000000000000000000000000000000000000000000000e730003800000000000000000000000000000000000000000000000000000000e7000e3800000000000000000000000000000000000000000000000000000000e0000e000000000000000000000000000000000000000000000000000000000007000038
  | 0, 6 => 0xe730000071c60000000000000000000000000000000000000000000000000000e730000071c600000000000000000000000000000000000000000000000000000700070001f800000000000000000000000000000000000000000000000000fffff018cff1c600000000000000000000000000000000000000000000000000e3ff3ff8387fc7000000000000000000000000000000000000000000000000001fe7ff07f871ff0000000000000000000000000000000000000000000000000000e730ffffffff0000000000000000000000000000000000000000000000000000e730000071c6
  | 0, 7 => 0xe73fe7307fff0000000000000000000000000000000000000000000000000000e73f000071c60000000000000000000000000000000000000000000000000000e73f000000000000000000000000000000000000000000000000000000000000e730e7007ffe0000000000000000000000000000000000000000000000000000e730e0007fc60000000000000000000000000000000000000000000000000000e730000071c60000000000000000000000000000000000000000000000000000e730070071fe
  | 0, 8 => 0x1f07ff07ff81ff000000000000000000000000000000000000000000000000001c07c007c781f8000000000000000000000000000000000000000000000000001c07c000000000000000000000000000000000000000000000000000000000001c000007c78000000000000000000000000000000000000000000000000000001c000007c0003800000000000000000000000000000000000000000000000000000700000781c000000000000000000000000000000000000000000000000000000000070780380000000000000000000000000000000000000000000000000000000000078000
  | 0, 9 => 0x1c07cfe7300e39000000000000000000000000000000000000000000000000001c07cf000000000000000000000000000000000000000000000000000000000000000fe7378e390000000000000000000000000000000000000000000000000000000f000780000000000000000000000000000000000000000000000000000000000fe7300e390000000000000000000000000000000000000000000000000000000f0000000000000000000000000000000000000000000000000000000000000000e0078e0000000000000000000000000000000000000000000000000000fffff01fcff1fe
  | 0, 10 => 0x1ce7f0000071c6000000000000000000000000000000000000000000000000001ce7f0000000000000000000000000000000000000000000000000000000000000e7300007f1c60000000000000000000000000000000000000000000000000000e730000071c60000000000000000000000000000000000000000000000000000e0000707f0380000000000000000000000000000000000000000000000000000e0000007f000000000000000000000000000000000000000000000000000001c07cfe7f78ff9000000000000000000000000000000000000000000000000001c07cf000001c0
  | 0, 11 => 0xfffff00000000000000000000000000000000000000000000000000000000000e3f83ff83ffe0700000000000000000000000000000000000000000000000000e0f800f807fe0000000000000000000000000000000000000000000000000000e0f8000000000000000000000000000000000000000000000000000000000000e00000f8078000000000000000000000000000000000000000000000000000001ce7ff000071c60000000000000000000000000000000000000000000000000000e730e007ffc6000000000000000000000000000000000000000000000000001ce7f007c7f1fe
  | 0, 12 => 0xe0ff30f807ffc600000000000000000000000000000000000000000000000000e0ff30000071c600000000000000000000000000000000000000000000000000e0f80fff37fe3900000000000000000000000000000000000000000000000000e0f80f0000700000000000000000000000000000000000000000000000000000e0f80fe7300e3900000000000000000000000000000000000000000000000000e0f80f0000000000000000000000000000000000000000000000000000000000e00000ff37803800000000000000000000000000000000000000000000000000fffff0f8cfffc6
  | 0, 13 => 0xfffff0fffff1c600000000000000000000000000000000000000000000000000fff83ffff87e0700000000000000000000000000000000000000000000000000ff07fffff801ff00000000000000000000000000000000000000000000000000ff0000fff8000000000000000000000000000000000000000000000000000000fcfff0000071c600000000000000000000000000000000000000000000000000fcffc0ffc7fff800000000000000000000000000000000000000000000000000fcffc00000000000000000000000000000000000000000000000000000000000e0ff3f000071c6
  | 0, 14 => 0xff000f0000000000000000000000000000000000000000000000000000000000ff0000fff80e3800000000000000000000000000000000000000000000000000ff0000fff80e0000000000000000000000000000000000000000000000000000ff0000fff80e0000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000ff0000fff8003800000000000000000000000000000000000000000000000000ff0000fff8000000000000000000000000000000000000000000000000000000ff0000fff80000
  | 0, 15 => 0xff07c0fff8000000000000000000000000000000000000000000000000000000ff07c00000000000000000000000000000000000000000000000000000000000ff0000ffff803800000000000000000000000000000000000000000000000000ff0000ffff800000000000000000000000000000000000000000000000000000ff0000fff8000000000000000000000000000000000000000000000000000000ffe730fff87fc600000000000000000000000000000000000000000000000000ff000ffff80e3900000000000000000000000000000000000000000000000000ff000ffff80000
  | 1, 0 => 0xffffff000071c600000000000000000000000000000000000000000000000000ffffff0000000000000000000000000000000000000000000000000000000000fff800fffffe0000000000000000000000000000000000000000000000000000fff800fff8000000000000000000000000000000000000000000000000000000fff8000000000000000000000000000000000000000000000000000000000000ff07c0ffff81f8
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x7bd700053aeb00000000000000000000000000000000000000000000000000007a9500053a83000000000000000000000000000000000000000000000000000053d3000520eb000000000000000000000000000000000000000000000000000052c2000520a0000000000000000000000000000000000000000000000000000052910005208300000000000000000000000000000000000000000000000000005280000520800000000000000000000000000000000000000000000000000000295700001a6b000000000000000000000000000000000000000000000000000000007bdbf7df
  | 0, 1 => 0x25084e842008200000000000000000000000000000000000000000000000000000000052828410000000000000000000000000000000000000000000000000000f057b7ffbf7ff000000000000000000000000000000000000000000000000000f057b0578016f000000000000000000000000000000000000000000000000000a04207bdbf7df000000000000000000000000000000000000000000000000000a042052ca85140000000000000000000000000000000000000000000000000005004a56a2843000000000000000000000000000000000000000000000000000007bd70005befb
  | 0, 2 => 0x90108010860000000000000000000000000000000000000000000000000000006fad7fad785b6f000000000000000000000000000000000000000000000000006cad46ad405b68000000000000000000000000000000000000000000000000006bac3da8785b070000000000000000000000000000000000000000000000000063a83dfbfbffdf0000000000000000000000000000000000000000000000000063a83da8385a07000000000000000000000000000000000000000000000000004280207bdbf7df0000000000000000000000000000000000000000000000000025084ed6a28c30
  | 0, 3 => 0xdad6a00004000000000000000000000000000000000000000000000000000000d0d280188760800000000000000000000000000000000000000000000000000098568010c7218000000000000000000000000000000000000000000000000000b518ced6a68c3000000000000000000000000000000000000000000000000000b518ce94a60820000000000000000000000000000000000000000000000000009510ca56a68430000000000000000000000000000000000000000000000000009510ca14a600200000000000000000000000000000000000000000000000000090108052868410
  | 0, 4 => 0x40142470084780000000000000000000000000000000000000000000000000004014204000020000000000000000000000000000000000000000000000000000000004200841000000000000000000000000000000000000000000000000000fbfebdb8ff7b8700000000000000000000000000000000000000000000000000b97e9db0f73b8300000000000000000000000000000000000000000000000000dfd7fb1dff61ef00000000000000000000000000000000000000000000000000dad6a07bdff7df00000000000000000000000000000000000000000000000000dad6a018cf6184
  | 0, 5 => 0x67a97fef38de7f0000000000000000000000000000000000000000000000000025295fe7309e7b0000000000000000000000000000000000000000000000000025295f842008200000000000000000000000000000000000000000000000000025280ce7309e100000000000000000000000000000000000000000000000000025014ae730847800000000000000000000000000000000000000000000000000242946e7009e7800000000000000000000000000000000000000000000000000202804e2009e10000000000000000000000000000000000000000000000000000421536710967b
  | 0, 6 => 0x4ee7732d5973ef000000000000000000000000000000000000000000000000004ae7316b59f7df000000000000000000000000000000000000000000000000000c47424741a5f800000000000000000000000000000000000000000000000000daf7b139df73cf000000000000000000000000000000000000000000000000006bef3da9797bcf000000000000000000000000000000000000000000000000004fe77b2d7973ef000000000000000000000000000000000000000000000000004ae7317bdbf7df000000000000000000000000000000000000000000000000004ae731295973cf
  | 0, 7 => 0x90528000040000000000000000000000000000000000000000000000000000006fef7fef79ffff000000000000000000000000000000000000000000000000006fef7fad797bef000000000000000000000000000000000000000000000000006fef7f84200820000000000000000000000000000000000000000000000000006eef77ef59ffff000000000000000000000000000000000000000000000000006aef35eb59ffdf000000000000000000000000000000000000000000000000006aef35a9597bcf000000000000000000000000000000000000000000000000004ee7736f59f7ff
  | 0, 8 => 0x9f57fb57ffa5ff000000000000000000000000000000000000000000000000009c57c257c7a5f8000000000000000000000000000000000000000000000000009c57c204040020000000000000000000000000000000000000000000000000009c568057c7a590000000000000000000000000000000000000000000000000009c054257c285780000000000000000000000000000000000000000000000000098578053c7a5d8000000000000000000000000000000000000000000000000009453c25787a4f8000000000000000000000000000000000000000000000000009052805287a490
  | 0, 9 => 0xbd7fdfe7349e7b00000000000000000000000000000000000000000000000000bd7fdf8424082000000000000000000000000000000000000000000000000000b57bdff7b7befb00000000000000000000000000000000000000000000000000b57bdfd6a7acb000000000000000000000000000000000000000000000000000b57bdfe7349e7b00000000000000000000000000000000000000000000000000b57bdf8424082000000000000000000000000000000000000000000000000000b07a84f287be9000000000000000000000000000000000000000000000000000ded7e25fcfe5fc
  | 0, 10 => 0xdef7f32d5d73ef00000000000000000000000000000000000000000000000000def7f30404002000000000000000000000000000000000000000000000000000daf7b17bdff7df00000000000000000000000000000000000000000000000000daf7b1295d73cf00000000000000000000000000000000000000000000000000d4f3d37f97f6fb00000000000000000000000000000000000000000000000000d0f2807a87f69000000000000000000000000000000000000000000000000000bd7fdff7f7bffb00000000000000000000000000000000000000000000000000bd7fdfa5753beb
  | 0, 11 => 0xfafea48004080000000000000000000000000000000000000000000000000000f3fabdfabffe9700000000000000000000000000000000000000000000000000f0fa84fa87fe9000000000000000000000000000000000000000000000000000f0fa848004080000000000000000000000000000000000000000000000000000f0d280fa87e49000000000000000000000000000000000000000000000000000ffffffad7d7bef00000000000000000000000000000000000000000000000000faffb5fbdfffdf00000000000000000000000000000000000000000000000000def7f37fdff7ff
  | 0, 12 => 0xfaffb5fbdfffdf00000000000000000000000000000000000000000000000000faffb5a95d7bcf00000000000000000000000000000000000000000000000000f5fbdfffb7fefb00000000000000000000000000000000000000000000000000f5fbdfad357aeb00000000000000000000000000000000000000000000000000f5fbdfe7349e7b00000000000000000000000000000000000000000000000000f5fbdf8424082000000000000000000000000000000000000000000000000000f5d3caffb7e4f800000000000000000000000000000000000000000000000000fafea4facfff94
  | 0, 13 => 0xffd6a8ffff618400000000000000000000000000000000000000000000000000ffac3dfffa5b0700000000000000000000000000000000000000000000000000ff857bfffa416f00000000000000000000000000000000000000000000000000ff8428fffa410400000000000000000000000000000000000000000000000000fefff7ad5d7bef00000000000000000000000000000000000000000000000000fcffc6ffc7fff800000000000000000000000000000000000000000000000000fcffc68404082000000000000000000000000000000000000000000000000000ffffffad7d7bef
  | 0, 14 => 0xffad7f8420082000000000000000000000000000000000000000000000000000ffad6efffadf7c00000000000000000000000000000000000000000000000000ffad3dfffadf5f00000000000000000000000000000000000000000000000000ffac2cfffadf1400000000000000000000000000000000000000000000000000ffac2c8420080000000000000000000000000000000000000000000000000000ff856afffac57c00000000000000000000000000000000000000000000000000ff856afffa412400000000000000000000000000000000000000000000000000ff8428fffac514
  | 0, 15 => 0xffd7eafffe412400000000000000000000000000000000000000000000000000ffd7ea8424002000000000000000000000000000000000000000000000000000ffd7eaffffe5fc00000000000000000000000000000000000000000000000000ffd6a8ffffe59400000000000000000000000000000000000000000000000000ffd6a8fffe410400000000000000000000000000000000000000000000000000ffef3dfffbffdf00000000000000000000000000000000000000000000000000ffad7ffffadf7f00000000000000000000000000000000000000000000000000ffad7ffffa4924
  | 1, 0 => 0xffffffad7d7bef00000000000000000000000000000000000000000000000000ffffff8424082000000000000000000000000000000000000000000000000000fffeacffffff9400000000000000000000000000000000000000000000000000fffeacfffe490400000000000000000000000000000000000000000000000000fffeac8424080000000000000000000000000000000000000000000000000000ffd7eaffffe5fc
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 134 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 134 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 134 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 134 then wireAt i else 0
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
  | 5 => 13
  | 6 => 476
  | 7 => 2141
  | 8 => 589
  | 9 => 15
  | _ => 0
def CH : Nat → Nat → Nat
  | 5, 0 => 0xebbb84669a67914394df6c778889eb828808a6cc7da08451779a61b96adf9d2c5fd369bc5ad354c75704cfcd42b779a31ed15b31
  | 6, 0 => 0x157530901567545c155f9e68155ed66715527a69154d78621546604914ec82a214c15aa414b260431436a47013c93bbb13a7772312f3f245119dfe10111585de0fa9c97d0f8898390f173e660f1096c80ebd9b2a0eb903040ea756a30e7e15130e55716a0d55e2950d3533830cabde0a0c0203ab0bb5b40f0bb59b8a0ae52c1109e76cd90965c6230919997808f317a508d564270884eaa3088078d607696e7206dfb59b06b70239068217d406519409063215340603175b0601567c0545cfaa053f9f860528c7320505ca7204a49784048395a90416c318040779340386da350355259e02e1925302dc1b2602535ba30229104300dbb76900b0956900739781
  | 6, 1 => 0x280a567c27d2a87727b3f54127a4a65b275dc42027446ccf2705880d26ee731726c09f4926b0cd0826acc7fc265fdab5265409bf262fef5c262799e925b7ff1b2583c6302502515424f85f8a24e0e441249d0b2024997c0724945bd1247aa6fc2408b6b123e3e51a23792ad3227ae2082245f0bb21f076d421bcc1d8217e629721763a3a213869ba21102ce020e3c0492078273420292edb1fb12d6a1f7fa4691df679371c4995e61c3bb9b21abf35371a959f931a4886a719e2a56619ba301a19a0d01c190a1b2718af49f71842f65e1815e4b617f95b8717d6fff4178f1a7217360e58173285f61701656116a3d62d1658de33164ba189160c315a1594fa38
  | 6, 2 => 0x4211906141f93ba241cdfba64184574b416e98134127bd8c3fc0c4623df59e8a3d4362653d0ec8b73cafd4f03ca329da3c2b77b93c21f90f3c21c3983b4591a23a5358363a18430739e589bc38c26dc8383a11983835c33f381aa7ec376135eb36f80e8c36bd7d7436966b453674a6ad36679b94361bdb6035db6f9a35d59164341823e233b6c8233385d7e5336f4fbe32910d76321ef9393216d0dc31e171103174862d3146429630b737572fd209e42fcce5c12fc82d0a2fa041572f790d942efc38a62edae5ed2e2810e22cc60d482c0d21c62bceb6ad2b81626d2b812cf62ae91d492a369dfc294f475e28e38d0028a4a83e28520053282fb11428137f5a
  | 6, 3 => 0x5e71e56d5e5e08d45cde0cce5bccd1535afe7d8d5ad018fe5a657cac59d6cf1b58b3046f575beb7357530f6056dd108056d6e2c756b446985652bba656488c3a559e0c575544016d550eec055501a81c54d5d9f35491d78853b908f9533e15335318541d529a078b527b2df5525b0867516101665105b6dd504dfb8c4f3b12274ee852904ebb396a4e81933b4e0610dd4dbd72324d84259f4c9e493a4bd9ec344b04cebf4aba972c4aae3b9e49a0b8ec48f96e4e48be79ea48683a6347062c034675c8f9466798fe464d910745a7f59845808871457ae3f0451f7c0844b7429b445402504394911f4389d593436ee96142b779a3429d7e91428207b2424e3662
  | 6, 4 => 0x7fa63a517f78bc997e9fec817bdcd2c179e15a2879d7acfb79aa400a7835bf5077ed7ef27752791c76eb652275e89c1f75b758e67540a7b374952988734bd99472d5dab4729c0386726d1b96722eeeb6722280a571acb963713e6459709960ad7069d795705155296fd0a4136f92d4966f127c0f6e5661bc6e0cf9fd6ddf9c246dc267686d0bf2296b3569ed6a14d42a69d0ab8968eb1e25685d12cd6846ff966777796966fd2aea66b1e27a66a4064665883aeb657fa72665326e2a651b65ec64f3896864d04ae264610497640b444f64091cb064047b4d63d9a5e762a7224d624f6deb612c62816118463c60bfdce05fe3d1285ef62c355ef2ba575ef23df4
  | 6, 5 => 0xa216970ba1f48e03a19efacea0abaf399ea3bd2f9ea1af809e5afc4f9defe5a49d302a159c30a0c29be41d5a9b7186cd9b3408679ad005439a20f57f99a2dd3597b8b82697ac0d1096ce6dfd95f6cf7b949d51f494821043944a299593b3548d9384bb9e92fa595892c480a290e2f044900ea0798dbd473e8d00c0808c7d69638c76bee98ad166ae8a81f0ca8a2bb58a899d8f088948509588fde9be888e1594882be4e1880e699b87182184870b766e86d1aad786b3443c8657ef8885e13e5585d4451d857451d7856817d38564247784582a9483c8f6ab831814a882ecdd3b82781b9d81f71b7081f6d6c281f0b56481cd1add81556ecc80dcf341809fa340
  | 6, 6 => 0xde9c6949ddf6cc47dc862683dc4f5541dbb49a3eda447b0cd8ec94cfd78fc00fd7882a40d6de2321d46518b5d283c88ed16e2384d155ecd9d139f76bd0c88e6cd0b3c4ead02a929acd5635a5cc7cc0edcc470807ca58a948ca536b4ec8a38c7ac78bb67cc6526888c5736c6ac4122956c4054e05c2d0bd5ec1a17d6fbfc9a3e9beb14ce4be4be64fbe0137f1bdb36536bd8203c1bd67578cbae936eeb9b8f6f9b7e6dd5cb72cd29bb6ec3491b6c8cf77b6960370b61f6545b5bd08a5b4b81d3ab3b01fceb37da600b2edc881b2d95111aec45a1daea5f601ad7e8cbaad52b212a93e5661a70f3f44a6c8bf21a64b9defa4c44afaa40ff91ea3600842a245ec23
  | 6, 7 => 0xfd4ecf59fa8bcd18f9ebb5bcf9acd0faf8d44b18f863ef6af6d3a092f465566cf39943e7eed29112ed694d21ecc13a3fecae38b7ec5530e0ec164c1eebf06ba0eb4e471feb023407e94b1f1ae841ee01e6d3dc86e29f903be1da8e0de11915d9dff65054df0f379cdefb0a41debb2123
  | 7, 0 => 0x4d32ad804bca65904aea85504941f6a048faf4c0479bbe10472ece0046088880442bd8604427d3b041b5fb5040d80d603f1b95203eb258003cf5e0b03cf02d103c4ae050355cd580341d11b033b05b5033a727c0318307a030d3b30030a418d03087e0402e9d44b02c16857029aef9e02885a13027c6a3c02734c9f02470b1b02438cb9020b934d01eac28901e3cad001cde88101b8699b01b5ee8d01abdea401a6e4da019fd767019186980185f46d016ba7c501660357015fcb3e014ecf68014268c70124c53e011eaa2f011182d800f9b8fb00f5a3d200ea38dd00d76e0200b9120700955441007dbb7a007cee18005d9404003e83f9002bdc3e0029bfef
  | 7, 1 => 0x9bd51ef09a7f2140989c7c3096245740938c9750913c1b1090aa33808e9d98008e4c69e08b46af108b0be3e08b0816608739b700865d84f0856ca260844bf83083a68ad083004ee08297cd9081c74db07f1b6d607ed8a3207ca96c507c038b307b1fadf07a3436a078c6002078179cf074eba9407382cc5071cbf990715437d0709752007073daf06fb5c5206e4ef6406cd9ad406cb4d4b06c7dfaf06c4413d06bd2d1e068a399a0681af1906743d310665520c0659598f0651b5d5064cb8090636e8f606291d83062442000622ad21060f596e060e01a405fc8ebd05ad2f34057ed23605687e8905558372052aa49505169eb00509fa1f04fff25a04df8b0c
  | 7, 2 => 0xd7f85ab0d61f2fb0d570f570d52adb20d49c4170d40e0e10d37f59a0d2d22890d261b2b0d1802ee0d0ebdc20d05cbda0d02db730cf439bf0cea20e10cd88bf40cd4b54f0cb02ee00cabde0a0ca165b80c9d1f690c825c970c6f23470c269c8b0c232aad0c22507d0c0dba2d0c0bf6ea0bd124900bb2ffb10bb0f9310ba0f9160b985bbe0b76e6c50b3e33d00b2912830b2179b20afb5dd30acf09dd0ac986c50ac4d5b90abf97180abbeb7f0ab8b2690aad79ad0aa769cf0a9628be0a95e7770a8482510a7e53d60a7d079a0a7677f50a6426b20a5ed5a50a4eea960a40d6890a3f65910a3d884a0a2a32ae0a1454b209fb12fd09ee1b6f09ec2ffe09d99697
  | 7, 3 => 0x115e1032115b67ca114c695c1142fa4111408e9a113ee05b11266cf511141f6f110f8d8e10de35ff10b7c9a8109ef9a3109bbfbb1075aa7a105e2d191052a2c5104ef361102d648a102d4a7a101f34a21004221f0fec104b0fe0ac610fde41e30fb1a7760fa2a5570f88d0470f7ac0e10f53334a0f37de040f33fdd90f2c4f190f1c66040f1bfb200f15f96a0f06017a0ef737100ef5604a0eef2d5f0ee271f80ed3e0d70ed3950c0ed019dd0ecb2c040ebcf9d50ea022dc0e90cf7c0e7e15130e7ddf9c0e7dd0190e737a980e2c4ae30e05ccb20dfb96ef0df565b60df1ea5d0df0bcbb0dcfc1a80dc23f740db432850da3dd980d9cbe430d9a92370d95c735
  | 7, 4 => 0x15f3a94215f0607615da66d015d3ee2015d3b4e415c4f37415c1920715ba6e6315b3f79d15af65f115a088fc157b3ef6156445b91561a43a15602014155ed0bb15527a691517feab150f2c6414e907ff14de23b614db292014db18b514cc203914c0d43c14adee1014a3cc1814736e851461a25714466a8414446e3c1415063f13e90d2b13bf6c0813b50558139302bf13728f56136dc90413470650133c08ef13346ed11320e8dc1317dd2b12bb814412ae5da312a8595d12774f4f125d0b7e1236e74d1228cbf912245a68120d4198120061e011c1f92a11bd50f411a36f33119557c6118eca21118d0e1d1187183a11803b3c117804a41166de161160b3bd
  | 7, 5 => 0x1afecaa01ae9b4a21ac819931ac6cf551ac4a36f1a9f19ac1a9c7f661a5fb1a01a548add1a4dc7a41a1f1cf019fc1ed919ddb2d519c7c79119b64fa119b1d44819a917ce1990e0df198916cb1980bc2919555e81193687a71922d7aa18ccee3b18939c081892cd851891b64a1870ade618612faf18595dba18545dd61852bb5e183afea718261f781813153417ddd95917d9c21d17d64a9117c6894017c5c22e17bba65117b7e34f17a3f1f517617b9e1749ce821729918f172462521712096e1706ecff16f2a89916dfb77416dbf17016d8a81c16d21d8816c0f68e16b50ee91695814b167fda5b167d3186164f263716446b9c164042a2163fa58d1600b46f
  | 7, 6 => 0x2014c644200df9ca2009a42c1fecb1011fd3c25f1fb72b911fa939b01fa565611fa432931f6499cf1f3e5d811f3387171f05df5c1ee77a8a1ed55caf1ecbe4b41ec4d0da1eb936931ea663541e961c6a1e95def71e90e02a1e7359ed1e5a4bef1e3a97551e2d04af1e1a72c21e0973d31de8aaf61de631f51de3ad8f1de177831da019151d98a19b1d826c881d825b1b1d81c57f1d7876211d1d92371cfd2fc91cd93b5f1cd038361ca973311ca481c01ca3f4021ca0b1831c96ea491c7c268c1c5d3d531c32bad41c228a231c1ffead1bc210541bbd6d551bbaa2fd1b8548e61b61a0cd1b55df541b52f3321b504a801b4bad631b3c1cc21b27d2611b133099
  | 7, 7 => 0x265363bb2648e3a82639a0bd26396ad426146422260a164f25e030e425dfe4c825d992dc259a31372578e98e256e0f5a25494af5253ef9ad2523e0b424f59d0824e504de24dd90d224d8c2d724cbf97124bcbbe924abde1324831e1724429b14243e5010241577b923d675a923cff39623b7b0c523aa74da2385b3452359c6d0233e51982306a5fc22dd669422c4f10a22baad2d229eb02f229c3a0622986b962289ec0b226831b4225693612241709021e9d24d21e7d23f21e6cbde21c636b821a5f968219634db213f9045213bddeb210e27f820f506ac20e249a720cdfb2c20cd427720c7e35d20b7f16d2064873a2062e284205d7c21203e86e9203dbfd6
  | 7, 8 => 0x2bb1f6282b81faf52b81626d2b811d732b5913022b25f1c52b13e5c22afee4492afda44c2af40a152aa00b9d2a9588c32a8c3c9c2a6cf0712a6540552a5617002a245e7b2a222ab32a191a7929ed6e3b29e942c429dfb59429c478db29922d3f296b38aa296af49a2964176b295a32ef294399dc29428e4b29259dd72919e79328e1d56328df87aa28db312e28a1dfb0285879f1284514cc2817589127fa285b27f5c33a27c3516e27c12562279f070c279d6c642799761827933f3b27795cd1275d28bc2753b5b42752ae75274f7c5e273e087b2738adc82710b40c2705880d26f168c926eeeb7b26dab06026d0c80326beaf6f26bb2fef26974ef6265b0505
  | 7, 9 => 0x3129ad3f3122199e3118539930de567830dba214306aaa7f303f34b8302ca777301b2a853016f3a12fcfbe272fbf35272fb1aafd2fb10f502f8af2362f86b33f2f7db54e2f790d942f3c81e32f2d39052f1d68d52f1d2f5b2f1abea52f15a0e52efbd9642ef7eddb2eebbde72ed0d2042ec68d272eba05a82e8af7a22e8a65942e75f9142e7019832e4975d52e44164f2e3b996a2e38cc412e1a49802dfdbfd52df877932df013cb2de6358a2dbac35e2da6f7032d90db782d70ced82d618f3b2d53d1982d52d1502d4518622d3e70562d14647b2d0e06132d076f792d06ef6b2cf8cd042cf085992cebd1e12ce139a22cd4f0ce2c9fc5d62c86b1b52c7afb6d
  | 7, 10 => 0x368939d03678c0eb366fa272365a8560364691d83644f7dd362625043609387936042b1e35e7486435d89aaa35a563b8359f67e7358833f83579865d357321f8357193a635447ed935239d6d34ceb8d134c589ee34a771a734886bc33466ebee345ddff534563d19344aefb834487e123442a8cf341720a334171dd834064f6c33df688433da662c33d93c6b33d8677333b85c4333a0067c339be83033864f1f3380d2fa3359cc583351133033496ad533422da533335fb2332a82ad330a8e3532a1bcd5326c51de326bf53f326a54943264f194325e970c3252e2e03241705c319680a031959d4e3177ea8831752de731660f0b3159aba1315024ba31389c99
  | 7, 11 => 0x3c4debb33c38e0113c35f2033c26260f3c21f90f3c21b4153bf779883bcc8c933b9f7aeb3b94a0b73b754d643b5dab7f3b5624293b48a35c3b40a23f3b34c0e23b1d6fda3b132c693b08dcd23b05d6f73a8b1a653a8512d93a64e63a3a3b02003a2d6c623a2cded53a16892639fa66b039e86c4639a3fedd3975aed639693dae396724ec3965a1543956e3ad38eec90038d186c938c8629238c68766389a48a73899ed1838695c3f38422411383a0cba382f747e382eb67e382d4427381fcf1438120974380d7bfe37a858aa379db3ff3797a68e3791ff6b378ac55537596ec33716cbfd37139a0e36e9c65936cb597836c9556636c744ae36b5383e36b521a2
  | 7, 12 => 0x40c96f0f40bbc12740b5da8040af69b24079f6e6406f21e9405ffdff40530a25404b30134042c3c840419ef2403b69b7403af74d401a1c4f400945b43fe60be43fd62b933fd3ef6d3fca826d3fb404613fb101cf3f98c05e3f8398af3f71238c3f5aa7ff3f5789763f55675e3f49cd203f2afc363f1c7b813f15457d3f147cd73ef484683ee66eca3ec477b03e791ea93e3c0ae43e0e2b9b3e0be7f03e0713153de1cf0e3dc32c533db6e42c3db4e4813da8061b3d9c64d73d8ddd803d8a3cae3d820b7b3d7dc3333d6b3d603d67d4943d5c32c83d3e89f93d2c7c353d2562093d1c18ae3d1af72e3d18139e3d0f7e103cfaa5163cbde0b03c987a9b3c6b3250
  | 7, 13 => 0x47883d4b476a5be9476086824727debc471a541a46f379b846de759446d0e8cf46cefcc046ce551646c9322546c6bba646ba5dbb46b112e2469949b54667f2b74626019546230322462000d245f6b584459774c245940ada457a615d45473c884526b408450ea01a450651ef44f40dc344e5077444b7d8f94493839c445ca64c4458f2e5440fd5ef43fede5343eb0c0643be7d4943b4257143aea1a44397d140437f6b854356b115432dfd824305883642e7b5af42b779a342a0f1e94288da784270b5be425bc8a4425327d74250d609424d728e424083084214fad14210e2ff420d2e5641eef09a41d22c9a41b8ea3b416de72c4119dfa140e3c4e340e1c31a
  | 7, 14 => 0x4d3d159f4d159afc4cd6bec54ca101584c7c5aee4c77c2484c7463374c46545e4c2f2a6b4c20b62f4c1e35cd4c1326ad4c1064844bf147df4bd15be94b6de5b24b6978864b5e75fd4b51d8934b40518f4b226b904b17d9624b02825d4af8703d4aee73794aeba8ec4acdf8d54ab9f0674a9b31354a9428d24a77d2104a6c36964a44957f4a424f5b4a0ea6114a0d197449f3d2f349e8ddff49e125c649bb2fc349ae9520498bdef94987e828497e1ccf49787d0149697f424939f530491e4f5449148db0490584c9490384d348f0ff0048e193ac48d2e75b48b0ac9d48a6ffde4856da1d48339399482de2cd47ee69e847d7f35a47d1bb1b47a3d52347946ea9
  | 7, 15 => 0x533a10a7533669d953155c2b530ec13f52f9f55b52f5cae352dbe80452cf438752ce9ec252c60eec52c17ce552a2b541528d48c352820404525821c05253af2952477438523dc2115209977e51e81d5151bb2a0f51b5c513517e9cbd51688e2851501bab513a17cc5138718d512a0a4a5102a7f450e2359450bd4355509f358a506b190f50659ad750490acd500139404ff820184fbdd0064fb651434fb50f3e4fa260824f6cf5874f4c81644f49dd644f0494734ee3916b4ed752244e9caf7c4e7855394e7327324e3b68614e3a3a904e2cfa994e2ce2974e18a5394e086b364e0181164dffcf964dc9c7c04dc2d7694dc27b5b4db8aa404db0fe984dace24a
  | 7, 16 => 0x5927b4ea59254669591e47e6591227675911ad8058f887e458b561005875705b58597183582969ea57c491b857b34ba057b2372a5795fc8d578e67bf578d26c0576d4781575675b3574ab38e573f8ef45710b5f956f411bd56d32b8f56c5d00a56b44698567ee6cd567b152e56569ab456425f3156403068562fa21b55f9c36e55f5a32a556eec5f556207e255487be65520126a550e9fe655067f9c550188a454e177af54e081a454d5ab8054ca546154b47b9854a2686254a16d3c548e6dd8546df95f5465171a545f13eb54324e15540a4dbd540174e053f747b753e4482853d248aa53cb534053ca920853ab241b539d727b537c0e455372efcc534f52ae
  | 7, 17 => 0x5ed985675ecd913b5e5e95475e56e6485e22a7545dfe16575dd41be55d994f8a5d8c46d45d7bf2db5d6dd96d5d53729c5d4f251a5d464d8d5d1cf1905d0b15675cde0cce5cc14cd15cab1e5b5c97debb5c91de815c7117155c4918f65c3b8dfc5c366d385c33c1815c1f443a5bfb9d265bf13ab45bccb9a15bb301c65bb03c075b8e88025b8c3f8e5b88e0ee5b65c3955b5a05c25b5310a45b3eec9d5b34bf745aea31985ad4f9385ac679ad5aadae925a9469955a8322685a7ee5485a73054d5a5159be5a1dcce559fcbebe59f6336d59eaea5859e9114a59c84b705999c0685996f4f5597bfa89596e2a09595c19525956695a594a059159325022592f0198
  | 7, 18 => 0x64bd146164bb002464b153c16497d77e64789948646b28aa643ac4066433ac9f6413866e63e50b4763d9a5e763bdab1563939f33637c7ea66320cbf7630ff352630826d762da87e162d73fc862c7c6f462a97e13628e144f6264afc1624d6d5b62256876621d1ce6621351f36202e0dd61fe39a261d0c2e561874d90616fe8b4615c4496615a00e8613fcc2c613f4bb661381f97610913c860e8d6d560afae3b609eba3e60699461606901036058ad0a604693fd60205a02601d48af601b43136008d5905ff039eb5fd7d1ae5fd0ae2c5fc559925fbac6fd5fa8e5035f991b495f871fd25f74172a5f61952c5f5bcfc65f411ea25f20e9805f205a9d5edbff03
  | 7, 19 => 0x6a14d42a69da0c1f69b2eaed69b08c9069aba51e699c2c4a694fc71e693c91ca69250df36916740768fa082568f032ac6899ba5d6851887268439ee9683daa9068329f33682efe61682a009568201ef167bf3c7567b7d8a267b7bbf867891a306785247967841837676bd06167339425672edba1671066ce66fc748866fb4c9166e5ae6b66e4732066b2ba9b66a76ca4669b518a668f2c5366816af866730cef6644c8f8663dd1146639b9d86633371c661f8dfe6617db0a65fb2d0c65f74f0265ecad8165d6d88f65b3f9f765af57a565ac519f6566e4ba654872a765381a026532bf6465291588651f03686517bf0f651506a4650db29264f3896864ef4f5b
  | 7, 20 => 0x70b68b1c7066c393705b5d9f701fd29070120e997005f1236fe598a66fb3739e6f7090bd6f6f7e696f410f6b6f13e0ff6f0f44366ee8713b6edb0ec36ec28c856e7f41f46e5e503d6e16b7eb6dec12c46dcfb1e76db8095f6db3cd8b6d483b2f6d35546a6d2a833e6d0c81136d04869a6cd622c66cbe1d396c96b4706c6e76e86c64553c6c4b6e046c49cc986c41d5016c2bf7316c1056596c0eb07c6c0724ba6bf899566be903d06be1bd3a6bd47dc36bd3e8686bb065b86b7d89f26b76748c6b70d1e96b67104f6b4493be6b4207c06b3934176b302ff16b1be3666b0959bc6ae97d196ae5c9b86adc1e476a91b37d6a8281de6a7ff6686a2f8acb6a22b4f8
  | 7, 21 => 0x771f39f8770f6ecc7707b5a176f0de3376f096c376d6e32176c5d6f276b871ac769e1cc8768d442376509acf764e5f617649e3b276461d727626fba5761a42bc76151dfd7607603675cfa8b475576ffc7554e386753f33837539d26974d5843374cf39e474ae2b34749998787485a1e9746a0e0a745e41b7745649717433e09b7407475673fa28f273f993ba73f739d473be3a8b739a9980736647aa7365dcea734eaa0d73275b5973163a5772e94115729573027288949c727f14f3727daf3d72739f5472464c2172301b0f72286c4f721cd833720f098a7205adcc71d3d74b71ca317b71c8678771b7c8f27195975871905291715bc44070e34a0670d9524f
  | 7, 22 => 0x7ed513f37eaca16f7e8031507e5df3ff7e1a8a567dd747b97dc60fd37dc594b27db173387da51d3c7d5fc8b57d2a63907d21396f7cea112d7ca8786f7c9e1f737c9bab697c4bfba17c2948dc7c1abb197bff7fac7bf0d3337bf0b2df7bd0c6937baee3977bab0f147b86605a7b82908a7b6ae8e07b2f19917aface357aea77727ae6a9707ae1d81c7adb64027ada8ab67ad7bf5b7a7f403579f05dc079e15a2879cce61979b70aa9796fc1e1796deb39791c125478e9916b78e4358b78b54ae278ad3fcb78493a7f781b6dbd7819d38577ae3ab077adb12e77abcbfa779c985d778509c2777d8546777652a77746c839773b28e9773496ea772fc2f577231e6a
  | 7, 23 => 0x8788b73e8786ba7887806e58877779c3876bd56a874f92698708035287038fdf86fcb5f186d0ab7b86bb6894869b7594868952b7867726a1865cbae8863f7c598626971785a623a085355bfe849e475c84594c5e8450d9fa844c644984064fcd83ec43f583c7f1fb83b0d4c883814402833df9038323a63b82e8729d82de711782d3eb9982bd697582b45fb2828511a48275807782585f94821853fe81b76e8e81b5860c817be6a28134de5280b2da9b80b2a53b80977014808528c4807ff039806266ad805eb719804fdff58014550b7fe516d97fdec0a27fb50b547fa7685f7f8776eb7f82bf8b7f6323277f4ff8037f172bf77f0df4cc7ef4c7107edbceae
  | 7, 24 => 0x90e225fa90c0894f906d261190578f389049058a902c5a7f8fe77d2d8fc473788f78512d8f76ecae8f74f0a98f63e3fa8f5f11de8f4fefe28f24e6ba8f20258d8eef58df8ee425888e7643fa8e3f8c778e27cd4e8e2302ba8e1426838e0cfa578dce939b8dc0b2f38dbe23998d72216c8ccb4d078caed4eb8ca456c68c76bee98c5e2c4f8c47b39e8c3f36198c3d0db98bee01d98bd322518b607b078b1047578b080e6a8ad2ff418abb56b98aa701598aa44b2d8a81f0ca8a571a718a4b2c568a0b34fc89e468b289c4856389ba9fdf89b52b50899b6c72894ebb5e8948509588ede02888e50a9488d9be1688ade089888f7ea48824c165881af38987923757
  | 7, 25 => 0x9ab52eeb9a8abc959a6914bc9a55e6669a07492d99e5b62f99e3b42599ce680e998829a39977a4e199265abf98e2892c98ce4a8d988d75f4986d00ac9848d5ba9847a6bd98249f8697e2d59297a4f38797885ff99775269297708ba59713ecb1970d416897012b8496f60d7996867f0f967fbfcb965531e6960d324a95db4915956ca7b1955aec719551aacc954adec7953d24269520bde994de200194d4832a94ae1516945654d794302b6c942a4f20940a6f8393f5120693f42b8d93e2499393602c469329f8a2931be89e92fce1fd92cd311e92bdfe3b92aa991692904ad8927d838492012ccf92002a6a918c7c03917fb21d9176ae5f91503a30912b7fc7
  | 7, 26 => 0xa59b37c9a57519cca56effffa54be63aa4dfe492a4c7accca4ae7b11a494c22fa44634c2a416f695a40b50aca3beb5eea39ec2eea390017ea37a73fba32cb193a3098384a26534afa263fdeea1f16defa1e98a93a1e36dd6a1a3dfbba16c4690a1558ee5a13f99cfa0d05094a07b3991a049bbb5a0178350a00b64c39fd738f39fce48649fc0bc2f9fa2555f9f7298a79f726bb59f3cb69a9f307a4a9f281e6a9f22e88e9f1c706f9f19428c9ef130509eda496a9e93ebe99e4b2ef19e418da49e1370af9debfd949d9a91c89cf112e89c70cc409c5f65c29c20d3b29bb0ddf99b791ada9b786e2f9b7395e39b5bed5b9b58bf3b9b34b1219b0c849e9ae5da44
  | 7, 27 => 0xb109447db0a7b14db077cf95b052e84bb038e43cb028f5a0b0231954b02268afb017831caf9cc68aaeb40751ae932178ae82ff77ae40fbc6ae265fb5ae11518cadd493a1ad3bbe89acb5a4bdacb48a93ac9944f7ac98bd20ac87cf69ac7b9e87ac5d1b18ac41cfbeac0421faabfe5a79abe5308aabdf356cabd5fcedabc373b9ab89854eab55c58dab559622ab227451ab193334aad1e0f5aac5def6aaa90063aa93f772aa6f020ca9ebdc13a9bd2c7ba9700ab0a9681578a9679bafa9647ee6a8f0d2eda89eb231a884f245a840633ca83f9187a828f69ba7e69d5ca7470e27a735b1faa70ef21ea6d56581a6c134b9a6563cc3a5f12d82a5f0d5c5a5b36a13
  | 7, 28 => 0xbd6a8f7fbd686373bd386403bd1c3529bcc91ac8bb9f29ffbb80d0edbb727797bb0f98aebaefd317bad4da24babe4381b9e4f0ccb9df8830b9da70f2b9c33d03b99d8907b932cbabb91d4ce9b90d8a13b90994d0b8d9465db88c6d97b862d891b837fe7bb81c8db4b8025b3bb7ad2f8cb7a667eab7694f48b75d88c1b729b85fb7281d8bb7186549b6f964b2b6f77eaab6be7634b691c424b64eb09ab60f96a1b5f36f3fb5bed785b5a79115b593ef12b58b2dc5b51becfdb44008a2b40478deb3e7728fb3e394feb36df0c6b365558ab33f92c7b32e2ba0b325de37b31e2f22b31b8345b3163514b30843b8b276a275b27690e8b24e2c21b1ff7463b18c7b6c
  | 7, 29 => 0xca7e11e2ca4696dac9be5be9c9a3b4fac97fa584c8d8951dc8b75089c89b91e3c85ae621c7d22c68c63e6ab8c5ff83fec5eadd1ec5c517f6c5b5f6afc5b1003bc543b096c52f7576c4f9eddfc4e09fabc4d7a737c4d20e6dc4a50f80c496691ec48fe98ec416706bc40cc959c3e02969c39d801ec3606443c310f424c2eec2c3c2d42780c2afde01c28f46bdc27c2edfc26131dec25c674ac20018d3c1fa1783c1f2ab0ac1eeb825c1ebf1e0c1a3757dc1980f89c154e976c0f590b7bff257a0bfd8f6fabfd1f35bbfa41077bf82fa1abf239619beffe354befa2055bec33186be6f93eabe51e5eebe4be64fbe3add0dbe110a0dbdd154f7bdbe8df7bd82ee2a
  | 7, 30 => 0xd9eccea3d9bf06ebd9965d18d9891486d96359b3d957a573d920e647d89de169d865f783d84ccd00d84bd8e7d803eed7d7272a2ed6f8f5dad69e0a2ed64ffb9bd64c9b36d5e44738d5d57342d568b144d5583fe0d4a8a525d438da3ed3f10f9fd3958842d31dababd28d9f00d26e2c13d267eba2d2294a34d20af5b0d17bf5cfd173caa4d0c5752fd028b587d0188098d00c244bcfba7b07cfaaeb5dcfa1a4c1cf83b5d4cf1f3ed4cf010decce1f1d8dce1ee8e6cd65c46bcd46ee49cd3c3196cd25b609cd19d01fccef89f3ccb4b64fcc9fe01acc8a5c05cc6e82bfcc438988cbedcfe9cbb9f257cb868911cb5221cfcb46a5f8cb2f7209cb20c46eca8e6379
  | 7, 31 => 0xe82d725ee7fca500e73f702ce7283c3de6b00705e67c8f78e65393cae5e351dce5dbe277e5cb74e9e5c2ba49e5b7261de5a66be6e5608b63e5499e93e5495e69e4e88dfde4aa967ae491a641e3fab025e38241c1e329e45fe2f6af66e2f02cffe29f22e5e298b8f8e280ec37e25fc445e213f68ee1e5cc3ae195a639e18ace26e171d949e1283faae11915d9e1151f08e09b3ae1e08bbd81e0800c8de037bf09e03592fddfdba1afdfb32b5bdfafa89bdf1659addede789bde74f913de4eb049ddf8e307ddc64cabdd9de376dd1abbaedd040b83dcf90b68dccf1ccddcc1922bdcbe56d5dbd26c4fdb6940c7dab03a9fdaa10b17da9b4bd4da4ab022da389489
  | 7, 32 => 0xf8c7e701f8bf6874f8ba5c5ff8b72109f87e7dd9f808cdccf7a45692f6e5cf63f65cc66ef5ab4c3ff58f108cf4d74db7f49b46c7f484d313f44d45f4f440fa2ef3a1e699f388060af37d4a6df33384e5f32a1730f31ff462f2f3ae00f2e20aeaf2afc70af2976373f2854adff20c2781f1d8a3a4f1510a14f1360ff9f105951df053c1fdef06a02aeec40f0ceebe9aeaeebaff73ee996037ee2ffce1ee02495bedfca193ededf3f8ed56b179ed515974ed3bc136ecf33ac6ecbb97f1ec8b8b73ec8449e5ec297df4ec04ee7febdb61b4ebbcb677eb023407eaf7f023ea6cc730ea630ca9ea39f55de9f83c15e9c49255e9432f67e8b769b1e8ad37dee849f352
  | 7, 33 => 0xfffb2919ffcceadcff8b865fff6dda91ff3e3073fef288ebfe40f86efe2a185cfe1c6333fd7e81a8fd4ce9b4fd2775d6fcfeb677fcdeef09fcb4fc26fc762b04fc50f767fc3cf275fc1a4b00fc0b585bfbe1c5f5fb19fc8afb195303fab495f5fa7d76fdf9f459b8f9b835b8f9acd0faf8eb2a3d
  | 8, 0 => 0x135211a21317dd2b12e05c4012b8884a12ae5da3129997eb124e26351232479711eb7ccf1187183a11761aa81142fa411134c93410d1aa96103ead2a0fc22fb60f3badb20ea68d810e8414b20e783ebe0db675560d52c9a60d4d98860cf91d9f0cea20e10cc7aa850c2cfbb60c22507d0c167f100bb2ffb10ab0afbb0a71f95609ee1b6f06ecbabd06a150320663442506556796064612c705c61dd605ad2f34059e8b170590310f05869eb105169eb003f3df9703f1b95203e3645403bd1a64036df15003601271033a727c0291d00a024a740d023f103c01a603fb0198251c0196da2a0129b75501013f3600dd496a0086a50c006499150027347900103def
  | 8, 1 => 0x255ffecb24cb7b29246554a62429651523fe6fae233e51982310763b23038dd422f4640322c7351322543c1c223682592227588821a5f96820df43cc2081cc612064873a204aaf2d203e530f203cd04e1fd3d3851f608b651f3d31db1eb3facb1e8eec381e739d441e7359ed1e1aa3ae1e08e1531d989e101d81c57f1d73f5661c53b96d1c1ffead1bea35011be841c11bde45011b78d4bc1b61a0cd1b52f3321b2d157f1a5d39541a2bfa9c1a0ece7019f08aad19b1d448196672e11922d7aa1900f42918e3fb0a183e8305181aa94117d7cb9517d07b00175a929b1729918f170db67f16b50ee915ff8a4715f86a801561a43a15527a69141a4f1c14121a0c
  | 8, 2 => 0x3c39fd5e3b5624293b3c318a3afd7b253acd3e823a8b9b213a8b1a653a861c993a4766343a305add3950034038ad846e3899ed18387c2216375fd1e836f4981f36b6da92363c57f4361b1af4359f67e7359aee6d357bcd57355e29ce3518dab134064f6c3294bf40326a06213255c7c331381b0730ccd1eb3055c0a62fc976f62fa1c82a2f7655c82efbd9642eedfa852ee51d392e9e70832daad2e42d6df75a2d014b912cf3c0ef2cb7e2692bdd94e82ba0a43a2af4104e2acd7a982a60bc7d2a5175e429e942c42889888f287a5ebe2775450f2774c460275958f22752ae7526e36c2426d2458e26a4b5bf264ea12126396ad4262d41fb259eb530258a6ea4
  | 8, 3 => 0x4f8511f34f717d1d4f0fba7a4e5bae794e1db72a4e1717654e00c0ea4de27c5e4dd111674cd8ba054ca60af44c4c79c44c173de94c1326ad4bff26be4bf147df4b62f61f4b40518f4aee73794ac0774d4a0d1974499b08ca49148db048fa38cc48f889f848f0bd7d48b0ac9d484e6acf475141bb472e33c146e1bded46e149a245f6b58445c07cca457c5ed1454d83ff45179a8f44d9dfff43cee64d43555fb0433f660a432891ef4309ffd842f65e6542b779a341d9fb7841d622d341a8390641a4b5d6413f306a413ca69640db2d8b405c8f3d40455b7a3f49363a3ee6de3d3e277fff3dc32c533d8620523cedcf813cea22ce3c9f3cdf3c52b0633c3d4942
  | 8, 4 => 0x6336351163353df463275f156292bf226284e0436240ab8761f427ee61aa33686129ea2960d158046001a2b65fd513de5fbac6fd5f2a63495ebcebc25e22a7545e191a245e06e6065d9647d45d93d62e5d7bf2db5d6275f45d534c235d3a46645c91de815b4388f85b2acd595af03eb05aa8a6b95a437adf59e5330159d66aa059d395c75916f56256dbe56f56da22f0568ff7f1567ee6cd5640306855df5df855bb43f7558b875054ed1c755342fdb7531915d1530ec13f52acbe7d528ca242523dc211520a3fab51d2062b51bb2a0f51a4e007516924ff515c291951099cc651007c3a50b58b1c505beeb35059633d4fb2394c4f9b055d4f943bc44f8c57c2
  | 8, 5 => 0x7f1797dc7e8559377e1a8a567db1e1917dad4e397d776c2f7d33ff317cea112d7cd372a07ac854af7ab597257ab2c9087aa157477a85129f79c9043d791d9b417900675a78f13d897892577578493a7f77d135d077211a3f76f0916b76db0b2e764e5f61748c6eb5745a681c73f60c3a72b283397260e48f71be65bd707cee8d705b5d9f7005f1236fa6c90d6f69601f6ebe77696e834bca6e38e6f66ddedbb86be1bd3a6bcb63fb6b89f08a6b6909ce6b46b4d16b1be3666a7ff6686a5eea176a510b386a4fc62d69c031bf69b2eaed68ff5c7d683fb3fc67f1c0d3668c47706554bad1651506a464ffcc4e64cf00c564789948645092fc6401590263669d95
  | 8, 6 => 0x9c27c3cd9c1021289b71391a9b1dd7b09a36658d99ed5e879985b80798d8396997a5128c97012b84963c456d955a089893527dd5934043b892a6c201928cbda5925c0be491b98d12917fb21d91426eab906d261190061e318f46f2108e35cdb08e27eed18d92f6958d7f04bb8d6bb4b28d5eaaf98d1e3ac28bc68b508bbc73f08b8fda438b308e208aef68758a18c288897643b68968a0cb895976fa886bb2a58788b73e877910e2876b320387080352869b7594867726a18651842c85f48e9f85520fcd851cbe16850f030e8492c7cd83f048fb83c5bc52838341f483833bd783233d80830766bf828511a482739f2082121d0d7fe35f827f97da8d7f27d809
  | 8, 7 => 0xbee065e9bd5c9ba0bd2744b8bcc8e334bc5e25f5bb0a100bbad4da24bab08b31baa8a17cba2399e2b96ec08eb959c3c0b84d21e0b7610a65b6edc245b6be7634b69fded2b65f3e8fb5c9ec3db5195244b315333eb2f03ccbb253eee6b20ffb62b1b17014b12375bdb0f51e5bb0ec7e1fb0e1dcffb080f6ebb0480e0db038e43caf95e2ffaf935789af01b67aaee65ee3aec64c0eae8d3699ae5c9576ae064aa9ada32de2ad85a160ac23afedabe5308aabbe6e52ab681b8eaa87c3f1aa38618daa2867c5a9cb11c2a98c5b5da8e78fc4a8d69abba80d4bfda8098f40a6563cc3a4a02823a36baaf7a1f16defa0c045e2a07b39919ffd08839e6bbe4b9d3508f4
  | 8, 8 => 0xf05fc8f2efeaeca8ef0e3eb4ee6bbfe2ee22ff53ee13d582ed71b5aeed5612f6eca193e2eb3fcd10eaf7dac4ea72c195ea555bf2ea39f55de9d3bc26e9c49255e9599105e8b03ee3e81cf98ee7a75556e73f702ce7283c3de5d4dd4ce575a6eae4625a30e2f7dbbfe07b344ee04a17a1df7fbf91dede789bde1b0bb2dd9de376dd547ea2dc240579d9194922d8f62b1fd8e7dfa1d7d8277ed7c2c847d69e993fd697c1d4d6890d25d62ad27fd5d7c256d56748abd355d4ffd1d3f658d1b38e6dd051c79bcf9551ebcf84bc20cf6e15b1cecb96dfce6b8b90cd5fbf4fcc0b8b0bcb46a5f8cae6d7d7c9d46458c6f762cbc398766ec31b6fd9c1c6e06ebef4bb49
  | 8, 9 => 0xff5a28fefe12eeb4fce2758bfab495f5f9091127f646c3bff637ead7f62c0f9af2e571d9f2854adff22186e7f11d8484f0c5c7cb
  | 9, 0 => 0xbad4da24b6be76347cea112d5e22a75455df5df851bb2a0f5059633d4f8c57c24aee73793e277fff2efbd9642eedfa851e7359ed1b78d4bc1142fa41
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 5, 0 => 0x84109000000000000c000000000000d000000000000c0000000000004000000000000b000000000000c000000000000d00000000c810a000000000000b000000000000d00000000000000000000000005
  | 6, 0 => 0xe1010000000002104000000380a2020000003802203000000000000900000001051040000051081200000000000000c0000000000004000000000000b000000001210400000544c82010000000000015000000000a1020000042041203000000000000a000000480e202000000000a102000000000e1040000052041200000000000000700000214842000000002806200000000000000b000000000001300000324c8201000000000000a0000000000010000000000a10400000520c120100000000000080000000000008
  | 6, 1 => 0x2104000000000000900000324c8201000000000e1010000000000000000000000000b0000000000009000000000210500000530812010000000105105000000000a104000000000000b00000000121040000000000013000002148420000000000000070000054480201000000480e20000000000000060000000012101000000000000c0000000006105000000001210500000000021000000052041200000000000e1050000000000008000000480620000000000061040000000000007000000000000d0000000000015
  | 6, 2 => 0x1210100000038022020000000000007000000480620000000000000070000000012100000000000610100000000000120000000006105000000010510400000514802010000054081200000000000a104000000380a2030000000012104000000280620000000514c82010000000040103000000000000400000018022030000053480200000000000000a000005348020000000430412030000051480201000000000000b000000001210000000204802030000000000009000000000000d000000480e201000000000a105
  | 6, 3 => 0xc1104000000000000d0000054081200000000008410900000000801020000020480200000002048020000000000c8114000000480e201000000000210400000038062010000000012105000000000000b000005204120000000000000130000003802202000004108120300000000000150000000002104000000008010300000048062000000000000014000000000000d00000000000130000000000009000000380a201000000000000000000000021040000000000006000000000001000000000121050000000000010
  | 6, 4 => 0x380220100000000000140000000002101000000000a104000000000001300000000000130000000006101000000000e10500000001051050000000000009000000000000a000000000000d00000000c11050000053480200000000000210400000000061000000054480201000002048020200000000000090000000084109000000000000700000000c110400000038022000000000012101000000480a200000000000000c000002148420300000018022000000001802200000000380620100000540412000000000105104
  | 6, 5 => 0x6000000000000d000000480220200000000c1105000000000000800000534802000000002802201000000480220200000324c820200000544802010000000105104000000000001300000000841030000000002100000005210520000000514c0201000000000000900000000000140000000000008000000000000b00000000000070000000000008000000000000b000000380620100000000c11050000002806203000000000000b00000214842000000000000007000000000000b0000000002104000000000a105
  | 6, 6 => 0x11000000000e10200000520c1202000000000000700000000000100000003802201000000000000b00000514c82010000053440200000000000001100000000000110000051480201000000010110a000000010510500000544802010000000002105000000000210100000000000060000004802202000000280220200000000841090000053480200000000480620000000430812030000021484203000000000a10500000530812020000000000006000000000000000000048022010000000006105000000000000c
  | 6, 7 => 0x1000000000000130000000006100000000000000b000000000000b0000000084109000000000000d0000053440200000000000000c00000000000110000003806203000000000000b000000380220300000324c8202000000000000800000018022000000000006105000000000000900000000021040000000040103000000000000b0000042041203000000000000600000018022010000051081200000000010510500000000000130000000000015000000000001100000544c020100000000c81140000000000006
  | 6, 8 => 0x11000000000000e00000534402000000000000004000000000000d000000480220000000000000090000000002104000000480220000000514c0201000000000e1040000000000014000000000a10000000000000060000052041200000000000000c00000520412000000000000012000000000000900000000c1104000000000001400000504c82010000021484200000000000000b000000000a10500000000000070000001802200000000380a2020000003802202000000000000b0000002802200000000000e104
  | 6, 9 => 0x700000000121040000000000009000000000e10500000038062000000000000008000000000000b0000021484200000000000e104000000000610400000000000050000000000006000004304120300000000000100000020480201000000180220300000000000110000002802201000000000000a00000028022000000000000004000002048020300000520c1201000005408120000000544c0201000000280220000000544c02010000000006104000000000001300000324c82020000000012100000000000000d
  | 6, 10 => 0x54041200000000000001500000000061000000000002105000000000001100000000000040000000006102000000000610400000540412000000000080103000000000e104000000000001000000504c8201000000000000b000005404120000000000000130000000000006000000000000b000005408120000000018022000000021484203000000280220100000000000090000000000000000000380a2010000000012104000005308120200000000000020000010440200000000480a20200000214842030000000000006
  | 6, 11 => 0x210000000000c810a000000000a104000000000001300000000000060000000002102000000000000a000000000210400000324c82020000053480200000000380a2010000000002104000000000000c000000001210200000504c8201000000000000d000000000610400000000000130000000000015000005108120000000000c810a000000008010300000000c1104000000000001100000514c820100000520c12020000004802200000000001210500000324c8201000000008410900000000000090000000006105
  | 6, 12 => 0x2806200000000480220000000000401030000054041200000000001210500000304c0201000002148420000000324c82010000000000005000000000001200000000061040000000002102000000000001100000544c8201000000008410900000324c8201000000010510500000000c110400000000000080000000000006000000000a10400000000000010000000000007000000280620000190324c830200000000c1104000000000000d000000000e10400000510812000000000000013000000000e1050000000105104
  | 6, 13 => 0xa104000000000610100000324c820100000000c11050000002806203000000000210100000544c82010000000006105000000000001300000324c820100000018022010000004802200000000000000b000000000000d0000000000010000000000000d000000000000800000304c020200000000121010000000000011000000000000d000000000000000000000021050000000000006000005404120000000000000130000000002104000000000000900000000000020000000000014000000000000800000000c1104
  | 6, 14 => 0x61040000054041200000002148420000000214842000000000000001000000000001500000514c8201000000000000b0000000000011000000000001100000000021050000000084103000000000e10400000028062000000002806200000000000000c000000000000a000000000000200000214842030000020480200000000000000d000000008410900000000000130000000002100000000000000d000000000000a00000048022000000053440200
  | 7, 0 => 0xa1010000004802200000000000e10100000324c820100000000061030000000084103000000000000b0000000000015000000004110100000000121020000000000005000000000000100000000000040000001802200000000000e105000000280220200000000021020000000002101000000000000600000000c5101000000008510300000000000000000000002102000000000e10300000000801000000000002102000005408120200000000000040000000000002000000000000500000000000130000000012100
  | 7, 1 => 0xa000000000000600000000061030000054041200000000001210400000000000000000000000001000000280220200000038022000000000006101000005348020000000544c02010000000081101000000000a10100000000000050000000000004000000000a1030000000002102000000000000400000000000020000000000004000000000a1020000000000001000000000001000000324c8201000000010810000000304c0202000000000000000000000000130000000000006000000000000a00000000c1101
  | 7, 2 => 0x4000000000001300000000021010000054081200000000010910100000000c0103000000001210100000000c810200000000121000000000000004000002148420000000000841000000000040100000000000e10200000000021050000004802202000000000000c0000000000011000000000001100000000000090000000080100000000480220000000000000060000000012101000000000e1020000000000006000000004110000000000000000000000041100000000280620100000000061030000000000015
  | 7, 3 => 0xe101000000000001200000000021040000000006100000000010810000000000c11010000000040103000000000000a00000000121040000000002104000000000210100000324c8201000000010010000000000021020000000000006000000000000d00000000061000000000000001000000000a10300000000061040000000002103000000000000b0000003806201000000000a10200000430812030000000000004000000000000d000000380a2010000021484203000000000000400000000021010000000000004
  | 7, 4 => 0xd000000000000c0000000000007000000000a1040000000080103000000000000200000000021040000000000006000000008410300000000c8103000000000000100000000000040000001802202000000008410300000001091010000000104100000000000000d0000000000006000000000000a000000001210000000000000070000000000009000000000000800000000801010000000000007000000000000700000001051020000000000006000000000000000000000021010000000002103000000000a100
  | 7, 5 => 0x2103000000000a102000000008410300000000021010000004806200000000008410300000540c1202000000000000a0000000105105000000000001400000000c01010000000002104000000000a1000000000000004000000000e101000000000000800000324c820200000000c9101000000000a1010000000080102000000000000a0000001802201000000000000500000514c82010000000002100000000000a100000000000a10500000000021010000000002104000000000000200000001001020000002806201
  | 7, 6 => 0x20000000002100000000000000800000000021020000000000012000000000e1010000000002102000000000000600000001081000000000000004000000000e101000000000000a0000000002100000000000000a000000001210200000000021000000000000001000000000a10000000000000040000052041200000000000e10400000000c0102000000000e102000000010410000000001011010000000000001000000000000d0000000000005000000000a101000000000000700000000000060000000081101
  | 7, 7 => 0x21000000000000004000000000a10200000000c41000000010440200000000000000a00000000000000000000002101000000000000900000000021020000053440200000000000e102000000000610100000544c02010000000105104000000000a101000000000000400000000c8102000000000000200000000000070000000100100000000000000d0000000000000000000008010200000000000120000000000009000000008110300000000000110000000000000000000000000400000000021010000000002101
  | 7, 8 => 0x10000000000002000000000000800000000000070000000000002000000000000400000544c020100000304c0201000000001210000000000000060000000000001000000380620200000000000000000000002101000000000000c000000000000600000000000140000000000002000000000e1050000000000006000000000610500000000121020000003802202000000010510400000000c41030000000000004000000000001100000000000050000000000015000000001210000000000c8101000000000a102
  | 7, 9 => 0x8010300000000000000000000105102000000000000500000028022000000000000004000000000e10200000000000100000000000000000000000a100000000000610000000000c11010000000000004000000000610000000000000070000010440200000000000000000000324c8201000005108120000000018022000000000000005000000280220100000000411010000001802202000000000210100000000841030000000000009000000000000d0000000000005000000001210000000000c41030000000002102
  | 7, 10 => 0x210000000000000110000000002104000000180220200000000021010000000081100000000000000a000000380220000000000000020000004802201000000000e101000000000001300000000000040000000100100000000000000400000000000010000000002104000000000e104000000000000a000000000000800000000000010000000000001000000000e102000000000210100000000061020000000000004000000000a105000000000000b000000000000d000000000a10500000000000040000000002101
  | 7, 11 => 0x38062010000000012104000000000a100000000000000400000000c8101000000000001100000000021050000000006103000000010d1010000003806203000000000000800000000000020000000002100000000000a1010000000000002000000000a10000000000021010000000012105000000000001200000048062000000000084100000000008410300000000000040000000000002000000000000a0000000000007000000390520200000544c82010000000000006000000000a10500000000000080000000000002
  | 7, 12 => 0x84103000000000210200000000401030000000080102000000000210000000000000070000000002101000000000000400000000c0101000000000210300000000000080000000012101000000000e1010000000006100000000000a10300000000021000000000000004000000008110100000000021000000000002100000000008010000000000061000000000000004000000000000000000000000020000000000007000000000210000000000061000000000002100000000000a102000000000a1020000000105105
  | 7, 13 => 0x800000544c020100000000801000000000006100000000480a20200000000000000000000002102000000380a20200000304c0201000000000e101000000000a100000000000000a0000000000002000000010510400000038022010000000000008000000000000800000000401000000000006104000000000000a0000000000010000000000e103000000010c10000000000851010000000000002000000000e1000000000006100000000000a101000000000e1010000000000009000000000a1010000000084100
  | 7, 14 => 0x5000000008110000000520c120200000000061050000000000010000005108120000000000801000000000000004000000000e10400000000021010000000002101000000008510100000000c81020000000000007000000000a102000000000a10500000000021020000000000008000000000a103000000000000400000000c8101000000000e1050000000000001000000008410300000000000000000000006100000000000a10500000000000050000000002103000000000000c0000000000005000000000e105
  | 7, 15 => 0xc810200000028062000000000000009000000000000400000000121020000000002101000000000000800000540c9202000000000a1020000000002101000000008010300000000c01030000053081201000000000000a000000000e1030000000000012000000010410000000000021040000000002100000000010010200000000000050000053480200000000000000b000000010110100000000801030000000000005000000000000000000000061010000000000008000000000000700000000c11010000000000005
  | 7, 16 => 0x1044020000000540412000000000002100000000000000a000000180220100000000c4103000000000001100000000000050000000000002000000000000700000000000070000000012104000000000000400000001081020000000006104000000000a1040000000000005000000000000c0000000000005000000000210000000000000010000000000008000000380a20100000000000040000004802201000000001210200000544c020100000000000010000000002101000000008010200000000000050000000000013
  | 7, 17 => 0x81100000000000a1040000000002102000000000a103000000000a1030000000084100000000000000b00000000c010200000000000130000000100102000000000001000000000000050000000000001000000000000d000000000a102000000000a103000000000a1000000000000000000000000000a000000480e20100000000021010000000002101000000000000700000000c110500000000000000000000041101000000000a104000000000e10200000000000010000001802200000000380a2000000000905202
  | 7, 18 => 0x1000000000001100000000000080000000084103000000000001200000000000040000000000008000000000000100000000000000000000012100000000000001100000000021020000000000004000000000210400000000021000000000000001000000000000600000000061000000000006101000000000a1010000000000005000000008010100000000c0103000000000a10100000000000060000000002101000000000000f000000000a104000000000610000000000c01030000000002100000000000e101
  | 7, 19 => 0xe102000000010010000000000021020000000006105000000280220100000000000030000000002100000000000a1040000000012101000000000610000000000000070000000000002000000000e1000000000000007000000000e10100000000000070000000000006000000000610000000304c0201000000000210000000000c81020000000012100000000010010000000000000050000000000000000000010c10200000000000030000000000008000000000000400000000000020000000012102000000000e105
  | 7, 20 => 0x214842000000020480200000000008410000000028062000000004802201000000000000900000000000050000000000004000000000000700000000000070000004806202000000000a10400000544c0201000000000001400000000061040000000006100000000000000b000000000000d00000000000050000000000001000000000a1020000000000009000000480220200000000121040000000080101000000000610500000000000060000020480202000000000000800000000c9101000000000a101000000000a101
  | 7, 21 => 0x8110100000000c1101000000008010200000000c910100000018022030000000012100000000000e10400000304c02010000000000007000000000e100000000010010000000000c11040000000006100000000000a10200000018022000000000000004000000000e101000000000000c00000000000020000000000002000000000000d00000204802030000000000005000000000000d000000000e1000000000000005000000000000b00000000000110000054081200000000000000b000000380a2020000000000000
  | 7, 22 => 0x8410300000000000120000000006102000000000000600000000000020000000000000000000000a1050000000000009000000000a1010000000000004000000000000600000000c4103000000000610300000000000040000000002100000000000a1050000000000009000002048020100000028022010000000000005000000000e1020000001802201000000008510000000000c8102000000000e101000000000000000000000c1104000000000000200000000000010000000006100000000000a100000000380a200
  | 7, 23 => 0x61000000000108100000000000001400000000000070000000002100000000000a10000000000851010000002802202000000008010300000000c0103000000000000800000000121000000000000001000000000000600000000000130000000000001000000000e1020000000100100000000000a101000000000610300000000000050000004802201000000000a102000000000000400000304c020200000000000140000000000008000000000a102000000000001500000000061030000000000014000000000000b
  | 7, 24 => 0x10d1010000000040100000000000e10100000000021010000000000005000000001210000000000000070000000084100000000000000500000000000040000000105104000005204120000000001001000000000101101000000000a105000000004110000000000000040000000000004000000000e102000000000e1050000000002101000000000a100000000000e103000002048020200000000000150000000006100000000000001000000000000030000000000015000000000e102000005141220200000000c1104
  | 7, 25 => 0x21010000000006101000000000e101000005308120200000000000050000000006100000000000a104000000000210300000000000080000000012105000000000e10500000000c1104000000480a202000000000a1000000000000001000000000610000000000061000000000012100000000000e104000000000000d000000000610000000000801010000000000012000000000e10100000000000150000000012101000000000000200000000000060000000006105000000000000500000000021040000000000009
  | 7, 26 => 0x18022010000002802201000000000000a00000000000070000000080102000000000000400000000000010000000002104000000008010200000000c8102000000000000c0000000006100000000000210200000000000000000002905202000000000000200000304c0201000000001210500000000000000000000000008000000480a200000000000000b000000000210400000540c120200000000021020000000000004000005408120000000000021030000000000012000000000000a00000000c11010000000000005
  | 7, 27 => 0x600000000021050000000080100000000000a102000000380620000000000c510100000048062000000000000004000000001210400000000121000000000081101000000000610400000000841000000000000012000000000e1020000000002100000000000e101000000000000c0000000000005000000000e102000000000000000000000c9101000000000000500000000000060000000000008000000010410000000000c8102000000000610300000000841000000000002103000000000000d000000000e100
  | 7, 28 => 0x6100000000000e1010000000000006000000000a100000000000001000000000021000000000002100000000480e20000000000000040000000002100000000000000500000000000040000000002101000000000000600000000121050000000000011000000000a1010000000006102000000000000d0000000000008000000010510200000000000140000000002100000000000a103000000000000a000000000000a0000000000011000000000000600000000841030000000041101000000000a1010000003806202
  | 7, 29 => 0x5000000000a100000000000210200000000000040000000006103000000000e10100000000000000000000000004000000000000600000000c8102000000004010000000000000010000000000009000000001210100000000c010300000000c1104000000000210000000000021010000000040103000000000e10100000000411010000000006102000000008010100000000000010000000101100000000000e1030000000000006000000001210000000000000040000000000010000000000e1020000000105104
  | 7, 30 => 0x61040000000000006000000480e202000000008010000000000061010000000041103000000000000b000000000a105000000000a102000000000000600000001091010000001802202000000000210000000520c120200000000000060000000000004000000000000600000000c810100000000121010000000002104000000000e1020000000006100000000000e10200000000061050000000000004000000000000500000001001000000000000008000000000000500000000000130000000000005000000000a104
  | 7, 31 => 0xc110400000544c0201000000000000d000000000e1010000051081200000000008410300000000c01030000000000010000000000210500000514122020000000000006000000380620000000000000110000000000008000000000e101000000000a10000000001081020000000002100000005348020000000000000040000000000000000000000a10200000000000020000000081103000000000000a0000000109101000000000000a0000053081201000000000a105000000000610500000000000000000000000010
  | 7, 32 => 0x9000000000a103000000000000900000000841000000000905202000000000a10300000000000120000000000007000000000000400000000c8101000000000e1010000000000007000000000210000000000021020000000000009000000000000d0000004806200000000000001200000000401030000000002101000000000000400000000000060000000084103000000000000700000000c11050000000000006000000000610300000000021030000000000003000000000001400000000801020000000002102
  | 7, 33 => 0xc910100000000021030000000084103000000000000000000000c810100000001041000000000012105000000000210100000000121010000000000000000000000000600000000c8101000000000000e0000000041101000000000e105000000180220100000000000080000000002100000000480e200000000000a102000000000a10100000000000060000000000008000000000a1020000000000004000000000210200000000c4103000000000000700000000000080000000002100000000000e1010000000000008
  | 7, 34 => 0x100000000121000000000002100000000000a104000000000000200000000000060000000000008000000000001300000000000040000000000004000000000e104000000000210000000000000130000000006100000000480a20000000000801010000000012100000000000000200000000061000000000000011000000008410300000000000010000000000004000000000000c000000000e101000000000a102000000000a1050000000012105000000008110100000000000080000000002101000000000a104
  | 7, 35 => 0x5000000000a10300000104402000000000000013000000010d100000000000a101000000001210000000000000000000000000012000000000610000000000000120000000012102000000000a10200000000021050000000006100000000000a100000000000610000000000841030000000084103000000000000d0000000012100000000004010000000000000080000000002105000000000000b0000002802202000000000000400000520c12010000000080100000000000210000000000121020000000000008
  | 7, 36 => 0x700000000401030000000000013000000000000600000204802000000000000015000000000000a0000000012100000000008410300000001011010000000000014000000000e10000000000000050000000000007000000380a202000000010d1010000000006103000000010110100000000c010200000000c81010000000000015000000000e100000000000000800000534802000000000000007000000000a101000000000000800000000121000000000000009000000000000500000000000050000000006101
  | 7, 37 => 0xe1010000000006100000000008010300000000000090000000000000000000000610000000000021000000002806200000000004010300000000121010000000000004000000008410300000000000120000000100100000000000a1010000000105105000000290520200000324c82020000001802200000000000210400000000000070000000000004000000010c10200000000000040000000000000000000000000200000000000130000000002101000000001210500000000c010300000000000060000000000002
  | 7, 38 => 0x1000000000210300000000021000000000002102000000010c1020000000002103000000000000d000000000a10400000000000070000002806202000000000a10100000000c81020000000000002000000480a201000000000000c00000000c11040000000085103000000000e101000000380220000000000000060000000000009000000000a104000000000000600000540412000000000002105000000000000c000000000a1010000000084103000000000a101000000000000b000000000000500000520c1202
  | 7, 39 => 0x400000000021020000000006100000000000210100000000061000000000105104000000000e104000000000e10300000000000060000000012101000000000610100000000061030000000000007000000000e101000000000e1040000000006100000005408120200000000061050000004806202000000480e20100000000000010000000000004000000008110100000000021050000000000007000000000a100000000000e10200000000000000000000012102000000380a20000000000000060000000000009
  | 7, 40 => 0x1802200000000004010000000000000010000003802202000000001210200000000c8103000000000000d0000000006100000000000a102000000000000d0000000006100000000000000400000000411010000000000001000000000a10100000000000140000000000004000000000610400000000c110500000000c8103000000000210200000000061030000000000004000000000000400000000000010000000012101000000000610000000000811030000000006100000000000610000000000000050000000000000
  | 7, 41 => 0xa101000000180220000000000000000000000000006000000480e201000000000a102000000000610000000000000040000000000006000000000a101000000380220000000000000110000000012100000000000a1040000000000012000000001210200000000000060000000012104000000380220100000000000010000000040100000000000210200000324c82020000000000000000000380a201000005308120100000000000090000000080103000000000e101000000010110100000000121020000000000014
  | 7, 42 => 0x109101000000000a1010000000002105000005308120100000324c82020000003806202000000001210200000001011010000000000004000000001210200000039052020000000012100000004204120300000000c0103000000000000400000000c81010000000104100000000000000d000000000e10100000000000110000000002102000000000000a00000000c8101000000000000100000214842000000052041200000000000210300000000000010000053480200000005344020000000000061020000000002101
  | 7, 43 => 0xa105000000000000d000000000000400000000021000000000000001000000001210100000000000070000002806201000000000610100000000851000000000000006000000008510000000000000060000000000000000000000000500000000811030000000000007000000001210200000000000070000000012104000000000210500000000000110000000100100000000000000b0000000006100000000000210500000000000070000000006101000000000a101000000008410000000000801020000000000002
  | 7, 44 => 0x6100000000001210000000000841000000000000007000000000210400000038062000000000006104000000000a102000000000210000000000061010000002806200000000000000b0000000000004000000000a1020000000006104000000000000b0000000081101000000000a10100000530812020000000000000000000000000400000000c8101000000000210200000000000110000000002100000000000000000000000000140000000012101000000000610000000000841030000000002100000000000e103
  | 7, 45 => 0x40000000105102000000000000a0000000000000000000000000a0000000002104000000000000800000000000000000000080100000000010810000000000000080000000000004000000000000000000000021000000000000009000000000000100000000061000000000105105000000000a1020000000002101000000000a104000000010110100000000061000000000012100000000000000400000000061010000000041100000000000001200000000c1101000000000a1000000000000004
  | 7, 46 => 0xe102000000010110100000000c8102000000000210200000000000090000000002100000000480a20100000000000090000000000004000000000e1000000051412202000000480a202000000380620100000000000090000000000004000000000000800000000000000000053081201000000000000d0000000000009000000000000700000000121000000000002103000000000000700000000000040000000000009000000000e10300000000000060000000000001000000001210100000000021010000004802200
  | 7, 47 => 0x101101000000000001500000000c0103000000000610100000000801030000000000000000000000a1010000000109101000000000000d00000000021010000000081101000000000210000000000000020000000000000000000000000500000000000080000000000001000000000001000000000021030000020480202000000000a105000000000000d000000000210200000000000080000000084100000000000e1030000000002105000000000000400000000000000000000012104000000010d1010000000000007
  | 7, 48 => 0x9000000000610000000000000060000000000008000000000000600000001001020000000000004000000000e10300000000021000000000040103000000000210200000000021020000000000012000000000610000000000021040000000000004000000000a102000000000000400000000c8101000000000000b00000000000040000000000006000000004010300000000000040000000002100000000480a2010000000000002000000000a1040000000002102000000000210200000000021000000000101101
  | 7, 49 => 0x60000000000008000000000a10200000000841090000000012104000000000e10100000000000020000000000002000000000000400000000c4103000000000000400000001051020000000002102000000010d101000000010110100000000021020000000002100000000000e10200000000c81010000000085100000000000210200000000021000000000002100000000000210100000001011010000000002104000000000000a00000000801020000000000007000000000210100000000021020000000000005
  | 7, 50 => 0xd000000000001100000000061000000000084100000000000000400000000000070000000002101000000000e1040000000000008000000000000a0000004806202000000001210500000544802010000000100102000000000210200000000000070000000000004000000000a10500000000021030000053480200000000000000200000000021010000000000014000000000000a000000000000100000000c91010000000002102000000000210000000000c9101000000000000600000000021040000000105104
  | 7, 51 => 0x1210100000000121050000000000012000000000e10300000000021040000000000009000000000000d0000000000015000000000e102000000000000d0000003802201000000000a101000000000000600000000021030000000000006000000000610000000000000030000000105104000005408120200000000000020000000012101000000000e1030000000000004000000000000100000048022000000000000004000000480220200000000000000000000002102000000000a10200000000000130000000000010
  | 7, 52 => 0x9000000000210300000000000010000000000002000000000000a000000000000400000000000040000000000002000002048020000000000021040000000100100000000000001400000001041000000000000004000000000210100000000000080000000002102000000000000b0000000002101000000000210300000000000000000000000015000000000a103000000001210000000000000120000000081101000000004010000000000021030000000084103000000004010000000304c02020000000000008
  | 7, 53 => 0x6104000000001210100000000c0103000000000210100000000411000000004802201000000000210000000000000090000000000001000000000e105000000000001000000038022000000000000014000000000e100000000280220100000000000020000000002101000000000000000000000c11000000000000008000000000000a000000000001500000001091010000000000002000000000000b0000000012104000000000e10200000000000110000000104100000000000000c000000000e102
  | 7, 54 => 0x800000000061010000000000002000000000a10000000000801020000000100102000000008410300000000000010000000000004000000001210100000000000050000000012104000000001210000000520c1202000000000000900000000021010000000000008000000000a100000000000210100000000841000000000012100000000000610100000000000010000000000006000000000a1030000000085101000000000a103000000000210100000000c5100000000000210300000000851030000000000009
  | 7, 55 => 0x60000000000006000000000a10300000000000010000000104100000000180220200000000021050000000101101000000000a103000000000a10500000000021030000000000005000000000e1050000000000004000000000210000000000000050000000081101000000000610100000520412000000000000005000000000a1050000000000005000000000000b0000000000010000000000a102000000000210400000000121000000000000013000000000000200000000061000000000000011000000000a101
  | 7, 56 => 0x60000000080100000000000000d000000010510500000000c01000000000002100000000000210300000000061010000000000011000000000210000000000000020000000012100000000000210100000000000010000000002102000000000e10400000514c020100000000021010000000002103000000000000500000000121010000000002101000000004010000000000000010000000002103000000008510000000000121050000000002103000000000a10500000000841030000000000004000000000e101
  | 7, 57 => 0xc000000000000b0000000000009000000000001300000000021040000000000006000000001210200000000c0103000000000610100000000000040000000000000000000000000c00000000c9102000000000001000000000021000000000905202000000000610000000000000000000000002100000000010110100000000c810200000000000060000000000007000000000a10200000000801020000053504200000000000a10100000000000110000000000005000000000a10100000000000000000000000002
  | 7, 58 => 0xd000000008410000000000000010000000012100000000000210200000000000000000000012105000000000000400000000021010000000000008000000000000d0000003806200000000000210300000000121050000000085103000000000000600000504c8201000000004110100000000000020000000000002000000000610500000000841000000000002101000000000e10100000001081020000000012100000000000210100000000000060000002806202000000010010200000001011010000000000001
  | 7, 59 => 0x50000000000013000000480e2020000021484200000000480a2000000000040100000000000000900000540c120200000000c1104000000380a2020000000000004000000000000d00000000411030000000084103000000000210400000000000040000000084103000000000a101000000000000800000000c1102000000280620000000000000040000000006104000000000e10100000000000060000000002100000000000000b00000000061010000000105104000000008110200000000000000000000084100
  | 7, 60 => 0x480220200000000000000000000040100000000480e2000000000012102000000000210000000000000040000000012102000000000210100000000000080000000002105000000380620200000000000110000000101101000000000e10300000000121010000000100102000000008410000000000000140000000002101000000000000c0000000105104000000000000c000000000210400000038022030000020480201000000000000a0000000002101000000001210000000000121020000004802200000000000e101
  | 7, 61 => 0x600000001011010000000002101000000000610200000000000080000000002103000000000210200000000000010000000100100000000380a20100000000000000000000006100000000001210000000000000090000000006100000000000000000000520c12010000000084100000000010510500000324c820200000000121000000000100102000005404120000000000121010000000000007000000000000a000000000a10000000214842000000000002100000000000000400000000000150000000000001
  | 7, 62 => 0x12000000000210500000000021000000000000005000000008010200000001011010000000000001000000000000c000000000000b000000000210200000000c810200000000021010000000080100000000000210100000000021000000021484200000000000210500000000c01030000000104100000000000e101000000010010000000001001020000000012102000000480e20000000000021010000000041101000000000000900000000000080000000084100000000000e103000000000210000000000c8102
  | 7, 63 => 0x324c82010000000006100000000000210000000000021020000000002103000000000000a000000000000900000324c8201000000004010300000000021040000000002102000000380220200000000411010000000101101000000001210200000000000000000000002104000000000210000000000061010000000012101000000000210200000000021010000000002100000000000210100000001001000000000002101000000000000100000000000000000051412202000000000000900000000000080000000080102
  | 7, 64 => 0x841000000000041101000000000000400000000021030000000002100000000000000100000000000110000000000000000000010510200000000021000000000002100000000000e101000000000001200000001011010000000000001000000390520200000000061020000000002103000000000210200000000000080000000000009000000000000200000000c91020000000006102000000480e201000000000210100000000021000000000100100000000000000b00000000000000000000101101000000480e200
  | 7, 65 => 0x2102000000000000800000038022000000000002101000000480220000000000000080000000000002000000000000900000000c0103000000000a1040000000104100000000008510000000000061010000000084103000000380a2010000000905202000000001210100000001011010000000000001000000000210100000000c810200000000021000000000012100000000000000e00000000000130000000002101000000001210000000000801020000000002103000000000210000000000000090000000000010
  | 7, 66 => 0x12101000000000210000000000021010000000012101000000380a202000000000210200000000c8101000000000000200000000021030000000085103000000000000200000000c8101000000000210100000000021020000000000006000000000001400000000000060000000000001000000001210400000000000070000004802201000000380a2010000000000001000000000210100000000c81010000000000000000000280620300000000000040000002806200
  | 8, 0 => 0x21010000000000004000000000000000000000000020000000000006000000000000500000000000000000000012102000000008110200000000000020000000000004000000000000500000000000000000000000005000000000000300000000000010000000100100000000000000100000000000050000000041102000000000a100000000010d1010000000006100000000000a101000000000000000000000000000000000000002000000000000200000000811010000000085101000000000e10300000000c9100
  | 8, 1 => 0x40100000000000000100000000000010000000041103000000000000000000000000010000000000004000000000000500000000411000000000000005000000000e10100000000000020000000000005000000000a101000000000000200000000411020000000080102000000010d101000000000000000000000000040000000000004000000000000400000000811010000000000009000000000e10100000000000000000000000004000000000a1000000000000004000000000000200000000c81020000000084100
  | 8, 2 => 0x80101000000000210300000000000000000000000006000000000000400000000000000000000000002000000000210000000000000070000000000002000000000000500000000c1100000000000e102000000000a1000000000000000000000000000400000000000150000000000000000000008110200000000000120000000000009000000010410000000000000000000000000001000000000000d0000000002101000000000610000000000000020000000000005000000000000000000000811010000000000004
  | 8, 3 => 0x10410000000000c0103000000000a1010000000000008000000010010000000000000050000000101101000000000610300000000000000000000000004000000000000100000000061000000000000000000000000210200000000000030000000081101000000000000500000000000000000000000002000000004110100000000000020000000000001000000000000500000000c1101000000000000400000000c5100000000000000100000000801010000000000003000000000a10100000000021010000000000002
  | 8, 4 => 0x8010000000000411010000000000000000000000000100000000000090000000000003000000000000d00000000c91000000000000002000000000e100000000001210000000000c8102000000000000400000000000030000000000003000000000000300000001001020000000002101000000000a10200000001051020000000109101000000000001100000000000000000000000005000000010c1020000000000004000000010810000000000000050000000000004000000000000100000001081020000000000000
  | 8, 5 => 0x851020000000000001000000000000200000000c910000000000841000000000081100000000000000500000000121020000000012100000000000000500000000000080000000000005000000000a102000000000e100000000000000d000000000000500000000c810200000000000110000000000007000000000610000000000c010100000000000020000000000001000000000000400000000000000000000000001000000000000700000000000030000000000001000000000a10100000000c11020000000000003
  | 8, 6 => 0xe102000000000000900000000021020000000000001000000000000200000000c910200000000c8101000000000000000000000000020000000000002000000000000000000000000000000000000000000000000000400000000000080000000000000000000000000500000000000040000000000005000000000000000000000000000000000000001000000004110000000000061020000000000001000000000000400000000c110200000000000040000000000001000000000000200000000000140000000041101
  | 8, 7 => 0x41101000000008510000000000000050000000000004000000000000000000000c110100000000000010000000085102000000004110000000000c5102000000000000400000000061020000000000001000000000e10000000000121010000000000009000000000000400000000000010000000000011000000000a1000000000000012000000000a10100000000000010000000000005000000000a102000000000210000000000000090000000002101000000004110200000000000010000000000003
  | 8, 8 => 0x1000000000000400000000000000000000000002000000000000100000000021020000000002100000000000000200000001041000000000000004000000000000500000000411020000000000008000000000e10100000000021020000000000011000000000210000000000c9102000000000000200000000000000000000108102000000000000400000001001000000000000003000000000e1010000000000000000000000000000000000000000000000002100000000000210200000000061000000000000000
  | 8, 9 => 0x600000000021000000000002101000000008510000000000c910100000000000140000000000002000000000000000000000000080000000000004000000000000100000000c510000000000000020000000100102000000000000100000000000010000000000001000000000e102000000000000700000000000050000000006100000000000a102000000010510200000000c11010000000006101000000010d1010000000012101000000008510000000000000000000000000001000000000000600000000c5102
  | 8, 10 => 0xa102000000000000900000000000000000000012101000000000000d00000000000000000000000005000000000a101000000000610100000000000000000000000005000000000000500000000000040000000006103000000000000000000000c510100000000000040000000080102000000000610000000000000050000000000008000000001210100000000121020000000000004000000000a101000000000000400000000c91010000000000000000000000000800000000411010000000000000
  | 8, 11 => 0xc510000000000c910100000000000000000000000001000000000000200000000c01020000000041100000000000000000000000851010000000000012000000008510100000000c11000000000000000000000000000100000000000010000000081102000000000000500000000000030000000006101000000000a101000000000000400000000000020000000080102000000000001200000000000040000000000003000000010d10100000000401000000000000001000000000210100000000c91010000000000002
  | 8, 12 => 0x1001020000000000000000000000210200000000c9102000000000a1020000000105102000000000000100000000000020000000040100000000008010100000000000050000000002100000000000000000000000c5101000000000210100000000c9101000000010c102000000000000500000000021030000000085103000000000210000000000061020000000000011000000008510000000000c0102000000000210200000000000040000000000002000000000000400000000000010000000002101
  | 8, 13 => 0x80000000104100000000008410000000000000030000000000008000000000e10000000000c5101000000000000400000000000030000000000004000000000000100000000000050000000100102000000000000300000000841000000000109101000000000210100000000c9101000000000000500000000c5102000000000a1020000000000000000000010010000000000c110000000001011010000000000006000000000610000000000000010000000000003000000000000000000000061010000000000000
  | 8, 14 => 0xc11000000000000002000000000000500000000c810100000000c110000000001091010000000080102000000000000000000000000080000000000002000000000000000000000000020000000000000000000000000400000000000110000000080101000000010110100000000c11020000000081100000000000000500000000401030000000041102000000004010000000000000020000000006100000000008010100000000000020000000080100000000000e102000000000000500000000c81020000000081100
  | 8, 15 => 0x200000001011010000000000009000000000000200000000000020000000000001000000000000000000000021000000000000000000000000000400000000000030000000000001000000000000000000000000020000000000001000000000000200000000801010000000104100000000010110100000000000020000000012100000000000000700000000000110000000000001000000000000400000000021000000000101101000000000000d0000000000000000000008510000000000000050000000000001
  | 8, 16 => 0x300000000c1100000000000000100000000000030000000012101000000000e1000000000000005000000000000100000000000110000000000004000000000000800000000c810200000000401000000000000004000000000000100000000c8101000000008410300000000000030000000084100000000000000900000000000050000000000006000000000e10100000000c8101000000001210000000000c8101000000000000100000000000010000000000002000000000000000000000000020000000000002
  | 8, 17 => 0xc91020000000100100000000000210000000000851000000000006100000000000000000000000000040000000100100000000000000100000000c41030000000002102000000010410000000000c91020000000002102000000000001200000000000010000000000007000000000000d000000000000100000000000030000000002100000000000210200000000000010000000000005000000000610200000000000010000000000004000000000000800000000c9100000000000210100000000c81010000000000001
  | 8, 18 => 0x1210000000000000040000000084100000000000210100000000000010000000000004000000000000000000000000010000000000001000000000000100000000c5102000000000a1020000000108102
  | 9, 0 => 0x20000000000000000000000000100000000000020000000000001000000000000300000000000000000000000001000000000000100000000000000000000000001000000000000200000000000000000000000002
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 13 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_61 roots_61 8 s ws hint
  | 1 => checkCutEntry dom_31_32 roots_31_32 8 s ws hint
  | 2 => checkCutEntry dom_47 roots_47 8 s ws hint
  | 3 => checkCutEntry dom_45 roots_45 7 s ws hint
  | 4 => checkCutEntry dom_55_8 roots_55_8 7 s ws hint
  | 5 => checkCutEntry dom_59_4 roots_59_4 7 s ws hint
  | 6 => checkCutEntry dom_55 roots_55 6 s ws hint
  | 7 => checkCutEntry dom_59 roots_59 6 s ws hint
  | 8 => checkCutEntry dom_62_1 roots_62_1 6 s ws hint
  | 9 => checkCutEntry dom_62 roots_62 6 s ws hint
  | 10 => checkCutEntry dom_31 roots_31 6 s ws hint
  | 11 => checkCutEntry dom_23_32 roots_23_32 5 s ws hint
  | 12 => checkCutEntry dom_27_32 roots_27_32 5 s ws hint
  | 13 => checkCutEntry dom_51 roots_51 5 s ws hint
  | 14 => checkCutEntry dom_29_32 roots_29_32 5 s ws hint
  | 15 => checkCutEntry dom_53_8 roots_53_8 5 s ws hint
  | 16 => checkCutEntry dom_46_1 roots_46_1 5 s ws hint
  | 17 => checkCutEntry dom_54_8 roots_54_8 5 s ws hint
  | 18 => checkCutEntry dom_58_4 roots_58_4 5 s ws hint
  | 19 => checkCutEntry dom_60_1 roots_60_1 5 s ws hint
  | 20 => checkCutEntry dom_15 roots_15 5 s ws hint
  | 21 => checkCutEntry dom_23_8 roots_23_8 5 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_61 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31_32 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_45 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_55_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_59_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_55 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_59 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_62_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_62 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23_32 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_27_32 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_51 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_29_32 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_53_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_46_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_54_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_58_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_60_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23_8 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_63 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
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
private theorem z5_0 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := z5_0
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
private theorem z6_96 : ∀ i, 96 ≤ i → i < 108 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 96 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 108 → Z 6 i = true := (range_split (range_split (range_split z6_0 z6_16) (range_split z6_32 z6_48)) (range_split (range_split z6_64 z6_80) z6_96))
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
private theorem z7_256 : ∀ i, 256 ≤ i → i < 272 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 256 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_272 : ∀ i, 272 ≤ i → i < 288 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 272 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_288 : ∀ i, 288 ≤ i → i < 304 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 288 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_304 : ∀ i, 304 ≤ i → i < 320 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 304 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_320 : ∀ i, 320 ≤ i → i < 326 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 320 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 326 → Z 7 i = true := (range_split (range_split (range_split (range_split (range_split z7_0 z7_16) (range_split z7_32 z7_48)) (range_split (range_split z7_64 z7_80) (range_split z7_96 z7_112))) (range_split (range_split (range_split z7_128 z7_144) (range_split z7_160 z7_176)) (range_split (range_split z7_192 z7_208) (range_split z7_224 z7_240)))) (range_split (range_split (range_split z7_256 z7_272) (range_split z7_288 z7_304)) z7_320))
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
private theorem z8_128 : ∀ i, 128 ≤ i → i < 144 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_144 : ∀ i, 144 ≤ i → i < 160 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_160 : ∀ i, 160 ≤ i → i < 171 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 11 160 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 171 → Z 8 i = true := (range_split (range_split (range_split (range_split z8_0 z8_16) (range_split z8_32 z8_48)) (range_split (range_split z8_64 z8_80) (range_split z8_96 z8_112))) (range_split (range_split z8_128 z8_144) z8_160))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_0 : ∀ i, 0 ≤ i → i < 16 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_16 : ∀ i, 16 ≤ i → i < 19 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 3 16 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 19 → Z 9 i = true := (range_split z9_0 z9_16)
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

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 13]⟩], 16⟩

theorem wit_mono : PEqualNP.MetaComplexity.Monotone2 wit := by
  simp [wit, PEqualNP.MetaComplexity.Monotone2]

theorem wit_sz : wit.size ≤ 11 := by decide

set_option maxRecDepth 40000 in
theorem wit_ev : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = Nat.testBit (4277074600 * 2 ^ 32 + 4241287304) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel

set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_63.testBit r.val = (fun x : Fin 6 → Bool => Nat.testBit (4277074600 * 2 ^ 32 + 4241287304) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) (pt6 r.val) := by decide +kernel

theorem lower : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074600 * 2 ^ 32 + 4241287304) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) t → 11 ≤ t :=
  lower_to_circuit6 (fun x : Fin 6 → Bool => Nat.testBit (4277074600 * 2 ^ 32 + 4241287304) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) goal_63 11 hT6 (by unfold IsConst; decide) low_63

end PEqualNP.Outside.L_meta_46042_aux

theorem PEqualNP.Outside.L_meta_46042 :
  ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074600 * 2 ^ 32 + 4241287304) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074600 * 2 ^ 32 + 4241287304) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  exact ⟨PEqualNP.Outside.L_meta_46042_aux.wit, PEqualNP.Outside.L_meta_46042_aux.wit_mono, le_trans PEqualNP.Outside.L_meta_46042_aux.wit_sz (PEqualNP.Outside.L_meta_46042_aux.lower s hs), PEqualNP.Outside.L_meta_46042_aux.wit_ev⟩
