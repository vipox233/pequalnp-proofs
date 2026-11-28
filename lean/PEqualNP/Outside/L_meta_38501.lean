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

namespace PEqualNP.Outside.L_meta_38501_aux

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

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xeae8eae8e8a8e8a8eae8eae8e8a8e8a8eae8eae8e8a8e8a8eae8eae8e8a8e8a8
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xeeaaaa88ee888888eeaaaa88ee888888eeaaaa88ee888888eeaaaa88ee888888
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_31_32 : Nat := 0xffffffff00000000
def goal_31_32 : Nat := 0xeeeaeae8eeeaeae8eeeaeae8eeeaeae8eeeaeae8eeeaeae8eeeaeae8eeeaeae8
def roots_31_32 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xeaeae8e8a8a8a8a8eaeae8e8a8a8a8a8eaeae8e8a8a8a8a8eaeae8e8a8a8a8a8
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_31 : Nat := 0xffffffff
def goal_31 : Nat := 0xeea8e8a8eea8e8a8eea8e8a8eea8e8a8eea8e8a8eea8e8a8eea8e8a8eea8e8a8
def roots_31 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_39_16 : Nat := 0xff000000ff0000
def goal_39_16 : Nat := 0xeaeaeaeaa8a8a8a8eaeaeaeaa8a8a8a8eaeaeaeaa8a8a8a8eaeaeaeaa8a8a8a8
def roots_39_16 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xaaaaaaa0aaa0a0a0aaaaaaa0aaa0a0a0aaaaaaa0aaa0a0a0aaaaaaa0aaa0a0a0
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_55_8 : Nat := 0xff00ff00ff00ff00
def goal_55_8 : Nat := 0xeeeeeaeaeeeee8e8eeeeeaeaeeeee8e8eeeeeaeaeeeee8e8eeeeeaeaeeeee8e8
def roots_55_8 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_62_1 : Nat := 0xaaaaaaaaaaaaaaaa
def goal_62_1 : Nat := 0xfffffffcfffcfcfcfffffffcfffcfcfcfffffffcfffcfcfcfffffffcfffcfcfc
def roots_62_1 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_15 : Nat := 0xffff
def goal_15 : Nat := 0xe8a8e8a8e8a8e8a8e8a8e8a8e8a8e8a8e8a8e8a8e8a8e8a8e8a8e8a8e8a8e8a8
def roots_15 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0]

def dom_15_16 : Nat := 0xffff0000
def goal_15_16 : Nat := 0xeea8eea8eea8eea8eea8eea8eea8eea8eea8eea8eea8eea8eea8eea8eea8eea8
def roots_15_16 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0]

def dom_57 : Nat := 0x303030303030303
def goal_57 : Nat := 0xaaaaaa00aa000000aaaaaa00aa000000aaaaaa00aa000000aaaaaa00aa000000
def roots_57 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_58_1 : Nat := 0xa0a0a0a0a0a0a0a
def goal_58_1 : Nat := 0xffffffccffccccccffffffccffccccccffffffccffccccccffffffccffcccccc
def roots_58_1 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_23_8 : Nat := 0xff00ff00
def goal_23_8 : Nat := 0xeeeee8e8eeeee8e8eeeee8e8eeeee8e8eeeee8e8eeeee8e8eeeee8e8eeeee8e8
def roots_23_8 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0]

def dom_27 : Nat := 0xf0f0f0f
def goal_27 : Nat := 0xee888888ee888888ee888888ee888888ee888888ee888888ee888888ee888888
def roots_27 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_47_16 : Nat := 0xffff0000ffff0000
def goal_47_16 : Nat := 0xeeeaeeeaeea8eea8eeeaeeeaeea8eea8eeeaeeeaeea8eea8eeeaeeeaeea8eea8
def roots_47_16 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_23_32 : Nat := 0xff00ff00000000
def goal_23_32 : Nat := 0xeaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8
def roots_23_32 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0]

def dom_39 : Nat := 0xff000000ff
def goal_39 : Nat := 0xe8e8e8e8a8a8a8a8e8e8e8e8a8a8a8a8e8e8e8e8a8a8a8a8e8e8e8e8a8a8a8a8
def roots_39 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0]

def dom_39_8 : Nat := 0xff000000ff00
def goal_39_8 : Nat := 0xeaeaeaeae8e8e8e8eaeaeaeae8e8e8e8eaeaeaeae8e8e8e8eaeaeaeae8e8e8e8
def roots_39_8 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0]

def dom_51_8 : Nat := 0xf000f000f000f00
def goal_51_8 : Nat := 0xeeeeaaaaeeee8888eeeeaaaaeeee8888eeeeaaaaeeee8888eeeeaaaaeeee8888
def roots_51_8 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_60_1 : Nat := 0x2222222222222222
def goal_60_1 : Nat := 0xfffffff0fff0f0f0fffffff0fff0f0f0fffffff0fff0f0f0fffffff0fff0f0f0
def roots_60_1 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xeeeaeae8eea8e8a8eeeaeae8eea8e8a8eeeaeae8eea8e8a8eeeaeae8eea8e8a8
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

namespace S_47
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (2, 3), (4, 5), (6, 7), (6, 14), (6, 38), (9, 11), (9, 13), (9, 41), (10, 11), (10, 14), (12, 13), (12, 14), (33, 35), (33, 37), (33, 41), (34, 35), (34, 38), (36, 37), (36, 38), (40, 41), (42, 43), (42, 46), (44, 45), (44, 46)]
def r1sG : List Nat := [1, 1, 2, 4, 6, 6, 6, 9, 9, 9, 10, 10, 12, 12, 33, 33, 33, 34, 34, 36, 36, 40, 42, 42, 44, 44]
def r2sG : List Nat := [3, 5, 3, 5, 7, 14, 38, 11, 13, 41, 11, 14, 13, 14, 35, 37, 41, 35, 38, 37, 38, 41, 43, 46, 45, 46]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [2203520468227, 6601533424389, 4403048812037, 6601566979331, 2204059110915, 10999613490435, 37388296783107, 44122300613417, 6602072067589, 46321323868969, 44122300613929, 37525735736579, 13237106311950, 9904396829955, 9921930789646, 8822419170830, 36322641579561, 13237643182862]
def xsM : List Nat := roots_47.map (· &&& dom_47)
def goalM : Nat := goal_47 &&& dom_47
def NN : Nat → Nat
  | 4 => 1
  | 5 => 20
  | 6 => 17
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xf1fce07
  | 5, 0 => 0xd508e921c99008f2a7e1de7ea1c0b4b888e2183d71f40ace5ba073fa5b61388b4fada6a444dbae4a42829c103b21efc1286448961b2929df1412d30a13645f700f1fce070afba44c03b0c7d70335d817
  | 6, 0 => 0xf11b066ea1c0b4b8a12a17a39f39fa5295fc1c0b8c5e12726b7180a36594bfe25ba073fa5b61388b55c13d204d7877b92fef2b28270b03de160058940f1fce070da784ce
  | 7, 0 => 0xf1fce07
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xaaaa000000000000000000000000000000000000000000000000000000000000aa000000aa0000000000000000000000000000000000000000000000000000008888000088880000000000000000000000000000000000000000000000000000555500005555000000000000000000000000000000000000000000000000000033330000333300000000000000000000000000000000000000000000000000000f0f00000f0f000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000000000ffff
  | 0, 1 => 0xf0f00000f0f00000000000000000000000000000000000000000000000000000f0000000f0000000000000000000000000000000000000000000000000000000eeee0000eeee0000000000000000000000000000000000000000000000000000cccc0000cccc0000000000000000000000000000000000000000000000000000cccc000000000000000000000000000000000000000000000000000000000000c8c80000c8c80000000000000000000000000000000000000000000000000000c0c00000c0c00000000000000000000000000000000000000000000000000000aaaa0000aaaa
  | 0, 2 => 0xfff00000fff00000000000000000000000000000000000000000000000000000ffcc000000000000000000000000000000000000000000000000000000000000ffaa0000ffaa0000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000fcfc0000fcfc0000000000000000000000000000000000000000000000000000fa000000fa000000000000000000000000000000000000000000000000000000f8f80000f8f8
  | 0, 3 => 0xffff0000ff000000000000000000000000000000000000000000000000000000ffff0000f0f00000000000000000000000000000000000000000000000000000ffff0000f0000000000000000000000000000000000000000000000000000000ffff0000aaaa0000000000000000000000000000000000000000000000000000ffff000088880000000000000000000000000000000000000000000000000000ffff00000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x18a3d885
  | 5, 0, 0 => 0x7b10102e28f6957146204b8a3d845c5dcc42da8f62170f6102b8a3d485cd1ec42d1e81817747b10b88bd885c51ec42e2af6197b37b10b8a41885
  | 5, 0, 1 => 0xc510312e2924a17146104b47b1005
  | 6, 0, 0 => 0x51ec4017147b5886c51ec415b1493d886c51ec41db147b1286c51ec5a1818a310250628f6117147b1036c51ec411b98a3d886d628f621b149bd8860628f6217147b1016
  | 6, 0, 1 => 0x3b8a3d886
  | 7, 0, 0 => 0x18a3d885
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
  | 0, 0 => 0x1c000000000000000000000000000000000000000000000000000000000000000038000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003fe3c7c000000000000000000000000000000000000000000000000000000000339f38b0000000000000000000000000000000000000000000000000000000000e7cf8700000000000000000000000000000000000000000000000000000000001fc07f0000000000000000000000000000000000000000000000000000000000003fff
  | 0, 1 => 0x318307800000000000000000000000000000000000000000000000000000000030030000000000000000000000000000000000000000000000000000000000000c7cff70000000000000000000000000000000000000000000000000000000000c60c740000000000000000000000000000000000000000000000000000000000c6000000000000000000000000000000000000000000000000000000000000000000700000000000000000000000000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000000000000001c383
  | 0, 2 => 0x3f83ff80000000000000000000000000000000000000000000000000000000003e600000000000000000000000000000000000000000000000000000000000003e1ff830000000000000000000000000000000000000000000000000000000003e03f800000000000000000000000000000000000000000000000000000000003e000000000000000000000000000000000000000000000000000000000000003de3c7c00000000000000000000000000000000000000000000000000000000030033800000000000000000000000000000000000000000000000000000000003183078
  | 0, 3 => 0x3ffff800000000000000000000000000000000000000000000000000000000003fff0780000000000000000000000000000000000000000000000000000000003fff0000000000000000000000000000000000000000000000000000000000003ffc3830000000000000000000000000000000000000000000000000000000003ffc0000000000000000000000000000000000000000000000000000000000003ffc000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x16bc200000000000000000000000000000000000000000000000000000000000161178000000000000000000000000000000000000000000000000000000000004244950000000000000000000000000000000000000000000000000000000002942860000000000000000000000000000000000000000000000000000000000129930a000000000000000000000000000000000000000000000000000000000063468500000000000000000000000000000000000000000000000000000000001ec05f0000000000000000000000000000000000000000000000000000000000003dbf
  | 0, 1 => 0x39cb97a00000000000000000000000000000000000000000000000000000000038039200000000000000000000000000000000000000000000000000000000003ffffff0000000000000000000000000000000000000000000000000000000002d66cf50000000000000000000000000000000000000000000000000000000002d640400000000000000000000000000000000000000000000000000000000002d66cf5000000000000000000000000000000000000000000000000000000000294287000000000000000000000000000000000000000000000000000000000016bd79f
  | 0, 2 => 0x3fdbffa0000000000000000000000000000000000000000000000000000000003f742400000000000000000000000000000000000000000000000000000000003ebffbf0000000000000000000000000000000000000000000000000000000003e13fa00000000000000000000000000000000000000000000000000000000003e102000000000000000000000000000000000000000000000000000000000003defdff0000000000000000000000000000000000000000000000000000000003e13fa00000000000000000000000000000000000000000000000000000000003defdff
  | 0, 3 => 0x3ffffe00000000000000000000000000000000000000000000000000000000003fffb7a0000000000000000000000000000000000000000000000000000000003fffb600000000000000000000000000000000000000000000000000000000003ffd7df0000000000000000000000000000000000000000000000000000000003ffc6d50000000000000000000000000000000000000000000000000000000003ffc240
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 30 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 30 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 30 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 30 then wireAt i else 0
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 6 0 (NN s)
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

def symsG : List (List (Nat × Nat)) := [[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]]
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
private theorem z4_0 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_16 : ∀ i, 16 ≤ i → i < 20 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 4 16 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 20 → Z 5 i = true := (range_split z5_0 z5_16)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 16 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_16 : ∀ i, 16 ≤ i → i < 17 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 16 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 17 → Z 6 i = true := (range_split z6_0 z6_16)
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

namespace S_59
def pairsG : List (Nat × Nat) := [(1, 3), (2, 3), (9, 11), (9, 25), (9, 41), (10, 11), (10, 26), (17, 19), (17, 25), (17, 49), (18, 19), (18, 26), (24, 25), (24, 26), (33, 35), (33, 41), (33, 49), (34, 35), (40, 41), (42, 43), (42, 58), (48, 49), (50, 51), (50, 58), (56, 57), (56, 58)]
def r1sG : List Nat := [1, 2, 9, 9, 9, 10, 10, 17, 17, 17, 18, 18, 24, 24, 33, 33, 33, 34, 40, 42, 42, 48, 50, 50, 56, 56]
def r2sG : List Nat := [3, 3, 11, 25, 41, 11, 26, 19, 25, 49, 19, 26, 25, 26, 35, 41, 49, 35, 41, 43, 58, 49, 51, 58, 57, 58]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [2203722586371, 36293414885635, 18730909247769, 2204260964867, 2204260440579, 9904598948099, 18700691970307, 36357051849009, 36322826852649, 26392609293081, 26427103249177, 26397021635354, 26431381373722, 26466144813850, 19834715842842]
def xsM : List Nat := roots_59.map (· &&& dom_59)
def goalM : Nat := goal_59 &&& dom_59
def NN : Nat → Nat
  | 4 => 3
  | 5 => 48
  | 6 => 25
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xdd072281c38274818a0ae901
  | 5, 0 => 0xf3a9eb6beaaab64ae2ecea00d5a03194d4bec136d3d4756ace5b8369c3827481c1228dd0c00b58cdba0f5bffb9879e31a2b15d519f8692589a28898097d3497293b906c5925f5c689049529985f28ed373d4772669369245690ffc92622bdb265f210ebd5d8269015cfe36465b2b69ba4cac355d4b95005a484acddd37f8ccf43108c30d2dceab6126f145cd26bc2b5e243e20471f667e7f1ba5db2b1b891d441a71e841165cd17c0f49a64c0f1ba55d0b59138309710d2b06d5b4db061f7558
  | 6, 0 => 0xfdfe6beeeaaab64ad3d4756ac6eafbb0c3827481a4e07297a17346f292fd4275925f5c6887084d0275bef6de72783b7e6e9b733a6c35459f6b87e637652e56205a3c9a365878c3dd4cac355d4b95005a418db97037f8ccf42a5942f414d4acce006bb7a1
  | 7, 0 => 0xc3827481
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x50505050505050500000000000000000000000000000000000000000000000003030303030303030000000000000000000000000000000000000000000000000303030300000000000000000000000000000000000000000000000000000000000f000f000f000f00000000000000000000000000000000000000000000000000000f0f00000f0f000000000000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000a0a0a0a0000000000000000000000000000000000000000000000000000000003030303
  | 0, 1 => 0xc080c080c080c080000000000000000000000000000000000000000000000000c000c000c000c000000000000000000000000000000000000000000000000000a0a0a0a0a0a0a0a0000000000000000000000000000000000000000000000000a0a0a0a080808080000000000000000000000000000000000000000000000000a0a0a0a000000000000000000000000000000000000000000000000000000000a0a00000a0a00000000000000000000000000000000000000000000000000000808080808080808000000000000000000000000000000000000000000000000050505050f0f0f0f
  | 0, 2 => 0xe0e0e0e0e0e0e0e0000000000000000000000000000000000000000000000000e0e0e0e0c0c0c0c0000000000000000000000000000000000000000000000000e0e0e0e000000000000000000000000000000000000000000000000000000000e000e000e000e000000000000000000000000000000000000000000000000000c0c0c0c0f0f0f0f0000000000000000000000000000000000000000000000000c0c0c0c0c0c0c0c0000000000000000000000000000000000000000000000000c0c0c0c000000000000000000000000000000000000000000000000000000000c0c00000c0c0000
  | 0, 3 => 0xf0f0a0a000000000000000000000000000000000000000000000000000000000f0f08080f0f08080000000000000000000000000000000000000000000000000f0f00000f0f00000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000f0a00000f0a00000000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000f000f000f0000000000000000000000000000000000000000000000000000000f0000000f000000
  | 0, 4 => 0xf0f0f0f0a0a0a0a0000000000000000000000000000000000000000000000000f0f0f0f080808080000000000000000000000000000000000000000000000000f0f0f0f050505050000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000f0f0f000f0f0f000000000000000000000000000000000000000000000000000f0f0f00000000000000000000000000000000000000000000000000000000000f0f0c0c0f0f0c0c0000000000000000000000000000000000000000000000000f0f0a0a0f0f0a0a
  | 0, 5 => 0xf0f0f0f0f0f00000000000000000000000000000000000000000000000000000f0f0f0f0f000f000000000000000000000000000000000000000000000000000f0f0f0f0f0000000000000000000000000000000000000000000000000000000f0f0f0f0c0c0c0c0000000000000000000000000000000000000000000000000f0f0f0f0c000c00
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x89848d491d692354071948d4
  | 5, 0, 0 => 0x75a346155d692348592069229648d848d591d65235646da48d575a552356475a1c65a5d68d196575a48d591e692355d69234c57dd692356485a40d591a3460d6c71a48d5
  | 5, 0, 1 => 0x91d697256475a346575a592356875a48d575a487096475448d575a48d055d6923455692343096475a3cd575a48b1d6275a48d591d6921d6975a48d569234b0d646923435
  | 5, 0, 2 => 0xa5d691355d692342575a4d2355d6923405a5d6921d5d69234b5a9d692356475a48d591a4870d6969234359123440d5d68d182575a34b196575a487599d692356775a48b5
  | 6, 0, 0 => 0x91d71a48d6a6475a48d692175a48d691d692349691d69244d691d69234369e475a48d692075a48d691d69238d602475a487502975a48d5ae475a48d6024692343591d692347691d692342691d69848d6
  | 6, 0, 1 => 0x91d69234b601d692342501d69234b591d69748d602475a48d592375a48d691d69234a691d692346602475a3465
  | 7, 0, 0 => 0x2475a48d5
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
  | 0, 0 => 0x3fe3c62000000000000000000000000000000000000000000000000000000000325f39d000000000000000000000000000000000000000000000000000000000325c0000000000000000000000000000000000000000000000000000000000000e3cf8300000000000000000000000000000000000000000000000000000000001fc07f0000000000000000000000000000000000000000000000000000000000003fff000000000000000000000000000000000000000000000000000000000000039d000000000000000000000000000000000000000000000000000000000000339d
  | 0, 1 => 0x1800600000000000000000000000000000000000000000000000000000000000180060000000000000000000000000000000000000000000000000000000000001c39d000000000000000000000000000000000000000000000000000000000001c000000000000000000000000000000000000000000000000000000000000001c000000000000000000000000000000000000000000000000000000000000000038000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003fe3fff
  | 0, 2 => 0xdbcfff0000000000000000000000000000000000000000000000000000000000dbcc620000000000000000000000000000000000000000000000000000000000dbc000000000000000000000000000000000000000000000000000000000000018007c0000000000000000000000000000000000000000000000000000000000da3fff0000000000000000000000000000000000000000000000000000000000da0c620000000000000000000000000000000000000000000000000000000000da00000000000000000000000000000000000000000000000000000000000000c00c00
  | 0, 3 => 0x3e1c0000000000000000000000000000000000000000000000000000000000003e03f800000000000000000000000000000000000000000000000000000000003e03f800000000000000000000000000000000000000000000000000000000003e00000000000000000000000000000000000000000000000000000000000000300338000000000000000000000000000000000000000000000000000000000031c307c00000000000000000000000000000000000000000000000000000000031c30000000000000000000000000000000000000000000000000000000000003003000
  | 0, 4 => 0x3ffc39d0000000000000000000000000000000000000000000000000000000003ffc0000000000000000000000000000000000000000000000000000000000003fffc620000000000000000000000000000000000000000000000000000000003ffc0000000000000000000000000000000000000000000000000000000000003fc3ffc0000000000000000000000000000000000000000000000000000000003fc00000000000000000000000000000000000000000000000000000000000003fa3fe20000000000000000000000000000000000000000000000000000000003e1ff9d
  | 0, 5 => 0x3ffff800000000000000000000000000000000000000000000000000000000003fff07c0000000000000000000000000000000000000000000000000000000003fff0000000000000000000000000000000000000000000000000000000000003ffcc620000000000000000000000000000000000000000000000000000000003ffc060
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x290284000000000000000000000000000000000000000000000000000000000012593180000000000000000000000000000000000000000000000000000000001258210000000000000000000000000000000000000000000000000000000000063468300000000000000000000000000000000000000000000000000000000000ec0370000000000000000000000000000000000000000000000000000000000003def00000000000000000000000000000000000000000000000000000000000015af0000000000000000000000000000000000000000000000000000000000001108
  | 0, 1 => 0x2da6ce7000000000000000000000000000000000000000000000000000000000298286400000000000000000000000000000000000000000000000000000000016fd7bf00000000000000000000000000000000000000000000000000000000016fc6b700000000000000000000000000000000000000000000000000000000016fc210000000000000000000000000000000000000000000000000000000000161178800000000000000000000000000000000000000000000000000000000004a44a70000000000000000000000000000000000000000000000000000000002903def
  | 0, 2 => 0x3ffffff0000000000000000000000000000000000000000000000000000000003ffeef70000000000000000000000000000000000000000000000000000000003ffc21000000000000000000000000000000000000000000000000000000000039cb97c0000000000000000000000000000000000000000000000000000000002da7def0000000000000000000000000000000000000000000000000000000002da6ce70000000000000000000000000000000000000000000000000000000002da40000000000000000000000000000000000000000000000000000000000002d02cc0
  | 0, 3 => 0x3ffc2100000000000000000000000000000000000000000000000000000000003fb7fef0000000000000000000000000000000000000000000000000000000003f13fc80000000000000000000000000000000000000000000000000000000003f102000000000000000000000000000000000000000000000000000000000003f13fc800000000000000000000000000000000000000000000000000000000039cb97c00000000000000000000000000000000000000000000000000000000039cb9580000000000000000000000000000000000000000000000000000000003903948
  | 0, 4 => 0x3ffd7bf0000000000000000000000000000000000000000000000000000000003ffc6b70000000000000000000000000000000000000000000000000000000003ffea500000000000000000000000000000000000000000000000000000000003ffc2100000000000000000000000000000000000000000000000000000000003fdbffc0000000000000000000000000000000000000000000000000000000003fd82100000000000000000000000000000000000000000000000000000000003fb7fef0000000000000000000000000000000000000000000000000000000003ffffff
  | 0, 5 => 0x3ffffd80000000000000000000000000000000000000000000000000000000003fffb7c0000000000000000000000000000000000000000000000000000000003fffb580000000000000000000000000000000000000000000000000000000003ffeef70000000000000000000000000000000000000000000000000000000003ffea74
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 45 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 45 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 45 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 45 then wireAt i else 0
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

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
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
private theorem z4_0 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_16 : ∀ i, 16 ≤ i → i < 32 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_32 : ∀ i, 32 ≤ i → i < 48 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 32 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 48 → Z 5 i = true := (range_split (range_split z5_0 z5_16) z5_32)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 16 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_16 : ∀ i, 16 ≤ i → i < 25 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 9 16 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 25 → Z 6 i = true := (range_split z6_0 z6_16)
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

namespace S_31_32
def pairsG : List (Nat × Nat) := [(33, 35), (33, 37), (33, 41), (33, 49), (34, 35), (34, 38), (36, 37), (36, 38), (40, 41), (42, 43), (42, 46), (42, 58), (44, 45), (44, 46), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (56, 57), (56, 58), (60, 61), (60, 62)]
def r1sG : List Nat := [33, 33, 33, 33, 34, 34, 36, 36, 40, 42, 42, 42, 44, 44, 48, 50, 50, 50, 52, 52, 56, 56, 60, 60]
def r2sG : List Nat := [35, 37, 41, 49, 35, 38, 37, 38, 41, 43, 46, 58, 45, 46, 49, 51, 54, 58, 53, 54, 57, 58, 61, 62]
def mpG : Nat := 0xffffff
def pool6G : List Nat := [37525735744803, 46322064958249, 39724859860517, 61787955864378, 46321962984739, 46351893472041, 46322064961833, 55118023762737, 61753596650298, 55156526885178, 39724725445413, 48520952685349, 55118324966947, 57317179925285, 39729003569958]
def xsM : List Nat := roots_31_32.map (· &&& dom_31_32)
def goalM : Nat := goal_31_32 &&& dom_31_32
def NN : Nat → Nat
  | 4 => 13
  | 5 => 47
  | 6 => 24
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xcb85f5a5b07954b5b0273326afd37c517b0c59c06e0a56136151fc205f5ce351584362093668ecf31933c25c01313b960009ff46
  | 5, 0 => 0xfb45fe20f329cbdceea07002dc1b0d52cd07a878cce3300ebac05386ba24852eb740b46eaecd9a48a3c71882964a89bc8de7e228837263dc77dc40c7764c6cf37523d75b643ce693636d008b608578e95f5ce3515eeace285afe27275843620952a1850f50ff384b4726db884684411f42d4580c3c2f10113a877c6036c13d3b33ff42532c8bb1972a92d0ea239e6b931d05c19c1ccdf1150eac844f0e094e0c0c9503e80c70127509f3bf12082f92a30706fd0b0467640c02a103ae
  | 6, 0 => 0xeea07002e584d83dccf2db85b740b46e8f1909028986d9d586cfb07d7d657ff377186efb7523d75b608578e95fcdfb9d5f5ce351531e2a99527e04584fbea8484995ef473c415933358964b82f5e14ef273b926c1dcf21030706fd0b059706fd
  | 7, 0 => 0x5f5ce351
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x33333333000000000000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000f000f000000000000000000000000000000000000000000000000000000000000ff00ff00000000000000000000000000000000000000000000000000000000000f000f000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000000000000000000000000000000000000f0f00000000
  | 0, 1 => 0xcccc000000000000000000000000000000000000000000000000000000000000cc00cc0000000000000000000000000000000000000000000000000000000000c0c0c0c000000000000000000000000000000000000000000000000000000000aaaaaaaa00000000000000000000000000000000000000000000000000000000aa00aa0000000000000000000000000000000000000000000000000000000000a0a0a0a00000000000000000000000000000000000000000000000000000000088888888000000000000000000000000000000000000000000000000000000005555555500000000
  | 0, 2 => 0xf000f00000000000000000000000000000000000000000000000000000000000eeeeeeee00000000000000000000000000000000000000000000000000000000eeeecccc00000000000000000000000000000000000000000000000000000000eeee000000000000000000000000000000000000000000000000000000000000ecececec00000000000000000000000000000000000000000000000000000000eaeaeaea00000000000000000000000000000000000000000000000000000000e0e0e0e000000000000000000000000000000000000000000000000000000000cccccccc00000000
  | 0, 3 => 0xff00000000000000000000000000000000000000000000000000000000000000fcfcfcfc00000000000000000000000000000000000000000000000000000000fafafafa00000000000000000000000000000000000000000000000000000000faf0faf000000000000000000000000000000000000000000000000000000000f8f8f8f800000000000000000000000000000000000000000000000000000000f0fff0ff00000000000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000f0f0000000000000
  | 0, 4 => 0xfff0fff000000000000000000000000000000000000000000000000000000000fff0faf000000000000000000000000000000000000000000000000000000000fff0f0f000000000000000000000000000000000000000000000000000000000ffc0ffc000000000000000000000000000000000000000000000000000000000ffaaffaa00000000000000000000000000000000000000000000000000000000ffaaff0000000000000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000ff00aa0000000000
  | 0, 5 => 0xffffff0000000000000000000000000000000000000000000000000000000000fffff0f000000000000000000000000000000000000000000000000000000000fffff00000000000000000000000000000000000000000000000000000000000ffffcccc00000000000000000000000000000000000000000000000000000000ffffc0c000000000000000000000000000000000000000000000000000000000ffffa0a000000000000000000000000000000000000000000000000000000000ffff888800000000000000000000000000000000000000000000000000000000ffff000000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0xa2179240289903100ba7307402f9503100a21753402e9d02100a216d64a216503140ba740c402e40c0900b6740c402e9103100ba14904
  | 5, 0, 0 => 0xba1750316ea2740c5a2165531689d034c5a193070d6985940c5a27650216881940c5a21710316889940c5b6165031688d940b59d940c05689d940c5a21408196b85940c5
  | 5, 0, 1 => 0x85940805688594085a21653316c8593cc585940c056885940c5a2764c1d6840c183502e9d0312869940c585940c01616503055a21307196840c1845a21450316885e34c5
  | 5, 0, 2 => 0x2f7d940c5ba765031688503065a2165625688592075650303056885b40c5a2585031688593075a21652416a85940c5a2740c196885d40a585951031689d740c5
  | 6, 0, 0 => 0xa2165030a602885940850216503015a2165840c602885940c5a2385940c6a2165640c6b2885940c6a216503086a216503016a216503096a216503076ba885940c6a2165034c60289d940c5a217d940c6
  | 6, 0, 1 => 0x288503065a2175940c6be885940c60288593075a2179940c6a216503066a2165030b6a2165038c6
  | 7, 0, 0 => 0x2885940c5
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
  | 0, 0 => 0xfc71cf000000000000000000000000000000000000000000000000000000000033cf3f000000000000000000000000000000000000000000000000000000000033c0000000000000000000000000000000000000000000000000000000000000300f0000000000000000000000000000000000000000000000000000000000000fc0ff000000000000000000000000000000000000000000000000000000000003c03f0000000000000000000000000000000000000000000000000000000000003fff0000000000000000000000000000000000000000000000000000000000000f3f
  | 0, 1 => 0x380000000000000000000000000000000000000000000000000000000000000000e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000fffff0
  | 0, 2 => 0xc030000000000000000000000000000000000000000000000000000000000000038e3f0000000000000000000000000000000000000000000000000000000000038e3000000000000000000000000000000000000000000000000000000000000380000000000000000000000000000000000000000000000000000000000000038e30000000000000000000000000000000000000000000000000000000000000000f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000038e30
  | 0, 3 => 0xf000000000000000000000000000000000000000000000000000000000000000cfbef00000000000000000000000000000000000000000000000000000000000cc30cf0000000000000000000000000000000000000000000000000000000000cc30c00000000000000000000000000000000000000000000000000000000000cc30c00000000000000000000000000000000000000000000000000000000000cff0ff0000000000000000000000000000000000000000000000000000000000cc30c00000000000000000000000000000000000000000000000000000000000cc0000
  | 0, 4 => 0xfc3fc00000000000000000000000000000000000000000000000000000000000fc30c00000000000000000000000000000000000000000000000000000000000fc30c00000000000000000000000000000000000000000000000000000000000f03f000000000000000000000000000000000000000000000000000000000000f03f0f0000000000000000000000000000000000000000000000000000000000f03f000000000000000000000000000000000000000000000000000000000000f03f000000000000000000000000000000000000000000000000000000000000f00000
  | 0, 5 => 0xffff000000000000000000000000000000000000000000000000000000000000fff0c00000000000000000000000000000000000000000000000000000000000fff0000000000000000000000000000000000000000000000000000000000000ffce300000000000000000000000000000000000000000000000000000000000ffc0000000000000000000000000000000000000000000000000000000000000ffc0000000000000000000000000000000000000000000000000000000000000ffc0000000000000000000000000000000000000000000000000000000000000ffc000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x54514e000000000000000000000000000000000000000000000000000000000032cb1d000000000000000000000000000000000000000000000000000000000032c8080000000000000000000000000000000000000000000000000000000000320b0400000000000000000000000000000000000000000000000000000000000dc0fb000000000000000000000000000000000000000000000000000000000000c01900000000000000000000000000000000000000000000000000000000000037f70000000000000000000000000000000000000000000000000000000000000315
  | 0, 1 => 0xab88000000000000000000000000000000000000000000000000000000000000a22e0000000000000000000000000000000000000000000000000000000000008924a0000000000000000000000000000000000000000000000000000000000054d35f0000000000000000000000000000000000000000000000000000000000501304000000000000000000000000000000000000000000000000000000000044104200000000000000000000000000000000000000000000000000000000000082110000000000000000000000000000000000000000000000000000000000ab2ca0
  | 0, 2 => 0xc034000000000000000000000000000000000000000000000000000000000000ffffff0000000000000000000000000000000000000000000000000000000000ffeeb90000000000000000000000000000000000000000000000000000000000ffc8080000000000000000000000000000000000000000000000000000000000efbef30000000000000000000000000000000000000000000000000000000000ddf7ff0000000000000000000000000000000000000000000000000000000000cd34e20000000000000000000000000000000000000000000000000000000000abaeb1
  | 0, 3 => 0xf208000000000000000000000000000000000000000000000000000000000000efbef30000000000000000000000000000000000000000000000000000000000ddf7ff0000000000000000000000000000000000000000000000000000000000dd37e60000000000000000000000000000000000000000000000000000000000cdb6f30000000000000000000000000000000000000000000000000000000000cdf4fb0000000000000000000000000000000000000000000000000000000000cd34e20000000000000000000000000000000000000000000000000000000000cd0000
  | 0, 4 => 0xff3fe60000000000000000000000000000000000000000000000000000000000ff3fe60000000000000000000000000000000000000000000000000000000000ff3ce20000000000000000000000000000000000000000000000000000000000fb3fa40000000000000000000000000000000000000000000000000000000000f6ff5f0000000000000000000000000000000000000000000000000000000000f6ff0c0000000000000000000000000000000000000000000000000000000000f23f040000000000000000000000000000000000000000000000000000000000f21b04
  | 0, 5 => 0xffff0c0000000000000000000000000000000000000000000000000000000000fffcea0000000000000000000000000000000000000000000000000000000000fffc080000000000000000000000000000000000000000000000000000000000ffeeb90000000000000000000000000000000000000000000000000000000000ffeca80000000000000000000000000000000000000000000000000000000000ffd84a0000000000000000000000000000000000000000000000000000000000ffca190000000000000000000000000000000000000000000000000000000000ffc808
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 48 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 48 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 48 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 48 then wireAt i else 0
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_31_32 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_31_32 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
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

namespace S_55
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (2, 3), (4, 5), (6, 7), (6, 38), (17, 19), (17, 21), (17, 49), (18, 19), (20, 21), (22, 23), (22, 54), (33, 35), (33, 37), (33, 49), (34, 35), (34, 38), (36, 37), (36, 38), (48, 49), (50, 51), (50, 54), (52, 53), (52, 54)]
def r1sG : List Nat := [1, 1, 2, 4, 6, 6, 17, 17, 17, 18, 20, 22, 22, 33, 33, 33, 34, 34, 36, 36, 48, 50, 50, 52, 52]
def r2sG : List Nat := [3, 5, 3, 5, 7, 38, 19, 21, 49, 19, 21, 23, 54, 35, 37, 49, 35, 38, 37, 38, 49, 51, 54, 53, 54]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := [2203924694275, 18701162513667, 6601937650437, 4403183560197, 6601971205379, 2204193859075, 19796379174147, 37388296783107, 52849675731761, 39728733029158]
def xsM : List Nat := roots_55.map (· &&& dom_55)
def goalM : Nat := goal_55 &&& dom_55
def NN : Nat → Nat
  | 4 => 2
  | 5 => 8
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xa0f8f63247baa070
  | 5, 0 => 0xb5787098a4f836c38a64578173ea86206b85db7462f268f94e4db2d947baa070
  | 6, 0 => 0x47baa070
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf000f000f000f000000000000000000000000000000000000000000000000000cc00cc00cc00cc00000000000000000000000000000000000000000000000000aa00aa00aa00aa00000000000000000000000000000000000000000000000000aa000000aa000000000000000000000000000000000000000000000000000000550055005500550000000000000000000000000000000000000000000000000033003300330033000000000000000000000000000000000000000000000000000000ff000000ff0000000000000000000000000000000000000000000000000000000000ff00ff
  | 0, 1 => 0xff00ff0000000000000000000000000000000000000000000000000000000000ff00f000ff00f000000000000000000000000000000000000000000000000000ff00cc0000000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000ff000000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0xa7654c97655
  | 5, 0, 0 => 0xc76545c97635c97525976505c76515cb7655c87655c97655
  | 6, 0, 0 => 0xc97655
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
  | 0, 0 => 0x18c1c380000000000000000000000000000000000000000000000000000000000631a34000000000000000000000000000000000000000000000000000000000000e1c300000000000000000000000000000000000000000000000000000000000001c00000000000000000000000000000000000000000000000000000000001ff1e3c00000000000000000000000000000000000000000000000000000000019ce5cb00000000000000000000000000000000000000000000000000000000000fe03f0000000000000000000000000000000000000000000000000000000000001fff
  | 0, 1 => 0x1ffe0000000000000000000000000000000000000000000000000000000000001fc1ff80000000000000000000000000000000000000000000000000000000001f300000000000000000000000000000000000000000000000000000000000001f01fc00000000000000000000000000000000000000000000000000000000001f00000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x1ce5cba00000000000000000000000000000000000000000000000000000000016b3a750000000000000000000000000000000000000000000000000000000000b5efdf0000000000000000000000000000000000000000000000000000000000b08fc000000000000000000000000000000000000000000000000000000000014a1020000000000000000000000000000000000000000000000000000000000094c58a00000000000000000000000000000000000000000000000000000000000f603f0000000000000000000000000000000000000000000000000000000000000edf
  | 0, 1 => 0x1fff1200000000000000000000000000000000000000000000000000000000001fedffa0000000000000000000000000000000000000000000000000000000001fbb1200000000000000000000000000000000000000000000000000000000001f09fc00000000000000000000000000000000000000000000000000000000001f09100
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_55 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_55 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]
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
private theorem z4_0 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 8 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 0 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 8 → Z 5 i = true := z5_0
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
  scr dom_55 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_55 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_55 roots_55 goal_55 7 := by
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

theorem low_55 : Lower dom_55 roots_55 goal_55 7 := S_55.noCircuit

namespace S_31
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (2, 3), (4, 5), (6, 7), (6, 14), (9, 11), (9, 13), (9, 25), (10, 11), (10, 14), (10, 26), (12, 13), (12, 14), (17, 19), (17, 21), (17, 25), (18, 19), (18, 26), (20, 21), (22, 23), (22, 30), (24, 25), (24, 26), (28, 29), (28, 30)]
def r1sG : List Nat := [1, 1, 2, 4, 6, 6, 9, 9, 9, 10, 10, 10, 12, 12, 17, 17, 17, 18, 18, 20, 22, 22, 24, 24, 28, 28]
def r2sG : List Nat := [3, 5, 3, 5, 7, 14, 11, 13, 25, 11, 14, 26, 13, 14, 19, 21, 25, 19, 26, 21, 23, 30, 25, 26, 29, 30]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [2203520468227, 6601533424389, 11021172933902, 6601566979331, 2203722586371, 10999613490435, 26461395092249]
def xsM : List Nat := roots_31.map (· &&& dom_31)
def goalM : Nat := goal_31 &&& dom_31
def NN : Nat → Nat
  | 4 => 3
  | 5 => 8
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xc7224fa9bb9cd500ac05225e
  | 5, 0 => 0xc5159104be3fb924ac05225e8c616cec67c576555299e96d3a6b8d412b0e7274
  | 6, 0 => 0xac05225e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f0f0f000000000000000000000000000000000000000000000000000000000cccccccc00000000000000000000000000000000000000000000000000000000aaaaaaaa00000000000000000000000000000000000000000000000000000000555555550000000000000000000000000000000000000000000000000000000033333333000000000000000000000000000000000000000000000000000000000f0f0f0f0000000000000000000000000000000000000000000000000000000000ff00ff000000000000000000000000000000000000000000000000000000000000ffff
  | 0, 1 => 0xfffff0f000000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000fff0f0f000000000000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000ff00f00000000000000000000000000000000000000000000000000000000000ff000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x976540ba654ca7655
  | 5, 0, 0 => 0xa76505ca7535ca7655c76515a87655ca6525ca7645da7655
  | 6, 0, 0 => 0xca7655
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
  | 0, 0 => 0x33830380000000000000000000000000000000000000000000000000000000000360e34000000000000000000000000000000000000000000000000000000000001c1c30000000000000000000000000000000000000000000000000000000003fe3e3c0000000000000000000000000000000000000000000000000000000003c9f1cb0000000000000000000000000000000000000000000000000000000000c7cfc700000000000000000000000000000000000000000000000000000000003fc03f0000000000000000000000000000000000000000000000000000000000003fff
  | 0, 1 => 0x3fff0380000000000000000000000000000000000000000000000000000000003ffc0000000000000000000000000000000000000000000000000000000000003f830380000000000000000000000000000000000000000000000000000000003c03fc00000000000000000000000000000000000000000000000000000000003c030000000000000000000000000000000000000000000000000000000000003c00000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x338b4ba0000000000000000000000000000000000000000000000000000000002b66e7500000000000000000000000000000000000000000000000000000000015bd3df0000000000000000000000000000000000000000000000000000000002a42c20000000000000000000000000000000000000000000000000000000000149918a0000000000000000000000000000000000000000000000000000000000c74b4500000000000000000000000000000000000000000000000000000000001ac01f00000000000000000000000000000000000000000000000000000000000036ff
  | 0, 1 => 0x3fffdba0000000000000000000000000000000000000000000000000000000003ffc9000000000000000000000000000000000000000000000000000000000003fdbdba0000000000000000000000000000000000000000000000000000000003e53fe00000000000000000000000000000000000000000000000000000000003e53da00000000000000000000000000000000000000000000000000000000003e50900
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 14 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 14 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 14 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 14 then wireAt i else 0
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_31 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_31 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := []
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
private theorem z4_0 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 8 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 0 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 8 → Z 5 i = true := z5_0
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
  scr dom_31 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_31 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_31 roots_31 goal_31 7 := by
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

theorem low_31 : Lower dom_31 roots_31 goal_31 7 := S_31.noCircuit

namespace S_39_16
def pairsG : List (Nat × Nat) := [(17, 19), (17, 21), (17, 49), (18, 19), (20, 21), (22, 23), (22, 54), (48, 49), (50, 51), (50, 54), (52, 53), (52, 54)]
def r1sG : List Nat := [17, 17, 17, 18, 20, 22, 22, 48, 50, 50, 52, 52]
def r2sG : List Nat := [19, 21, 49, 19, 21, 23, 54, 49, 51, 54, 53, 54]
def mpG : Nat := 0xfff
def pool6G : List Nat := [19865099703571, 24263112659733, 22064089411861, 24263146214675, 19865099710739, 55049471792403, 52849945219889]
def xsM : List Nat := roots_39_16.map (· &&& dom_39_16)
def goalM : Nat := goal_39_16 &&& dom_39_16
def NN : Nat → Nat
  | 3 => 1
  | 4 => 3
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xd0e4fa84
  | 4, 0 => 0xf1f4dea9d0e4fa841af93793
  | 5, 0 => 0xd0e4fa84
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00000000000000000000000000000000000000000000000000000000000000f0000000f0000000000000000000000000000000000000000000000000000000cc000000cc000000000000000000000000000000000000000000000000000000aa000000aa000000000000000000000000000000000000000000000000000000550000005500000000000000000000000000000000000000000000000000000033000000330000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xb1a4
  | 4, 0, 0 => 0xb194b1a4b104
  | 5, 0, 0 => 0xb1a4
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 16
  | 4 => 16
  | 5 => 16
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 3 0) :: stateWires n (ids >>> 3)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xf800000000000000000000000000000000000000000000000000000000000000c70000000000000000000000000000000000000000000000000000000000000036800000000000000000000000000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000000000000000ff80000000000000000000000000000000000000000000000000000000000000c97
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfc40000000000000000000000000000000000000000000000000000000000000e720000000000000000000000000000000000000000000000000000000000000b6900000000000000000000000000000000000000000000000000000000000005bf0000000000000000000000000000000000000000000000000000000000000a400000000000000000000000000000000000000000000000000000000000000496
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_39_16 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_39_16 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_39_16 == dom_39_16) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_39_16 goalM u ys) : RunD dom_39_16 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_39_16 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_39_16 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_39_16 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_39_16 roots_39_16 goal_39_16 6 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_39_16 goal_39_16 := by
    have h0 : isConstB dom_39_16 goal_39_16 = false := by decide +kernel
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

end S_39_16

theorem low_39_16 : Lower dom_39_16 roots_39_16 goal_39_16 6 := S_39_16.noCircuit

namespace S_61
def pairsG : List (Nat × Nat) := [(1, 5), (4, 5), (9, 13), (9, 25), (9, 41), (12, 13), (17, 21), (17, 25), (17, 49), (20, 21), (24, 25), (28, 29), (33, 37), (33, 41), (33, 49), (36, 37), (40, 41), (44, 45), (48, 49), (52, 53), (56, 57), (60, 61)]
def r1sG : List Nat := [1, 4, 9, 9, 9, 12, 17, 17, 17, 20, 24, 28, 33, 33, 33, 36, 40, 44, 48, 52, 56, 60]
def r2sG : List Nat := [5, 5, 13, 25, 41, 13, 21, 25, 49, 21, 25, 29, 37, 41, 49, 37, 41, 45, 49, 53, 57, 61]
def mpG : Nat := 0x3fffff
def pool6G : List Nat := [18730909247769]
def xsM : List Nat := roots_61.map (· &&& dom_61)
def goalM : Nat := goal_61 &&& dom_61
def NN : Nat → Nat
  | 4 => 1
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x995298d1
  | 5, 0 => 0x995298d1
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x33333333000000000000000000000000000000000000000000000000000000003333000033330000000000000000000000000000000000000000000000000000330033003300330000000000000000000000000000000000000000000000000030303030303030300000000000000000000000000000000000000000000000002222222222222222
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
  | 0, 0 => 0x3ff00000000000000000000000000000000000000000000000000000000000003c0fc00000000000000000000000000000000000000000000000000000000000330c3c00000000000000000000000000000000000000000000000000000000002a8a2200000000000000000000000000000000000000000000000000000000000071dd
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3ff11000000000000000000000000000000000000000000000000000000000003c4fc80000000000000000000000000000000000000000000000000000000000332cbc00000000000000000000000000000000000000000000000000000000002a9a6700000000000000000000000000000000000000000000000000000000003fffff
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_61 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_61 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]]
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
  scr dom_61 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_61 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_61 roots_61 goal_61 6 := by
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

theorem low_61 : Lower dom_61 roots_61 goal_61 6 := S_61.noCircuit

namespace S_55_8
def pairsG : List (Nat × Nat) := [(9, 11), (9, 13), (9, 25), (9, 41), (10, 11), (10, 14), (10, 26), (12, 13), (12, 14), (24, 25), (24, 26), (28, 29), (28, 30), (40, 41), (42, 43), (42, 46), (42, 58), (44, 45), (44, 46), (56, 57), (56, 58), (60, 61), (60, 62)]
def r1sG : List Nat := [9, 9, 9, 9, 10, 10, 10, 12, 12, 24, 24, 28, 28, 40, 42, 42, 42, 44, 44, 56, 56, 60, 60]
def r2sG : List Nat := [11, 13, 25, 41, 11, 14, 26, 13, 14, 25, 26, 29, 30, 41, 43, 46, 58, 45, 46, 57, 58, 61, 62]
def mpG : Nat := 0x7fffff
def pool6G : List Nat := [11033973230859, 13232962931469]
def xsM : List Nat := roots_55_8.map (· &&& dom_55_8)
def goalM : Nat := goal_55_8 &&& dom_55_8
def NN : Nat → Nat
  | 4 => 2
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xddcfd71ec22d231e
  | 5, 0 => 0xc22d231e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00ff0000000000000000000000000000000000000000000000000000000000ff00f000ff00f000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000cc00cc00cc00cc00000000000000000000000000000000000000000000000000aa00aa00aa00aa00
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x584256885
  | 5, 0, 0 => 0x56885
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
  | 0, 0 => 0x7fe00000000000000000000000000000000000000000000000000000000000007e1f800000000000000000000000000000000000000000000000000000000000781e000000000000000000000000000000000000000000000000000000000000661980000000000000000000000000000000000000000000000000000000000001c070000000000000000000000000000000000000000000000000000000000000000f
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x7fe00800000000000000000000000000000000000000000000000000000000007f9fe60000000000000000000000000000000000000000000000000000000000791e4400000000000000000000000000000000000000000000000000000000006699a2000000000000000000000000000000000000000000000000000000000055d57100000000000000000000000000000000000000000000000000000000002a6a9f
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_55_8 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_55_8 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)]]
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
  scr dom_55_8 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_55_8 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_55_8 roots_55_8 goal_55_8 6 := by
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

theorem low_55_8 : Lower dom_55_8 roots_55_8 goal_55_8 6 := S_55_8.noCircuit

namespace S_62_1
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (9, 11), (9, 13), (9, 25), (9, 41), (17, 19), (17, 21), (17, 25), (17, 49), (33, 35), (33, 37), (33, 41), (33, 49)]
def r1sG : List Nat := [1, 1, 9, 9, 9, 9, 17, 17, 17, 17, 33, 33, 33, 33]
def r2sG : List Nat := [3, 5, 11, 13, 25, 41, 19, 21, 25, 49, 35, 37, 41, 49]
def mpG : Nat := 0x3fff
def pool6G : List Nat := [18730909247769]
def xsM : List Nat := roots_62_1.map (· &&& dom_62_1)
def goalM : Nat := goal_62_1 &&& dom_62_1
def NN : Nat → Nat
  | 4 => 2
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xe3d1755c4ced5003
  | 5, 0 => 0x4ced5003
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xaaaaaaaa00000000000000000000000000000000000000000000000000000000aaaa0000aaaa0000000000000000000000000000000000000000000000000000aa00aa00aa00aa00000000000000000000000000000000000000000000000000a8a8a8a8a8a8a8a8000000000000000000000000000000000000000000000000a0a0a0a0a0a0a0a00000000000000000000000000000000000000000000000008888888888888888
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x58d258c85
  | 5, 0, 0 => 0x58c85
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
  | 0, 0 => 0x3c0000000000000000000000000000000000000000000000000000000000000003c0000000000000000000000000000000000000000000000000000000000000003c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3e2000000000000000000000000000000000000000000000000000000000000023d0000000000000000000000000000000000000000000000000000000000000113c0000000000000000000000000000000000000000000000000000000000000ccf000000000000000000000000000000000000000000000000000000000000088a0000000000000000000000000000000000000000000000000000000000000445
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_62_1 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_62_1 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]]
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

namespace S_15
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (2, 3), (4, 5), (6, 7), (6, 14), (9, 11), (9, 13), (10, 11), (10, 14), (12, 13), (12, 14)]
def r1sG : List Nat := [1, 1, 2, 4, 6, 6, 9, 9, 10, 10, 12, 12]
def r2sG : List Nat := [3, 5, 3, 5, 7, 14, 11, 13, 11, 14, 13, 14]
def mpG : Nat := 0xfff
def pool6G : List Nat := [10999613490435, 4402510168837]
def xsM : List Nat := roots_15.map (· &&& dom_15)
def goalM : Nat := goal_15 &&& dom_15
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xa8d11512
  | 4, 0 => 0xa8d11512
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00000000000000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000cccc000000000000000000000000000000000000000000000000000000000000aaaa
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
  | 0, 0 => 0xfc00000000000000000000000000000000000000000000000000000000000000c38000000000000000000000000000000000000000000000000000000000000033400000000000000000000000000000000000000000000000000000000000000c3
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfe00000000000000000000000000000000000000000000000000000000000000eba0000000000000000000000000000000000000000000000000000000000000b7500000000000000000000000000000000000000000000000000000000000005df
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_15 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_15 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]
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

namespace S_15_16
def pairsG : List (Nat × Nat) := [(17, 19), (17, 21), (17, 25), (18, 19), (18, 26), (20, 21), (22, 23), (22, 30), (24, 25), (24, 26), (28, 29), (28, 30)]
def r1sG : List Nat := [17, 17, 17, 18, 18, 20, 22, 22, 24, 24, 28, 28]
def r2sG : List Nat := [19, 21, 25, 19, 26, 21, 23, 30, 25, 26, 29, 30]
def mpG : Nat := 0xfff
def pool6G : List Nat := [19864628107539, 26461597209369]
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_15_16 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_15_16 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]]
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

namespace S_57
def pairsG : List (Nat × Nat) := [(9, 25), (9, 41), (17, 25), (17, 49), (24, 25), (33, 41), (33, 49), (40, 41), (48, 49), (56, 57)]
def r1sG : List Nat := [9, 9, 17, 17, 24, 33, 33, 40, 48, 56]
def r2sG : List Nat := [25, 41, 25, 49, 25, 41, 49, 41, 49, 57]
def mpG : Nat := 0x3ff
def pool6G : List Nat := [18730909247769]
def xsM : List Nat := roots_57.map (· &&& dom_57)
def goalM : Nat := goal_57 &&& dom_57
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x4c41b69c
  | 4, 0 => 0x4c41b69c
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x303030300000000000000000000000000000000000000000000000000000000030300000303000000000000000000000000000000000000000000000000000003000300030003000000000000000000000000000000000000000000000000000202020202020202
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
  | 0, 0 => 0x3e0000000000000000000000000000000000000000000000000000000000000031c0000000000000000000000000000000000000000000000000000000000000293000000000000000000000000000000000000000000000000000000000000006f
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3ea000000000000000000000000000000000000000000000000000000000000035d00000000000000000000000000000000000000000000000000000000000002b700000000000000000000000000000000000000000000000000000000000003ff
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_57 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_57 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_57 == dom_57) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_57 goalM u ys) : RunD dom_57 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_57 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_57 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_57 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_57 roots_57 goal_57 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_57 goal_57 := by
    have h0 : isConstB dom_57 goal_57 = false := by decide +kernel
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

end S_57

theorem low_57 : Lower dom_57 roots_57 goal_57 5 := S_57.noCircuit

namespace S_58_1
def pairsG : List (Nat × Nat) := [(1, 3), (9, 11), (9, 25), (9, 41), (17, 19), (17, 25), (17, 49), (33, 35), (33, 41), (33, 49)]
def r1sG : List Nat := [1, 9, 9, 9, 17, 17, 17, 33, 33, 33]
def r2sG : List Nat := [3, 11, 25, 41, 19, 25, 49, 35, 41, 49]
def mpG : Nat := 0x3ff
def pool6G : List Nat := [18730909247769]
def xsM : List Nat := roots_58_1.map (· &&& dom_58_1)
def goalM : Nat := goal_58_1 &&& dom_58_1
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xe01b32dc
  | 4, 0 => 0xe01b32dc
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xa0a0a0a000000000000000000000000000000000000000000000000000000000a0a00000a0a00000000000000000000000000000000000000000000000000000a000a000a000a000000000000000000000000000000000000000000000000000808080808080808
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_58_1 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_58_1 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_58_1 == dom_58_1) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_58_1 goalM u ys) : RunD dom_58_1 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_58_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_58_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_58_1 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_58_1 roots_58_1 goal_58_1 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_58_1 goal_58_1 := by
    have h0 : isConstB dom_58_1 goal_58_1 = false := by decide +kernel
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

end S_58_1

theorem low_58_1 : Lower dom_58_1 roots_58_1 goal_58_1 5 := S_58_1.noCircuit

namespace S_23_8
def pairsG : List (Nat × Nat) := [(9, 11), (9, 13), (9, 25), (10, 11), (10, 14), (10, 26), (12, 13), (12, 14), (24, 25), (24, 26), (28, 29), (28, 30)]
def r1sG : List Nat := [9, 9, 9, 10, 10, 10, 12, 12, 24, 24, 28, 28]
def r2sG : List Nat := [11, 13, 25, 11, 14, 26, 13, 14, 25, 26, 29, 30]
def mpG : Nat := 0xfff
def pool6G : List Nat := [11033973230859]
def xsM : List Nat := roots_23_8.map (· &&& dom_23_8)
def goalM : Nat := goal_23_8 &&& dom_23_8
def NN : Nat → Nat
  | 3 => 2
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x41ff4bae07711a25
  | 4, 0 => 0x7711a25
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00f00000000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000cc00cc0000000000000000000000000000000000000000000000000000000000aa00aa00
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x10836884
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_23_8 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_23_8 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)]]
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

namespace S_27
def pairsG : List (Nat × Nat) := [(1, 3), (2, 3), (9, 11), (9, 25), (10, 11), (10, 26), (17, 19), (17, 25), (18, 19), (18, 26), (24, 25), (24, 26)]
def r1sG : List Nat := [1, 2, 9, 9, 10, 10, 17, 17, 18, 18, 24, 24]
def r2sG : List Nat := [3, 3, 11, 25, 11, 26, 19, 25, 19, 26, 25, 26]
def mpG : Nat := 0xfff
def pool6G : List Nat := [2203722586371]
def xsM : List Nat := roots_27.map (· &&& dom_27)
def goalM : Nat := goal_27 &&& dom_27
def NN : Nat → Nat
  | 3 => 2
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x4ad23dd9317f6efe
  | 4, 0 => 0x317f6efe
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f0000000000000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000f000000000000000000000000000000000000000000000000000000000000000c0c0c0c000000000000000000000000000000000000000000000000000000000a0a0a0a
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_27 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_27 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
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

def isoMv_47_16 : List (Nat × Nat) := [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]
theorem low_47_16 : Lower dom_47_16 roots_47_16 goal_47_16 8 :=
  lower_iso isoMv_47_16 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31_32

def isoMv_23_32 : List (Nat × Nat) := [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)]
theorem low_23_32 : Lower dom_23_32 roots_23_32 goal_23_32 5 :=
  lower_iso isoMv_23_32 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15_16

def isoMv_39 : List (Nat × Nat) := [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]
theorem low_39 : Lower dom_39 roots_39 goal_39 5 :=
  lower_iso isoMv_39 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15

def isoMv_39_8 : List (Nat × Nat) := [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)]
theorem low_39_8 : Lower dom_39_8 roots_39_8 goal_39_8 5 :=
  lower_iso isoMv_39_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15_16

def isoMv_51_8 : List (Nat × Nat) := [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_51_8 : Lower dom_51_8 roots_51_8 goal_51_8 5 :=
  lower_iso isoMv_51_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15_16

def isoMv_60_1 : List (Nat × Nat) := [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem low_60_1 : Lower dom_60_1 roots_60_1 goal_60_1 5 :=
  lower_iso isoMv_60_1 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_58_1

namespace S_63
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (2, 3), (4, 5), (6, 7), (6, 14), (6, 38), (9, 11), (9, 13), (9, 25), (9, 41), (10, 11), (10, 14), (10, 26), (12, 13), (12, 14), (17, 19), (17, 21), (17, 25), (17, 49), (18, 19), (18, 26), (20, 21), (22, 23), (22, 30), (22, 54), (24, 25), (24, 26), (28, 29), (28, 30), (33, 35), (33, 37), (33, 41), (33, 49), (34, 35), (34, 38), (36, 37), (36, 38), (40, 41), (42, 43), (42, 46), (42, 58), (44, 45), (44, 46), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (56, 57), (56, 58), (60, 61), (60, 62)]
def r1sG : List Nat := [1, 1, 2, 4, 6, 6, 6, 9, 9, 9, 9, 10, 10, 10, 12, 12, 17, 17, 17, 17, 18, 18, 20, 22, 22, 22, 24, 24, 28, 28, 33, 33, 33, 33, 34, 34, 36, 36, 40, 42, 42, 42, 44, 44, 48, 50, 50, 50, 52, 52, 56, 56, 60, 60]
def r2sG : List Nat := [3, 5, 3, 5, 7, 14, 38, 11, 13, 25, 41, 11, 14, 26, 13, 14, 19, 21, 25, 49, 19, 26, 21, 23, 30, 54, 25, 26, 29, 30, 35, 37, 41, 49, 35, 38, 37, 38, 41, 43, 46, 58, 45, 46, 49, 51, 54, 58, 53, 54, 57, 58, 61, 62]
def mpG : Nat := 0x3fffffffffffff
def pool6G : List Nat := [2203520468227, 9904396829955, 4402510168837, 6601533424389, 4403048812037, 6601566979331, 2203722586371, 10999613490435, 19795908630787, 37388296783107, 11021727439374, 18730909247769, 2203419346179, 9921543144197, 18718308827909, 9913491852805, 18709719623173, 11033973228803, 18735051708675, 9904598948099, 9921576699139, 2204059110915, 6602072067589, 46218246226729, 9922081787397, 18718309557765, 55048698987313, 11034478316291, 55019087931674, 55001639617830, 26461395092249, 26431381373722, 26427103249177, 26427641109017, 48417269482793, 57247722242865, 36301636502277, 19795974948099, 36293080122627, 13220196188942, 26462135589401, 36322641579561, 39728464593702, 46334258512678, 13237106311950]
def xsM : List Nat := roots_63.map (· &&& dom_63)
def goalM : Nat := goal_63 &&& dom_63
def NN : Nat → Nat
  | 5 => 17
  | 6 => 218
  | 7 => 585
  | 8 => 248
  | 9 => 23
  | 10 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0xed65c9fbe39172d7dec50353d640cf82c05feb307b30d805690b53645c3cfa52532a6f1250f9f54945227f713294dd262c1c38e125219d330dfb5be7083364ee0058ccbe
  | 6, 0 => 0x48208d5b451f7c0844a5495d44171c5a4336213041d2b5e9413a622b3d6a3aa23d535c863c9d32213c90e5203ac40ac738d4648438b24b9336bd7d74357914e53492314e3404b2bb33e54322338e8f4532973ec63099cb892ef292772ee6f2792ebe6d1e2e6465742ab77fdf2a74cf62292e6b882779c54f25c2de98259c3dab2540075924af7386249d0b20240fb7712244ea161fc65dff1cdb9a501cd4a8b619e9242f19d5fa501937f12c17ee43171794abf01658de33136f20cf12f8fd591233c968118e73740e5d008b0d4ae8920b09be8408f317a508b6a95208b46aa406e4336306165d7605a197e904773d450407793401af582a01aa037001066dc7
  | 6, 1 => 0x9474875292c480a291d2873e8f7a66348b4cbdd88962c5848779863784aee97b84a84090847b918683d3f0b082edb98b80f736817f7fda887ec1d06c7dc38fba7bd03bf87b28099b7b21dfe47ae95c9a78bfe5b478ad1f3a77f0a41a7540a7b373fc3566734bd994733b5fbd722eeeb671c6cf516ecfff346c8086ed6a8772f968eb1e2567aab8ca6763e9e567565d1c670d50ea66b0725163e5ff9a6118463c5e8590775e2d8aab5de8ee725d32c40d5d26770c5b599cb35b3aaa0c5a093d145969f67057856ccf575b122e57530f605500c22f546ec5c45219ec9450d5abbc4ffd7cef4f91d4624f528bca4e5da3554d4559a54beaf5014952e23548558c39
  | 6, 2 => 0xe239d3cedfafa86bdefc4b6fdbbf0132db91cf32d98b4f12d96b098ed94242e0d71df03fd6209a43d4e034e8d44acf7bd39bcc59d24dccc2d1cac08ed0598291cf88cc23cd09a9edcc64bb85cc074e3dcb5a385fca68402bca5bf32ac9880156c95fdca5c88f18d1c87f4516c44ede8ac3ce9525c2326ee5c1c6c658c1c1b5f9bd8203c1bb404d62bafe51c4b93d8228b8e76ab4b64c0e50b5ed8edbb53518b2b413d78cb1dac57bb1c041a4ac947fdeaab8c6f9aa9fb6c0a6d960c6a6b1151ba639a4b1a5ab77aea35c9dd6a2cebd7fa099576aa0745bbaa0156c749fccbae49cf000b59cec71d59c280e959b7eee8699aeb74597c9062c9554ae35948dfb25
  | 6, 3 => 0xfff9fcc0fe552278fd53dd81fac2bdd0f9d7d4ccf88239f6f6ff1a04f6bf844df66bd375f6225679f5a82443f575c6d4f47b805bf1d24826f0f9ec74f04399afee2cb29febf74c8aea742c98e9e0e609e85d85b9e77599a9e68c3207e580cb8ae2c800d1e25c5844
  | 7, 0 => 0x1baefe3919ba301a19389a7718595dba182b403118261f78181315341701656116bceacf1673385e15d3b4e415ba6e6315af65f114e907ff1421b37a13dbfd0413967e2f130a5a8912763853120eee54117804a41161181a109410fb0fe6d3690fcb33c20f9aa5fd0f7093b80e38b6fe0e1f184a0e19c3470db432850d5a81df0cec37f80cb5970c0c6d8e9c0c232aad0c22507d0b88cc090b3080880af197a60acf09dd0a7677f509199978081c74db07ff7b8107d530e907c20e2706415f2606291d8306237d4e060f596e057c0b7a04824cd40442bd8604064f330389d21f035eb4ec020b934d0185b8510166035701430e7d00d76e0200b91207003e83f9
  | 7, 1 => 0x35fe022a35169f3a34b74566345ddff533d25e6233cd017f338d060c332a82ad330bca3f32fa2f95328e870832440aae31959d4e30b8bae1309e6aff303037e9301052cd2f67316b2f3594f12f1abea52e9b5e9e2e8a65942df741622df013cb2d7f44742d4b28f82d076f792bc612742bbea46f2b811d732b7b467f2b0fca262af8e8dd2a2ab54a29e188d329af2b6429259dd728c73e9828bd116f27d257372713cf0026ad11912648e3a824f59d08247cfe3f23f0c29e232c6add22c96b302288025420f506ac20887980204fb0ae1f9547f51f3e5d811ea663541e5c09241df8f12c1cd038361c96ea491c93c9e31c397d011c193f401c0dd5381bc7d4b0
  | 7, 2 => 0x5133fceb50e23594506a59244ffcc3574fbdd0064e5372144e3cd4e24dc9c7c04d84259f4cec75af4c16af5f4b8c97694b2478044b093b3e4aeba8ec4abd1d0b4a9428d24a530fc24a0a039049e125c649bb2fc3480eeebd476a5be94760868246f1b31146de759445a7f598459ecff74486548a445ca64c441caf3c43c1fcc9431f7df7412c1b3840e5429a408f5a30405e8a73401a1c4f3fd3ef6d3f4622693f3bf5403f2afc363f0151163da8061b3d3e89f93d2c7c353cba78eb3c21f90f3c21b4153ba5ac113b795ba03af6ada23a822ece3a4fc20639c6347938eeefa638c6876638c0d21d38bbb164389a48a73872edd9381fcf14381209743644f7dd
  | 7, 3 => 0x6b302ff16a27cc6b6a08291469dcc40d680f799367c6dab467b7d8a267339425671066ce66ea172966e4732066d0a35665b3f9f765ac519f65778ba46433ac9f6414205d6407b8f163939f3362d73fc862bc93d2624d6d5b61d0c2e560c0426060afae3b601579705f7e58aa5f5675315f411ea25f18482b5ef408b65dd41be55dd08b735d5fdc975d464d8d5d0b15675cb746015c97debb5bf13ab45b8c3f8e5b3bed485aa8a6b95a8322685a7ee5485a5bc66559d5a23b595c19525925466958e8d81658b561005863a643583d5a59565f733c56488c3a55f5a32a54b99c5154af2ec554a96c09547f88975462936b53c0149952a2b5415253af29514e4ccd
  | 7, 4 => 0x8cc6a357894ebb5e88f1dcc588a82a54884d6a8e87fc390c87ef60598436e17f83c0be0982e2ff4782c96d8a826a3ebd8265c20c817ebe3580ad9dba80ab0b5c7f24c13b7f123d697ef09be27eeeae697ead80c27e9aa7927e79e8eb7e704a887dc60fd37da51d3c7da0a7537d7e4e447bd0c6937ba3c0797ad7bf5b79f7001d79f05dc0799c7ca278d1319678b010357851225b7849360277e8b9bb77b0fd7077abf413778509c27677af7c75ce6c6f7544c0b174cf39e473a349a873764210730c5ff87301de5f72e94115727718da72286c4f71b7c8f26fb8decd6f410f6b6edb0ec36d0dc9146cbe8b686cac52696c85f2fa6c2229556bd931506b345782
  | 7, 5 => 0xabbe6e52ab8bcb77aab1140caa904610a99c2534a994b72fa98efbbea97a0c43a7853e24a748d152a692d1eba63f2c4fa6246bc4a5f12d82a4d69db9a44634c2a39ec2eea37a73fba3147353a296a4d8a1ecc184a174c228a16a86e7a1033ae0a0c208bfa0bf578aa041465d9f3c616f9f19428c9edbc97b9ec0d7899db654639d65b4079d648c2e9d28f2069be41d5a9b6287b79b5b3fbe9b258fe99aca79e39a6914bc9a320e8e9a07492d99e5b62f98f4208d970d4168963ca10f960bb76c95d4c56f9551aacc94fe5d2694d778219438db949329f8a291ed9b59919a80f891503a30902de3228f052a2c8e3f8c778da35b008d9c69668d1b84e68ced12b2
  | 7, 6 => 0xc6dfc8e3c6919570c5eadd1ec5e5017dc5368674c4d7a737c4cfc905c4b9fc07c42e642ac3651e39c33e8ebcc22ea7bdc20018d3c1f8fe15c1f2c1fcc1980f89c154e976c10d13c9c0f590b7c088640ac01a4c7abf239619bebb555abe697909be4ba155bd323f75bcc91ac8bcb9a3e3bcb2b5b1bbf021b9bae8aadfbab9a1bdba9cdb19ba1aa2e5b91d4ce9b8e84e0bb859f422b7dce78eb79618a9b7874599b75b51ebb702d21ab6919842b62ad8c2b5f6eebfb593ef12b5446adbb413f1b2b2ce525eb247a1b0b1bbd0a8b1522b5aaf9abc18af616e2baeef6ae1ae1b1d36ae1abeb8ade6658dadd6bb62ad64f2d1ad58a5d0ad096b8bac71715eac41cfbe
  | 7, 7 => 0xdd864c18dd6521e7dd5eacb4dcbf3510dcb507e7dbcabd8fdb7eec9cdb4f33a9db12c556da446b89da2e6ae7d957a573d9196516d8f800a3d872797ad84d19d6d7e8ebedd7abb4fbd7783301d7272a2ed6d35949d67f4dd9d6165ffad53d3f77d5194ea3d4adc04ad4890869d4061f74d405b4dbd31fe84fd3152e0bd30c22d4d1e7bd46d18b6727d14d3a21d1296545cfb854c2cf96c9c3cf94ce8dcf84fccdcf245f8dcef3ff30ceddfab4ce4a3505cde52a59cd786ec8cc6d1337cc438988cc026abccb5a385fcb099803cb08702aca5180ccc9f553bac9ecc21fc934441dc8c1bbacc8bcd3fdc822d2dec7b46166c7914283c73369bbc72863d7c71b0c31
  | 7, 8 => 0xfbf342e7fbac7402fb83ad54faeaf5bdfad9fd75fa510104f9aef702f92406b2f8f03dcbf87e7dd9f86c0c02f70b8f8af6d3c780f66bd375f6680c4df5e5463cf582e6acf4d74db7f47a7e2cf42d11bff415a1b9f377c984f32d82bcf2c92a07f1febaa9f1e2cc0df0e272b8f0b82528f0479b38f0187b65ef37b654ef04ed08ede0877aed3bc136ec56a60cebefca4bebb11d4aeb7dc701ead62371ea42ff39e9e0e609e849f352e8027d18e695e825e60fff99e56d3923e52d0e51e4e88dfde4a6b616e403206de3ecbae8e2f6af66e28853e8e27a3ccfe1760161e171d949e041dc16e01ebd33dffa78b3df1659addeff409cde8141e7de0e2346ddf8e307
  | 7, 9 => 0xfff37a59ffcf0a7cff939ceffe3b2b67fdfab3d3fd16c02afce85029fcd91be7fc465d48
  | 8, 0 => 0x405c8f3d3f69e5183f086e6d3c38e0113c21f90f387c2216359f67e7354bc4fd342cdee934064f6c32ba82ac315024ba302ca7772f1362052de85b922d90db782cb7e2692c9946a22b81626d2b44f41a28a4a83e284f0649275958f2272770732705880d26beaf6f26488ebe261c309d233e519822c735132219ec0a20292edb1fb72b911e7c63c91d094b741b78d4bc1b70b190196672e1191531f4175a929b131bfefa12baa67712324797119811441187183a1004221f0f8898390e7e15130e7dd0190e783ebe0d52c9a60cabde0a0c867e660c22507d0c167f100acf09dd087867580754ea1506291d8305c61dd605869eb103f1b952036df15000f5a3d2
  | 8, 1 => 0x833df9038276397281bd8a2f806266ad804281917ecd8d627e22428f7e1a8a567db173387d7d57bc7cea112d7bf841387bf0d3337b2b17a179e15a2877d135d076f0de3376db0b2e7341d2fd70946692705b5d9f6f69601f6c4b6e046b6909ce679d352a673394256449b75d62623a3561ca400861aa33685fff77045f492eb65d1e66bc5c9fbd605af03eb05aa8a6b95916f56256dbe56f54c1de1054b47b9853b7a8b552942b72523dc211515c2919514aca6d51099cc65038abd6500139404f0fba7a4ed5e3f64e2ce2974c4c79c44b62f61f4b0c2c394a3f78dc4a0d197449e125c649226c8f48b0ac9d44cd758b43a9f848425327d74214fad14079af63
  | 8, 2 => 0xc31b6fd9be4be64fbc545819baa8a17cba45dd7fb84d21e0b7a3f583b702d21ab4e46fecb37ef559b253eee6b0e1dcffb080f6ebaf1123ebae064aa9ace974c5ac8a86ebabbe6e52aab1140caaa935daaa8df529aa87c3f1aa07d0ffa98e4816a8e78fc4a661d0dfa5cabbeaa494c22fa3f2435da1807b91a1662bafa141bf77a02ef21b9e58572e9db654639c48de239b56a6c89b1dd7b099ed5e8798411d819710a45894b8834e944ede0093f42b8d9351acbb917fb21d9117715e90061e318f78512d8f6e24048d5eaaf98d3d413a8c76bee98b3e939c8a81f0ca89211e6a88f300e188edfe0d88ede02887b12daa869b7594867726a184e9742a84a3bdb4
  | 8, 3 => 0xffcceadcff939ceffb192d73fac274d4f9b99d75f96feb04f9092d95f8b72109f13569a4f109fd47f1027f58efeaeca8eef3064deec76f65eeae7dabec164c1eeb94b67beb7a065aeabec0cdea643d52e8b54ab1e878be20e73f702ce606f433e575a6eae46b0a58e3d420a8e2f02cffe21fca1de1ccafbce07b344edf6d0221dec9aaa0ddd589c4dd4db3aada7890dfd988b69cd87f9952d8653959d7d8277ed4fb6d4fd4e47617d3152e0bd1efb8f3d0dd3a20d0317033d010ef66cf446c2dcea2794ccdd2d617cb46a5f8c5d3e588c5899ec0c576ef75c483e9fec33e8ebc
  | 9, 0 => 0xf2854adfdee29a6ad1efb8f3bad4da24b47be621b031a5c87f4590c97e1a8a567cea112d76f0de33764e5f61705b5d9f61ca40085fbac6fd5cde0cce42b779a334064f6c2efbd9641b78d4bc1729918f1606144c0e7e151305169eb0
  | 10, 0 => 0x42b779a3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x7700770077007700000000000000000000000000000000000000000000000000550f5f00550f5f000000000000000000000000000000000000000000000000005500550055005500000000000000000000000000000000000000000000000000330033333333330000000000000000000000000000000000000000000000000033003300330033000000000000000000000000000000000000000000000000000f000f000f000f0000000000000000000000000000000000000000000000000000ffff0000ffff00000000000000000000000000000000000000000000000000000000ffffffff
  | 0, 1 => 0x5050505050505050000000000000000000000000000000000000000000000000303030303030303000000000000000000000000000000000000000000000000020202020202020200000000000000000000000000000000000000000000000000ff00ff00ff00ff00000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000ee00ee00ee00ee00000000000000000000000000000000000000000000000000cc00cc00cc00cc00000000000000000000000000000000000000000000000000aa00aa00aa00aa
  | 0, 2 => 0x11111111ffffffff000000000000000000000000000000000000000000000000111111113333333300000000000000000000000000000000000000000000000011111111111111110000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000000e0e0e0e0e0e0e0e0000000000000000000000000000000000000000000000000707070707070707000000000000000000000000000000000000000000000000050f050f050f050f00000000000000000000000000000000000000000000000005050505ffffffff
  | 0, 3 => 0x3333333333333333000000000000000000000000000000000000000000000000333333330000000000000000000000000000000000000000000000000000000033303330333033300000000000000000000000000000000000000000000000003300330033003300000000000000000000000000000000000000000000000000222222222222222200000000000000000000000000000000000000000000000011ff11ff11ff11ff000000000000000000000000000000000000000000000000113311331133113300000000000000000000000000000000000000000000000011111f1f11111f1f
  | 0, 4 => 0x777777777777777700000000000000000000000000000000000000000000000066666666666666660000000000000000000000000000000000000000000000005577557755775577000000000000000000000000000000000000000000000000555f555f555f555f0000000000000000000000000000000000000000000000005555555555555555000000000000000000000000000000000000000000000000555555550000000000000000000000000000000000000000000000000000000055005500550055000000000000000000000000000000000000000000000000004444444444444444
  | 0, 5 => 0xaa88aa8888888888000000000000000000000000000000000000000000000000aa55aa55aa55aa55000000000000000000000000000000000000000000000000aa00aa00aa00aa00000000000000000000000000000000000000000000000000a8a8a8a8a8a8a8a8000000000000000000000000000000000000000000000000999999999999999900000000000000000000000000000000000000000000000088ff88ff88ff88ff00000000000000000000000000000000000000000000000088888888ffffffff0000000000000000000000000000000000000000000000008888888888888888
  | 0, 6 => 0xbbbbbbbbbbbbbbbb000000000000000000000000000000000000000000000000aaeeaaeeaaeeaaee000000000000000000000000000000000000000000000000aaaaaaaaaaaaaaaa000000000000000000000000000000000000000000000000aaaaaaaa00000000000000000000000000000000000000000000000000000000aaa8aaa8aaa8aaa8000000000000000000000000000000000000000000000000aaa0aaa0aaa0aaa0000000000000000000000000000000000000000000000000aa88aa88aa88aa88000000000000000000000000000000000000000000000000aa88aa88aa00aa00
  | 0, 7 => 0xcccccccccccccccc000000000000000000000000000000000000000000000000cccccccc00000000000000000000000000000000000000000000000000000000ccc8ccc8ccc8ccc8000000000000000000000000000000000000000000000000ccc0ccc0ccc0ccc0000000000000000000000000000000000000000000000000cc88cc88cc88cc88000000000000000000000000000000000000000000000000cc33cc33cc33cc33000000000000000000000000000000000000000000000000cc00cc00cc00cc00000000000000000000000000000000000000000000000000c8c8c8c8c8c8c8c8
  | 0, 8 => 0xeecceeccaa00aa00000000000000000000000000000000000000000000000000eeaaeeaaeeaaeeaa000000000000000000000000000000000000000000000000eeaaeeaacc00cc00000000000000000000000000000000000000000000000000ee00ee00ee00ee00000000000000000000000000000000000000000000000000e0e0e0e0e0e0e0e0000000000000000000000000000000000000000000000000dddddddddddddddd000000000000000000000000000000000000000000000000cceecceecceeccee000000000000000000000000000000000000000000000000cccfcccfcccfcccf
  | 0, 9 => 0xeeeeeeeeaaaaaaaa000000000000000000000000000000000000000000000000eeeeeeee00000000000000000000000000000000000000000000000000000000eeeee8e8eeeee8e8000000000000000000000000000000000000000000000000eeeee0e0eeeee0e0000000000000000000000000000000000000000000000000eeee0000eeee0000000000000000000000000000000000000000000000000000eeeceeeceeeceeec000000000000000000000000000000000000000000000000eee0eee0eee0eee0000000000000000000000000000000000000000000000000eecceecceecceecc
  | 0, 10 => 0xf3f3f3f3f3f3f3f3000000000000000000000000000000000000000000000000f3f3f3f3f0f0f0f0000000000000000000000000000000000000000000000000f3f3f3f300000000000000000000000000000000000000000000000000000000f3f0f3f0f3f0f3f0000000000000000000000000000000000000000000000000f1f1f1f1f1f1f1f1000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000000eeeeeeeeeeeeeeee000000000000000000000000000000000000000000000000eeeeeeeecccccccc
  | 0, 11 => 0xfafafafa00000000000000000000000000000000000000000000000000000000faf8faf8faf8faf8000000000000000000000000000000000000000000000000faf8faf8f8f8f8f8000000000000000000000000000000000000000000000000faf0faf0faf0faf0000000000000000000000000000000000000000000000000fac8fac8fac8fac8000000000000000000000000000000000000000000000000fa00fa00fa00fa00000000000000000000000000000000000000000000000000f8f8f8f8f8f8f8f8000000000000000000000000000000000000000000000000f5f5f5f5f5f5f5f5
  | 0, 12 => 0xfefcfefcfefcfefc000000000000000000000000000000000000000000000000fe00fe00fe00fe00000000000000000000000000000000000000000000000000fdfdfdfdfdfdfdfd000000000000000000000000000000000000000000000000fcfcfcfcfcfcfcfc000000000000000000000000000000000000000000000000fcfcfcfcf0f0f0f0000000000000000000000000000000000000000000000000fcf0fcf0fcf0fcf0000000000000000000000000000000000000000000000000fafafafafafafafa000000000000000000000000000000000000000000000000fafafafaf0f0f0f0
  | 0, 13 => 0xff33ff33ff33ff33000000000000000000000000000000000000000000000000ff33ff33ff00ff00000000000000000000000000000000000000000000000000ff11ff11ff11ff11000000000000000000000000000000000000000000000000ff00ff00ff00ff00000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000fefefefefefefefe000000000000000000000000000000000000000000000000fefefefefcfcfcfc000000000000000000000000000000000000000000000000fefefefe00000000
  | 0, 14 => 0xffaa0000ffaa0000000000000000000000000000000000000000000000000000ffa8ffa8ffa8ffa8000000000000000000000000000000000000000000000000ff88ff88ff88ff88000000000000000000000000000000000000000000000000ff88ff8888888888000000000000000000000000000000000000000000000000ff55ff55ff55ff55000000000000000000000000000000000000000000000000ff55ff55ff00ff00000000000000000000000000000000000000000000000000ff55ff5555555555000000000000000000000000000000000000000000000000ff44ff44ff44ff44
  | 0, 15 => 0xffddffddffddffdd000000000000000000000000000000000000000000000000ffccffccffccffcc000000000000000000000000000000000000000000000000ffccffccff00ff00000000000000000000000000000000000000000000000000ffccffcccccccccc000000000000000000000000000000000000000000000000ffaaffaaffaaffaa000000000000000000000000000000000000000000000000ffaaffaaff00ff00000000000000000000000000000000000000000000000000ffaaffaaaaaaaaaa000000000000000000000000000000000000000000000000ffaaf0a0ffaaf0a0
  | 1, 0 => 0xfffcfffcfffcfffc000000000000000000000000000000000000000000000000fffcfffcfcfcfcfc000000000000000000000000000000000000000000000000fffafffafffafffa000000000000000000000000000000000000000000000000fff8fff8fff8fff8000000000000000000000000000000000000000000000000fff5fff5fff5fff5000000000000000000000000000000000000000000000000fff0fff0fff0fff0000000000000000000000000000000000000000000000000fff0fff0f0f0f0f0000000000000000000000000000000000000000000000000ffeeffeeffeeffee
  | 1, 1 => 0xffffffff88888888000000000000000000000000000000000000000000000000ffffffff00000000000000000000000000000000000000000000000000000000fffff8f8fffff8f8000000000000000000000000000000000000000000000000fffff0f0fffff0f0000000000000000000000000000000000000000000000000ffff8888ffff8888000000000000000000000000000000000000000000000000ffff0000ffff0000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x8c8278351f58d6c59510158c7559510158c6c52260158c6c522b015887559510058c823f35065886c52260058d8859510c5897552510058c8852260c58c8859510758c6c594d355886c522b0058c8952510758c88523a235
  | 5, 0, 1 => 0x8c88522b0c5
  | 6, 0, 0 => 0x8c8b6c59513568c8a6c493f3568c885951280c68c6c643835016896c5251280066c52231f010068a826c351f0068c6c533f350168c5251280c016886c231f14006886c525128176887b522d1f0068c885128140c68c885251270c68c7552351f0168d6c593f35016
  | 6, 0, 1 => 0x8c6c523f350668c8a826c231f6886c5128140068c8859351f0c6886c5251270068c885251280a68a52351f0c0068c883f35130c688524e3f351a68873523f21006886c5251292868c44433f35016896c593f350068c886c52512f68c593f350c0168c52514b280c6
  | 6, 0, 2 => 0x8c88523a3556c593f35010068c8a827b351f66c52514b280068875523f230066c4e3f3514016886c5951280068c8a6c351f026786c523f350066c52514e280168c6c613f2c0168c89523f350768c826c4c3f3566c52512801006886c593f352968852443f23006
  | 6, 0, 3 => 0x8c8a603f350c6887e393514006886c59351f0066c524e351f0168c8a826c512868c88525128076886c4e351f146886c3f35130068c524c3f350c68c885951350c68c8852371b0c68c885143280c68c8a52231f0c65f523f350c0168c351f140c0168c8852351f0a6
  | 6, 0, 4 => 0x8a6c52231f0068c8852351f0768c8a5251280c66c351f14010068852443f3517688524e3f230c66c5552351f0168d75523f350168c6c593f230168c6c3f35120168d89523f350c68c88593f350768c8876523f2368c4b433f350c6885f52351f0c68c885242200c6
  | 6, 0, 5 => 0x886c524220006883f23140c0068975523f350066c4e433f350168c6c52512c0168d885251280c68c8a593f350c68c887e39231468c8a6c56351f6008c886c522b56c524c3f35006886c595135006886c52371b006886c5143280068c8b593f350c68c886c5d3f356
  | 6, 0, 6 => 0x8b6c593f350068852231f0c0068c885251281a68c88533f350c68c886c51351268c887b52321f68a6c5251280066c5f523f2301688443f35140068c6c231f140168d88593f350c68c885228150c688525144280068c887b2d1f1466c4b433f35006523f230c01006
  | 6, 0, 7 => 0x887552351f006886c5228150068c6c5128140168c6c5251270168875593f350068c886c5950356885244351f0068c8a6c603f2368c8b846c3f3568a6c593f3500675523f3501006524b443f3500688753f35140068c886438350c68875525128006524e443f35016
  | 6, 0, 8 => 0x88593f350c006524e3f350c016008c886c52265884e3f35140c68852514e280c68c8a6c593f236886c6438350068c75523f230168c88753f231468c88613f2c0c68c6c595128016886c533f35006885251280c0068c8b6c593f236008c8975525158a6c524e351f6
  | 6, 0, 9 => 0x886c613f2c0068c886c351f1368a523f230c006008c8875595153f35140c0100688524e351f0c6008c82783f3558c8a6c5e3f3568c88433f351a68c6c59351f016524e4b3f350c68c786c52351f68844433f350068c6c3f35130168a826c3f230068d88523f35076
  | 6, 0, 10 => 0x8c88523f2e58c8a6c3f2302652351f0c01006886f52351c0068c8852231f0c68c6c5951350168c6c52371b01688351f140c0068c886c59483568c6c5143280168c887b523f256885552351f0c68c8852512a2868c88593f230c68c883f35120c6008d886c59515
  | 6, 0, 11 => 0x6c524e3f230168c88523f3a3568c525144280168c6c524c351f68c88523923036884e433f350c68c89756c525168c8852512c0c66c5f52351f0168c6c5242200168c3f23140c0168a75523f350068c88523f230a68c88524a393568c887b523f2468c88593f352a6
  | 6, 0, 12 => 0x8c88523f230766c3f2314010068d6c5251280168c8844351f146887b3f2d140068c8a75523f2368c753f35140168c755251280168c895251280c68c885251280c68c52231f0c016885f523f230c68c8a6c60351f68c88231f140c6886c593f23006886c3f3512006
  | 6, 0, 13 => 0x8c6c5228150168c886c3f231268c88756c595168c6c523f35186886c52512c0068c75593f350168c89593f350c6887e5239230068c88593f350c68a524e3f350c6
  | 7, 0, 0 => 0x8c88523f35230c78c886c5235321f78c886c5251442878c6c523e351f017886c52423f230078c6c523f231f0178c8a826c3f351f78c886c523f350478c886c6b593f357886c523f23200078c886664523f3578c886c3f231f147008c8a6c3f350266c52513f35010078c886c5235311f78c886c5e523f357
  | 7, 0, 1 => 0x6c52514b3f350078c89523f35280c7886c5239351f0078c886c52231f1e78c88523f35280c78c887e523935317008c8a523f230c68c886c5852231f78c88736c523f23700886c525128006008c3f35140c0168c8852351f0c0b78c887c6c523f237008c88523f350a66c52514e3f35017008c8a827b3f356
  | 7, 0, 2 => 0x886c4e3f351468c88756c52512878c88523f351b0c78c8a6c5235231f7886c5251351f00700886c52514e2868c886c5234231f78c8a826c3f3c357008c885239350368c88523f37350c78c886c52231f0c78c75523f35280178c88876c52351f78c886c63523f237008c886c613f2c68c88523f3b350c7
  | 7, 0, 3 => 0x885f523f350c6008c88351f140c68c8a7e6c52351f78c8864613f350c78c8a523f351f0c78c8852423f350c78c886c523f2302700886c593f350068d6c523f3528017006c524e3f350168c88523f3e230c78c6c523f23220178c88523f35200c78c886c3f39231478c8851433f350c78c8a523f35340c7
  | 7, 0, 4 => 0x6c524e4b3f3568c6c60523f350178c88523f230c0878c883f3523140c78c88756c593f3578c886f52351f0c78c887b52351f0c78c8a6c52351f1b78c6c524f3f350178c6c52513f23017008c52351f0c0168c8a826c513f357008c886f52351c6886c523f352c0078c886c613f350e78c886c52483f237
  | 7, 0, 5 => 0x887e5239350068c886c503f35147008c88523f35076006c3f3514010068c523f35280c0178c8875523f352d78c88756c52351f78c736c523f2301700886c524e351f68c886c6b351f1478c883f3528140c78c88736c3f23147008c8a75523f3568c88523f35270c78c523f35230c0178c6c52513f28017
  | 7, 0, 6 => 0x886c523f2d230078c8857523f350c78c6c523f350e0178c886c5251342877b6c523f35010078c6c58523f350178c886c5251280c7886c523f3b35007886c52463f35007896c523f35280078c6c52503f35017008a6c523f23006887b6c3f35140078c64523f350c0178c886c523f353078c88523f230c097
  | 7, 0, 7 => 0x886c64524e3f35700886c5552351f6886c51433f350078c6c523f3835017008d8875523f3568c885235231f0c78c886c351f1c1478c888252351f0c7886c523f351b007008c886c593f236008c886c3f35126886c62523f350078c886c6052351f78c8a52513f350c78c88593f35280c7886c523f3735007
  | 7, 0, 8 => 0x8c886452351f0c78c886c593f35347886c523f35292878c887e52351f0c78c886c593f350c700886c351f140068c885235281f0c7886c64613f350078c88523f350f0c78a6c523f351f007886c52423f350078c886c523f352f78c88736c52231f78c886a523f350c78c886c523f2c237886c523f3520007
  | 7, 0, 9 => 0x826c523f3501007008c887b3f2d146886c3f3523140078c8a6c523f353178c886c52351f0378c8852351f1b0c7886f6c52351f007887b523f352d007887b6c52351f0078c886c5852351f78c886c44433f3578c886c5250351f78c885237351f0c7006c52351f010068c6c59523f35017008c886c52231f6
  | 7, 0, 10 => 0x8c7b6c523f2301700886c4e433f356008c886c52512c68c887e6c523f2376c523f352801007887e6c3f35140078c886c65523f2378c8875523f35317008c887e5239236886c3f352814007008c6c3f2314016008c887b523f316886c523f35270078c6c523f3c350178861523f350c0076c523f352301007
  | 7, 0, 11 => 0x886c593f35280078c886c5c52351f78c8a6c523f34237886c57523f350078c6c6152351f0178c6c3f3534140178c886c62523f2378c886c52514e2870088523f230c006008c7b77523f2d66c64523f35010078c88523f35150c7885251443f35007008c887b523f3267e6c523f35010078c886c523f35197
  | 7, 0, 12 => 0x8c8a826c351f6886c6a523f350078c886c5251350e700886c5f523f2368c887c6c3f35147008c886c231f1468c886c523f352578c8a6c523f231f78c88645251350c7008c887b522d1f68c8852513f351a7886c5235231f00788826c52351f0078c6c3f351f140178c88525135280c78a6c52513f35007
  | 7, 0, 13 => 0x8c886c351f140c78c6c52351f1e0178c88816c523f2378c885752351f0c7886c6452351f0078c886c52493f3578c886c52513f317887e6c52351f007008c896c5251286008c886c52512868c886c351f1e14788523f351f0c007886c5235281f007008852443f35006886c523f350f007008c6c52231f016
  | 7, 0, 14 => 0x8c88523f35280778c887e6c3f231478c887b64523f2d78c886c3f28231478c88746c523f3578c88523f35310c78c6c5235341f0170088524e443f356886c52351f1b0078c8861523f230c78c8a826c3f352378c6c63523f350178c886c523f352478c826c523f230178c886c35341f147886c5237351f007
  | 7, 0, 15 => 0x8c6c513f35140178c886c483f35147008c8873523f2168c887c6c52351f78c6c64523f23017008c896c593f3568c88523f35320c7008c886c593f3568c523f3e350c017008a6c524e3f3568c7e6c523f23017008875523f350068c6c523f28230178c88716c523f2378c8a826c3f352878c883f3e35140c7
  | 7, 1, 0 => 0x8852513f350c0078c886c5b523f357886c52513528007008c886c52512768c88523f34230c78c6c52423f230178c88826c52231f78c6c523f23200178c886c423f23147008c8a52351f0c68c8852413f350c78c88736c52351f78c8858523f230c7886c523f35150076c615f523f35017886c524e3f352d7
  | 7, 1, 1 => 0x8c886c52351f0278c8a523f35280c78c886c523f350d78c886c6452231f78c887d6c523f2378c8a736c523f2378d88756c523f3578c88523e351f0c7008c6c5251280168c887e6c52231f78c88523f231f0c7008c8852443f236886c64525135007008c886c51281468c8a523f35230c78c886c52473f357
  | 7, 1, 2 => 0x8c886c59512868a7b6c523f35007008c786c523f3568c88827b52351f78c6c5251351f0178c88706c523f2378c8852443f35347886c3f352d140078c88523f230c0578c886c5248351f7886c5752351f0078c8a6c52503f3578c886c51351f1478c886c65523f3578c887a6c523f2378852514e3f350c7
  | 7, 1, 3 => 0x8c886c523f351178c6c523f352c0178d88523f35280c70088524e3f350c6886c523f35320078c886c64603f3578c88523f23220c7008c6c593f35016008c6c52514b286886c523f3531007008c8875523f2368c887c6c52513578c8852351f0c087008c8876523f3568c88523f3935327886c61523f23007
  | 7, 1, 4 => 0x886c523f2321007008c887e39351468c8852513f280c7008c886c59351f68a6c523f35230078c8860523f350c7886c52352d1f007886c523f230c0078c886c523f230878c88524f3f350c78c8852513f230c78c88826c5251287008a6c52351f006008c886c3f35136886c58523f230078c8852351f0c097
  | 7, 1, 5 => 0x8c6c523f37350178c886c3f351b1478c88524e443f35700883f35140c0068a7e6c523f350078c88816c613f3578c6c523f3b350178c88826c593f3578c886c3f2d231478a6c523f35280078c8873523f230c78c88716c523f3578c7b6c3f3514017886c523f231f0078c88866c523f3578c887e6c5251287
  | 7, 1, 6 => 0x8c6c523f3e230178c6c523f35200178c886c423f351478c887e6c593f3578c6c51433f350178c886c6452503578c88523f350e0c78875523f35280078c886c3f3e231478c8858523f350c78c6c523f351b0178c8852503f350c78c886c5250352878c886c523f3123700523f350c01006008c88523f230c6
  | 7, 1, 7 => 0x8c887e6c52351f7008c886c51432868c88523f351f0c7886c523f3923007008c8a6c52231f68c887b6c351f1478c886c5652351f7006c5f523f35016008c6c351f140168c886c645c3f3578c88523f38350c78c88523f230c0b78c6c64613f350178c6c52423f35017886c524e443f3578c886c523f32237
  | 7, 1, 8 => 0x8c886c52403f3578c8a6c5235341f78c6c523f35270178c61523f350c017886c52513f23007008852351f0c0068c8859523f350c7008c6c524c3f3568c6c3f3523140178c886c522d231f78c8a6c52351f1e7008c886c5951356008c886c52371b68c6f6c52351f0178c7b6c52351f0178c88876c523f237
  | 7, 1, 9 => 0x88736c523f2300700886c5f52351f6008c886c5242206008c8a6c603f3568c5251443f35017008c883f23140c6008c8975523f3568c8a523f3e350c78c8a7e6c523f237008c8875523f3568c88523f3c350c78c8a6c523f2823788523f35230c007886c52513f280078c7e6c3f35140178c6c3f352814017
  | 7, 1, 10 => 0x886c58523f350078c8a826c3f353278c826c52351f0178c883f3534140c7008d896c523f3568c88816c52351f78c886c35231f1478c6c593f35280178864523f350c0078c6c57523f350178c887b523f230c78c886c5452351f7008c6c4b433f35688523f35280c0078c88523f3935037008c523f230c016
  | 7, 1, 11 => 0x8c88756c523f2378c6c523f350f0178c6c6a523f350178c887e6c351f14700886c524e3f2368c883f351f140c78c886c6b3f23147886c6864523f357008c88443f351468c523f35340c0178c8852513f350c78c8a6c52423f237886c523f350e007008c885251442868c886152351f0c78c6c5235231f017
  | 7, 1, 12 => 0x8c8b6c593f356008c8852231f0c68c6c5237351f0178c886c351f1b147008c887e523b356886c61523f351078c6c6452351f017886c52351f1c0078c7e6c52351f017008c886c523d356008c8a6c52512868c523f351f0c0178c6c5235281f0178c886c523f351d7886c523f38350078c886c69523f357
  | 7, 1, 13 => 0x6c61523f35010078c8863523f350c78c8882523f230c7008c88753f351468c886c60523f2378c8852351f0c0378c8852351f1e0c7886c59523f350078c8a6c5251351f7008c887552512868c886c523f351678882523f39350078c6c52351f1b017008c886d523f3568c886c52512d2878c88726c523f237
  | 7, 1, 14 => 0x8c88523f28230c7008c885244351f6008d886c5251286886c523f3c3500700887b523f2d0068c887f6c523f237887e523f39350078c886c524a3f3578c886c52453f357008c8a6c593f3568c886c523f35337008c75523f350168c885235341f0c7008c524b443f3568c886c523f35317886c5c523f35007
  | 7, 1, 15 => 0x8c886c52413f3578c88513f35140c7887b6c523f230078c887a523f352d78c887a6c52351f78c886c52503f237008c8875593f356006c523f2301006008a826c3f350068c8864523f230c78c887d6c52351f78c6c523f35150178c887e523f230c78c886c593f352d700886c3f23140068c886c6b52231f7
  | 7, 2, 0 => 0x8c887552351f6008d886c593f3568c8852423f230c7008c886c5228156886c6152351f0078c6c645251350178c88523f23200c78c886c6452483578c52513f350c0178c6c52513528017886c3f35140c0078c886c524835287886c52513f351778c886c523f2303788615f523f350c78c886c523f230e7
  | 7, 2, 1 => 0x8c6c61523f230178c886c3f35311478c52514b3f350c700886c52231f006008c886c533f3568c886c59523f2378c6c5752351f0178c8882523f39237008c885251280c66c523f351f01007008c88523f2d0568c886452443f3578c88523f352a287886c3f351f140078c886c52231f1c78c88836c523f237
  | 7, 2, 2 => 0x8c6c523f35320178c886c52351f1d78c88523f39350278c886e6c52351f78c8a6c523f3e237886c52351f0c0078c886c52351f087886c5f5a523f3578c6c3f3e351401788826c523f230078c885251351f0c78c8a6c523f351b7008c886c64383568c6c523f3531017008a523f350c0068c886c5c523f237
  | 7, 2, 3 => 0x8c886c3f23140c78c89756c523f3578c88523f352c0c7008c8844433f356886c64523f230078c6c58523f23017887e6c523f230078c8852513f350a7886c3f393514007886c523f28230078c88523f36350c7008c8a826c3f2368c886c6b5251287008c88593f350c68c8a6c52423f3578c886c67523f357
  | 7, 2, 4 => 0x8c6c523f3423017886c52483f35007008c8852351f0c6886c5f523f352d7886c513f35140078c886c3f34231478c8a7b6c52351f78c88846c593f3578c886c352d1f147
  | 8, 0, 0 => 0x8c8864523f350c78c887e6c523f35318008c887e523f350c70000886c3f3514006008c886c6b52351f7008c88523f35280c78c88826c523f35328008c88736c523f2378c886c52513f353488c886c52513f350c8008c88523f35230c7008c886c52513f287008c8882523f350c7008c886c60523f3578c886c523f3935348008c886c524f3f357
  | 8, 0, 1 => 0x8c886c59523f357008c8882523f393578c88876c64523f358008c886c523f351f78c886c6b64523f358008c886c52351f1c78c886c6b523f35288008c886c523f383578c886c6b523f35238008c886c523f35037008c886c523f350e700887b6c523f35007008c886c58523f357008c886c52503f35700006c523f350100600008c886c523f236
  | 8, 0, 2 => 0x886c523f35280078c886c523f3e352d800008c6c523f2301600008c8a826c3f35600008c886c3f23146008c8a6c523f3e357008c886c523f3c3578c886c52514e3f35800008c887b523f2d600886c523f3523007008c887e523f393570088826c523f35007008c886c5c523f357008c886c523f35057008c6c61523f350170000886c52351f006
  | 8, 0, 3 => 0x8c886c52351f1e700008c8a523f350c6008c88736c523f357008c887c6c523f35700008c886c52231f6008c6c523f351f017008c886c3f351f1478c88756c523f35288008c6c523f3534017008c886c52513f357008c886c6152351f7008c886c3f3534147008c886c3f35140c700886c64523f3500700887e6c523f35007008c887b6c523f237
  | 8, 0, 4 => 0x8c88826c523f351f800886c615f523f357008c886c513f35147008c886c523f350278c886c523f3534238008c886c64523f2378c886c523f35230c8008c88523f3e350c7008c887e6c523f237008c886c3f3935147008c886c523f28237008c886c5235341f7008c886c52351f0c7008c886c63523f357008c88826c523f2378c887e6c61523f358
  | 8, 0, 5 => 0x8c6c52514b3f357008c886c5239351f78c88826c523f3c35800008c886c5251286008c887e7b523f3578c887e6c523f351f8008c88523f350c087008c886c52423f2378c886c64523f353488c886c64523f350c8008c886c523f232078c886c523f3534288008c88827b523f357008c6c52513f350178c886c523f35280c8008c886c52483f357
  | 8, 0, 6 => 0x8c886c523f352378c886c61523f352d88c88736c523f352388c886c6452513f35800008c886c52351f68c887e6c52513f358008c886c523f352c78c886c615a523f3588c88826c52513f35800008c886c593f35600886c523f352d007008c886f6c523f357008c887b6c523f357008c886c5251351f700008a6c523f35006008c88523f350c097
  | 8, 0, 7 => 0x8c886c523f351b7008c886c62523f357000088523f350c006008c886c523f37357008c886c523f2d237008c7b6c523f35017008c886c523f3b357008c887e6c523f357008c886c52463f357008c896c523f35287008c886c523f3528700008c8a6c523f236008c887b6c3f3514700008c887e523935600008c6c3f3514016008c88856c523f357
  | 8, 0, 8 => 0x8c887b523f352d7008c887b6c52351f700008c6c52351f0168c886c523f352d1f80000886c5f523f3568c886c615f523f35800008c886c351f146008c886c64613f357008c8a6c523f351f78c886c523f35342d8008c886c52423f357008c7b776c523f357008c886c523f3e237008c886c523f35207008c886c51433f357008c8a6c523f35347
  | 8, 0, 9 => 0x8c886c57523f3578c887b6c64523f35800008c88523f230c6008c6c64523f35017008c885251443f357008c7e6c523f35017008c6c523f3528017008c887e6c3f35147008c886c3f3528147008c886c523f35277008c8861523f350c7008c6c523f3523017008c826c523f35017008c88816c523f357008c886c3f3523147008c886f6c52351f7
  | 8, 0, 10 => 0x8c887d6c523f357008c887e6c52351f7008c88523f351f0c7008c886c6b523f237008c886c5235281f78c88826c523f3523800008c8852443f356008c886c523f350f7008c886c6a523f357008c88523f35340c78c886c52513f352d8008c886c5235231f7008c88826c52351f7008c8a6c52513f357008c886c593f352878c886c6b61523f358
  | 8, 0, 11 => 0x8c886c5251352870000886c523f23006008c886c523f351578c887e6c64523f358008c88806c523f3578c887e6c523f352888c886c6b523f351f800008c8875523f35600886c61523f350078c886c64523f352388c887e6c523f35238008c886c52351f1b78c88826c523f35288008c887a6c523f357008c886c5237351f7008c886c6452351f7
  | 8, 0, 12 => 0x8c886c3f3e35147008c88796c523f357008c886c523f3531700008c88523f350c6008c886c61523f2378c886c6b52513f358008c886c523f35097008c8a7b6c523f357008c886c3f352d147008c886c5752351f700886c523f351f00700886c523f350c007008c886c523f35087008c886c6452513578c886c523f351f1c8008c8852513f350c7
  | 8, 0, 13 => 0x8c886c6a64523f358008c8a6c523f3523700886c52513f35007008c886c523f34237008c886c52352d1f7008c886c523f230c7008c88876c523f3578c886c5251443f35800886c523f393500700008c8a6c52351f6008c886c58523f237008c88523f350c0b78c886c61523f35348008c886c523f353278c886c61523f350c8008c6c523f3e35017
  | 8, 0, 14 => 0x8c8875523f352878c886c64523f352d8008c887b523f350c78c886c523f35341f800008c523f350c0168c886c523f351f0c88c886c523f352d28800008c883f35140c6008c8a7e6c523f3578c886c523f351f1e800886c52514e3f357008c8a6c523f352878c886c523f352d238008c886c523e351f7008c886c523f231f7008c886c523f23217
  | 8, 0, 15 => 0x8c886c52513f23700008c8852351f0c6008c88756c523f357008c886c523f39237008d886c523f352870000886c524e3f356008c886c6b3f35147008c886c523f23227
  | 9, 0, 0 => 0x8c887e6c523f3578c886c523f352878c886c523f352378c88826c523f357008c886c52351f68c887b6c523f357008c6c523f35016008c886c3f35146008c886c523f3568c886c52513f3578c886c523f393578c886c523f351f78c886c523f353478c886c523f350c7008c886c523f2368c886c61523f357
  | 9, 0, 1 => 0x886c523f350068c886c6b523f357008c88523f350c68c886c523f3e3578c886c523f352d7008c8a6c523f3568c886c64523f357
  | 10, 0, 0 => 0x8c886c523f356
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 44
  | 6 => 52
  | 7 => 60
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
  | 0, 0 => 0x3f03fc3ff007f0000000000000000000000000000000000000000000000000003f3ffc3f03fff0000000000000000000000000000000000000000000000000003f03c03f0007c00000000000000000000000000000000000000000000000000031033fc4fc78b00000000000000000000000000000000000000000000000000031033c04f000b0000000000000000000000000000000000000000000000000000f00fc03f000700000000000000000000000000000000000000000000000000000fffc000ffff000000000000000000000000000000000000000000000000000000003fffffff
  | 0, 1 => 0xcf3cc0c303804000000000000000000000000000000000000000000000000000c1043cc0f078300000000000000000000000000000000000000000000000000000003c00f07830000000000000000000000000000000000000000000000000003f03fc3ff007f0000000000000000000000000000000000000000000000000003f03fc00000000000000000000000000000000000000000000000000000000000e00fc3bf00770000000000000000000000000000000000000000000000000000e00c03b0007400000000000000000000000000000000000000000000000000000003c00f0003
  | 0, 2 => 0x3f1c703fffffff000000000000000000000000000000000000000000000000003f1c703c4fc78b000000000000000000000000000000000000000000000000003f1c703c40c008000000000000000000000000000000000000000000000000000cf3cfcc3f3f870000000000000000000000000000000000000000000000000000e38fc03f3f87000000000000000000000000000000000000000000000000000cf3cfcc3f3f87000000000000000000000000000000000000000000000000000cf3cfcc3f3807000000000000000000000000000000000000000000000000000cf3cc3fffffff
  | 0, 3 => 0x3f1c73fc4fc78b000000000000000000000000000000000000000000000000003f1c73c0000000000000000000000000000000000000000000000000000000003f0c703c40c788000000000000000000000000000000000000000000000000003c0c403c00c78000000000000000000000000000000000000000000000000000000003c00f0783000000000000000000000000000000000000000000000000003ffc7fffffc07f000000000000000000000000000000000000000000000000003f1c73fc4fc00b000000000000000000000000000000000000000000000000003f1ffffc40ff8f
  | 0, 4 => 0x3fffffffffffff0000000000000000000000000000000000000000000000000000e38fc3bf3ff7000000000000000000000000000000000000000000000000003ffffffffff87f000000000000000000000000000000000000000000000000003ffffffffff87f000000000000000000000000000000000000000000000000003ffffc3ff0f87c000000000000000000000000000000000000000000000000003ffffc00000000000000000000000000000000000000000000000000000000003c0fc03c00f8000000000000000000000000000000000000000000000000000000e38c03b03874
  | 0, 5 => 0x3f03c03f007fc00000000000000000000000000000000000000000000000000000000000007800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003f1c703c40c0080000000000000000000000000000000000000000000000000003f03fc3ff007f000000000000000000000000000000000000000000000000000000003fffffff0000000000000000000000000000000000000000000000000000000000000000
  | 0, 6 => 0x3f1c73fc4fc78b0000000000000000000000000000000000000000000000000000e00fc3bf07f700000000000000000000000000000000000000000000000000000003c00f078300000000000000000000000000000000000000000000000000000003c00000000000000000000000000000000000000000000000000000000000000000000780000000000000000000000000000000000000000000000000000000000000078000000000000000000000000000000000000000000000000000000000000007800000000000000000000000000000000000000000000000000000000000000780
  | 0, 7 => 0xe38c03b038740000000000000000000000000000000000000000000000000000e38c00000000000000000000000000000000000000000000000000000000000003800380387000000000000000000000000000000000000000000000000000000380038038700000000000000000000000000000000000000000000000000000038000003800000000000000000000000000000000000000000000000000000313b3c04f380b00000000000000000000000000000000000000000000000000000380000038000000000000000000000000000000000000000000000000000000000003800070
  | 0, 8 => 0xe38c0000078000000000000000000000000000000000000000000000000000000383c00f3f8300000000000000000000000000000000000000000000000000000383c00038000000000000000000000000000000000000000000000000000000038000003f800000000000000000000000000000000000000000000000000000000003800070000000000000000000000000000000000000000000000000003ffffc3ff0f87c0000000000000000000000000000000000000000000000000000e38fc3bf38770000000000000000000000000000000000000000000000000000f38fc3bf3877
  | 0, 9 => 0xe38fc00f07830000000000000000000000000000000000000000000000000000e38fc00000000000000000000000000000000000000000000000000000000000e00003bf00700000000000000000000000000000000000000000000000000000e00003bf00700000000000000000000000000000000000000000000000000000e00003bf00000000000000000000000000000000000000000000000000000000e38c03b03ff40000000000000000000000000000000000000000000000000000038003803ff00000000000000000000000000000000000000000000000000000e38c03b03ff4
  | 0, 10 => 0x3f1c73ffcfc7fb000000000000000000000000000000000000000000000000003f1c73f3c0c078000000000000000000000000000000000000000000000000003f1c73c0000000000000000000000000000000000000000000000000000000003f0c703fc0c7f8000000000000000000000000000000000000000000000000003f1c703fc0c07800000000000000000000000000000000000000000000000000330c3033c0c0780000000000000000000000000000000000000000000000000000e38fc3bf3ff70000000000000000000000000000000000000000000000000000e38fc3b03874
  | 0, 11 => 0x330c33c000000000000000000000000000000000000000000000000000000000330c3033c0c7f800000000000000000000000000000000000000000000000000330c3033c0c07800000000000000000000000000000000000000000000000000330c3033c0c7f800000000000000000000000000000000000000000000000000300c003380c7f000000000000000000000000000000000000000000000000000300c003000c78000000000000000000000000000000000000000000000000000330c3033c0c078000000000000000000000000000000000000000000000000003ffffc3ff0f87c
  | 0, 12 => 0x33efbc33f0fffc00000000000000000000000000000000000000000000000000300f803000ff80000000000000000000000000000000000000000000000000003ffffc3ff0f87c0000000000000000000000000000000000000000000000000033efbc33f0f87c0000000000000000000000000000000000000000000000000033efbc33c0c07800000000000000000000000000000000000000000000000000330fb033c0f87800000000000000000000000000000000000000000000000000330c33f3cfc7fb00000000000000000000000000000000000000000000000000330c33f3c0c078
  | 0, 13 => 0x3f1ff3fc4fff8b000000000000000000000000000000000000000000000000003f1ff3fc00ff80000000000000000000000000000000000000000000000000003f1ff03c40ff88000000000000000000000000000000000000000000000000003c0fc03c00ff80000000000000000000000000000000000000000000000000003c0fc0000000000000000000000000000000000000000000000000000000000033efbff3ffffff0000000000000000000000000000000000000000000000000033efbff3f0f87c0000000000000000000000000000000000000000000000000033efbfc0000000
  | 0, 14 => 0x3c00003c0f0000000000000000000000000000000000000000000000000000003c0fc03c00ff80000000000000000000000000000000000000000000000000003c0fc03c00ff80000000000000000000000000000000000000000000000000003c0fc000000000000000000000000000000000000000000000000000000000003ffffc3ff0fffc000000000000000000000000000000000000000000000000003ffffc3c00ff80000000000000000000000000000000000000000000000000003ffffc3ff0f87c000000000000000000000000000000000000000000000000003cefcc3fb0fff4
  | 0, 15 => 0x3ffffc3ff0fffc000000000000000000000000000000000000000000000000003cefcc3fb0fff4000000000000000000000000000000000000000000000000003cefcc3c00ff80000000000000000000000000000000000000000000000000003cefcc03b03874000000000000000000000000000000000000000000000000003c0fc3fc0fff83000000000000000000000000000000000000000000000000003c0fc3fc00ff80000000000000000000000000000000000000000000000000003c0fc3c00f0783000000000000000000000000000000000000000000000000003c0c003c0fc000
  | 1, 0 => 0x3feffc3ff0fffc000000000000000000000000000000000000000000000000003feffc33f0f87c000000000000000000000000000000000000000000000000003f0ff3ffcffffb000000000000000000000000000000000000000000000000003f0ff03fc0fff8000000000000000000000000000000000000000000000000003ffffc3ff0fffc000000000000000000000000000000000000000000000000003f0ff03fc0fff8000000000000000000000000000000000000000000000000003f0ff033c0c078000000000000000000000000000000000000000000000000003cefcfffbffff7
  | 1, 1 => 0x3fffffc0000000000000000000000000000000000000000000000000000000003fffffc0000000000000000000000000000000000000000000000000000000003ffc303fffc078000000000000000000000000000000000000000000000000003ffc303fffc078000000000000000000000000000000000000000000000000003ff0003fff0000000000000000000000000000000000000000000000000000003ff0003fff0000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3503a824a004a000000000000000000000000000000000000000000000000000240ed42000cc5000000000000000000000000000000000000000000000000000240280200004000000000000000000000000000000000000000000000000000011012944e430a00000000000000000000000000000000000000000000000000011012804a000a000000000000000000000000000000000000000000000000000030064019000500000000000000000000000000000000000000000000000000000dfdc000ddff000000000000000000000000000000000000000000000000000000003df7fbbf
  | 0, 1 => 0x882000820200000000000000000000000000000000000000000000000000000041043040c060000000000000000000000000000000000000000000000000000041043040c06000000000000000000000000000000000000000000000000000003703ec2db005f0000000000000000000000000000000000000000000000000003703ec20800400000000000000000000000000000000000000000000000000003703ec2db005f0000000000000000000000000000000000000000000000000002602c4291005500000000000000000000000000000000000000000000000000013016c0db001f
  | 0, 2 => 0x3df7fbbf000000000000000000000000000000000000000000000000000000001446430a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cb2c74c3d2e85000000000000000000000000000000000000000000000000000cb2c74c3d2e85000000000000000000000000000000000000000000000000000c92430c2c26000000000000000000000000000000000000000000000000000008b20648392005000000000000000000000000000000000000000000000000000882003df7fbbf
  | 0, 3 => 0x151453944e470a0000000000000000000000000000000000000000000000000015145380080400000000000000000000000000000000000000000000000000001504519446470a000000000000000000000000000000000000000000000000001404411404470000000000000000000000000000000000000000000000000000151453944e470a0000000000000000000000000000000000000000000000000003703ec2db005f00000000000000000000000000000000000000000000000000011012804a000a000000000000000000000000000000000000000000000000000000c540000c85
  | 0, 4 => 0x3fdf7bbf6ef76a000000000000000000000000000000000000000000000000003fdf7bbf6ef76a000000000000000000000000000000000000000000000000002bdb3aab6ab06a000000000000000000000000000000000000000000000000002afb2e6b39b065000000000000000000000000000000000000000000000000002acb282b20b060000000000000000000000000000000000000000000000000002acb280200004000000000000000000000000000000000000000000000000000288b002920b020000000000000000000000000000000000000000000000000002acb282b20b060
  | 0, 5 => 0x1424c540910c95000000000000000000000000000000000000000000000000001644e916044fc0000000000000000000000000000000000000000000000000001404c114044f8000000000000000000000000000000000000000000000000000112494d0d3499f0000000000000000000000000000000000000000000000000000208440910895000000000000000000000000000000000000000000000000000370bec2db08df000000000000000000000000000000000000000000000000000020847df7fbbf0000000000000000000000000000000000000000000000000000208440910895
  | 0, 6 => 0x1534d7d4df4f9f000000000000000000000000000000000000000000000000001774ffd6df4fdf000000000000000000000000000000000000000000000000001534d7d4df4f9f000000000000000000000000000000000000000000000000001534d7c0080400000000000000000000000000000000000000000000000000001524d5d4d74f9f000000000000000000000000000000000000000000000000001504d194c64f9a000000000000000000000000000000000000000000000000001424c554954f95000000000000000000000000000000000000000000000000001424c554044f80
  | 0, 7 => 0x2aebac6bb1b8f5000000000000000000000000000000000000000000000000002aebac42000040000000000000000000000000000000000000000000000000002aebac6bb1b8f5000000000000000000000000000000000000000000000000002acba82ba0b8f00000000000000000000000000000000000000000000000000028ab8469b1b8b500000000000000000000000000000000000000000000000000299b92a96ab8aa00000000000000000000000000000000000000000000000000288b802920b8a0000000000000000000000000000000000000000000000000002269ac639198f5
  | 0, 8 => 0x3eefed56044fc0000000000000000000000000000000000000000000000000003dbfd7fdffffbf000000000000000000000000000000000000000000000000003dbfd7e928bca0000000000000000000000000000000000000000000000000003c8fc13d24ffa000000000000000000000000000000000000000000000000000334d38b3c2d17a000000000000000000000000000000000000000000000000002aebac6bb1b8f5000000000000000000000000000000000000000000000000002bfbbeebfbb8ff000000000000000000000000000000000000000000000000002afbae6bb9b8f5
  | 0, 9 => 0x3fffffd6df4fdf000000000000000000000000000000000000000000000000003fffffc2080440000000000000000000000000000000000000000000000000003fffbefffffbff000000000000000000000000000000000000000000000000003fff3abffff37a000000000000000000000000000000000000000000000000003ff2023fff2200000000000000000000000000000000000000000000000000003feffdfff7ffff000000000000000000000000000000000000000000000000003fcff9bfe6fffa000000000000000000000000000000000000000000000000003eefed7fb5fff5
  | 0, 10 => 0x375d7bb7ced77a00000000000000000000000000000000000000000000000000375d7bb3cad57a00000000000000000000000000000000000000000000000000375d7b8208044000000000000000000000000000000000000000000000000000374d79b7c6d77a00000000000000000000000000000000000000000000000000334d38b3c2d17a00000000000000000000000000000000000000000000000000334d38b3c2d17a000000000000000000000000000000000000000000000000003fffffffffffff000000000000000000000000000000000000000000000000003fffffebb9bcf5
  | 0, 11 => 0x377dffc208044000000000000000000000000000000000000000000000000000376dfdf7d7dfff00000000000000000000000000000000000000000000000000376dfdf3d3ddff00000000000000000000000000000000000000000000000000374df9b7c6dffa00000000000000000000000000000000000000000000000000366ded7795dff500000000000000000000000000000000000000000000000000340dc13504dfa000000000000000000000000000000000000000000000000000336dbcf3d3d9ff000000000000000000000000000000000000000000000000003bcf38bbe2f17a
  | 0, 12 => 0x3feffdfff7ffff000000000000000000000000000000000000000000000000003c8fc13d24ffa0000000000000000000000000000000000000000000000000003befbcfbf3f9ff000000000000000000000000000000000000000000000000003befbcfbf3f9ff000000000000000000000000000000000000000000000000003befbcf3c2d17a000000000000000000000000000000000000000000000000003bcfb8bbe2f9fa00000000000000000000000000000000000000000000000000377dfff7dfdfff00000000000000000000000000000000000000000000000000377dfff3cad57a
  | 0, 13 => 0x3d9fd3bd6effaa000000000000000000000000000000000000000000000000003d9fd3bd2cffa0000000000000000000000000000000000000000000000000003c8fc13d24ffa0000000000000000000000000000000000000000000000000003c8fc13d24ffa0000000000000000000000000000000000000000000000000003c8fc100000400000000000000000000000000000000000000000000000000003fffffffffffff000000000000000000000000000000000000000000000000003ffffffbfbfdff000000000000000000000000000000000000000000000000003fffffc2080440
  | 0, 14 => 0x3db2023dff2200000000000000000000000000000000000000000000000000003dafd5fdf7ffbf000000000000000000000000000000000000000000000000003cafc57db5ffb5000000000000000000000000000000000000000000000000003cafc540910c95000000000000000000000000000000000000000000000000003ecfe93f24ffe0000000000000000000000000000000000000000000000000003ecfe93f24ffe0000000000000000000000000000000000000000000000000003ecfe92b20b460000000000000000000000000000000000000000000000000003ecfe93f24ffe0
  | 0, 15 => 0x3eefed7fb5fff5000000000000000000000000000000000000000000000000003eefed7fb5fff5000000000000000000000000000000000000000000000000003eefed7f24ffe0000000000000000000000000000000000000000000000000003eefed6bb1bcf5000000000000000000000000000000000000000000000000003dbfd7fdffffbf000000000000000000000000000000000000000000000000003dbfd7fd2cffa0000000000000000000000000000000000000000000000000003dbfd7d4df4f9f000000000000000000000000000000000000000000000000003dbf12bdfff33a
  | 1, 0 => 0x3feffdfff7ffff000000000000000000000000000000000000000000000000003feffdfbf3fdff000000000000000000000000000000000000000000000000003fffffffffffff000000000000000000000000000000000000000000000000003feffdfff7ffff000000000000000000000000000000000000000000000000003fcff9bfe6fffa000000000000000000000000000000000000000000000000003fcff9bfe6fffa000000000000000000000000000000000000000000000000003fcff9b3c2d57a000000000000000000000000000000000000000000000000003fffffffffffff
  | 1, 1 => 0x3fffffc2990cd5000000000000000000000000000000000000000000000000003fffffc2080440000000000000000000000000000000000000000000000000003fffbefffffbff000000000000000000000000000000000000000000000000003fff3abffff37a000000000000000000000000000000000000000000000000003ff2867fff2a95000000000000000000000000000000000000000000000000003ff2023fff2200
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 142 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 142 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 142 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 142 then wireAt i else 0
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 11 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 5 => 54
  | 6 => 950
  | 7 => 3214
  | 8 => 841
  | 9 => 21
  | _ => 0
def CH : Nat → Nat → Nat
  | 5, 0 => 0xfd2cb01ff9903e3df7654d36ecbe4694ec8c197dead9cd49e9af5f4ee637d2f3e460028ae2559978da48d724d37c7943d1e55450cba7b6d0c9a8ffaabd833101b560754eb1898289af7b4160a615d43da35c9dd6a20c5d739d91a06c9d12cfee92d5f19f8d1ca8dc8beba93e86489e5a8498750b81b42a4b7f569d5f7b72b17778541dd6740f1b3f6ff5f38965bb60175e2d8aab51957ea84ed2c8b44eb8c4794c0d1f964a0fbea6468f8d1242b779a3418b8ad53d6423283d02f8483be97e912b7a26fe29120d5526908c901e0c58bf1da2b6e210d6c9fb
  | 6, 0 => 0xfb3ce380fa22a3f0f8898390f2f0b0d0f1848110ee2d2210ea800b80e93e78d0e7e15130e28db320e1588020dfc2cef0de96aba0dca489b0d3f24990d1bca3e0cd40f4c0cabde0a0c8981740c685d450c4110400c0ec6b60c0630490bd5dce90b3080880ab3b82d0a7677f50a2e374109e76cd9096e9438095e497f0922d09808d3e38907d6fdfe07d530e907962ead0772c9e80772bb3e0762ccac06d95953069bc502064bab2605d8ca4d05941c820505ca7204955e22034b623b0333699b02a793510274c39c0251a4460229104301da0aa5019eee950198e672017c2aac013f67a6013f19960116dc7e00dd3aaa00c3cc4b00c274f100904a510026e37e
  | 6, 1 => 0x229961ad21fbc41421b34e6b21b04b4821488ce020d6910f20c912ec20bc756a20550ffd203f324b20292edb1fd723ee1f7973ec1e4a11701cca3d711c96ea491bd1a8b11baefe391b932b621b6d57411b544ecf1adf1ef61ad2d1f51a85e0ab1a1f0ef61a0f2ada19ba301a198c51fb197c4452195794341955014619146ee01905f79c18d861fb18af49f7189a029d17c6219b176424311701656116ec765a16c882231673385e164c3b1b1619ab3215dcfbc215a6611415a322c01594fa38152e636e14b54a2d142b99a713c93bbb13967e2f1356a1bd12fe840a12dc22d3123ce246121b112311f45ea911a70469119dfe101161181a104283190fe749af
  | 6, 2 => 0x3292cbac328e87083257a965314c8f7130ed48393037bc2b2fd39b2d2f8051022f732a3a2ef74e3e2eeaa8122eb8ae822cce811c2cab1c642c86ddd02be61f7b2b87ab452b81626d2b44f41a2a47f4e42a347f192a0c3e3929f1c6ed29e188d329d2bd7f293f76f02937eecd292f8a3b2909654c28ce93e328ccd98028acf45728abb43f28a4a83e288ed9b9285b57bf28496c982800253a27fa285b27d9de4a2794cf0a2713cf002705880d26d3ff3726c09f492697790e2629ae6e2626b09b257a8a91255713b324f85f8a24d87e4324997c072496c8bb247cfe3f247608982455dc8223e3e51a235b96e02330e4952312fd3622d2ddb122bb5ff722999e8c
  | 6, 3 => 0x444d856e44081bfe42b779a3422278a2420e8bc441e2448a41bd3810414d38a14130a40640722d1640722552404dc3333fd62b0b3fc0c4623f8bbd3f3f7ccd563f69e5183ec88a5d3ec197f13ea3916a3e938f913d513e8d3d303da33cae957f3c86b61d3c6e2b553c62cb853c21f90f3bf19aa63b723e203b6273ae3b5816813af29aed3a792f6a3a149176393cca5b39241b63389e72c53805244f37fae97137cbacf1376135eb373b41c136be8f8a3660102c3637002235dd329c35d5916435c3f55a35bdfb0a35b2fb7e353a12a935169f3a347d3d4f343eb05733d9d424339e64ea3396b5b5338d7624335f927a3321cd97330bb31b32fa2f9532b0b299
  | 6, 4 => 0x523aacb75220e23b51ef2992519ffb995163956051610166510100775076c1ad5070db8b50370826502be650500d4be74f9f11514f972f1e4f891e7f4f3d32654ebf453b4e6d31f64e19168a4df8f18d4ddb76074dbb91724d8f90524d84259f4d40ae504d2923874cc5cc4f4c7b77174c30865f4c2fdd6d4bc7d61e4bc38b784b81a28f4ab737524aae3b9e4aa80dbc4a9136874a899ff94a7fb41e4a4706c249a0b8ec496f52fb4941462b48d1f704486f703648388c2847fc363747d3da5547cdaa5647b4abff4712aa5546f1b31146e4d62d4675c8f94640bf1846101c7d45ed83a045eca59f45a9bd13459ecff74525e12044f25f26445e4d8044540250
  | 6, 5 => 0x67339425671308da66f06e6e66ea172966d0a356657fa7266579f191654a77cb652fce69645af945643096bb641d64326404f01663fb6a7f63f5006b6378df7f6330b2ce63079e1f62fe35e162a21d5162443cd8620318f261868c926176425e609e1391606bbcf760326b045fff77045ffb8d615fc63bae5fc5f6df5fc563225f7534725ef19ced5e7772575e5eebdf5e2f68925db19d095d4d88645bab394b5b3bed485b2a96f85ac606bf5aa8a6b95a1d211859d5a23b596304d6592546695901c7ff58bacad958b855a7583d5a59583a210d57f5134d577377cb57542176574207dd5724b26256488c3a557ca93d53a145075342c976533e1533527bcb80
  | 6, 6 => 0x77efa4c177ba444e77abf41377a4037f77377e1476d8ef9576d6b2d1763d513c7633297d75ce6c6f75b2778375921c8d7578bdb575628073754f5d0e75413da674cf39e474c57267741a2ad273b05cba739112cc734cebaa7342b3f373221ae0730a5f69727718da7263ed8471f6935271c4c2dd71c1199471b0389c71acb963715fe4557147b3d9710c539970f028e070c4cd53705b5d9f704d5e58702cc10a70126baa6ec0f03b6e861e126e7126476e7107f36e5d2e3b6dd56b946db7a48b6d0dc9146cdf2d166c61f74d6bc292956b85bd996b43cd8a6adec8c96a4b04a66a0829146939788468f7280068e5d86668e3acd568b61f47680c8898673859b6
  | 6, 7 => 0x8802b78d87d2433f8744a6f887345c3f870b766e870312318643ceda85e13e5585ac7091858b93b385353ca284eff23484b6983b8436e17f842ebc3f8421f27883c0be09835cb4198340c9be8334520682f377b082c96d8a829841d78250d0be822db78b81bd8a2f817ebe358110aa5480311ee57fb807ca7f24c13b7ef47dcb7edb443f7e969d807e4fb0497e21fdaa7d7f56c67d5745f97d4640047d455fe77ce8aa237c64872b7c6329377c5cfe467bf841387babef657ba3862e7b2b17a17b04cbf17ae6d58b7aaf2d897a9854157a9059ab7a454d657a1f52087a03bd0e79e1b8a679e15a28796b687f792b8e4178b16f76788aa5397860c2e477f6f3be
  | 6, 8 => 0x96ced85296ce6dfd96aafa8e96911e4996181c3c958fec68956abeb095559da594d7782194ab739f94836f6d93b30e82939a9e6192d1b9c992954b7691b91115919f4e7b9138155890e2f04490d496ca9082705d907f0366907b4dcd904d09d68ff4ff9a8ff4638c8e8df0778e6afd808e64265c8e4d0a488def5d868d9c69668d5eaaf98d53961e8d257af88c9dac058c76bee98c48ca1e8c243bc08bf0530d8be0e7ea8bb136488b7945308afdd0c98aaa220c8a81f0ca8a7e13518a69d2278a2d572e8a26b5248a00162a89e8323289e2582189b3a92689b2bdc1899fef998941d6398938e0ef89292a5e88d1482288a82a5488795121882be4e1882a0edc
  | 6, 9 => 0xa745880ca6f69afda6d9df7fa621259fa58d967ca5858420a57708b2a5743486a52f323ba454196aa4185384a3ffc12ea3fb81c1a372506ba3600842a3481cd9a306cbaaa2f2aa4ba2a1f3bca290cb5fa26cae21a19e0ceea14c8a87a0c89d3ca0b7fc57a008b32d9fa732239f904c919f3993f29f012d219ee683bf9e820b8f9e499af29e3c6feb9e1b11719e04e86b9df726d99de751349db654639d8acf679d57d1949d4f86ac9ba551609b8f302a9b7186cd9af3cbb99aed284e9ad7f7b499af20c7993f0a3899172f0d98d939b2987315029860223597d04e5497b27ae397ac0d1097a4f441977d7102975d5d9f975bb4f89711f50496f3335c96d86ce2
  | 6, 10 => 0xb89cb980b8836763b7f7f538b7dce78eb7a30225b7842fb5b777b8bab72f59aeb702d21ab6a4cf19b60f3062b5640a2ab46bdf36b4437dbab39a081ab36d65c4b318fc1cb3088cf5b254f826b239bc2cb22bdbebb1aef324b17477aab15a5aecb110dfb9b10e3c9fb0e29bc2b06d5186b068de6cafc9bbddaf988793af616e2baf5e1350af22a231ae9420f6ae653a8dadf83960addf8c5cad64f2d1ad5c986ead0897dcac9ead07ac9841fdac70ae9eac1f1206abed000fabdd680fab8bcb77ab50c5bfaad5a17faa63c7b4aa07d0ffa99c2534a97a0c43a97112e5a8db08d3a88a08cea867d52ba8531185a850eeb5a83cd88ba81e07a4a8148062a7c9ee2b
  | 6, 11 => 0xc9d889a9c97b4c03c96120f6c8e0b569c8d38284c841b061c83f9268c822d2dec77f38fbc74fce60c73fff91c73e5431c6ef296dc6ce6bb3c6b1912dc67def90c63eccd6c60c4a4cc603fb3ac5b7867ec5368674c52c43f5c4f7a12bc4c317e4c4b0bd76c43418f9c42e642ac3c2b85fc3a09f6ec39d4205c3890914c35a3d98c28c44a4c24f89c6c223982ec219efd3c1f8fe15c18b0dadc153d67dc04e0880bfc48248bf9904febf8705ebbf777d50bedf2cdebeb777e1be8da24abe8cb8c5be75d1f4be657855be4be64fbd9ea937bd199d0fbcc6287dbc397160bc0e36a8baecf4e5bac1ef08bab9a1bdba762a6eba1aa2e5b9770643b93f5b72b8afd059
  | 6, 12 => 0xdee74686de41cfb7ddd589c4ddbdf96eddad8f2fdd5bba69dc3f7989dc1f9140dba68411db52af0fdaa96d91da8582f9da6e9c28da40dfa5d9c77036d9af5a0fd9814c0bd94e9fa2d9320379d8980b35d87949a8d83748ead80b7990d7ca6921d7abb4fbd78fc00fd7825539d7783301d71e8632d67d0a21d6455af1d5005540d4d90fa6d4a3e2c7d4413610d4061f74d372f882d35cca1dd343e014d2bc2d14d2a0aeedd282ff82d2580c3dd20a0996d207fa96d1efb8f3d1bcabd4d18249eed1296545cf8745bfcefac579cef63139cef3ff30ce5ba581ce3a6e85cd786ec8cd0d5f86ccd45e46cc1639eacc026abccbdf4e81cb9c6576cb1c4c97cab6f4f1
  | 6, 13 => 0xef46a522eef8ea5aeef3064dee997921ee4e9dc4ee3cb461ee02d3caedbe3076edb06ad3ed467b7aed38ee7feca992adec9eed60ec164c1eebefca4bebb11d4aeb58dd0beb111565eaa735a9ea7bbc22ea5699ade91a925be919e04ae8d9024ce8211766e8001871e7adafabe79f01f3e763fd9fe754ce26e73a9f67e6cd3ac0e6c27151e6751897e5c02157e5a6c51de58a7b3fe558a9d0e539fca5e4a6b616e47813f7e432d3f1e3f397d2e3d47b38e389f5f5e3489894e32a90e7e30f2048e2f6af66e2e36728e276b9c4e2496609e1fd657be1faee85e1d569fbe131b184e0a988d5dff65054dff144ffdf5d199fdf5c9f52df415612df04cf42defb0a41
  | 6, 14 => 0xff98f9d2ff939ceffefe41f4fecd4941fe2a659ffe186c62fdc77755fd4efca1fd4ecf59fd1d4291fcdf97c7fcba46ebfbf44d83fb76c82ffb1c52c4fb07d043fad70c7afac52187fa4cf7cafa03ea34f9c10a12f9a64eb8f97998eef96feb04f8dc0f96f8c7cd80f8c3bf6ff86e66d5f86bc050f85dc413f811ea51f80c1680f801033bf7aa57d7f6b0e670f68e595af656e46ef56ca133f55da781f54769d6f4af0255f49cfee6f4591915f3d6a6a3f37019b2f32b697af3175066f2da6a70f2ba8c79f230e269f20a0dc1f19ec62cf0895967efd562cd
  | 7, 0 => 0x55f0adf0535f29d052aa49505169eb00509fa1f04e553f804df8b0c04bca659049f4c59049d41a4048faf4c048ad07d0479bbe10460888804427d3b03d4cc4103a624c70369e6ec0357f040033a727c0318307a030a418d02e9d44b02d6a72e02c1685702b2728d029f514b029bda2f0294122e028de01e02885a130285087d0249a99b023f5c5b0232af73022ee8080219fdf801eac28901cde88101c90a2501b5ee8d01abdea4019fd767019f361a0191869801866a3601794b5f015fcb3e01551783014ecf680146c416014268c7012a584001189ba90114ca86011182d800f9b8fb00da586b00d5313e009614c3007dbb7a0031a7ea002d875e00296567
  | 7, 1 => 0xaf23e1b0ae653d70abf97180abce8420ab8b2690aad79ad0a7d079a0a3d884a09ee1b6f09d9969709d1727609c0e32809bd51ef0989c7c30941c54b093e73560938c975090dfc840903dbc508e4c69e08df973908d0d2ed08c7c03908c5dc3f08b46af108664b500865d84f0856ca260844bf83083004ee0804e8ba07fab1ba07f70b8707ed8a3207ca96c507a3436a07962ead0790b29f078c6002078179cf0772bb3e074894330725e959071cbf990715437d0711d49e0709752007073daf06fb5c52068bc39d065964650651b5d5064cb8090644c92306350246062e761d060e01a405e9221005c61dd605bbae7e05bb49a605ad2f340590ddec057729b6
  | 7, 2 => 0xf16fff20f115ba20f06017a0ee2d2210ee271f80ee0de320ee057d40ed019dd0eccb92a0ecc23a60ebfb63b0ebee7890ea800b80e9765830e974d5b0e90cf7c0e7e15130e7dd0190e7db3450e67dc250e39d93f0e1f55bb0e05ccb20df435510df1ea5d0dc23f740db9c7830da91e400da6941f0d9cbe430d86001e0d7f85ab0d570f570d52c9a60d49c4170d40e0e10d377cd70d3586890cea20e10ce9b2880cd896110cd88bf40c97cf590c969c940c867e660c825c970c77bbc50c70ad7a0c6f23470c687b0e0c2ad96d0c0cfb940c0bf6ea0b9beb890b985bbe0b8ad6cc0b7f14bf0b5bfccf0b41c7720b2c8ce60b2912830b29023d0b25135a0b2179b2
  | 7, 3 => 0x13e0e2a713e030a013d6d81d13c146b613b5055813ab1ac313aad82f13a8dfe0138cad00133c08ef13346ed1132f4ac71320e8dc1317dd2b12ddb43412bb814412baa67712b8ab4112aabf8d12a8595d1265ef971247bf781233466a12300b7112245a68122261f812140faf120d1dd3120061e011d306b611c1f92a11bd50f411b9e05611b4bd5b11ae78c211981144118eca21118d0e1d11880f961187183a116c6f82115e10321137d80a110f8d8e1106ad5710d89c48109bbfbb104ef361104243571037e7201019bd290fec104b0fc7e3a30fb1a7760f8e38f60f8009980f7ac0e10f77871a0f6a02c20f53334a0f48aa660f3d84400f2c4f190f1c6604
  | 7, 4 => 0x18e3fb0a18c40ebb18ac994f1882b169186c38811862a4c918545dd6183afea7182361ff181c7acd181c0a6c18103f881808214e17e7c6aa17e4d13d17ddd95917d64a9117c5c22e17bcd81e17bba65117b7e34f17b77a5217a712b017a3f1f5178953db1781fd24177b74fc175a929b173643a81729918f172462521708743b1706ecff16e96cfa16deab0b16d21d8816c91dcd16b50ee916b01e5416995adb1695814b1661bbe9165a1433164f38e0164042a2163cc666161648bc16118174160c7aef1606144c15cb6ef015c4f37415b18426158c470e156445b9154b3952153fc09e14db292014cc203914c0d43c1499cfe514466a841415063f13fe9497
  | 7, 5 => 0x1d1165dd1d07cbc61d06d2eb1cfd2fc91cd93b5f1ca81a3a1ca481c01ca0b1831c8e80241c8b50101c32bad41c1ffead1bd1fa481bcc3d7d1bc210541bbaa2fd1b9d622f1b933b9e1b8548e61b8076ce1b7eaebf1b78d4bc1b62a5db1b61a0cd1b55df541b52f3321b3fed3d1b1c36fd1afecaa01ae9b4a21ac819931ac6e6c71ac6cf551aa1953a1a9c7f661a9329761a6a04de1a63a0ea1a4dc7a41a4058c31a39c2a21a33b1c31a13ea6d1a04d9791a04b3101a0286ae19ff9c8019fd5caf19fc1ed919f37e0719e5257c19c7c79119c5957e19b1d44819a917ce198916cb1980bc29197e4e1f19774199196672e11921f28d18f302eb18ef4baf18eed24c
  | 7, 6 => 0x236d9b64233e519822d85c9a22d2ddb122c7351322c4f10a22986b962289ec0b225e9c11223c385a223380ee2225318021eaa96f21e6cbde21dae13221ce372521c636b821a5f968219634db213f9045213dff81213bddeb20df43cc20d5617920be360620bc14c120b7f16d209d2b87208f5f63206bd0132064873a2062e284204a722020292edb1fecb1011fd3c25f1fb72b911fad31dc1fa565611fa432931fa23c8a1f8f063d1f3387171f2ee9851f15ac8f1ed94da01ed55caf1ea4ddda1e95def71e7c63c91e35b7f71e2d04af1e184c7d1e0ecd901e08e1531deba4451de177831daeb8c11d98a19b1d948ff71d85da9b1d81c57f1d7215931d160c6b
  | 7, 7 => 0x2992b9322989cbc02980ce66297c99f8296af49a29428e4b29342757291d2a9e2912a74928e5022c28e3ecc328df87aa28d1b8ee28b1318528a4a83e28a4634428a1dfb0287085f9286658d0285879f1284514cc28222a1a27c1256227c009a4279f070c27795cd1275d8171275d28bc275958f22750b4f62748e4d0273e087b272630b12710b40c2705880d26f168c926eeeb7b26beaf6f26b4fa76265b050526488ebe2639a0bd26396ad4260a164f2609324125d992dc259fb2c9259a31372597a519258a6ea425882208250b3e6a250aba5724f9d1c424dd90d224b5fa3e2467ee6a243971d52416c07e2414ae9a23fdb2ee23e6582623e6546623a4af75
  | 7, 8 => 0x2de6358a2dcb18752dbac35e2dac07892da94f942d98c7d02d9165262d90db782d8de92d2d70ced82d618f3b2d5ab92f2d52d1502d4fca342d4cea722d4518622d3e70562d2f16c62d06d0c22d0132102cfe0cfa2cf085992ce139a22cdf3e6c2cc746d12cbb9f1f2cb7e2692ca072292c86b1b52c7afb6d2c58dac22c42325c2c2937292c18d8712baf6f8f2badab652ba065fa2b87620c2b81626d2b5787d12b27b74c2b26d94b2b25f1c52b2253022b09ceab2afda44c2ad9fd9b2aad75692aa00b9d2a8c3c9c2a8999b02a6cf0712a6bc7352a5617002a4993872a4238582a245e7b2a14d0f729f0b1cd29ed6e3b29e942c429ce843e29b291b72993998d
  | 7, 9 => 0x34064f6c33df688433da662c33d93c6b33b85c4333a2828e339be830337bedf0336a01d233511330334e11ad330a8e35330961a63303cae532f11b9a32bc680832ba82ac32a9a19b32a1bcd53294f0e0326bf53f3264f1943252e2e03241705c3228b4233210954331ffed8331f5eab3318125c63159aba1314b726931470cdc3129ad3f3122199e3115c93030de567830dba21430d5282030959bfe308c42f8306f6ccb306cb522303f34b8302ca777301b2a853016b5f92ffb65112fc5bf282fbf35272fbdf3d12fbbf89b2f8af2362f3c81e32f2d39052f20329b2f1d2f5b2efbd9642ede35262ecd9b512ecaebe82e9987ce2e3b996a2e28d5a52de85b92
  | 7, 10 => 0x388a7a14387c221638422411382f747e382eb67e3821da663808c78237ea8af437d8e1ca37d8b58137a858aa37a858a7379a889137962c633791ff6b377efee6376cce2b3766c8503743a61d371a462236fb367836e2575236de7a8736cd76be36b5383e36b521a23678c0eb3673afdd3669c03b366946d036648703366248523652e1123652c142364691d83609387935f2a55735f0e23f35e7486435d89aaa35bf14c3359f67e7358e7c13358ad894358833f8357db5073579865d35787e2635771853356512d0355e296434d9f43b34d2fbb734a771a73492603134886bc334718ef03466ebee346502b5345154f5344f47aa34487e123434573834171dd8
  | 7, 11 => 0x3f69e5183f1e2b9c3f15457d3f086e6d3ee6de3d3ee052543e791ea93e5766453e49633b3e444aad3e3a3ac43e38dfb93e277fff3de1cf0e3d8b1b8b3d8a3cae3d6d79af3d64e4c33d60158c3d0e52963d0124c93cfaa5163cedcf813cedc83e3ce437ac3cd396533c9addd13c407f353c35f2033bd6ad1d3bcc8c933bc8e96e3bc2c63b3bbe60cd3ba1e58b3b9f7aeb3b7fb1233b5dab7f3b4d023c3b43ce223b40a23f3b34c0e23b05d6f73aace7f43a8e04dd3a8512d93a67daad3a64e63a3a48a4863a2d6c6239e1752a39ddbebc39a3264a39775201396f572d3956e3ad394f1420390ed69f390153ab38ed825b38e1a69e38a2f6f4389cbe3638962217
  | 7, 12 => 0x43eb0c0643db6ae443d6f05343c469ce43ab146a43a9f848439b611c4397d140439406ca43686f9d43555fb0434bdc18434ac032433cb82e432dfd8243110caa4305883643008d1e42ef746f42ecbb3d42e7b5af42b779a3427599744270b5be425ea23c425bc8a4425ac010424d728e4240830842245e244214fad141b8ea3b417fec1d4170bcbe416de72c414d83594132065940fe085a40e3c4e340d32ec340bbc12740846bf6406f21e9405c8f3d4052419f4042c3c84041a8df40419ef2403af74d4028922d3ff4ef3e3fed8a9b3fed881a3feafc213fe000373fd72a663fd62b933fca826d3fb8a6af3fb404613fb101cf3fa66a2d3f8aca813f8398af
  | 7, 13 => 0x49e8ddff49e3bfbd49d9a14a49c3e2a949b6983f498effba4987e828497e1ccf49787d0149780ea84975de444943f32c493c34104939f53049148db0490584c94903ddd948f6d72e48d95d2048b0ac9d48ae22b5485a11cb4827cfeb47f2bd0447ee69e847e43cbf47b76ea347b1a80947a0deee4795ee6d47946ea947703dcb4755b8444727debc471a541a471718c447154d3e46ed067a46df279b46dd85d846cefcc046c932254687df06467646d64667f2b7466764c54632f1c64626019545f9c57745f6b58445abfc78459774c2456daacd4526b40844fe769744ee3ad244cd758b4493ef314458f2e54418c564440fd5ef4408d56744032d5043f50390
  | 7, 14 => 0x4e3a3a904e2ce2974e18a5394df560734de2370b4dd542384dc4f8224db0fe984dace24a4d5b0f8d4d3d159f4d2ff4d14d159afc4d11c68b4cfd734b4cf5a2254ce11a174ce115d74ca859dc4c8a818c4c7d8ce64c7463374c70a3534c58a4c04c46545e4c43d6c54c2eb5784c29021d4c2047c54c1e35cd4c173de94c0122844bf147df4beb8c424bd15be94bb8d2fa4bacc54f4b83bc6a4b77d19c4b6978864b5e75fd4b50406a4b40518f4b2e44754b25a97b4b226b904b222bf34b21fba14b17d9624b0c2c394aee73794acdf8d54ac7dfcf4ab9f0674aab57be4a8291714a77d2104a57ba7f4a4249ab4a25f4994a1660524a0d197449f3d2f349eb0664
  | 7, 15 => 0x53dd4ed053ca920853b2be725395ea5853812058537c0e455377f3e65377c91a536a150753466db8532df2e15318541d531108d6530ec13f52dbe80452d0b5be52ce9ec252a7682352943af55281620b52534f94523dc211520f182951ed228251e93bed51e2c49a51dd55d151bb2a0f51b101cb51608443514aca6d5124950151099cc650dc89c550b00f9a509f5416508708d350754638507207e4506b190f5069bcbd50490acd500139404fff2dd54fcc8ff24fa260824f9d2f8d4f99f6424f7141a24f49dd644f46dbe14f0eed5e4f0d6f114f0494734ef7acb24ed5e3f64ebf453b4ea817a54ea26bcf4e9a87094e7855394e6d95844e6d16534e3b6861
  | 7, 16 => 0x5996f4f559952f0b59907843597bfa89593cbb0a593c2d6b5936765a5931d5e8592f01985916f56258f47f0f58eb4e3858d7b5fd58a9df50588269ee58817b3f5875705b5838ecf2581fb8f6581a3e365817addf5810d46d5795fc8d5794fb70578e67bf578d26c0576d4781575675b3574ab38e5727b7f4571462ac5707fb6756e6f7eb56d32b8f56c5d00a56a942945693fbe5568d8c7e567ee6cd567c7f5156403068562fa21b5618ad155612b12055f2ea45557cb75455067f9c54fdc76d54fd3cee54f251df54e7b9da54de0ffe54c1de1054b88b5354b5735e54b47b9854acafc4548e6dd85467b4c6544bdb3154324e155416d04b53ec72ba53e18f1b
  | 7, 17 => 0x5edef5275edbff035ecd913b5ec2fe405eaf95c95e95b4465e82f8175e7cab7d5e56e6485e5492d85e394d3c5e2a7c045e13ada65dfe16575debf6475deb71af5ddab89c5dcdee225db7bfac5d8c46d45d8bf1475d87fd325d7d6e2d5d71535d5d6dd96d5d48a8d45d1e66bc5d0eae245d063e105cde0cce5c9fbd605c929b395c91de815c82d1285c7a05f25c79bb025c5fae8d5c5858275c3b8dfc5c33c1815c1f443a5c0bbbc75bccb9a15bb226b25b98587d5b4dbe2c5b4bee605b3eec9d5b34bf745b023f875aecd9575ae1ffbf5ac679ad5aadae925aa52f8d5a97dc395a97a4eb5a9469955a77071659fcbebe59e5b39359c84b7059aeef8f59a0c2fc
  | 7, 18 => 0x642e54a06423aefe641cb567641ca4e7640f62e363fb6a7f63e50b47637c7ea663720e7a6332600f6330b2ce6320cbf7631fb15362dfa08f62c7c6f462a39a81629689a2628e144f62735d4f627050f9626f737f62623a35621d1ce66202e0dd61fe39a261f63a0061f5a73b61f427ee61ca400861b8723761aa336861a45f8b61874d90617d3f4b617d206761381f976119d7e1610c35a8610913c86108511860e8d6d560ad45a2607f1ebe60690103605eb047604fd85a6049964d604693fd601d48af6008d5905ffbf7845fee1a255fc559925fbac6fd5fa8e5035fa001255f942b505f6139d15f4d90645f492eb65f26c7b65f20e9805ef492105ef0b1fa
  | 7, 19 => 0x69b08c9069ac57256969e1b6694fc71e6933ccb2692183276909578d68fc772168fa0825689e6745689b990368935998684a9053683ca0f9682efe61682ec21a682a009568201ef1680cb64d680bbea968090f896805cfb767eb4a3067891a306786b84767852479677d84d8676198836733c99a67240676671ea51e671d423867133b2966fc748866fb4c9166e9390a66e5ae6b66c9726066b2ba9b66a804cd669e5573667f2e9a66730cef663dd11466314d2e6625b9e96617db0a660f2a8665e88a3d65d6d88f6566e4ba65542827654dfbc065381a026532bf64650bdfd764ea33b664b23f0e64b153c164aa6b4464a0c73f64789948646b28aa643ac406
  | 7, 20 => 0x6de93f766dd08b0e6dcc76296db8095f6db7a3286dab2ce86da2ccf46d9729bf6d916c166d7e78d66d76e7956d483b2f6d4717016d326bf66d31fd9d6d2cc71f6d1b608b6d1675326d055eef6d04d5956d04869a6cf4f29e6cd622c66ccc398e6cc11e926cb5b4df6c96b4706c8c37936c80921c6c79ed6a6c66f60c6c64553c6c4b6e046c41d5016c3e88df6bf899566bf58d8b6be5d2566bd3e8686bd20d4e6bcf90f36bcb63fb6bba30316b715d986b67104f6b3934176b1be3666b0d63fc6b0959bc6afc1fc26ae5c9b86ac5c8b56abcdfc56aa508c56a95be0b6a91b37d6a4320db6a41599e6a2a46cf6a13aebb6a08bb056a00c0a569da0c1f69c0add4
  | 7, 21 => 0x7300cad672b283397288949c7281f925727f14f372739f54724693b772464c217236e26572301b0f721cd83371e12dcc71d3d74b71c52b6a71c48435718d4b85718aa31d717f4ee0716be5777158096d71288197710997a570fe4ee070f943ac70eea42e70e34a0670bb677e70a579f870607efa705b5d9f703b0e08701d07ab70120e997005f123700050ab6ff70bd36fe18fc46fb3739e6faba2b06f6f7e696f6a8dfb6f43e1be6f3a9e9a6f1a2e9b6f13e0ff6f0f44366ee8713b6ecfcc7c6ec911ee6ec7a3626ebaa7026eaec77d6ea3e37a6e9ef1636e81dc4c6e73e5206e7147e16e6fcff76e6a31206e4e17c76e16b7eb6e04f5ec6e01e9f06df7e42c
  | 7, 22 => 0x77d135d077ae3ab0779c985d777d8546777652a7776847947746c8397744f9e77731b80f77231e6a771f39f876fcecf676f0de3376f096c376e1a5f076df94a676d07db476c6508b76b871ac76a139dd769e1cc876607b8d765bdd3276549099764e5f61763744917626fba5761a42bc7613d46a7605ae21756ef7e975576ffc7554e38675516084753f33837539d26975364d1d75249840752306507508aada74fe289274d57dbf74d0803174ae2b347485a1e974789e64746a0e0a744813417408724473fa28f273f993ba73e2848473da4b1a73bcfd3f73a48879739a99807394bd34736647aa734eaa0d73437dc2734049fb733d888d730cc97a7309ea2f
  | 7, 23 => 0x7c88cd607c7fcf387c79c7f27c69c65e7c60a6ce7c4c7c107c4bfba17c4260817c2f60d67c1abb197c170b2e7c1140187c08287b7bf841387bf7fc3e7bf0d3337b9474917b86605a7b665f577b4332737b2b17a17b1b71df7b16ea687aface357ae6a9707accf5cb7aaf2d897aa157477a9933267a7f40357a7a23a87a644d067a5b787a7a260a2f7a11764d7a00aa8b79e5550479d3e13a79cce61979c219c979bb6d1e79a30aba79952bdb79737713797234ad796fc1e1796deb3979684f627961f7277911f99d78e9916b78e4358b78bbf39778bb1eaa78b54ae278a666597893519d7892577578768cc37872d0267819d385781289727800865577e0dac7
  | 7, 24 => 0x817be6a2814d04b78123ee888101e0aa80b3c20480b2da9b80b2a53b80aa07e380920950808226668069eaef806266ad804281918034d29c8032d7667fe1a60d7fdec0a27fac73bc7f8ef2d87f8c014d7f86a8967f82bf8b7f75ea277f75d2d77f65878f7f6323277f5f0e0b7f54e5c77f4f5e1f7f4af1e47f4590c97f2c02b87f2587b17f172bf77f0df4cc7f0507a47f01445f7efde3047eeb3f2f7eddc2a37edbceae7ed513f37ecd8d627ebbf6017eadd0e57ea020fc7e22428f7e1a8a567dfd47397dfb85ac7df703d67dc594b27dc3639f7db173387d7d57bc7d5fc8b57d566ba87d44009e7d420fc87d303bbe7d2e7cf97cea112d7cb1fb967ca8786f
  | 7, 25 => 0x871ec9f887062e308703169686fe088a86e09f0686bbbf6886bad95e869b759486981ab6868f8bfa868ceed7868cb4248681b5e9867726a1867254828672012f866977d4865e272f865cbae886465a8a863f7c59861a00e9860c78ef85f6241e85f1f72685dafb7a85c3b14985c39cf285a623a0858e52b8857f1b668542769184e9742a84d4bec084c93e8b84b247538486022884594c5e8450d9fa842f3b0e8422cac983fe99eb83e4146483d093ae83c7f1fb83aaf517838341f48380407183621177833df9038323a63b82e0b6ab82d3eb9982c92c1882c4fa7082a1ab69829ec1d68295aa1e828511a4827963fa8276397282585f94821853fe81bd8a2f
  | 7, 26 => 0x8b27f4e18b1fd6d78b1a453a8b080e6a8afbf1a48adfa09e8ac24ab88aa701598aa44b2d8aa3b04f8a81f0ca8a7994f88a59424c8a553e488a516cc38a4dce858a4b88898a46621b8a2ec80d8a1fecb889fab42489efee9189ecd54589d9702089ba9fdf89b9a4c589b52b5089acfcb189a3f71c8983c1878974814d893fe42c89312aef88f823fd88f300e188ede02888e50a9488e0387f88d9be1688ceb15588cd013b88a938b6888f7ea488416ce5884052b7882e82c9882be4e1881f30c0881af3898816e94987fff5c087ec230287e75edb87e088dd87de9c8a87ba84e887b12daa87a5f8ba878be23f8786f1f7877779c38752d38b872d9429872c006d
  | 7, 27 => 0x909d23ce9066fa269061f6a59049058a90416138902a64c690104b5a90061e318fc473788fc42d338fb5d0938fa972eb8f9d1d5f8f980bea8f80fc978f7b76b18f78512d8f76ecae8f74f0a98f6e24048f6057d08f5f73c98f5f11de8f4062dd8f1f96978ee425888ee20b498ed973b68ec635f58ec3721a8e92684e8e7679718e63fa418e52fbf68e3f5deb8e2302ba8e1426838e0cfa578dc4f0798dbe23998d869bbd8d5eaaf98d5a65f78d3157b68d2f53818cfeab508cd916648cd766ed8caed4eb8ca14df68c8a824c8c76bee98c66e23c8c51c7138c4a4e318c3998428c353f988bf68fee8bc68b508b9764df8b8fda438b74ea068b4da15b8b31c58e
  | 7, 28 => 0x96424b41963e51e196255115961ed463960d324a960a5d0495ddc41b95d27d40959b0bcb9595a4cf956d10289566b56d954bc9dd954b64c194e56e8494de200194d4832a94d3851794c7ea7294b8834e94ae151694aba5ca94a609ff949f308d947fb432947da14a944ede0094302b6c942a4f2094062d519402840893f91dd793f42b8d93c2bae393b396f9939a9e6193965cc293602c46931be89e92d5a09492beb26492bdfe3b92bb0e5892b8eaa092aa991692904ad8928e17b2927d83849272b1cc921c7d4491f7c8fb91a73dfd9190d39c918c7c03918bb4fb9147ad6a913d8ae5912821e49117715e9102d10890f610e690c7888690c0894f90b87dbd
  | 7, 29 => 0x9b1dd7b09b0c849e9b0b079d9aec1f2b9ae5da449ab4c0929aabbbef9a92230d9a88f9d89a7a06c29a6ab1be9a1f18269a18a8839a0d459599f80ac699ef520099ed5e8799e3b42599be6db899a181bf999971879998b674998cf53c998cea0d9985a136997374ef994b9d089933b443992721c299265abf990f6ebb98ff0c1898e9771598e2892c98de873598bfc76298a19efa9848d5ba98468f5c98411d81982e64fb9823da6497e71c9697e2d59297d874bc97d8066397ce2acb97a75f8e97a53cfb97a4a4a197a3eae797a00225979c56d897885ff997752692975a043b9756cee9975460df9736bddf9710a45896f60d79969645529661aced964c30c0
  | 7, 30 => 0x9ff394c19fce48649fc0bc2f9f9ea33e9f8732b19f7986cc9f69f2ff9f6868319f6676b19f5ea4e59f4a44a19f307a4a9f281e6a9f22e88e9f1c706f9f0c76639eda496a9ed6de7b9eca50df9ec9ae489ebfb44d9e93ebe99e91ae509e5fc6b79e5f4b7a9e5adc459e4b2ef19e418da49e1860da9e1370af9e0362479debfd949dbc54029db823729daae7359da9d51f9d9a91c89d72dd149d45ceeb9d42c3eb9d0960989d0504429cfa7ec49ce7c5ba9cd4fd939cbb54e09caba4cf9c9ccc9d9c9a324b9c8d8e2a9c86b7d99c6826aa9c625b659c0b11509bd78ad69bca9a899bbf435b9bbebdb69b9060219b6cf8b59b6512559b5bed5b9b56a6c89b34b121
  | 7, 31 => 0xa499e38aa494c22fa466259aa434b4b6a40b50aca4093031a3f2ed10a3f2435da3eb5964a3d373cba3c1ab4ba3ad5187a390017ea38922d9a3697d85a362549ba352c6cfa34d458fa34b2fb8a34731dba33952fca32cb193a319940ca2efe0c0a2a97873a29245d0a26ac20ea26534afa256c1a0a2501c7ba2487bd3a2377ba9a22b6a16a212b62da20ecd8ca20e77f5a1f9723ea1f783b5a1f2e5c7a1f0ea91a1d7c0d5a182c893a1807b91a170cb80a1662bafa13f99cfa0d05094a0c59c23a0ab1187a0aab22aa09db9cca09b5bdda099d7c2a088b577a08609cca07b3991a0566735a049bbb5a034aed1a02ef21ba0219339a0178350a010db98a00b64c3
  | 7, 32 => 0xaaa935daaa99e01daa8df529aa8b3282aa732844aa2cb15caa07d0ffaa00aaa3a9f3d131a9ebdc13a9b30c36a99ee458a97aa236a9789813a9679bafa9647ee6a909e4c1a8f6772ea8e78fc4a8e24e8ca8d6fed1a8cb32a4a8b61457a8b24ba4a8a73885a89eb231a884f245a85da819a851a7e3a840633ca828f69ba8249059a81c3a5aa7fbc882a7f526c6a7c9a009a7c19259a7b45be4a7966e15a786503aa732a1a6a69d5214a685bbbaa661d0dfa65dd945a65c3616a61bfe94a5ed4e39a5ed1e7ba5cf7206a5b66d6ea5b438dfa5b36a13a592a0a9a57519cca56effffa52c7e6ba528621ea5268c5fa4ef705ca4eede4aa4c7accca4c4fe3ba4ae7b11
  | 7, 33 => 0xafe2c7a5afd5f4c9afd4ec35afcd53fcaf8f26f6af79b774af76925faf75ff26af647c31af3465dfaf0ce506aef5af7aaedf1679aed6ebcfaec7458daebe772fae82ff77ae75712bae61e220ae1e846dae18ff3dae119917ae110966ae064aa9ae018b7aadf352c3adeaf2e8ade4afffadbaafa4adab993dad9c65faad9683faad783fe6ad6104f6ad4120a3ad3bbe89ad1391a5ace974c5acba04cfacac34b6aca9b064aca06ab9ac9a2774ac829a92ac7b9e87ac5fd9fdac41a9b3abdd680fabdc18a3abd053b4abc6268baba64548ab9f69a8ab89854eab79c6cbab5f845dab583dfdab55c58dab555734ab227451ab213bb8ab12b296aafef900aae6feaf
  | 7, 34 => 0xb4c2adf4b4b838bfb4b7aa29b4abe74eb4a1ec86b47be621b45bea12b44008a2b43f5990b432738eb4309820b41b0a9db3e7728fb3bf8a8eb3b09514b37c045eb379f728b36e8d29b36df0c6b33f471fb325de37b322ff62b31e2f22b30843b8b2fd0e45b2e2d36fb2d74cacb2d40c22b2a6c045b28d5826b285abbdb27cccb0b27690e8b272d876b23ecad5b22053d7b21e5031b2118fd6b1ff7463b1f94ce0b1ce22c6b1b8bb56b14c7d40b124246db0e1dcffb0dfdfceb0de38b8b0c3750eb0a1ca65b09debbbb08e74bcb07fb45bb077cf95b074fd4cb06a21d7b06379a0b062d898b0377981b031a5c8b028f5a0b0231954b01a1d6eb017831caff20c80
  | 7, 35 => 0xb9e29b05b9d0b111b9c6a5e9b9c577d5b9c08083b99861f2b97b0eeab95f4ed5b95b557bb94d1047b94719e8b9349dd0b92956c4b9218214b90b816bb8f9e3e0b8c9f8fbb8a185a6b89c56bbb886585eb87cae82b868040bb85c2f59b84d5911b8405c07b81d78f4b810844bb7f92244b7ef6c85b7b92ec7b7ae1533b7a9ba99b79ef288b793d28db7892a55b75d88c1b75432adb751909cb72f93ffb72628a3b7186549b71329c5b6f964b2b6dcaf1eb6c50266b691c424b6855c3db67647cbb66f714eb66e795fb666254db63ee375b62fb8d8b6251136b60f96a1b601f9d2b5bed785b59006feb57d39f3b55f3ecfb55daf2bb55511a6b5546fedb50f2cb0
  | 7, 36 => 0xbefa2055beea5a39bec4f692bec33186bec0a575bea336b7be907f01be70a23bbe51e5eebe4be64fbe4769d9be3add0dbe2639d5be18d688be110a0dbe0ade22bdeb6445bde1cfb5bddd5bacbdc9682bbdb42f56bd7b6565bd6a8f7fbd41015bbd386403bd376e02bd2fc437bd2fb554bd209ae2bd1c3529bcfc0514bccd4b3fbcb7912bbc87e6edbc7e8f37bc591900bc545819bc544fa2bc50101bbc398ae1bc2c003fbc28c4e9bc1a5d6dbc19ed6dbc042ef7bbe34f76bbcf1011bbcc115cbba70ebcbb80d0edbb779f5abb75fc4ebb727797bb5ca883bae9d770bad4da24ba7d336aba779f70ba558546ba460977ba45dd7fba231cbbb9e4f0ccb9e4c7c8
  | 7, 37 => 0xc3ba5c8dc3b4db41c3aeb668c3ad2618c398766ec395a7f7c391afb2c3848ffbc337f1aac3347db3c31b6fd9c3117bbbc310f424c30e22efc2f91008c2ed32f6c2dde247c2c56a8ec2bcb42dc2932210c28877b3c27c2edfc278c27bc25c674ac23c0a35c237d00fc228c216c22701b7c2138c1cc1eeb825c1ebf1e0c1dbd993c1d94010c19d30e4c1947749c1907b16c17173dcc13e825dc12d8925c1041042c0d8bcdac0b02379c088ed64c0705a57c05fc100c05eefcec0586e8fc0342f00c031db64c01695c8c00da4a7bfda4f41bfd1f35bbfb7ee36bfb0cba3bf9179cbbf8705ebbf6247b9bf58e8f0bf4172fabf39cbf0bf25a648bf01fb40beffe354
  | 7, 38 => 0xc88fa312c85e0905c82cddd4c7fb6ba2c7ed3172c7ec7312c7d9cf9cc7d22c68c7bda704c7b65101c7ac8334c77014e1c75da4c0c756f41ec731841fc730d938c71007f0c70b1e59c6d2c7e1c6bc9380c6b11a16c6a95673c6912187c66d8871c667cc40c63e6ab8c637c9f1c60d321bc6068286c5ff83fec5d3e588c5b1003bc599e51bc595198ec5899ec0c58038e5c576ef75c5736c6ac572feb0c54fca04c54b438ac548e825c52f7576c510d9fac4f9eddfc4f7a12bc4ef24d3c4e09fabc4b48854c4a50f80c4a4bbb4c4949487c46ebe18c46ac8f7c465a5dcc462ab86c453a13bc416706bc407b8a3c3e2d77bc3e02969c3d7b039c3d681efc3c26a3d
  | 7, 39 => 0xcd59af77cd41c6a2cd3bc669ccf052c5ccc35adbccbe85adccbc3f42cc6e339fcc6ac460cc639849cc5ce581cc513b19cc396419cc260ed1cc1a159bcc147145cbedcfe9cbd77c2fcbd5b4f2cbcebefdcbb8063dcba4f72bcb8dd51ccb7281a8cb711f61cb6c5600cb67cfd6cb5221cfcb51ce3acb46a5f8cb34f701cb2f7209cb20c46ecae6a019cad25745caca82d9caa6b7f9ca7e11e2ca5d1f3fca2ab66fca19e985ca0e29ffca0c0aa6c9f99698c9db9549c9c359b5c9be5be9c9a019fdc9978f7dc996b3b6c98dd445c97fa584c96f57afc9447f4ac937b716c90a6c4ac908aec5c904d60fc8fa8ac4c8e779a6c8df6e8fc8dc7b70c8d8951dc8a7967d
  | 7, 40 => 0xd2849381d282ff82d282c284d27af234d277a55ad26e2c13d26dffcbd23dc786d2370a95d231461dd20d1552d1ffa714d1f2c56dd1efb8f3d1d6acffd1c3e382d191abc0d173caa4d1375c51d1145570d0e05608d0dd3a20d0cb81bbd0afe803d0ad1508d07c39efd07aaddad028b587d027ba97d0188098d010ef66d00c244bcfec020dcfdc665acfc00382cfaaeb5dcf9551ebcf7d9acacf527d16cf446c2dcf33b5c0cf26ac8fcf25c9ebcf1f3ed4cf1e8bb0cf0b78d5cf0b0317cf0a0fabcf010deccefdaf14cedb421eceafa34ace81f3a6ce597d4cce40adbdce3dbbbece3a426ace1f1d8dce1436abcdf98342cde202f0cdd6b28fcdd2d617cd6ae6eb
  | 7, 41 => 0xd832781cd81cd785d8198d9fd803eed7d7e2f6add7c43538d7a5749ed7a472f4d79dcf25d786c099d7799b21d7492ad9d740303ad7322c12d72da707d70862e2d701e0ccd6adc8bdd6acef47d6a5bda7d68b73c0d67aeb44d670e039d619fd3dd615987fd6073c10d5ce88c2d5bfd6fdd5ab9fc9d5a0d46dd58ce416d5877e98d5583fe0d52fb620d52b0a13d520c64ed4bc2908d47b26a0d47790a3d47578b6d46c70aad445852fd438da3ed41d6596d4077324d4001a12d3fa20bfd3f10f9fd3a84f1fd3980975d390a498d383a931d372f882d35f8c6fd34d4128d34a65d0d2e063b0d2d46463d2cc6b2ad2c6073ad2b5723cd2b422bed29df2f9d295064f
  | 7, 42 => 0xdd420304dd1abbaedd0995b1dd040b83dcfabaabdcf90b68dccf1ccddcc1922bdc9f55a6dc8a5345dc4d3caedc44c054dc35b29bdbe6b227dbd26c4fdbd11a6cdbc7af05db8893fbdb84b914db56751ddb4f7d39db3a90b6db3a67f6db2fff8ddb29872fdb23cb92db01ce84dae9e1fadae0a906dac26754daa10b17da7890dfda650bedda60bae0da504eebda5018b2da4ab022da411fa3da3ac1adda26b2c9da02da95d9c59a29d9c2325fd9bee8b0d9ad9916d9840b17d97fc822d9680625d96359b3d9459020d931e8a7d9288e6bd90a4927d906f914d8c89669d8c3f1bfd8b0bc51d8960f8bd88d7dfad87f9952d85d0165d85aabdfd84ccd00d834e651
  | 7, 43 => 0xe28cec1ae259762ee2433ca3e232c2d0e230c8c7e21fca1de21681bae1ccafbce1b8e7c4e1b6be3ee152e27ee1482590e1283faae11df5f6e1151f08e10a457be0f77e7be0f3695fe0e3b973e0d18bdae0b9173ae095f543e07b344ee05cd451e02ccb21e02caf5ee026649fdff7db62dfdba1afdfd44c62dfcc093ddfb031ebdf9d82a0df91a28ddf75e0f9df7206c2df66edf2df50f4a6df397890df204264dee29a6adede789bdec9dac1dec49712debf7146deb3b729de9d2c44de7f46b1de74f913de622395de4eb049de41358fde36dd88de361975de1fa90ddddb30c3ddd589c4ddbf0999ddb7dd18dd9eb6bddd93fd71dd8ed5d6dd53a98ddd4db3aa
  | 7, 44 => 0xe729414be7283c3de6d0b57ee6a36757e6971501e69515eae66050c7e6548bb9e6118099e60c839ae606f433e5e72a27e5e2bbe9e5e14f13e5dbe277e5d68d5ae5d45f7de5cc13a1e5cb74e9e5c2ba49e5c21b2ce5b7261de5b44ac5e5786fb8e56c6f69e56ae1b2e55c4d4fe54b61f5e54af070e5499e93e5179d48e506db91e501ca94e4f3f667e4c3cb35e4aa967ae49d4a8fe491a641e46b0a58e4625a30e43a6889e41e5447e3fab025e3ef42d0e3d420a8e3cc7821e3c6ad28e3ae621ae3a70da7e3a5ddcee38241c1e35df4cfe33cbff7e32177e1e3212e0be31a7a5ae30e0cd1e2f02cffe2ee6b60e2e5bc00e2d732e2e29e9f1de298b8f8e28f5f02
  | 7, 45 => 0xebc28ee5ebbcb677ebb0b335eba5c6a6eba28b6aeb9c6eb4eb94b67beb813fa8eb3c36aaeb2b9f5deb121e74eb03cd4beafba6c3eabec0cdeabd810beab31e8aea99b7d8ea81aee3ea6cc730ea643d52ea63c2d5ea5b7527ea58eba1ea39f55dea378291ea35abe9e9f83c15e9cf7cc3e9bbe516e9ab449de97bba2fe96ff558e96fe5a4e96aff58e964ad1ae9644731e93d2869e93a90d6e902d71ae8e680b2e8e376bce8ba254ae8a543c6e8796d32e878be20e875f0c4e8529c71e8372b18e81b836ce7ff3ec4e7f96942e7eb888ae7e9c17be7e6faa8e7c700b7e7b0d071e7a75556e7978a5be786527ae76f56cee76202ffe73f702ce73672d5e72bf883
  | 7, 46 => 0xeff06597efdd5beeefd4f348efaf60deef885172ef5b4d9fef321432ef265975ef21becbef0b0942eef3064deed743b2eed63fa9eed16d21eecf8408eebe9aeaeeb4af79ee8f06c5ee8dd083ee5bfb02ee4f0bb0ee1e2c58ee02495bedfb3d90edfa1c5eeddc92d2edbcadb6edb71183edb06ad3ed90fd8fed7d44f8ed7abd14ed5ae6a4ed56b179ed478fe8ed302685ed2ae9e7ed243597ed143cc0ece6cd05ecd93a30eccef605ecc12505ecbba0bdecb47af8ecb4322beca5df3cec8449e5ec6b46deec503c81ec497f1dec39cb86ec362226ec338729ec2b22aaec297df4ec164c1eec0c1396ec06b14dec04ee7febf03b1eebd9c278ebd7fcb0ebca1dd1
  | 7, 47 => 0xf462ddedf44d45f4f404136df3f152c6f3e2aa94f3b0d898f3a1e699f390e940f38cf389f381f6adf34d8d5cf3487822f334359ff33384e5f323a335f31ff462f31deba9f318916ef30e72ccf30d3746f2f9478bf2f3ae00f2d35972f2b97b7df2a6d50af2a62c7df29edce5f2976373f2854adff26d9b06f265e2cdf263a04ff249a559f220f913f20f2a2ef2000644f1e7c371f1d45c2af1c9ec54f1c8b033f1c6f18ff1c51099f19a7985f17a65ebf171c893f1510a14f140df91f13c5a6af13569a4f12c673ef1027f58f0f8df95f0c52c6af0a96dc2f09dd260f0577b70f0556ec8f053c1fdf03d9387f02a6079f01ca677f0158209f0010e1beff3c368
  | 7, 48 => 0xf9b99d75f9b835b8f9b17da6f9afb2a4f96feb04f96ea5d4f9414bd9f9050bc6f8eb2a3df8e8bc33f8c7e701f8c59d50f8bf6874f8ba5c5ff8b72109f89a03eff886c565f87511f0f867a20ff84fd4fbf82f3da8f808cdccf80299a1f7fc1ceff7efd299f7e68aa8f7db9c7ff7d6a695f7cb8231f7a45692f77bde39f77446d5f767a578f755edc8f743fdf9f7424647f72a0023f71746d7f68b5da2f6875a6cf683528bf666a70df6535463f650f9aaf6338be1f6281cb5f61da697f5e5decaf5c486c0f5c3fe68f5b7b2e4f5ab4c3ff59108abf58f108cf58d3b0df5664f27f52ab2dbf5277aadf50a354cf4fad81af4f9312af49f240af49b46c7f469637d
  | 7, 49 => 0xff4c58d9ff3e3073ff231777ff03a3d4fef9de42fed1b51bfecffd16fec4ed6ffeb8db38fe938ec3fe919d83fe88ed5bfe84086cfe811e1cfe632f60fe3abca4fe2b8d04fdf6b6b9fdd6902afdbf008bfdb4d362fd904c97fd804a56fd7e81a8fd634e2cfd4ce9b4fd1e6eeafd174984fcfeb677fcf27d52fcf048affc82fc20fc807a7ffc78f6f8fc6afe7dfc65f621fc4a1fedfc1a4b00fc0c146cfbf0a596fbefb591fbec0709fbe1c5f5fbccf7fafb89f1edfb779ff9fb4036c7fb314dddfb19fc8afb195303fb192d73fb07d043fb03a34bfaec6079faea169efaea070ffac274d4fab495f5faa1c779fa4ce404fa0234daf9f0eb0ef9efe375f9daeab0
  | 7, 50 => 0xfffb2919ffecddf1ffde5bbbffcceadcffc6e326ffb70c06ffa13466ff9fd7dbff98826cff91be5cff77da54ff6dda91ff63e5f3ff55b127
  | 8, 0 => 0x181aa94117d7cb9517d07b001729918f16e8db1816b50ee91606144c15f022ce1561a43a141a4f1c1415063f14121a0c13b5da6d135211a21317dd2b12b8ab4112b8884a12ae5da3129997eb12798028124e263511eb7ccf11d7480611761aa81142fa411134c9340fc22fb60e8414b20dfb96ef0db675560d9cbe430d61f2fb0d4d98860cf91d9f0cea20e10cc7aa850bb2ffb10b41c7720ab7b9ae09ee1b6f08aedd4607bd347d07af559e06ecbabd06b07a0306556796065223ce05ad2f34059e8b1705169eb003e3645403601271033a727c02d5abde0296f5790291d00a024a740d023c952e01a603fb0129b7550086a50c00649915002734790008238d
  | 8, 1 => 0x2a7c85282a6cf0712a6bdfc02a5175e429f1177429e942c42964176b292df8a1291abe562882e2b2284db2db2774c46026e36c2426d2458e26a4b5bf26396ad4262d41fb25bece64258a6ea42509c4b824cb7b2924a7e76c2429651523fe6fae23afce9223a7fde622daf26b225c733221f6124621a5f96821698b1520df43cc2081cc61204aaf2d203e530f203cd04e1f608b651f3d31db1ebb13731eb3facb1e8eec381e739d441e7359ed1e3d0e221e08e1531d81c57f1d73f5661c1ffead1bea35011be841c11bde45011b61a0cd1b52f3321b325a461a45ab1d1a4058c31a2bfa9c1a0ece701a0dc40d19f08aad19b1d4481900f42918e3fb0a183e8305
  | 8, 2 => 0x3d0124c93cedcf813c9f3cdf3c9dc2fe3c9d75a23c3d49423c39fd5e3bf3e2703bd0b7833b5624293b23954e3acd3e823a8b9b213a8b1a653a861c993a67daad3a4766343a305add396f572d3950034038ad846e3899ed18375fd1e83732d33a36e4026d36c744ae36ad51603678c0eb363c57f436224d1b35d89aaa359aee6d358e7c13357bcd573518dab134cf795334746a9f34744a7f33d93c6b330961a63294bf403264f194317141fd3150ae1431381b073129ad3f3055c0a6302a0a262fc976f62fa1c82a2f7655c82efbd9642eedfa852ee51d392edbd6b52ea0b9112e9e70832daad2e42da80a642d6df75a2d014b912cf3c0ef2cf085992ba0a43a
  | 8, 3 => 0x4e1db72a4e0e9fc94e00c0ea4de27c5e4dd111674dc27b5b4d17706a4d0476064cfd734b4cd8ba054ca60af44c5cc68f4c1e35cd4c173de94bff26be4bf147df4bb13b214b7591cb4b40518f4b180f9b4b02825d4aee73794ac0774d4a670715499cfa0a499b08ca49148db048fa38cc48f889f8484e6acf475141bb472e33c146e1bded4609964845f6b58445c07cca457c5ed144d9dfff43b425714365b3a9434ac032433f660a4309ffd84305883642b779a342815d8a4223bdb941d9fb7841d622d341a8390641a4b5d640db2d8b40d0012440455b7a3f49363a3ee6de3d3e9c5ebb3e277fff3e1c8eb63dff89d03dc32c533d8620523d6d0b963d18fbc9
  | 8, 4 => 0x5e22a7545e06e6065debf6475dc82fa15d93d62e5d7bf2db5d3a46645cde0cce5ca9ea895c91de815c0095e65bff541c5b2acd595b0171135a73054d5a437adf59e9c31b59d66aa059d395c7596bf2065923c1c658a5f177584e132a5837177e581fb8f65806ebe256fffaeb567ee6cd5640306856240dff55df5df855bb43f755ab6c46558b875054ed1c755342fdb7531915d153169294530ec13f52e996fb52de426a52acbe7d528ca242520a3fab51efbb6051e81d5151d2062b51bf3f2b51bb2a0f51ab7a23516924ff51007c3a50c4b4ed50a706e85059633d4fb2394c4f9b055d4f943bc44f8c57c24f717d1d4f624ff44ec05ebd4e79bd534e732732
  | 8, 5 => 0x706753917005f1236fa6c90d6f6c29a26ebe77696eba99336e9f1e276e834bca6e38e6f66e1ad9ba6db8095f6d483b2f6cd622c66bed6d236be1bd3a6bcf90f36bcb63fb6b89f08a6b7c11ab6b58c0516b46b4d16b1be3666aa2ab606a7ff6686a5eea176a510b386a4fc62d6a2a46cf6a0139de69f5d2f969b2eaed69b07ce3692e70ee6920920f68b561d0689e6745683fb3fc67f1c0d366fb4c91668c4770651506a464ffcc4e64cf00c564789948645092fc640159026379a67663669d95633af0116336351163353df463275f156292bf226284e0436240ab8761f427ee6129ea2960c016456001a2b65fbac6fd5f2a63495eebace45edafec85ec2fe40
  | 8, 6 => 0x8380407183233d80830766bf82dbd05f82d3eb99828511a482739f207fe35f827fc0036d7fbd20fa7f97da8d7f5f0e0b7f4590c97f27d8097f1797dc7ebbf6017e8559377dfd47397dd5c4a57db1e1917d776c2f7d356db97d33ff317d303bbe7cd372a07c0721267bc86ac17ac854af7ab597257ab2c9087aa157477a85129f79c9043d79a4d76c798a90b2794717d67946d3e3791d9b417913045378f04d3478925775785a178978493a7f781054e37733bc5377211a3f76fcab1e76bdf4b9766385db764e5f6175a74bbc7540089874f2245d73f60c3a73a1eeb772b283397290cad5727daf3d72739f547260e48f721cd83371be65bd710f96de70cdf074
  | 8, 7 => 0x934043b8929a9c84928df7689272b1cc926d751e925c0be491b98d1291426eab91015b8b9074f28c906d26119037c66b9011f5828f9d1d5f8f7fd14d8f6680978f46f2108eb06ba68e7679718e4941358e35cdb08e2374cd8e0d834f8dce939b8d7f04bb8d6fdaea8d1e3ac28ce77a638c8386ea8c1a6ee88bedc1998bc68b508bbc73f08b8fda438b308e208aef68758ab84b5d8a8bfac78a7994f88a18c2888a0d10dd89beef4c897643b689605ac2886bb2a587ec230287ca80ca877c8a9f877910e2872610b887080352868cb4248651842c8635a6fc85f48e9f85520fcd85210b03851cbe16850f030e8492c7cd83f048fb83c5bc52838341f483833bd7
  | 8, 8 => 0xaa3f12b1aa21bb6da9cb11c2a98c5b5da9647ee6a95dfcd0a909e4c1a8d9852aa80d4bfda77ce252a71939e5a70b5b06a6563cc3a5103ec2a4dede88a499e38aa35f8a0fa309310ca302d5f5a2d855f3a1f16defa0c045e2a0b26703a07b39919ffd08839eab30d29de9f1209d42bc1d9d3508f49d2d50bb9c97dd089c7605899c6826aa9c36144f9bfcd7929b71391a9b34b1219aec1f2b9ab0be7a9a488f169a36658d9985b807996c23f498d8396998553ede984899db97a5128c97251c989721f5ed97012b8496e3fc359690ba6e963c456d9603a49895fe78aa956125c69502be1694355c1494331b6593cd8fe0939a9e619396353d93602c4693527dd5
  | 8, 9 => 0xbf4172fabf355634bf01fb40bef1afedbee065e9beb2f988be4f311bbe3418b4be2639d5be107ab6bddd5bacbd2744b8bd199d0fbcc8e334bcb2dff7bc18011abb3f92c0bad4da24bab08b31ba9e7ab4ba708858ba477786ba2399e2ba1f06b4b9782853b8689f9eb85c2f59b837fe7bb81d78f4b6edc245b6be7634b65f3e8fb644e080b59a84ddb52557b8b47be621b3feb3cab354b256b315333eb2dc7687b272f2abb2313513b2306866b20ffb62b1b17014b18cc501b12375bdb0ec7e1fb07bc511b031a5c8b01ae1b0afebec7daf01b67aaef43dc2aebd223cadab993dada32de2ad6e1b08ad1a90a7acac34b6ac23afedaba1ac24ab94b348ab681b8e
  | 8, 10 => 0xd6890d25d64007d5d630e845d62ad27fd5d13c99d58853add56748abd3fa20bfd3a21f4ed38eac86d355d4ffd1d3f658d17f337bd0e5095fd0a7e5c1cfe713d2cf9551ebcf6e15b1ceecb93fceeb1ad8cecb96dfcdfcbe79cd5fbf4fcbfcbae9cb26fa2bcb191b4cca5eb5a5ca5838f3c9e24337c9d88a90c9c8daa4c9a019fdc8e779a6c8df6e8fc8d8951dc876c3bec7ad77bcc7a9b843c7a3ca76c7554d2ec7466283c707ac1ec6f762cbc6ea46f2c689fa79c61b5c10c5dca5abc5690328c52f7576c4eae2e7c4ac2c82c3d681efc398766ec37f968dc34f33b5c30bd3fac2afde01c278c27bc21dcfbbc1c5a5bec150c440c110cb7dc1043454bf8705eb
  | 8, 11 => 0xea39f55dea04555ae9d3bc26e8f19d4fe8b03ee3e812cbdfe7a75556e7283c3de7199440e5c6ac76e5b5122de5179d48e49194eae48a3599e4763a0be4625a30e45c7de4e4402e8ee3c88b86e2f7dbbfe2e94854e2e453e9e25263cde1c2a466e1b94d76e1283faae0f3695fe0d9cf49e0d27efae088d44ddfdba1afdfb32b5bdf91a28ddf7fbf91dee29a6adede789bdec49712de7f8515ddd7f9c9dd9de376dd547ea2dd1bb31cdd0995b1dc240579dbeeb34dda8fa153da52a0c6da26b2c9d9ed2281d9eccea3d9e7a089d9b9b7a8d96359b3d958a3e4d8f62b1fd8e7dfa1d8dd76c6d86400d8d863d13ed7c2c847d7c0c947d7661623d69e993fd697c1d4
  | 8, 12 => 0xfe091979fdf560cffd875a02fceb370cfce2758bfcb0a9dbfc7cb7dbfc3e0176fbefb591fbe5e7c4fab495f5faa130d0fa4dc81bf9acd0faf9824cb5f80ff336f80fe67ff7fbcecdf7f3c11df7e68aa8f76d67adf762f14af734b506f6e94291f6657479f646c3bff637ead7f5a8ee32f5210d0ef50771aef498545ef39bac49f34c8d5af33b5fd0f2e571d9f2854adff22186e7f20a7ebff1c1f496f17a65ebf171c893f15afe71f14d1f92f0f10dbef0c2900ff05fc8f2f053c1fdf03d9387efdef6d4ef0e3eb4ee6bbfe2ee22ff53ee1e2c58ede64ad6ed5ae6a4ed5612f6ecbfbceeec848404ebc28ee5ebb77889eaf7dac4ea9e47f9ea782c38ea555bf2
  | 8, 13 => 0xffabe638ffa13466ff8b32caff5a28feff3df527ff3992a2fefb8721fef2bd64fe12eeb4
  | 9, 0 => 0xf33b5fd0dd9de376c3d681efc2afde01b6be7634a6563cc3a1f16def9b34b1218ab84b5d8a7994f85e22a75455df5df851bb2a0f5059633d4f8c57c24aee73793e277fff2eedfa851e7359ed1561a43a1142fa41
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 5, 0 => 0x1000000000000120000000000004000000000001000000000c91080014d10440303000000000001000000000000110000000000013000000000001200000000000110000000000012000000000001200000000c9113000000000000900000000061060000000000012000000000000f00000000000120000000000012000000000001200000000000000000000000012000000000001200000000021060000000000012001491044030200000000000120000000000010000000000001000000000000120000000000010
  | 5, 1 => 0x120014d104403030000000000012001491044030200000000021060000000000012000000000000f000000000001000000000000130000000000012000000000001200000000000120000000000004000000000001100000000000120000000000010000000000001000000000000120000000000010000000000001000000000000070000000006106
  | 6, 0 => 0x2806201000000000a1050000000000008000000590020100000000000120000054006201000000480620000000000c9108000000000000800000000000120000000006106000000000e1000000000002106000000000000800000000000120000000002106000000010010100000104402020000000000010000000000000f000000000000b00000000c91080000052041201000000590020100000000000110000001802202000000000610600000000000120000000000012000000000001100000000000120000003806203
  | 6, 1 => 0xa104000000380a201000000001210000000048022010000010440201000000000000200000000000040000052440201000000000210000000000000060000000109105000000001210200000000000080000000006105000000480a20300000000000120000000012100000000480a2000000010440203000005244020300000000061030000000000009000000000000800000000000040000002802201000000001210500000104402020000004806202000000000e102000000480e201000000480a2010000000000007
  | 6, 2 => 0x104402010000000002104000000000210400000000121040000000000004000000000e10500000524402020000004806201000000000000a0000054041200000003248120200000000000090000004802201000000000001200000019092020000002900201000000380a200000000004110900000000021040000000012104000005404120100000038062010000000012104000000000000900000000021060000000000000000000000001200000000000070000010440201000000000000900006424c93020000000000007
  | 6, 3 => 0x10000000000000f00000514c0202000000000001200000000000130000000006104000000000e1020000004806203000000000e10500000530412010000004806200000000000001000000048c9203000000001210500000038062030000003806200000005344020300000029002010000000909202000000000a105000000000610500000000000110000000000010000000380220200000540412010000004806201000000280620100000324c1203000000480a20200000000c910400000000000120000052440203
  | 6, 4 => 0x38062000000002802200000000000001200000000000100000000002100000000000001100000524c0202000000000e1000000001900201000000000610500000304c02000000010440202000000480e202000000000001100000000121000000000006105000000380620000000028022010000000002104000000000000e00000000121050000005905201000005244020100000000121050000054440203000000380a202000000180220000000000021050000000000007000000000a101000000000000500000000c9103
  | 6, 5 => 0x480a200000000000001000000000000010000000000013000000000000e000000480e201000000000e105000005204120300000000000110000000002104000000000610500000000061010000000006106000000000a101000000000000900000000121020000000000011000000000210000000000c9100000000001210100000000000120000010440200000000000000f00000000000080000054440202000000000000200000028022030000000000012000000000a102000000000a1040000000002100000000000000c
  | 6, 6 => 0xf000000000000900000018c920200000000061060000002900201000005304120100000000021020000054041202000000000000f00000038062020000000000010000000000e1030000000000010000005108120100000000000120000002900201000000480a200000000000e105000000004110900000000061050000054006201000000000001000000000000030000000000009000000480e20300000000c9108000000000001200000038062020000000000010000000000e10300000000000120000000000011
  | 6, 7 => 0xe106000000000000f00000000000000000000002100000000000e1010000010440200000000000a10600000000021040000010440202000000000000100000000000070000000000010000000380a201000000280220200000530412010000000000008000000000e10000000000000120000000000005000005244020100000000000140000003802202000000000001100000000000110000000006102000000000001000000038062010000001802200000000000000500000008c920300000534402020000000000010
  | 6, 8 => 0x120000000000011000000280220100000324c1203000000000e101000000000000400000000000100000000000009000000000000100000000121040000004806200000000000001000000000121000000000000009000000000e10600000000000050000000006104000002048020100000000000080000000002104000000000000e0000000002102000000000210100000048062000000053041203000000480220100000058c920300000000000080000000006106000000000001000000525002030000003806201
  | 6, 9 => 0x61020000000000010000000000000400000000000120000000000007000000000e1030000054041201000000280620100000000000110000000000005000000000001200000104402020000002806202000000380220300000540062010000054006201000000000e102000005244020000000000121020000000000010000000000a10100000524402020000000012105000000380220200000000121010014910440302000000380220300000000000100000003802201000001044020300000000000090000000000007
  | 6, 10 => 0x6105000000000000800000520412010000003806200000000000a1060000000000000000000000000700000000121040000010440203000000010910500000000c9108000001044020000000000c910800000530412020000000000011000000180220000000000000120000052440203000000000000f0000000900201000000000000500000000000080000000000012000000001210300000000000120000002806201000000180220100000000021060000000012103000001044020100000018022020000004806202
  | 6, 11 => 0x52440200000000000000f00000000000110000054041201000005344020200000000000010000051500203000000000000700000204802010000000000007000001044020100000000411090000000041109000000000000400000000021060000000000010000000000000400000000000010000052041200000000000000e00000000000090000000000000000000001210300000000000070000000000012000000480e20100000000000100000000012100000000000610100000000000120000052041202000000000000f
  | 6, 12 => 0x520412010000000000000000000480620100000000000080000000000009000000000610000000028022010000004802203000000000001200000001091050000000000010000005308120100000000121010000000000000000000000e1030000000000009000000280620100000000000070000000002105000000480e202000000000000800000048022010000000006104000000000e10600000000021040000000002101000000480e200000000380a20200000534402030000042481202000000000000e000000000a104
  | 6, 13 => 0x424812020000004806201000001044020000000000021040000003909202000000000e1060000052041201000000000000f000005304120200000000021040000000900201000000000001300000048022020000000000010000000000000f00000048022010000010440201000000001210400000000061060000054081200000000000001000000000021030000000000012000000000001100000000000070000000000007000000090020100000000121030000010440202000000000001000000000061060000000006106
  | 6, 14 => 0x1100000204802010000052440202000000000a1040000000002103000000000a10400000000000130000000006106000000000e10500000038022010000003806202000000010910200000000021000000000000008000000480a20100000314c420000000000000070000000000011000005001220100000048c920300000000000120000000000010000000000001300000000000120000000000011000000000a100000005304120000000000411090000000000009000000000001300000008c92020000000000012
  | 6, 15 => 0xe106000000000e1030000003806201000000280620100000000021060000000006100000000000210600000000000120000000000012000000280620100000000000100000003802200000004248120200000524402000000000000011000000380620100000104402000000000000012000000000e10600000000000100000000000003000000000001200000058c9202000000480e2030000052440200000000480e20000000524402010000054041201000000000e102000000000000700000000000070000004806200
  | 6, 16 => 0x610000000000c9108000000000001000000000000100000054081200000000000000d000000000001400000000000090000000000012000000380a2020014d10440303000000480a2010000000006100000000280620000000000021060000000002101000000000610400000000061000000000000009000000000000400000000c01040000000006106000000000a10100000000401010000000012102000000000001100000029002010000000000010000000000e105000000000000900000540412010000052440203
  | 6, 17 => 0x1000000000e105000000000e10500000008c9203000000000001200000000121000000000000007000005404120300000000000070000000000012000000000000900000018022010000052041200000000000210600000000c910400000000411090000000006104000000000000900000048022010000000006104000000000a100000000000e105000000000a101000000000a10100000000000110000000000010000000480e20200000000121030000000000012000001044020000000000021030000000041101
  | 6, 18 => 0x38022030000053440200000000000e1020000000000008000000380a201000000000001100000038022000000053440202000000000000700000018c920300000524402010000000000012000000280220100000514c0202000001044020100000524402000000000000009000000000000900000530812010000000000009000000000e1060000000000012000000000001300000000121020000000000012000000000000000000534802000000000000010000000000000f000000000210600000000000070000000000007
  | 6, 19 => 0x120000002802201000000000001000000048062010000000000011000000480220000000514c020300000028022020000000012105000000000210400000424c9202000000000610000000000021060000000000012000000390020100000000061040000002802202000000190920200000520412010000054006201000000480a2010000002806202000000000001000000058c920300000000000070000000000010000000000000700000000c9108000000000210600000524402020000000000009000000000000e
  | 6, 20 => 0x100000000000010000000001210200002424c93020000000000012000005404120100000000411090000000000003000000000000700000000000060000000000010000000000000600000000000100000000002105000000000000400000104402010000054041203000000480e2000000000002103000005304120000000018022010000054081200000000000a106000005404120100000534402030000000012103000000000610200000048022020000000000012000000000610100000424c92020000004806201
  | 6, 21 => 0x16424c930200000204802010000000006101000000280220100000000000130000010440201000000000000900000514c02020000053440200000000000e10400000000c911300000104402010000000002106000000000a10100000028062000000000000007000000000000f0000000000009000000000a10600000104402010000000000012000000480a2020000003806203000000000001100000000c91130000054440203000000001210100000000000120000002806200000000000001200000000000080000003806202
  | 6, 22 => 0x12000000280620200000000061060000001802201000000000000900000000000100000000002104000000000e102000000000e105000000000001300000544402000000010440203000000480220300000000c91040000000000013000000480e201000000001210400000028022010000004802200000000001210500000544c4200000000000a101000000390920200000000000120000003802203000000000a1050000003802200000000000e1010000001900201000000000210500000304c02000000000000007
  | 6, 23 => 0xf00000000000100000000000007000000000e10400000540412000000053041201000000280220200000104402010000000000010000000000e106000000000001200000000c9108000000390020100000038022000000000000009000000480e20100000540412010000000000011000000000a1040000000900201000000000210500000048062020000052041201000000000e10000000038062020000000000001000005204120100000018022010000003900201000000380220000000000121050000000000010
  | 6, 24 => 0x121010000000000009000000190020100000534402000000000084101000000000210500000000000110000021484201000000480a201000000000e103000000000001100000048062030000000000011000000000e1000000000000010000000380220200000524402010000000000007000000000000800000000c910800000000000070000000000000000000000001100000000000080000000002105000000000610400000000000140000052440203000000000a103000000004110900000048022020000052041201
  | 6, 25 => 0x3806201000000000610000000000000090000053440202000000001210100000000c91080000000000011000005148020000000000000040000000002102000000380220100000000021040000000000010000000000001200000000000130000000006104000000480a20100000000000130000000000011000000380220100000008c920200000000000070000000000009000000000610400000019002010000000002106000001044020200000048062010000000041109000000000000700000000c9108
  | 6, 26 => 0x70000000000012000000000000e00000520412010000000000000000000001210000000000000070000000000007000000000000f0000004802200000000000001000000000000070000000000012000000000210600000000000010000052440203000000000000900000510812010000003802201000001044020100000000c9113000000000e1040000053041202000000000a10600000540412000000052041201000000000001000000000000110000000006103000000000000800000039092020000004802201
  | 6, 27 => 0x70000052440201000000000e10000000028022010000000000009000000000001100000018022030000000000007000000000000500000000000110000000000007000000380a2030000000000010000000380a2000000001802202000000000000900000424c920200000000000090000053440200000000000000e000000000001200000000000100000001802201000000380a201000000000610600000000000120000003802202000000000000f0000004802200000000000000e000000000e1060000003806200
  | 6, 28 => 0x2806201000005404120000000000000020000000909202000000000a10300000018c9203000000000000400000000061030000000000008000000000001200000000061010000000000010000000480a20200000104402030000002806201000000000001300000000000070000002802201000000000610600000001091050000052440202000000000e1060000000000007000005444020000000018022010000000000012000000001210400000000000110000054041201000000000001000000000000040000000000009
  | 6, 29 => 0x12000000380620000000530412010000000000010001491044030200000038022010000000000012000005250020300000028062010000000000011000000001210400000000000130000000000007000000000e1020000000000012000000000e10000000000000130000000000012000000000a105000000000000600000000000070000000000010
  | 7, 0 => 0x80000000002105000000000001000000000000010000000040101000000000e102000000000a103000000000a101000000480a201000000000e10500000000121000000000002105000000000210100000000000050000000006102000000000e101000000380220300000028022000000000000005000000000210000000000851010000000000013000000000000100000000c510200000000061030000000000001000000004110100000000021030000054081200000000004110200000000000110000000000000
  | 7, 1 => 0x80101000000000210300000000000070000000081100000000000610100000000000110000002900201000000000000400000000c5102000000000000f00000000000130000000040101000000000000100000028022000000000006102000000000610200000058c920200000000411000000000000003000000000a101000000000a10000000000021060000000000002000005404120100000304c02000000000006100000000000001000000000000040000000000011000000000210100000000000120000052041201
  | 7, 2 => 0x40101000000001210400000038062020000000000004000000000000500000000061010000000000004000000380a2020000000000005000000000e10300000000c110200000000021020000000000008000005404120300000000000080000001802201000000000210200000000061000000000000007000000000210100000048022000000054041200000000000001000000000021040000004802201000000000a1040000000000007000000000e1020000000085101000000001210000000001041010000000000009
  | 7, 3 => 0x8000000000000900000000061030000000012101000000000000800000018022000000000000005000000000000100000000021020000003806202000000000e1050000000000004000000000e10200000000021010000053041203000000000000700000000c5102000000000000400000000000070000000000013000000000210000000000000110000000002100000000000e1040000000002103000000000610100000000021000000000000004000000000a10400000000000020000000012103000000010c100
  | 7, 4 => 0x380620100000000000040000000012101000000000e10100000000000090000003806203000000000e1020000000000004000000000000000000000000090000054041200000000000210300000000061020000001802202000000001210400000000c9102000000010010100000038062000000000006102000000008010100000000021020000000000001000000000a10400000000000050000000006100000000000001000000000061010000010440203000000000000f00000000000090000000000003000000000e104
  | 7, 5 => 0x13000000000210300000000021000000000000002000000000000400000000c91030000000000010000000000e102000000000000800000018022010000000000004000000000e10100000000000040000000000004000000380620200000000121000000000002100000000000a10100000048062020000000000008000000000610200000001091020000000000006000000000e1020000000006101000000000a103000000001210300000000061010000053041203000000000000100000000000040000001802203
  | 7, 6 => 0x411030000000084101000000000000400000000c1102000000000000800000000000040000000000007000000000210100000000061010000000002104000000000000400000001001010000052440201000000000000000000000061020000000000008000000008010100000000000090000000100103000000000a101000000000000300000000021010000000000010000005244020100000000021040000000000007000000000000c000000000000700000000c9103000000000000100000000021020000000000000
  | 7, 7 => 0x1044020200000000000100000000000009000000000a101000000000210400000000c11030000000000012000000000a102000000000000400000304c020200000000121010000000000001000000000000400000000000020000000000011000000380620000000000000080000000006102000000000610200000000021020000000104101000000000000800000000000020000000000013000000000e101000000000a100000000000a101000000000a1000000000006101000000000001000000000121000000003802200
  | 7, 8 => 0x210500000000000080000000002101000000000000200000048022010000000002102000000000e101000000000e1030000000006100000000004110100000000411010000000000004000000000a1010000053440203000000000a1020000021484201000000000a106000000000e1000000000000012000000000e1050000000000007000000000000700000000000040000000006103000000000000f0000002802202000000180220000000048022000000000000003000000001210100000000021000000000000009
  | 7, 9 => 0x4010200000000021020000054041200000000000000900000000121000000000000012000000000000900000000021050000000002106000000000000e000000000000f0000000000002000000000001000000000000100000000002101000000180220000000000000120000000002106000000010010300000000000000000004802202000005244020300000000c5103000000000e10200000000c9104000000000000600000424c92020000000040101000000000000d0000000100100000000000e1050000000002101
  | 7, 10 => 0x13000005344020300000000000090000000002102000000000e1000000000006101000000480a20300000000000040000000002101000000000210200000000000080000000000008000000000000f000000000e10300000000000080000000000002000000000000000000000000110000000000008000000000a10200000424c9202000000000a10100000000021020000000002101000000480a2000000000012103000000000000700000000061040000000000008000000001210200000000000030000000000008
  | 7, 11 => 0x110000000000009000000000e103000000000000800000000c0102000000000e102000000001210200000000000010000000012102000000000000f0000000081102000000000210000000000000030000000000004000000000610400000000000030000000012100000000008110200000000000010000000000010000005350020300000000061000000000000009000000000000000000000000010000000002100000000004110000000000000110000003806202000000001210400000038062030000051081201
  | 7, 12 => 0x1000000000061020000000000010000000480a2000000000040101000000000a101000000380a20000000304c0202000000000610100000000000020000000000005000000000e1020000000006104000000000000700000038022020000000002105000000000210300000000841010000000000007000000000e1010000000100101000005304120000000000c510000000424c920200000000061010000002802201000000000210000000000000070000004802203000000000210200000000021050000000012101
  | 7, 13 => 0xe10300000000801010000000000002000000000a10100000000000080000000006101000000000a101000000000000600000000121010000000006103000000000210300000000000120000004802203000000000a10000000000000080000000000008000000000e103000000000210000000000000090000000006103000000000000900000304c02030000000006100000000000001200000001081010000000000009000000000000400000000061030000000109102000005244020200000000000010000000000003
  | 7, 14 => 0x6102000000380a202000000000000400000048022020000000012100000000000210200000424c9202000000000001200000000000040000000002101000000000a10100000000021020000000000002000000000a100000000000610000000000021020000000006101000000000610000000540c12020000000000001000000000000200000000061030000000000012000000010410100000001091020000000000007000000000000300000028022020000000002103000000000001000000000021040000000000009
  | 7, 15 => 0x120000000006106000000000a101000000000000300000000411020000000002101000001044020000000000000050000000000008000000000000900000000061000000000000005000000000210300000214842010000000002101000000000a10100000000000050000000002104000000000001200000018022020000003806201000000000a1030000000000001000000000000f0000000000013000000000000f000000000000700000001001010000000084101000000000610100000000000080000000000002
  | 7, 16 => 0x70000000002104000000000000000000000021010000003909202000000000e101000000000210000000000c910400000000000090000053041202000000000000400000000061030000053440200000000000001200000000000090000000000014000000000e10100000000000020000000002100000000000a1010000000000009000000000000600000000021000000000000007000000280620100000000000070000000000000000000480e2020000000002100000000000001100000000021030000000006102
  | 7, 17 => 0x21010000004806203000000000210000000000061030000000000009000000000001200000524c42030000000000009000000000000100000000000120000000000002000000000000700000104402010000000006100000000000e1020000000006102000000000a10200000000061020000000000013000000010910200000048062000000000002102000000000000f000000000a105000000000001100000000c9104000000004010200000000411010000000002104000000480a20100000000061010000000000009
  | 7, 18 => 0xe100000000000000200000000000020000000006104000000280220200000000000070000000000011000000000000500000314c420000000000000040000000002101000000000a1010000000012102000000000a10300000000c510300000001081010000000000000000000000000e0000000012105000000000e10200000304c020200000000021010000000000007000000000610200000000c41000000000000012000000000610100000000401030000000000012000000000a103000000000001200000000c5102
  | 7, 19 => 0x41100000000004010100000304c0200000000008410100000048022020000000000012000000000000100000424c920200000000000070000004806200000000000e106000000000a105000000000e10000000000000060000000041101000000000000700000000061010000000012101000000480e20300000000061020000000080101000000000a1000000004802200000000480e20300000000000070000003909202000000000210100000314c4202000000004010100000000c910200000000c0102000000000e103
  | 7, 20 => 0xc91000000000006101000000280220300000304c0202000000000000000000000021040000000012105000000004110200000524402000000000006101000000000e1000000000000000000000000a10000000001091020000002802200000000000610200000000021030000000000005000000000e10300000000c9108000000000001300000304c0203000000000000300000000000030000000109102000000000a104000000000210000000000061020000000000004000000000a101000000000a103000000380a200
  | 7, 21 => 0x5204120300000000061000000000000004000000000a103000000000e10500000534402020000000000010000000000000f0000000012101000000010010100000028022020000000000010000000000a10000000000021000000001802202000000000001300000000000060000000000012000000000e10400000000c91040000052440201000000000000700000534402020000000000010000000000a101000000380a20100000000c1102000000010810100000000061060000000002102000001044020000000000c9102
  | 7, 22 => 0x800000000121020000000000009000000000610300000000000060000004806203000000000610100000000000120000000006101000000000000200000028062030000000000007000000380620200000048022020000000000004000000000a10000000424c920200000304c02000000000002104000000004010100000000c5100000000000e10000000000401000000000006100000000000000500000000021010000000000005000000000e101000000000a102000000008410100000028022010000000000012
  | 7, 23 => 0xa101000000000e1000000000002103000000000000800000000061000000000100101000000000210200000000021010000000000008000000480220100000000021050000054041203000000010d10000000000851010000000000006000000000001200000000021020000000080101000000000000700000000811020000000000000000005408120300000000c1100000000000000f00000000811020000000006101000005250c203000000000e1010000054081203000000000000700000028022000000000000004
  | 7, 24 => 0x841010000054041200000000090020100000000c91020000054041201000000000610100000000c1102000000000610100000000061020000000002104000000000001000000000061020000000006101000000001210100000001001000000000000006000000480a20000000000061010000000000007000000000000f00000000000000000000000012000000000610100000000061020000000006101000000000000e0000000000008000000000a1010000002806200000000000000500000000061030000000002101
  | 7, 25 => 0x1000000000000500000000021030000000000008000000010910200000000061040000000012103000000000000900000000061030000000012101000000000000100000000000060000000000003000000380a201000000001210100000304c0200000000000610100000000000000000052440200000000000000400000000021000000000000000000000010410100000304c0202000000000000600000000121030000000000003000000000e1020000000012104000000000e10200000000021010000000006103
  | 7, 26 => 0x2806201000000000a100000000000a100000000000a105000000000000900000000000070000010440202000000000210100000000121010000000081102000000000610500000000000060000001802202000000000e1010000000000004000000000e1020000000080101000000000e10000000000411020000000000004000000000000400000000000050000000000007000005204120100000000061020000000000005000000180220200000001091020000002802202000000000000600000000121030000000000005
  | 7, 27 => 0x1200000000000030000000000007000000180220300000314c42000000000000003000000000210100000000000080000000002102000000000000900000000061030000000000012000000008110100000000121010000000012101000000000610000000000c1100000000180220000000000c9102000000000001200000000000080000000002104000000000000300000000000060000000000004000000000610400000000000110000000006103000000390920200000000000050000003806200000000380a201
  | 7, 28 => 0x1210000000000000080000000000003000000000000500000000061030000000002104000000000001000000000000090000000002102000000380a203000000000e1020000000000008000000180220200000000411020000000000007000002148420100000000061000000000002101000000010110000000000000040000000002101000000480620100000048c92020000000002102000000000e1000000000000006000000000001000000000000070000000012101000000000e10200000000121050000000084101
  | 7, 29 => 0x38022030000000041101000000000e10000000000851010000000006100000002148420100000000000110000000100101000000000000100000000000100000000108101000000000a1060000000000004000000000000400000000000020000000100103000000000000300000000061010000000000008000000000000900000000000040000000000005000000000210400000009092020000000000003000000000e10600000000000120000000000009000000000001000000000000010000000006100000000000e100
  | 7, 30 => 0x41100000000000e1040000000000009000000000a10500000000c91020000000000009000000010910200000000000120000000040103000000480e2000000000000004000000000a1050000000109102000000000a10000000000000130000000006106000000000000700000018022000000000002106000000000000100000018c9203000000000001200000530412030000000100101000000000e1020000000000001000000000210100000038022030000000000004000000390920200000000000020000000012102
  | 7, 31 => 0x2806201000000000e1010000000002105000000000a103000000000210600000000121050000000000007000000000000900000524402020000000006102000000000001300000000000010000000000001000000000a1010000000012105000000000e10000000000021010000000000000000000010810100000314c4203000000000210500000000000090000000000009000005404120100000524402010000000000008000000000000700000001051000000000000004000001044020300000000811010000000000004
  | 7, 32 => 0x314c42000000000000003000000000a1000000000000010000000000000c000000000e103000000000210000000314c42030000000002101000000000e102000001044020200000000000030000000000010000000000a1020000000002101000000000000700000000000070000010440200000000000001200000000121010000000000004000000000000700000000411010000000000012000000480a200000000000a104000000480a201000000000a104000000000210200000000c010200000000000070000000006104
  | 7, 33 => 0xe1020000000002103000000000a101000000000a10000000000c910400000000000060000000002102000000000e102000000000000f00000000000080000000108101000000000000200000000121040000054041203000000000001200000000000070000000002102000000000001100000000000040000000000000000000000e105000000280620100000000411020000000006100000000000e101000000180220200000000000090000001802203000000480e201000000000a100000000000a1030000000006101
  | 7, 34 => 0x61020000000000000000000480e2000000000104101000000000000a00000000c5102000000000210100000028022000000000000008000000000000e0000000000012000000000000200000000c9104000000000000200000018c920200000000000090000000000012000005408120000000000000000000000000009000000000e1010000000000012000000000610000000000000010000000006100000000000610500000000021020000000006101000000000000400000000000080000000000007000000000e101
  | 7, 35 => 0xc1102000000000610200000038062030000000000000000000000001000000000000070000000000000000000000000600000000021050000000002103000000000210400000000021000000000000001000000001210100000000061000000052440203000000000a10400000000061010000000000001000000000a105000000000000900000000c91000000000000010000000000a10300000000021010000000012102000000004110000000540412030000000000000000000000a10000000000061040000000000014
  | 7, 36 => 0x40000052440200000000000610400000000000120000000000012000000000e1020000000000005000000000a102000000010010100000000061060000000000012000000001210500000000c9108000000000610400000000121010000000041101000000380a20000000038062010000000002103000000000000300000000000130000000000000000000000210100000000000090000000002103000000000210100000000061040000000000004000000000210100000001001010000000006101000000000000a
  | 7, 37 => 0x20000000040100000000000000400000000061050000010440201000000000000400000000121020000000006105000000004010200000038062030000000000004000000480a20000000000061000000010440202000000000210100000524402020000000000011000000000e103000000000610300000000000120000000100101000000000000700000000000000000000002102000000001210100000000000000000000000000000000000000000000000c1100000000000000900000000000120000000002103
  | 7, 38 => 0x610300000000000040000000002101000000000a101000000000000200000000c410200000018022010000000000006000000000a1010000000085100000000000a10100000028062000000000000011000000000a106000000480a20200000000021010000000000011000000000e102000000000a10500000000c5100000000000000900000000000120000000002101000005344020100000000000070000000000005000000000000300000000000010000053440203000000000000100000000061010000000000012
  | 7, 39 => 0x210200000104402020000000109102000000000000e0000000000009000000000e10100000048022010000000100101000000000610200000000000000000002802201000000000000f00000104402030000000002106000000000610100000009092020000004806200000000000e10000000001001010000000006104000000000a102000000480e2010000004806201000000000000100000534402030000000000001000001044020000000314c42020000000000010000000000a10200000000061010000000000009
  | 7, 40 => 0x4010100000038022000000000000002000000000a1000000000000012000000480a2030000000041102000000000a10500000000000000000000006102000000000210500000000811010000000006101000000000210000000000000040000000012100000000000a10100000000021000000000012102000000000e10100000000061000000000006100000000000000900000000061030000000006100000000000610100000000c010200000000000130000000000010000000001210200000000021000000000000001
  | 7, 41 => 0x6102000001044020000000000061010000000002100000000000000400000000121040000000000010000000000a1010000000006100000000000000200000540412000000000000001000000000001100000000c910200000000000110000000000012000000010910200000000000120000000104101000000000a10500000000000060000000041102000000000a101000000000000700000000000100000000104103000000001210000000000021010000000000007000000000001200000000000090000000000011
  | 7, 42 => 0x480e202000000000a100000000000000500000000000100000000012105000000000000800000000c9103000000010010100000524402020000000000000000000000000400000000c911300000038022030000000012104000000000000f000000480220300000000000030000020480201000000010010100000000121050000000000001000000090920200000515002010000000006103000000004010300000000000110000000000001000000000000e0000003802202000000000000700000000121040000000000008
  | 7, 43 => 0xa10100000000000020000051500203000000000e105000000000000400000001041010000000012104000000000a1040000000000009000000000e102000000000210000000000061020000000000002000000000000600000000000000000000000005000000000e102000000000610500000001001010000000006104000005404120100000000061050000000000009000000000610100000000061030000000006100000000000000500000028022000000002802201000000000610000000534402020000000000001
  | 7, 44 => 0x2101000000480a2020000000002104000000000610500000530412010000000002104000000000e10400000000000100000000000012000005244020300000000021040000000000009000000000610200000504c4203000000000a10200000000000010000052440200000000000a102000000000210100000001081010000000000007000000000000100000000000010000003806200000000000a1010000000012100000000000000300000038022010000000000010000000000000f00000000000090000000006101
  | 7, 45 => 0x81101000002048020100000000000120000000000007000000000e10100000009092020000000012102000000000001100000000000080000000012103000000000000400000000000000000000002100000000000000200000000c9103000000000e103000000000a104000000000001000000028062020000000000005000000480620000000038022000000000000000000000000001200000000c910000000524402020000000000012000000000000e0000010440202000000000210000000000000070000000000013
  | 7, 46 => 0x52440200000000001210100000000000070000000006106000001044020000000000000090000000000012000000000610100000000000090000000006106000000480620200000000801010000003802200000000000000f0000000012104000005404120100000000000120000051081200000000000a1000000000006105000000000610100000000000120000000012104000000480620100000530412000000000006102000000000000700000038022000000000000005000000000a10300000000851010000000000010
  | 7, 47 => 0xf00000000000060000000000012000001044020100000000000100000000000006000000000610100000000021010000000000011000000000a1000000000006101000000000610500000000000040000000002101000000000a10100000000811010000000000000000000000610200000000061010000000000012000000000000400000000c910300000000000010000000000004000000000a1040000000000006000000000000200000000061020000000000005000000000e10100000000000010000003909202
  | 7, 48 => 0xc510200000000000020000000012100000000000001300000000021010000000000008000000000001100000000000120000000002102000000000000500000000c1100000000000000200000000c51030000000000008000000000000700000000c51000000000006100000000000000200000000021010000000000009000000000e10400000000000040000000040103000000000000400000000000040000053041203000000000000300000000061000000000000000000000004010000000520412010000000000012
  | 7, 49 => 0xe101000000000e106000005344020000000000000080000000000005000000480a2000000003806202000000000000400000001091020000000006105000000000e10100000000000070000000002104000000000000f000000010910500000000000120000000000013000000000610100000000000070000002806201000000000001000000204802010000000006100000000000a101000000000000e0000004806203000000000610200000000061040000000006102000000000e10000000000851000000000000004
  | 7, 50 => 0x411010000000040101000000000a10200000000c11020000000000010000000000a101000000000a1040000000909202000000180220000000038022010000001802201000000000e103000000480620300000000000040000000006100000000000a10100000314c4202000000000001200000000121030000000000001000000000e1000000000000012000000000a1000000000000007000005244020200000000000070000000002100000000008110100000000841010000000000012000000480a202000000000e102
  | 7, 51 => 0xe100000000000210000000000000040000000000004000000000610600000000000140000000000012000000000210200000000000100000000000003000000008410100000001081010000000000001000000000000700000524402000000000040101000000000000300000001091050000000100101000000000001200000304c020300000000000070000000000009000000000a1000000002806202000000000610300000530412000000000006104000000000210300000534402000000000000003000000000a104
  | 7, 52 => 0x4802201000000010010100000000061010000000000012000000480a20200000000021020000000000000000000480620200000314c420300000000000100000000002100000000000a1040000000000002000000000a1010000000000005000000000e1040000000000009000000000610100000314c420000000000c510200000000061020000000002105000000280220300000000c910400000000c110000000000121020000000000007000000000000800000000061020000000000007000000000e104000000000a101
  | 7, 53 => 0xe102000000000610100000000c51030000000002104000000090920200000000000070000000000012000000000210000000304c02030000010440202000000000610100000000841000000000006100000000000000200000000000080000000006104000000000e101000000000e10200000314c42020000000000008000000000210400000000000030000003802202000000380a20100000000121010000000000007000000000000800000524402010000000002104000000000000000000000000040000000000001
  | 7, 54 => 0x610400000314c4200000000000210400000000000120000000000012000000000210200000000000080000000000005000000000001000000000061000000000109105000000004010100000000000070000054081200000000000a10200000048022000000000002102000000000000700000000841010000000100101000000000610000000000000120000000000005000000000000700000001091020000000084101000000000610000000000411010000000006100000000000001300000000021020000000000000
  | 7, 55 => 0xc91030000000000005000000000a1010000000000013000000000000f000000000210400000000000120000000000007000000000000000000000000070000000012102000000480220300000000021010000000006100000000480e201000000000210100000000000040000000012105000000008010100000000000120000000000003000000480e2030000000002100000000000e1030000000000008000000000e1000000000000009000000000e1020000000000000000000000e102000000480e2000000000002101
  | 7, 56 => 0x21000000000000006000000000a1010000000000001000000001210100000000000010000000002103000000000e10200000534402000000000002102000000000000300000028062020000003900201000000000000500000000000070000000000002000000000a101000000000610100000000811010000000000001000000000000200000000000090000000000002000000000a10000000000000110000000000004000000000210100000000c01040000004802201000000000001000000000021050000000080101
  | 7, 57 => 0x61000000053041202000000000210200000000021010000000000012000005304120000000000000030000000000010000000000000500000048062020000000000007000000000210400000000000070000000000011000000480e2000000000002102000000000000e0000000084101000000280620200000000000070000000002104000000000a1020000000002105000000180220100000000000060000000000005000000000a10100000048062000000000012101000000004010200000000000100000000000002
  | 7, 58 => 0x1000000000a10200000000000040000000006104000000000000000000000000100000000006102000000008510100000000000060000002806203000000000a1010000054081200000000000a102000000000001100000000061040000000000000000000000000700000048062020000000000010000000000210100000001041030000000012102000000001210300000001001010000002806200000000000610300000000000100000000040101000000480220000000314c420200000000851020000000000004
  | 7, 59 => 0xc510000000304c020000000000000110000000006101000000000000900000000000060000000000001000000000e10300000000000100000002806201000000010910500000000c110200000540812030000000000009000000000000300000000000100000000040100000000000a104000000000a1020000000000004000000000001200000000021010000000000004000000008110100000028062020000000006100000005408120000000000000040000000000002000000380220200000000000000000000000005
  | 7, 60 => 0xa101000000000000800000000000030000002806200000000000210200000000000010000000002106000000000000200000000c91040000000000001000000380a2030000000006100000000000a101000000000000100000028022000000000084101000000380a203000000001210100000000000100000000012101000000480620200000000000080000000000012000005404120200000000121020000000006104000000001210400000000000120000000000007000000180220300000000000090000000080100
  | 7, 61 => 0x5000000000000500000018022030000054081200000000000000800000000000060000000000011000000000610000000000c9100000000000210100000000021040000000000004000000000000000000000000120000000002103000000000000300000540062010000000000007000000010010100000000851010000000000002000000000000800000000000080000054041203000000000610500000000000120000000002102000000000000900000000000000000000002100000000000000f0000000012104
  | 7, 62 => 0x4000000000a10500000000000030000000104100000000000000700000000021020000000000008000000000e105000000000000f00000000000000000000041101000000000610100000000000070000000012104000000000001300000000021010000000000009000000000000400000000000100000000000005000000000000700000000000090000000000008000000000e100000000000610200000000000130000000006101000000000610100000048062010000000006105000000000e1000000000012101
  | 7, 63 => 0xa101000000000001200000000121030000000000011000000000e101000000000001200000001091050000000006101000000010010100000000000030000000000010000000004110100000000121050000000006104000000001210300000000c91130000000109105000000000e1030000001900201000000000000700000534402020000000002101000000000610100000000801010000010440200000000000a102000001044020100000000021020000000000005000000000e10200000000000050000000002104
  | 7, 64 => 0xe1050000000000002000000000a103000000001210000000000121010000000012100000000000a102000000000000300000000c510000000001001010000000000005000000000e1020000000000008000000000610000000000000090000003802202000000280620200000000000080000002806203000000000610300000000021010000000000001000000000001200000000121020000000085100000000000e103000000000000800000000121050000000012101000000000610100000000061000000000002100
  | 7, 65 => 0x2102000000000e100000000000000700000038022000000000012102000000000001000000000000040000000000002000005404120300000001001010000000000006000000000001100000000121010000000000004000000000000500000000021010000000080101000000000000500000000411010000000002103000000000a10200000000401010000000000007000000000000f000000000000200000000061040000000002102000000008510000000000000120000000000001000000000610200000304c0202
  | 7, 66 => 0xe1010000000006104000000000e1030000000006102000000000e10200000000061010000003802202000000000e1000000000000007000000480220200000000c9102000000000000f000000000000600000000061020000000000000000000000000400000000000040000000000012000000000000700000001081010000000006102000000000000900000038022010000000000004000000380220300000000061020000000000012000000000a1010000000000007000000000001000000530412020000000000013
  | 7, 67 => 0xc910300000000121030000000000003000000010410100000000021010000000012100000000000e100000000000e104000000000001200000524402000000052500203000000004010100000000000100000000006101000000000e10200000000021020000000000006000000000a1010000000080101000000000210400000000021020000000000012000000000000100000000000070000000000009000000000e102000000000000100000000061030000053440203000000000e10000000000000030000000000012
  | 7, 68 => 0x400000534402020000053041202000000000000f00000000000040000000000008000000000000800000000000040000000000001000000000000300000534402000000000006106000000000001200000001091050000003802200000000004110200000038c9203000000000e10100000000401000000000006101000000380620300000535042000000000000003000000000e101000000000a1020000000000000000000000000000000018022000000000002101000000000001000000038062030000000041101
  | 7, 69 => 0x3806200000000000210000000000401020000000006101000000000610400000000c010000000001091020000000002100000000000001200000000000000000000006105000000000000700000514c0202000000008110200000000000000000000000011000000000001200000520412010000000002103000000000e100000001044020100000000061030000000000002000000001210400000000000120000000000001000005204120000000000000080000000000012000000000001200000514c02030000000000011
  | 7, 70 => 0x80000000006103000000000210400000000000070000000040101000000000000400000314c4202000000000001000000000061040000000085102000000000a1010000053041200000000000001200000000000120000000000009000000000e102000000000e1010000000000007000000000000700000544402030000000104100000000000000400000000061020000000000012000000000001200000000061050000000000011000000000000900000000000070000000000012000000000001300000000c0103
  | 7, 71 => 0x104402030000054440200000000000a101000000000000400000000000030000000000001000000000e10200000000000010000000081101000000000000800000530812010000000000007000000000e10000000038022020000053041202000000000000500000000841010000000002102000000000a1010000000002101000000001210100000000000040000000006100000000000000300000000000130000000006101000000000a10200000000061020000003806201000000000001000000000000050000053041203
  | 7, 72 => 0x12000000000000200000000000120000000000002000000000000900000000061020000000100101000000000e100000000000e100000000000e10500000018022010000000000005000000000210100000000c91030000000000009000000000000100000000411010000000012100000000000000800000000021010000000006103000000010910200000000000040000000104100000000000000600000001091020000000006101000000480e2010000000000008000000000000400000000c91000000000002104
  | 7, 73 => 0x210200000000000070000000081101000000000e10200000000000020000000000001000000000000100000000000060000000012101000000000210200000104402030000020480201000000000e1020000000006101000000280620000000000061050000000000007000000000000100000000000040000000012103000000000001200000000000060000000012101000000180220200000000021040000000000000000000480a20300000530412000000000000013000000000001200000000000120000000000000
  | 7, 74 => 0x6103000000380a20100000000061040000000000009000000000610300000000061010000000000007000000000610100000000000090000000000009000000000a101000000000e10200000000000130000000002103000000010910500000000000040000000006103000000000610400000001001010000000000009000000004110200000000000110000000040101000000000000800000000000020000000002103000000008110100000000000040000053440202000000010910500000000021000000000006101
  | 7, 75 => 0x2101000000000210100000000000120000000002100000000000000000000520412020000000000008000000000a10400000000801010000000000001000000000000900000000000040000000000007000000004110100000000811020000021484201000000000210200000001001010000000104101000000000000200000000000130000000012101000000000000400000000000070000000000006000000000000800000000000030000052440203000000000e101000000000000900000204802010000000000008
  | 7, 76 => 0xc91040000000000008000000000000400000000000120000000041101000000000210100000530412020000000000002000000000610000000000021020000000012101000000000e10500000000000050000000000004000000000001200000000c1100000000000001000000000061010000053440203000000000000500000000000090000000000007000000000a100000000000000000000000000090000000000011000000000e10300000000121030000000006102000005344020000000001091000000000002100
  | 7, 77 => 0x52041201000000000000200000000000100000054041200000000000000100000000061010000000000013000000380a20000000001091020000000002102000000000210600000000c9104000000000000700000000000070000000000001000000000610400000000061010000000000006000000380a2000000000000005000000000000f0000000000012000000000000f0000052440203000000380220100000000000080000000040101000000000e1040000053440202000000000a101000000000e102000000000e105
  | 7, 78 => 0x48022000000004806201000005244020300000000c9103000000000000800000000000090000000000001000005344020000000000061060000000012104000000190920200000000000020000000012103000000000a101000000480e200000000000000400000324c42030000000041101000000000000e000000480a20100000000000120000053041200000000000000f000000010010300000000c9108000000010010100000000000120000000000004000000010010100000000000080000000006101000000000e103
  | 7, 79 => 0x61030000000012100000000000a102000000000210100000000000060000000000013000000000000900000000000040000000012104000000000610200000000c4102000000000e100000000000e100000000000e1030000054041201000000000000e0000004802203000000000e100000000000a1010000000002103000000001210100000000021000000000006102000000000210000000000000040000000000004000000000210200000000021020000000002102000000000610200000000000010000000012100
  | 7, 80 => 0x41103000000000000f0000000081102000000000a1010000000006100000000000e10200000000411090000000081101000000000e1010000000006100000000000000f000000000000900000000021030000000041102000000001210100000000000070000000002104000000008510100000000000040000010440200000000000210100000524c02030000000000008000000000000700000000c91040000003806200000000000000000000000000020000000000005000000001210300000000061010000000000012
  | 7, 81 => 0x2000000000e10300000028062000000000000009000000000e10000000000061010000053440202000000280620100000000000090000000000012000000000000500000000000090000000000001000000000e1000000000000008000000000e1060000000104101000000480220000000048c9203000000000a1020000000000004000000000210100000000c1103000000000000500000048062030000001909202000000010010100000000000010000000000000000000001210200000000000040000000012100
  | 7, 82 => 0x4806200000000008510000000000801010000003806201000000000a101000000004010100000540812000000000002101000000000000f0000000000009000000010010100000000021040000000000007000000000610000000000061000000000012102000002148420100000000000010000000041102000000000000400000000000060000000000002000000000000500000000c91030000000000012000000000000c0000000000003000000000000700000000000070000000006101000000000e1050000000000013
  | 7, 83 => 0x480e20000000001091020000000006102000000000a10400000000061000000000000004000000004010100000000c9104000000000000900000000000070000000002100000000000000e000000000a1020000000000012000000000001400000018022010000000006104000000000610400000000000090000000000008000000000001200000000000110000000000004000000000e1020000000000008000000480a201000000000000700000000000040000000085101000000000000200000001041010000000000011
  | 7, 84 => 0x314c42030000000000002000000000a101000000380620000000000021010000000000002000000480a201000000000e1020000053041202000000004010100000000021030000000012100000000000a10200000000000080000000000009000000000a1040000000002101000000190920200000000121010000002802203000000000e102000000000a10000000001081010000052440201000000380220200000000c9104000000000000400000000801010000000000008000000000a104000000380a2020000000000006
  | 7, 85 => 0x11000000000e10200000000021000000000041102000000000a101000000010010000000000121000000000012100000000000a10400000000121020000054081203000000000e104000000000e10200000000000000000000041102000000000000100000104402020000000006103000000000a101000000000a101000000380620000000524402000000000000012000000000a101000000480e202000000000000800000000000080000000000012000000000e10400000000000010000010440201000000000e102
  | 7, 86 => 0x41101000000000e100000000010c10300000000061010000000000003000000000000700000000000040000000000005000000010c100000000000210200000314c4203000000000e1000000000000005000000000000400000000000030000000002105000000000210100000000000110000000084101000000000000900000000000040000000000004000000000610100000000000000000000006101000000000a1000000000000004000000000000400000000c0100000000000000100000000000120000000002101
  | 7, 87 => 0x600000000000070000000000008000000480e20100000000000080000000006104000000000e105000000000210400000000401030000000002103000000000000900000544402010000000002101000000000a1020000000002101000000000e100000000480e203000000000e102000000000e105000000000000500000000061020000000006102000000008510100000000000040000000000008000000010910200000000000050000000012101000000000210000000000061010000000000004000000000000f
  | 7, 88 => 0x4000000010010100000000c91030000000002105000000001210300000000061020000000002101000000000610000000000000120000000000008000000001210200000304c020200000000411020000000000010000000000a104000000000001100000000121040000000000012000000000210000000000000090000052440202000000010010100000000000120000000000002000000000a104000000000210200000000000050000000000000000000000e10600000424c9202000000000210200000000c1103
  | 7, 89 => 0x900000000021000000000000002000000000e1040000000085100000000001210100000000000120000000100101000000000000100000019092020000000002104000000004110300000000121050000000000002000000380620100000000000070000000002103000000000000000000000000090000000002100000000000000000000038022000000000000012000000280220100000000000090000000000004000000480e2030000000081101000000000e1030000000012100000000000e1000000000000002
  | 7, 90 => 0x811010000000081101000000000000900000000000080000000012103000000000210000000000c91020000000000004000000000610000000000000100000000000006000000000000000000000061020000000041101000005244020200000000401010000001909202000000010910200000000061010000000000003000000000001200000000000040000000006104000000000210100000000411000000000000012000000380a202000000000e1030000000012102000000000001200000000000120000000040101
  | 7, 91 => 0x400000000000100000054081203000000000a10600000000000070000000000010000000008510100000000061040000000000012000000000000600000000000100000000002101000000004110100000000000090000000006102000000008010100000000000080000000002102000000000610000000000401010000000000004000000000001200000000121010000000002100000000000000f0000000012104000000000001200000000021030000002806203000000000a101000000000e1020000000006101
  | 7, 92 => 0xe1000000000000009000000000000600000008c92030000000006102000000000e1030000000000006000000001210000000019092020000000012100000000000000000000000121030000000000005000000000a101000000180220300000000061000000000012101000000008110000000000c010200000000000090000000109102000000000000900000000021010000000002103000000000a101000000000000300000000c51020000000002100000000000000400000524c020200000000061040000003806202
  | 7, 93 => 0x841010000000002103000000004010000000000021010000000000009000000000000000000314c4200000000000e10300000000c91020000000000011000000000e100000000001210200000000000130000000000007000000010010100000000000030000004806200000000000001100000000000090000000000009000000000000800000000000040000000000007000000000e1000000000002103000000000001000000000021060000000000008000000000000500000000121010000000040102000000000e100
  | 7, 94 => 0x304c0203000000008510200000000000120000002802201000000000000600000000841010000052041201000000000000700000000000030000000041100000000000000800000000061010000000000004000000180220000000000c510200000000061000000000000007000000000e10000000000000040000000000002000000000a10200000000000020000000012103000000000a10200000000000030000000006101000000000000100000000061020000000006104000000010010100000304c02000000000000004
  | 7, 95 => 0x12000000380a20200000000c11000000000000010000000000a101000000000a1010000000012102000000000001000000000000030000000012104000000000000900000000000070000000012102000000000210200000000c9103000000000001200000000c91020000000012103000000000a1000000000012100000000000000300000000061020000004806201000000000000800000000000090000000080101000000000a10100000000021020000000012100000000000000700000000000080000000041101
  | 7, 96 => 0x58c920300000000000030000000006104000000000a103000000480e20200000000000020000000006104000000008510200000000061050000003802201000000000610100000000000040000002802201000000000000900000000000000000000109102000000480e20000000000121010000000002100000000000a10100000304c020000000104402010000000000004000000010910500000000021010000000000010000000000210200000000000070000000006103000000000000f0000000006102000000000e101
  | 7, 97 => 0x40102000000380a20300000000000040000020480201000000000000500000008c920200000540412000000002802202000000380a200000000000e10300000000021000000000040103000000000210100000000021000000000002102000000000000300000000000070000000081100000000000000900000000000070000000000004000000000000900000000061020000000006101000000000001200000000000000000000000008000000000e1000000000000007000000000000000000000000060000000002101
  | 7, 98 => 0xa101000000000a102000000000000900000324c120300000314c4202000000000001300000314c42000000000002101000000000000200000000121010000004802202000000000e1060000000040101000000000001300000000c51020000000000001000000380a20200000000000020000000000008000000000e1000000003806202000000000000400000000c510200000001091020000000002104000000000210200000000851010000000000007000000280220300000001001010000000000000000000000e102
  | 7, 99 => 0xa101000000380a200000000000610600000534402000000000108101000000000000900000000021060000052440201000000000000100000000c91040000000002101000000280620000000000000000000000000012000000010010000000000000110000003802201000000480e20200000000000080000000000004000000000000700000000121010000000000010000000000000e00000000000010000000000000000000000a10200000000021010000000002102000000000000600000038022030000054440202
  | 7, 100 => 0x12102000000000a10100000000000000000000000009000000000001200000000c911300000000000020000000002104000001044020300000001081010000000006102000000001210000000000061020000000012102
  | 8, 0 => 0x811020000000080101000000000e10200000000000120000000000000000000000610100000000c4100000000000210200000000000010000000000007000000000610200000000c91030000000041101000000000000400000000c41030000000012100000000008110000000000000010000000085103000000000000200000000000040000000104100000000010410100000000411000000000000004000000000e102000000008410100000000000010000000081102000000000000100000000121030000000000003
  | 8, 1 => 0xc01030000000000005000000004010100000000000020000000006102000000000210200000000000040000000000003000000000000100000000811020000000000003000000000000800000000c0103000000010410100000000000020000000000005000000008110300000000000010000000000002000000000000400000000c110300000000811000000000002101000000000e1020000000000000000000000000100000000411000000000000001000000000000300000000000040000000000001000000000a103
  | 8, 2 => 0x8110200000000000120000000000000000000004110200000000000020000000000001000000000000200000000c1102000000000000400000001041030000000000000000000000e10200000000000030000000002102000000000000000000000021030000000000001000000000000400000000000080000000000000000000000210000000000c410200000000000040000000000004000000000000100000001041030000000000003000000000e100000000000a101000000008510100000000000050000000081100
  | 8, 3 => 0x6102000000000a10100000000c41020000000100100000000000000000000000021020000000000001000000000e100000000000610300000000c010000000000061000000000002103000000010c10000000000c91030000000108101000000000a101000000000000200000000061020000000006100000000000e10200000001001030000000000005000000000000900000001001000000000006102000000000e103000000000e10000000001041000000000000006000000000210000000000c91030000000006103
  | 8, 4 => 0xe10300000000000000000000000004000000000000300000000811010000000080101000000000000400000000000060000000000002000000000e101000000000e10200000000000010000000000002000000000e10300000000c110000000000000010000000085103000000000000400000000411020000000000004000000000000200000001001010000000104100000000000610000000000c5103000000000000400000000c910200000000401030000000000000000000000000000000000000050000000085101
  | 8, 5 => 0x3000000000000000000000c4103000000000000100000000411020000000085100000000000000200000000c4100000000000000200000000000070000000104101000000000001200000000000010000000012100000000000000400000000121010000000000009000000000000300000000000090000000000001000000000a100000000010810100000000c4102000000000610200000000000010000000006103000000000000500000000000130000000040102000000000000500000000c0102
  | 8, 6 => 0x20000000006101000000000e1000000000000011000000000210000000000c91000000000000004000000000000500000000000030000000000000000000004110200000000061010000000000000000000010c10300000000c410000000000000080000000002101000000004110300000000000010000000041100000000000000300000000000020000000000012000000000610000000000000050000000000002000000010c10300000000c4102000000000000100000000c110000000000411010000000000000
  | 8, 7 => 0x8000000000000400000000c1102000000000000200000000851000000000000001000000008110000000000000040000000000002000000000000100000000c510000000000000060000000000001000000000610000000000000060000000012102000000008010100000000401000000000000005000000000000100000000121010000000000002000000000001300000000c410200000000000040000000002101000000000a10200000000121000000000000001000000000210300000000021020000000041100
  | 8, 8 => 0x700000000000130000000081103000000004110000000000000090000000000007000000000e102000000010c10000000000000050000000002100000000000001300000000c91000000000000001000000000a10100000000000000000000012103000000000000200000000000050000000000004000000000e102000000008510100000000000040000000000000000000000001200000000021000000000040101000000000000000000000411020000000080101000000000001000000000000090000000000001
  | 8, 9 => 0xe1000000000000003000000000a1010000000000001000000000000100000000c110200000000000010000000000004000000000610200000000c110300000000000120000000012102000000008510000000000000010000000000002000000000001000000000c5100000000000000200000000c510300000000000070000000040100000000000a102000000000000300000000000040000000000010000000000000200000000021000000000002101000000001210300000000000000000000104101
  | 8, 10 => 0x70000000040102000000000000100000000000000000000000009000000001210200000000021010000000012100000000000a10200000000c010300000000c9102000000000000100000000811030000000041102000000000610000000000000010000000006101000000000000400000000000120000000002102000000000000400000000c91020000000100103000000000000000000000000090000000000004000000000000200000000000000000000100100000000010010100000001081010000000000000
  | 8, 11 => 0x10000000000a100000000010010100000000c11030000000012102000000000000400000000c1100000000000a1010000000000012000000000000400000000021030000000000001000000000a1010000000000009000000000a10200000000000000000000006102000000000001000000000851020000000104103000000000000900000000000040000000000002000000000a103000000000000400000000c5102000000000a101000000000000400000000c11020000000000004000000000a1000000000000003
  | 8, 12 => 0x108101000000000e10300000000c51020000000104101000000010c10300000000811000000000000005000000000000700000000061020000000040102000000000a10200000000000030000000040100000000000000000000000c41000000000084101000000010010300000000000010000000100101000000000e10300000000c11000000000006101000000004010300000000000020000000000001000000001210100000000000050000000002102000000000210300000000c9102000000000000400000000c1102
  | 8, 13 => 0x600000000c910000000000c01000000000000001000000000e1030000000002100000000000e103000000000000800000000c0103000000000000400000000000020000000006102000000000000100000000021020000000006103000000000000200000000c9102000000000610300000000c1100000000000000200000000c010000000000c11020000000000012000000000610000000000851020000000041100000000004110100000001001030000000085102000000000610300000000061020000000000002
  | 8, 14 => 0xc51030000000006103000000010010000000000c51000000000000000000000004010300000000000010000000002100000000000e100000000004010000000000c910000000001041000000000000002000000000000500000000000040000000085102000000008410100000000801010000000000001000000000000500000000c51020000000000001000000000210200000000c91020000000040102000000010c1000000000000001000000000210300000000c9103000000000210000000000061000000000000005
  | 8, 15 => 0x4110300000000c4103000000000000300000000000040000000085100000000000210200000000c910200000000c510000000000000050000000000001000000000a10000000000c0100000000004010000000000021020000000006100000000010c103000000000000200000000000020000000002101000000008510200000000c41030000000000013000000010410300000000000030000000104101000000000000200000000c510200000000851030000000041101000000008510000000000401020000000006102
  | 8, 16 => 0x1091020000000000004000000000001200000000061010000000000001000000000610100000000851020000000000001000000000000900000000c510200000000000010000000000004000000004010200000000000020000000041103000000000e102000000010010100000000000010000000000008000000010410000000000000020000000000009000000000a101000000000000800000000000040000000000003000000008110200000000000030000000000001000000000000700000000000010000000100100
  | 8, 17 => 0x400000000c1100000000008110100000000021010000000000004000000000000400000000000100000000041100000000000e1010000000000007000000000000200000000000000000000000001000000000a100000000000a1010000000000004000000001210300000000c410000000001091020000000000000000000000000400000000c0102000000000e10000000000000010000000040101000000000000200000000121010000000000012000000000000800000000061020000000000006
  | 8, 18 => 0x200000000811030000000041102000000000000400000000411010000000000002000000000000200000000000010000000081101000000000000400000000000010000000100101000000000000800000001081010000000000012000000000a1010000000000001000000000000100000000c410200000000c0102000000000001000000000841010000000000004000000000e1000000000000009000000010c10000000000c0102000000000e1000000000000012000000010910200000000000090000000000008
  | 8, 19 => 0x40000000109102000000000210300000000021000000000000000000000000210100000000c91000000000000004000000000e1020000000000001000000000000400000000000120000000000002000000000000000000000c0102000000000a103000000000000000000000000020000000000009000000010c10000000000000050000000081101000000000001300000000c5102000000000001000000001091020000000006100000000000e1010000000006101000000000000200000000000000000000006101
  | 8, 20 => 0x40000000000005000000000610100000001041030000000100103000000010410000000000c01000000000000003000000008510000000000000010000000000002000000000e103000000000e10300000000c5100000000008510100000000c11030000000012101000000004010000000000401010000000000001000000000000000000000c0102000000000001300000000000020000000000001000000000000400000000c0103000000000000400000000c0100000000001210000000000c11030000000000002
  | 8, 21 => 0x400000000000020000000000002000000000210300000000c110000000000c91030000000040101000000000610300000000811000000000000004000000000000300000000000020000000000006000000000a100000000000610000000000c0102000000000610300000000021010000000041101000000000000700000000000010000000104100000000000e102000000000610300000000000040000000000002000000000000200000000000010000000084101000000000000200000000000050000000000004
  | 8, 22 => 0xe10300000000c410300000000000020000000002102000000000e10000000000851030000000000012000000000000100000000c5103000000000000300000000021000000000040103000000000000400000000021030000000000002000000000e1020000000000001000000000000100000000000120000000000012000000000210100000000000080000000041103000000000000000000000000050000000000004000000000000500000000000010000000000001000000000000100000000000020000000085101
  | 8, 23 => 0x2100000000000610000000001001010000000000000000000000a101000000000000400000000000030000000002100000000000000200000000c41020000000100100000000000e100000000000e100000000004110300000000000050000000006100000000000000100000000c41000000000000001000000000000200000000c110200000000000010000000000002000000008110100000000c51030000000002101000000000e1020000000012102000000008110000000000401030000000002103000000000e101
  | 8, 24 => 0x8510000000000000000000000100100000000000000200000000c5100000000010c100000000000e10000000000061020000000000004000000000001200000000811020000000040100000000000e10000000000c910000000000061010000000000001000000000000400000000000120000000000013000000000610100000000000040000000000002000000000e10200000000000050000000000001000000010c1030000000000004000000010c10000000000021000000000108101000000000001300000000c9100
  | 8, 25 => 0x40102000000000000400000000c410000000000000040000000040101000000008110100000000c01000000000080101000000000000200000000000060000000002102000000000e10100000000000020000000000001000000000000200000000000070000000002102000000000000000000000000010000000000000000000000000100000000000100000000006100000000000210100000000000090000000000001000000000001300000000000080000000000001000000000000700000000000030000000000003
  | 8, 26 => 0x200000000000020000000012100000000000000100000000c510200000000c510000000000841010000000085101
  | 9, 0 => 0x300000000000010000000000002000000000000100000000000000000000000003000000000000300000000000010000000000000000000000000100000000000020000000000000000000000000200000000000030000000000000000000000000200000000000020000000000002000000000000000000000000010000000000000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 13 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_47 roots_47 8 s ws hint
  | 1 => checkCutEntry dom_59 roots_59 8 s ws hint
  | 2 => checkCutEntry dom_31_32 roots_31_32 8 s ws hint
  | 3 => checkCutEntry dom_47_16 roots_47_16 8 s ws hint
  | 4 => checkCutEntry dom_55 roots_55 7 s ws hint
  | 5 => checkCutEntry dom_31 roots_31 7 s ws hint
  | 6 => checkCutEntry dom_39_16 roots_39_16 6 s ws hint
  | 7 => checkCutEntry dom_61 roots_61 6 s ws hint
  | 8 => checkCutEntry dom_55_8 roots_55_8 6 s ws hint
  | 9 => checkCutEntry dom_62_1 roots_62_1 6 s ws hint
  | 10 => checkCutEntry dom_15 roots_15 5 s ws hint
  | 11 => checkCutEntry dom_15_16 roots_15_16 5 s ws hint
  | 12 => checkCutEntry dom_23_32 roots_23_32 5 s ws hint
  | 13 => checkCutEntry dom_39 roots_39 5 s ws hint
  | 14 => checkCutEntry dom_39_8 roots_39_8 5 s ws hint
  | 15 => checkCutEntry dom_51_8 roots_51_8 5 s ws hint
  | 16 => checkCutEntry dom_57 roots_57 5 s ws hint
  | 17 => checkCutEntry dom_58_1 roots_58_1 5 s ws hint
  | 18 => checkCutEntry dom_60_1 roots_60_1 5 s ws hint
  | 19 => checkCutEntry dom_23_8 roots_23_8 5 s ws hint
  | 20 => checkCutEntry dom_27 roots_27 5 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_59 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31_32 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_55 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_39_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_61 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_55_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_62_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23_32 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_39 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_39_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_51_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_57 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_58_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_60_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_27 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_63 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := []
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
private theorem z5_0 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_16 : ∀ i, 16 ≤ i → i < 17 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 16 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 17 → Z 5 i = true := (range_split z5_0 z5_16)
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
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_144 : ∀ i, 144 ≤ i → i < 160 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_160 : ∀ i, 160 ≤ i → i < 176 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 160 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_176 : ∀ i, 176 ≤ i → i < 192 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 176 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_192 : ∀ i, 192 ≤ i → i < 208 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 192 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_208 : ∀ i, 208 ≤ i → i < 218 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 10 208 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 218 → Z 6 i = true := (range_split (range_split (range_split (range_split z6_0 z6_16) (range_split z6_32 z6_48)) (range_split (range_split z6_64 z6_80) (range_split z6_96 z6_112))) (range_split (range_split (range_split z6_128 z6_144) (range_split z6_160 z6_176)) (range_split z6_192 z6_208)))
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
private theorem z7_320 : ∀ i, 320 ≤ i → i < 336 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 320 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_336 : ∀ i, 336 ≤ i → i < 352 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 336 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_352 : ∀ i, 352 ≤ i → i < 368 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 352 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_368 : ∀ i, 368 ≤ i → i < 384 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 368 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_384 : ∀ i, 384 ≤ i → i < 400 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 384 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_400 : ∀ i, 400 ≤ i → i < 416 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 400 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_416 : ∀ i, 416 ≤ i → i < 432 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 416 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_432 : ∀ i, 432 ≤ i → i < 448 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 432 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_448 : ∀ i, 448 ≤ i → i < 464 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 448 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_464 : ∀ i, 464 ≤ i → i < 480 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 464 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_480 : ∀ i, 480 ≤ i → i < 496 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 480 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_496 : ∀ i, 496 ≤ i → i < 512 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 496 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_512 : ∀ i, 512 ≤ i → i < 528 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 512 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_528 : ∀ i, 528 ≤ i → i < 544 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 528 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_544 : ∀ i, 544 ≤ i → i < 560 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 544 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_560 : ∀ i, 560 ≤ i → i < 576 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 560 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_576 : ∀ i, 576 ≤ i → i < 585 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 9 576 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 585 → Z 7 i = true := (range_split (range_split (range_split (range_split (range_split (range_split z7_0 z7_16) (range_split z7_32 z7_48)) (range_split (range_split z7_64 z7_80) (range_split z7_96 z7_112))) (range_split (range_split (range_split z7_128 z7_144) (range_split z7_160 z7_176)) (range_split (range_split z7_192 z7_208) (range_split z7_224 z7_240)))) (range_split (range_split (range_split (range_split z7_256 z7_272) (range_split z7_288 z7_304)) (range_split (range_split z7_320 z7_336) (range_split z7_352 z7_368))) (range_split (range_split (range_split z7_384 z7_400) (range_split z7_416 z7_432)) (range_split (range_split z7_448 z7_464) (range_split z7_480 z7_496))))) (range_split (range_split (range_split z7_512 z7_528) (range_split z7_544 z7_560)) z7_576))
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
private theorem z8_160 : ∀ i, 160 ≤ i → i < 176 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 160 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_176 : ∀ i, 176 ≤ i → i < 192 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 176 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_192 : ∀ i, 192 ≤ i → i < 208 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 192 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_208 : ∀ i, 208 ≤ i → i < 224 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 208 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_224 : ∀ i, 224 ≤ i → i < 240 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 224 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_240 : ∀ i, 240 ≤ i → i < 248 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 240 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 248 → Z 8 i = true := (range_split (range_split (range_split (range_split z8_0 z8_16) (range_split z8_32 z8_48)) (range_split (range_split z8_64 z8_80) (range_split z8_96 z8_112))) (range_split (range_split (range_split z8_128 z8_144) (range_split z8_160 z8_176)) (range_split (range_split z8_192 z8_208) (range_split z8_224 z8_240))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_0 : ∀ i, 0 ≤ i → i < 16 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_16 : ∀ i, 16 ≤ i → i < 23 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 7 16 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 23 → Z 9 i = true := (range_split z9_0 z9_16)
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

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 15]⟩], 16⟩

theorem wit_mono : PEqualNP.MetaComplexity.Monotone2 wit := by
  simp [wit, PEqualNP.MetaComplexity.Monotone2]

theorem wit_sz : wit.size ≤ 11 := by decide

set_option maxRecDepth 40000 in
theorem wit_ev : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = Nat.testBit (4008372968 * 2 ^ 32 + 4004047016) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel

set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_63.testBit r.val = (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 4004047016) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) (pt6 r.val) := by decide +kernel

theorem lower : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 4004047016) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) t → 11 ≤ t :=
  lower_to_circuit6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 4004047016) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) goal_63 11 hT6 (by unfold IsConst; decide) low_63

end PEqualNP.Outside.L_meta_38501_aux

theorem PEqualNP.Outside.L_meta_38501 :
  ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 4004047016) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372968 * 2 ^ 32 + 4004047016) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  exact ⟨PEqualNP.Outside.L_meta_38501_aux.wit, PEqualNP.Outside.L_meta_38501_aux.wit_mono, le_trans PEqualNP.Outside.L_meta_38501_aux.wit_sz (PEqualNP.Outside.L_meta_38501_aux.lower s hs), PEqualNP.Outside.L_meta_38501_aux.wit_ev⟩
