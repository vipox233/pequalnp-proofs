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

namespace PEqualNP.Outside.L_meta_41598_aux

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

def dom_31 : Nat := 0xffffffff
def goal_31 : Nat := 0xfae8e8e0fae8e8e0fae8e8e0fae8e8e0fae8e8e0fae8e8e0fae8e8e0fae8e8e0
def roots_31 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xeeeeeeaaaa888800eeeeeeaaaa888800eeeeeeaaaa888800eeeeeeaaaa888800
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_47_16 : Nat := 0xffff0000ffff0000
def goal_47_16 : Nat := 0xfeeefeeefae8fae8feeefeeefae8fae8feeefeeefae8fae8feeefeeefae8fae8
def roots_47_16 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_31_32 : Nat := 0xffffffff00000000
def goal_31_32 : Nat := 0xfeeeeeeafeeeeeeafeeeeeeafeeeeeeafeeeeeeafeeeeeeafeeeeeeafeeeeeea
def roots_31_32 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_62 : Nat := 0x5555555555555555
def goal_62 : Nat := 0xfcccccc0f0c0c0c0fcccccc0f0c0c0c0fcccccc0f0c0c0c0fcccccc0f0c0c0c0
def roots_62 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xeeeaeeeae8e0e8e0eeeaeeeae8e0e8e0eeeaeeeae8e0e8e0eeeaeeeae8e0e8e0
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_30_32 : Nat := 0x5555555500000000
def goal_30_32 : Nat := 0xfcccccc0fcccccc0fcccccc0fcccccc0fcccccc0fcccccc0fcccccc0fcccccc0
def roots_30_32 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfaaaaaaafaa0a0a0faaaaaaafaa0a0a0faaaaaaafaa0a0a0faaaaaaafaa0a0a0
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61_2 : Nat := 0xcccccccccccccccc
def goal_61_2 : Nat := 0xfffffffafafafaf0fffffffafafafaf0fffffffafafafaf0fffffffafafafaf0
def roots_61_2 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_62_1 : Nat := 0xaaaaaaaaaaaaaaaa
def goal_62_1 : Nat := 0xfffffffffffcfcf0fffffffffffcfcf0fffffffffffcfcf0fffffffffffcfcf0
def roots_62_1 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_15 : Nat := 0xffff
def goal_15 : Nat := 0xe8e0e8e0e8e0e8e0e8e0e8e0e8e0e8e0e8e0e8e0e8e0e8e0e8e0e8e0e8e0e8e0
def roots_15 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0]

def dom_27 : Nat := 0xf0f0f0f
def goal_27 : Nat := 0xaa888800aa888800aa888800aa888800aa888800aa888800aa888800aa888800
def roots_27 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_45_16 : Nat := 0x3333000033330000
def goal_45_16 : Nat := 0xfaaafaaafaa0faa0faaafaaafaa0faa0faaafaaafaa0faa0faaafaaafaa0faa0
def roots_45_16 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_45_2 : Nat := 0xcccc0000cccc
def goal_45_2 : Nat := 0xfffafffafaf0faf0fffafffafaf0faf0fffafffafaf0faf0fffafffafaf0faf0
def roots_45_2 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_55_8 : Nat := 0xff00ff00ff00ff00
def goal_55_8 : Nat := 0xfefeeeeefafae8e8fefeeeeefafae8e8fefeeeeefafae8e8fefeeeeefafae8e8
def roots_55_8 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xeeeeeaeae8e8e0e0eeeeeaeae8e8e0e0eeeeeaeae8e8e0e0eeeeeaeae8e8e0e0
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_23 : Nat := 0xff00ff
def goal_23 : Nat := 0xe8e8e0e0e8e8e0e0e8e8e0e0e8e8e0e0e8e8e0e0e8e8e0e0e8e8e0e0e8e8e0e0
def roots_23 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0]

def dom_53_8 : Nat := 0x3300330033003300
def goal_53_8 : Nat := 0xfafaaaaafafaa0a0fafaaaaafafaa0a0fafaaaaafafaa0a0fafaaaaafafaa0a0
def roots_53_8 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_53_2 : Nat := 0xcc00cc00cc00cc
def goal_53_2 : Nat := 0xfffffafafafaf0f0fffffafafafaf0f0fffffafafafaf0f0fffffafafafaf0f0
def roots_53_2 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_30_1 : Nat := 0xaaaaaaaa
def goal_30_1 : Nat := 0xfffcfcf0fffcfcf0fffcfcf0fffcfcf0fffcfcf0fffcfcf0fffcfcf0fffcfcf0
def roots_30_1 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_58_1 : Nat := 0xa0a0a0a0a0a0a0a
def goal_58_1 : Nat := 0xffffffffffcccc00ffffffffffcccc00ffffffffffcccc00ffffffffffcccc00
def roots_58_1 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfeeeeeeafae8e8e0feeeeeeafae8e8e0feeeeeeafae8e8e0feeeeeeafae8e8e0
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

namespace S_31
def pairsG : List (Nat × Nat) := [(1, 5), (2, 6), (3, 7), (3, 11), (3, 19), (4, 5), (4, 6), (9, 11), (9, 13), (9, 25), (10, 11), (10, 14), (12, 13), (12, 14), (12, 28), (17, 19), (17, 21), (17, 25), (18, 19), (18, 22), (20, 21), (20, 22), (20, 28), (24, 25), (24, 28), (26, 27), (26, 30)]
def r1sG : List Nat := [1, 2, 3, 3, 3, 4, 4, 9, 9, 9, 10, 10, 12, 12, 12, 17, 17, 17, 18, 18, 20, 20, 20, 24, 24, 26, 26]
def r2sG : List Nat := [5, 6, 7, 11, 19, 5, 6, 11, 13, 25, 11, 14, 13, 14, 28, 19, 21, 25, 19, 22, 21, 22, 28, 25, 28, 27, 30]
def mpG : Nat := 0x7ffffff
def pool6G : List Nat := [4402509972997, 9908776407819, 4402745972997, 4402644715013, 4411099907589, 9912953013765, 18730403957529, 13232962733573, 4406788162822, 19864291247379, 18709180777989]
def xsM : List Nat := roots_31.map (· &&& dom_31)
def goalM : Nat := goal_31 &&& dom_31
def NN : Nat → Nat
  | 4 => 3
  | 5 => 29
  | 6 => 23
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xac05225e97a62e987ebc43de
  | 5, 0 => 0xf671b849f0b2ef13e1005450de66a692d591247cc72c2e23be3fb924ac05225ea571db929e9c03b28c616cec81ea162e64d480335e90018e5e1d4aa85d1936d05299e96d526e44fc4ca6240746836c3c3a6b8d413649f21e32f633fb2637312d25e0cf661f6c5e8b1d34fcbf1ac7d7cf15863287
  | 6, 0 => 0xfd575aabf27aa6a5d051f507be3fb924be3a6442b4992a82ac05225ea0508cfd93c0f7228c616cec818360617ecfa1837702c5a9744473ec554c825e5299e96d3a6b8d4130706e42276bea43206585ea1b8a7ef1126b25b70241d3e1
  | 7, 0 => 0xac05225e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xaa00aa0000000000000000000000000000000000000000000000000000000000a0a0a0a0000000000000000000000000000000000000000000000000000000008888888800000000000000000000000000000000000000000000000000000000555555550000000000000000000000000000000000000000000000000000000033333333000000000000000000000000000000000000000000000000000000000f0f0f0f0000000000000000000000000000000000000000000000000000000000ff00ff000000000000000000000000000000000000000000000000000000000000ffff
  | 0, 1 => 0xecececec00000000000000000000000000000000000000000000000000000000eaeaeaea00000000000000000000000000000000000000000000000000000000cccccccc00000000000000000000000000000000000000000000000000000000cc00cc0000000000000000000000000000000000000000000000000000000000c8c8c8c800000000000000000000000000000000000000000000000000000000c0c0c0c000000000000000000000000000000000000000000000000000000000aaaaaaaa00000000000000000000000000000000000000000000000000000000aaaa0000
  | 0, 2 => 0xff00000000000000000000000000000000000000000000000000000000000000fcfcfcfc00000000000000000000000000000000000000000000000000000000fafafafa00000000000000000000000000000000000000000000000000000000fa00fa0000000000000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000eeeeeeee
  | 0, 3 => 0xffccff0000000000000000000000000000000000000000000000000000000000ffcccccc00000000000000000000000000000000000000000000000000000000ffcc000000000000000000000000000000000000000000000000000000000000ffc0ffc000000000000000000000000000000000000000000000000000000000ffaaffaa00000000000000000000000000000000000000000000000000000000ffaa000000000000000000000000000000000000000000000000000000000000ffa0ffa000000000000000000000000000000000000000000000000000000000ff00ff00
  | 0, 4 => 0xffffff0000000000000000000000000000000000000000000000000000000000fffff0f000000000000000000000000000000000000000000000000000000000ffffcccc00000000000000000000000000000000000000000000000000000000ffffcc0000000000000000000000000000000000000000000000000000000000ffffaaaa00000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000fff0fff000000000000000000000000000000000000000000000000000000000ffccffcc
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x2261334950257d325009de4c94
  | 5, 0, 0 => 0x89e613256285134959184cd256260d24258984d0156261310356984cd256261334458994cd2562349081589854d196251334957584cd25626132c9589334405627133495
  | 5, 0, 1 => 0x226133c9589858a256260d10259d74cd25626d334758984ce356261324358984cd2553349040589324305624cd24158a04cc25626090c25
  | 6, 0, 0 => 0x8984cd245689859334960224cd24159a261334968984cd24369e261334968984cd28968984cd248602260d242502261334458a061334968e2613349689855334968984cd24068984cd30968984d23496
  | 6, 0, 1 => 0x8984cd24268984cd24668984cd244602261324358985d334968984d034960226133495
  | 7, 0, 0 => 0x226133495
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
  | 0, 0 => 0x3800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001c0000000000000000000000000000000000000000000000000000000007fc7c620000000000000000000000000000000000000000000000000000000001f3f3e100000000000000000000000000000000000000000000000000000000078f8f9f00000000000000000000000000000000000000000000000000000000007f807f0000000000000000000000000000000000000000000000000000000000007fff
  | 0, 1 => 0x60c0c1e000000000000000000000000000000000000000000000000000000000003839d00000000000000000000000000000000000000000000000000000000060c0c1e0000000000000000000000000000000000000000000000000000000006000c00000000000000000000000000000000000000000000000000000000000000001c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003839d0000000000000000000000000000000000000000000000000000000000038000
  | 0, 2 => 0x780000000000000000000000000000000000000000000000000000000000000067c7c7e000000000000000000000000000000000000000000000000000000000073f3fd000000000000000000000000000000000000000000000000000000000000738000000000000000000000000000000000000000000000000000000000007070600000000000000000000000000000000000000000000000000000000000700000000000000000000000000000000000000000000000000000000000000000700000000000000000000000000000000000000000000000000000000000060f8f9f
  | 0, 3 => 0x78c7f8000000000000000000000000000000000000000000000000000000000078c0c1e00000000000000000000000000000000000000000000000000000000078c00000000000000000000000000000000000000000000000000000000000007807f80000000000000000000000000000000000000000000000000000000000783ff9d00000000000000000000000000000000000000000000000000000000078380000000000000000000000000000000000000000000000000000000000007807f800000000000000000000000000000000000000000000000000000000007807f80
  | 0, 4 => 0x7ffff800000000000000000000000000000000000000000000000000000000007fff0600000000000000000000000000000000000000000000000000000000007ff8c1e0000000000000000000000000000000000000000000000000000000007ff8c000000000000000000000000000000000000000000000000000000000007ff839d0000000000000000000000000000000000000000000000000000000007ff80000000000000000000000000000000000000000000000000000000000007f07fe000000000000000000000000000000000000000000000000000000000078c7f9e
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x28217880000000000000000000000000000000000000000000000000000000000111125000000000000000000000000000000000000000000000000000000000204849c00000000000000000000000000000000000000000000000000000000056868420000000000000000000000000000000000000000000000000000000001d35321000000000000000000000000000000000000000000000000000000000286869800000000000000000000000000000000000000000000000000000000003d80770000000000000000000000000000000000000000000000000000000000003def
  | 0, 1 => 0x63dbdff0000000000000000000000000000000000000000000000000000000006bfbfff00000000000000000000000000000000000000000000000000000000062cacde0000000000000000000000000000000000000000000000000000000006002c8800000000000000000000000000000000000000000000000000000000062cacde000000000000000000000000000000000000000000000000000000000428284600000000000000000000000000000000000000000000000000000000029797bd0000000000000000000000000000000000000000000000000000000002978210
  | 0, 2 => 0x7c2420000000000000000000000000000000000000000000000000000000000077dfdff0000000000000000000000000000000000000000000000000000000007ffffff0000000000000000000000000000000000000000000000000000000007c27f880000000000000000000000000000000000000000000000000000000005797967000000000000000000000000000000000000000000000000000000000579400000000000000000000000000000000000000000000000000000000000054079000000000000000000000000000000000000000000000000000000000006bfbfff
  | 0, 3 => 0x7eeff980000000000000000000000000000000000000000000000000000000007eeeede0000000000000000000000000000000000000000000000000000000007eec2100000000000000000000000000000000000000000000000000000000007ea7fce0000000000000000000000000000000000000000000000000000000007d7ffbd0000000000000000000000000000000000000000000000000000000007d7c2100000000000000000000000000000000000000000000000000000000007d37fad0000000000000000000000000000000000000000000000000000000007c27f88
  | 0, 4 => 0x7ffff980000000000000000000000000000000000000000000000000000000007fffb770000000000000000000000000000000000000000000000000000000007ffeede0000000000000000000000000000000000000000000000000000000007ffee980000000000000000000000000000000000000000000000000000000007ffd7bd0000000000000000000000000000000000000000000000000000000007ffc2100000000000000000000000000000000000000000000000000000000007fb7fef0000000000000000000000000000000000000000000000000000000007eeffde
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 40 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 40 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 40 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 40 then wireAt i else 0
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_31 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_31 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
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
private theorem z5_0 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_16 : ∀ i, 16 ≤ i → i < 29 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 13 16 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 29 → Z 5 i = true := (range_split z5_0 z5_16)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 16 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_16 : ∀ i, 16 ≤ i → i < 23 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 7 16 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 23 → Z 6 i = true := (range_split z6_0 z6_16)
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
def pairsG : List (Nat × Nat) := [(1, 33), (3, 11), (3, 19), (3, 35), (9, 11), (9, 25), (9, 41), (10, 11), (10, 42), (17, 19), (17, 25), (17, 49), (18, 19), (18, 50), (24, 25), (26, 27), (26, 58), (32, 33), (34, 35), (34, 42), (34, 50), (40, 41), (40, 42), (48, 49), (48, 50), (56, 57), (56, 58)]
def r1sG : List Nat := [1, 3, 3, 3, 9, 9, 9, 10, 10, 17, 17, 17, 18, 18, 24, 26, 26, 32, 34, 34, 34, 40, 40, 48, 48, 56, 56]
def r2sG : List Nat := [33, 11, 19, 35, 11, 25, 41, 11, 42, 19, 25, 49, 19, 50, 25, 27, 58, 33, 35, 42, 50, 41, 42, 49, 50, 57, 58]
def mpG : Nat := 0x7ffffff
def pool6G : List Nat := [9908776407819, 18730403957529, 18704735210259, 11008574365963, 19804667912467, 11034444833035, 28600760410379, 37426397514538, 18735455936787, 19865032335635, 35188837583649, 18730926090777]
def xsM : List Nat := roots_59.map (· &&& dom_59)
def goalM : Nat := goal_59 &&& dom_59
def NN : Nat → Nat
  | 4 => 3
  | 5 => 29
  | 6 => 23
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xc38274816110326e1345fe16
  | 5, 0 => 0xf3a9eb6beaaab64ac3827481c1228dd0ba0f5bffb9d56310b9879e319cb3f76c97d3497293b906c5925f5c68916a454f8c5020338bab304b73d47726693692455f210ebd4cac355d38efa4c337f8ccf437ce546a26f145cd26bc2b5e1ba5db2b1b891d4416a6bae609710d2b06d5b4db061f7558
  | 6, 0 => 0xfdfe6beeeaaab64ac6eafbb0c3827481a4e07297a17346f292fd4275925f5c6887084d0275bef6de72783b7e6e9b733a6c35459f6b87e637652e56205a3c9a365878c3dd4cac355d418db97037f8ccf42a5942f414d4acce006bb7a1
  | 7, 0 => 0xc3827481
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xa0a0a0a000000000000000000000000000000000000000000000000000000000a0a00000a0a0000000000000000000000000000000000000000000000000000080808080808080800000000000000000000000000000000000000000000000005050505050505050000000000000000000000000000000000000000000000000303030303030303000000000000000000000000000000000000000000000000000f000f000f000f00000000000000000000000000000000000000000000000000000f0f00000f0f000000000000000000000000000000000000000000000000000000000f0f0f0f
  | 0, 1 => 0xe000e000e000e000000000000000000000000000000000000000000000000000c0c0c0c0c0c0c0c0000000000000000000000000000000000000000000000000c0c0c0c080808080000000000000000000000000000000000000000000000000c0c0c0c000000000000000000000000000000000000000000000000000000000c0c0c000c0c0c000000000000000000000000000000000000000000000000000c0c00000c0c00000000000000000000000000000000000000000000000000000c000c000c000c000000000000000000000000000000000000000000000000000a0a0a0a0a0a0a0a
  | 0, 2 => 0xf0c00000f0c00000000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000f000f000a000a000000000000000000000000000000000000000000000000000f000c000f000c000000000000000000000000000000000000000000000000000f0000000f0000000000000000000000000000000000000000000000000000000e0e0e0e0e0e0e0e0000000000000000000000000000000000000000000000000e0e0e0e0c0c0c0c0000000000000000000000000000000000000000000000000e0e0e0e00000000
  | 0, 3 => 0xf0f0f000f0f0f000000000000000000000000000000000000000000000000000f0f0f000f000f000000000000000000000000000000000000000000000000000f0f0c0c0f0f0c0c0000000000000000000000000000000000000000000000000f0f0c000f0f0c000000000000000000000000000000000000000000000000000f0f0a0a0f0f0a0a0000000000000000000000000000000000000000000000000f0f0a0a0f0f00000000000000000000000000000000000000000000000000000f0f00000f0f00000000000000000000000000000000000000000000000000000f0f000000000000
  | 0, 4 => 0xf0f0f0f0f0f00000000000000000000000000000000000000000000000000000f0f0f0f0f000f000000000000000000000000000000000000000000000000000f0f0f0f0c0c0c0c0000000000000000000000000000000000000000000000000f0f0f0f0a0a0a0a0000000000000000000000000000000000000000000000000f0f0f0f00000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x2065638850205c921008132c84
  | 5, 0, 0 => 0x81a58e215958e10058193ce2156388040581958e116065634858163880560654388581b58e19607d3388565640e2160656103581954e2160756288581620305646163885
  | 5, 0, 1 => 0x226563085656388016065638858163840560388081581959121595880c0581c58e216165638758195921560656203581958b21607993885
  | 6, 0, 0 => 0x20656203581961638868a0656388681d656388681958e205681958e308681958e2016860656388681b656388681958e248602065638458e0656388602058e201581958e204681958e20068195933886
  | 6, 0, 1 => 0x81958e207601958e20058195923886020656388581f656388681958e206681958e2036
  | 7, 0, 0 => 0x206563885
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
  | 0, 0 => 0xe00000000000000000000000000000000000000000000000000000000000000000e0000000000000000000000000000000000000000000000000000000007fff1800000000000000000000000000000000000000000000000000000000007e24e7100000000000000000000000000000000000000000000000000000000019e3e0f00000000000000000000000000000000000000000000000000000000007e01ff000000000000000000000000000000000000000000000000000000000001ffff
  | 0, 1 => 0x181f000000000000000000000000000000000000000000000000000000000001db18e00000000000000000000000000000000000000000000000000000000001c000e00000000000000000000000000000000000000000000000000000000001c0000000000000000000000000000000000000000000000000000000000000001b180000000000000000000000000000000000000000000000000000000000001b00000000000000000000000000000000000000000000000000000000000000181800000000000000000000000000000000000000000000000000000000000000e7f
  | 0, 2 => 0x601f000000000000000000000000000000000000000000000000000000000000661c1f00000000000000000000000000000000000000000000000000000000006600070000000000000000000000000000000000000000000000000000000000601c180000000000000000000000000000000000000000000000000000000000601c00000000000000000000000000000000000000000000000000000000000001dbfff00000000000000000000000000000000000000000000000000000000001db18e00000000000000000000000000000000000000000000000000000000001c0000
  | 0, 3 => 0x7e1fff00000000000000000000000000000000000000000000000000000000007e1c1f000000000000000000000000000000000000000000000000000000000079dff8e000000000000000000000000000000000000000000000000000000000781ff80000000000000000000000000000000000000000000000000000000000781fe7f000000000000000000000000000000000000000000000000000000000781fe00000000000000000000000000000000000000000000000000000000000781fe000000000000000000000000000000000000000000000000000000000007800000
  | 0, 4 => 0x7fffe000000000000000000000000000000000000000000000000000000000007ffc1f00000000000000000000000000000000000000000000000000000000007ffb18e0000000000000000000000000000000000000000000000000000000007fe0e7f0000000000000000000000000000000000000000000000000000000007fe0000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x2a60849000000000000000000000000000000000000000000000000000000000280de24000000000000000000000000000000000000000000000000000000000004929e00000000000000000000000000000000000000000000000000000000055921000000000000000000000000000000000000000000000000000000000002a24c610000000000000000000000000000000000000000000000000000000001963a0d00000000000000000000000000000000000000000000000000000000006e01db000000000000000000000000000000000000000000000000000000000000d6b6
  | 0, 1 => 0x669c5f200000000000000000000000000000000000000000000000000000000055db39e00000000000000000000000000000000000000000000000000000000055db39e00000000000000000000000000000000000000000000000000000000055d2108000000000000000000000000000000000000000000000000000000000559b396000000000000000000000000000000000000000000000000000000000511b20400000000000000000000000000000000000000000000000000000000044981920000000000000000000000000000000000000000000000000000000002a6deff
  | 0, 2 => 0x711f624000000000000000000000000000000000000000000000000000000000669c5f2000000000000000000000000000000000000000000000000000000000669c5f2000000000000000000000000000000000000000000000000000000000649c5b2000000000000000000000000000000000000000000000000000000000601c4200000000000000000000000000000000000000000000000000000000007ffffff0000000000000000000000000000000000000000000000000000000007ffbbdf0000000000000000000000000000000000000000000000000000000007ff2949
  | 0, 3 => 0x7f9fff60000000000000000000000000000000000000000000000000000000007f9edf20000000000000000000000000000000000000000000000000000000007ddffbe0000000000000000000000000000000000000000000000000000000007d9ffb60000000000000000000000000000000000000000000000000000000007b7feff0000000000000000000000000000000000000000000000000000000007b7fe6d000000000000000000000000000000000000000000000000000000000791fe240000000000000000000000000000000000000000000000000000000007912800
  | 0, 4 => 0x7ffff6d0000000000000000000000000000000000000000000000000000000007ffedfb0000000000000000000000000000000000000000000000000000000007ffbbdf0000000000000000000000000000000000000000000000000000000007ffffff0000000000000000000000000000000000000000000000000000000007ff2949
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 37 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 37 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 37 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 37 then wireAt i else 0
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
private theorem z5_16 : ∀ i, 16 ≤ i → i < 29 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 13 16 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 29 → Z 5 i = true := (range_split z5_0 z5_16)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 16 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_16 : ∀ i, 16 ≤ i → i < 23 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 7 16 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 23 → Z 6 i = true := (range_split z6_0 z6_16)
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

namespace S_47_16
def pairsG : List (Nat × Nat) := [(17, 19), (17, 21), (17, 25), (17, 49), (18, 19), (18, 22), (18, 50), (20, 21), (20, 22), (20, 28), (24, 25), (24, 28), (26, 27), (26, 30), (26, 58), (48, 49), (48, 50), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [17, 17, 17, 17, 18, 18, 18, 20, 20, 20, 24, 24, 26, 26, 26, 48, 48, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [19, 21, 25, 49, 19, 22, 50, 21, 22, 28, 25, 28, 27, 30, 58, 49, 50, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0x7fffff
def pool6G : List Nat := [22063550436117, 19864560735507, 26474465269020, 52854155973426, 26461630895385]
def xsM : List Nat := roots_47_16.map (· &&& dom_47_16)
def goalM : Nat := goal_47_16 &&& dom_47_16
def NN : Nat → Nat
  | 4 => 1
  | 5 => 5
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x73240d52
  | 5, 0 => 0xd7c737eb73240d521b7e40381a28733105dfb75b
  | 6, 0 => 0x73240d52
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffff000000000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000f0f00000f0f00000000000000000000000000000000000000000000000000000cccc0000cccc0000000000000000000000000000000000000000000000000000aaaa0000aaaa00000000000000000000000000000000000000000000000000005555000055550000000000000000000000000000000000000000000000000000333300003333000000000000000000000000000000000000000000000000000000ff000000ff0000
  | 0, 1 => 0xffff0000f0f00000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x765435
  | 5, 0, 0 => 0x765425765435765315865435754305
  | 6, 0, 0 => 0x765435
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
  | 0, 0 => 0x7f80000000000000000000000000000000000000000000000000000000000000707c0000000000000000000000000000000000000000000000000000000000000e03800000000000000000000000000000000000000000000000000000000000007070000000000000000000000000000000000000000000000000000000000000000f00000000000000000000000000000000000000000000000000000000007ffff000000000000000000000000000000000000000000000000000000000007f8f8f00000000000000000000000000000000000000000000000000000000000f83ff
  | 0, 1 => 0x7f8380
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x7fc0480000000000000000000000000000000000000000000000000000000000787e0400000000000000000000000000000000000000000000000000000000004e2ba20000000000000000000000000000000000000000000000000000000000257171000000000000000000000000000000000000000000000000000000000012949f00000000000000000000000000000000000000000000000000000000006d6b6000000000000000000000000000000000000000000000000000000000005a8e8e00000000000000000000000000000000000000000000000000000000000781fb
  | 0, 1 => 0x7febea
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_47_16 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_47_16 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]]
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
  scr dom_47_16 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_47_16 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_47_16 roots_47_16 goal_47_16 7 := by
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

theorem low_47_16 : Lower dom_47_16 roots_47_16 goal_47_16 7 := S_47_16.noCircuit

namespace S_31_32
def pairsG : List (Nat × Nat) := [(32, 33), (34, 35), (34, 38), (34, 42), (34, 50), (36, 37), (36, 38), (40, 41), (40, 42), (44, 45), (44, 46), (44, 60), (48, 49), (48, 50), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [32, 34, 34, 34, 34, 36, 36, 40, 40, 44, 44, 44, 48, 48, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [33, 35, 38, 42, 50, 37, 38, 41, 42, 45, 46, 60, 49, 50, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0xfffff
def pool6G : List Nat := [39729390955046, 44127370354986, 61796562642492, 44127370356266, 48525416867370, 44127370359338, 48525483977254, 39729390957094, 52923329160754]
def xsM : List Nat := roots_31_32.map (· &&& dom_31_32)
def goalM : Nat := goal_31_32 &&& dom_31_32
def NN : Nat → Nat
  | 4 => 2
  | 5 => 6
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x5f5ce3515d84b26c
  | 5, 0 => 0xda60a3d7b740b46e7523d75b608578e95f5ce3514a9e6e6a
  | 6, 0 => 0x5f5ce351
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xfafafafa00000000000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000eeeeeeee00000000000000000000000000000000000000000000000000000000cccccccc00000000000000000000000000000000000000000000000000000000aaaaaaaa00000000000000000000000000000000000000000000000000000000555555550000000000000000000000000000000000000000000000000000000033333333000000000000000000000000000000000000000000000000000000000000ffff00000000
  | 0, 1 => 0xffff000000000000000000000000000000000000000000000000000000000000ffaaffaa00000000000000000000000000000000000000000000000000000000ff00ff0000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0xa864350a9654
  | 5, 0, 0 => 0xa86535a86315a86425864305a86435a87435
  | 6, 0, 0 => 0xa86435
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
  | 0, 0 => 0x1ce60000000000000000000000000000000000000000000000000000000000001ce60000000000000000000000000000000000000000000000000000000000000001e000000000000000000000000000000000000000000000000000000000000001e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000fffff00000000000000000000000000000000000000000000000000000000000fffe10000000000000000000000000000000000000000000000000000000000000fff
  | 0, 1 => 0xff00000000000000000000000000000000000000000000000000000000000000e0f8000000000000000000000000000000000000000000000000000000000000e0f80
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xbdee7000000000000000000000000000000000000000000000000000000000009ce64000000000000000000000000000000000000000000000000000000000006f7ff000000000000000000000000000000000000000000000000000000000004a55e00000000000000000000000000000000000000000000000000000000000252a300000000000000000000000000000000000000000000000000000000000dad5c00000000000000000000000000000000000000000000000000000000000b5aa100000000000000000000000000000000000000000000000000000000000007ef
  | 0, 1 => 0xff81000000000000000000000000000000000000000000000000000000000000f5fab00000000000000000000000000000000000000000000000000000000000f0f88
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 11 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 11 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 11 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 11 then wireAt i else 0
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_31_32 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_31_32 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)]]
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
private theorem z4_0 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 6 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 0 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 6 → Z 5 i = true := z5_0
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
  scr dom_31_32 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_31_32 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_31_32 roots_31_32 goal_31_32 7 := by
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

theorem low_31_32 : Lower dom_31_32 roots_31_32 goal_31_32 7 := S_31_32.noCircuit

namespace S_62
def pairsG : List (Nat × Nat) := [(2, 6), (4, 6), (10, 14), (10, 42), (12, 14), (12, 28), (18, 22), (18, 50), (20, 22), (20, 28), (24, 28), (26, 30), (26, 58), (34, 38), (34, 42), (34, 50), (36, 38), (40, 42), (44, 46), (44, 60), (48, 50), (52, 54), (52, 60), (56, 58), (56, 60)]
def r1sG : List Nat := [2, 4, 10, 10, 12, 12, 18, 18, 20, 20, 24, 26, 26, 34, 34, 34, 36, 40, 44, 44, 48, 52, 52, 56, 56]
def r2sG : List Nat := [6, 6, 14, 42, 14, 28, 22, 50, 22, 28, 28, 30, 58, 38, 42, 50, 38, 42, 46, 60, 50, 54, 60, 58, 60]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := [26474751591964, 37401517497350, 28673774847516, 22042345875996, 13203671751686, 4407579253766, 11013238430726, 52922790184498, 19809331452934, 44126831380010]
def xsM : List Nat := roots_62.map (· &&& dom_62)
def goalM : Nat := goal_62 &&& dom_62
def NN : Nat → Nat
  | 4 => 2
  | 5 => 7
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xa91103de6065dbdd
  | 5, 0 => 0xe324ca91deee3556c894e17ca91103de45028db10ebf8666009ef5f6
  | 6, 0 => 0xa91103de
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x50505050505050500000000000000000000000000000000000000000000000004444444444444444000000000000000000000000000000000000000000000000444444444040404000000000000000000000000000000000000000000000000044444444000000000000000000000000000000000000000000000000000000001111111111111111000000000000000000000000000000000000000000000000050505050505050500000000000000000000000000000000000000000000000000005555000055550000000000000000000000000000000000000000000000000000000055555555
  | 0, 1 => 0x5555555550505050000000000000000000000000000000000000000000000000555555550000000000000000000000000000000000000000000000000000000055550000555500000000000000000000000000000000000000000000000000005500550055005500
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0xa98765098754
  | 5, 0, 0 => 0x987605a98735987645a98765a98625a87615b98765
  | 6, 0, 0 => 0xa98765
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
  | 0, 0 => 0x6d0332000000000000000000000000000000000000000000000000000000000000f8cd000000000000000000000000000000000000000000000000000000000000e000000000000000000000000000000000000000000000000000000000000000e0000000000000000000000000000000000000000000000000000000000001ff0732000000000000000000000000000000000000000000000000000000000192fccd00000000000000000000000000000000000000000000000000000000000fe03f0000000000000000000000000000000000000000000000000000000000001fff
  | 0, 1 => 0x1ffe3320000000000000000000000000000000000000000000000000000000001ffe0000000000000000000000000000000000000000000000000000000000001f01fc000000000000000000000000000000000000000000000000000000000018e1c3c
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x16d2f770000000000000000000000000000000000000000000000000000000000b7f9df0000000000000000000000000000000000000000000000000000000000b7f9df0000000000000000000000000000000000000000000000000000000000b7f0880000000000000000000000000000000000000000000000000000000001480620000000000000000000000000000000000000000000000000000000000092d088000000000000000000000000000000000000000000000000000000000007601f0000000000000000000000000000000000000000000000000000000000000f77
  | 0, 1 => 0x1ffffff0000000000000000000000000000000000000000000000000000000001fff0880000000000000000000000000000000000000000000000000000000001f89fe00000000000000000000000000000000000000000000000000000000001ce5e3c
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 12 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 12 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 12 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 12 then wireAt i else 0
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_62 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_62 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
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
private theorem z5_0 : ∀ i, 0 ≤ i → i < 7 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 7 0 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 7 → Z 5 i = true := z5_0
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
  scr dom_62 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_62 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_62 roots_62 goal_62 7 := by
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

theorem low_62 : Lower dom_62 roots_62 goal_62 7 := S_62.noCircuit

namespace S_47
def pairsG : List (Nat × Nat) := [(1, 5), (1, 33), (2, 6), (3, 7), (3, 11), (3, 35), (4, 5), (4, 6), (9, 11), (9, 13), (9, 41), (10, 11), (10, 14), (10, 42), (12, 13), (12, 14), (32, 33), (34, 35), (34, 38), (34, 42), (36, 37), (36, 38), (40, 41), (40, 42), (44, 45), (44, 46)]
def r1sG : List Nat := [1, 1, 2, 3, 3, 3, 4, 4, 9, 9, 9, 10, 10, 10, 12, 12, 32, 34, 34, 34, 36, 36, 40, 40, 44, 44]
def r2sG : List Nat := [5, 33, 6, 7, 11, 35, 5, 6, 11, 13, 41, 11, 14, 42, 13, 14, 33, 35, 38, 42, 37, 38, 41, 42, 45, 46]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [4402509972997, 9912953013765, 11033838486795, 11008574365963, 4402914067973, 4411083130118]
def xsM : List Nat := roots_47.map (· &&& dom_47)
def goalM : Nat := goal_47 &&& dom_47
def NN : Nat → Nat
  | 3 => 1
  | 4 => 3
  | 5 => 9
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xb8efdaaa
  | 4, 0 => 0xd089bf2e3a49c0100f1fce07
  | 5, 0 => 0xf641318ca1c0b4b88888432e5ba073fa5b61388b5aff2a1a530ab54651e3a4940f1fce07
  | 6, 0 => 0xf1fce07
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xccc00000ccc00000000000000000000000000000000000000000000000000000cc000000cc000000000000000000000000000000000000000000000000000000aaaa0000aaaa0000000000000000000000000000000000000000000000000000555500005555000000000000000000000000000000000000000000000000000033330000333300000000000000000000000000000000000000000000000000000f0f00000f0f000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000000000ffff
  | 0, 1 => 0xffff0000f0f00000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000fff00000fff00000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000f0f00000f0f00000000000000000000000000000000000000000000000000000cccc0000cccc
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xd753
  | 4, 0, 0 => 0xc97540db854ca9855
  | 5, 0, 0 => 0xc98515a98505ca9535ca8525ca9845c98655da9855cb9855ca9855
  | 6, 0, 0 => 0xca9855
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 16
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
  | 0, 0 => 0x38000000000000000000000000000000000000000000000000000000000000003800000000000000000000000000000000000000000000000000000000000000073b0000000000000000000000000000000000000000000000000000000003fff8c40000000000000000000000000000000000000000000000000000000003f1c7c30000000000000000000000000000000000000000000000000000000000cf3f3f00000000000000000000000000000000000000000000000000000000003f00ff000000000000000000000000000000000000000000000000000000000000ffff
  | 0, 1 => 0x3ffc0c00000000000000000000000000000000000000000000000000000000003ff00000000000000000000000000000000000000000000000000000000000003f0ffc00000000000000000000000000000000000000000000000000000000003c0ff00000000000000000000000000000000000000000000000000000000000330c0c000000000000000000000000000000000000000000000000000000000000e383c
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x2acb99c000000000000000000000000000000000000000000000000000000000288b9100000000000000000000000000000000000000000000000000000000001534f7b0000000000000000000000000000000000000000000000000000000002acb08400000000000000000000000000000000000000000000000000000000015146430000000000000000000000000000000000000000000000000000000000cb2d3200000000000000000000000000000000000000000000000000000000003700ef000000000000000000000000000000000000000000000000000000000000dbdd
  | 0, 1 => 0x3fff6ef0000000000000000000000000000000000000000000000000000000003ff24220000000000000000000000000000000000000000000000000000000003fcffdd0000000000000000000000000000000000000000000000000000000003c8ff10000000000000000000000000000000000000000000000000000000000334d2cd0000000000000000000000000000000000000000000000000000000002aeb9bc
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_47 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_47 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := []
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
private theorem z4_0 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 9 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 9 0 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 9 → Z 5 i = true := z5_0
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
  scr dom_47 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_47 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_47 roots_47 goal_47 7 := by
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

theorem low_47 : Lower dom_47 roots_47 goal_47 7 := S_47.noCircuit

namespace S_30_32
def pairsG : List (Nat × Nat) := [(34, 38), (34, 42), (34, 50), (36, 38), (40, 42), (44, 46), (44, 60), (48, 50), (52, 54), (52, 60), (56, 58), (56, 60)]
def r1sG : List Nat := [34, 34, 34, 36, 40, 44, 44, 48, 52, 52, 56, 56]
def r2sG : List Nat := [38, 42, 50, 38, 42, 46, 60, 50, 54, 60, 58, 60]
def mpG : Nat := 0xfff
def pool6G : List Nat := [39729390955046, 48525416867370, 44127370359338, 48525483977254, 39729390957094, 57321576999462, 52923329160754]
def xsM : List Nat := roots_30_32.map (· &&& dom_30_32)
def goalM : Nat := goal_30_32 &&& dom_30_32
def NN : Nat → Nat
  | 3 => 1
  | 4 => 3
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x4b5c3f1e
  | 4, 0 => 0x4b5c3f1e440e8fef0969002f
  | 5, 0 => 0x4b5c3f1e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x555500000000000000000000000000000000000000000000000000000000000055005500000000000000000000000000000000000000000000000000000000005050505000000000000000000000000000000000000000000000000000000000444444440000000000000000000000000000000000000000000000000000000011111111000000000000000000000000000000000000000000000000000000000055005500000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xb1a4
  | 4, 0, 0 => 0xb1a4b194ad04
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
  | 0, 0 => 0xf800000000000000000000000000000000000000000000000000000000000000c70000000000000000000000000000000000000000000000000000000000000036800000000000000000000000000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000000000000000ff8000000000000000000000000000000000000000000000000000000000000038f
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfc40000000000000000000000000000000000000000000000000000000000000e720000000000000000000000000000000000000000000000000000000000000b6900000000000000000000000000000000000000000000000000000000000005bf0000000000000000000000000000000000000000000000000000000000000a40000000000000000000000000000000000000000000000000000000000000018d
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_30_32 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_30_32 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_30_32 == dom_30_32) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_30_32 goalM u ys) : RunD dom_30_32 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_30_32 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_30_32 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_30_32 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_30_32 roots_30_32 goal_30_32 6 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_30_32 goal_30_32 := by
    have h0 : isConstB dom_30_32 goal_30_32 = false := by decide +kernel
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

end S_30_32

theorem low_30_32 : Lower dom_30_32 roots_30_32 goal_30_32 6 := S_30_32.noCircuit

namespace S_61
def pairsG : List (Nat × Nat) := [(1, 5), (1, 33), (4, 5), (9, 13), (9, 25), (9, 41), (12, 13), (12, 28), (17, 21), (17, 25), (17, 49), (20, 21), (20, 28), (24, 25), (24, 28), (32, 33), (36, 37), (40, 41), (44, 45), (44, 60), (48, 49), (52, 53), (52, 60), (56, 57), (56, 60)]
def r1sG : List Nat := [1, 1, 4, 9, 9, 9, 12, 12, 17, 17, 17, 20, 20, 24, 24, 32, 36, 40, 44, 44, 48, 52, 52, 56, 56]
def r2sG : List Nat := [5, 33, 5, 13, 25, 41, 13, 28, 21, 25, 49, 21, 28, 25, 28, 33, 37, 41, 45, 60, 49, 53, 60, 57, 60]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := [4402745972997, 26427136935193]
def xsM : List Nat := roots_61.map (· &&& dom_61)
def goalM : Nat := goal_61 &&& dom_61
def NN : Nat → Nat
  | 4 => 2
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x995298d155165737
  | 5, 0 => 0x995298d1
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x333333330000000000000000000000000000000000000000000000000000000033330000333300000000000000000000000000000000000000000000000000003300330033003300000000000000000000000000000000000000000000000000330000003300000000000000000000000000000000000000000000000000000030303030303030300000000000000000000000000000000000000000000000002222222222222222
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x2c6428a884
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
  | 0, 0 => 0x1ff80000000000000000000000000000000000000000000000000000000000001f07f0000000000000000000000000000000000000000000000000000000000018e60f8000000000000000000000000000000000000000000000000000000000180600000000000000000000000000000000000000000000000000000000000006d18c4000000000000000000000000000000000000000000000000000000000000073b
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x1ff84220000000000000000000000000000000000000000000000000000000001f87f900000000000000000000000000000000000000000000000000000000001ce72f80000000000000000000000000000000000000000000000000000000001c8729000000000000000000000000000000000000000000000000000000000016d59cd0000000000000000000000000000000000000000000000000000000000b7af7f
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_61 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_61 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
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

namespace S_61_2
def pairsG : List (Nat × Nat) := [(2, 6), (3, 7), (3, 11), (3, 19), (3, 35), (10, 11), (10, 14), (10, 42), (18, 19), (18, 22), (18, 50), (26, 27), (26, 30), (26, 58), (34, 35), (34, 38), (34, 42), (34, 50)]
def r1sG : List Nat := [2, 3, 3, 3, 3, 10, 10, 10, 18, 18, 18, 26, 26, 26, 34, 34, 34, 34]
def r2sG : List Nat := [6, 7, 11, 19, 35, 11, 14, 42, 19, 22, 50, 27, 30, 58, 35, 38, 42, 50]
def mpG : Nat := 0x3ffff
def pool6G : List Nat := [11008574366475, 11008574890771]
def xsM : List Nat := roots_61_2.map (· &&& dom_61_2)
def goalM : Nat := goal_61_2 &&& dom_61_2
def NN : Nat → Nat
  | 4 => 2
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xf32b51400571b122
  | 5, 0 => 0xf32b5140
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xcccccccc00000000000000000000000000000000000000000000000000000000cccccc00cccccc00000000000000000000000000000000000000000000000000cccc0000cccc0000000000000000000000000000000000000000000000000000cc00cc00cc00cc00000000000000000000000000000000000000000000000000c0c0c0c0c0c0c0c00000000000000000000000000000000000000000000000008888888888888888
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x2b4428b084
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
  | 0, 0 => 0x3c0000000000000000000000000000000000000000000000000000000000000003fe00000000000000000000000000000000000000000000000000000000000003f0000000000000000000000000000000000000000000000000000000000000038e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001e
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3e4900000000000000000000000000000000000000000000000000000000000033fec0000000000000000000000000000000000000000000000000000000000023f0800000000000000000000000000000000000000000000000000000000000138e40000000000000000000000000000000000000000000000000000000000009243000000000000000000000000000000000000000000000000000000000000493e
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_61_2 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_61_2 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_61_2 == dom_61_2) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_61_2 goalM u ys) : RunD dom_61_2 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_61_2 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_61_2 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_61_2 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_61_2 roots_61_2 goal_61_2 6 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_61_2 goal_61_2 := by
    have h0 : isConstB dom_61_2 goal_61_2 = false := by decide +kernel
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

end S_61_2

theorem low_61_2 : Lower dom_61_2 roots_61_2 goal_61_2 6 := S_61_2.noCircuit

namespace S_62_1
def pairsG : List (Nat × Nat) := [(1, 5), (1, 33), (3, 7), (3, 11), (3, 19), (3, 35), (9, 11), (9, 13), (9, 25), (9, 41), (17, 19), (17, 21), (17, 25), (17, 49)]
def r1sG : List Nat := [1, 1, 3, 3, 3, 3, 9, 9, 9, 9, 17, 17, 17, 17]
def r2sG : List Nat := [5, 33, 7, 11, 19, 35, 11, 13, 25, 41, 19, 21, 25, 49]
def mpG : Nat := 0x3fff
def pool6G : List Nat := [9908776407819]
def xsM : List Nat := roots_62_1.map (· &&& dom_62_1)
def goalM : Nat := goal_62_1 &&& dom_62_1
def NN : Nat → Nat
  | 4 => 2
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x663eaaf34ced5003
  | 5, 0 => 0x4ced5003
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xaaaaaaaaa0a0a0a0000000000000000000000000000000000000000000000000aaaaaaaa00000000000000000000000000000000000000000000000000000000aaaa0000aaaa0000000000000000000000000000000000000000000000000000aa00aa00aa00aa00000000000000000000000000000000000000000000000000a0a0a0a0a0a0a0a00000000000000000000000000000000000000000000000008888888888888888
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x568246885
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
  | 0, 0 => 0x3c0000000000000000000000000000000000000000000000000000000000000003c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003c
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x2aa700000000000000000000000000000000000000000000000000000000000022220000000000000000000000000000000000000000000000000000000000003d1000000000000000000000000000000000000000000000000000000000000013c80000000000000000000000000000000000000000000000000000000000000885000000000000000000000000000000000000000000000000000000000000047c
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

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)]]
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
def pairsG : List (Nat × Nat) := [(1, 5), (2, 6), (3, 7), (3, 11), (4, 5), (4, 6), (9, 11), (9, 13), (10, 11), (10, 14), (12, 13), (12, 14)]
def r1sG : List Nat := [1, 2, 3, 3, 4, 4, 9, 9, 10, 10, 12, 12]
def r2sG : List Nat := [5, 6, 7, 11, 5, 6, 11, 13, 11, 14, 13, 14]
def mpG : Nat := 0xfff
def pool6G : List Nat := [4406788162822, 4402509972997, 9912953013765]
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_15 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_15 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0x2222222222222222222222222222222222222222222222222222222222222222, 1)]]
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

namespace S_27
def pairsG : List (Nat × Nat) := [(3, 11), (3, 19), (9, 11), (9, 25), (10, 11), (17, 19), (17, 25), (18, 19), (24, 25), (26, 27)]
def r1sG : List Nat := [3, 3, 9, 9, 10, 17, 17, 18, 24, 26]
def r2sG : List Nat := [11, 19, 11, 25, 11, 19, 25, 19, 25, 27]
def mpG : Nat := 0x3ff
def pool6G : List Nat := [9908776407819]
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_27 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_27 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)]]
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

namespace S_45_16
def pairsG : List (Nat × Nat) := [(17, 21), (17, 25), (17, 49), (20, 21), (20, 28), (24, 25), (24, 28), (48, 49), (52, 53), (52, 60), (56, 57), (56, 60)]
def r1sG : List Nat := [17, 17, 17, 20, 20, 24, 24, 48, 52, 52, 56, 56]
def r2sG : List Nat := [21, 25, 49, 21, 28, 25, 28, 49, 53, 60, 57, 60]
def mpG : Nat := 0xfff
def pool6G : List Nat := [22063651494165, 26461630895385]
def xsM : List Nat := roots_45_16.map (· &&& dom_45_16)
def goalM : Nat := goal_45_16 &&& dom_45_16
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x2baa1fe3
  | 4, 0 => 0x2baa1fe3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x3333000000000000000000000000000000000000000000000000000000000000330000003300000000000000000000000000000000000000000000000000000030300000303000000000000000000000000000000000000000000000000000002222000022220000
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_45_16 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_45_16 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_45_16 == dom_45_16) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_45_16 goalM u ys) : RunD dom_45_16 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_45_16 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_45_16 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_45_16 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_45_16 roots_45_16 goal_45_16 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_45_16 goal_45_16 := by
    have h0 : isConstB dom_45_16 goal_45_16 = false := by decide +kernel
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

end S_45_16

theorem low_45_16 : Lower dom_45_16 roots_45_16 goal_45_16 5 := S_45_16.noCircuit

namespace S_45_2
def pairsG : List (Nat × Nat) := [(2, 6), (3, 7), (3, 11), (3, 35), (10, 11), (10, 14), (10, 42), (34, 35), (34, 38), (34, 42)]
def r1sG : List Nat := [2, 3, 3, 3, 10, 10, 10, 34, 34, 34]
def r2sG : List Nat := [6, 7, 11, 35, 11, 14, 42, 35, 38, 42]
def mpG : Nat := 0x3ff
def pool6G : List Nat := [11008574366475]
def xsM : List Nat := roots_45_2.map (· &&& dom_45_2)
def goalM : Nat := goal_45_2 &&& dom_45_2
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xa6268017
  | 4, 0 => 0xa6268017
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xcccc000000000000000000000000000000000000000000000000000000000000cc000000cc000000000000000000000000000000000000000000000000000000c0c00000c0c00000000000000000000000000000000000000000000000000000888800008888
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
  | 0, 0 => 0x38000000000000000000000000000000000000000000000000000000000000000700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3c800000000000000000000000000000000000000000000000000000000000002740000000000000000000000000000000000000000000000000000000000000123000000000000000000000000000000000000000000000000000000000000009e
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_45_2 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_45_2 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_45_2 == dom_45_2) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_45_2 goalM u ys) : RunD dom_45_2 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_45_2 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_45_2 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_45_2 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_45_2 roots_45_2 goal_45_2 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_45_2 goal_45_2 := by
    have h0 : isConstB dom_45_2 goal_45_2 = false := by decide +kernel
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

end S_45_2

theorem low_45_2 : Lower dom_45_2 roots_45_2 goal_45_2 5 := S_45_2.noCircuit

def isoMv_55_8 : List (Nat × Nat) := [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_55_8 : Lower dom_55_8 roots_55_8 goal_55_8 7 :=
  lower_iso isoMv_55_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47_16

def isoMv_55 : List (Nat × Nat) := [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_55 : Lower dom_55 roots_55 goal_55 7 :=
  lower_iso isoMv_55 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47

def isoMv_23 : List (Nat × Nat) := [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_23 : Lower dom_23 roots_23 goal_23 5 :=
  lower_iso isoMv_23 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15

def isoMv_53_8 : List (Nat × Nat) := [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_53_8 : Lower dom_53_8 roots_53_8 goal_53_8 5 :=
  lower_iso isoMv_53_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_45_16

def isoMv_53_2 : List (Nat × Nat) := [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_53_2 : Lower dom_53_2 roots_53_2 goal_53_2 5 :=
  lower_iso isoMv_53_2 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_45_2

def isoMv_30_1 : List (Nat × Nat) := [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]
theorem low_30_1 : Lower dom_30_1 roots_30_1 goal_30_1 5 :=
  lower_iso isoMv_30_1 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_45_2

def isoMv_58_1 : List (Nat × Nat) := [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)]
theorem low_58_1 : Lower dom_58_1 roots_58_1 goal_58_1 5 :=
  lower_iso isoMv_58_1 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_45_2

namespace S_63
def pairsG : List (Nat × Nat) := [(1, 5), (1, 33), (2, 6), (3, 7), (3, 11), (3, 19), (3, 35), (4, 5), (4, 6), (9, 11), (9, 13), (9, 25), (9, 41), (10, 11), (10, 14), (10, 42), (12, 13), (12, 14), (12, 28), (17, 19), (17, 21), (17, 25), (17, 49), (18, 19), (18, 22), (18, 50), (20, 21), (20, 22), (20, 28), (24, 25), (24, 28), (26, 27), (26, 30), (26, 58), (32, 33), (34, 35), (34, 38), (34, 42), (34, 50), (36, 37), (36, 38), (40, 41), (40, 42), (44, 45), (44, 46), (44, 60), (48, 49), (48, 50), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [1, 1, 2, 3, 3, 3, 3, 4, 4, 9, 9, 9, 9, 10, 10, 10, 12, 12, 12, 17, 17, 17, 17, 18, 18, 18, 20, 20, 20, 24, 24, 26, 26, 26, 32, 34, 34, 34, 34, 36, 36, 40, 40, 44, 44, 44, 48, 48, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [5, 33, 6, 7, 11, 19, 35, 5, 6, 11, 13, 25, 41, 11, 14, 42, 13, 14, 28, 19, 21, 25, 49, 19, 22, 50, 21, 22, 28, 25, 28, 27, 30, 58, 33, 35, 38, 42, 50, 37, 38, 41, 42, 45, 46, 60, 49, 50, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0x3fffffffffffff
def pool6G : List Nat := [4402509972997, 9908776407819, 18704735210259, 18730403957529, 11008574365963, 19804667912467, 26439971308828, 37401517497350, 9912953013765, 11033838486795, 4402745972997, 13207361815819, 11034208834315, 37387860839173, 37387860839201, 26427136935193, 26461630891289, 22042345875996, 35189106022689, 4411083130118, 22003403916550, 37426396071210, 37426397514538, 13207176152326, 37460756333874, 37396450773766, 37460757254962, 44023567944490, 4402644715013, 19864291247379, 57329962124805, 39656374409477, 37470236974086, 18704785737235, 39622014671109, 4402914067973, 9908826932747]
def xsM : List Nat := roots_63.map (· &&& dom_63)
def goalM : Nat := goal_63 &&& dom_63
def NN : Nat → Nat
  | 4 => 1
  | 5 => 14
  | 6 => 113
  | 7 => 335
  | 8 => 194
  | 9 => 25
  | 10 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x18244df6
  | 5, 0 => 0xd005d31cb9a1c1fca5760da19da8f7c88bf18cbc86261e35721d02cc617c6c2a571615e6554f05234455b5353b1d4bb232917f320801b9b7
  | 6, 0 => 0x67aab8ca654b05bf6364ed4c614d42ef6118463c60efd5a75e2f68925e2d8aab592546695843793f57530f6052c456aa4f93257d4e25833648cbb65d47fc363747c9508f451f7c0844791ed041687f4b3d9f94a43d84ec9438d2b5b937dc523537809ff03728b9ed36bd7d743660102c355c7597346621283248999f2de36d7f2bd16d4b2bac480627a3923b256fb51724a93d7522973d4121a6ca701d53ac7e1c96ea491b9c12d81a790e7716eb0e0415eac7dd153e569a147d2596117e334c101091050db5a09d0c70abe40baac8070a7e198b09e3818409d65bad08f317a506e4336306165d7605f5b00604139c010407793403dc8ef4015ae24a00e0e71a
  | 6, 1 => 0xff6ffa63fa6bbea2f9f35cfbf6090b36edeab750eddb268ce85d85b9e6ee6dd1de72f46eda6b9e3ad7aa92d6d5ff09a9d4e034e8d0b43e4bcc64bb85caf5a39dc91c43e9c8d0b400c77f38fbc738897ac2cbf4e9bab9a1bdb8e76ab4abb9803fa0934f719ca8fdac983c2f6e9380eeae9014a0488fdacb3a8fc877068fc0b60b8ba80bb78b4f7a7682d33eba7c95abe27c43653a7a31650678603ecf7836dae37788247a760389f6735b7bd8734bd994727b135971acb9636ecfff346bb3a4396a8772f9
  | 7, 0 => 0x29af2b6429259dd7286658d0275b976e268308622648e3a825d65b7e2447fb33237aefb8232c6add21eaa96f20819f3a204fb0ae1fecb1011fd3c25f1d2aeaa91cd038361c96ea491c397d011c228a231b35e26c1b27d2611b16f5ed1afecaa01a4dc7a41a256c9319ddb2d519ba301a1980bc2917c5c22e16d77b9d16446b9c14e907ff144baa9113aad82f12bb8144122a3819117804a41161181a10763c720f7093b80e7db3450dd633720d3dec4f0c8a4ae10c6d8e9c0ace38ec0a386e390938390c091999780824e87707f4e76207ca96c5078179cf064cb8090442bd8603b853e6030a418d01ad4403016603570155178300d76e0200a28bea0029bfef
  | 7, 1 => 0x46f1b31146a11ddf45ff713245b797dc45a7f5984449f595441caf3c4408d56743e5620b431f7df741cd4617412c1b38406f21e940419ef2402fc56c3f78cd7a3f3bf5403e1ce6143e0fc03d3d8a3cae3d2c7c353d0b3b903cfeefc53cba78eb3c21f90f3bcc8c933b5dab7f3b05d6f73a4fc2063a2d6c6238c6876637d1fc6e37468a16364691d835c10950357f7388354e1e60353aa3c633cd017f33a95ef3338d060c336e091f3351133032eb626b32d045d1315c08eb30625d632ea523322e9b5e9e2e450d9e2dd37e3b2dcb18752d70ced82c2026e82c009a592bf5c8d22bbea46f2b81626d2b811d732b35846d2af8e8dd2aef9cf32a06a6fe29cdf5ee
  | 7, 2 => 0x6fb8decd6f410f6b6ecfcc7c6eb15a926bf58d8b6b302ff16afee7646a8281de6a27cc6b6a0abb03689f85b8683daa90682a0095680f799366e473206625b9e965ec78e265959c726542ebe464dbd5c46497fa936332600f621cd20f60fe5bb260d65753601d48af60157970600ad1db5ecd913b5e1ccb875dd41be55dd08b735cb746015c97debb5bdcf6cb5b34bf745a7ee54859254669582291a257dd7a93575675b356488c3a54acafc454a96c0953c014995372c47952a2b5415257aedf518d110e4ffcc3574fbdd0064d84259f4d5b0f8d4d2ff4d14c16af5f4b77d19c4b50406a4b2472944aeba8ec4aabf4e84a9428d249cc486f49c3e2a947e720b8
  | 7, 3 => 0x9fa1d4049eeb49849ec0d7899b353f739ab78fed9ab4c092999971879985a136996657c29823da64970d41689551aacc9512475994e56e8494c7ea7294487611939a8dab9381e4a092cd700b92b8eaa091d14c51919a80f88e92684e8d5eaaf98aa44b2d88e50a94886050ee87e13aa085f1f7268544e6468422cac98362117782cfc52182204782821853fe80d851b57fe1a60d7e159c437da0a7537d8dbfab7d327abc7c039c0f7bd0c69379cce61979c2eecc797004af78b0103577abf41377a1c377779c985d76c6508b75e005e575a1e3db7544c0b174cf39e474ae25e074a44fa473d644c7739a99807301de5f729c25ac70a579f87037bb1370120e99
  | 7, 4 => 0xeb121e74e73f702ce66050c7e56d3923e52d0e51e3a5ddcee3212e0be2f6af66e28853e8e1fa8566e041dc16dff2e4cfddf8e307d94a31a4d9288e6bd872797ad7322c12d5b38d53d282c284d0ad1508d04632e9ccc7daa6cc7593fecbedcfe9cb08702aca14a60bc934441dc82cddd4c7fcec2ec7b46166c72863d7c548d783c4b48854c3606443c2b39fdfc20018d3c13d7091bf662c09beed43e6bebb555abd2fc437bb968f55bab9a1bdba85faa9b5bed785b5446adbb1eb36f8b1522b5ab0de38b8b0cf1072af647c31af20d37cad58a5d0ac0421faaba990fbaa904610aa2ce68ba994b72fa94c64a9a893383aa6608c0ea5b66d6ea3105a4fa1561606
  | 7, 5 => 0xfe811e1cfdfab3d3fdf6b6b9fde4e8a1fd75c11dfd1287fffc465d48fad9fd75f72a0023f5192827f2bca34feef3064deca5df3cec2d7d95ebefca4b
  | 8, 0 => 0x410d76963c21f90f3a861c99387c221637f1b8763732d33a359f67e7358e7c1334064f6c330961a632ba82ac317141fd3129ad3f302ca7772fc976f62f1362052d90db782b81626d292df8a128a4a83e2774c460275958f22705880d26488ebe261c309d2609324123e92d1223afce92233e519822d85c9a2219ec0a21a5f96820df43cc20292edb1fb72b911e3d0e221c1ffead1b78d4bc1b52f3321a433cbc196672e1183e8305181aa941175a929b16a6119912b8884a1232479711eb7ccf119811440f8898390e7e15130e7dd0190d61f2fb0cabde0a0c22507d0bd753a90a2e187206291d8305c61dd605ad2f34059e8b17023f103c01013f3600273479
  | 8, 1 => 0x8b8fda438a81f0ca8a0d10dd877c8a9f867726a185520fcd8492c7cd83f048fb806266ad7f5f0e0b7e8559377e05acff7dfd47397bf0d3337b2b17a17ab597257aa157477a38d5c279e15a2879a4d76c78bca8127892577574f2245d745a681c73b2320a705b5d9f6f6c29a26ebe77696be1bd3a6bcb63fb6a7ff66867f1c0d3679d352a651506a463353df461aa3368602f2d625fbac6fd5c9fbd605b2acd595abc6cf25aa8a6b958905d13584e132a57a1024a567ee6cd53346db9530ec13f523dc21151099cc6505beeb3500139404fb2394c4e2ce2974e1717654d17706a4bff26be4bc969994b0c2c394a3f78dc49226c8f45f6b58443a9f8484214fad1
  | 8, 2 => 0xf17a65ebeef3064deabec0cde73f702ce606f433e48a3599e3d420a8e21fca1ddec9aaa0ddd7f9c9d9b9b7a8d58ce416d1786b89d0dd3a20cf6ea403cea2794ccdd2d617cb46a5f8c7d3f23bc576ef75c5690328c4eae2e7bf01fb40bef1afedbe4be64fbc545819b9782853b85c2f59b59a84ddb511b645b4e46fecb37ef559b24f00d3b0e1dcffb01ae1b0ae064aa9ace974c5aa8df529aa87c3f1a98e4816a8e78fc4a8d9852aa80fa957a68098aea4dede88a494c22fa3f2435da309310ca302d5f5a02ef21b9e58572e9c97dd089b1dd7b097a4f38797251c989710a458950fbbe392ef453391b98d1291495fea9117715e8f6e24048df2ab598d5eaaf9
  | 8, 3 => 0xffcceadcfb7259a6
  | 9, 0 => 0xf33b5fd0f2854adfc3d681efb47be6218ab84b5d876dd2497f4590c97cea112d76f0de33764e5f61705b5d9f61ca40085fbac6fd5cde0cce51bb2a0f5059633d4aee737942b779a33e277fff34064f6c2efbd9641b78d4bc1606144c0e7e151305169eb0
  | 10, 0 => 0x42b779a3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x3030f0f03030f0f000000000000000000000000000000000000000000000000030303030303030300000000000000000000000000000000000000000000000000ff00ff00ff00ff000000000000000000000000000000000000000000000000003333ff003333ff000000000000000000000000000000000000000000000000000f0f0f000f0f0f0000000000000000000000000000000000000000000000000000ffff0000ffff00000000000000000000000000000000000000000000000000000000ffffffff000000000000000000000000000000000000000000000000000000000f0f0f0f
  | 0, 1 => 0x3300330033003300000000000000000000000000000000000000000000000000222222222222222200000000000000000000000000000000000000000000000011111111111111110000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f000000000000000000000000000000000000000000000000070707070707070700000000000000000000000000000000000000000000000005050f0f05050f0f0000000000000000000000000000000000000000000000000505050505050505000000000000000000000000000000000000000000000000030f030f030f030f
  | 0, 2 => 0x99999999999999990000000000000000000000000000000000000000000000008888888888888888000000000000000000000000000000000000000000000000555555555555555500000000000000000000000000000000000000000000000055005500550055000000000000000000000000000000000000000000000000004444444444444444000000000000000000000000000000000000000000000000333333333333333300000000000000000000000000000000000000000000000033333333303030300000000000000000000000000000000000000000000000003333000033330000
  | 0, 3 => 0xccc0ccc0ccc0ccc0000000000000000000000000000000000000000000000000cc00cc00cc00cc00000000000000000000000000000000000000000000000000c8c8c8c8c8c8c8c8000000000000000000000000000000000000000000000000bbbbbbbbbbbbbbbb000000000000000000000000000000000000000000000000aaaaaaaaaaaaaaaa000000000000000000000000000000000000000000000000aaaa0000aaaa0000000000000000000000000000000000000000000000000000aa00aa00aa00aa00000000000000000000000000000000000000000000000000a8a8a8a8a8a8a8a8
  | 0, 4 => 0xcccccccccccccccc000000000000000000000000000000000000000000000000cccccccccc00cc00000000000000000000000000000000000000000000000000ccccccccc0c0c0c0000000000000000000000000000000000000000000000000cccccccc88888888000000000000000000000000000000000000000000000000cccccc00cccccc00000000000000000000000000000000000000000000000000ccccc0c0ccccc0c0000000000000000000000000000000000000000000000000cccc8888cccc8888000000000000000000000000000000000000000000000000cccc0000cccc0000
  | 0, 5 => 0xeeeeeeee00000000000000000000000000000000000000000000000000000000eeeeee00eeeeee00000000000000000000000000000000000000000000000000eeeeaaaaeeeeaaaa000000000000000000000000000000000000000000000000eee0eee0eee0eee0000000000000000000000000000000000000000000000000eecceecceecceecc000000000000000000000000000000000000000000000000eeaaeeaaeeaaeeaa000000000000000000000000000000000000000000000000eeaacc00eeaacc00000000000000000000000000000000000000000000000000ddccddccddccddcc
  | 0, 6 => 0xfaf0faf0faf0faf0000000000000000000000000000000000000000000000000fac8fac8fac8fac8000000000000000000000000000000000000000000000000f8f8f8f8f8f8f8f8000000000000000000000000000000000000000000000000f3f3f3f3f3f3f3f3000000000000000000000000000000000000000000000000f2f2f2f2f2f2f2f2000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000000eeeeeeeeeeeeeeee000000000000000000000000000000000000000000000000eeeeeeeee0e0e0e0
  | 0, 7 => 0xfcfca8a8fcfca8a8000000000000000000000000000000000000000000000000fcf8fcf8fcf8fcf8000000000000000000000000000000000000000000000000fcf0fcf0fcf0fcf0000000000000000000000000000000000000000000000000fafafafafafafafa000000000000000000000000000000000000000000000000fafafa00fafafa00000000000000000000000000000000000000000000000000fafaf0f0fafaf0f0000000000000000000000000000000000000000000000000fafac8c8fafac8c8000000000000000000000000000000000000000000000000fafa0000fafa0000
  | 0, 8 => 0xfefefefefefefefe000000000000000000000000000000000000000000000000fcfcfcfcfcfcfcfc000000000000000000000000000000000000000000000000fcfcfcfcfcf0fcf0000000000000000000000000000000000000000000000000fcfcfcfcf8f8f8f8000000000000000000000000000000000000000000000000fcfcfcfca8a8a8a8000000000000000000000000000000000000000000000000fcfcfcf0fcfcfcf0000000000000000000000000000000000000000000000000fcfcfc00fcfcfc00000000000000000000000000000000000000000000000000fcfcf0f0fcfcf0f0
  | 0, 9 => 0xffaaffaaffaaffaa000000000000000000000000000000000000000000000000ffaacc88ffaacc88000000000000000000000000000000000000000000000000ffaaaaaaffaaaaaa000000000000000000000000000000000000000000000000ff888888ff888888000000000000000000000000000000000000000000000000ff33ff33ff33ff33000000000000000000000000000000000000000000000000ff00ff00ff00ff00000000000000000000000000000000000000000000000000ff00cc00ff00cc00000000000000000000000000000000000000000000000000ff000000ff000000
  | 0, 10 => 0xffccffccffccffcc000000000000000000000000000000000000000000000000ffccffccfcccfccc000000000000000000000000000000000000000000000000ffccffccaa88aa88000000000000000000000000000000000000000000000000ffccff00ffccff00000000000000000000000000000000000000000000000000ffccf0c0ffccf0c0000000000000000000000000000000000000000000000000ffccccccffcccccc000000000000000000000000000000000000000000000000ffcccc00ffcccc00000000000000000000000000000000000000000000000000ffcc0000ffcc0000
  | 0, 11 => 0xffffaaaaffffaaaa000000000000000000000000000000000000000000000000ffff3333ffff3333000000000000000000000000000000000000000000000000ffff0000ffff0000000000000000000000000000000000000000000000000000ffff0000f0f00000000000000000000000000000000000000000000000000000fff0fff0fff0fff0000000000000000000000000000000000000000000000000fff0fff0ccc0ccc0000000000000000000000000000000000000000000000000fff0f0f0fff0f0f0000000000000000000000000000000000000000000000000fff0aaa0fff0aaa0
  | 0, 12 => 0xffffffff00000000000000000000000000000000000000000000000000000000ffffff00ffffff00000000000000000000000000000000000000000000000000ffffff00cccccc00000000000000000000000000000000000000000000000000ffffff00aaaaaa00000000000000000000000000000000000000000000000000fffff0f0fffff0f0000000000000000000000000000000000000000000000000fffff0f0aaaaa0a0000000000000000000000000000000000000000000000000ffffccccffffcccc000000000000000000000000000000000000000000000000ffffcc00ffffcc00
  | 0, 13 => 0xffffffffffff0000000000000000000000000000000000000000000000000000ffffffffff00ff00000000000000000000000000000000000000000000000000fffffffff0f0f0f0000000000000000000000000000000000000000000000000ffffffffcccccccc000000000000000000000000000000000000000000000000ffffffffaaaaaaaa000000000000000000000000000000000000000000000000ffffffff33333333
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0xd74a11b4
  | 5, 0, 0 => 0x35d1649cdae7a4c91955cf4539b18b49923360573d284c8daeb910939b5bb29e3024b29e304e0973d1649caaeba0f539b5cec939b08b45927360575d2648cdae7a48cd8c5
  | 6, 0, 0 => 0x1aeeb22a482b00d725927406d806bc35192736c024324e8cd81601af0ca7880db00cf9a9324e558067c12939518c025322a481016019d9312c141300bb28a921805806bbb5dea736c035dd949cd886019eeb12c302b00649cd850401806094c8d9202c035dd92f139b6
  | 6, 0, 1 => 0x176a324e540b00d729ea73609806790c93a32ac028324e78d81601aeec9646c9300d776a323649805e94c8d9002c033e094c8a926019d91b24141300cf924324e6d806794d593104c033e16480a856019a4324e6c0300cf4251b2431805d646c90500c035e690c93956
  | 6, 0, 2 => 0x1aeeca78c49300bb5cf1b18058000bb29e304ea033d0649cf156019ef4a64548300d6f139b0a09806094c939b00c035dd9500d926018653240540b00d729e314e098067364860504c033dd966c78c6019f0574e6c6300d7825324e55805d64c139b0ac02ec9649ca816
  | 6, 0, 3 => 0x17539518140b00cf8501b1815806bbb28d9212c035b236482826019eed73c546300d7765b2363d80679e9cc8c04c00067bb299175019e5322a481300cf9a9273631804a364860202c035ca4e6c482601af348789cdb00d775e1b24158067cd20d9218c02bb23c6c1016
  | 6, 0, 4 => 0x33d1649cda80d79a9324e6d806690c939502c02ec94e6c60160176a2736300b00d7765424e6d806bbb29ca736c030d4649cd816019e427466c6300d79a43236498067945490c04c035e094f139b6019e7b232481300cf7679924318067c128d9218c019272a141016
  | 6, 0, 5 => 0x19eeca64c45b00cf7651c1c31805d92c939b00c035dd92c93956019d9272a1413004e6c60504058067bb2591524c035c8649d19b6d77653c4e8cdb80cf764a72a318067c3519272ac02ed76478d80601af0b2406c2b00cf4139e3631805d92c8d9202c035ddaec8f156
  | 6, 0, 6 => 0x19f34864549300cf221324e6db3dd9509e2736e03352649cd81600033d2648cda80cec8a920a098067cd2139518c03348646c901601765404e6c0300d77653e4e6d806bbb2a0272ac033a72a3028260176532606c9300646c90504058066909cd8c02c033d07ac939b6
  | 6, 0, 7 => 0x35b24e542826
  | 7, 0, 0 => 0x1a73e690c939b700033a736302826019aeca649cd80701aeeb2629cd85701a73dd646c905701b73dd4e6c60570176548649ca817019e5324e54902701af35d94c93957019e5324e54a027019e84a649cd957019eeca4e5490c7019f1dd649ca85701299314e6c101700035e194c901b601765324e84d817
  | 7, 0, 1 => 0x19eeca4e78a8c701aefdd94c8d927019eeca6454a127019eeb23648282700035d094c939b60176532626c90170002eca64c57966cf7653c649d19b8019eeca6454905701af3ca646c9027019f25d94c939b7019eec0649cd85701aeed294c939b701765323c6c9017019eeca78c890e700035dd950139b6
  | 7, 0, 2 => 0x19e532629ca82700033b23648282600033dd96c8d8f6019eeca649d095700033e0aec939b600033e6909cd8c6019eeca7ec939b701b73dd646c90570186eca4e6c601700035dd94f18a76019eeca649d195700033dd364860560176527406c6017019e5324e78a82701865324e80d817019eed894c939b7
  | 7, 0, 3 => 0x252736301016019d92736582827019eeca6478a927019eeca8ac939b701aeeca649ca857019eea736586057019f1ca90c8d92701af0dd649cd85701aeeb24e80d857019d92736542827018eeca649ca81700035dd789cd856019eea736546057019eeca629cb0c7017652736301017019eebc64c53857
  | 7, 0, 4 => 0x13e5324e6c1017019eeca64a539b70176540649cd8170186eca646c9017019eeca64c4a92701a73e094c939b7019eeca74c8d92701aeeca649ca92701767ca4e6c601700033ca649ca826019e3324e6c2827019eeca649cd8770002ed76478d81601765324e6c28070176dc8649cd81701aeeb24e6c2827
  | 7, 0, 5 => 0x1ae5324e94d827019f0dd949ca8c700035dd949cd896019eecc94c939b7019f1d294c939b7019f348649cd957019eeb23654905700035b24e6c2826019eeca364878c701af3dd92c939b7017653236481017019eeca649cd8a7019f0ca649d015701af3dda8c939b701765324e6c900700033e690c8d926
  | 7, 0, 6 => 0x1767ca646c901700033e6a4c939b600033e0949cd8c6019eed778c8f1b700025323648101601af3e194c901b7019eeca4e90d8c7019e535649cd82700033dd94c8a926019eeca4e546027017aeca646c9017019f35d946c90c70002eca36486016019eecf649cc827019eeb24e6c485701aeedc94c8d927
  | 7, 0, 7 => 0x33ddaec8f15601af3dd950139b7019eedb90c9395700035e690c939b600033ca4e54602600035dd646c90560175e324e6c281700033cf649cc82601765324e78d807016e5324e6c101701af35d94f139b700033dd9e9cc8c6019eed74e78d8c7019e537649cd827019eeca4e98d8c701aeeca649cf157
  | 7, 0, 8 => 0x33e094c8d9260176534649cd817019e53c646c90270002eb24e542816019eeca6ac8d927019e52736302827012a3324e6c1017019eeca7cc939b7019efdd4e6c605700033e16480d856015e5324e6c1017019eeca82c939b7019e7ca649ca827019eeca80c93957019f0dd94c8a92701aeeca6494d927
  | 7, 0, 9 => 0x176546646c9017019eeca64b139b700033c8649d19b6019eecf94c8a92701759273648281700033ca64549026019f04a649cd9570176cca649cd817019ef5d94c8a92700033dd945490c601765484e6c601700033dd9ec8c9260176dca646c9017019eece94c939b7019e52736486027019eeca86c939b7
  | 7, 0, 10 => 0x1aeeca789ce9b701af35d94c8d9270186eca649cd80701aeed694c939b701aeeca789cd857019f1dd646c90570002ec9649cd816019eed594c939b701af0dd94c93957019eea736686057019eebc649ca8570002ed4649cd816019efdd646c905701aeeca646c90f70176532386c9017019eeca36486057
  | 7, 0, 11 => 0x19eedb94c8a927019e5324e549827019aeca649ca817019eeca64b4d927019eeca68c93957019e5314e6c602701aeed7649cf1b7019eeca4e84d8c7019eeca569cd8c701aeeca789cd92700035e094c939b6019eeca4e8cd8c70176548646c9017019e546649ca827019ebca649ca827019e5273c6c6027
  | 7, 0, 12 => 0x17694a649cd817019eeca64a13957019eeca3c6c90c701aefdd649cd85700033d0649cf1b6017654664c4d81700033dd94c4b0c6019eec978c939b700025324e6c1006019eed994c93957019eeb236689057019eeca6cc939b7019eed478c939b7019eeca909ca8c700035ca649ca82601af3b24e6c2827
  | 7, 0, 13 => 0x19f15d94c939b701af3e690c939b701a73ca4e6c602700035dd94c8a926019eeca6454992700033dd92c939560176534646c901701aeeca789cf1b701ae5324e6c902700033dda8c93956019eeca626c90c7019eeca6470a927019eed77ac939b7019eedb94e939b7019eeca8cc8a92700033ca64c4b026
  | 7, 0, 14 => 0x19eed294c93957019eeca649cd83701aeeca649d19b701a73dd946c90c701aeeca78e139b701765324e5428170175927406c281700033ca646c9026019f1dd9ec9399701ab3ca4e6c602701aeeca646c9057019eeca80f139b701b33dd946c90c70002eca646c9006019eeca90c8a92701a73ddaec8f1b7
  | 7, 0, 15 => 0x176548649cd80701af0dd94f139b700019273614101601aeeca90c93957019eeca88c939b7019e532549cd827019eeca68c8a92701ab3dd946c90c701aeedc649cd857019f0dd946c90c701765324e54901700033ddae78d8c601aeeca649d09b701759273614101701a33dd946c90c7019eeca64c519b7
  | 7, 1, 0 => 0x19eeb24e5428270003348649cd816019eed76478d95701aeeca646c911700033dd94c8e0e601765324e88d817019eeca80c8d92701765324e78a817019eed394c939b7019eecf946c90c7019eeca76c939b7019eeca6ac98a7701aeeca64c4d927019ef5d946c90c70002eca64c139b601aeeca6478d927
  | 7, 1, 1 => 0x19eeca365890c7019f34878c939b701af0dd94c8d92701765324e6c3017019f2dd94c939b7019eeda94c939b700035dd94f0d926019eeca365490c7019aeca4e6c6017019eeca78c9892700033b24e54282601a73dd92c939b7019eeca645490d7019ebca4e6c6027019eed994f139b7019de324e6c2827
  | 7, 1, 2 => 0x19eeca646c9097019eed994c8d927019eeca906c90c7019aeca646c901701aef5d94c8d92700033e690c9395600033dd929cd8c60186eca649ca817019eeca364870c7019eeca64b939b7017653236487817019eeca386c90c7019eeca649d1157019d9273648282701765324e74d817019eecd94c8d927
  | 7, 1, 3 => 0x19eeca649cd8b7019eeca649ca927019eeca68c989b7017652736486017019eeca645490f7019eeca66c8d927019eeca649ce95700033dd94c8b0d6017653c646c9017019eed2949cd8c7019d9314e6c282700033dd92c8d926019eeca649ca86701aeeca90f139b7019f35d949ca8c70002eca4e546016
  | 7, 1, 4 => 0x19eeca78c8a92701765314e6c601701ab3b24e6c282701765324e8cd81700033dd94d5931601aeeca90c8d927019eeca366490c70176546649ca81701a73b24e6c282700033dd94c989d601aeeca6470d92700033b24e6c2826019f35d94c8a927019eeca84c939b70002eca64549016
  | 8, 0, 0 => 0x1767ca649cd81700025324e6c101600033dd94c93956019eec6649cd857019f35d949cd8c70002eca4e6c6016019eeb24e6cb057d79eeca90c939b801aeedc94c939b7019eeb24e6ca857019eeca64c5396701765324e6c1017cf7653c70c939b8d59f35d94c939b800033e690c939b60186eca649cd817
  | 8, 0, 1 => 0x19f35d94c8d9270002eca646c9016019eeca6ac939b7d39eeca649cd858019f0dd94c93957019eeca649cd927019eeca649d015701aeeca649d29b7019eeca646c90f7cf7653c649cd828cf8eeca649cd998019eeca649ce9b700035dd649cd856cf86eca78c939b8019eeca649cd867cf7653c649d01b8
  | 8, 0, 2 => 0x19eecf94c9395700033ca649ca826cf765324e6c282800033dd949ca8c6cf9aeca649cd958019eeca649cf9b700033dd9ec93996019eed7649cf1b70176dca649cd817019eeca649d31b700033e094c939b6d39eeca649cd928019eeca6ec939b7019eeca649d21b7019e53c649cd827019eeca649ca827
  | 8, 0, 3 => 0x19eeca64b539b700033dd94c8a9260176548649cd817019e5324e6c902701af35d94c939b7d39eeca649cf1b8019eeca4e6c90c7019f1dd649cd857019eeca64c539b7019e5324e6c2827019eeca78c8d927db9eeca649cd858019efdd649cd857019eeca4e6c6057cf9aeca8cc939b80176546649cd817
  | 8, 0, 4 => 0x19eeca649ca937019e532629cd827019eeca649d09b7019eeca64ad39b7cf765324e6ca928019eeca629cd8c7019eeca649d19b7cf7654878c939b8019e5324e78d827d99f0dd94c939b8019eeca8cc93957cf765324e6ca858019eeca4e78d8c7019eeb24e6cd057019eeca646c9057019eedb94c93957
  | 8, 0, 5 => 0xcf76dca64c539b801a73dd949cd8c7cf765324e78d958019eeca64c4d92701aeeca649cd92700033ca649cd826019eeca6478d92701b33ca649cd82701aeeca649cd85700033dd94c98966d39f0dd94c939b801b33dd949cd8c70002eca649cd806019eeca90c9395700035dd94c9395601af3dd649cd857
  | 8, 0, 6 => 0x1a33dd94c8d927019eedb90c939b700033ca4e6c6026cf8eeca649cd85801aeeca64c539b701a73dd94c8d927cf767ca649cd828d79f35d94c939b801aeeca649cf1b700033dd94c8d926cf86ecf94c939b801ab3ca649cd82701ab3dd949cd8c701b33dd94c8d927019f0dd949cd8c701a73ca649cd827
  | 8, 0, 7 => 0x19ef5d94c8d92700033dd946c90c6cf765324e6cd058d39eeca8cc939b8019eeca649cd937d59eedb94c939b8cf86eca649cd958cf86edb94c939b8019eeca649ce1b701ab3dd94c8d927d39eedb94c939b8019eeca80c939b7019f0dd94c8d927019eecf949cd8c700033ddaec8f1b6d99eeca8cc939b8
  | 8, 0, 8 => 0xcf765324e78d9a8019eeca68c939b7cf767ca8cc939b8d79eeca649cd928019ebca649cd827019eecd94c939b7d79eeca649cd858019eeca4e6cb0c701af0dd94c939b7d39eeca90c939b8db9eedb94c939b800035dd94f139b6019eeca4e6ca8c7019eecf94c8d927019eeca78c98a7700033ca646c9026
  | 8, 0, 9 => 0x33dd92c939b6019eeca646c90e7d79eeca649cf1b8019eeca6470d927019eeca8cc8d927019eeca646cb127cf76dca649cd958019eeca649cd897019eeca8ec939b7cf76546649cd988019eed994c939b701aeecf94c939b7019eeca909cd8c7019eeca646ca927019eedb94c8d927019aeca649cd817
  | 8, 0, 10 => 0x19eeca68c8d92701765324e6c9017019eed294c939b7019eeca8cc989b7cf8eecf94c939b8cf76548649cd968019f35d94c93957cf76548649cd9580002eca649ca816019eeca649cd8d7cf76546649cd968019eeca90c8d927cf9aeca78c939b800035dd94c8d926017653c649cd817cf76546649cd958
  | 8, 0, 11 => 0x1af3dd94c8d92700033b24e6c2826017653262bd39b7019eeca649ca927019eeca649ca947cf9aeca64c539b80176532629cd817019eeca646cc92701765324e78d817cf7653c649cd928cf7653c649ce9b8019eeca649d29b7d79f0dd94c939b8019eeca78c9395701aeeca90c939b7019eeca4e6cc8c7
  | 8, 0, 12 => 0x19eeca64c53957d39f35d94c939b8
  | 9, 0, 0 => 0xcf76dca649cdb80cf765323649b3dd9f2992736e033ca649cd826019eeca4e6c636acf765324e6df3e1bb2992736fa73dd94c939b7019eeca649cdb6ccf765324e6df3dd94c98a736f9eeca649cf1b7cf765324e6c93e7bb299273615c067bb299272ad9eeca78c939b7
  | 9, 0, 1 => 0x19f35d94c939b701765324e6c0b6bcf765324e6df3dd94c939b32f9eeca90c939b701aeeca649cdb67bb2a3324e6df3dd94c939b2cf9eeca649cd957
  | 10, 0, 0 => 0x33dd94c939b6
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 32
  | 5 => 39
  | 6 => 53
  | 7 => 60
  | 8 => 60
  | 9 => 53
  | 10 => 46
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 7 0) :: stateWires n (ids >>> 7)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x38c67c6078fe7f0000000000000000000000000000000000000000000000000038c60460781e030000000000000000000000000000000000000000000000000007c1fc1ff801ff0000000000000000000000000000000000000000000000000007fffc1c7f1fff0000000000000000000000000000000000000000000000000000c67c03f8fe7f00000000000000000000000000000000000000000000000000003ffc0007ffff00000000000000000000000000000000000000000000000000000003ffffffff00000000000000000000000000000000000000000000000000000003e3f8fe7f
  | 0, 1 => 0x383e0060071e000000000000000000000000000000000000000000000000000000000000781e03000000000000000000000000000000000000000000000000003fff847c0701800000000000000000000000000000000000000000000000000038c67fe3f8fe7f0000000000000000000000000000000000000000000000000038c67fe3f8fe070000000000000000000000000000000000000000000000000038c67fe380fe7f0000000000000000000000000000000000000000000000000038c67fe380e0040000000000000000000000000000000000000000000000000038c67c63f81e7f
  | 0, 2 => 0x3fff847c0701f80000000000000000000000000000000000000000000000000000000000000078000000000000000000000000000000000000000000000000003fffffff87e18400000000000000000000000000000000000000000000000000383e03e007e0000000000000000000000000000000000000000000000000000000007b8380e004000000000000000000000000000000000000000000000000003fff847c7f1f83000000000000000000000000000000000000000000000000003fff841c070180000000000000000000000000000000000000000000000000003fc0007c780000
  | 0, 3 => 0x38000e000000000000000000000000000000000000000000000000000000000038000e0000000000000000000000000000000000000000000000000000000000000000078000000000000000000000000000000000000000000000000003fff847c7f1ffb0000000000000000000000000000000000000000000000000000000000781e7b00000000000000000000000000000000000000000000000000000000007800000000000000000000000000000000000000000000000000000000000000001e000000000000000000000000000000000000000000000000000000000000000078
  | 0, 4 => 0x7b8380e07c0000000000000000000000000000000000000000000000000000007b8000e00000000000000000000000000000000000000000000000000000000078000000000000000000000000000000000000000000000000000000000000007800000078000000000000000000000000000000000000000000000000000000038380e000000000000000000000000000000000000000000000000000000000038380000000000000000000000000000000000000000000000000000000000003838000780000000000000000000000000000000000000000000000000000000383800000
  | 0, 5 => 0x78000000000000000000000000000000000000000000000000000000000000000383f8fe000000000000000000000000000000000000000000000000000000000383f81e7b000000000000000000000000000000000000000000000000000000038000fe000000000000000000000000000000000000000000000000000000007b8380fe7c000000000000000000000000000000000000000000000000000000038078fe7b000000000000000000000000000000000000000000000000000000038078e00000000000000000000000000000000000000000000000000000383e7be387e07c
  | 0, 6 => 0x739801c071f800000000000000000000000000000000000000000000000000000380000071e78000000000000000000000000000000000000000000000000000739801c0701f8000000000000000000000000000000000000000000000000003fff847c7f1f83000000000000000000000000000000000000000000000000000739801c7f1f83000000000000000000000000000000000000000000000000000739801c0701800000000000000000000000000000000000000000000000000000007b83f8fe7f0000000000000000000000000000000000000000000000000000007800000000
  | 0, 7 => 0x700039f800078000000000000000000000000000000000000000000000000000739839c07e1f8000000000000000000000000000000000000000000000000000739839c07e180000000000000000000000000000000000000000000000000000739801c7f1ffb000000000000000000000000000000000000000000000000000738001c7f1e00000000000000000000000000000000000000000000000000000739801c7f0180000000000000000000000000000000000000000000000000000700001c780078000000000000000000000000000000000000000000000000000700001c780000
  | 0, 8 => 0x739fb9fffffff000000000000000000000000000000000000000000000000000739fb9f87e1fc000000000000000000000000000000000000000000000000000739fb9c07e180000000000000000000000000000000000000000000000000000739f81c0701f8000000000000000000000000000000000000000000000000000739f800000078000000000000000000000000000000000000000000000000000739839f87e180000000000000000000000000000000000000000000000000000738039f87e000000000000000000000000000000000000000000000000000000739839f870180
  | 0, 9 => 0x383e03e07ffe7b00000000000000000000000000000000000000000000000000380003e078e07800000000000000000000000000000000000000000000000000380003e0781e7b00000000000000000000000000000000000000000000000000380003e0000078000000000000000000000000000000000000000000000000003fff87fc7fff8300000000000000000000000000000000000000000000000000383e03e007fe0000000000000000000000000000000000000000000000000000380003e000e00000000000000000000000000000000000000000000000000000380003e0000000
  | 0, 10 => 0x383e7be387fe7c00000000000000000000000000000000000000000000000000383e7b8387e07c00000000000000000000000000000000000000000000000000383e7800001e7800000000000000000000000000000000000000000000000000383e03e387fe0000000000000000000000000000000000000000000000000000383803e38700000000000000000000000000000000000000000000000000000038007be380e07c00000000000000000000000000000000000000000000000000380003e380e00000000000000000000000000000000000000000000000000000380003e3800000
  | 0, 11 => 0x3fc003fff81e7b000000000000000000000000000000000000000000000000003fff87ffff1f83000000000000000000000000000000000000000000000000003fc003fff80000000000000000000000000000000000000000000000000000003fc0001c000000000000000000000000000000000000000000000000000000003f3f83fc07ff80000000000000000000000000000000000000000000000000003f3f838000e000000000000000000000000000000000000000000000000000003f3983fc070180000000000000000000000000000000000000000000000000003f0003fc001e00
  | 0, 12 => 0x3ffffc00000000000000000000000000000000000000000000000000000000003ffe03fffffe00000000000000000000000000000000000000000000000000003ffe038380e000000000000000000000000000000000000000000000000000003ffe0000781e00000000000000000000000000000000000000000000000000003ff983ffff0180000000000000000000000000000000000000000000000000003ff98000780000000000000000000000000000000000000000000000000000003fc07bfff8e07c000000000000000000000000000000000000000000000000003fc003fff8e000
  | 0, 13 => 0x3ffffffff80000000000000000000000000000000000000000000000000000003fffffe007fe00000000000000000000000000000000000000000000000000003ffffc1c070180000000000000000000000000000000000000000000000000003fffff8380e07c000000000000000000000000000000000000000000000000003ffffc00781e7b000000000000000000000000000000000000000000000000003ffffc7c7f1f83
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x8462c2060ba5200000000000000000000000000000000000000000000000000084204206018020000000000000000000000000000000000000000000000000003c1dc0fd801ef00000000000000000000000000000000000000000000000000014b9c045115cf0000000000000000000000000000000000000000000000000000c66c02c8b27200000000000000000000000000000000000000000000000000001fbc0003f7df00000000000000000000000000000000000000000000000000000001fdbf6fbd00000000000000000000000000000000000000000000000000000000a0a82a30
  | 0, 1 => 0x2c2a0070251c0000000000000000000000000000000000000000000000000000094a8424711c8300000000000000000000000000000000000000000000000000242000500400000000000000000000000000000000000000000000000000000018c66ea2e8ba720000000000000000000000000000000000000000000000000018c666226098020000000000000000000000000000000000000000000000000010866e0200b25200000000000000000000000000000000000000000000000000108462020080000000000000000000000000000000000000000000000000000008c24c22e81862
  | 0, 2 => 0x242008d08c227800000000000000000000000000000000000000000000000000000008808822780000000000000000000000000000000000000000000000000036b5735b06c104000000000000000000000000000000000000000000000000003434235006c000000000000000000000000000000000000000000000000000001295730b02c104000000000000000000000000000000000000000000000000002d6a8474751c83000000000000000000000000000000000000000000000000002d6a8454551483000000000000000000000000000000000000000000000000002d600074740800
  | 0, 3 => 0x1215338902e31c000000000000000000000000000000000000000000000000001014238002e21000000000000000000000000000000000000000000000000000021119898a637c000000000000000000000000000000000000000000000000002d6a8cf4fd3efb00000000000000000000000000000000000000000000000000094a8ca4f93efb00000000000000000000000000000000000000000000000000094000a4f8082000000000000000000000000000000000000000000000000000080a00a0213e1000000000000000000000000000000000000000000000000000010888849926f9
  | 0, 4 => 0x12957b8b8ae37c0000000000000000000000000000000000000000000000000012957b8202e2500000000000000000000000000000000000000000000000000012957b0b02c14c0000000000000000000000000000000000000000000000000012957a8288a278000000000000000000000000000000000000000000000000001294638b8ae230000000000000000000000000000000000000000000000000001291538b8a412c0000000000000000000000000000000000000000000000000012804b8b882278000000000000000000000000000000000000000000000000001280438b880020
  | 0, 5 => 0x1bdffe02409042000000000000000000000000000000000000000000000000001bde63affbfe30000000000000000000000000000000000000000000000000001bcacfaff93efb000000000000000000000000000000000000000000000000001b1fb3ad33ff9d000000000000000000000000000000000000000000000000001a9f7bababff7c00000000000000000000000000000000000000000000000000195eafa4fbfefb00000000000000000000000000000000000000000000000000195423a4faea300000000000000000000000000000000000000000000000000036b57bdb8ee37c
  | 0, 6 => 0x2f3b91fd377f9d000000000000000000000000000000000000000000000000002e3b19f9af7f7c00000000000000000000000000000000000000000000000000273999dd9f67fd000000000000000000000000000000000000000000000000002f7b957d775d8f000000000000000000000000000000000000000000000000002f7b957d775d8f000000000000000000000000000000000000000000000000002739915d17458d000000000000000000000000000000000000000000000000001bdfffaffbffff000000000000000000000000000000000000000000000000001bdfff0f53d5cf
  | 0, 7 => 0x37a8cbdf9d26f900000000000000000000000000000000000000000000000000373dbbdd9fe7fd00000000000000000000000000000000000000000000000000373db3dd17e79d000000000000000000000000000000000000000000000000002f7b9dfdff7fff000000000000000000000000000000000000000000000000002f7a01fdff7e30000000000000000000000000000000000000000000000000002f7991fdff4dad000000000000000000000000000000000000000000000000002f7119fdfe6b7c000000000000000000000000000000000000000000000000002f6001fdfc0820
  | 0, 8 => 0x3fffffffffffff0000000000000000000000000000000000000000000000000037bdfbdf9fe7fd0000000000000000000000000000000000000000000000000037bdfbdf17e7dd0000000000000000000000000000000000000000000000000037bdfbdf9fe7fd0000000000000000000000000000000000000000000000000037bdfa8699a6f90000000000000000000000000000000000000000000000000037bdf3df9fe7bd0000000000000000000000000000000000000000000000000037bc63df9fe6300000000000000000000000000000000000000000000000000037b9d3df9f45ad
  | 0, 9 => 0x3d7eaff4fffefb000000000000000000000000000000000000000000000000003d742bf4feea78000000000000000000000000000000000000000000000000003d6a8ff4fd3efb000000000000000000000000000000000000000000000000003c200bf0ac2a78000000000000000000000000000000000000000000000000003d7ea7f477fe93000000000000000000000000000000000000000000000000003c3e23f027fe10000000000000000000000000000000000000000000000000003c3423f026ea10000000000000000000000000000000000000000000000000003c2003f0240800
  | 0, 10 => 0x3ebf7bfbafff7c000000000000000000000000000000000000000000000000003ebf7bdb8ff77c000000000000000000000000000000000000000000000000003ebf7aa2a9be78000000000000000000000000000000000000000000000000003ebe63fbaffe30000000000000000000000000000000000000000000000000003eb953fbaf4d2c000000000000000000000000000000000000000000000000003eb57bfbaeeb7c000000000000000000000000000000000000000000000000003eb463fbaeea30000000000000000000000000000000000000000000000000003ea043fbac0820
  | 0, 11 => 0x3feacffffd3efb000000000000000000000000000000000000000000000000003feac7fffd1ca3000000000000000000000000000000000000000000000000003fe043fffc0820000000000000000000000000000000000000000000000000003fe0435f540000000000000000000000000000000000000000000000000000003f3fb3fd37ff9d000000000000000000000000000000000000000000000000003f3fb38902f31c000000000000000000000000000000000000000000000000003f3993fd374d8d000000000000000000000000000000000000000000000000003f2a83fd353e99
  | 0, 12 => 0x3ffffe02409042000000000000000000000000000000000000000000000000003ffe63fffffe30000000000000000000000000000000000000000000000000003ffe638bcaf230000000000000000000000000000000000000000000000000003ffe62a6f9be30000000000000000000000000000000000000000000000000003ff9d3ffff4dad000000000000000000000000000000000000000000000000003ff9d2a6f90ca9000000000000000000000000000000000000000000000000003ff57bfffeeb7c000000000000000000000000000000000000000000000000003ff463fffeea30
  | 0, 13 => 0x3ffffffffc9862000000000000000000000000000000000000000000000000003ffffff267fe52000000000000000000000000000000000000000000000000003fffff5f57d5cf000000000000000000000000000000000000000000000000003fffff8bcaf37e000000000000000000000000000000000000000000000000003ffffea6f9befb000000000000000000000000000000000000000000000000003ffffe76759cc3
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 110 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 110 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 110 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 110 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 7 0) :: stateWiresD n (ids >>> 7)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 7 0) :: stateWiresS n (ids >>> 7)
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
  | 5 => 20
  | 6 => 426
  | 7 => 2243
  | 8 => 734
  | 9 => 9
  | _ => 0
def CH : Nat → Nat → Nat
  | 5, 0 => 0xf01a60ffe8f0c836de1469c7d9a25eddd180d922c2e1ec4cb8f35e72ad3d50b5a7f84918a35c9dd6a2e3e3517b30d80578541dd66dfec0ab55b2c8785503753a42b779a318e0c1a7188e615b0dfb5be7
  | 6, 0 => 0x16716f5b160c315a15a66114155c2731151ef48314c968a61408a6d3138eea8a1293710d12468813122a3819121c758111f6a69f112beca4106bf30e0fa22a3f0f8898390f3fbb520f30a6a30f19ec700f124bee0ebf98610eb903040e7e15130debb1ea0dbf4b5e0cabde0a0c79efff0c3077410c2a9c4c0bcc18bf0b1ccf780a8a47a809e01646099ad82c096e9438091eccf20919997808e9193f0897ec84077b76f807168e4906c001df065eb57006307106062f14f405f4395105a197e90541786f053f9f86053cd7d10505ca720502ca7804773d450229104301af582a01aac27e0187a4c00111388401013f3600ffd4c500e3021600b9d8bd00a23625
  | 6, 1 => 0x32e5408e32257abc3099cb893037bc2b2eed62162e973eaf2e6465742cce811c2be61f7b2bd1071b2b87ab452b81626d2b3f49ac29bb4707292f8a3b2909654c28cf661928ce93e328a4a83e2872ba3328236680281a6a4327fc79e327ad080c2779c54f273bbb93272c93bd2705880d26c09f4926acc7fc264006cf25d20d0b258fa56f249d0b2023e92d1223e3e51a23dd768222e74ca7213869ba20292edb2011aae2200e109c1fc92cf81f5cb9dc1e8255921e375b431dcf29111d600c9e1b2ade4a1acbab401ac91f151a0f2ada19c7b6e719ba301a197c44521926f56718f964911863fd7c17c1f8db179c54481797b46516ec765a16a61199169bd2c1
  | 6, 2 => 0x4e58e5db4dcff21e4dbfbbf34d8d556d4d84259f4d6d10f44ca384c24c30865f4c01ea4a4badbbbf4b02581f4aa1705d4a9dd6174a1426de48d9c66848be10a548558c394836f03147ece91247a42f1c471c98aa46253cd745a7f59844debf44445402504449f5954409d31843ab0e6e43984d6b434e857e42b779a3422c19c341cdfba6413a622b40a1d520406aeb143f17e77e3e0fc03d3dafa5e43da66f633d8e30e53d2c7c353ceb5ccb3c90e5203c86b61d3c21f90f3bd360a33b222c1b3afd2ed739cf80cd39a2116939270f8338ced832376135eb35dbf84635c7f4993540bfd43505b6fb34c5f9743480fa58345cc7b03402996c33a95ef333693c76
  | 6, 3 => 0x727718da727253ef722eeeb6705b5d9f704d5e587037bb136fd89f086ed6f5bf6e7107f36e5d6c3b6e5661bc6e2812e66e24e7616d6074136cc23b146c95d74d6bc0ca106b319a9b6adec8c96a45fe15695d162a692ba2fb689f85b8689d4a6b68962c4067a4845b660cf112637eec3e62ef3d9e629080c262816019621cd20f600ad1db5fde2b075fd0854f5fbac6fd5fa9c4225e9ff2d95e7088c05e3fd68c5de3fb985de38ba85d26770c5bb6c60e5b10b1b25aa8a6b959a87018592af3475871d44e5833dde557a1024a56488c3a551ff99a546ec5c4535e595e53346db95264a207522c1d2d5123c034510b81b64fa0e5564f9f11514f1bb8244eb19c7e
  | 6, 4 => 0x9700fa2696af18389596f4c094d05cba94ba3ca293bb68769339fee992c480a291495fea9138155890fd764c90e985a190ab1af68f2073e78e8df0778e0eb1b98d5eaaf98cb445068c9dac058c20b6ae8c1a8e7e8ab3df568a81f0ca8a63c16d8a5e4e3e8a5002bf89a882578980dac788bf2e0d88bb05488744a6f885c3c9ca844e44c0839d4e8f8312f1aa8312ea918299684781556ecc80feb7d980d851b580739fc77fafbf157f936f117f1fd1587ee807d27ed89cb97e7fdd457e159c437dc410ae7d6730d47cdf2fa47ca8f3cc7c039c0f7b2b17a17a1348b479e15a2878890f6f7793da377744dfae77259cda76fc3d0f76d2b1ee751113a074b250c2
  | 6, 5 => 0xc61131fdc598271cc581d55ac559b1f3c4230668c24f89c6c219efd3c0b25433bfcea96abfa40e66be9d15f9be4be64fbe32aebdbdc85e88bd41ff14bd36ed7aba36dadcb8335b93b5b54eadb511b645b46ce8cdb42e327eb36d65c4b3350d52b3088cf5b2f8b09db2db658ab24f00d3b148aac1ad439259acebe7f0ace24fd5ac34fcd2abd19988abc86761a72ca08ba621259fa5ab77aea4e6f963a4b989ffa49ab9a0a47ac71da43410a8a400ecdca3ab4432a345c7d7a296d0cba2737540a24442aea2295e83a20e55779f6b79719ec0d7899e5f0cb99ceb5ea59cbb25209c71fa569c6c69fb9afee4e099af20c798f89da998f164109860223597ac0d10
  | 6, 6 => 0xfed2e10cfd75c11dfd1d4291fcfcb63cfae73b35fac52187f9d7d4ccf9262a4ff8819b03f83a08a0f6dae056f5192827f46a6070f3d6a6a3f2da6a70f20efe76eef3064debefca4bea635f01ea589c94e8d9024ce5b5a113e1c9df61e0c5505edefcae48defb0a41d98dd0c7d9682be0d9238dfbd7da8571d7ca6921d792b42fd4d90fa6d3504c30d1ae18e1d04e8a61cfe56affcf8d861dcf034ff7cd47ff8dcc7593fecae7fde5
  | 7, 0 => 0x4a7431304824cd4046088880459b5e304427d3b042b899703f7cba003ae4e9903abb2f003ab13ef0375c6cf0330c8120318307a030dcc6802ea715a02e2bc3202dc927b02d6a72e02c16857029f514b029bda2f029aef9e0295a2700294122e0293b452028de01e028da25d0289e80802465a51023f5c5b02363de2020b934d01eac28901e3cad001cde88101c8376401b5ee8d01abdea4019fd767019f361a019c9fad01794b5f0165a78a015fcb3e014268c7013e3f930124c53e01189ba9011182d8010ac531010ab0bf00f9b8fb00f76a5900f5a3d200ea38dd00ce59c000b9120700b34936009aeaed00955441006fb9d30031a7ea002d875e00296567
  | 7, 1 => 0x8df973908d6f02608c7c03908c5dc3f08ba381d08b46af108b081660899ab530865d84f084ecf140844bf83081c74db081be466080fe2c307f90a6207f70b8707ed8a3207e4ea3e07d1c87f07c20e2707a676fd0790b29f078f1e53078c6002077a422d076636a7073d42b70737882a072f1b210715437d0709752007073daf06b031a2068bc39d06735b220663ee92065eb5700659598f065932810651b5d5062e761d06291d8306237d4e060f596e060e01a405f2790c05eb17b705e9221005e77d7105c61dd605ad2f34057c0b7a052aa4950526b2fd051f1fac05169eb00509fa1f04e553f804e37e8404d0089104bca65904ba8cc304aea85504ac2cb3
  | 7, 2 => 0xd3586890d15a3500d05cbda0cedf22c0cea20e10ce9b2880cd7607a0cd4b54f0cd412060cba81470c867e660c825c970c6ed2f30c687b0e0c60dcf80c232aad0c22507d0c0bf6ea0c0ba5d40bd3d3cb0bd0ae970bcc18bf0ba0f9160b985bbe0b8ad6cc0b88cc090b80dabe0b7f14bf0b76e6c50b41c7720b2c8ce60b2912830b2179b20af89e950af197a60ae653d70ae34fac0acf09dd0acc38510ab8b2690aad79ad0aa0caca0a7e53d60a7677f50a5e33fe0a3ff7660a2d481b0a01f69909ee1b6f09eb9e2109d9969709c0e32809bdf0a009bd51ef0989c7c3097689a809643386094cc1c4093e7356092be94c090dfc8408fadadf08fa445b08e6fd46
  | 7, 3 => 0x11bf1a8111bd50f411ae78c2118eca211188f51f1187183a115e1032114c695c11408e9a1120d6461119f0ef10de35ff109ef9a3109bbfbb109410fb108bef57104862a5102d8cd3102cf6ef101fadf41004efa20fec104b0fcb33c20fb1a7760f9aa5fd0f8898390f7ac0e10f78ea770f77871a0f76f4eb0f53334a0f1a8f2b0f1986a90f16fff20f06017a0ee7b93a0ee2d2210ed86b730ed019dd0ecc23a60ea800b80e974d5b0e90cf7c0e7e15130e7dd0190e79ef230e7515ed0e67dc250e5672a30e39d93f0e1f184a0e05ccb20e0550e70df565b60de1cc4b0dc23f740db9c7830d9dd24c0d8eedc30d7f85ab0d5a81df0d570f570d49c4170d4430e8
  | 7, 4 => 0x1640b406164042a216358c21161648bc1612f34116118174160c7aef1606144c15f022ce15e9498b15d3b4e415cb6ef015ba6e6315af65f1159392c6158c470e15776f951574b12d155ed0bb154b3952153fc09e153802db1535fac81517feab14e2d7e014db292014c7480c14b29a231480f23a14696ac214649f8f1433f3701409a61314009f0a13ea83c213e0e2a713dbc3bf13b3a35d13a8dfe013967e2f138cad00133c08ef13346ed1130a5a8912ff424112ddb43412cd450012bff5d612b8ab4112aabf8d12a8595d12892ebd12763853125d0b7e12590aad12348c591234695d1228cbf912245a68122261f8121617f5120061e011d306b611c1f92a
  | 7, 5 => 0x1a6a04de1a548add1a433cbc1a4058c31a33b1c31a0dc40d1a00275719fc1ed919f37e0719f2db1c19c7c79119b1d44819a917ce198b4576198916cb196672e1195f5caf19399e181921f28d18f302eb18ef4baf18eed24c18c40ebb18b0796518ac994f1891280c1883498818781c341862a4c91860cf55183afea71830634d182bf92618261f78181c7acd1813153418103f88180c2da517e7c6aa17e4d13d17ddd95917d64a9117ce2ba217cb86b117c5bde017bf920f17b7e34f17a3f1f5179c6b23175a929b171cf5b0170d4c581706ecff16b01e5416a611991695814b16859a0f1673385e1665ef1c166385a0165ce3e9165a143316573f00164f38e0
  | 7, 6 => 0x20df43cc20d561792065dc9f203e530f203dbfd6203a916820292edb1fed21a51fc92cf81fb72b911fa432931fa23c8a1f634b621f59336e1f3e5d811f3387171f2ee9851f15ac8f1efda3231edd0b6f1edb86661ed55caf1ea663541e8c48a51e19b2591dedee551de177831db4e0681daeb8c11d9e38471d98a19b1d948ff71d85da9b1d83b5c31d81c57f1d75a3ee1d68e5f71d6198e01d2a81d31d160c6b1d1165dd1cfd2fc91ca81a3a1ca481c01ca0b1831c8e80241c5d76581c1ffead1c193f401bc7d4b01bc210541baf8e761b9935371b8548e61b78d4bc1b6003b71b52f3321b1a2ca91ae9b4a21ac819931ac6cf551ab658ae1ab64be91a814813
  | 7, 7 => 0x262c82e82629067d260a164f25e4685525de985025d992dc25a9c205259fb2c9258a599a254b6a5725320fbe250b3e6a250aba5724fedf5924fc57bc24f59d0824f27cee24c9ba2d24bf6a3624b2b20a2491fa55246984012454ab9d2443fd3024429b14243971d5242f629b241eca5d2416c07e2414ae9a2409402823f0c29e23e92d1223e6546623e3ab762383a1de237fdc382373cc5223679dba2360aec52341f14022fd835122c96b3022c7351322c4f10a2289ec0b225693612219ec0a22040c5022016d1d21f73ff421e6cbde21de28f921c636b821bfee5721b5c2d421a5f96821997fae2177d428214d97092145e849213f9045213bddeb21331633
  | 7, 8 => 0x2a6540552a5617002a541ffe2a4b2ce12a2491622a245e7b2a222ab32a1706c02a121f8d29f9c57229ed6e3b29e0d67129da34ba29b291b72993998d2989cbc02971ba4029428e4b2934275728e3ecc328e1d56328bd116f28b64d0b28b1318528a4a83e28a46344286028b1285a6120285879f1284514cc2842fbd32823303428222a1a2803ddcb27d2573727c1256227b87eed279f070c27795cd1276fb0f9275958f2275880df2750b4f6273e087b272630b12724c80b2713cf002710b40c2707a0fd26f168c926eeeb7b26dd32d726d622c326beaf6f26bb2fef26ad119126a8a4502682d2eb267b41f526786863265b05052655fd64265363bb26396ad4
  | 7, 9 => 0x2f86b33f2f7e6ae62f7a6d102f67316b2f48cad42f3e6dd02f3594f12f2d39052f2cdf472f1d2f5b2efbd9642ec30bf92e8af7a22e8a65942e3b996a2e3a69332df877932df741622de6358a2dbac35e2db09fc22da7f5f52d93a3d72d7f44742d7484b62d618f3b2d52d1502d4fca342d4518622d3e70562d2f16c62d1894d92d17f6e82d06d0c22d014b912cf3c0ef2ce139a22cdf3e6c2cadd3bf2c86b1b52c7afb6d2c5dadfc2c58dac22c42325c2b87620c2b81faf52b5913022b43cf532b27b74c2b2253022b19bbf42b15732c2b0fca262b08f8cc2afee4492ad9fd9b2abd4cd92aa00b9d2a97a7b92a8c3c9c2a8999b02a6f28832a6cf0712a6c6154
  | 7, 10 => 0x34171dd8340993c534064f6c33da662c33d93c6b33ce134333b85c4333a8219a339be830338d9c583389f6ab336a01d23366c242334a7e36332a82ad3327d92c330bca3f330a8e35330961a632ecdd7e32d484fe32bc680832ba82ac32a1bcd532854622326a54bf3264f194326007a8324417603241705c32113f4a31ffed8331f5eab3318b16ac3185f30f318125c63159aba131389c99313027203129ad3f311dfd6a311853993112a29330eb45fe30e1709b30dee9b130de567830ddf49130dba21430d5282030cca4c4309e97613078e78b30705e06306f6ccb303037e9302ca777301b2a8530010ce22fbf35272fbbf89b2fb1aafd2fa88bf32f8af236
  | 7, 11 => 0x38abbdef389cbe3638962217388012b1387c2216386585533864ee273856408c385204ef38422411383a0cba382f747e381fcf143812097437fdfb7837a858aa37a858a7379a88913791ff6b376b796b37596ec33748575a3747e8a73743a61d36f3d80736e3b36d36e2575236cd76be36b521a2367ad4223669c03b366487033644f7dd36273865361d50e73615bd783609387935f2a55735e7486435e23d5c35d89aaa35a0b6f0359f67e7358e7c13357bcd5735787e26357193a6350ff6a1350a1aa334f524f934f3ec2d34ecd7be34d88abb34a771a734962a6d3492603134886bc33469cfe73466ebee345ddff5344da13934487e1234417d0f342cdee9
  | 7, 12 => 0x3dc07c953da1e2333d9457913d8f565c3d62290f3d5d39623d3e89f93d2562093d1f3f593d18fbc93d10cdeb3d0f7e103cedc83e3ce8d0283cd396533cc696da3cbde0b03cb227733c9f3cdf3c9926183c5112f13c407f353c3ab5c83c21b4153c0ce04f3bee29753be497a23bdc2ed73bbe60cd3b9f7aeb3b40a23f3b35cfbe3b33d6c03b08dcd23af9666f3af6ada23ae826bb3acedf3f3a8512d93a7742c03a678d5f3a64e63a39fa66b039f7e21b39de4fb639ddbebc39c6347939c282b039ae44eb39a3264a3977520139731d65396f572d3961b02b3956e3ad394f14203926b9f839234c07390ed69f3909b49e390153ab38ed825b38e1a69e38da452b
  | 7, 13 => 0x43555fb0434bdc18433f660a433cb82e432e5dba432dfd824325dcc443130f0343110caa430c7f9b4305883642e7b5af42c7651642b779a342b451b04291ffc9428dbbfe4270b5be425327d7424d728e424083084214fad141b8ea3b41b7ba0441b50f1d417515864149098f413f306a4110f4a8410d769640fe085a40eca96440e5429a40c11d8e40bbc127409c406a4089915f405e8a73405c8f3d4042c3c8403af74d401a1c4f3fed881a3fe000373fdba9f43fd62b933fb404613f5aa7ff3f5789763f4622693f2afc363f291ad13f15457d3ef484683ee6de3d3e791ea93e444aad3e3c0ae43e3a3ac43e38a55b3e277fff3de291263dd170cf3dce4f97
  | 7, 14 => 0x4a7c767c4a3f5f3c4a0d19744a0a039049f3d2f349eb066449e579ed49e3bfbd49bb2fc3498effba4987e82849787d0149585913493c34104939f53049148db048f0ff0048efd81348c35a8b47f0cb2247e43cbf47b76ea347a3d52347946ea94772c4c347703dcb476a5be94755b8444727debc471a541a471718c446ed067a46ec901e46df279b46de759446cefcc046c9322546c7cf0746bddc5e4687df064667f2b746260195460f5a0845f6b58445f28fa6459774c24563ccbf4526b4084519cf8c44fe769744f4548e44cd758b44ab1cba44834382445ca64c4458f2e5442e32fa43eb0c0643df582343db6ae443c469ce43c1fcc943a9f8484397d140
  | 7, 15 => 0x5059633d50490acd502b26864fff2dd54ff820184fb50f3e4fa260824f9d2f8d4f050fd04f0494734ef54bfc4ea817a54e9d19034e6d16534e5372144e3b68614e3a3a904e2ce2974e2566f84e18a5394de2370b4dd542384dd3ad484dc9c7c04dc4f8224d77b7814d6c43d14d3fd3814d3fd1c54d3c580d4d356aa64d0ce2f04d0bceb24cfd734b4ce115d74cd6bec54ca1aa074c8a818c4c7463374c70a3534c46545e4c29021d4c1e35cd4bff26be4bf147df4bacc54f4b9665454b8c97694b83f37a4b6978864b48acc94b25a97b4b236a724b21fba14b1cd1974b17d9624b0c2c394aee81944aee73794adf76294abd1d0b4ab9f0674a9a544d4a83c1d6
  | 7, 16 => 0x557f4cd955739b7c556f06955521817b551f842c54f505d054f251df54de0ffe54ba411f54b47b9854b456dd54afff1c54af2ec554a268625467b4c65462936b5421f2ba540a4dbd53f747b753ec72ba53dd4ed053ca920853b2be7253ad163d538ec419536b8d0a53466db853346db9533428bf530ec13f52dbe80452d64d8252ce9ec252839f995281620b526177285253af2952534f945248446852477438523dc21152184ba15209224c52018dc651e9127651dd55d151d2062b51bb2a0f513cd70c5139dea75137e929513663bd5124950151099cc650eadeb950dc89c550d8a92350c24f90509f5416508e1ebc507c4096506b190f50695857505beeb3
  | 7, 17 => 0x5c15a7e65c10eb415c0bbbc75bea2b975bdd230c5bb301c65b65c3955b3409c15b2acd595abc6cf25aa8a6b95aa52f8d5aa2af7a5a9f5dfd5a97dc395a97a4eb5a9469955a8322685a6afd255a5bc66559fcbebe59f11cdb59a3041859a0c2fc5996f4f5597e76b4597bfa89595c19525944924458e6c54658d7b5fd58b561005863a6435859718358413d465817addf5810d46d5795fc8d578e67bf578969f35770ff1d576f03e7576d4781576b2807574ab38e5727b7f4571462ac570c318b5707fb6756e8a03d56e6f7eb56c5d00a568e1c39568d8c7e567ee6cd567c7f51564030685618ad15561504715600570755eeb91a55d72eec55a5888d559d3a72
  | 7, 18 => 0x62c7c6f462bf39f9628e144f62729ccd627050f96247a48a622a4e0c61f427ee61de9b7b61de52a861d0c2e561cf8f7361ca400861aa336861a45f8b617c8feb610c35a86108511860dc0ef760c0e6cc60bd229660b772cb60afae3b608a33c1607f1ebe60774438604fd85a6049964d604693fd602f2d626008d5905fbac6fd5fa001255f4c3dc55ef408b65edbff035ed6a3f15ec5fd9a5ec2fe405ebac33b5ea6e3535e682cee5e427dc45e1bc49c5e13ada65dfe16575debf6475de083ce5ddab89c5d8bf1475d5fdc975d48a8d45d0ffb5a5d0b15675cea4ee05ce6bbf35cde0cce5cac1ec35c9fbd605c9b90375c91de815c50e6185c3b8dfc5c33c181
  | 7, 19 => 0x689b990368962c40684a905368439ee9682efe6168090f896805cfb767f849e667f1c0d367eb4a3067a2a106678eb54067891a30677dc39c677d8db967770155677213ae6761988367322581672edba167240676671ea51e671066ce66fd841f66fc748866e5ae6b66d044b066c9726066b2ba9b669e557366596eea663e596f6617db0a65fd862665e88a3d65d6d88f65b3f9f765961aed65438d016532bf6464f4abb564c8c42e64c5236664a20483649ea5e0648a2c2b646d8437646b28aa6452482b643ac4066433ac9f642e54a0641ca4e76413866e640f62e363fb6a7f63e50b4763b3242b63939f33637c7ea6636b8ef7631fb15363112f0b62d73fc8
  | 7, 20 => 0x6e0e67d66dec12c46de93f766dab2ce86d964c5c6d916c166d7e78d66d6074136d5b00e46d483b2f6d35546a6d2f2df16cfb7a1c6cf954796cdfaffa6cd622c66cb3a7766c96b4706c85f2fa6c79ed6a6c64553c6c4b6e046c41d5016c2bf7316c2229556bf899566bd670bc6bcb63fb6bbbe0b36bab48676b9d976b6b67104f6b3934176b1a64bf6b0d63fc6afc1fc26aefc37a6ac69eeb6ac5c8b56abf8ae76abcdfc56aa508c56a95be0b6a91b37d6a729fe46a6a7ad66a41599e6a2ef61d6a2e06a76a13aebb6a08bb056a0829146a00c0a569da0c1f69b21a1169b0c44b69ac5725699f003a694fc71e69218327691a8b436909bb466909685e6909578d
  | 7, 21 => 0x7597c94175576ffc7554e3867539d2697523065074e3001d74b7658874ae2b347485a1e9746a0e0a744ac9477394bd347393454b73823427736647aa734eaa0d73437dc273275b59731a9a37730cc97a72fca04172e9411572e5367072b28339727718da7247341e724693b772301b0f7229b8f672286c4f71e12dcc71c7957571c52b6a71c4843571b7c8f271aa199571a26241718aa31d717f4ee0715dd49f70fe4ee070f943ac70e34a0670607efa705b5d9f701d07ab701838507001f6a36fbebba96f9a15cd6f8476496f2349176f1741246eeb6aab6ee314666edb0ec36ec7a3626ec28c856ebe77696e97376a6e6dcf996e4e17c76e2e056d6e16b7eb
  | 7, 22 => 0x7dd765af7da51d3c7cea112d7ca8786f7c69c65e7c4c7c107c4bfba17c4260817c2f60d67c140d477bbafb617ba3c0797b86605a7b75c3147b665f577b25fb187ae6a9707aa157477a7f40357a55c08d7a44d4b97a399f0c7a3225fd79e15a2879d3e13a79c219c979952bdb797234ad796deb39791e9fb778e9916b78e3378f78d1319678bca81278b54ae278a6665978925775784337a87812897277cf974077ae3ab077abcbfa77a84497779ca86b777d854677728e4a7770db527746c83977231e6a77211a3f771f39f8771b4a3a76f6d5a476f0de3376df94a676d6e32176b871ac76b3c8af769ee49076863e3b76549099764e5f6176461d7276076036
  | 7, 23 => 0x84af188b849e475c8475b5338450d9fa844c6449840799a683fe99eb83e41464838f94ca833df9038323a63b82fee33982e72b3682e2ff4782dd367682b3ae8082a1ab69829835b3827963fa8267361782585f9481f114c781cf546f81b726b381a42827818c8a24817cef80817be6a2814d04b7812adf7780ab0b5c80977014809286e3808b00fd808a241e807ff0398069eaef806266ad805c907380381ef1802cffed800a6df47fdec0a27fca014e7f75ea277f65878f7f5f0e0b7f4af1e47f4590c97f2c02b87f0fc1c87f0df4cc7eddc2a37edbceae7ed8b83c7ec8813d7ead80c27e9aa7927e912cbc7e704a887e05acff7dffd2af7dfd47397dfb85ac
  | 7, 24 => 0x8abb56b98ab84b5d8aa3b04f8a8f77978a81f0ca8a7994f88a59424c8a4b88898a2ec80d8a0b34fc89ef6b9089d970208983ce31894ebb5e894cf98589312aef88fe5bb888ede02888d87a2e88cd013b88c15bf7888f7ea4884d6a8e882be4e18826fc39881af38988107e0887fff5c087e75edb87e4b66087bbe0dc876dd249876ab6d28752d38b871506e98709807d87062e3086d3f20a86cb537786c118bf86be95e986b63847869b759486981ab6868f8bfa867726a18676ba268660afd3861db7ce861a00e9860c78ef85f5891085d3fdb585c3cf3c85a623a085912956857f1b66855ab552854276918519787e8512e7e384f92b6a84d9addf84d1eb36
  | 7, 25 => 0x92d649fa92a02566927fc7e792734505921c7d4492002a6a91ed9b5991d9edf191d399d491b3cbf1919f9a92919ac8ae9196ca6a918c7c0391592acd9147ad6a913d8ae59117715e90f610e690e91ce690d48e739066fa2690247a8c9022657e9021a9fa8fe77d2d8fc284df8fa972eb8f9d1d5f8f7b76b18f6e24048f6057d08f5f11de8f20258d8ed741c18eac1af08e7679718e63fa418e52fbf68e3f8c778e3f5deb8e2302ba8e1426838df2ab598dd8c5358dc4f0798da6f0c78d1b84e68cfa91f68cd916648cd7ccae8cae17488c66e23c8bf8e0e98bda66da8bb785dd8bacebb78b8fda438b7531c58b37e8088b31c58e8b1fd6d78b1e27148b105bec
  | 7, 26 => 0x9aca79e39aabbbef9a8abc959a88f9d89a6914bc9a6324e39a55e6669a4655a29a3389189a0d45959a07492d99f80ac699ef520099d8cbd499ce680e99c74fee9998b674998432bd9978ab00996ad43e98e9771598bfc76298a19efa982c402a97f3060497ec88bb97d874bc97ce2acb97a002259791a640977488ac974dbfb49736bddf96f41ab796b2164796a2e0f996964552968d4d5f96885ed1967fbfcb9667f9e59630ff519625511595d4c56f95872ae69570da099566b56d954c87d994fb6bc794d3db9f94b8834e94b791e694ae151694aba5ca94a8304894a609ff949f308d945f3018942f197093f09492932ed1f7931be89e92fea01592e33b3d
  | 7, 27 => 0xa1f2e5c7a170cb80a1537f86a1483727a0f696e5a0c27a1ca0c208bfa09db9cca099d7c2a08759d0a07b3991a05f6e2fa0566735a0369f44a02ef21ba0219339a0178350a010db98a0092fe09fd738f39fada3039f8732b19f77feb79f76ec7a9f6868319f631d9f9f5eff5f9f5ea4e59f55b6a39f3584529f28b2e59f1c706f9edbc97b9ed600aa9ebfb44d9e9360949e8581b59e5f82759e5f4b7a9e5adc459e56566f9e418da49e1370af9daae7359d9a91c89d99351f9d648c2e9d0504429cf2a1969ce7c5ba9c9b27e79c1ef4619bfb29749be7a9099bd78ad69bbf435b9b9060219b3ef8b79b258fe99b1dd7b09af9d2839af6890e9aec1f2b9ae5da44
  | 7, 28 => 0xac4df83bac38c2aaac2d59fbabe9eccbabb3dcc5ab9f69a8ab55c58daaa935daaa8df529aa00aaa3a9f3d131a9eed033a9647ee6a9585d29a8e78fc4a8e4ad46a8cb32a4a8c9d8aaa828f69ba827e4dca8193e84a7fc18f5a7fbc882a7ea78b0a7dd5251a7c9a009a7966e15a73b62e2a71e49bea6f3a76da6aa7b4ba6a209e6a60a91baa5766eeba57519cca5141b3ba509d3d0a4ef705ca4eede4aa4eb786ea4c4fe3ba4ae7b11a494c22fa486a606a44634c2a434b4b6a4212d34a3f399afa3f2435da3ad5187a39dd69ca39257a9a38922d9a37956e6a3697d85a32cb193a3147353a2a97873a2a24eeda296d0cba29245d0a26ac20ea25e4bf1a22b6a16
  | 7, 29 => 0xb6459460b635de6ab6251136b623fb60b60f96a1b5f36f3fb5995d73b593ef12b58ba30bb55daf2bb511b645b4b838bfb4abe74eb47be621b43f5990b432738eb41b0a9db33f92c7b322ff62b3216c62b30843b8b29f981cb27cccb0b24f00d3b2227a10b2131be6b1fe93d5b1d1766ab1cb86b2b1c06140b176cf6cb104f48eb0e1dcffb09b89e2b081bca1b06379a0b05c264fb0377981b03615abb01e39c8aff20c80afd23c0caf9abc18af80d0deaf79b774af75ff26af364f0eaf057aaeaef5af7aaedf1679aed6ebcfae6822efae2a8799ae1bf85dae064aa9ade6658dadbf072fadab993dad9c65faad9683faace974c5aca9b064ac7b9e87ac610a62
  | 7, 30 => 0xc019f768bfda4f41bfcbcf73bfb0cba3bf7d00d2bf6247b9bf58e8f0bf57afedbf01fb40befa2055beea5a39bec33186bec0a575bea336b7be51e5eebe4be64fbe18d688be0ade22bde1cfb5bd82ee2abd48b01bbd41015bbd386403bc87e6edbc878e76bc7e8f37bc63c02abc545819bc398ae1bbd772e5bbcc115cbba736d9bba66d37bb80d0edbae9d770bae1c4e0bad4da24ba558546ba45dd7fba231cbbb9e4f0ccb9b83f34b94d1047b932cbabb921fd5ab91d4ce9b89c56bbb85c2f59b81d78f4b7f92244b7b92ec7b793d28db7892a55b78864c3b7784d34b72f93ffb72628a3b71329c5b6e98fdcb6cb1964b69c07f9b691c424b6855c3db64eb09a
  | 7, 31 => 0xcc375d6acbdbb155cbd77c2fcbb8063dcb7bf774cb7281a8cb6178aacb46a5f8cb3988b3cb2d7f47cb2d12cccafe9774cae6a019cac2eddbcaa28a59ca8af8c4ca740502ca6c9484ca5290e6ca2351cdc9fcc544c96f57afc9656ec8c8e3e5cfc8d8951dc7f451a9c71007f0c6f8273dc6c77138c6631c17c63e6ab8c60d321bc582c47ac576ef75c54fca04c5368674c52f7576c518bf53c4e635f6c4a50f80c4949487c46ac8f7c41566b1c406f821c3d681efc3c26a3dc3b4db41c398766ec367270ec3651e39c364e4f4c31b6fd9c30e22efc2db04abc2bc05a5c285e459c25c674ac2363c82c1eeb825c1ad95ecc19d30e4c152b13fc111313ec0d8bcda
  | 7, 32 => 0xde7f46b1de2834c3ddf155d3dd8ed5d6dd4db3aadd420304dd2a54f0dc5b4c2ddc52a6e6dbc7af05dbb7842adb3a67f6db37660edb29872fdb23cb92da650bedda4ab022da411fa3d9c29a4fd9891486d96359b3d96035f2d9588732d8c00a96d8811cb7d86386c7d78a0a44d786c099d7799b21d70862e2d68b73c0d67f4dd9d67aeb44d5735722d445852fd3dd3852d3ab69cdd3980975d3152e0bd30f653ad2c6073ad2b422bed2a903ffd2a62dd6d29440d5d26d319fd2370a95d1145570cf96c9c3cf84fccdcf770a8ccf384970cf2fed9ecf0b0317cf010deccef767cfce3dbbbece252d20cdf98342cdd6b28fcdd2d617cd3bc669cc639849cc396419
  | 7, 33 => 0xed37c018ed35f865ed215bcfecc601fdecbba0bdec6b46deebc28ee5eb949f2aeb7dc701eb03cd4beabec0cdeabbbb9dea766cbdea5d5ff0ea58eba1e9f83c15e9cf7cc3e9a1d114e995372ee96ff558e94b1ad5e878be20e8529c71e7f96942e7b301e7e7b0d071e729414be69515eae609d82ce606f433e4e54ac1e491a641e45a7bffe4489ffce3d420a8e3ae621ae3760cf3e358b1ffe31a7a5ae3018797e2ef9098e2da3c15e29b9837e298b8f8e274b8a0e24960d0e21fca1de1cc7a45e1808a81e1283faae11bb465e1151f08e0b9173adfeb71eddfa277d1df9d82a0df8ae938df7206c2df64decadf204264deff409cdede789bded5d017dec9dac1
  | 7, 34 => 0xfeb8db38fe89ee6dfd904c97fd1e6eeafd16c02afd0a6dbffcd3d19afc78f6f8fc6afe7dfbefb591fbec0709fb55f38cfb52609ffb379514fb314dddfb2339d9fb195303fab495f5f9872d4af96feb04f94691eaf9050bc6f8b72109f8202e5df80299a1f7dda69af779760bf766edbbf6875a6cf683528bf6535463f6281cb5f5e5463cf5c3fe68f59835a5f58f108cf577d637f503ca7df33b5fd0f2f3ae00f2d35972f2854adff25014fff1d8e4a8f19fcd6bf1914f74f17a65ebf171c893f12be4b6f10d01a6f0f8df95f0c52c6af09b8930efb37741ef75fb71ef444dcfeeb70349ee9ef80aee5bfb02ee44a0bced9de86aed86fa4eed7abd14ed56b179
  | 7, 35 => 0xffcceadcff88f5fdff77da54
  | 8, 0 => 0xfd4c3f50fc22fb60f6b9a140f5c5cfb0edd17080ea68d810e8414b20e783ebe0dfb96ef0df078900db675560d9cbe430d91ebc20d52c9a60d4d98860cf91d9f0cea20e10cc7aa850cb3009d0c867e660c2cfbb60c167f100bb2ffb10b989d440b41c7720acf09dd0ab8b26f0ab7b9ae0ab0afbb0a9628be0a172c4909ee1b6f08d6f0260878675807d82e3c07bd347d07af559e076636a70754ea15075140fd06ecbabd06b07a03066344250590310f05869eb105169eb004d0acec040745c603e36454036df150033b05b5033a727c02e9d44b02d5abde0291d00a024a740d023c952e01a603fb0188fb4b01283a1700dd496a0086a50c0064991500103def
  | 8, 1 => 0x1e17d8601e08e1531d989e101d81c57f1d73f5661c53b96d1bea35011bde45011b70b1901b325a461b1036f41a5d39541a45ab1d1a4058c31a2bfa9c1a0ece701a0dc40d19f08aad19e3604919deb3e219b1d4481979f4171923eb0b191531f41900f42918e3fb0a18787ffd17d07b0017a820261729918f16e8db1816b50ee9168a4efe1662ea0a1606144c15f86a801581f8c81561a43a1528ba3c141a4f1c1415063f1413d60814121a0c13b5da6d136d10ac131bfefa1317dd2b12baa67712b8ab4112ae5da3129997eb12798028124e263511ed84b711d748061187183a11761aa81142fa411134c93410d1aa96103ead2a102d8cd30ffdfe370ff07395
  | 8, 2 => 0x2cf3c0ef2cf085992cb7e2692cae27f22ca821632c9946a22baacaed2ba0a43a2ba064522b48380c2b0f56702a7c85282a6cf0712a6bdfc02a5e00e12a5175e42964176b291abe562889888f2882e2b22775450f2727707326e36c2426d2458e26beaf6f26bb2fef26aa53c3265363bb264ea12126396ad4262d41fb25bece64259eb5302509c4b824cb7b292485a934246ade96246554a62429651523a7fde62398f310231857ea2310763b23038dd422ea3ac022daf26b22c7351322543c1c21e9d24d2179389d204aaf2d2046aaad203e530f203cd04e1fd3d3851f9bef851f608b651f3d31db1ee4e3db1ebb13731eb3facb1e8eec381e739d441e7359ed
  | 8, 3 => 0x3d18fbc93d0124c93cedcf813cd7d7c23c9f3cdf3c9dc2fe3c9d75a23c8fe41f3c3d49423c39fd5e3bf3e2703bd0b7833b76a7473b3c318a3afd7b253a8b9b213a8b1a653a4766343a305add39de879e396f572d3950034038ad846e3899ed18378f31e83724f45b36c744ae36b6da9236ad51603678c0eb366fa272363c57f436224d1b35d89aaa359aee6d357bcd57354bc4fd3518dab134ceb8d134746a9f34744a7f342cdee933d93c6b33ab0d08333d92c433193e9a32e7627a32e64fc53264f194319b3e42315024ba31381b073122199e30f26f092fbf18df2fa1c82a2f7655c82efbd9642eedfa852ea0b9112e46479b2d770a592d6df75a2d014b91
  | 8, 4 => 0x4dc27b5b4d2b306b4d0476064cfd734b4cd8ba054ca60af44c4c79c44c1e35cd4bf147df4bb8974e4bb13b214b7591cb4b62f61f4b02825d4aee73794ac0774d4a9f53ac4a6707154a0d197449d602e849ccf756499cfa0a499b08ca49148db048f889f848b0ac9d484e6acf47f69d26475141bb46e1bded46e149a24696c818465e79d54609964845c07cca457c5ed145179a8f44cd758b43cee64d43b9f0a343b42571433f660a4309ffd84305883642b779a342815d8a41d9fb7841d622d341a8390641a4b5d6413f306a40bb2834405c8f3d40455b7a4025ca0a3ffca0873f49363a3ee6de3d3e277fff3dff89d03df1aaf13dc32c533d8620523d6d0b96
  | 8, 5 => 0x5ec2fe405ebcebc25e06e6065debf6475dc82fa15d93d62e5d7bf2db5d6275f45d3a46645d2e415c5cde0cce5c91de815c0095e65bff541c5bdfea355ba915895b4388f85af03eb05a437adf5a17fce059f223e559e9c31b59d66aa05992adb05923c1c65806ebe256abec62568ff7f15640306855ab6c465592bd7c557f4cd954b47b9853b7a8b553b3d16b5342fdb7531915d15316929452f2fea452e996fb52943af552942b7251efbb6051d2062b51bb2a0f516924ff515c291951007c3a50a706e85059633d5038abd64f943bc44f624ff44f490be64f0fba7a4ec05ebd4e79bd534e5bae794e1db72a4e0e9fc94e00c0ea4de27c5e4de254b54dd11167
  | 8, 6 => 0x72e03d9b72b28339727daf3d72739f547263b2ee7260e48f71fb25a271be65bd70cdf07470c4152b70946692707cee8d6f3b46226eba99336e9f1e276e834bca6e38e6f66e34ebde6d9b14bb6d483b2f6d45b13a6cd622c66c8fa51c6c4b6e046bed6d236bc490ee6b89f08a6b7c11ab6b58c0516b46b4d16b1be3666a4fc62d6a4f22086a2a46cf6a0139de69d0a4b0692e70ee6920920f688d1b55683fb3fc67044c4c66fb4c916554bad164ffcc4e64cf00c5647899486449b75d640159026379a67663669d95633af0116336351163275f156292bf226284e04362542af861f427ee61ca40086129ea2960d1580460c016456001a2b65f5d13a95f2a6349
  | 8, 7 => 0x8a7994f889f226db88f823fd88edfe0d88ede028886bb2a5881ad29987ca80ca877910e2876dd249872610b887080352869b75948635a6fc862851b985f48e9f85e99b5485210b03850f030e84fbb42083d9bb2c833df90383233d8082ddd8a581b633a5804281917f4590c97f27d8097ebd26667dd5c4a57db1e1917dad4e397d776c2f7d356db97d33ff317cea112d7cd372a07c0721267bc86ac17b25f4ae7ae97d0f7a85129f7a2bfc5d7a2bf4367952d27478f04d34785a178977f10ba277d135d07770373f7733bc5377211a3f76fcab1e76f0de3376eecc3f76db0b2e76bdf4b9764e5f6175ee73ad7521769374e1bd6173f60c3a73a4532b7333c42e
  | 8, 8 => 0xa8d69abba71939e5a6395456a62fa927a5cabbeaa5103ec2a36baaf7a1946574a141bf77a0c045e2a0b26703a07b39919ffd08839eab30d29de9f1209d42bc1d9d3508f49d2d50bb9bfcd7929b71391a9b34b1219aec1f2b9a81c9ca9a36658d99bbfbc9997d4564996c23f4992721c2985a34f7984899db981b7e9297ec88bb97012b8496e3fc3596a4b77d9680ac86967182b59603a49895a996be94b8834e94331b659409b1f09396353d92b08ece908ca4449074f28c906d26118fa4cc1f8f9d1d5f8f6680978e7679718e4941358e2374cd8e21c9a38d6fdaea8d3d413a8ce77a638c8386ea8bedc1998bbc73f08b7e195e8b3e939c8ab84b5d8a8bfac7
  | 8, 9 => 0xc7466283c707ac1ec6398efac5e58a67c52f7576c4ac2c82c483e9fec4605fcec3fbe96fc3d681efc398766ec37f968dc31b6fd9c30bd3fac21dcfbbc1a069d3c16463c6c1043454bf46884bbef4bb49beb2f988be4f311bbe107ab6bd2744b8bcb2dff7bba736d9bb04b807bad4da24bab08b31ba477786ba45dd7fb81d78f4b7a3f583b6edc245b65f3e8fb644e080b52557b8b4d0d4a4b47be621b315333eb2dc7687b2572353b22e7c90b210ca3fb1b17014b12375bdb0ec7e1fb080f6ebb04d71d7b00d02d1afebec7daf01b67aadab993dada32de2ac23afedabe5308aab94b348ab681b8eaabfa2cbaaa935daaa38618da9cb11c2a98c5b5da9647ee6
  | 8, 10 => 0xeeae7dabee22ff53ed71b5aeeca193e2ebc28ee5eb7a065ae8f19d4fe8b54ab1e878be20e5d4dd4ce575a6eae33582dbe32cc12de2f7dbbfe2f02cffe25263cde1283faadfeb09c7dfa5c541df71e0b2dede789bde2834c3ddfd151add9de376dd4db3aadaf5c757da0af02ed9ed2281d988b69cd96359b3d90de9d2d8c00a96d7c2c847d7c0c947d7661623d69e993fd5d7c256d56748abd4fb6d4fd355d4ffd3152e0bd30f653ad2da325bd27a66b2d1d3f658cf84bc20cf6e15b1cf2fed9eceecb93fceeb1ad8cecb96dfce8cc780cdb20f90cdae7ca3cc0d7bc5cbfcbae9ca5eb5a5c9e24337c9d88a90c8df6e8fc8d8951dc876c3bec7ad77bcc7554d2e
  | 8, 11 => 0xff8b32cafe9afd92fe091979fcb4afe6fc7cb7dbfc3e0176fbefb591fabc44b5fab495f5f96feb04f9323ec7f8b72109f80fe67ff7fbcecdf762f14af6657479f5493ef0f5210d0ef50771aef3e60244f33b5fd0f2854adff1c31697f1c1f496f171c893f14d1f92f109fd47f0107b11efeaeca8ef0e3eb4
  | 9, 0 => 0xdd9de376bad4da249b34b1218a7994f82eedfa851e7359ed1729918f1561a43a1142fa41
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 5, 0 => 0x8000000010510b00184324c830100000000c810900000000c910a0018c2148430100000000c81090018c2148430100000000c910a0000000000005000000000210800000000000100000000000014000000010510b00184324c830100000000061080000000000000000000000a108000000000000e0000000002108
  | 6, 0 => 0xe10100000520c52010000000109107000000480e20100000000c4107000000380a20100000324c820100000000121040000002806201000000000e102000000000210300000000000010000000000006000000380a2000000000006108000001044020000000540c5200000000480a2010000050484200000000000e10300000000061020000000002108000000000a103000000000a105000005308520100000000021010000000000011000004350c200000000480a201000000000000500000000c51020000000006106
  | 6, 1 => 0x5000000480e200000000000610300000001091020000000002106000000000e1040000000109102000000000610800000001091070018c214843010000053085201000000000000f000000010910600000520c520100000000c910a000000380a20100000000121000000010440201000000000000a00000524c4201000000000a10200000000061020000001802201000000000210000000000c910a000000010510b000000000a100000000001210300000000c4106000000001210700000000061000010d5150c300
  | 6, 2 => 0x610800000544c4200000000380a200000000000610200000000c910600000028022010000000006100000000000a107000000000a10300000520c5201000000000e100000000000e10600000000c51020000053484201000000000a1050000000006101000000000210200000314c42010000004806201000000000a1080000002806201000000480a2000000000000012000000000610800000000121020000000006105000001044020100000000021070000004806201000000000e10000000314c4200
  | 6, 3 => 0x18022010000050105205000000480a200000000480e2010000020480201000000000a1080000000000010000000000e1030000000012104000005348420100000000000140000004802200000000000210500000000021080000000100105000000000a1040000004806200000000000a107000000280220000000000021030000000002107000004350c20000000000c51020000000002108000000000e1080000000109106000000010510b00000304c0200000000480e2000000003806200000000010510b00000324c8201
  | 6, 4 => 0x48022010000002806200000000000a102000000000e108000000001210600000534842010000000012103000000000a1030000004802201000000480620000000000c510300000000000110000000006104000000180220000000000c5102000000000a10800000000c5103000001044020100000001091020000003802200000004350c200000000380620000000000c4106000000010510b000000000a10600000000000010000000000008000005404120100000000021020000000006101000000380a2010000003802201
  | 6, 5 => 0x10440201000000380a2010000053105200000000000a106000000380220000000000061020000000012101000000380220100000324c8201000005350420000000544c420000000001091070000000109103000000001210300000000000090000000006106000000000a105000000000210100000510c920100000000c81090000000109107000000000000700000038022010000000000007000000380620100000028062010000001802201000000010510b000000000a106000000001210200000000000000000010440201
  | 6, 6 => 0x5350420000000324c8201000000010910600000000121000000053085201000000010510b0000002806201000000000000000000214842010000000000011000000000210800000544c420000000000021060000010440200000000000210300000000c910a00000000000100000000000005000000000a1000000001802201000000000a103000000380220000000001091070000000002100000000001210300000544842000000000006103000000000210800000000c4106000000280620000000028062000000000000008
  | 6, 7 => 0x5000000000e1010000000000012000000000610000000028022010000003802201000000000210800000000000080000051480200000000000210300000304c020100000001091060000000002101000000000e1000000000012103000002044120400000000c910a0000000109102000000000000300000000000000000000105105000000000a1020000053484201000000000610300000314c420100000000121060000000002103000000000a1060000000012107000001044020100000000c41070000053105200
  | 6, 8 => 0xc910a00000000021060000021484201000000000610100000038022010000000006108000000000e10500000018022010000000012102000000010910300000314c4201000000000e10600000000021070000051101201000000000e1080000000002102000000010510b000000000000b00000000000000000000006102000000000210300000314c4200000000000e108000000480a200000000000001100000000c41070000000006108000000000000e0000000006106000000000a10300000214842010000000012107
  | 6, 9 => 0x210800000000c8109000000000a10100000000000140014d4150430000000001091020000001802201000000000210800000000811000000000002108000000480a200000000001210200000000021070000000002108000000480e200000000010910600000048062000000010440201000000000610500000000c5102000000000e10800000000021080000002806200000000480e20000000038022010000000006103000000000000800000000c8109000000000e108000000000210300000038062010000000000014
  | 6, 10 => 0x520c5201000000000000b000000000000f00000510812000000004806201000000480e200000000000001300000000121020000002806200000000480620000000000c41060000000000001000000480620100000000c810900000524c4201000000010510b00000314c4200000000000000900000000000100000004806201000000480e20000000000c510200000000061060000000002108000004350c20000000000021020000001802201000000000000a00000000c810900000000c510200000000021050000000002105
  | 6, 11 => 0x8000000000000800000000000000000000006102000005304120100000028062000000001802201000000000210200000000000010000001802201000000010510b000000000210000000000021010000000006100000000000000f000005404120100000520c5201000000000210800000000121030000000006100000000000a103000000000001400000000000050000000006104000000000210500000314c4200000000000000100000531052000000000006104000000000000800000000000080000000002102
  | 6, 12 => 0x380a20100000104402010000000000005000000000e10800000018022000000000002108000000480e200000000180220000000000021080000000000008000000380a201000001044020100000104402010000000006107000000010910300000048022010000000002108000005310520000000000c41070000000000010000000000000a0000001802200000000001210100000000c4106000000000210300000510c9201000000000000600000000c910a0000000000010000000000a10700000520c52010000000012106
  | 6, 13 => 0x1210200000104402010000000000014000005404120100000324c820100000000021050000000012105000000001210600184324c830100000000c910a
  | 7, 0 => 0xe1040000000101101000000000a1020000000109106000000480a201000000000e10000000000121020000000002100000000008510100000000000000000000006106000000000e1010000000002106000000010910300000000021020000000012103000000000000000000000000030000000000014000000000610200000001041000000000000000000000000210100000000c110100000000021050000000006106000000000000400000000021020000000000004000000000000800000000000140000000000006
  | 7, 1 => 0x10910200000000121050000002802200000000000a10100000000061000000000002106000000010910300000314c42010000000000002000000010910200000000000020000000000009000000000a100000000010510500000001091070000000104100000000000e100000005404120100000304c0200000000280620000000000000070000000000001000000000a106000000000001400000001051050000000002101000000000000200000000c51010000000109102000000000210000000000021010000000000008
  | 7, 2 => 0x40000000006106000000000610100000000061040000000000001000000000e102000000000000700000000021010000000002107000000000a10500000000021050000000000012000000480220100000000000000000000000007000000000a1070000000000003000000000000500000000121000000004806200000000000610300000001091030000000000014000000008110000000000061010000000000014000000000e10100000001091030000000000007000000010c100000000000a1030000000109103
  | 7, 3 => 0x210600000000000030000000000005000000000e10700000524c420100000000021020000000105101000000000610100000048022000000000109106000000000a1070000003806200000000000a100000000000e101000000000000300000000401010000000012107000000010910600000001051050000000000010000000000001100000000061010000000000006000000000000500000000000070000000000001000000480220000000000000020000000109107000000000000300000000000030000001802201
  | 7, 4 => 0xe10700000000121000000000002105000000000000b0000000000002000000000210300000520c520100000000000030000001802201000000000000700000000000070000000000008000000000e10200000001091030000000041101000000000000a00000000021000000000012102000000000001100000000000070000000000008000000000e10000000000021010000000000002000000000a101000000000e104000000000000900000000000030000000000007000000000000700000000000030000000000011
  | 7, 5 => 0x1200000000c410700000000021020000000041100000000000e10000000000000070000000000008000000000e101000000000000b0000000000005000000000610000000000021050000000000008000000000001100000000000020000001802200000000000a105000000000210400000000c510100000000c510100000000c5103000000000610000000000061010000000006105000000000000000000000000030000000006105000000000610600000000121010000000006100000000000000f000000000a103
  | 7, 6 => 0xa00000000121030000000002106000000000000900000000000040000000000002000000000e10000000018022010000000000007000000000001200000000121060000000002100000000000a101000000000a103000000000e1050000000000003000000010910700000000061000000000006103000000000e103000000000000a000000000a1010000000000007000000000a102000000001210200000001091070000000006101000000000210500000000000030000003806201000000001210100000000c4101
  | 7, 7 => 0xc9100000000000a10500000000000070000000000003000000000000200000000021010000000002107000000000a1020000000040101000000000000400000000061040000000002103000000000000200000000061000000001802200000000000a107000000000e1020000000000007000000000000400000544c42000000000000010000000000a1010000000000003000000000210100000000000110000000012100000000000a1050000000000000000000000210500000000c510200000000000090000000105101
  | 7, 8 => 0x800000000c510100000000c9101000000000000500000000c51020000000000002000000000a104000000000a100000000000000700000304c020000000000121010000000000005000000000000300000028022000000000000009000000000e1060000000000000000000000610000000000021000000000006101000000000a105000000000000500000000c8101000000000000800000000000010000000002102000000000e101000000000a1060000000109103000000000610100000000000140000000012106
  | 7, 9 => 0xb000000380a200000000000e108000000000a104000000000610600000314c4200000000480a200000000000e100000000000000000000000c91000000003802200000000000210500000048022000000000000011000000000210100000000000050000000000007000000000000300000000061010000000006102000000000a10300000000000120000053085201000000010d101000000000a100000000280220000000001091030000000000003000000010510000000314c420100000000c0101000000000e104
  | 7, 10 => 0x6103000000000a105000000000e1030000000002103000000000000400000000c9101000000000001400000000021010000001802200000000000000a00000000000010000000105105000000010910600000000121000000004802200000000000e100000000000a1000000000040101000000000e10400000001091060000000002100000000000e101000000000a1010000000006100000000001210400000000121000000000002101000000000610500000000c4101000000004110100000000000010000000000007
  | 7, 11 => 0x3000000010d10000000001041010000000000005000000000210400000000000020000000012101000000000e105000000000001400000324c8201000000000a103000000000a101000000000210000000000c51000000000002101000000000610700000000000010000000000002000000000000300000000121040000000000002000000000000300000000021040000000006101000000000000c000000000e10200000000c01010000000109106000000000000a00000000061020000000002100000000000a105
  | 7, 12 => 0x800000000061010000000002100000000000000b0000000012103000000000a1060000000012102000000001210100000000021030000000000003000000000e100000000000e1030000000000001000000001210000000000121060000000002102000000001210500000000000050000000006107000000000a1000000000006100000000000000100000000061000000000000006000000000210600000000000060000000012103000000000001100000304c0200000000000a10100000000851000000000000005
  | 7, 13 => 0x6102000000000000a00000000811040000000000002000000000e10700000000021080000000006100000000000e1070000000000002000000004010100000000000050000000006101000000004110100000000c510300000000061030000000000000000000000e10000000000021050000000000004000000000e1040000000000008000000000a108000000000610300000000121000000000002101000000000a101000000000610100000535042000000002802201000000001210400000000021020000000000005
  | 7, 14 => 0x200000000021070000000000000000000000000e0000000000003000004150420000000000000080000000006101000000000e104000000000a103000000000000f00000000000030000000006101000000000e1030000000002102000000000e101000000000210100000000000030000000006103000000000e10100000000c1100000000000e102000000000210100000000000070000000002102000000000000c000000000a10000000000000040000000002104000000000610200000000000030000000000004
  | 7, 15 => 0x12101000000010c1000000000002100000000000210200000000021010000000006105000000000e1040000000006106000000000610200000000000060000000000002000000000000100000000000030000000000003000000000e103000000000610500000000000060000000006102000000000000700000000000020000000105105000000000e101000000010c10100000000000060000000000000000000000000900000000000080000000000008000000000000200000000061080000000006107000000000a105
  | 7, 16 => 0xa10200000000c4101000000000e1050000000000001000000000a1040000000012103000000000a1030000000002101000000008410100000000000040000000006101000000000e1000000000006104000000000a1080000000006100000000000a1070000000000006000000000e108000000001210200000000000070000000002108000000000210000000000c0101000000280620000000000000010000000109107000000000000200000000000000000001802200000000000000200000000c8101000000000a101
  | 7, 17 => 0xa102000000000e103000000000a1070000000012101000000000a10600000028062010000000000000000000000a10200000000401010000000012101000000000e10700000000021050000000000009000000000210200000000061040000004806200000000000000600000000021010000010440201000000000610000000000841010000000006103000000000e10500000214842010000000002101000000000a1010000000006100000005350420000000018022000000004806200000000000000e0000000006101
  | 7, 18 => 0xe10200000000c910000000000000020000000000002000000000a103000000000a10000000000000060000000002100000000000e10000000001091020000000006101000000000000b000000000e1010000000000001000000000e102000000000000f000000000000a0000000006102000000000610000000000000020000000002103000000010d1000000000000002000000000000b0000000000008000000000e101000000000000400000000c910000000000021060000000006100000000000a1010000053105200
  | 7, 19 => 0x10000040500200000000000a100000000000001100000000000020000000109103000000000001000000000021010000000006100000000000610000000000c410000000000061040000000012101000000000e105000000000a102000000000a104000000000000100000000000110000000002101000000000210600000000000120000000000000000000000a1060000000000013000000000a1010000000000004000001044020100000000061060000000006103000000000a10400000000061000000000105105
  | 7, 20 => 0x7000000000000200000000000050000000040101000000000000000000000000010000000000000000000000e1020000000000003000000000000200000000000060000000006100000000000000300000000061060000000006107000000001210200000000061080000010440200000000000a10100000000000090000000109107000000000000600000000000070000000000013000000000a1010000000012104000000000000600000000000060000000012100000000000e101000000000a1040000000000000
  | 7, 21 => 0xa10700000415042000000000041100000000000001100000000841010000000000001000000000e108000000000000400000000000010000000012104000004050020000000000000090000000000006000000000a103000000000610300000000000040000000012105000000000a100000000000e103000000000001200000001091070000000000009000000000610100000000121070000000012104000000000000b000000000e1010000000012104000000000000b0000000012103000000000e1040000000002101
  | 7, 22 => 0x8000000000e103000000000000a00000000021020000000000008000000000000600000000121000000000109102000000000000000000000000020000000006101000000000a10100000000000020000000006100000000000e10000000000000120000000006101000000000610000000000000010000000000005000005310520000000000000120000000000001000000000000200000000000020000000104101000000000a107000000000000f0000000000005000000000a10100000000c51020000000012100
  | 7, 23 => 0x3000000380220000000000061030000000000008000000000000f000000000000000000000000060000000002106000000010910200000000000070000000006100000000000a10200000000000120000000000005000000008010100000000061080000000000005000000000a1030000000002108000000000000700000304c0201000000000000a0000000000007000000000e107000000000e106000000008410100000000000090000000000014000000380a201000000000610300000000000100000010440200
  | 7, 24 => 0xf00000000000010000000000003000000000610300000000c910000000000c0101000000000e108000000000e1030000000000006000000000a1060000000006105000000000e102000000000000900000000401010000000000011000000000a100000000010d1010000000000002000000000e1000000000084100000000000000200000000021030000000002105000000000000000000000121020000000002102000000000210100000001091030000000000000000000000e101000000000a1000000000000004
  | 7, 25 => 0x1300000000061060000000006102000000000001000000001011000000000000009000000000001100000000c0101000000000e100000000000e101000000000a1060000000006102000000000a10300000000c81010000000006101000000000000a000000000e1020000000109106000000001210000000000000020000000109107000000000e10100000000061060000000000012000000000000a000000004110100000314c420100000001091020000000012100000000000610200000000061010000000006104
  | 7, 26 => 0x610800000000000010000000006104000000001210000000000000060000000006103000000000610000000000121010000000012101000000000001200000000000060000000006101000000000000f0000000006101000000000a101000000000e100000000001210000000000121050000000002105000000000000b0000000002102000000000000000000000061010000000002104000000480220100000000c910100000000021000000000000004000000000000000000000061020000000006107000000000000a
  | 7, 27 => 0x1000000000000f00000000c0101000000380a20100000000000040000000012101000000000610000000000c01010000000000003000000000000f000000000610100000000021020000000000001000000000000000000000c51000000000006100000000000610600000000000080000000000000000000000e10000000000121070000000002101000000000610200000000061040000000002104000000000e102000000000e102000000000000200000000061060000000000006000000000610100000000c4101
  | 7, 28 => 0x210200000104402000000000006108000000001210100000000000000000000006103000000004110100000000061000000000002108000000000e100000000000a100000000000a10500000000021010000000000007000000000000300000000000000000000000003000000000000900000000000040000000006100000000000000b0000000000008000000000000f000000000210800000000061040000000000001000000008510000000000000000000000000003000000000e10800000000061030000000002103
  | 7, 29 => 0x800000000c5101000000000e10000000000000050000000012100000000008410100000000000000000000000002000000000e108000000000000200000000021010000000002104000000000000600000000811010000000012101000000000a1000000000002102000000000000800000324c8201000000000a10100000000061070000000000014000000000000100000000061070000000000013000000380a20100000000000050000002806201000000000a106000000000a102000000000a1000000000000009
  | 7, 30 => 0xe1020000000006100000000000610100000000021020000000000006000000000000b0000000000000000000000a1050000000000002000000000000b0000000000001000000000e10700000000121000000000006102000000000a1010000000000012000000000000000000000021050000000006105000000000210800000535042000000021484201000000000e1040000000006103000000000210100000000061060000000000000000000000a108000000000000a000000480620100000000000090000000002101
  | 7, 31 => 0x105100000000480a2010000000012104000000000a1000000000006100000000000a101000000000a10600000314c420000000000000020000000000005000000000a102000000000000100000000841000000000000004000000480a200000000000e10300000000021030000000041101000000000e105000000000e10000000000061060000021484201000000000e1000000010440200000000000000a000000000210500000530852010000000006100000000000a10000000000061040000053105200000000000a107
  | 7, 32 => 0x2802200000000000000800000000000070000000000002000000000a105000000000210000000000000040000040500200000000000000500000000c91010000000109103000000000000200000000000040000000000009000000000000200000000000000000000006100000000000000a00000000000070000000012106000000000000700000000000100000000109103000000000e107000000000a1080000000002104000000000a10000000000061060000000000009000000000610300000001051050000000000002
  | 7, 33 => 0x104100000000000000b000000000000100000000000020000000002102000000010910200000000000050000000012101000005308520100000000000050000000109106000000000e10600000000000120000000000014000000480a201000000000210800000000c11010000000000003000000000610700000000000090000002806201000000000e101000000000210000000000000090000000109102000005348420100000000061000000000002101000000000a101000000000e1000000000012100000000000a100
  | 7, 34 => 0xa000000001210400000000c5101000000000e10000000028062010000000000000000000000e1010000000012106000000010910300000000000000000000002105000000000e107000000480e2010000000006105000000000a10200000000000070000000006101000000000610100000314c4200000000480a2000000000000008000000000e102000000000210600000000000030000000002101000000000000800000000c4100000000000e102000000000000600000000000040000000000008000000480a200
  | 7, 35 => 0x90000000040101000000000e103000000380620100000000c41010000000012101000000000a10200000000000140000000012100000000000a101000000000000500000000061060000000000002000000000000500000000000010000000006102000000000610000000028062000000000006102000000000210800000000061010000000000002000000000a100000000000e101000000000e10000000324c8201000000000e1010000000000013000000000000a00000000c110100000000121070000000000013
  | 7, 36 => 0xa00000000c51030000002806200000000000610300000001091010000000002105000000000000300000000000020000000109107000000000a101000000000000200000000000090000000000001000000000a1000000000000002000000000a100000000000a107000000000000b0000004806200000000001210400000000000080000000000011000000000a108000000000a108000000000a1000000000000003000000000610700000000000080000000006100000000000000200000000021010000000002101
  | 7, 37 => 0x21010000000109102000000000e10200000000061020000000000003000000000e106000000010910300000000000060000000012102000000000e1030000004806200000000000210400000000c1100000000000000a00000000021020000000000008000000000e104000000000a100000000000000200000000c51020000000006100000000000e1070000000002108000000000610700000000000050000000000012000000000610300000000121010000000041101000000000610100000038062010000000012100
  | 7, 38 => 0x480a20000000000121000000000000005000000000e100000000000e1050000000002101000000000000100000000021010000000109106000000000000900000000000110000000000008000000001210500000001051050000000040101000000000610100000000000000000000000005000000380a200000000000000300000000061000000000006101000001044020100000000000050000000012100000000000000800000000000120000000006100000000000000b000000000610600000000000080000000006105
  | 7, 39 => 0x28022010000000000002000000000000a00000000121000000000006101000000000a100000000480e201000000000e10400000000121000000004806201000000000e10100000000000040000000000001000000000000400000001091030000000000009000000000000500000314c420000000000000030000000000008000000000a1040000000006101000000480e200000000010410100000000000070000000081100000000000e10100000000c41000000001802201000000000a10100000000000060000000000002
  | 7, 40 => 0x21000000000000002000000480e2010000000002106000000000a1010000000000007000000000e101000000000000400000000061060000000002105000000000000a00000000061020000000000009000000000000a000000000610100000324c8201000000000a1010000000012103000000000000a0000000000005000000001210400000000021020000000081101000000000000a000000000000800000540c5200000000000e103000000000e1010000004806200000000000000800000000000020000000002100
  | 7, 41 => 0xa000000010110000000000061040000000012105000000008410000000000061060000000000004000000000e10000000000021010000000000001000000000a10100000000021060000000012100000000000000e0000000012106000000000e10000000000000040000000012106000000000a105000000000000a00000000000140000000040101000000280220100000000121010000000000013000000000a102000000000000300000000061000000000000008000005348420100000001011010000000006101
  | 7, 42 => 0xe1030000000000006000000000e10500000001091020000000000005000000000e10000000000061000000000006100000000000000a00000000061010000000006106000000280220100000000061000000000000001000000000000200000000000070000000012102000000000000200000000c8101000000000a1010000000000008000000380a20100000000061020000000006105000002048020100000000121020000000012100000004350c20000000000c5102000000000e1030000000000014000000000a105
  | 7, 43 => 0x109103000000001210300000000021010000000006100000000000e107000000000a1010000000109106000000000000b0000000006100000000000a1000000000002105000000000a1010000000000002000000000210600000000121060000000000002000000380220100000000121020000000000002000000000000a000000000e1010000000012105000000000000f0000000041100000000000000500000000000080000000012107000000000e1000000000006108000000380220000000000061000000000012101
  | 7, 44 => 0x500000000411010000000012107000000480620100000000061000000000006101000000000a102000000000000000000204802010000000002101000000010c10100000001091070000000000009000000010510000000000061010000000012100000000001210200000000000020000000000007000000000e101000000000a1000000000002100000000000e10200000000121000000002806200000000000000800000000000000000000002102000000000210500000000c910000000000000000000000012101
  | 7, 45 => 0x2102000000000000a000000004010000000000021050000010440201000000000e10300000000061010000000002101000000000000a0000000002100000000000000900000000000050000000006100000000000000200000000061010000000000001000000000a1000000000006100000000000e1010000000006101000000000a101000000000000c0000000109106000000000e10100000001001050000000006101000000480620000000038022000000000012107000004350c200000000000a1060000000012100
  | 7, 46 => 0xa10500000000061070000000000002000000000000b000000000e10100000000000090000000000005000000000610700000000121000000000000006000000001210300000000811040000000006102000000000e1030000000006100000000000e1060000000085100000000000000700000000000030000000012100000000000000a0000000002100000000000210100000524c4201000000000001000000000021030000000000004000000000610800000000c4101000000000000900000000061020000000000004
  | 7, 47 => 0x5350420000000000c8101000000000a102000000000a1000000000002102000000001210400000038022010000001802201000000001210600000000000050000000012102000000000001400000524c420100000000121050000000012106000000000a10600000000021050000000000008000000008110100000000000100000000002105000000000000a000000000e101000000000000e0000000109102000000000000b000000000000e000000000e101000000000e108000000000a10400000000000080000000000005
  | 7, 48 => 0xc91070000000006103000000000000a000000000000000000038022010000000012100000000000210100000531052000000000040100000000000a1060000000002100000000000000a00000000000020000000000005000000004110400000000000070000000000006000000000000900000000021030000000109102000000000000f00000000000140000000002102000000000000400000000000020000000084100000000000a1030000000000009000000000610000000520c5201000000000000b0000000040101
  | 7, 49 => 0x2102000000010c10000000000000080000000000008000000000610100000000841000000000006106000000000e101000000000000a00000304c020100000000c4100000000480e2000000000006100000000000e10500000000061010000004802201000000000000900000000000050000000002106000000000000a00000000121040000000002106000000001210500000000000000000000105100000000000000b000000010910600000000000090000000006100000000000000400000000061010000000000000
  | 7, 50 => 0x210600000000021020000000081104000000010d10000000000021010000000006100000000000000f000000000001100000000021070000000002105000000000000a00000000411010000000084101000000000000300000000c410100000000121050000000040101000000000a104000000000000b000000000e100000000000610600000535042000000000000008000000000210200000000000040000000006102000000000a105000000001210100000000000030000000006101000000480e200000000000000a
  | 7, 51 => 0x10d10000000000c81010000000000009000000000e106000000000610100000000021010000000002108000000000000a0000000000008000000000000400000000000020000000000005000000000a103000000000000a0000000000006000000000a10200000000000140000000002101000000480220100000000c9106000000000000100000000000000000000000000000000000000f00000000000000000000000006000000000210100000000121050000000002100000000000210100000000061030000000000002
  | 7, 52 => 0xa00000000000080000000000004000000000000d000000000000f000000000000b000000010910200000000000020000000000007000000000610600000000021000000000000008000000000000700000000000040000000002107000000000a1020000000000008000005150c200000000000000500000000000080000000002107000000000a10000000000061040000000002100000000180220100000000000140000000012101000000000000f0000000041104000000000210200000000021020000000041101
  | 7, 53 => 0x1100000000000010000000012102000000000001400000000061050000000000005000000001210300000000000030000000006106000000000000b0000000002103000000000000200000000021050000000000006000000000e10000000000c8101000000000210100000000c41070000000000008000000010510500000000000010000000006103000000000000600000000c410100000000061020000000041100000000000a1040000000006100000000000210100000000061010000000006100000000000000f
  | 7, 54 => 0x5000000000210600000000000040000000000007000005310520000000000000030000000006100000000000000500000000c0101000000000000500000000000020000000000002000000000210400000000401010000000006105000000000000100000000061010000000002105000000001210000000000000060000000000006000004350c2000000000002103000000000e10300000000121070000000006103000000000000f000000000e103000000000000b000000000210100000000061010000000000005
  | 7, 55 => 0x3000000000610100000000000080000000006100000000000000700000000000030000002802200000000000001400000000000090000000081100000000000a10100000000000010000000006104000000000000900000000061010000004806201000000000610000000000000030000000000002000000000e102000000001210100000000000030000000000001000000000e102000000000610600000000121010000000000008000000000210100000001051050000000000006000000000e1020000000002102
  | 7, 56 => 0x100000000000000000000006103000000000610300000001041010000000012100000000001210100000000000080000000006102000000000210600000000021050000000002104000000000000500000000000140000000012103000000000000100000000061010000000041101000000000000a000000000610400000000000030000000109106000000001210200000000021010000000006105000000000001000000001091020000000000003000000000a100000001044020100000000000010000000000005
  | 7, 57 => 0x4150420000000304c0201000000000000e0000000000008000000010410100000000061040000000006104000000000210000000000021050000000000004000000010d10000000000021000000000002100000000000000800000000411010000000109103000000004010100000000061020000000006100000000000000400000000411010000000000002000000000000400000000c510100000000000020000000012106000000000a100000004350c2000000000081100000000001210200000000000060000000000006
  | 7, 58 => 0x210500000000000020000000006104000000000e10100000000000080000000000006000000000000b0000000012101000000004110100000001091030000000000008000000000e1070000000012106000000000e10700000000c510100000001091020000000040101000000000610500000000061010000000000006000000000000800000000c9100000000000000900000000021050000000000007000000000e1000000000000002000000000000500000000061010000000000005000000000e1050000000006101
  | 7, 59 => 0x60000000000006000000000000700000000000080000000006100000000000a105000000000000200000000000080000000000007000000000000900000000061010000000002100000000280620000000000c01000000001802200000000000000600000000000090000000012100000000000610200000000000070000000012107000000000610400000000000050000000000002000000000e10600000000061080000000000001000000010c10000000000000140000000000000000000000e1000000000000003
  | 7, 60 => 0x21010000000012105000000000000700000000401000000000000000000000000610100000000000030000000000007000000000000200000000000030000000000003000000000000500000000061010000000000005000000000a101000000000610600000000061010000000006104000000000000a000000000610200000000021070000000041101000000000000b0000000000003000000000000a00000000851000000000006100000000000000500000000021050000000002105000000000000b0000000002103
  | 7, 61 => 0x21030000000006105000000001210600000000401010000051101201000000000210200000000811010000000006104000000000210200000000021000000000000009000000000e1000000000000004000000000000100000000121010000000002100000000000610100000000061000000000000001000000010d10000000000061040000000002108000000000000500000000000030000000081101000000000000a0000000080101000000000000a000000000e106000000010910200000000000010000000002101
  | 7, 62 => 0x105105000000004110100000000061000000000002100000000000a1000000000000014000000000a1020000000006101000000000000000000000000090000000006104000000000e10200000000000000000000002106000000000210100000000000030000000041101000000480e20000000000c510200000000000050000000041101000000000000600000000c4101000000010c100000000000210500000000c8101000000000000b0000000006104000000380a201000000000000a000000000000b000000000000a
  | 7, 63 => 0xa1020000000000006000000480e200000000001210100000001051050000000002106000000000e103000000000610000000000000020000000000008000000004110400000000000060000000006100000000000210500000000c51020000000000007000000000a10000000000c41000000000000009000000000000500000000000060000000000005000000000000800000000000030000000006101000000010510500000000061010000000000008000000000a101000000010510b0000000000003000000000e107
  | 7, 64 => 0x14000004350c200000000000000a000000000610000000324c820100000000000010000000000003000000000000600000104402000000000006101000000004110100000000401000000000000005000000000000b000000000000a000000000a1000000000006103000000000000800000000411000000000006101000000000000100000000121010000000002107000000000610500000000000090000000000004000000000000400000000121020000000006101000000000a1000000000006104000000000a105
  | 7, 65 => 0x210000000000000000000000006100000000000000100000000021010000000006105000000000000500000000000140000000000002000000000000800000000000010000000002105000000000e107000000480e2000000000000003000000000000f00000000021010000000085100000000000000f00000000061010000000002101000000000000400000000021040000000012101000000000000500000000061020000000105105000000000000300000000000050000001802200000000000000a0000000002103
  | 7, 66 => 0x5108120000000000021080000000041100000000000001400000000000040000000000007000000000000400000000021040000000000005000000000000500000000811040000000002100000000000210500000000c810100000000021050000000000007000000000000700000000021010000000000002000000000210100000000061000000000000009000000000610100000000411010000000002108000000000610100000000000080000000000000000000004110000000000021000000000041101000000000000f
  | 7, 67 => 0x4350c200000000000a10600000000c910100000000c8101000000001210200000000121010000000000007000000000000400000000000050000000002101000000004110000000510c9201000000000000400000000000080000000012101000000000000a0000000002102000000000000800000000c81010000000006101000000000210800000000061000000000000008000000000610100000000c81010000000002101000000000000500000000121010000000000008000000000000500000000061010000000006100
  | 7, 68 => 0xa000000000a10000000000021080000010440200000000000000a0000000000000000000010d100000000000610000000048062010000000000000000000000001000000000000080000000006101000000000000b00000000061000000000000005000000000000200000000121020000000000004000000000a100000000000000100000001041010000000109102000000000210800000000000040000000000008000000000000a000000000210100000000411010000000000001000000000e1020000000000005
  | 7, 69 => 0x100000001011010000000012101000000000a100000000280220000000000000040000000006101000000000a100000000000000a00000000401000000000012101000000000210800000000021080000000000002000000000000100000000c91010000000041100000000000210000000001051050000000000000000000004110000000000061050000000002100000000010510b00000000061000000000000005000000010510b0000000000005000000000000000000000061000000000006101000000000000b
  | 7, 70 => 0x500000000000020000000006104
  | 8, 0 => 0x3000000004110000000000000040000000000009000000000610000000000000010000000000012000000000000000000000000030000000041101000000000000200000000000020000000000003000000000000100000000000060000000000002000000000000a00000000c4100000000000000600000000000070000000000007000000010c10000000000411010000000000003000000000e1000000000084101000000000000000000000000060000000000002000000000000800000000000010000000000002
  | 8, 1 => 0x60000000041100000000000000200000001011000000000000003000000000000200000000000010000000000003000000000000200000000000000000000000003000000000000100000000000040000000000003000000000000800000000801010000000000007000000000000a0000000109101000000000610000000000c910100000000000030000000000005000000000000100000000061000000000000005000000000000200000000c410000000000c8101000000000000000000000000040000000000008
  | 8, 2 => 0x400000000000020000000000003000000000000200000000000040000000000001000000000000400000000000080000000000002000000000000400000000000030000000000005000000000000600000000021000000000000004000000000000300000000000000000000000001000000000000000000000c910000000000000030000000000004000000000210000000000000050000000000003000000000000100000000c910000000001091010000000000002000000000000700000000000060000000000002
  | 8, 3 => 0xc41010000000000002000000010110100000000000080000000000003000000000000100000000000010000000000003000000008510000000000c41000000000000006000000000000200000000c51000000000000007000000008510000000001011000000000000002000000000000700000000000000000000000005000000000a10100000001011010000000000003000000004010000000000c51000000000000000000000000000300000000401000000000000002000000000000000000000000110000000000008
  | 8, 4 => 0x10c100000000000001200000001051000000000000004000000000e1010000000105101000000000000b000000000001200000000000000000000000002000000000000800000000c5101000000000000600000000000110000000000003000000000000000000000c110100000000000030000000000012000000010510100000000000060000000041100000000000000500000000000000000000000000000000000000100000000c510100000000000000000000000003000000000e10000000001091000000000000000
  | 8, 5 => 0x200000000000000000000000008000000010d101000000000000300000000c010000000000000020000000085101000000000000200000001041000000000000004000000000000a000000000a1010000000000003000000000000000000000121000000000000001000000000000a000000000e101000000000000500000000000010000000041100000000010c100000000000000300000000000080000000000005000000000000000000000000070000000000001000000000a10100000000000000000000000009
  | 8, 6 => 0x5000000000000000000000000080000000000006000000000000500000000000030000000000002000000008110100000000801010000000012100000000000000700000000000050000000000002000000000000000000001001000000000000007000000000e1010000000012100000000000a10000000000000030000000000005000000010c10000000000000060000000000005000000000000800000000000070000000000000000000000000f000000000e1010000000000000000000000000f0000000000006
  | 8, 7 => 0x60000000000005000000000000200000001011000000000012100000000000000f0000000000001000000010510000000000000080000000000010000000000000000000000000090000000012100000000000000200000000c9101000000000001100000000000010000000012101000000000000b0000000000000000000000000200000000000050000000000001000000000a10000000000000010000000000000000000000000100000000c010100000000000090000000000000000000000000100000000c1100
  | 8, 8 => 0x610100000000000050000000002101000000000000300000000061000000000000001000000000000000000000000070000000000006000000000000800000000061010000000000000000000010910000000000000030000000002101000000000000a000000000000100000000000020000000105100000000000610000000000000040000000000004000000000000600000000000050000000006101000000000000000000000000120000000000000000000000000100000000c11000000000041101
  | 8, 9 => 0x1000000000000000000000c410000000000000040000000000001000000008510100000000000030000000000001000000001210000000000c91010000000080101000000004010100000000021000000000012101000000000000000000000c91000000000000001000000000000f000000000e1000000000000006000000000000100000000000030000000002101000000000a10000000000000010000000000005000000000000500000000000020000000000005000000000000000000000000020000000000004
  | 8, 10 => 0x5000000008510000000000000060000000000010000000000000b0000000040100000000000000400000001001000000000000007000000000001200000000000010000000000002000000000000000000000000030000000040100000000000000300000000c010000000000000020000000000011000000004010100000000c010000000000000040000000000011000000000000a000000000000500000000000020000000000003000000000000300000000c1100000000000000000000000000060000000000001
  | 8, 11 => 0x6000000000000000000000000030000000000002000000000a1010000000000001000000000000100000000c810100000000000030000000000002000000000000100000000061000000000000003000000000000a0000000000000000000000000100000000000020000000000003000000000000000000000000010000000000000000000000000500000000c510000000000000000000000000009000000000000a000000000000400000000000020000000002101000000000000900000000000060000000000004
  | 8, 12 => 0x200000000000000000000000008000000000000000000000000090000000040100000000000000600000000000050000000000004000000000210100000000000020000000000003000000000000300000000000010000000000008000000000000800000000000100000000000001000000000610100000000000050000000002100000000000000300000000c91000000000000006000000000000600000000000030000000002100000000010d10000000000000000000000000000000000000000a000000010c100
  | 8, 13 => 0x3000000000000400000000121010000000000000000000000000500000000000080000000000002000000000000300000000000080000000000004000000000000a00000000c1101000000000000400000000000070000000000011000000000a10100000000000050000000109100000000000000300000000000010000000000002000000000e10000000000000060000000000005000000000000b000000000000200000000000120000000085100000000010d100000000000000b0000000000003000000000a101
  | 8, 14 => 0x5000000000000800000000811000000000000005000000000000a00000000000100000000041101000000000000200000000000040000000000000000000000000300000000000010000000000004000000000000900000000000080000000000002000000000000300000000000030000000000005000000000000200000000000070000000000005000000010c1000000000000005000000008410100000000000010000000000004000000000000100000000000010000000006101000000000000000000000c9101
  | 8, 15 => 0x10000000000002000000000000500000000c01000000000000005000000000000000000000000050000000000003000000008410100000000000010000000080101000000000a10000000000021000000000000001000000000000300000000000080000000109101000000000000500000000000010000000000004000000000000200000000000050000000000011000000000000400000000000040000000000005000000000000100000000000050000000000001000000000000300000000000040000000101100
  | 8, 16 => 0x10000000000003000000010910100000000000010000000000004000000000000500000000c110100000000000050000000000008000000000000400000000061000000000101101000000010d1010000000000001000000000000100000000000040000000000008000000010d1000000000002101000000000000a000000000e100000000010d10000000000000000000000000012000000000000a00000000411010000000000008000000000000a000000000000100000000811000000000000006000000000000f
  | 8, 17 => 0xc510100000000c41000000000000000000000000000300000000000050000000000001000000010110100000000000010000000081100000000000000700000000c0100000000000a10100000000811000000000040101000000000000000000000000000000000000003000000000000300000000000050000000006101000000000000100000000061010000000105101000000000000a00000000000100000000105101000000000000100000000000050000000000002000000000000000000000c51010000000000008
  | 8, 18 => 0x61000000000000000000000000610000000000000000000000000008000000000000500000000000050000000000000000000000000100000000000040000000000008000000000000200000000000030000000000005000000000e10000000000000110000000000000000000000000000000000000030000000085100000000000e100000000000000a00000000411000000000000001000000000000a0000000000003000000000000200000000021000000000105101000000000000300000000811010000000002100
  | 8, 19 => 0x100000000000001000000000000100000000c910100000000121010000000040101000000000000a0000000000002000000000000100000000000000000000000006000000000000800000000000050000000000000000000000001200000000000080000000000004000000000000b00000000000000000000000002000000000210100000000000030000000000001000000000000500000000000050000000000008000000000000100000000000000000000000005000000008110100000000000030000000006101
  | 8, 20 => 0x1000000000000100000000000010000000000000000000000e1010000000040101000000000a100000000000000200000000000050000000000006000000000000000000000c8101000000000000400000000c4101000000000210100000000000010000000041100000000000000500000000000010000000000002000000000000800000000000080000000000000000000000000f000000000000000000000c41000000000000000000000000000000000000061010000000105100000000010d1000000000000002
  | 8, 21 => 0x5000000000610100000000000020000000000000000000000000700000000061000000000000000000000000000500000000061000000000000000000000000000a00000000c81010000000101101000000000000000000000021000000000000000000000000210100000000000010000000000006000000010d100000000000000500000000000000000000000001000000000000000000000000050000000000001000000000000400000000000010000000081100000000000210100000000000000000000000004
  | 8, 22 => 0x2000000000000800000000c410100000000000070000000080101000000000000400000000000000000000002100000000000000000000000000080000000002100000000000000800000000000060000000085100000000000000b00000000000020000000000001000000004010000000000c8101000000000000200000000000000000000000002000000000e100000000000000500000000811000000000000012000000000000600000000061000000000002100
  | 9, 0 => 0x1000000000000100000000000000000000000000000000000000000000000000010000000000001
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 13 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_31 roots_31 8 s ws hint
  | 1 => checkCutEntry dom_59 roots_59 8 s ws hint
  | 2 => checkCutEntry dom_47_16 roots_47_16 7 s ws hint
  | 3 => checkCutEntry dom_55_8 roots_55_8 7 s ws hint
  | 4 => checkCutEntry dom_31_32 roots_31_32 7 s ws hint
  | 5 => checkCutEntry dom_62 roots_62 7 s ws hint
  | 6 => checkCutEntry dom_47 roots_47 7 s ws hint
  | 7 => checkCutEntry dom_55 roots_55 7 s ws hint
  | 8 => checkCutEntry dom_30_32 roots_30_32 6 s ws hint
  | 9 => checkCutEntry dom_61 roots_61 6 s ws hint
  | 10 => checkCutEntry dom_61_2 roots_61_2 6 s ws hint
  | 11 => checkCutEntry dom_62_1 roots_62_1 6 s ws hint
  | 12 => checkCutEntry dom_15 roots_15 5 s ws hint
  | 13 => checkCutEntry dom_23 roots_23 5 s ws hint
  | 14 => checkCutEntry dom_27 roots_27 5 s ws hint
  | 15 => checkCutEntry dom_45_16 roots_45_16 5 s ws hint
  | 16 => checkCutEntry dom_45_2 roots_45_2 5 s ws hint
  | 17 => checkCutEntry dom_53_8 roots_53_8 5 s ws hint
  | 18 => checkCutEntry dom_53_2 roots_53_2 5 s ws hint
  | 19 => checkCutEntry dom_30_1 roots_30_1 5 s ws hint
  | 20 => checkCutEntry dom_58_1 roots_58_1 5 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_59 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_55_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31_32 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_62 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_55 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_30_32 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_61 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_61_2 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_62_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_27 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_45_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_45_2 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_53_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_53_2 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_30_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_58_1 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_63 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
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
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 14 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 14 0 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 14 → Z 5 i = true := z5_0
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
private theorem z6_112 : ∀ i, 112 ≤ i → i < 113 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 112 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 113 → Z 6 i = true := (range_split (range_split (range_split z6_0 z6_16) (range_split z6_32 z6_48)) (range_split (range_split z6_64 z6_80) (range_split z6_96 z6_112)))
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
private theorem z7_320 : ∀ i, 320 ≤ i → i < 335 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 15 320 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 335 → Z 7 i = true := (range_split (range_split (range_split (range_split (range_split z7_0 z7_16) (range_split z7_32 z7_48)) (range_split (range_split z7_64 z7_80) (range_split z7_96 z7_112))) (range_split (range_split (range_split z7_128 z7_144) (range_split z7_160 z7_176)) (range_split (range_split z7_192 z7_208) (range_split z7_224 z7_240)))) (range_split (range_split (range_split z7_256 z7_272) (range_split z7_288 z7_304)) z7_320))
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
private theorem z8_192 : ∀ i, 192 ≤ i → i < 194 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 2 192 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 194 → Z 8 i = true := (range_split (range_split (range_split (range_split z8_0 z8_16) (range_split z8_32 z8_48)) (range_split (range_split z8_64 z8_80) (range_split z8_96 z8_112))) (range_split (range_split (range_split z8_128 z8_144) (range_split z8_160 z8_176)) z8_192))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_0 : ∀ i, 0 ≤ i → i < 16 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_16 : ∀ i, 16 ≤ i → i < 25 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 9 16 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 25 → Z 9 i = true := (range_split z9_0 z9_16)
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

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 13]⟩], 16⟩

theorem wit_mono : PEqualNP.MetaComplexity.Monotone2 wit := by
  simp [wit, PEqualNP.MetaComplexity.Monotone2]

theorem wit_sz : wit.size ≤ 11 := by decide

set_option maxRecDepth 40000 in
theorem wit_ev : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = Nat.testBit (4277071594 * 2 ^ 32 + 4209567968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel

set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_63.testBit r.val = (fun x : Fin 6 → Bool => Nat.testBit (4277071594 * 2 ^ 32 + 4209567968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) (pt6 r.val) := by decide +kernel

theorem lower : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071594 * 2 ^ 32 + 4209567968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) t → 11 ≤ t :=
  lower_to_circuit6 (fun x : Fin 6 → Bool => Nat.testBit (4277071594 * 2 ^ 32 + 4209567968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) goal_63 11 hT6 (by unfold IsConst; decide) low_63

end PEqualNP.Outside.L_meta_41598_aux

theorem PEqualNP.Outside.L_meta_41598 :
  ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071594 * 2 ^ 32 + 4209567968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071594 * 2 ^ 32 + 4209567968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  exact ⟨PEqualNP.Outside.L_meta_41598_aux.wit, PEqualNP.Outside.L_meta_41598_aux.wit_mono, le_trans PEqualNP.Outside.L_meta_41598_aux.wit_sz (PEqualNP.Outside.L_meta_41598_aux.lower s hs), PEqualNP.Outside.L_meta_41598_aux.wit_ev⟩
