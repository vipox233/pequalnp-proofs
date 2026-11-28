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

namespace PEqualNP.Outside.L_meta_40545_aux

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
def goal_47 : Nat := 0xeeeaeeeaa888a888eeeaeeeaa888a888eeeaeeeaa888a888eeeaeeeaa888a888
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_31 : Nat := 0xffffffff
def goal_31 : Nat := 0xfeeaa888feeaa888feeaa888feeaa888feeaa888feeaa888feeaa888feeaa888
def roots_31 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_55_8 : Nat := 0xff00ff00ff00ff00
def goal_55_8 : Nat := 0xfefeeeeefefea8a8fefeeeeefefea8a8fefeeeeefefea8a8fefeeeeefefea8a8
def roots_55_8 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_62 : Nat := 0x5555555555555555
def goal_62 : Nat := 0xfcc0ccc0fcc00000fcc0ccc0fcc00000fcc0ccc0fcc00000fcc0ccc0fcc00000
def roots_62 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_31_32 : Nat := 0xffffffff00000000
def goal_31_32 : Nat := 0xfeeaeeeafeeaeeeafeeaeeeafeeaeeeafeeaeeeafeeaeeeafeeaeeeafeeaeeea
def roots_31_32 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xeaeaeaeaeaea8888eaeaeaeaeaea8888eaeaeaeaeaea8888eaeaeaeaeaea8888
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfaaaaaaafaaaa000faaaaaaafaaaa000faaaaaaafaaaa000faaaaaaafaaaa000
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_15_16 : Nat := 0xffff0000
def goal_15_16 : Nat := 0xfeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeea
def roots_15_16 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0]

def dom_15_48 : Nat := 0xffff000000000000
def goal_15_48 : Nat := 0xfeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeea
def roots_15_48 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0]

def dom_23 : Nat := 0xff00ff
def goal_23 : Nat := 0xeaea8888eaea8888eaea8888eaea8888eaea8888eaea8888eaea8888eaea8888
def roots_23 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0]

def dom_39_8 : Nat := 0xff000000ff00
def goal_39_8 : Nat := 0xeeeeeeeea8a8a8a8eeeeeeeea8a8a8a8eeeeeeeea8a8a8a8eeeeeeeea8a8a8a8
def roots_39_8 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0]

def dom_30 : Nat := 0x55555555
def goal_30 : Nat := 0xfcc00000fcc00000fcc00000fcc00000fcc00000fcc00000fcc00000fcc00000
def roots_30 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_30_32 : Nat := 0x5555555500000000
def goal_30_32 : Nat := 0xfcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0
def roots_30_32 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_27_4 : Nat := 0xf0f0f0f0
def goal_27_4 : Nat := 0xffeeaa88ffeeaa88ffeeaa88ffeeaa88ffeeaa88ffeeaa88ffeeaa88ffeeaa88
def roots_27_4 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_59_4 : Nat := 0xf0f0f0f0f0f0f0f0
def goal_59_4 : Nat := 0xffeeeeeeffeeaa88ffeeeeeeffeeaa88ffeeeeeeffeeaa88ffeeeeeeffeeaa88
def roots_59_4 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xeeaaeeaaeeaa8888eeaaeeaaeeaa8888eeaaeeaaeeaa8888eeaaeeaaeeaa8888
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_39 : Nat := 0xff000000ff
def goal_39 : Nat := 0xeaeaeaea88888888eaeaeaea88888888eaeaeaea88888888eaeaeaea88888888
def roots_39 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0]

def dom_27 : Nat := 0xf0f0f0f
def goal_27 : Nat := 0xeeaa8888eeaa8888eeaa8888eeaa8888eeaa8888eeaa8888eeaa8888eeaa8888
def roots_27 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_43 : Nat := 0xf0f00000f0f
def goal_43 : Nat := 0xeeaaeeaa88888888eeaaeeaa88888888eeaaeeaa88888888eeaaeeaa88888888
def roots_43 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_43_4 : Nat := 0xf0f00000f0f0
def goal_43_4 : Nat := 0xeeeeeeeeaa88aa88eeeeeeeeaa88aa88eeeeeeeeaa88aa88eeeeeeeeaa88aa88
def roots_43_4 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_53_8 : Nat := 0x3300330033003300
def goal_53_8 : Nat := 0xfafaaaaafafaa0a0fafaaaaafafaa0a0fafaaaaafafaa0a0fafaaaaafafaa0a0
def roots_53_8 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_57_4 : Nat := 0x3030303030303030
def goal_57_4 : Nat := 0xffaaaaaaffaaaa00ffaaaaaaffaaaa00ffaaaaaaffaaaa00ffaaaaaaffaaaa00
def roots_57_4 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_51_8 : Nat := 0xf000f000f000f00
def goal_51_8 : Nat := 0xeeeeeeeeeeee8888eeeeeeeeeeee8888eeeeeeeeeeee8888eeeeeeeeeeee8888
def roots_51_8 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfeeaeeeafeeaa888feeaeeeafeeaa888feeaeeeafeeaa888feeaeeeafeeaa888
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

namespace S_47
def pairsG : List (Nat × Nat) := [(1, 3), (1, 33), (2, 3), (5, 7), (5, 13), (5, 37), (6, 7), (6, 38), (9, 11), (9, 13), (9, 41), (10, 11), (10, 42), (12, 13), (14, 15), (14, 46), (32, 33), (34, 35), (34, 38), (34, 42), (36, 37), (36, 38), (40, 41), (40, 42), (44, 45), (44, 46)]
def r1sG : List Nat := [1, 1, 2, 5, 5, 5, 6, 6, 9, 9, 9, 10, 10, 12, 14, 14, 32, 34, 34, 34, 36, 36, 40, 40, 44, 44]
def r2sG : List Nat := [3, 33, 3, 7, 13, 37, 7, 38, 11, 13, 41, 11, 42, 13, 15, 46, 33, 35, 38, 42, 37, 38, 41, 42, 45, 46]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [2203924701443, 15432390411021, 13233367163149, 6601971212547, 11000085094659, 37388296790275, 5506754552067, 37388431002883, 48417739244301, 11034444833027, 15415210803981, 9917652674061, 39608274453286, 35188770210593]
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
  | 5, 0 => 0xd4c9adb2915d40018888432e71f40ace6fa9a6b35ba073fa5b61388b54e97e2452ee9a9e4fada6a442c1d77f42829c102b135e402a48ff95286448961b2929df0f1fce070afba44c03b0c7d70335d817
  | 6, 0 => 0xe505bdfaa1712e8b8c5e12728888432e7445a6b56949f7d6686e9bda6594bfe25ba073fa5b61388b55c13d204d7877b92fef2b28270b03de160058940f1fce070da784ce
  | 7, 0 => 0xf1fce07
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xaa000000aa000000000000000000000000000000000000000000000000000000a0a00000a0a000000000000000000000000000000000000000000000000000008888000088880000000000000000000000000000000000000000000000000000555500005555000000000000000000000000000000000000000000000000000033330000333300000000000000000000000000000000000000000000000000000f0f00000f0f000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000000000ffff
  | 0, 1 => 0xf0000000f0000000000000000000000000000000000000000000000000000000eeee0000eeee0000000000000000000000000000000000000000000000000000eeee000000000000000000000000000000000000000000000000000000000000e0e00000e0e00000000000000000000000000000000000000000000000000000cccc0000cccc0000000000000000000000000000000000000000000000000000cccc000000000000000000000000000000000000000000000000000000000000aaaa0000aaaa0000000000000000000000000000000000000000000000000000aaaa00000000
  | 0, 2 => 0xfff00000fff00000000000000000000000000000000000000000000000000000fff00000ff000000000000000000000000000000000000000000000000000000ffaa0000ffaa0000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000ff000000f0000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000f8f80000f8f80000000000000000000000000000000000000000000000000000f0f00000f0f0
  | 0, 3 => 0xffff0000ff000000000000000000000000000000000000000000000000000000ffff0000f0f00000000000000000000000000000000000000000000000000000ffff0000cccc0000000000000000000000000000000000000000000000000000ffff0000aaaa0000000000000000000000000000000000000000000000000000ffff000088880000000000000000000000000000000000000000000000000000ffff00000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x18a41695
  | 5, 0, 0 => 0xc41230ae28b48971482c8b89c1695c518b4ae2ef5a570b4882b882c815c5a0b4ad20d5a573482d2b4824605c520b4ae2b059d7b282d2b8a45695
  | 5, 0, 1 => 0xc52041aee905257148246b8a41c55
  | 6, 0, 0 => 0xc520b499b1482d2860629048d715a41696c5e905a5b1483d696c520b525818a2d2250629059171482d236c520b491b98a41696d62905a5b14941696062905a571482d216
  | 6, 0, 1 => 0x378a41696
  | 7, 0, 0 => 0x18a41695
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
  | 0, 0 => 0x700000000000000000000000000000000000000000000000000000000000000003800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003fff8c40000000000000000000000000000000000000000000000000000000003f1273b0000000000000000000000000000000000000000000000000000000000cf1f0700000000000000000000000000000000000000000000000000000000003f00ff000000000000000000000000000000000000000000000000000000000000ffff
  | 0, 1 => 0x300e00000000000000000000000000000000000000000000000000000000000000edfff00000000000000000000000000000000000000000000000000000000000e0000000000000000000000000000000000000000000000000000000000000000c0f800000000000000000000000000000000000000000000000000000000000ed8c400000000000000000000000000000000000000000000000000000000000e0000000000000000000000000000000000000000000000000000000000000000073b0000000000000000000000000000000000000000000000000000000000000000
  | 0, 2 => 0x3f0fff80000000000000000000000000000000000000000000000000000000003f0ff000000000000000000000000000000000000000000000000000000000003c0ff3b0000000000000000000000000000000000000000000000000000000003c0ff000000000000000000000000000000000000000000000000000000000003c0e0000000000000000000000000000000000000000000000000000000000003c00000000000000000000000000000000000000000000000000000000000000330e0f8000000000000000000000000000000000000000000000000000000000330e0f8
  | 0, 3 => 0x3ffff000000000000000000000000000000000000000000000000000000000003ffe0f80000000000000000000000000000000000000000000000000000000003ffd8c40000000000000000000000000000000000000000000000000000000003ff073b0000000000000000000000000000000000000000000000000000000003ff00000000000000000000000000000000000000000000000000000000000003ff0000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x1406f100000000000000000000000000000000000000000000000000000000001106278000000000000000000000000000000000000000000000000000000000002494d0000000000000000000000000000000000000000000000000000000002ac908000000000000000000000000000000000000000000000000000000000015126320000000000000000000000000000000000000000000000000000000000cb1d0700000000000000000000000000000000000000000000000000000000003700ef0000000000000000000000000000000000000000000000000000000000006b5d
  | 0, 1 => 0x300e2100000000000000000000000000000000000000000000000000000000003ffffff0000000000000000000000000000000000000000000000000000000003ff94a2000000000000000000000000000000000000000000000000000000000334e2f80000000000000000000000000000000000000000000000000000000002aed9cd0000000000000000000000000000000000000000000000000000000002ae90800000000000000000000000000000000000000000000000000000000001536f7f0000000000000000000000000000000000000000000000000000000001530422
  | 0, 2 => 0x3fcfff80000000000000000000000000000000000000000000000000000000003fcffb00000000000000000000000000000000000000000000000000000000003dbff7f0000000000000000000000000000000000000000000000000000000003c8ff100000000000000000000000000000000000000000000000000000000003c8f6100000000000000000000000000000000000000000000000000000000003c89400000000000000000000000000000000000000000000000000000000000336ebfd000000000000000000000000000000000000000000000000000000000334e2f8
  | 0, 3 => 0x3ffffb20000000000000000000000000000000000000000000000000000000003fff6fa0000000000000000000000000000000000000000000000000000000003ffddef0000000000000000000000000000000000000000000000000000000003ffffff0000000000000000000000000000000000000000000000000000000003ffddef0000000000000000000000000000000000000000000000000000000003ff94a2
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

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
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

namespace S_31
def pairsG : List (Nat × Nat) := [(1, 3), (1, 17), (2, 3), (5, 7), (5, 13), (5, 21), (6, 7), (6, 22), (9, 11), (9, 13), (9, 25), (10, 11), (10, 26), (12, 13), (12, 28), (14, 15), (14, 30), (16, 17), (18, 19), (18, 22), (18, 26), (20, 21), (20, 22), (20, 28), (24, 25), (24, 26), (24, 28)]
def r1sG : List Nat := [1, 1, 2, 5, 5, 5, 6, 6, 9, 9, 9, 10, 10, 12, 12, 14, 14, 16, 18, 18, 18, 20, 20, 20, 24, 24, 24]
def r2sG : List Nat := [3, 17, 3, 7, 13, 21, 7, 22, 11, 13, 25, 11, 26, 13, 28, 15, 30, 17, 19, 22, 26, 21, 22, 28, 25, 26, 28]
def mpG : Nat := 0x7ffffff
def pool6G : List Nat := [2203655213315, 15432120926989, 13233097675021, 6601701724419, 10999815606531, 19795841257731, 5506485063939, 15432120930573, 6618881593603, 13215918067981, 9917383185933, 22067693814550, 11034175344899, 17596583117585, 26431246631706]
def xsM : List Nat := roots_31.map (· &&& dom_31)
def goalM : Nat := goal_31 &&& dom_31
def NN : Nat → Nat
  | 4 => 3
  | 5 => 29
  | 6 => 23
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xb160d858ac05225e8842d027
  | 5, 0 => 0xe457f490d75027cad68db2b9c56e12e7c5159104be3fb924b5aa084fac05225e81ea162e7873cae76f5141bc6bff23c86baa58136a3f50af64d480335e1d4aa855fbf4bf537bfbe75299e96d526e44fc4ca62407439e85fd3a6b8d4132f633fb32bc99002637312d1d973d961ac7d7cf15863287
  | 6, 0 => 0xe40c141be0bddffad051f507ce00c9b9c5159104c1afdc6dbe3fb924ba7741d8b4992a82ac05225ea0508cfd7ecfa1837702c5a9554c825e5299e96d3a6b8d4130706e42276bea4325303d37206585ea1b8a7ef1126b25b70241d3e1
  | 7, 0 => 0xac05225e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xaa00aa0000000000000000000000000000000000000000000000000000000000a0a0a0a0000000000000000000000000000000000000000000000000000000008888888800000000000000000000000000000000000000000000000000000000555555550000000000000000000000000000000000000000000000000000000033333333000000000000000000000000000000000000000000000000000000000f0f0f0f0000000000000000000000000000000000000000000000000000000000ff00ff000000000000000000000000000000000000000000000000000000000000ffff
  | 0, 1 => 0xeeeeeeee00000000000000000000000000000000000000000000000000000000eeeecccc00000000000000000000000000000000000000000000000000000000cccccccc00000000000000000000000000000000000000000000000000000000cccc888800000000000000000000000000000000000000000000000000000000cccc000000000000000000000000000000000000000000000000000000000000cc00cc0000000000000000000000000000000000000000000000000000000000aaaaaaaa00000000000000000000000000000000000000000000000000000000aaaa0000
  | 0, 2 => 0xfcccfccc00000000000000000000000000000000000000000000000000000000fc00fc0000000000000000000000000000000000000000000000000000000000fafafafa00000000000000000000000000000000000000000000000000000000fafaf0f000000000000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000f0f0a0a000000000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000f000f000
  | 0, 3 => 0xffff000000000000000000000000000000000000000000000000000000000000fff0fff000000000000000000000000000000000000000000000000000000000ffccffcc00000000000000000000000000000000000000000000000000000000ffc0ffc000000000000000000000000000000000000000000000000000000000ff88ff8800000000000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000ff00f00000000000000000000000000000000000000000000000000000000000fcf0fcf0
  | 0, 4 => 0xffffff0000000000000000000000000000000000000000000000000000000000fffff0f000000000000000000000000000000000000000000000000000000000ffffcccc00000000000000000000000000000000000000000000000000000000ffffaaaa00000000000000000000000000000000000000000000000000000000ffff8888
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x7de5c947da4cd25407dd6094
  | 5, 0, 0 => 0x7da4ce255f6890c257de40d255f6923495693344015f68d24257da4cf155f69310357db4cd255f69334457cd242055f69434957da54d195f65334957d3344055f7133495
  | 5, 0, 1 => 0x2169334856932430163691349589a4cb255a4cd24057da4c90d6069334957da4cd255f75328957da5d3255f69330957d64cd255a3490805
  | 6, 0, 0 => 0x7da4cd2c967da4cf349601f69334957da4cd24567da4cd243691f69334967da4cd248601f68d242501f69334457dd693349685f69334967da4d034967da55334967da4cd24067da4cd28967da4d13496
  | 6, 0, 1 => 0x7de69334967da4cd24167da4cd244689f693349601a4cd24057da4cd247601f6932435
  | 7, 0, 0 => 0x1f6933495
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
  | 0, 0 => 0x700000000000000000000000000000000000000000000000000000000000000003800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007fff8c40000000000000000000000000000000000000000000000000000000007e2673b00000000000000000000000000000000000000000000000000000000071e1f070000000000000000000000000000000000000000000000000000000000fe00ff000000000000000000000000000000000000000000000000000000000001ffff
  | 0, 1 => 0x1d9fff00000000000000000000000000000000000000000000000000000000001d98c400000000000000000000000000000000000000000000000000000000001d98c400000000000000000000000000000000000000000000000000000000001c000000000000000000000000000000000000000000000000000000000000001c00000000000000000000000000000000000000000000000000000000000000019800000000000000000000000000000000000000000000000000000000000000073b0000000000000000000000000000000000000000000000000000000000000000
  | 0, 2 => 0x1df8c4000000000000000000000000000000000000000000000000000000000001f8000000000000000000000000000000000000000000000000000000000000e1e7fb0000000000000000000000000000000000000000000000000000000000e1e0f80000000000000000000000000000000000000000000000000000000000e1e0f80000000000000000000000000000000000000000000000000000000000e000380000000000000000000000000000000000000000000000000000000000e00000000000000000000000000000000000000000000000000000000000000001e000
  | 0, 3 => 0x7fe00000000000000000000000000000000000000000000000000000000000007e1fff800000000000000000000000000000000000000000000000000000000071dffc4000000000000000000000000000000000000000000000000000000000701ffc0000000000000000000000000000000000000000000000000000000000701ff00000000000000000000000000000000000000000000000000000000000701ff00000000000000000000000000000000000000000000000000000000000701e0000000000000000000000000000000000000000000000000000000000000e1f8f8
  | 0, 4 => 0x7ffff000000000000000000000000000000000000000000000000000000000007ffe0f80000000000000000000000000000000000000000000000000000000007ff98c40000000000000000000000000000000000000000000000000000000007fe073b0000000000000000000000000000000000000000000000000000000007fe0000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x100af10000000000000000000000000000000000000000000000000000000000020a278000000000000000000000000000000000000000000000000000000000004894d0000000000000000000000000000000000000000000000000000000006d950800000000000000000000000000000000000000000000000000000000005a266320000000000000000000000000000000000000000000000000000000003161d0700000000000000000000000000000000000000000000000000000000006e00ef000000000000000000000000000000000000000000000000000000000000ab5d
  | 0, 1 => 0x37fbfff00000000000000000000000000000000000000000000000000000000037f9def00000000000000000000000000000000000000000000000000000000025d99cd00000000000000000000000000000000000000000000000000000000025d99cd00000000000000000000000000000000000000000000000000000000025d10800000000000000000000000000000000000000000000000000000000002119900000000000000000000000000000000000000000000000000000000000126af7f0000000000000000000000000000000000000000000000000000000001260422
  | 0, 2 => 0x6ddfbdd000000000000000000000000000000000000000000000000000000000691fb100000000000000000000000000000000000000000000000000000000005efefff0000000000000000000000000000000000000000000000000000000005efe6fa0000000000000000000000000000000000000000000000000000000004e9e2f80000000000000000000000000000000000000000000000000000000004e9e2f80000000000000000000000000000000000000000000000000000000004e940a0000000000000000000000000000000000000000000000000000000000481e210
  | 0, 3 => 0x7ff54a20000000000000000000000000000000000000000000000000000000007f9fff80000000000000000000000000000000000000000000000000000000007ddffdd0000000000000000000000000000000000000000000000000000000007d9ffd8000000000000000000000000000000000000000000000000000000000795ff5d000000000000000000000000000000000000000000000000000000000791ff10000000000000000000000000000000000000000000000000000000000791f6100000000000000000000000000000000000000000000000000000000006f9fbf8
  | 0, 4 => 0x7ffffb20000000000000000000000000000000000000000000000000000000007fff6fa0000000000000000000000000000000000000000000000000000000007ffddef0000000000000000000000000000000000000000000000000000000007ffffff0000000000000000000000000000000000000000000000000000000007ffddef
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_31 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_31 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
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

namespace S_55_8
def pairsG : List (Nat × Nat) := [(9, 11), (9, 13), (9, 25), (9, 41), (10, 11), (10, 26), (10, 42), (12, 13), (12, 28), (14, 15), (14, 30), (14, 46), (24, 25), (24, 26), (24, 28), (40, 41), (40, 42), (44, 45), (44, 46), (44, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [9, 9, 9, 9, 10, 10, 10, 12, 12, 14, 14, 14, 24, 24, 24, 40, 40, 44, 44, 44, 56, 56, 56]
def r2sG : List Nat := [11, 13, 25, 41, 11, 26, 42, 13, 28, 15, 30, 46, 25, 26, 28, 41, 42, 45, 46, 60, 57, 58, 60]
def mpG : Nat := 0x7fffff
def pool6G : List Nat := [11034175478029, 11034175346955, 26439971310876, 15432558447883, 44023568468778, 26427103251225, 13233198733581]
def xsM : List Nat := roots_55_8.map (· &&& dom_55_8)
def goalM : Nat := goal_55_8 &&& dom_55_8
def NN : Nat → Nat
  | 4 => 1
  | 5 => 5
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xc22d231e
  | 5, 0 => 0xc22d231e7ef3d89f7a5e75653356818827f195c0
  | 6, 0 => 0xc22d231e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff000000ff000000000000000000000000000000000000000000000000000000fc00fc00fc00fc00000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000cc00cc00cc00cc00000000000000000000000000000000000000000000000000aa00aa00aa00aa000000000000000000000000000000000000000000000000005500550055005500000000000000000000000000000000000000000000000000330033003300330000000000000000000000000000000000000000000000000000000000ff00ff00
  | 0, 1 => 0xff00ff0000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x875435
  | 5, 0, 0 => 0x875435875315754305876435875425
  | 6, 0, 0 => 0x875435
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
  | 0, 0 => 0x70700000000000000000000000000000000000000000000000000000000000000e0ff000000000000000000000000000000000000000000000000000000000000e0f800000000000000000000000000000000000000000000000000000000000000e70000000000000000000000000000000000000000000000000000000000000000f00000000000000000000000000000000000000000000000000000000007ffff000000000000000000000000000000000000000000000000000000000007ff18f0000000000000000000000000000000000000000000000000000000000007fff
  | 0, 1 => 0x7f8000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x78752400000000000000000000000000000000000000000000000000000000006f6ff300000000000000000000000000000000000000000000000000000000004e4f820000000000000000000000000000000000000000000000000000000000252e71000000000000000000000000000000000000000000000000000000000012929f00000000000000000000000000000000000000000000000000000000006d6d6000000000000000000000000000000000000000000000000000000000005ad18e00000000000000000000000000000000000000000000000000000000000077b7
  | 0, 1 => 0x7f8848
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

def symsG : List (List (Nat × Nat)) := [[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)]]
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

namespace S_62
def pairsG : List (Nat × Nat) := [(6, 22), (6, 38), (10, 26), (10, 42), (12, 28), (14, 30), (14, 46), (18, 22), (18, 26), (20, 22), (20, 28), (24, 26), (24, 28), (34, 38), (34, 42), (36, 38), (40, 42), (44, 46), (44, 60), (50, 54), (50, 58), (52, 54), (52, 60), (56, 58), (56, 60)]
def r1sG : List Nat := [6, 6, 10, 10, 12, 14, 14, 18, 18, 20, 20, 24, 24, 34, 34, 36, 40, 44, 44, 50, 50, 52, 52, 56, 56]
def r2sG : List Nat := [22, 38, 26, 42, 28, 30, 46, 22, 26, 22, 28, 26, 28, 38, 42, 38, 42, 46, 60, 54, 58, 54, 60, 58, 60]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := [22067946461718, 22016743054358, 26431969696794, 26474482112028, 26465925862938]
def xsM : List Nat := roots_62.map (· &&& dom_62)
def goalM : Nat := goal_62 &&& dom_62
def NN : Nat → Nat
  | 4 => 3
  | 5 => 7
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xa91103de7be3913609720071
  | 5, 0 => 0xe324ca91deee3556c894e17ca91103de45028db13a415d320ebf8666
  | 6, 0 => 0xa91103de
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x50505050505050500000000000000000000000000000000000000000000000004444444444444444000000000000000000000000000000000000000000000000444444444444000000000000000000000000000000000000000000000000000044444444000000000000000000000000000000000000000000000000000000001111111111111111000000000000000000000000000000000000000000000000050505050505050500000000000000000000000000000000000000000000000000005555000055550000000000000000000000000000000000000000000000000000000055555555
  | 0, 1 => 0x55555555555500000000000000000000000000000000000000000000000000005555555500000000000000000000000000000000000000000000000000000000555544445555000000000000000000000000000000000000000000000000000055550000555500000000000000000000000000000000000000000000000000005500550055005500
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0xb987650987540a8764
  | 5, 0, 0 => 0x987605b98735987645b98765b98625c98765b87615
  | 6, 0, 0 => 0xb98765
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
  | 0, 0 => 0x66867300000000000000000000000000000000000000000000000000000000001861ef000000000000000000000000000000000000000000000000000000000018618000000000000000000000000000000000000000000000000000000000001860000000000000000000000000000000000000000000000000000000000001e79e10000000000000000000000000000000000000000000000000000000000199798c000000000000000000000000000000000000000000000000000000000007e07f0000000000000000000000000000000000000000000000000000000000001fff
  | 0, 1 => 0x1ffff800000000000000000000000000000000000000000000000000000000001ffe0000000000000000000000000000000000000000000000000000000000001f87f800000000000000000000000000000000000000000000000000000000001f81f80000000000000000000000000000000000000000000000000000000000187187c
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x16eb6f30000000000000000000000000000000000000000000000000000000000bbebef0000000000000000000000000000000000000000000000000000000000bbebef0000000000000000000000000000000000000000000000000000000000bbe04a0000000000000000000000000000000000000000000000000000000001441410000000000000000000000000000000000000000000000000000000000091490c000000000000000000000000000000000000000000000000000000000003e04a0000000000000000000000000000000000000000000000000000000000001fb5
  | 0, 1 => 0x1ffffff0000000000000000000000000000000000000000000000000000000001ffe04a0000000000000000000000000000000000000000000000000000000001ffffff0000000000000000000000000000000000000000000000000000000001fc1fb50000000000000000000000000000000000000000000000000000000001d75d7c
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_62 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_62 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
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
private theorem z4_0 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := z4_0
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

namespace S_31_32
def pairsG : List (Nat × Nat) := [(32, 33), (34, 35), (34, 38), (34, 42), (36, 37), (36, 38), (40, 41), (40, 42), (44, 45), (44, 46), (44, 60), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [32, 34, 34, 34, 36, 36, 40, 40, 44, 44, 44, 48, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [33, 35, 38, 42, 37, 38, 41, 42, 45, 46, 60, 49, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0x1fffff
def pool6G : List Nat := [39729390955046, 57321576999462, 44127370356266]
def xsM : List Nat := roots_31_32.map (· &&& dom_31_32)
def goalM : Nat := goal_31_32 &&& dom_31_32
def NN : Nat → Nat
  | 4 => 1
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x5f5ce351
  | 5, 0 => 0x5f5ce351
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffff000000000000000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000cccccccc00000000000000000000000000000000000000000000000000000000aaaaaaaa00000000
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
  | 0, 0 => 0x1ff80000000000000000000000000000000000000000000000000000000000001c07c00000000000000000000000000000000000000000000000000000000000038730000000000000000000000000000000000000000000000000000000000000700e0000000000000000000000000000000000000000000000000000000000000000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x1ffc0000000000000000000000000000000000000000000000000000000000001e47c8000000000000000000000000000000000000000000000000000000000013a73400000000000000000000000000000000000000000000000000000000000972ae0000000000000000000000000000000000000000000000000000000000049953
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_31_32 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_31_32 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
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
  scr dom_31_32 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_31_32 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_31_32 roots_31_32 goal_31_32 6 := by
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

theorem low_31_32 : Lower dom_31_32 roots_31_32 goal_31_32 6 := S_31_32.noCircuit

namespace S_55
def pairsG : List (Nat × Nat) := [(1, 3), (1, 17), (1, 33), (2, 3), (5, 7), (5, 21), (5, 37), (6, 7), (6, 22), (6, 38), (16, 17), (18, 19), (18, 22), (20, 21), (20, 22), (32, 33), (34, 35), (34, 38), (36, 37), (36, 38), (48, 49), (50, 51), (50, 54), (52, 53), (52, 54)]
def r1sG : List Nat := [1, 1, 1, 2, 5, 5, 5, 6, 6, 6, 16, 18, 18, 20, 20, 32, 34, 34, 36, 36, 48, 50, 50, 52, 52]
def r2sG : List Nat := [3, 17, 33, 3, 7, 21, 37, 7, 22, 38, 17, 19, 22, 21, 22, 33, 35, 38, 37, 38, 49, 51, 54, 53, 54]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := [2203655213315, 6601701724419, 17596583117585]
def xsM : List Nat := roots_55.map (· &&& dom_55)
def goalM : Nat := goal_55 &&& dom_55
def NN : Nat → Nat
  | 4 => 2
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xa584d60f47baa070
  | 5, 0 => 0x47baa070
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00ff00ff000000000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000cc00cc00cc00cc00000000000000000000000000000000000000000000000000aa00aa00aa00aa
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x544246885
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
  | 0, 0 => 0x1fffc000000000000000000000000000000000000000000000000000000000001ff80000000000000000000000000000000000000000000000000000000000001f07c0000000000000000000000000000000000000000000000000000000000018c63f00000000000000000000000000000000000000000000000000000000000631b880000000000000000000000000000000000000000000000000000000000000077
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x1ffff660000000000000000000000000000000000000000000000000000000001ff82440000000000000000000000000000000000000000000000000000000001f07d220000000000000000000000000000000000000000000000000000000001ce73f000000000000000000000000000000000000000000000000000000000016b5b990000000000000000000000000000000000000000000000000000000000b5acff
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_55 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_55 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]
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

namespace S_61
def pairsG : List (Nat × Nat) := [(1, 17), (1, 33), (5, 13), (5, 21), (5, 37), (9, 13), (9, 25), (9, 41), (12, 13), (12, 28), (16, 17), (20, 21), (20, 28), (24, 25), (24, 28), (32, 33), (36, 37), (40, 41), (44, 45), (44, 60), (48, 49), (52, 53), (52, 60), (56, 57), (56, 60)]
def r1sG : List Nat := [1, 1, 5, 5, 5, 9, 9, 9, 12, 12, 16, 20, 20, 24, 24, 32, 36, 40, 44, 44, 48, 52, 52, 56, 56]
def r2sG : List Nat := [17, 33, 13, 21, 37, 13, 25, 41, 13, 28, 17, 21, 28, 25, 28, 33, 37, 41, 45, 60, 49, 53, 60, 57, 60]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := [13198704775437, 13215951753485, 17596684176657]
def xsM : List Nat := roots_61.map (· &&& dom_61)
def goalM : Nat := goal_61 &&& dom_61
def NN : Nat → Nat
  | 4 => 2
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x995298d1145b47b8
  | 5, 0 => 0x995298d1
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x333333330000000000000000000000000000000000000000000000000000000033330000333300000000000000000000000000000000000000000000000000003300330033003300000000000000000000000000000000000000000000000000303030303030303000000000000000000000000000000000000000000000000030003000300030000000000000000000000000000000000000000000000000002222222222222222
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x2c6828b084
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
  | 0, 0 => 0x1ff80000000000000000000000000000000000000000000000000000000000001f07c0000000000000000000000000000000000000000000000000000000000018e63e000000000000000000000000000000000000000000000000000000000006d1b1c00000000000000000000000000000000000000000000000000000000000c030000000000000000000000000000000000000000000000000000000000000000ff
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x1ff80920000000000000000000000000000000000000000000000000000000001f87e490000000000000000000000000000000000000000000000000000000001ce73e400000000000000000000000000000000000000000000000000000000016d5b3c00000000000000000000000000000000000000000000000000000000014c53240000000000000000000000000000000000000000000000000000000000b7adff
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

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
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

namespace S_15_48
def pairsG : List (Nat × Nat) := [(48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [48, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [49, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0x3ff
def pool6G : List Nat := [57390296480310]
def xsM : List Nat := roots_15_48.map (· &&& dom_15_48)
def goalM : Nat := goal_15_48 &&& dom_15_48
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x8a5bc14c
  | 4, 0 => 0x8a5bc14c
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00000000000000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000cccc000000000000000000000000000000000000000000000000000000000000aaaa000000000000
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_15_48 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_15_48 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_15_48 == dom_15_48) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_15_48 goalM u ys) : RunD dom_15_48 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_15_48 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_15_48 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_15_48 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_15_48 roots_15_48 goal_15_48 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_15_48 goal_15_48 := by
    have h0 : isConstB dom_15_48 goal_15_48 = false := by decide +kernel
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

end S_15_48

theorem low_15_48 : Lower dom_15_48 roots_15_48 goal_15_48 5 := S_15_48.noCircuit

namespace S_23
def pairsG : List (Nat × Nat) := [(1, 3), (1, 17), (2, 3), (5, 7), (5, 21), (6, 7), (6, 22), (16, 17), (18, 19), (18, 22), (20, 21), (20, 22)]
def r1sG : List Nat := [1, 1, 2, 5, 5, 6, 6, 16, 18, 18, 20, 20]
def r2sG : List Nat := [3, 17, 3, 7, 21, 7, 22, 17, 19, 22, 21, 22]
def mpG : Nat := 0xfff
def pool6G : List Nat := [6601701724419, 17596583117585]
def xsM : List Nat := roots_23.map (· &&& dom_23)
def goalM : Nat := goal_23 &&& dom_23
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x678b910d
  | 4, 0 => 0x678b910d
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00000000000000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000cc00cc0000000000000000000000000000000000000000000000000000000000aa00aa
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
  | 0, 0 => 0xf800000000000000000000000000000000000000000000000000000000000000c780000000000000000000000000000000000000000000000000000000000000364000000000000000000000000000000000000000000000000000000000000001b
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfd20000000000000000000000000000000000000000000000000000000000000e780000000000000000000000000000000000000000000000000000000000000b6d00000000000000000000000000000000000000000000000000000000000005bf
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_23 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_23 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_23 == dom_23) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_23 goalM u ys) : RunD dom_23 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_23 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_23 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_23 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_23 roots_23 goal_23 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_23 goal_23 := by
    have h0 : isConstB dom_23 goal_23 = false := by decide +kernel
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

end S_23

theorem low_23 : Lower dom_23 roots_23 goal_23 5 := S_23.noCircuit

namespace S_39_8
def pairsG : List (Nat × Nat) := [(9, 11), (9, 13), (9, 41), (10, 11), (10, 42), (12, 13), (14, 15), (14, 46), (40, 41), (40, 42), (44, 45), (44, 46)]
def r1sG : List Nat := [9, 9, 9, 10, 10, 12, 14, 14, 40, 40, 44, 44]
def r2sG : List Nat := [11, 13, 41, 11, 42, 13, 15, 46, 41, 42, 45, 46]
def mpG : Nat := 0xfff
def pool6G : List Nat := [11034444835083, 44019290344233]
def xsM : List Nat := roots_39_8.map (· &&& dom_39_8)
def goalM : Nat := goal_39_8 &&& dom_39_8
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x63a897bc
  | 4, 0 => 0x63a897bc
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00000000000000000000000000000000000000000000000000000000000000f0000000f0000000000000000000000000000000000000000000000000000000cc000000cc000000000000000000000000000000000000000000000000000000aa000000aa00
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_39_8 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_39_8 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_39_8 == dom_39_8) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_39_8 goalM u ys) : RunD dom_39_8 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_39_8 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_39_8 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_39_8 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_39_8 roots_39_8 goal_39_8 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_39_8 goal_39_8 := by
    have h0 : isConstB dom_39_8 goal_39_8 = false := by decide +kernel
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

end S_39_8

theorem low_39_8 : Lower dom_39_8 roots_39_8 goal_39_8 5 := S_39_8.noCircuit

namespace S_30
def pairsG : List (Nat × Nat) := [(6, 22), (10, 26), (12, 28), (14, 30), (18, 22), (18, 26), (20, 22), (20, 28), (24, 26), (24, 28)]
def r1sG : List Nat := [6, 10, 12, 14, 18, 18, 20, 20, 24, 24]
def r2sG : List Nat := [22, 26, 28, 30, 22, 26, 22, 28, 26, 28]
def mpG : Nat := 0x3ff
def pool6G : List Nat := [22067946461718]
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
  | 0, 0 => 0x3f0000000000000000000000000000000000000000000000000000000000000030e00000000000000000000000000000000000000000000000000000000000000cd000000000000000000000000000000000000000000000000000000000000003b
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3ff00000000000000000000000000000000000000000000000000000000000003ae00000000000000000000000000000000000000000000000000000000000002dd000000000000000000000000000000000000000000000000000000000000017b
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

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]]
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

namespace S_30_32
def pairsG : List (Nat × Nat) := [(34, 38), (34, 42), (36, 38), (40, 42), (44, 46), (44, 60), (50, 54), (50, 58), (52, 54), (52, 60), (56, 58), (56, 60)]
def r1sG : List Nat := [34, 34, 36, 40, 44, 44, 50, 50, 52, 52, 56, 56]
def r2sG : List Nat := [38, 42, 38, 42, 46, 60, 54, 58, 54, 60, 58, 60]
def mpG : Nat := 0xfff
def pool6G : List Nat := [57321576999462, 44127370356266]
def xsM : List Nat := roots_30_32.map (· &&& dom_30_32)
def goalM : Nat := goal_30_32 &&& dom_30_32
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x4b5c3f1e
  | 4, 0 => 0x4b5c3f1e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x5555000000000000000000000000000000000000000000000000000000000000550055000000000000000000000000000000000000000000000000000000000050505050000000000000000000000000000000000000000000000000000000004444444400000000
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_30_32 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_30_32 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
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
  scr dom_30_32 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_30_32 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_30_32 roots_30_32 goal_30_32 5 := by
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

theorem low_30_32 : Lower dom_30_32 roots_30_32 goal_30_32 5 := S_30_32.noCircuit

namespace S_27_4
def pairsG : List (Nat × Nat) := [(5, 7), (5, 13), (5, 21), (6, 7), (6, 22), (12, 13), (12, 28), (14, 15), (14, 30), (20, 21), (20, 22), (20, 28)]
def r1sG : List Nat := [5, 5, 5, 6, 6, 12, 12, 14, 14, 20, 20, 20]
def r2sG : List Nat := [7, 13, 21, 7, 22, 13, 28, 15, 30, 21, 22, 28]
def mpG : Nat := 0xfff
def pool6G : List Nat := [6618881594631, 6618881987853]
def xsM : List Nat := roots_27_4.map (· &&& dom_27_4)
def goalM : Nat := goal_27_4 &&& dom_27_4
def NN : Nat → Nat
  | 3 => 2
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xde1ca23153667bc8
  | 4, 0 => 0xde1ca231
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f0000000000000000000000000000000000000000000000000000000000000f0c0f0c000000000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000c0c0c0c000000000000000000000000000000000000000000000000000000000a0a0a0a0
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_27_4 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_27_4 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_27_4 == dom_27_4) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_27_4 goalM u ys) : RunD dom_27_4 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_27_4 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_27_4 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_27_4 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_27_4 roots_27_4 goal_27_4 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_27_4 goal_27_4 := by
    have h0 : isConstB dom_27_4 goal_27_4 = false := by decide +kernel
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

end S_27_4

theorem low_27_4 : Lower dom_27_4 roots_27_4 goal_27_4 5 := S_27_4.noCircuit

def isoMv_59_4 : List (Nat × Nat) := [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem low_59_4 : Lower dom_59_4 roots_59_4 goal_59_4 7 :=
  lower_iso isoMv_59_4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_55_8

def isoMv_59 : List (Nat × Nat) := [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem low_59 : Lower dom_59 roots_59 goal_59 6 :=
  lower_iso isoMv_59 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_55

def isoMv_39 : List (Nat × Nat) := [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]
theorem low_39 : Lower dom_39 roots_39 goal_39 5 :=
  lower_iso isoMv_39 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23

def isoMv_27 : List (Nat × Nat) := [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem low_27 : Lower dom_27 roots_27 goal_27 5 :=
  lower_iso isoMv_27 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23

def isoMv_43 : List (Nat × Nat) := [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]
theorem low_43 : Lower dom_43 roots_43 goal_43 5 :=
  lower_iso isoMv_43 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23

def isoMv_43_4 : List (Nat × Nat) := [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem low_43_4 : Lower dom_43_4 roots_43_4 goal_43_4 5 :=
  lower_iso isoMv_43_4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_39_8

def isoMv_53_8 : List (Nat × Nat) := [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)]
theorem low_53_8 : Lower dom_53_8 roots_53_8 goal_53_8 5 :=
  lower_iso isoMv_53_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_39_8

def isoMv_57_4 : List (Nat × Nat) := [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)]
theorem low_57_4 : Lower dom_57_4 roots_57_4 goal_57_4 5 :=
  lower_iso isoMv_57_4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_39_8

def isoMv_51_8 : List (Nat × Nat) := [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem low_51_8 : Lower dom_51_8 roots_51_8 goal_51_8 5 :=
  lower_iso isoMv_51_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_27_4

namespace S_63
def pairsG : List (Nat × Nat) := [(1, 3), (1, 17), (1, 33), (2, 3), (5, 7), (5, 13), (5, 21), (5, 37), (6, 7), (6, 22), (6, 38), (9, 11), (9, 13), (9, 25), (9, 41), (10, 11), (10, 26), (10, 42), (12, 13), (12, 28), (14, 15), (14, 30), (14, 46), (16, 17), (18, 19), (18, 22), (18, 26), (20, 21), (20, 22), (20, 28), (24, 25), (24, 26), (24, 28), (32, 33), (34, 35), (34, 38), (34, 42), (36, 37), (36, 38), (40, 41), (40, 42), (44, 45), (44, 46), (44, 60), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [1, 1, 1, 2, 5, 5, 5, 5, 6, 6, 6, 9, 9, 9, 9, 10, 10, 10, 12, 12, 14, 14, 14, 16, 18, 18, 18, 20, 20, 20, 24, 24, 24, 32, 34, 34, 34, 36, 36, 40, 40, 44, 44, 44, 48, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [3, 17, 33, 3, 7, 13, 21, 37, 7, 22, 38, 11, 13, 25, 41, 11, 26, 42, 13, 28, 15, 30, 46, 17, 19, 22, 26, 21, 22, 28, 25, 26, 28, 33, 35, 38, 42, 37, 38, 41, 42, 45, 46, 60, 49, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0x3fffffffffffff
def pool6G : List Nat := [2203655213315, 2203722584323, 15432120926989, 9917383185933, 15414941319949, 19834243976474, 19817131216150, 19795606373137, 6601701724419, 19795841257731, 22016020251414, 22067693814550, 17596684176657, 2203924701443, 22067946461718, 35188770210593, 21994629628689, 26392743510801, 5502189900035, 6602105692419, 19795908628739, 2203553957635, 6618780337923, 37409318309158, 5502156345603, 15414941323533, 22041857166620, 5502088840963, 37426431069482, 2203521387779, 48438660104988, 37387793466145, 19795740593425, 13215951753485, 17596718386465, 21994730687761, 26392777198865, 35188904430881, 10999495984899, 15398198447363, 48383043961633, 48400323842317, 22016020251430, 26465673216794, 39608207344422, 21995267890193, 13233198731533, 26474482112028]
def xsM : List Nat := roots_63.map (· &&& dom_63)
def goalM : Nat := goal_63 &&& dom_63
def NN : Nat → Nat
  | 1 => 1
  | 2 => 2
  | 3 => 5
  | 4 => 14
  | 5 => 61
  | 6 => 358
  | 7 => 776
  | 8 => 298
  | 9 => 25
  | 10 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 1, 0 => 0xe45a5cfe
  | 2, 0 => 0xe82242f6e6392d87
  | 3, 0 => 0xff445be6ea01137fe5969956abc61f692b63e37c
  | 4, 0 => 0xe95e7f4eaf8e0561ab238b38a8f8557a99002268706938bf4285fc6c330ff9d32d42b4052867add02658facc25766108235e91be01232c6f
  | 5, 0 => 0xf61a2418f5325d7af4ff858bf2cfa5e7ee796e0fe770bba7d8a96787c6b01e51c42d56b4b6feb63cb1e33fe7b0f17419b0223b58afb1883aaeeb7130aad72603a9e92ed4a3c2d3a194f8a9e58a5465a187ca096d870ae7f886c414e07e5ddefe7b30d8057a37d19878541dd676cc1efb76519a5971fb62816cd512345e8d144a5791ab49468f8d1244a7ee114464ccf53da975783d3008b63c9879f83a80aaae36c88086326d65a232334d582d9e4af02c2f93c82b4a5a102a9fafc227c5199f2755319120c1cba51be89da81a695e72177ef6ab14e5fc0c0dfb5be70de5c68e0d0324830ca1b0ed0c6ef09d0a5c0143022e2603
  | 6, 0 => 0x22df8dff225eabe820bc756a2083e4e5202e99431f32f90b1f2478e81ef373fc1e9cc3911d8558b71c89b87f1af0026819ba301a1801cbea16ec765a163d7d3b15dac5e9152bb1531499d35c136f20cf131ed0f6120a7d62120898f01099094c105e20a00fa22a3f0ea0e8490e9e03da0e72868d0e2fb7100dd7f6160d3f24990d3c3d080ce727380c8d67dd0c17cb990b473e830b1f72c00a8b9a7a0a410a790a2e37410a1d775509f1bed70985e8ad096e9438094b01c808f317a507b6b1a60770b60c06e4336306d526820653330106165d76059b86ff048b1ab104773d45043575920407793403f4dcfd03cafc6f02248e4602141efc01aa0370016f0f1c
  | 6, 1 => 0x41b0005d40a605d0405d8ca33e774a813dfd6b3c3d8521ca3c918fa43c86b61d3c73d1683c50ab893aefdd6b3a7beb523a6a1268396cd777393cca5b37dabc6e37786e1936bd7d74354b0a453535ffea342fbfa3342e277a3404b2bb33abea14335d721e32e5408e32b049dc32a1c9b93253c5543240a7d031247b87308f8f193037bc2b300b6c6f2fea97062faafad52f3768e32ef81bc92ed076b62ecf36372e9d9a572e6465742e39ccc52daf83d32cd7fc3a2cc97de72c05aa412bc7d4c12b8cff972b896f002b87ab452b864c3c292917232909654c280701e12779c54f274008b7262449c0256eb4e124f17cc6249d0b20247d61fb24253d7323c3c9dd
  | 6, 2 => 0x6118463c606890ab5fbd7bb65f6a76f25e2f68925e2d8aab5e03e3065db364cf5da5c7265d6299ff5d5685745d26770c5c4066715c37edd15bc1552b5a859bc75a0287bc59e66e3f598ead455919d7465918149f58280b7857f49c8f57bb87b15774f75957530f6056e35aec5671318556488c3a5519ba1b54cbb6cd53d1b7ef53b44d1253a485fb51287763508043c85043af794ff122394fb7f99b4f7c60744f24b30c4e6543824d27656c4cf16d7e4c30865f4b2f44694af9b4664ac8006b4955664848abc4a147ab784b4621232945870eb2451f7c0844a5495d44605e224454025043ce39d243660a1b4351acb842c49da2426c730041c4ac5641c1c8b2
  | 6, 3 => 0x92c480a29138155890b5b860905e2d978f0b27718c5b23db8b3b61e889ba4896888265a58582521585608b2884cb2ae58439d46b84149d908101c17480f736818005e9617e4a8ec17ba3862e7b673f657987147e787cbaa1776eb37a767e65fb75af2d3a75413da674bbbb81745428d773e5e17c73da330a73d9f62c7367b864734bd99472bbb27f723b692c722eeeb671acb963717dc5bd70bc839a706417e56fb53ea26f71344e6f3ea5fc6ecfff346eb3c4396e21c3316ce454cd6bc292956b574dbe6b1a44016afea1cb6a8772f96a3ddff369a9469668f6787b68e5d86667aab8ca666cb1e865233d0763354a6c6308ebc862a203dd61e2945361d7af80
  | 6, 4 => 0xd848128fd7fc3831d7ca6921d71e8632d699040dd68ff896d4e034e8d382d7dbd1d9802ed0d44853cfe8f325ce90062dcbc4c03aca5bf32ac9dc63d9c9880156c96e2cf4c7bb17e5c67def90c598adc9c3e4acefc35d2172c1f92d71c07272b0bfcc018bbfc9aac5be3fd440baf55d2bb8e76ab4b8b042bfb8682e78b7dce78eb461f023b2bc8ad0b02be350afa0a3f5af1e77e5af0ef409ae713628abf5bd73ab7e78f1ab26b7f7ab05838bab03f1a5a8c66ffda764573ea475ea75a43e68a99fc00bf19da01b9e9c4bd7d69c04b2559b6392cd9a8bfa8d99af20c79955b6a598dddbf998a285c79791ee61973b918196f31b5296df659996c3c09c96834a82
  | 6, 5 => 0xfff9fcc0ffb9d880ff2252acfe292062fd9810a5fc40a38ff8bcae25f5a27ec1f546465bf3a2bcc9f3175066f2f328c0f0dc9f5ef0cf9de6f0583e98f02ca1a4f0046573eca992adec82db7dec46f140eb1a49a4ead9e5ceea635f01e876697ce580cb8ae52ad8a9e4c5638ae4b38d88e2961cc8e276b9c4e0e648dbdff65054df47c834defb0a41dc9a8eb0db2ea2b1d9352887d8bb42fe
  | 7, 0 => 0xb2e0ec30ae653d70ac7b95d0ac4d5b90a7a55280a7677f5096f6e7c0919997808e3547c08b081660899ab530844bf8307f1b6d607ca96c507c20e2707a72649078179cf077a5788074eba9407073daf06735b22065d5685065bd6fd062e761d060f596e060e01a40608061805e9221005b10e6b054b0cc90512d189050c65e0050bb04c0509fa1f04fde5bd04ec9b9b04e553f804d8394304963a7b048cd7a50442bd860380978b033a76b4030a418d02ebab1d029b1558028de01e0266400402363de2020b934d01eac28901e3cad001dadaa501cde8810166035701551783015437cd014fcec700d76e02009bfdb900481fea0031a7ea002d875e0029bfef
  | 7, 1 => 0x1bc210541b24771a1b16f5ed1afecaa01a4dc7a41a1f1cf01a07944f19f37e0719ddb2d519ba301a198e7f10198916cb1891280c1862a4c917e4d13d17c5c22e17761fd81701656116dbf17016bc7a2616b01e5416446b9c161648bc154b39521517feab14e907ff14a1e5f2140c1c6113a8dfe013a5e7b213346ed111f8a56611bd00b711a579d6118d0e1d117804a41161181a115e10321144e41f104862a51001b9520ff47fa50f8899180f2f25820f2b7b310f1986a90ee2d2210ed5a7770ecc23a60e974d5b0e7db3450e255d760dc23f740d871bf50d6e8d170d5878c60d570f570d3586890ce9b2880cc62e6c0c9359830c6d8e9c0be174e40ba8521d
  | 7, 2 => 0x29b291b729af2b642993998d293f76f0292c965229259dd72908d1e428e3a3d128e38c4e28a4a83e286658d02824ea9a27bb223c276fb0f92750b4f62738adc8272630b12724c80b2710b40c26f168c92648e3a825e030e425c30139257baa0e2409402823fc45a223e65826237f0a232360951f232c6add22dc5fcc22c96b30224d3e3d2208064121eaa96f21e8fd3821997fae219634db213f9045211778dc20cdfb2c20779391204fb0ae203a916820257d1e2014c6441fea900e1f4d89821edb86661ed8ca961ed55caf1e5ad6651df73f721de177831db4fd5a1daeb8c11d85da9b1d75a3ee1d66c50e1cd038361c96ea491c397d011c228a231bf6c35a
  | 7, 3 => 0x3d2c7c353d18139e3c66947b3c21f90f3c21b4153ba23b6b3b9f7aeb3b754d643b5dab7f3b40a23f3b3e76333b05d6f73a8512d93a4fc2063a3b596f39ab24c4396724ec390ed69f38334b9d37b0076a37a858aa3791ff6b3778a28c36b521a23669c03b364691d83644f7dd359166703542ae7334fe1fe134a771a73466ebee345ddff5343eb05733cd017f33b85c433360306f32693d4d3244176032113f4a3140401c30f2019a30dba214308db847303037e92fa88bf32f2d39052f03b74b2e9b5e9e2df013cb2de6358a2dcb18752d90a6012d7f44742d70ced82d2f60a22c42325c2bbea46f2b87620c2b811d732b25f1c52a95810c2a8620162a245e7b
  | 7, 4 => 0x4ae43b454acde2064abd1d0b4ab9f0674a9428d24a55e64349f5550949e8ddff49c3e2a949bb2fc34994bba049780ea84975de4448a6ffde487e5127480eeebd47b76ea347b1a80947703dcb46de759446bdac874667f2b7465893254641fd804636123045f28fa645a7f598455be5b544978530447c8c18446729e6445ca64c4458f2e5441784af440fd5ef4408d56743d9e1c143c1fcc9433c06d4431f7df7430c7f9b42691ba042115aa642048bd541ec4f6f419ac2004175158641669563412c1b3840e8120340e5429a40acb173404b3013401a1c4f3ff0f5f13fdba9f43fd3ef6d3f7f6a493f3bf5403f291ad13efd382b3e444aad3e43e3b53d4e642e
  | 7, 5 => 0x5b796d475b34bf745af3513e5a7ee5485a5bc66559b8153059a3d552593c1d17592ae1565925466958e6c546584a10b25810d46d580e34785794d580578d26c0575675b3574ab38e5744b4ce5707fb675695f06f567043f556488c3a5640306855f9c36e554bcaab551f842c54d5ab8054b5735e54a96c09548e6dd85467b4c65462936b53f747b753c014995395ea585372c479535ddd7852a2b54152747f074fc3b88c4fbdd0064fb909274efcd55e4ebf453b4e9a87094e9581a94e2ce2974db8aa404d84259f4d7a1a494d43334a4d2ff4d14d2e7a0c4d1a0f054c8a818c4c3dfc2c4c29021d4b8c97694b51d8934b50406a4b2d583b4b25a97b4aeba8ec
  | 7, 6 => 0x6b9d976b6b39f7fd6b302ff16ac69eeb6a95be0b6a77afd06a27cc6b69ee0a6569b0c44b69846ed56972e47d68fa0825684a90536805cfb76722fc5967133b2966e4732066db2e4966b2ba9b6579a4ac6554023764497e5c643988c96413866e6407b8f163939f336390b0186378333e633659f86309db4662515d59621bcd566218865161aa3368613fcc2c60afae3b609eba3e6008d590600139515ffaba205fbb4cfd5f64e4b85f35ba935f26c7b65f18482b5ef083785ecd913b5e618c165e394d3c5dd41be55dd08b735d8bf1475d87d7425d7c88575d797f965d71535d5d6dd96d5d24c09a5cb3f1435c9b90375c97debb5bccb9a15bc3aaf25b8c3f8e
  | 7, 7 => 0x7e7a0a4c7e704a887db173387da51d3c7d8ecad87caec7187c1e2ac87bd0c6937b665f577a92749f7a399f0c79ee9d3679cce61979c0734279b70aa979a30aba78a6665977abf413779ce732779c985d778509c277439b8c7713b4c076f5840f76132263753f338374f8ca7a74d57dbf74cf39e4749a5b0074789e647406feac7369e1d773627f61730cc97a730c5ff872dbdfac726a4e0172464c217236cfcc7158096d7108872f70f586af70eea42e70b68b1c70abc4e07083b44a7066c39370607efa7019ef6970120e996fb8decd6f410f6b6f089c3c6edda0a16d78f77c6d70aedd6d04869a6cce300b6c64553c6c3bd30b6c2229556be5d2566bb1d2a9
  | 7, 8 => 0x9595a4cf956ca7b19551aacc951cbb3294d7782194ae151694a8304893266c9891b481cb918c7c0390f610e68fe45b0a8f80fc978efb1ed68e7679718e1426838d51792f8d08c8b48c6170088b3f92418ac0ec5d8aa44b2d8a81f0ca89eee1ee89ddcb6f8990733489312aef88e50a94881af38987de9c8a8742e14786934d3e863197e385a623a085569ca785355bfe8475b5338436e17f8433dbed84064fcd83e740ff83c7f1fb83a489f18397403a833cce4882f4c1688220babb821853fe81fd9d37812adf7780b2a53b80ab0b5c807ff0398069eaef8018916b7fe1a60d7f68a8f97f6323277f3318f67f0164fb7ed1cb467eba6e227ead80c27e877dce
  | 7, 9 => 0xb64b2e2db6251136b5bed785b593ef12b4efd615b4c2348eb36df0c6b285abbdb20fcd5fb1373743b0b60c78b077cf95b0775d12afc49eb7af9abc18aeb40751ae5daa71ad58a5d0ad096b8bac0421faabd5fcedab79c6cbab55c58dab555734aab7ca8baab16adaa9e955e2a994b72fa97aa236a96b0c4ea8f52011a840633ca7db1328a787d6aea41d54f3a398e729a37a73fba3780a8ca343ddefa32cb193a1537f86a0566735a02193399fc0bc2f9fb7f0179f90b24e9e7744839d81d89d9d72dd149d65b4079c625b659be41d5a9b5bed5b9b56d6249b2cc6529ab4c09298f4208d9873ca0f97f3060497a4a4a197a00225970d4168968d4d5f95b93d76
  | 7, 10 => 0xd7948ba0d7272a2ed70a1d9bd6d35949d5e44738d445852fd2299bdcd1296545d0853c66d031b422d028b587cfe29780cf8a4768cf564008ce26823ccde52a59cdd3764dcbedcfe9cbaeeccfcb502d09cb18ca29cb099803c97fa584c94a0471c8c1bbacc7914283c641ee37c63265b2c5736c6ac543b096c4d7a737c3b83a47c3ab90edc3432490c2a091e1c1eeb825c1d4122fc1980f89c1041042c0f590b7c07820b8c02abdb5bf74c678bf662c09beffe354bef0b2a0bee3383dbe663abdbe51e5eebd2fc437bcbbca35bc7e8f37bc545819bc1a5d6dbc042ef7bbd1589fbb4177cfbaaf9667b92faeabb87338fbb865d7beb7f92244b7dce78eb6855c3d
  | 7, 11 => 0xf9aef702f8bf6874f808cdccf5cc8aeef5985e51f4dbe8a1f44d45f4f31ff462f318916ef2d35972f2bcc31ff250bba1f1e2cc0df0f8df95f053c1fdefdd5beeee71c1e8ee597df1ee1c04b4edb21186ed2ae9e7ed05a64cec164c1eebefca4bebdb61b4eafba6c3ea478666e9f83c15e8fb991ee86bdb4be849f352e7da183de73f702ce712a48ae6f5ef60e5dbe277e55dcfb7e4c89be1e4489ffce2f6af66e2e6d92ae247b55ee232c2d0e175a2ade171d949dff3a4ccdfe0ba32df3d5635dee983e1decf68e7de74f913dd6521e7dcbac6b9dc8a5345dbe204b1db4f33a9daa10b17da4ab022d97fc822d9612da7d957a573d8f65272d8af4f05d82e7458
  | 7, 12 => 0xffa01f3aff98826cff17444ffecb99bcfe2b8d04fdde0471fb19fc8af9b835b8
  | 8, 0 => 0x275958f22705880d26beaf6f265363bb261c309d26093241246554a62429651523afce9223038dd422d85c9a2219ec0a21e9d24d20df43cc2081cc61204aaf2d20292edb2014c6441f3108e21d989e101d89743f1d81c57f1d29fe0a1ca0b1831c1ffead1b78d4bc1a0dc40d19b1d448196672e1181aa941175a929b16d8a81c16b50ee91581f8c81460a7d9141a4f1c1308cd7712b8884a12ae5da311ed84b7119811440f8898390e8414b20e7e15130e7dd0190dfe576f0dfb96ef0d9cbe430d9a92370d61f2fb0d4d98860cea20e10cc7aa850cabde0a0c22507d09ee1b6f06b07a0306291d8305c61dd605a3eb0a040745c602e9d44b0086a50c00273479
  | 8, 1 => 0x4dc27b5b4cfd734b4c1e35cd4c1326ad4bff26be4b02825d4a67071549e125c6499b08ca4951a01343b42571434ac0324309ffd8430588364214fad141a8390640ccbe134079af633dff89d03d6d0b963c9dc2fe3c3d49423c21f90f3be08ad93b5624293a476634396f572d39374a4d387c221637b9fc1b3732d33a36e4026d36c744ae366fa272359f67e7359275fc3481847a34064f6c33d93c6b339be83032ba82ac3264f1943243d5cd321769013129ad3f30ccd1eb30bda81a302ca7772fc976f62f7655c82efbd9642de85b922d90db782cb7e2692b81626d2a7c85282a6cf07129f0f18429e942c42964176b291abe5628a4a83e2838c79a2774c460
  | 8, 2 => 0x7a372f2c7a2bf43679e15a2879a4d76c7892577578493a7f75d42690759ff9f3749b988673f60c3a72b28339727daf3d721cd833705b5d9f6f69601f6ebe77696e8018a76db8095f6d483b2f6be1bd3a6bcb63fb6a7ff6686a4f220867f1c0d3679d352a6733942567044c4c651506a4645092fc6401590263669d9563353df461aa33685debf6475d1d08615cde0cce5c9fbd605bff541c5bec8f385b2acd595aa8a6b9568ff7f15640306856240dff55f35c3e5550dd6c5423f49e531915d15314eaf6530ec13f52943af5523dc21151ee61ea51e81d5151bf3f2b51099cc6505beeb3500139404fb2394c4f717d1d4f5ddbaa4e9d19034e2ce2974e171765
  | 8, 3 => 0xb253eee6b23cd636b0e1dcffaf95e2ffae064aa9ada32de2abbe6e52aa8df529aa87c3f1a8d69abba840633ca4a02823a494c22fa3f2435da1b25c0ca00d2aa29dac490d9b71391a9b1dd7b09a36658d99ed5e879985b80797ec88bb97a5128c968ac1e9965531e695a996be93f42b8d93602c469351acbb934043b8927d838491b98d12913f544190061e318e7679718e35cdb08d5eaaf98d1e3ac28bc68b508bbc73f08b8fda438acf54ff8a8bfac78a81f0ca8958e8bc877910e2867726a18651842c85520fcd8492c7cd83f048fb82d3eb9981102355806266ad7f5f0e0b7e8559377dfd47397db1e1917db173387bf0d3337ab597257ab2c9087aa15747
  | 8, 4 => 0xffcceadcfefc312dfce2758bfbefb591fa7b52c7f9acd0faf6e94291f4642245f32a1730f053c1fded80931eec164c1eeabec0cde7a75556e73f702ce3d420a8e1283faadfb32b5bde1b0bb2dd547ea2db3f7080d96359b3d8f62b1fd58853add1b38e6dd051c79bcf9551ebcb46a5f8cae6d7d7c9f2a206c8d8951dc73804a5c52f7576c2afde01bf8705ebbe4be64fbc545819baa8a17cb96ec08eb837fe7bb59a84ddb3feb3ca
  | 9, 0 => 0xf2854adfc2afde01a6563cc3a1f16def9b34b1217e1a8a567cea112d76f0de33764e5f61705b5d9f5fbac6fd5e22a7545cde0cce51bb2a0f5059633d4aee737942b779a33e277fff34064f6c2efbd96421b9f7ae1b78d4bc1561a43a0e7e151305169eb0
  | 10, 0 => 0x42b779a3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x333300003333000000000000000000000000000000000000000000000000000011110000ffff00000000000000000000000000000000000000000000000000000000ffffffff00000000000000000000000000000000000000000000000000000000eeeeeeee000000000000000000000000000000000000000000000000000000007777777700000000000000000000000000000000000000000000000000000000555555550000000000000000000000000000000000000000000000000000000033333333000000000000000000000000000000000000000000000000000000000000ffff
  | 0, 1 => 0x55505550555055500000000000000000000000000000000000000000000000003ff03ff03ff03ff000000000000000000000000000000000000000000000000033f033f033f033f000000000000000000000000000000000000000000000000033303330333033300000000000000000000000000000000000000000000000000ff00ff00ff00ff0000000000000000000000000000000000000000000000000000ffff0000ffff00000000000000000000000000000000000000000000000000007777000077770000000000000000000000000000000000000000000000000000555500005555
  | 0, 2 => 0x1133113311331133000000000000000000000000000000000000000000000000111111111111ffff000000000000000000000000000000000000000000000000111111111111333300000000000000000000000000000000000000000000000011111111111111110000000000000000000000000000000000000000000000000fff0fff0fff0fff0000000000000000000000000000000000000000000000000ff00ff00ff00ff00000000000000000000000000000000000000000000000000f3f0f3f0f3f0f3f0000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f
  | 0, 3 => 0x33333333222222220000000000000000000000000000000000000000000000003333222233332222000000000000000000000000000000000000000000000000330033003300330000000000000000000000000000000000000000000000000030f030f030f030f00000000000000000000000000000000000000000000000003030303030303030000000000000000000000000000000000000000000000000300030003000300000000000000000000000000000000000000000000000000022222222222222220000000000000000000000000000000000000000000000001155115511551155
  | 0, 4 => 0x3f003f003f003f000000000000000000000000000000000000000000000000003c3c3c3c3c3c3c3c000000000000000000000000000000000000000000000000333333333333ffff000000000000000000000000000000000000000000000000333333333333cccc0000000000000000000000000000000000000000000000003333333333337777000000000000000000000000000000000000000000000000333333333333333300000000000000000000000000000000000000000000000033333333333322220000000000000000000000000000000000000000000000003333333333330000
  | 0, 5 => 0x55445544554455440000000000000000000000000000000000000000000000005500550055005500000000000000000000000000000000000000000000000000545454545454545400000000000000000000000000000000000000000000000050505050505050500000000000000000000000000000000000000000000000005000500050005000000000000000000000000000000000000000000000000000444444444444444400000000000000000000000000000000000000000000000044004400440044000000000000000000000000000000000000000000000000003f3f3f3f3f3f3f3f
  | 0, 6 => 0xa0a0a0a0a0a0a0a000000000000000000000000000000000000000000000000099999999999999990000000000000000000000000000000000000000000000008f8f8f8f8f8f8f8f00000000000000000000000000000000000000000000000088888888888888880000000000000000000000000000000000000000000000005555555555555555000000000000000000000000000000000000000000000000555550505555505000000000000000000000000000000000000000000000000055554444555544440000000000000000000000000000000000000000000000005550555055505550
  | 0, 7 => 0xbbbbbbbbbbbb3333000000000000000000000000000000000000000000000000afafafafafafafaf000000000000000000000000000000000000000000000000aaffaaffaaffaaff000000000000000000000000000000000000000000000000aaaabbbbaaaabbbb000000000000000000000000000000000000000000000000aaaaaaaaaaaaaaaa000000000000000000000000000000000000000000000000aaaaaaaaaaaa0000000000000000000000000000000000000000000000000000aaaa8888aaaa8888000000000000000000000000000000000000000000000000aa00aa00aa00aa00
  | 0, 8 => 0xccc0ccc0ccc0ccc0000000000000000000000000000000000000000000000000cc88cc88cc88cc88000000000000000000000000000000000000000000000000cc00cc00cc00cc00000000000000000000000000000000000000000000000000c8c8c8c8c8c8c8c8000000000000000000000000000000000000000000000000c0ffc0ffc0ffc0ff000000000000000000000000000000000000000000000000c0c0c0c0c0c0c0c0000000000000000000000000000000000000000000000000c000c000c000c000000000000000000000000000000000000000000000000000bbbbbbbbbbbbbbbb
  | 0, 9 => 0xcccccccccccc8888000000000000000000000000000000000000000000000000cccccccccccc0000000000000000000000000000000000000000000000000000cccccccccc00cc00000000000000000000000000000000000000000000000000ccccccccc0c0c0c0000000000000000000000000000000000000000000000000cccccccc88888888000000000000000000000000000000000000000000000000cccccc00cccccc00000000000000000000000000000000000000000000000000ccccc0c0ccccc0c0000000000000000000000000000000000000000000000000cccc8888cccc8888
  | 0, 10 => 0xddccddccddccddcc000000000000000000000000000000000000000000000000cfcfcfcfcfcfcfcf000000000000000000000000000000000000000000000000cf0fcf0fcf0fcf0f000000000000000000000000000000000000000000000000ccffccffccffccff000000000000000000000000000000000000000000000000ccccddddccccdddd000000000000000000000000000000000000000000000000ccccccccccccffff000000000000000000000000000000000000000000000000cccccccccccccccc000000000000000000000000000000000000000000000000cccccccccccccc00
  | 0, 11 => 0xeecceecceecceecc000000000000000000000000000000000000000000000000eeaaeeaaeeaaeeaa000000000000000000000000000000000000000000000000ee00ee00ee00ee00000000000000000000000000000000000000000000000000ecececececececec000000000000000000000000000000000000000000000000eca0eca0eca0eca0000000000000000000000000000000000000000000000000eaeaeaeaeaeaeaea000000000000000000000000000000000000000000000000eaaaeaaaeaaaeaaa000000000000000000000000000000000000000000000000e0e0e0e0e0e0e0e0
  | 0, 12 => 0xeeeeeeeeeeeeaaaa000000000000000000000000000000000000000000000000eeeeeeeeeeee0000000000000000000000000000000000000000000000000000eeeeeeeeeeaaeeaa000000000000000000000000000000000000000000000000eeeeeeee00000000000000000000000000000000000000000000000000000000eeeeeeaaeeeeeeaa000000000000000000000000000000000000000000000000eeeaeeeaeeeaeeea000000000000000000000000000000000000000000000000eeeaeeeaeeea0000000000000000000000000000000000000000000000000000eee0eee0eee0eee0
  | 0, 13 => 0xf0f0c0c0f0f0c0c0000000000000000000000000000000000000000000000000f0f0a0a0f0f0a0a0000000000000000000000000000000000000000000000000f0e0f0e0f0e0f0e0000000000000000000000000000000000000000000000000f0c0f0c0f0c0f0c0000000000000000000000000000000000000000000000000f0a0f0a0f0a0f0a0000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000eeeeeeeeeeeeeeee000000000000000000000000000000000000000000000000eeeeeeeeeeeecccc
  | 0, 14 => 0xf0f0f0f0f0f0a0a0000000000000000000000000000000000000000000000000f0f0f0f0f0f03030000000000000000000000000000000000000000000000000f0f0f0f0f0f00000000000000000000000000000000000000000000000000000f0f0f0f0f000f000000000000000000000000000000000000000000000000000f0f0f0f0c0c0c0c0000000000000000000000000000000000000000000000000f0f0f0f0a0a0a0a0000000000000000000000000000000000000000000000000f0f0f000f0f0f000000000000000000000000000000000000000000000000000f0f0e0e0f0f0e0e0
  | 0, 15 => 0xfa00fa00fa00fa00000000000000000000000000000000000000000000000000f8f8f8f8f8f8f8f8000000000000000000000000000000000000000000000000f888f888f888f888000000000000000000000000000000000000000000000000f3f3f3f3f3f3f3f3000000000000000000000000000000000000000000000000f0fff0fff0fff0ff000000000000000000000000000000000000000000000000f0f0f0f0f0f0ffff000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000000f0f0f0f0f0f0f000
  | 1, 0 => 0xfafafafafafafafa000000000000000000000000000000000000000000000000fafafafafafaf0f0000000000000000000000000000000000000000000000000fafafafafafa0000000000000000000000000000000000000000000000000000fafafafac8c8c8c8000000000000000000000000000000000000000000000000fafafaaafafafaaa000000000000000000000000000000000000000000000000fafaf8f8fafaf8f8000000000000000000000000000000000000000000000000faeafaeafaeafaea000000000000000000000000000000000000000000000000faaafaaafaaafaaa
  | 1, 1 => 0xfcfcececfcfcecec000000000000000000000000000000000000000000000000fcfca8a8fcfca8a8000000000000000000000000000000000000000000000000fcf0fcf0fcf0fcf0000000000000000000000000000000000000000000000000fcccfcccfcccfccc000000000000000000000000000000000000000000000000fccca888fccca888000000000000000000000000000000000000000000000000fcc0fcc0fcc0fcc0000000000000000000000000000000000000000000000000fca8fca8fca8fca8000000000000000000000000000000000000000000000000fc00fc00fc00fc00
  | 1, 2 => 0xfeccfeccfeccfecc000000000000000000000000000000000000000000000000feaafeaafeaafeaa000000000000000000000000000000000000000000000000fe00fe00fe00fe00000000000000000000000000000000000000000000000000fcfcfcfcfcfcfcfc000000000000000000000000000000000000000000000000fcfcfcfcfcfca8a8000000000000000000000000000000000000000000000000fcfcfcfcfcfc0000000000000000000000000000000000000000000000000000fcfcfcfcecececec000000000000000000000000000000000000000000000000fcfcfcccfcfcfccc
  | 1, 3 => 0xff00ff00aa00aa00000000000000000000000000000000000000000000000000ff00f000ff00f000000000000000000000000000000000000000000000000000ff00ee00ff00ee00000000000000000000000000000000000000000000000000ff00cc00ff00cc00000000000000000000000000000000000000000000000000ff00aa00ff00aa00000000000000000000000000000000000000000000000000ff008800ff008800000000000000000000000000000000000000000000000000fefefefefefefefe000000000000000000000000000000000000000000000000feeefeeefeeefeee
  | 1, 4 => 0xff33ff33ff33ff33000000000000000000000000000000000000000000000000ff0fff0fff0fff0f000000000000000000000000000000000000000000000000ff00ff00ff00ff00000000000000000000000000000000000000000000000000ff00ff00ff00f000000000000000000000000000000000000000000000000000ff00ff00ff00aa00000000000000000000000000000000000000000000000000ff00ff00ff000000000000000000000000000000000000000000000000000000ff00ff00f000f000000000000000000000000000000000000000000000000000ff00ff00cc00cc00
  | 1, 5 => 0xffaaffaaffaaff00000000000000000000000000000000000000000000000000ffaaffaaffaaaaaa000000000000000000000000000000000000000000000000ffaaffaaffaa0000000000000000000000000000000000000000000000000000ffaaffaafaaafaaa000000000000000000000000000000000000000000000000ffaaffaaeeaaeeaa000000000000000000000000000000000000000000000000ffaaeeaaffaaeeaa000000000000000000000000000000000000000000000000ffaacc88ffaacc88000000000000000000000000000000000000000000000000ff88ff88ff88ff88
  | 1, 6 => 0xfff0ccc0fff0ccc0000000000000000000000000000000000000000000000000fff0aaa0fff0aaa0000000000000000000000000000000000000000000000000ffeeffeeffeeffee000000000000000000000000000000000000000000000000ffccffccffccffcc000000000000000000000000000000000000000000000000ffccffccffcccccc000000000000000000000000000000000000000000000000ffccffccfcccfccc000000000000000000000000000000000000000000000000ffc0ffc0ffc0ffc0000000000000000000000000000000000000000000000000ffaaffaaffaaffaa
  | 1, 7 => 0xffff3333ffff3333000000000000000000000000000000000000000000000000ffff2222ffff2222000000000000000000000000000000000000000000000000ffff0f0fffff0f0f000000000000000000000000000000000000000000000000ffff00ffffff00ff000000000000000000000000000000000000000000000000ffff0000ffff0000000000000000000000000000000000000000000000000000fff0fff0fff0fff0000000000000000000000000000000000000000000000000fff0fff0fff00000000000000000000000000000000000000000000000000000fff0fff0ccc0ccc0
  | 1, 8 => 0xffffcc00ffffcc00000000000000000000000000000000000000000000000000ffffc0c0ffffc0c0000000000000000000000000000000000000000000000000ffffaaaaffffaaaa000000000000000000000000000000000000000000000000ffffaa00ffffaa00000000000000000000000000000000000000000000000000ffffa0a0ffffa0a0000000000000000000000000000000000000000000000000ffff8888ffff8888000000000000000000000000000000000000000000000000ffff5500ffff5500000000000000000000000000000000000000000000000000ffff4444ffff4444
  | 1, 9 => 0xfffff0f0fffff0f0000000000000000000000000000000000000000000000000fffff000fffff000000000000000000000000000000000000000000000000000ffffeeeeffffeeee000000000000000000000000000000000000000000000000ffffeeeeffffcccc000000000000000000000000000000000000000000000000ffffeeeeffff0000000000000000000000000000000000000000000000000000ffffccccffffcccc000000000000000000000000000000000000000000000000ffffccccffff8888000000000000000000000000000000000000000000000000ffffccccffff0000
  | 1, 10 => 0xffffffff33333333000000000000000000000000000000000000000000000000ffffffff30003000000000000000000000000000000000000000000000000000ffffffff22222222000000000000000000000000000000000000000000000000ffffffff11111111000000000000000000000000000000000000000000000000ffffffff0f0f0f0f000000000000000000000000000000000000000000000000ffffffff00ff00ff000000000000000000000000000000000000000000000000ffffffff00000000000000000000000000000000000000000000000000000000ffffff00ffffff00
  | 1, 11 => 0xffffffffcccc8888000000000000000000000000000000000000000000000000ffffffffcc00cc00000000000000000000000000000000000000000000000000ffffffffc0c0c0c0000000000000000000000000000000000000000000000000ffffffffaaaaaaaa000000000000000000000000000000000000000000000000ffffffffaa00aa00000000000000000000000000000000000000000000000000ffffffffa0a0a0a0000000000000000000000000000000000000000000000000ffffffff99999999000000000000000000000000000000000000000000000000ffffffff88888888
  | 1, 12 => 0xffffffffffff8888000000000000000000000000000000000000000000000000ffffffffffff3333000000000000000000000000000000000000000000000000ffffffffffff0000000000000000000000000000000000000000000000000000ffffffffff00ff00000000000000000000000000000000000000000000000000fffffffff0f0f0f0000000000000000000000000000000000000000000000000fffffffff000f000000000000000000000000000000000000000000000000000ffffffffeeeeeeee000000000000000000000000000000000000000000000000ffffffffcccccccc
  | 1, 13 => 0xffffffffffffff00000000000000000000000000000000000000000000000000fffffffffffff0f0000000000000000000000000000000000000000000000000ffffffffffffcccc000000000000000000000000000000000000000000000000ffffffffffffaaaa
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 1, 0, 0 => 0x8b612
  | 2, 0, 0 => 0xe58b623c58c613
  | 3, 0, 0 => 0xd1bb8b624e5c58c624bb8c613b4c56a61514e58b473b4
  | 4, 0, 0 => 0xe5bb8c623b5e5c56a62515bb6a61513b5d1caba8b3b500e5b78c3b400cba579364d1bb8b473b5d1cac56a625e5c58c473b5c5a57961515009d7966344e5ba8b513b500e5ca8a3b4d1c5bb8c625
  | 5, 0, 0 => 0xe5ca6c453b500e5caba8c3b5bba57961513b6e5c5ba8c513b600caa579673a500a579693406500d1bb8c603b500cda5796634500bba5796436500bba5793605500d1bb513b0d500e59d793b22500e5cab48d3b500d4bba57936500d1bb8c623b500d18c473b0a5
  | 5, 0, 1 => 0xd1caa58b793b6d1bb8c885a3b600e5b76a513b500e5886f513b500d9bba57936500caa5793b165d1c5bb8c473b600ca79663b0b500e5bba579365d1bbba8b513b600d1cabb8a3b500bba5793b245d1cabb6a623b600e5a5705133500d1bba533265e5c5a57962516
  | 5, 0, 2 => 0xd1cac5a579626e5bb6a62513b6d1cac5ba8c3b600cca579663b500d1bb8a5133500bb8c473b055d1bb8c6a623b600bb8a513b05500cba5693410500a57066513b500e5a5706934500d1a579360a500caa5796633500d1bba53610500d1bb5133125d1cac56a473b6
  | 5, 0, 3 => 0xe5ca6a473b500cba5793414500d18a513b0a5e5c56a51473b6e5a58b79513b600a579663b07500d1bb3b22125d1c5bb6a6251600e5bb8c473b500e5bb8a513b500d1bb473b0c500d1bb8c4733500d1bbb78c3b5
  | 6, 0, 0 => 0xd1bbb48d693b600d17969340b0a600e5c379513b0b600e5bbba6a3b22600bba5332210056d1bba58b79513b700a56c513b0a05600bbb079382205600d7bba5793b20600d1bb6934100b600e5a58e79513b600e5bba4793b22600d1bb88513b2c600eabb75513b0b600d1a8793b220a600e579513b0b076
  | 6, 0, 1 => 0xd1cabb6a473b600e5a59c793b22600c5a5793b2200600d1caa579673b600bbb194513b05600d4bba5513b10600bbb179513b00600d1bba53b2211600d8a5793b220a600e5bca5793b226d1c5bb6a51473b700e5c5a5793a22600a58751370a05600d1bba5795136600a57933220a05600e5caa5793b146
  | 6, 0, 2 => 0xd1bb9558513b600bba56c3b2205600d1a58d3b220a600d17e513b0b0a6e9bba5796a4e3b700e5c5a58d513b600cba579695133600e5c679513b0b600d1bbba513313600d194423b0b0a600e5ca79693b0b600e0d1bb6a473b600d1bb9d796934600e5bba5944233600bba579665133600c2a5513b10056
  | 6, 0, 3 => 0xbb8879513b00600e9bb794e3b0b600c2a5793b2205600d1a56c51330a600e5bbb0513810600bb513b100b00600e5caa55133106e5dcbba56c513b700d4bba5793b22600e5cab0795138600ca79513b0b006e5bba59379513b700d1bb3b22100b600cba579695134600bba57c3b1b05600d1bba551331c6
  | 6, 0, 4 => 0xe5bba57962513b700e5caa586513b600bba569643410600d1bbb1945a3b600e5a5876e513b600bba5513b1004600e5a579513331600a57969340a05600d1bbb1945133600e7a59a79513b600d1bbba8c693b600d1bb8d51330b600bba569341005600e5c4a5793b22600d1bb9d793b22600d1cabbb48d3b6
  | 6, 0, 5 => 0xa594423b0a056e5d1caa58c793b700e5a59b7951336e5a5796e514e3b700e5bba5763b22600e3bba5753b22600e5a5796f5133600bb8851423b05600d1bb6c5e513b600a5796964340a600e5caa56c513b600e5ca794e3b0b600e5caa5793b20600bbba6a513b00600ebbba2793b22600d1bb7951330e6
  | 6, 0, 6 => 0xe5bc7951330b600d13b22100b0a600e5bba5332210600e5bb77513b0b600e5a58f79513b600e5c5513b100b600a57e513b0a05600e5bbb0793822600a59c79513b00600d1bba57c331b600bb793b220b00600e5caa5793322600e5bea5793b22600bba579684e3b600d1bba56c3322600e5c7a5793b226
  | 6, 0, 7 => 0xe5bba5863b22600d1bb8858513b6e5d1a58e79513b7d1c5bbba8c513b700e5a579513307600d1bb8c8a513b600caa5794e3b3a600bba5793b2204600e5c2a5513b10600e5a9a579513b6ebbba29479513b700e5bbb194513b600d188793b220a600d1bb8c88423b600d1a7793b1d0a600e5c58879513b6
  | 6, 0, 8 => 0xd1bba5705133600e5bb8875513b600e5c5793b220b600e5bba57c3b1b600bba58d513305600bbb4453b1005600bba57e3b2205600e5bba56c3b22600d1ba6a3b220a600e0d1bb6c453b600bba5513b10036d1c5bba5796251700d1bbb86a513b600d1cabb6c453b600e5c5ba6a513b600d1cabbba8c3b6
  | 6, 0, 9 => 0xd1bba5555133600e5ba9b79513b600e5caa5796934600e5bba3793b22600e5cca579683b600e5c2a5793b22600e7c2a5513b10600d1bba5796936600e7bba5513b10600d1a5513b1009600e5c6a5795133600e5a5796e3b22600d1a59442330a600e5caa5796933600e5bda5795133600d1bb885142336
  | 6, 0, 10 => 0xbba579696634600e5caa594423b600caa57966513b600d1bba5423b0c600caa579513300600d1bba58c4233600d1bb8a6a513b600e5a57069513b600e5bba5683b10600a53b22100a05600bba5793b2203600e5bba5793b21600d1bba5332210600e5a579513c3b600e5caa579683b600e5bba56934106
  | 6, 0, 11 => 0xd1bbb4453310600cba569513b10600e5cd79513b0b6e5bba39479513b700d1b05138100a60000d1bba57936500e5bb8851423b600e5caa57e513b600bba57968663b600e5bba54f3b10600e5c5a5795e51600bba579401905600e5a579513b31600bba566513b10600bba551331000600bb6a51473b056
  | 6, 0, 12 => 0xbb8879513305600e5c579513a0b600e5a579513b1e6007951330b0a05600e5caa5794e33600d1bb8875513b600e5aaa579513b600d8bb513b100b600bb5133100b0560000e5a570513b500d1bb8c6a473b600e7c2a5793b22600cbbba5796934600e7bba5793b22600d1a5793b220960000d1bba53b265
  | 6, 0, 13 => 0xd1a53322100a600e5caa579473b600d1bbba3b2213600d1bb7934140b600d1b07938220a600d1bba3793b22600e5c5a55133106d1cac5ba6a513b700bba579663b226e5c5a57951473b700bba579332200600d1bbb0382210600d1bb886f513b600c579513b0b0060000cba5796934500d879513b0b0a6
  | 6, 0, 14 => 0xd1bb8873513b600e5a59b513b10600bb8751370b05600d1bb6a513330600e5bbaf513b10600d1b194513b0a600d1bba5793b21600d1bb6a514733600d1bbb76a513b600bbba6a513305600e5bba58d5133600e5bbb4453b10600cba579693b226d1cac5a58c793b700e5bba57e3b22600a5796e513b006
  | 6, 0, 15 => 0xbba579341405600d4bba5793414600cba57966513b600e5bba5793b23600bbba8c513b05600e5bba5794019600d1caa5794e33600e5bb6a51473b600d1caa5794833600d1bb8a6c513b600e8bba5513a10600d1bb51453b11600e5c5a5793322600e5a5513b1008600e5caa53b2210600bba8513b10056
  | 6, 1, 0 => 0xcaa57969663b600e5caa579332a600e5cda5795133600d18851423b0a600e5caa5795f3b600e5bb88795133600bba579643414600e5bc793b220b600e8bba5793a22600e5a5793b221e600e5a5793b2208600e5caa582513b600d1bb6c51332e600e5bb5133100b600a58d513b0a05600bba594423b006
  | 6, 1, 1 => 0xbba57967513a600d1a58d51330a600e5bba8513b10600d1bb6a513b30600e6bba5793b206d1cabba579623b70000caa579663b500d1bbba513b0c600e5c5a594423b600c5a57966513b60000d1bb513b12500d1bbba8c5133600cbcaa579693b600bba58d3b2205600e5bbba6a5133600cccba579693b6
  | 6, 1, 2 => 0xd1bbb08c79693b700d16a51473b0a600ba6a513b0a05600e5caa5796939600d1bbb1944233600d1bba58d3322600e5bba5793414600e5caa58d513b600bc79513b0b00600d1bba58c5a3b600e5bbba8c513b600caa5793b2200600513b100b0a05600e5bba5793f3b600e5a579693b07600d1bb5133100b6
  | 6, 1, 3 => 0xbba579513b1660000d1bb8a513b500d1bba5793614600bbba6a3b2205600e5bba58d3b22600e5b49c79513b600d15133100b0a600caa579693b00600e5caa5793b2a600c5a579514e3a600d1bb6a62513b600cba579513b14600e5caa579403b600d1a57940190a600e5caa579663b600bb3b22100b056
  | 6, 1, 4 => 0xd4bba5793322600e5cda5796934600d1bb3322100b60000d1bb8c473b500d1bb886c513b600e9bba5793b25600e5ca513b100b600d1ba6a51330a6e5dcbbba6a513b700d1bb6a60513b600d6bba5793b22600bba594423305600e5bbb96a513b600e5b7a579513b600d1bba5943328600e5c0a57951336
  | 6, 1, 5 => 0xe5bb3b22100b600d1bb51473b13600a57969513b06600e5caa58c793b600d1bbba6a33226d1cac5a579473b700cda57966513b600e5a57953513b6e5c5a58c79513b700e5caba6a513b600e5caa5793b25600d1c2513b100b6e5bba58c794e3b700e5bba5793b15600e5caa579673b600d1caa579663b6
  | 6, 1, 6 => 0xd1a57934140a600e5c5a5807951600e5b6a579513b600e5cda5793b22600d1bbb96a513b600d1ba8c513b0a6
  | 7, 0, 0 => 0xd1bba5796e5133700bba57951332a05700e1d1bb79513b0b700dcd1bbba6a513b700e5bba579514b3b700d1cdbba5513b10700d1bba551332210700d1cfbb7951330b70000e3bba575513b600d1bbb09e79513b700a57969513b0a05700e5bba59279513b700d1bba579513328700bba57969513b04700d1bba551332e10700bba57951483b057
  | 7, 0, 1 => 0xe5bba579514d3b700d3d1bba53b221070000e5caa5795133600d1bba58d5e513b700bba56964513b10700e5d1ca79513b0b700d1bba57d79513b700e6e5bba5793b22700d1a5795133220a70000d1bba56c5133600e5bba57951503b700d1a57951332e0a70000e5c7a579513b6e5d1c5b4a579513b800d1bba55651331070000d1bbb48d453b6
  | 7, 0, 2 => 0xe5d1bb513b100b7d1c5bba58c79513b800d1cabbba6a513b700d1bba579332c22700d1bba579743b22700d1bbada579513b700e5bba57951473b700d1bba579545133700d1bba579695d34700bba5795142330570000e5bbb0795138600d1bba5513b1d10700d1bbaca579513b700e5bbb47951453b70000d1bbb1793b2260000bb79513b0b006
  | 7, 0, 3 => 0xe5d1bb8879513b700d1bba579513b2f700e5c5a5796a513b700d1cabba58c793b700d1bba56a3b221070000bba579693405600e5bb79513b370b70000d1513b100b0a600e5bba5793b3a22700e0d1bbba6a513b700d1bba579723b22700d1bba55d513b10700d1bba57953513b700dcd1bb793b220b700a5796964513b0a70000e5bba55133106
  | 7, 0, 4 => 0xd1bba579332210700e0d1bb793b220b700e3d1a5793b220a700d1bbb4a279513b700d1bcbba5513b1070000d1c9a579513b60000d1bba5943b28600e5caa5a279513b700d1a5796a3b220a700d1cabb793b220b700d1bb795e513b0b70000d18879513b0a600e5bbb0a5795133700bba579453b2205700e5caa579513b10700d1bbb179513b337
  | 7, 0, 5 => 0xe5bba587793b22700d1bbaba579513b700d1bbb479513b2e700bba579693b220570000bba579696434600d1bba579513329700d1bba59779513b700d1bb79513b0b08700e5bba5a2513b10700e5bbaea579513b700d1bba59473513b700e5bba5513b100b700e5c8a579514e3b700d1bba5793b222070000bba579513b04600d1bbb08879513b7
  | 7, 0, 6 => 0xd1bba587513b1370000bba57e513b05600d1c5bba580795170000e5bba56c513b60000d1ba6a513b0a600d1bbb6a579513b700d8d1bba5513b10700d1cdbba5793b22700e5d1bbba6a513b700d1bba551453310700e5bba5513b221070000e5bba586513b600ded1bba5513b1070000e5bba578513b60000bba594423b05600e5caa579513b227
  | 7, 0, 7 => 0xd1bba5795d3b2270000e5bba5793322600d1bba58e79513b700e5d1bb793b220b700cabba5513b1005700d1bba59879513b70000e5c579513b0b600d1bba569513310700d1bba579514a3370000d1bb3b22100b600bba5795c513b05700d1bba5513e3310700d1bb79513b0b07700bba57969643b22700d1bba579585133700d1a5795145330a7
  | 7, 0, 8 => 0xd1bba579514e33700d1cabba5793b14700e3d1bb7951330b700d1bba5a1795133700d1c3bb79513b0b700d1bba5796c3b22700d1bba56a514233700d1bb796a51330b700c5bba579513305700dcd1bba5795e5170000d1bb88793b22600d1a5796951330a70000d1793b220b0a60000d1bba7793b1d600d1bba579514833700bba57a79513b007
  | 7, 0, 9 => 0xe5c2a579513b600e5bba5793b2210700cfbba579513305700d1bb796a51332e700d1bba59279513b700d1bbb5795d513b700d1bcbba5793b22700e5bbbaa5795133700d1cebba5793b22700e5bb79513b0b00700d1bb513b33100b700e0d1bba5793b14700d1bbb2a579513b700d1bba58079513b700e5bba57975513370000e5a5796e513b6
  | 7, 0, 10 => 0xded1bba5793b22700e0d1bb79693b0b700d2d1bb513b100b700e4d1a57951330a700d1bb513b34100b700d1bba59679513b700d1cabb79693b0b700e5caa57951453b700d1bba59c793b22700d1bb8879513b33700d1bba58979513b700e5bba5a2793b2270000d1bb7951433b600d179513b330b0a70000e5bba379513b600d1a5796951340a7
  | 7, 0, 11 => 0xd1bfbba579513370000a5513b100a05600d8d1bba5793b2270000bba579513b03600d1c5bba58d513b700d179513b340b0a700d1bba56c69513b700e5bbb4a579513370000d1bb79513b2760000d1bba5513310600d1bba579453322700e5bba551453b10700d1c6bb79513b0b700d1bba57971513370000d1bbba6a3b22600d1bba58379513b7
  | 7, 0, 12 => 0xb0a579513b0a05700bba57951463b05700d1bbba6a513b33700cabba5793b2205700d1bbb0a179513b700bba5795e513b05700d1bba579693322700e5bba569513b10700d1bba579513b30700bbb0a5513b1005700d1a59451423b0a700d19479513b0b0a700d1bbb48879513b700d1c2a59a79513b700e5caa57969513b700d1bb793b221b0b7
  | 7, 0, 13 => 0xd1a57951443b0a70000d1a579513b09600d1bb793b33220b700dcd1a57951330a700bba5796966513b7e5bba5a29479513b800d1bba57963513b700e5e3bb79513b0b700e5bba57951332a700d1bbaea579513b700dcd1bba5513310700d1bba5a0793b22700bba57951403b05700d1bba5513b100170000d1bba5944233600e5bba5795f513b7
  | 7, 0, 14 => 0xd1cac5a5796a513b800d1bba57951331b700bba58779513b00700e0dcbba5513b10700e0d1bba5513310700e4d1bba5793322700d1bb8c79513b0b700d17951423b0b0a700d1a5793b221d0a700d1cabba5513310700bba579513b2a0570000e7c2a579513b600e5bba57951423370000e7bba579513b600d1cabbb0795138700d1bba5513b2e107
  | 7, 0, 15 => 0xa5793b220a05600d1a58079513b0a700cbbba57969513b70000d1bba5793322600d1bb94793b220b700e5bba579453b22700d1c4bba5793b22700d1bba579513b0f700bfbba5793b2205700d1bba5793b2c22700d1bba5793b2213700d1d0bba53b2210700e0d1a57951330a70000bba53b221005600d1bba580513b1070000e5bba57969346
  | 7, 1, 0 => 0xd1bbb0513810600d1bba579755133700bba5513b331005700e5bba579693b22700d1bba5876e513b700d1bb793b22190b700dcd1bba56c513b700d1a579514b3b0a700bba7a5793b2205700d8bba5796a513b700bbb0a5793b2205700d1bba579513331700e5bbb3a579513b700bba5796a513305700e9bba579514e3b70000e5bba579683b6
  | 7, 1, 1 => 0xdcd1bba5793322700e5dcbba5513b10700e5d1bba551331070000d1b07951380a60000d1bba379513b600a579513b330a0570000e5bba5794f3b600baa579513b0a05700d1a579514d3b0a70000e5bba594423b60000bba57966513b600eae5bba5793b22700d1bba5945a513b70000bba579513300600d1bb79513b0b00700e5d1caa57951337
  | 7, 1, 2 => 0xd1bbb0a5513310700d1c7bba5793b22700d179513b370b0a700bba5513b341005700e0d1bba56c513b700d7d1bba5793322700cabba579693b0570000cba57969513b60000e5bba57e513b600d1bba5796f513370000d1a55133100a600d1cabba56c513b70000d1bbba513b13600d1bba5a2793b22700d1bba56d69513b700d1a57951473b0a7
  | 7, 1, 3 => 0xe5e0bba5513b10700e5e4bba5793b22700d1bba579513b17700bba5793b221b05700d1b0a57951330a70000e0bba5794b3b600bba5a279513b00700d1bba579514633700d1cabba5793322700a579513b340a05700e5caa579514e3b700d1bba5795e5133700d1bebba5793b22700d1cac579513b0b700bba579513b1000700bbb4a5513b10057
  | 7, 1, 4 => 0xd1bba580793b2270000bb7951330b05600bbb0796a513b05700cabba57969643b700d1a5513b100b0a700e5c5a58779513b700d1bb795a513b0b700d1bba57962513b700e5bba5514e3b10700d1bba579514033700d1bb79513b140b700d1bba58f79513b700d1c5bb513b100b700e0dcbba5793b22700e0d1bba5793322700b4a579513b0a057
  | 7, 1, 5 => 0xbba5793b332205700d1bba59e793b22700bbbaa5793b2205700d1c2bba5513b10700d1bba9a579513b70000e5caa5513b10600d1a5513b22100a700d1d0bb7951332e7eae5bbb4a579513b800d1a587793b220a700e8e5bba5513b10700d1c5bb8879513b70000d8bb79513b0b600d1bcbb7951330b700bba579513b2200700d1bba569513b107
  | 7, 1, 6 => 0xd1bfbba5793322700a57951423b0a05700d1bba579735133700d1bba6a53b221070000e5c5a5795133600e5d1c579513b0b70000d1bba5332210600d1bba579514233700d1bba58758513b700d1bb8c8879513b700d1bba579513307700dad1bb79513b0b700d1bba59469423b70000d1bbb0793822600d1bba554513b10700bb79513b100b057
  | 7, 1, 7 => 0xd1bbb194513b600d1bbb0a5793322700e5bbb0a5513b10700bb79513b220b05700bba5793b3422057e5e4bba59479513b800e5d7bba5793b22700e5bbb9a579513b70000d1bb8d513b0b60000d1a57933220a600d1c5bbba6a513b700e5cab0a579513b700d1bb793b37220b700bba58c79513b05700e5dcbba5793b22700e5d1bba57933227
  | 7, 1, 8 => 0xd1bb7b7951330b700bba579403b2205700d1bba53b22100b700d1bba57969443b7e5dcbbbaa579513b800e5bba57966513b700e5c5a579513b1070000d1c2a5513b10600d1bba59451332c700e5bba57951463b700e5bba5795e513b700d1bba57965513b700d1bba57960513b700d1bba7a5793322700d1bb876a513b0b700bbb4a5793b22057
  | 7, 1, 9 => 0xbba57951453b00700d1bba579693b22700d1bba5793e3b22700bba5793b221905700d1bba59079513b700d1a5793b22100a70000d1bb79513b0e600d1bbb3a579513b700e5bba5794e3b22700e5bba57951403b700d1bbba8c6a513b700d1bba5796b5133700d1baa57951330a700e5c5a5a279513b700d1c5bb793b220b700e5e0bba5793b227
  | 7, 1, 10 => 0xd1b4a57951330a70000e5caa5793b22600d1bba57933221b700e5bba579513b2a7e5dcbbb4a579513b800d1c6bba579513370000d1bba5794f3b600d1bba5796e3b22700d1bbb4a5513310700d1bbb094795138700e5c5a579513b22700e9e5bba5513b10700e8e5bba5793b2270000e5a5796f513b600d1cabba5796933700d1bdbba57951337
  | 7, 1, 11 => 0xdcd1bba594423b70000e8bba579513a600d1a569513b100a700d1bbba9b79513b700d4bba579513b14700e5bb79513b3a0b700d1bba55f513b1070000e5a579513b08600d1bba5793b221f70000e5bba53b2210600d1bbb0796a5133700dbd1bba5793b22700d1cabba5796934700a579513b370a05700bba57969513b00700d1c2bba5793b227
  | 7, 1, 12 => 0xd1bb795133100b700e5bba5513b3310700e3d179513b0b0a700d1bbbaa5793322700d1a57951332a0a700e5bba7a5793b22700d1bba57069513b700e5bba5796a5133700e5caa579513b33700d1a5795f513b0a700e5cabaa579513b700d1bba551332a10700d1bba579513c3b700bba579513b1405700c5bba5513b100570000e5bc79513b0b6
  | 7, 1, 13 => 0xe5caa579513b34700d1bba579513b31700bba57964513b14700bb7969513b0b0570000eabba575513b600e0d1bba594423b700d1bb513d3b100b70000e5a579513b07600d1bb793b38220b700d1cabba594423b7e8e5bbb4a579513b80000d1c2a5793b22600e8d1bba5513b10700e5caa5796f513b70000dfbba579513b600d1bba5514233107
  | 7, 1, 14 => 0xbba5793b37220570000d1a57969340a60000e5c3a579513b600d1bba579575133700d1bbb4a5793322700e5bbb4a5513b10700e5c5a57951453b700e9e5bba5793b22700e5bba5513b3410700d1bb7951332e0b700d1bba579513b0c700d1cabba57e513b70000d1bba5693410600e5cab4a579513b700d1c5bba5795e51700d1bba58c7951337
  | 7, 1, 15 => 0xd1bba57966513b700bba5513b381005700d1bba5795e513b700d1bba5795f3b2270000d1bba570513b600e5bbb0796a513b700e5c5a57969513b700d1bba5693b2210700d1bba53e3b221070000e0bba5794e3b600d1bbb9a579513b700e5bba5793b221b700d1bba57940332270000bba58d513b05600e2d1bba5793b22700d1a579453b220a7
  | 7, 2, 0 => 0xd1bba58d514533700d1bba5513b1002700e3d1bb793b220b700bba58779513305700d1bba57951333270000d1a594423b0a600d1bbaaa579513b700d1bba579332a2270000e5caa579693b600c5bba5793b220570000e5bda579513b60000d1bb8851423b600e5d1bba594423b700e5bba57967513b700d1a579693b220a700e5c5a5796e513b7
  | 7, 2, 1 => 0xbba579514e3b00700d1c1bba5795133700d1bba56a5a513b700d1cac5a5795133700e9d1bba5513b1070000d1a57e513b0a600e8d1bba5793b22700d1bbb07f79513b700d1bba55c513b10700cfbba5793b2205700e5bba579513b25700e5bba5793b3322700d1bbb08c79513b700e5bbbaa5793b22700d1bba579513b1e700dcd1a5513b100a7
  | 7, 2, 2 => 0xcaa579513b00600e5bba579403b2270000d1bba58c423b600e0d1bba579473b700e5bbb4a5793b22700d1cfbbb079513870000d1bba53b2210600d1bba57959513b700d1cabba579473b700e5bba5793b3422700bba57951332c05700e0d1a5513b100a700d1bba579513314700d1c5bba5513310700e5bba58c79513b7d1c5bba57951473b8
  | 7, 2, 3 => 0xdcd1a5793b220a700d1bba59b513b1070000d1bbb4453b10600d1bba58479513b70000d1bba57e3b22600d1bba579513d33700d1bba5793b220270000e9bba5794e3b600e5caa579513b37700d1bba579514014700bba57951331005700e5bba5793b2219700a5796a513b0a057d1bbb0796a69513b800d1bba5796a5133700d1bba5795134147
  | 7, 2, 4 => 0xd1bba5513b35600d1a57951403b0a700e0d1a5793b220a70000bb513b100b05600d1c5bba5793322700e5bba579513b14700e5c5a579514e3b700d1a5795e513b0a700d1b0a5513b100a700e5c5a57951483b700e9d1bba5793b22700d7d1a5793b220a700d1bba594423b33700bba57951332205700d1bba57969483b70000d1bba58d51336
  | 7, 2, 5 => 0xe5bba5793b3722700d1bbb0876a513b700d1bfbba579693b700eae5bb79513b0b700d1a579513b2a0a70000bba5793b2200600e5d1caa5793b22700d3d1bba5513310700d1bba579514c33700e1d1bba5793b22700bba5796a3b2205700d1cfbba5793322700d1bba57967513b70000bb8879513b0560000e5caa5794e3b6e0dcbba5796a513b8
  | 7, 2, 6 => 0xd1cabba582513b70000d1bba5794019600d1a7a5793b220a700bba57951493b05700d1bba57957513b700d1a5796a51330a700d2d1bba5793b22700d1bba5795e3b2270000d1bb6a51473b600e5bba57952513b7e5dcbba5796a513b800d1bbb0a53b221070000bbba6a513b05600bbbaa579513b0070000e5bba58d513b600d1bba58c79513b7
  | 7, 2, 7 => 0xd1bba5816c513b700d1bbb4795e453b700d1bba579332214700bba57969513405700e0d1a579693b0a700d1cabba579332a700d1cdbba5795133700d1cabba5795f3b7e5bba5796a514e3b800bbb4a579513b007e5e0bba5796a513b800d1bcbb793b220b7dcd1bba58c79513b800d1bba5793b221e700bba57969513305700d1bba5793b22087
  | 7, 2, 8 => 0xbba59451423b05700d0bba5513b100570000d1caa579483b600bba57969645134700d1bba579513b14700d1bba5796a3322700d1bba5796c5133700e5d1caa579693b700d1bba58d69513b700d1b0796a513b0a700e5caa5796a513b70000e5c5a5793b22600e5bba57951332c700d5d1bba5793b2270000d1bb5133100b600bba579696451337
  | 7, 2, 9 => 0xe5d1bba58c79513b800d1c2a5796a513b700d1c5bba594423b700d1bba57951332d700e5cda57969513b700d1a5793b33220a700d1bba5796b3b22700d1baa5793b220a700e5bba579513b20700e5bba57951331070000d1caa5794e3b600d1bbb8a579513b700d1bba5793b221a700d1cebba5795133700e5bba5793b2200700e5c5baa579513b7
  | 7, 2, 10 => 0xd1bba59179513b700cabba579513305700d1bba57952513b700d1bbb0796a3b2270000e5bb513b100b600d1a579403b220a700bb7951423b0b057e9e5bba5796a513b800d1b4a5793b220a700d1a5793b34220a700e5bba579513322700e5c5b4a579513b70000d1bbba6a5133600d1a58c79513b0a700d1bb513b22100b700e5bba58579513b7
  | 7, 2, 11 => 0xd1cabba58d513b700bba57951473b05700d1bbba806a513b70000bbb079513805600d1bba58c793b22700d1bba579693414700dcd1bba58d513b70000d1bba8513b1060000e5cda579513b600bba579514e3b3a700d1bba59458513b700bba58079513b05700d1bba579693b07700e5bba5796a3b22700d1cebbb079513b700d1a5793b22190a7
  | 7, 2, 12 => 0xc5a579513b00600e5bba579695133700d1bba579514133700d1bb69513b100b700d1cabba579693970000d8a579513b0a60000e5c5a579513a60000a57951330a05600d1bba5796a6934700d1bba594514233700d1bba579513b18700d1bba579513313700d1a579513b140a700e0d1bba58d513b70000e5bbba6a513b600e5bba59475513b7
  | 7, 2, 13 => 0xd1bba579513322700d1cac5a5793b2270000d1a58d513b0a600d1a5793b37220a700e5d1bba58d513b700e5bba579695134700e0d1bba579403b70000d1bba5793414600d1cabba579403b700d4bba57969513b700a579513b100a05700d1bba579513b20700d1bba594795f3b700d1bba5795b513b700d1bba5793b220070000d1bbba8c513b6
  | 7, 2, 14 => 0xd1bba58c79693b700e5bba579514f3b700e5bba5793b2220700d1bbb49c79513b70000d8bba5793b226d1cac5baa579513b80000d1bb513b100b60000bba579332205600d1bba580795133700d1bbba6a69513b7e9d1bba5796a513b800d1bba5793b2214700d1cabba5793b2a700e5bba57968513b700a579513b220a05700e5caa579513b397
  | 7, 2, 15 => 0xbbb4a579513305700d1bba57951332b700d1bba579513330700bba5796a513b007e5d1caa5796a513b800e5d1c5a5793b22700dcd1bb513b100b700d1bba57951473370000c2a579513b05600bba5793b221005700e5caa579513b3a700d1bbb7a579513b700bbbaa57951330570000d4bba579513b600d1bba5796a3b22700d1c0bba57951337
  | 7, 3, 0 => 0xd1cac5a579693b700d1cdbba5796934700e5bba58079513b700bba57952513b00700d1a5795133100a700e5bba579514e33700e0d1bb513b100b700d1cabb513b100b7
  | 8, 0, 0 => 0xd1bba579513b13700d1d0bba5513b107dcd1bba58779513b800d2d1bb79513b0b7d1bba57969513b2280000bba5513b1005600d1bb79513b340b700e4d1bba57951337d1bba57969513b10800d1bb79513b330b700d1bba5796951347d1bba5795a51423b8d1cabba59c79513b800d1bba5a079513b7e4d1bba58779513b800cabba579513b057
  | 8, 0, 1 => 0xdcd1bba5795133700d1bba579513b01700eae5bba579513b7e0d1bba58779513b800e5bba57969513b7d1cabba58779513b800d1bba57951413b7e0d1bba5a079513b800bbb0a579513b0570000a579513b0a05600d1bba59451423b70000d1bba5795133600d1bb9479513b0b700e5bba57951453b700d1c4bba579513b700d1bba579513b2c7
  | 8, 0, 2 => 0xbba5793b2205600d1bba58079513b700d1bbb17951423b7dcd1bba579513b10800e0dcbba579513b700e0d1bba5795133700e5e4bba579513b700d1bba57956513b700d1cabba5795133700d1bba579513b22700d1c7bba579513b700d1bb7951423b0b700d1bba5793b221d7d1cfbba579513b38800d1bba57951443b700d1bba5a279513b7
  | 8, 0, 3 => 0xd1bba57951473b70000d1bbb0795138600bba579513b3305700d1bba59e79513b700bbbaa579513b05700d1bba579514d3b7e0d1bba579513b108d1bbb0a58779513b8dcd1bba579513b228d1cabba579513b10800d1bba579514b3b700d1a58779513b0a7d1c5bba5796a513b800d1d0bba5793b227e5d1bba58779513b8d1bba5796951453b8
  | 8, 0, 4 => 0xd1d0bba59479513b8e4d1bba57969513b800d1bba57951453b700bbb4a579513b05700d1bbb0a5795133700bba579513b340570000d1a57951330a6e0d1bba579513b22800d1bb79513b370b700e5dcbba579513b700e5d1bba5795133700d1bba6a5513b107d1cabba579513b2280000d1bba55133106d1bba58c796a513b8d1d0bba579513b338
  | 8, 0, 5 => 0xd1bba556513b10700d1bba5796e513b700d1bba5513b2210700e8e5bba579513b700d1bba579513b28700d1bba57969513b700d1bba58879513b700d1bba579513e3b700d1bba587793b22700d1a579513b100a7e5d1bba5a279513b800e5bba579514e3b700d1c5bb79513b0b7e5d1bba579513b10800e5e0bba579513b700d1bba5513b100b7
  | 8, 0, 6 => 0xe5bbb0a579513b7d1bbb4a58779513b8e0d1bba57951453b8d1bba5796958513b8d1cabba57951453b8dcd1bba57969513b80000d1bba579332260000e5bba5513b10600dbd1bba579513b700bba57951423b05700d1c2bba579513b70000e5caa579513b600d1a579513b220a70000d1bba56c513b6dcd1bba57951453b8e5d1bba579513b228
  | 8, 0, 7 => 0xd1bba5513e3b10700d7d1bba579513b700d1bba57958513b700e2d1bba579513b700d1a57951453b0a700bba579513b37057e5d1bba57951453b800d1bbb4a57951337d1bba579513b3310800e9e5bba579513b700d1bb79513b380b70000d1c2a579513b6e0d1bba57969513b800d1bba5793b2210700d1bbbaa57951337d1cabba57969513b8
  | 8, 0, 8 => 0xd1bba579514e3b700e3d1bb79513b0b700d1bba5a179513b700d1bba57951332a700d1bba56a51423b700d1bb796a513b0b700c5bba579513b05700d1a57969513b0a700d1bba57951483b700d1bba5795f513b7d1bba579513b33228e5d1bba57969513b80000e5bba5793b22600ddd1bba579513b700d1bba569513b10700d1bba579514a3b7
  | 8, 0, 9 => 0xd1bba579693b22700d1bfbba579513b700e5bbb4a579513b70000d1bba5513b10600d1bba579453b227d1bba579513b2219800e5bba579513b34700e4d1a579513b0a70000d1bba5796934600e8d1bba579513b700d1bba579514233700cfbba579513b05700e5bba579513b33700e5bbbaa579513b700e5bba57975513b7d1bbb0a57969513b8
  | 8, 0, 10 => 0xe5d1bba579514e3b800d1c5bba5795133700d1bba579513b1b700e0d1bba5513b10700e4d1bba5793b22700d1cabba5513b10700e9d1bba579513b700dcd1a579513b0a7d1bbbaa57969513b80000d1bba57e513b600d1bba579513b02700dcd1bba5513b107d1c5bba58779513b8e1d1bba57969513b80000d1bba594423b6d1bba57951453b338
  | 8, 0, 11 => 0xe5bba579513b37700d1bba5796f513b70000d1a5513b100a6d1cfbba579513b0b800dcd1bba5793b22700e5d1bba5513b1070000bba579513b00600e5d1caa579513b7d1c5bba579513b108d1bba579513b3722800e1d1bba579513b700bba5796a513b05700d1cfbba579513370000d1bba5793b226d1bbb4a57969513b800e0d1a579513b0a7
  | 8, 0, 12 => 0xdcd1bbb4a579513b8e0d1bbbaa579513b8d1cabba579513b338d1cabbbaa579513b800d1bcbb79513b0b700d1bba579513b08700d1bba57951403b700e0d1bba5793b227dcd1bbbaa579513b800d1cabba5793b22700d2d1bba579513b700d1bba5795e513b700d1bbb0a5513b107e4d1bba59479513b8d1c5bba579513b22800d7d1bba5793b227
  | 8, 0, 13 => 0xe5d1bbbaa579513b800e5bba579513b00700d1bba7a5793b22700d1bba5796a51337d1c5bba57951453b80000d1a5793b220a6e0d1bbb4a579513b800e5d1bba5793b227d1cabbb4a579513b800d1bfbba5793b2270000e5c5a579513b6d1cabba579513b3480000d1bba53b2210600d1bba579513b077d1bba57951453b37800d1bba579513b2a7
  | 8, 0, 14 => 0xd1bbb0796a513b7d1bba5796a513b22800d1b4a579513b0a7d1bba5997969513b800d1a579513b340a7e5d1bbb4a579513b800e0d1bba579693b7d1cfbba57969513b800d1cabba579693b700d1bdbba579513b7d1c5bba5796e513b800d1a579513b330a700d1bba5796b513b700d1baa579513b0a7d1c5bba57969513b800d1bba59f79513b7
  | 8, 0, 15 => 0xd1bbb4a579513b33800d1bba579513b00700d1bba5793b22197d1c5bba57951483b800d1bba579403b227d1bba57969513b14800d1bbb4a5793b22700d1bba5793b34227d1bbbaa579513b338d1cabba579513b37800d1bba58c79513b700d1bba551423b10700d1bba5793b3322700d1bbbaa5793b22700e5bba5796a513b7d1bba580796a513b8
  | 8, 1, 0 => 0xd1c5bba5793b22700bba579513b22057dcd1bba5796a513b80000d1bba58d513b600d1bba5793b3722700e5d1c5a579513b700bba579513b1005700d1bba5796a513b70000d8bba579513b60000bba579513305600d1bba579513b147d1bbb4a59479513b800d1cac5a579513b700d1a579513b370a7d1d0bba58779513b8d1bba5796a69513b8
  | 8, 1, 1 => 0xe5bba579513360000d1bb513b100b600bba5796964513b700d1cdbba579513b700d1bba579513322700bba57969513b05700d1bba579513310700d1a5796a513b0a7e5d1bba5796a513b8d1c5bbb4a579513b800e5bba579513b3a700d1bba57951332c7d1cdbba57969513b8d1c5bbbaa579513b8e0d1bba5796a513b8d1cabba5796a513b8
  | 8, 1, 2 => 0xd1bba5796951337d1cabba579513b398d1bba5796a513b34800d8d1bba579513b700e5bba579513b2270000d1bbba6a513b6d1bba5796a513b33800e5bba579513b10700d1cebba579513b700d1bba5796a3b227
  | 9, 0, 0 => 0xd1bba5793b22600d1a579513b0a6e5d1bba579513b700d1bba5513b106e0d1bba579513b7d1cabba579513b7dcd1bba579513b700d1bba579513b6e4d1bba579513b7d1bba57969513b7d1bba57951453b700e5bba579513b6d1bba579513b227d1bba579513b10700d1bba57951336d1bba58779513b7
  | 9, 0, 1 => 0xbba579513b056d1bba5796a513b7d1cfbba579513b7d1c5bba579513b7d1bba579513b377d1bbb4a579513b7d1bba579513b347d1bba579513b337d1bbbaa579513b7
  | 10, 0, 0 => 0xd1bba579513b6
  | _, _, _ => 0
def stateW : Nat → Nat
  | 1 => 20
  | 2 => 28
  | 3 => 36
  | 4 => 44
  | 5 => 52
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
  | 0, 0 => 0xfe2000c78f700000000000000000000000000000000000000000000000000000fe2007fffff00000000000000000000000000000000000000000000000000000001ffffffff000000000000000000000000000000000000000000000000000000000773ffff00000000000000000000000000000000000000000000000000000001ffffffff00000000000000000000000000000000000000000000000000000001ffff870800000000000000000000000000000000000000000000000000000001f88c78f700000000000000000000000000000000000000000000000000000000007fffff
  | 0, 1 => 0x3ff1ffff838708000000000000000000000000000000000000000000000000003ff1ffff807fff000000000000000000000000000000000000000000000000003ff1ffff8078ff000000000000000000000000000000000000000000000000003f11e3f88078f70000000000000000000000000000000000000000000000000007f07e3f8007ff00000000000000000000000000000000000000000000000000000ffe007fffff00000000000000000000000000000000000000000000000000000ffe007fffff00000000000000000000000000000000000000000000000000000ffe007f8708
  | 0, 2 => 0x3f1fe3f88c00f7000000000000000000000000000000000000000000000000003f1fe3f8ffffff000000000000000000000000000000000000000000000000003f1fe3f88c78f7000000000000000000000000000000000000000000000000003f1fe3f88c0000000000000000000000000000000000000000000000000000003ff1ffff83ffff000000000000000000000000000000000000000000000000003f01e1f803fff0000000000000000000000000000000000000000000000000003ff1ffff83f8ff0000000000000000000000000000000000000000000000000038f19fc783f80f
  | 0, 3 => 0x3f1fe2000078f7000000000000000000000000000000000000000000000000003f1001f88078f700000000000000000000000000000000000000000000000000380f81c00c780000000000000000000000000000000000000000000000000000070e60380c07f000000000000000000000000000000000000000000000000000070e60380c00f000000000000000000000000000000000000000000000000000000e00000c000000000000000000000000000000000000000000000000000000000000000078f7000000000000000000000000000000000000000000000000003fffffff8c0708
  | 0, 4 => 0x380f81c00ff8000000000000000000000000000000000000000000000000000007ee7c3f0f80f8000000000000000000000000000000000000000000000000003f1fe3f8ffffff000000000000000000000000000000000000000000000000003f1fe3f8f38708000000000000000000000000000000000000000000000000003f1fe3f8ffffff000000000000000000000000000000000000000000000000003f1fe3f88c78f7000000000000000000000000000000000000000000000000003f1fe3f88078f7000000000000000000000000000000000000000000000000003f1fe3f8800000
  | 0, 5 => 0x38ef9dc77f870800000000000000000000000000000000000000000000000000380f81c07f80000000000000000000000000000000000000000000000000000007ee7c3f7f870800000000000000000000000000000000000000000000000000070e60387c070000000000000000000000000000000000000000000000000000000e00007c00000000000000000000000000000000000000000000000000000000e01c077387080000000000000000000000000000000000000000000000000000000000738000000000000000000000000000000000000000000000000000003fffffff8ff8ff
  | 0, 6 => 0xf0000000000000000000000000000000000000000000000000003f1fe3f88c00000000000000000000000000000000000000000000000000000038f19fc783f80f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003fffffffff8708000000000000000000000000000000000000000000000000003ffe61fffc0700000000000000000000000000000000000000000000000000003ff01dfff38708000000000000000000000000000000000000000000000000003f0fe1f87f8700
  | 0, 7 => 0x3f1fe3f88c78f70000000000000000000000000000000000000000000000000038f19fc783f8ff0000000000000000000000000000000000000000000000000007f07e3f807fff00000000000000000000000000000000000000000000000000000fe2000c78f700000000000000000000000000000000000000000000000000000000000078f7000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007800
  | 0, 8 => 0x7387000000000000000000000000000000000000000000000000000000000000738000000000000000000000000000000000000000000000000000000000000073800000000000000000000000000000000000000000000000000000000000007007000000000000000000000000000000000000000000000000000007f07e3ff007ff00000000000000000000000000000000000000000000000000000000007007000000000000000000000000000000000000000000000000000000000000700000000000000000000000000000000000000000000000000000003f1fe3f88c78f7
  | 0, 9 => 0xe01c070000000000000000000000000000000000000000000000000000000000e01c070000000000000000000000000000000000000000000000000000000000e01c007380000000000000000000000000000000000000000000000000000000e01c007007000000000000000000000000000000000000000000000000000000e01c000000000000000000000000000000000000000000000000000000000000e000077380000000000000000000000000000000000000000000000000000000e000077007000000000000000000000000000000000000000000000000000000e00007000000
  | 0, 10 => 0x38ef9dc77f87080000000000000000000000000000000000000000000000000038f19fc7f3ff0f0000000000000000000000000000000000000000000000000038f19fc7f3f80f0000000000000000000000000000000000000000000000000007f07e3ff387ff0000000000000000000000000000000000000000000000000000effe077f87080000000000000000000000000000000000000000000000000000e01c077fffff0000000000000000000000000000000000000000000000000000e01c077387080000000000000000000000000000000000000000000000000000e01c07738000
  | 0, 11 => 0xe01c0773ff08000000000000000000000000000000000000000000000000000000000073f8f7000000000000000000000000000000000000000000000000000000000073f8000000000000000000000000000000000000000000000000000000e01c077387f800000000000000000000000000000000000000000000000000000000007380f00000000000000000000000000000000000000000000000000000000000707ff700000000000000000000000000000000000000000000000000000000007078f700000000000000000000000000000000000000000000000000000000007007f0
  | 0, 12 => 0xe01c070078f70000000000000000000000000000000000000000000000000000e01c070000000000000000000000000000000000000000000000000000000000e01c0073f8f70000000000000000000000000000000000000000000000000000e01c000000000000000000000000000000000000000000000000000000000000e0000773f8f7000000000000000000000000000000000000000000000000000000000073fff70000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000073fff0
  | 0, 13 => 0x700003870070000000000000000000000000000000000000000000000000000070000380000f000000000000000000000000000000000000000000000000000000e00007c07f000000000000000000000000000000000000000000000000000000e00007c070000000000000000000000000000000000000000000000000000000e00007c00f000000000000000000000000000000000000000000000000000000e00007c00000000000000000000000000000000000000000000000000000000e01c0773ffff0000000000000000000000000000000000000000000000000000e01c07738708
  | 0, 14 => 0x70e60380000f000000000000000000000000000000000000000000000000000070e60380c00f000000000000000000000000000000000000000000000000000070e603800000000000000000000000000000000000000000000000000000000070e60007c000000000000000000000000000000000000000000000000000000070e600070070000000000000000000000000000000000000000000000000000070e60000000f000000000000000000000000000000000000000000000000000070e00387c000000000000000000000000000000000000000000000000000000070000387007f0
  | 0, 15 => 0xe00007c780000000000000000000000000000000000000000000000000000070e60387c07f000000000000000000000000000000000000000000000000000000e00007c0000000000000000000000000000000000000000000000000000003f1fe3f8fc7ff70000000000000000000000000000000000000000000000000007fe7e3ffc07ff00000000000000000000000000000000000000000000000000070e60387fffff00000000000000000000000000000000000000000000000000070e60387c07f000000000000000000000000000000000000000000000000000070e60387c0000
  | 1, 0 => 0x70e60387c7ff700000000000000000000000000000000000000000000000000070e60387c07f000000000000000000000000000000000000000000000000000070e603800000000000000000000000000000000000000000000000000000000070e600070070000000000000000000000000000000000000000000000000000070e00387c78f700000000000000000000000000000000000000000000000000070e60387c07f000000000000000000000000000000000000000000000000000000e00007c7ff700000000000000000000000000000000000000000000000000000e00007c78f7
  | 1, 1 => 0x7e01c3f7387f80000000000000000000000000000000000000000000000000007e0003f0000f000000000000000000000000000000000000000000000000000070e60387f87f00000000000000000000000000000000000000000000000000000ee1c077f87080000000000000000000000000000000000000000000000000000e0000700000000000000000000000000000000000000000000000000000000000e00007f870000000000000000000000000000000000000000000000000000000e00007f80f000000000000000000000000000000000000000000000000000000e00007f8000
  | 1, 2 => 0xee1c077fff0800000000000000000000000000000000000000000000000000000e00007ff8f700000000000000000000000000000000000000000000000000000e00007ff8000000000000000000000000000000000000000000000000000007ee7c3f7f87f80000000000000000000000000000000000000000000000000007ee7c3f0000f00000000000000000000000000000000000000000000000000007ee7c3f0000000000000000000000000000000000000000000000000000000007ee7c077387f80000000000000000000000000000000000000000000000000007ee1c3f7f8708
  | 1, 3 => 0x380f800000780000000000000000000000000000000000000000000000000000380e01c07c000000000000000000000000000000000000000000000000000000380001c073f80000000000000000000000000000000000000000000000000000380001c073800000000000000000000000000000000000000000000000000000380001c000780000000000000000000000000000000000000000000000000000380001c00000000000000000000000000000000000000000000000000000000007ee7c3f7fffff0000000000000000000000000000000000000000000000000000ee1c077fffff
  | 1, 4 => 0x3f1fe3f8fff8f70000000000000000000000000000000000000000000000000038ff9fc7fff80f00000000000000000000000000000000000000000000000000380f81c07ff80000000000000000000000000000000000000000000000000000380f81c07c000000000000000000000000000000000000000000000000000000380f81c000780000000000000000000000000000000000000000000000000000380f81c000000000000000000000000000000000000000000000000000000000380f80007c000000000000000000000000000000000000000000000000000000380f8000738000
  | 1, 5 => 0x380f81c07ff80000000000000000000000000000000000000000000000000000380f81c00078f700000000000000000000000000000000000000000000000000380f81c000000000000000000000000000000000000000000000000000000000380f80007c78f700000000000000000000000000000000000000000000000000380f800073f8f700000000000000000000000000000000000000000000000000380001c073f8f700000000000000000000000000000000000000000000000000380001c073800000000000000000000000000000000000000000000000000000380f81c07ff800
  | 1, 6 => 0x3f0001f8738700000000000000000000000000000000000000000000000000003f0001f80078f00000000000000000000000000000000000000000000000000038ef9dc77fffff0000000000000000000000000000000000000000000000000038ef9dc77fff080000000000000000000000000000000000000000000000000038ef9dc77387080000000000000000000000000000000000000000000000000038ef9c077f870800000000000000000000000000000000000000000000000000380f81c07fff0000000000000000000000000000000000000000000000000000380f81c07ff8f7
  | 1, 7 => 0x3fffe3ff8c78f7000000000000000000000000000000000000000000000000003ff001ff8078f7000000000000000000000000000000000000000000000000003ff19fff83f80f000000000000000000000000000000000000000000000000003ff07fff8007ff000000000000000000000000000000000000000000000000003ff001ff800000000000000000000000000000000000000000000000000000003f0fe1f87ffff0000000000000000000000000000000000000000000000000003f0fe1f8000000000000000000000000000000000000000000000000000000003f0fe000738700
  | 1, 8 => 0x3ff001fff38000000000000000000000000000000000000000000000000000003ff001fff00700000000000000000000000000000000000000000000000000003ff001ff8078f7000000000000000000000000000000000000000000000000003ff001ff807800000000000000000000000000000000000000000000000000003ff001ff8000f0000000000000000000000000000000000000000000000000003ff001ff800000000000000000000000000000000000000000000000000000003fff81ffff8000000000000000000000000000000000000000000000000000003ff01dfff38708
  | 1, 9 => 0x3ffe61fffc07f0000000000000000000000000000000000000000000000000003ffe01fffc0000000000000000000000000000000000000000000000000000003ff01dfff3ffff000000000000000000000000000000000000000000000000003ff01dfff38708000000000000000000000000000000000000000000000000003ff01dff800000000000000000000000000000000000000000000000000000003ff01dfff38708000000000000000000000000000000000000000000000000003ff01dff800000000000000000000000000000000000000000000000000000003ff01dff800000
  | 1, 10 => 0x3ffffff88c78f7000000000000000000000000000000000000000000000000003ffffe000c0000000000000000000000000000000000000000000000000000003ffffe000078f7000000000000000000000000000000000000000000000000003ffffff88c0000000000000000000000000000000000000000000000000000003fffffc783f80f000000000000000000000000000000000000000000000000003ffffe3f8007ff000000000000000000000000000000000000000000000000003ffffe00000000000000000000000000000000000000000000000000000000003fff81fffff800
  | 1, 11 => 0x3ffffe07000000000000000000000000000000000000000000000000000000003ffffe00738000000000000000000000000000000000000000000000000000003ffffe00700700000000000000000000000000000000000000000000000000003ffffe000078f7000000000000000000000000000000000000000000000000003ffffe00007800000000000000000000000000000000000000000000000000003ffffe000000f0000000000000000000000000000000000000000000000000003ffffff88c0000000000000000000000000000000000000000000000000000003ffffe00000000
  | 1, 12 => 0x3fffffff800000000000000000000000000000000000000000000000000000003fffffff8c78f7000000000000000000000000000000000000000000000000003fffffff800000000000000000000000000000000000000000000000000000003fffffc07ff800000000000000000000000000000000000000000000000000003ffffe387c07f0000000000000000000000000000000000000000000000000003ffffe007c0000000000000000000000000000000000000000000000000000003ffffe0773ffff000000000000000000000000000000000000000000000000003ffffe07738708
  | 1, 13 => 0x3ffffffffff800000000000000000000000000000000000000000000000000003ffffffffc07f0000000000000000000000000000000000000000000000000003ffffffff38708000000000000000000000000000000000000000000000000003fffffff8078f7
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x2a2000450a4000000000000000000000000000000000000000000000000000000000014993900000000000000000000000000000000000000000000000000000001ffbdbb7b00000000000000000000000000000000000000000000000000000000dfb5bb7b00000000000000000000000000000000000000000000000000000001fead326200000000000000000000000000000000000000000000000000000001b629020000000000000000000000000000000000000000000000000000000001688c30620000000000000000000000000000000000000000000000000000000000149939
  | 0, 1 => 0x12c15896030600000000000000000000000000000000000000000000000000000b70ee5b8067df000000000000000000000000000000000000000000000000000930a6498060cf000000000000000000000000000000000000000000000000000910a2488060c60000000000000000000000000000000000000000000000000003706e1b8007df000000000000000000000000000000000000000000000000000007fe0056ddbd000000000000000000000000000000000000000000000000000007fa004654a40000000000000000000000000000000000000000000000000000055800420400
  | 0, 2 => 0x251823288800c600000000000000000000000000000000000000000000000000240801201c993900000000000000000000000000000000000000000000000000240801200c10200000000000000000000000000000000000000000000000000024080120080000000000000000000000000000000000000000000000000000001bf1fedf83efdf000000000000000000000000000000000000000000000000001bc1f8de03efd00000000000000000000000000000000000000000000000000019b1b6cd83e8cf0000000000000000000000000000000000000000000000000018b196c583e80f
  | 0, 3 => 0x2d1aa2488470e6000000000000000000000000000000000000000000000000002d1aa3688c70e6000000000000000000000000000000000000000000000000002c0a81600c702000000000000000000000000000000000000000000000000000274a693a0c17f000000000000000000000000000000000000000000000000000250a21280c10e000000000000000000000000000000000000000000000000000240a01200c1020000000000000000000000000000000000000000000000000000912a2488470e60000000000000000000000000000000000000000000000000026484932080600
  | 0, 4 => 0x3c8b91e40ff8200000000000000000000000000000000000000000000000000035ab35ad0f98e9000000000000000000000000000000000000000000000000002d1aa3689cf9ff000000000000000000000000000000000000000000000000002d1aa36898e9df000000000000000000000000000000000000000000000000002d1aa3688c70e6000000000000000000000000000000000000000000000000002d1aa3688c70e6000000000000000000000000000000000000000000000000002d1aa3688c70e6000000000000000000000000000000000000000000000000002d1aa3688860c6
  | 0, 5 => 0x36cd59b66b060000000000000000000000000000000000000000000000000000348d11a46b00000000000000000000000000000000000000000000000000000036cd59b66b060000000000000000000000000000000000000000000000000000264c493268060000000000000000000000000000000000000000000000000000240c01206800000000000000000000000000000000000000000000000000000012c558966306000000000000000000000000000000000000000000000000000010851084630000000000000000000000000000000000000000000000000000003dbbb7ed8ff8ef
  | 0, 6 => 0x10220081411f000000000000000000000000000000000000000000000000000242805211889190000000000000000000000000000000000000000000000000018b196c593e91f00000000000000000000000000000000000000000000000000002004011089190000000000000000000000000000000000000000000000000036cd59b66b06000000000000000000000000000000000000000000000000000036cc49b66906000000000000000000000000000000000000000000000000000036cd59b66b06000000000000000000000000000000000000000000000000000036cd59b66b0600
  | 0, 7 => 0x2d3aa7698c70e60000000000000000000000000000000000000000000000000019b3b6cd97f9ff000000000000000000000000000000000000000000000000000b72ee5b94ffff000000000000000000000000000000000000000000000000000932a64994f9ff000000000000000000000000000000000000000000000000000932a64994f9ff000000000000000000000000000000000000000000000000000932a6498060c6000000000000000000000000000000000000000000000000000930044990a95b000000000000000000000000000000000000000000000000000802804014f820
  | 0, 8 => 0x12c55896738f100000000000000000000000000000000000000000000000000010a5148573891900000000000000000000000000000000000000000000000000108510847388000000000000000000000000000000000000000000000000000002644c13708f190000000000000000000000000000000000000000000000000003746e1bf007df00000000000000000000000000000000000000000000000000024448127007100000000000000000000000000000000000000000000000000000040000700000000000000000000000000000000000000000000000000000002d3aa7699cf9ff
  | 0, 9 => 0x12e55c97738f190000000000000000000000000000000000000000000000000012e55c976306000000000000000000000000000000000000000000000000000012e55c84738c000000000000000000000000000000000000000000000000000012e55c127207100000000000000000000000000000000000000000000000000012e55c01528d190000000000000000000000000000000000000000000000000012e51097738a000000000000000000000000000000000000000000000000000012e448977107100000000000000000000000000000000000000000000000000012e00497318b19
  | 0, 10 => 0x36ed5db77b8f19000000000000000000000000000000000000000000000000001af5ded7f3ef1f0000000000000000000000000000000000000000000000000018b596c5f3e80f0000000000000000000000000000000000000000000000000013f57e9ff38fdf0000000000000000000000000000000000000000000000000012e55c97738f190000000000000000000000000000000000000000000000000012e55c97779f390000000000000000000000000000000000000000000000000012e55c97738f190000000000000000000000000000000000000000000000000012e55c97738e00
  | 0, 11 => 0x1ae7dcd777ff390000000000000000000000000000000000000000000000000019b7b6cdf7f9ff00000000000000000000000000000000000000000000000000188790c477f8200000000000000000000000000000000000000000000000000013e77c9f779ff9000000000000000000000000000000000000000000000000001187308c7799f0000000000000000000000000000000000000000000000000000b76ee5bf4ffff000000000000000000000000000000000000000000000000000936a649f4f9ff000000000000000000000000000000000000000000000000000346681a7417f0
  | 0, 12 => 0x1bf7fedff7ffff000000000000000000000000000000000000000000000000001bf7fedfe366c6000000000000000000000000000000000000000000000000001bf7fecdf7fdff000000000000000000000000000000000000000000000000001bf7fe00424484000000000000000000000000000000000000000000000000001bf7b6dff7fbff000000000000000000000000000000000000000000000000001bf7fedff7ffff000000000000000000000000000000000000000000000000001bf7fedfe366c6000000000000000000000000000000000000000000000000001bc7f8de77fff0
  | 0, 13 => 0x274c493a78075000000000000000000000000000000000000000000000000000274a213a3c13f000000000000000000000000000000000000000000000000000274e693a7c17f000000000000000000000000000000000000000000000000000264e49327c173000000000000000000000000000000000000000000000000000250e21287c11f000000000000000000000000000000000000000000000000000240e01207c1020000000000000000000000000000000000000000000000000001bf7fedff7ffff000000000000000000000000000000000000000000000000001bf7fedff3efdf
  | 0, 14 => 0x274e693a7c17f000000000000000000000000000000000000000000000000000274e693a6c16e000000000000000000000000000000000000000000000000000274e693a6806c000000000000000000000000000000000000000000000000000274e69207c14a000000000000000000000000000000000000000000000000000274e681270079000000000000000000000000000000000000000000000000000274e68085415f000000000000000000000000000000000000000000000000000274e013a7c126000000000000000000000000000000000000000000000000000274e693a7c17f0
  | 0, 15 => 0x2c0e81607cf82000000000000000000000000000000000000000000000000000276e6d3b7c9ff900000000000000000000000000000000000000000000000000242e05217c9939000000000000000000000000000000000000000000000000002f5eeb7afc77f600000000000000000000000000000000000000000000000000277e6f3bfc17ff00000000000000000000000000000000000000000000000000274e693a7c9ff900000000000000000000000000000000000000000000000000274e693a7c17f000000000000000000000000000000000000000000000000000274e693a7c16e0
  | 1, 0 => 0x2f7eef7bfcffff000000000000000000000000000000000000000000000000002f7eef7bfc77f6000000000000000000000000000000000000000000000000002f7eef7be866c6000000000000000000000000000000000000000000000000002f7eee1370cf9d000000000000000000000000000000000000000000000000002f7ea77bfcfbff000000000000000000000000000000000000000000000000002f7e6d7bfcbffb000000000000000000000000000000000000000000000000002f7eef7bfcffff000000000000000000000000000000000000000000000000002d3ea769fcf9ff
  | 1, 1 => 0x37ef7dbf7f9ff90000000000000000000000000000000000000000000000000037ea25bf3d9bf90000000000000000000000000000000000000000000000000037cf79be7f9ff00000000000000000000000000000000000000000000000000036ef5db77f9f390000000000000000000000000000000000000000000000000036ea05b73d9b390000000000000000000000000000000000000000000000000036cf59b67f9f300000000000000000000000000000000000000000000000000035af35ad7f99f900000000000000000000000000000000000000000000000000348f11a47f9820
  | 1, 2 => 0x3eefddf77fff39000000000000000000000000000000000000000000000000003dbfb7edfff9ff000000000000000000000000000000000000000000000000003c8f91e47ff8200000000000000000000000000000000000000000000000000037ef7dbf7f9ff90000000000000000000000000000000000000000000000000037ef7dbf7f9ff90000000000000000000000000000000000000000000000000037ef7dbf6b06c00000000000000000000000000000000000000000000000000037ef7c9f779ff90000000000000000000000000000000000000000000000000037ef5dbf7f9f79
  | 1, 3 => 0x3c8f904056f820000000000000000000000000000000000000000000000000003c8e01e47d3020000000000000000000000000000000000000000000000000003c8f91e47ff820000000000000000000000000000000000000000000000000003c8d11e47ba800000000000000000000000000000000000000000000000000003c8a81e43df820000000000000000000000000000000000000000000000000003c8801e439a800000000000000000000000000000000000000000000000000003fffffffffffff000000000000000000000000000000000000000000000000003fffffffffffff
  | 1, 4 => 0x3d9fb3ecfff8e6000000000000000000000000000000000000000000000000003cbf97e5fff82f000000000000000000000000000000000000000000000000003c8f91e47ff820000000000000000000000000000000000000000000000000003c8f91e47f7020000000000000000000000000000000000000000000000000003c8f91e47ff820000000000000000000000000000000000000000000000000003c8f91e46b6000000000000000000000000000000000000000000000000000003c8f91207e5020000000000000000000000000000000000000000000000000003c8f908473c800
  | 1, 5 => 0x3dbfb7edfff8e6000000000000000000000000000000000000000000000000003dbfb7edfff9ff000000000000000000000000000000000000000000000000003dbfb7edeb60c6000000000000000000000000000000000000000000000000003dbfb769fef9ff000000000000000000000000000000000000000000000000003dbfb6cdf7f9ff000000000000000000000000000000000000000000000000003dbfb7edfff9ff000000000000000000000000000000000000000000000000003dbd15edfba95b000000000000000000000000000000000000000000000000003caf95e57ff939
  | 1, 6 => 0x3fcd59fe7baf50000000000000000000000000000000000000000000000000003fcaa1fe3dfbf0000000000000000000000000000000000000000000000000003fffffffffffff000000000000000000000000000000000000000000000000003eefddf77fff39000000000000000000000000000000000000000000000000003eefddf77bef19000000000000000000000000000000000000000000000000003eefddb77fdf39000000000000000000000000000000000000000000000000003ecfd9f67fff30000000000000000000000000000000000000000000000000003dbfb7edfff9ff
  | 1, 7 => 0x3ffaa3ffad72e6000000000000000000000000000000000000000000000000003ffaa3ffad72e6000000000000000000000000000000000000000000000000003ff997ffabea4f000000000000000000000000000000000000000000000000003ff86fffa927df000000000000000000000000000000000000000000000000003ff801ffa92242000000000000000000000000000000000000000000000000003fcff9fe7ffff0000000000000000000000000000000000000000000000000003fcff9fe6b66c0000000000000000000000000000000000000000000000000003fcff89673cf90
  | 1, 8 => 0x3ffd11fffbaa42000000000000000000000000000000000000000000000000003ffc49fff92752000000000000000000000000000000000000000000000000003ffaa7ffbdfbff000000000000000000000000000000000000000000000000003ffa81ffbdfa62000000000000000000000000000000000000000000000000003ffa21ffbd33f2000000000000000000000000000000000000000000000000003ff805ffb9ab5b000000000000000000000000000000000000000000000000003ffd11ffeb2242000000000000000000000000000000000000000000000000003ffd59ffeb2642
  | 1, 9 => 0x3ffe69fffd37f2000000000000000000000000000000000000000000000000003ffe01fffd3262000000000000000000000000000000000000000000000000003fffffffffffff000000000000000000000000000000000000000000000000003ffffffffbefdf000000000000000000000000000000000000000000000000003fffffffeb66c6000000000000000000000000000000000000000000000000003ffd5dfffbaf5b000000000000000000000000000000000000000000000000003ffd5dfffbaf5b000000000000000000000000000000000000000000000000003ffd5dffeb2642
  | 1, 10 => 0x3fffff68ce74e6000000000000000000000000000000000000000000000000003fffff204e54a4000000000000000000000000000000000000000000000000003ffffe48c674e6000000000000000000000000000000000000000000000000003fffff204a4484000000000000000000000000000000000000000000000000003ffffec5c3ec8f000000000000000000000000000000000000000000000000003ffffe1bc247df000000000000000000000000000000000000000000000000003ffffe00424484000000000000000000000000000000000000000000000000003fff91fffffa62
  | 1, 11 => 0x3ffffe9773cf9d000000000000000000000000000000000000000000000000003ffffe8473cc84000000000000000000000000000000000000000000000000003ffffe12724794000000000000000000000000000000000000000000000000003ffffe49d6fdff000000000000000000000000000000000000000000000000003ffffe4056fca4000000000000000000000000000000000000000000000000003ffffe085655f4000000000000000000000000000000000000000000000000003fffff215acd9d000000000000000000000000000000000000000000000000003ffffe0152cd9d
  | 1, 12 => 0x3ffffffffbefdf000000000000000000000000000000000000000000000000003fffffffef76e6000000000000000000000000000000000000000000000000003fffffffeb66c6000000000000000000000000000000000000000000000000003fffffe47ffca4000000000000000000000000000000000000000000000000003fffff3a7e57f4000000000000000000000000000000000000000000000000003fffff207e54a4000000000000000000000000000000000000000000000000003ffffedff7ffff000000000000000000000000000000000000000000000000003ffffe9773cf9d
  | 1, 13 => 0x3ffffffffffee6000000000000000000000000000000000000000000000000003fffffffff77f6000000000000000000000000000000000000000000000000003ffffffffbefdf000000000000000000000000000000000000000000000000003fffffffffffff
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 236 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 236 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 236 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 236 then wireAt i else 0
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
  | 5 => 60
  | 6 => 1027
  | 7 => 2872
  | 8 => 641
  | 9 => 9
  | _ => 0
def CH : Nat → Nat → Nat
  | 5, 0 => 0xfef748adf68b4a72f5a4f138ead85079e5976888e52ad8a9e1548b33d7fc3831d34ea9dfd1c90f44c808d0e5ae713628acfc84caa748c8a0a35c9dd69ecc28d09ac615d191606f4f90b9fe6c8f4b6ac68d4e7aff8a0801968808a6cc84b2c6ee82970bb37f082b4f7edafcda7e840f7e79817f08708794376f19bae26d89224d6d7849276ce454cd6bb96a906714678b666cb1e860c4eb815f8ddb7b5dbdf6d45ad354c755985a5f553ff1a44c1b459648b12055485e3ceb42b779a340da2d8b3492314e33796f6931e8d3b92e31c080267200ee213dbd1320b9c3271850cc6f11a580bc0cf5ee480b1fab2b05a01c2d
  | 6, 0 => 0xcc62e6c0cad16120cabde0a0c51fffe0c236eef0b931def0b7002330b5c8d9b0b09be840afa84920a4512b30a1efef009e9743d09d0c57e09cab3ef09b6e9a20938f13a091999780914ff9e08f8b29208ea0cab08e406de080764f207e998db07e60a5907b40e2807acb22207a72649078bc61a0772c9e8075388ef07517d12066ec89b066e0be70660539806275f7305e4b9fb05a197e905941c82054f0a5e053f9f860512d1890505ca720416c31803aa83300380978b0365e3d00335110b03037b5802e06dbe0263132a0229104301c03b0201af582a01606109015801e0013f1996012946cb00c4bb5100bbc06900908c600059da6c0026e37e00054bc7
  | 6, 1 => 0x16771b7216718ae7166768e0162db144161c81b3160c315a15df18e415b54dd11525889515215ed914e0d35f149cc32e147b4953145964121436fa1214152387140c1c6114075a0513ff4e7e13c93bbb13967e2f1384a6d1136780c0135f48e41356a1bd13412e6212e0218d12b6672712a37ef012973a77125e755f12120e6711fcada011f45ea9119dfe10111f248c1101e7680fcf0a8d0fa07d310f8898390f46fe910f131deb0f124bee0f115ba20f02a2440ee2d2210eb903040e98ce120e7e15130e6b58460e6855b40e5d008b0e55716a0e3e12370e1cb4fc0e1685680e0ba9260dfc2cef0d8be47f0d6509840d4ae8920cf4a78e0ce13a310cc70a28
  | 6, 2 => 0x1fa0bfc01f9970c71f4d89821f3964b41ef049541e9338031e6f71cd1e661b081e5785271e4a11701e02d8001df679371d9c4fc11d66c50e1d49aee91d360a691cf504e81c96ea491c1146c21bf750b41bc7f02d1ba2f0771b99af581b6d57411b65139f1b254c411b24771a1b0575b31a9c820e1a959f931a85e0ab1a7844491a55d1981a43f61b1a3fc2e51a1f0ef61a01aba319f07a7819d5fa5019888e56197c4452197b07c81958fcab19426dab1937f12c18f54d0218f49d0918c1be6718b8018118b45e2e18af49f718649a4f1832f4c31827ba4f17baf8001725f0f217143ad01711465c170619d11701656116eb0e0416bc7a2616b5413616a1bc0d
  | 6, 3 => 0x2909547d2907425528e38c4e28d38b6528ce93e328bd5cef28a4a83e2891eb71288ee8df287956ab28732d7b28388f0f28035332280064ef27c4c54d27adaf2027907a0e2750b4f627490071274252af2713cf002705880d26ecc19726e8b26e26e23bf026d3ff3726cbdab126c09f4926b0cd0826acc7fc268556952629ae6e2603491925d32ac225b7ff1b251acd5d24b2a7bb24aa73a3249f6b482420522f240fb77123e3e51a23b5d9fe239a033b2360951f2356686b230b537222dc5fcc22bbb1f1229998fb2244ea16220fb33a21a6ca70213869ba2118e3f220e5b12b206d0bcf20292edb2021166620053c3a1ffb6b551fe241a91fdef7c21fbe5386
  | 6, 4 => 0x36695f8a3660102c361db8d535dd329c35bbb4cb35b4a5d535a96a4635916670355171d635099e5634fe1fe134dea09a34db039134af42f934473c39342a7ce533cc68a433bfc780333d305e3316142f330c3a5933053b0932fa2f9532c1a6cd32973ec632947f4f324db0f43247665231e36bd9317a69f6310f69bb30a9350c3099cb893093c23b307255b930378bbb300024392ffc33932f72e55f2f4925952f2d39052f2417652f092b1b2ef292772eeaa8122d8de92d2d75525e2d5c9c142cab1c642c71edda2c22e3092c1d4d1a2be61f7b2be3fc842b81626d2b271cc32b233a512a836aa22a71da712a41475529f1c6ed29eedbb82937eecd292f8a3b
  | 6, 5 => 0x4292f7574273161b4270ba7742115aa641cdfba641539b2e413a622b40f2455040722d16406cc11a4063e2793fdfad263fc20f233fc0c4623f5ccddd3f4f329f3f3c75c43f03b75c3ea27b1c3e9c32c83e5943583d9f94a43d513e8d3d4e642e3cc02c263cb53f9e3ca49f7a3c90e5203c4a4fba3c2f41443c21f90f3bf435893be08ad93b932d743b5f491b3b2afff13abbfa5a3aa25ffe3a66033f3a59b26b3a4fc2063a3e6b5339f21efe39cceaf8399bcfc139741cad3949f01a39374a4d38e11646385fd603382e3a70382d5f613827c47437c76af637bb82de37b9fc1b378d583937809ff03761c3f3376135eb36fe3fe736c6764c36a8c238369ccad4
  | 6, 6 => 0x4e3b10334e0610dd4d84259f4d6f6fcf4d40ae504cef4cf74c7b72804bf409854bb86ef14b42c94f4b41efc94b24895f4b17beb24af3ace14aae3b9e4a56b1024a4dcfc44a3a228249c0fcf449abc86549a9db37499b09a6493de9d2490aeca9490aa71f48e000be48cbb65d48558c394801046047e02fb147b4abff46e531e746e4d62d46ba812f468cd27a4659100f4642c44a4641fd8046361230461a5b9f45e6d9a845a7f5984553d9704551190a44bfc70a447b530344171c5a440fb91144081bfe43fcb21b43f5604343d9e1c143a0e1a0436382a2434ac0324348e435433c06d443275ba7430a1f7942fde88a42fbb3f542c4a4e542b779a3429d7e91
  | 6, 7 => 0x5c9148e35c8b3feb5bf6e8f75befc8825b796d475b3567f95b33e9485b17c0ab5ab959735aa8a6b95a657cac5a51b1885a2234fa59f9642e59c1311659254669584e77cd57a6f8fe57a686cf57856ccf577e2ebe5766e5cc572157c5571375965705d9ff56e8a09f56ae721e5687704a56802f075651fe30563381df5600878055df73815598098a551fbc1154f327b754de6a7c54863188546ec5c453da06d253b87aa1533ef3e9533e15335318541d52e838c0528b153a527bcb8052147bd852016d3b51ef2992517996e55104791b503d7cf7501d2ed7500d7df74ffd7cef4f6881884f5ddbaa4f3018244f1bb8244f0d9c4b4ebf453b4ead05c84e9582ab
  | 6, 8 => 0x6a01d59869dcc6f2698d8c3069846ed56939788468f79ab368eb1e256898b4e5688ea6bc687e9ce968264b4367772396675ddb146759339d6733942566e365b266b0725165822271657fa726654b05bf647c796e646c71d464591ab2643988c963cf9d8563669d9563395f8a6309db466282849662501bbd61c7787b619ad28a60dd2f1b60bfdce0609e13916089b30a608535a560741d37605307b3603f542e600575d45fe3d1285fc63bae5f8055db5f6c68fa5f3e629d5f2e81df5f27f51b5f2468c65f14a8005eed08085e9e0f5a5e7dd2645e511c6f5e4be6235e273f465da2216f5d903ee95d8c42c05d8c1cb05d71535d5d692e8e5cde0cce5c9c219b
  | 6, 9 => 0x784883f2783cf8ee77c20c9877b53d6377af6815777cb77e76f68eae76c913cb76c00ca7767c5d4276676d1f75e89c1f75d426907592030a7562807374e00fc474cf39e474b89a8b743d2db1742fd60273afffd273a82e6e7396326d7337295c732cd8d972e6c30b72e18a9b72dbdfac727718da71c45c0a7182e331716d65b470eea42e70e87d76705e5568705b5d9f704274da703a7ec86ffcb1086f9a52366f70d59c6f4297b46f1d63696ec03e9f6e7b828c6e6c39c86e5661bc6d7c2e6c6d00b1d96cba734f6c899b716c8466796c5c601b6bd565cd6bb1d2a96b9ebe4d6b9195906b8d563b6b63ee136b2b753e6b0981336ae721e26aaa55ef6a4eedeb
  | 6, 10 => 0x891d5143890f53db890ea697888e159488464f41883d4557883af1d1880106e9878d38738771b59c870b766e86e4511f86ce647d8687bc2f864f59148611bd4f85e097ab85d4451d85d14e8085642477850c74d184febac284743fba8436e17f82d5f1d682b74a9c82558bf181e9f85c817874d381556ecc813cd62381329d2980feb7d980ab13678082da9780377bfc7f8ad48b7f7b54597f78bc997f35034b7f3318f67f0ee6617f0d3e2d7ee6ae5b7e601bf47e21d4ac7d8ecad87d8ca7b77d2179b27d0486ab7c755b1f7bdef42f7bc2c51c7b4794bc7b2f7e8d7a700f037a5971ad7a1f520879e15a2879c0734279bf06b0794e884678f0b0da788d21e7
  | 6, 11 => 0x9be41d5a9b7186cd9b3436919a6181019a5041129a1a9ee099d1462f9947bb249933ef069907a25398db887398602235981fcaf497ac0d109795c1f9975635b6972eb7d796a96f09967a4d0a962a443f96181c3c95e3291b95d3ea0895b93d769546af70953b022894fdd57994d2bf9d949869de945fdd43940156cf93266c9892b8d6db9223ea6d9205c370919f4e7b91689310915bd75d90e2f044908c771d90484fc68f7a66348f6ee9598f5dcb3c8ed8553b8e8c69608e4d0a488dc553a68d8701a48d5eaaf98d3c57818d2489c58ccbd9178cbc07238c6170088bb136488b0ac84d8ae0c39c8acf54ff8ac846398aaa47758a81f0ca897c1ede895920a1
  | 6, 12 => 0xac516425ac3d3f99abce5f07ab5286c1aafd78a5aab01f51aaa3bf37aa881170aa879d64a9955fb4a96c3fefa964bd62a953fed7a8f52011a850eeb5a7ebe2bba7de44d7a7d551c1a67b5273a66d83b6a669c737a663c17fa6529d9ca621259fa5f793f5a5f4b976a5a6ca44a590843ba55cc56fa5229c1aa4a1ed71a495cd23a47ac71da4505ea7a3ffc12ea3ab4432a3ab4275a37fb9a7a2de2702a2cebd7fa2c08215a25280d9a1edb3e3a1b668aba140bfa1a12472aba0bbc0d7a05b43e5a045292fa03a41ae9fdab3c89f90b24e9f52393c9f0d993d9e7744839e65c6a69e2798469e137d329dc5f1299cf000b59ce854ff9c9fc8a49c7ea1b39c280e95
  | 6, 13 => 0xc423a3c7c4122956c38e21afc266fb96c25165c3c2217eaac219efd3c1fecd57c1836a42c1053da7c0b25433c07b57e6c02c7afac0179d13bfa40e66bf8705ebbedf2cdebe8b8beebe4be64fbe469854be43cddabe083947bd54ed31bd3c5e53bd37e00fbcbf7b05bc9e1780bbbf0735bb233dd8bb00ba17bacec824ba762a6eb9fd5190b929de84b8f18557b7aa0c84b72be490b6fd049db6b512f6b5640a2ab55ca5b9b53b7098b4e8bf3cb45ca86cb4107d9db3db5d80b36d65c4b3088cf5b1b0cf21b172b195b16cdfcab15baf8cb0b01378b065425bb029b9f2afa5fec7af4b6f81aead6968ae4f3667adddc41aad6d5218ad41f4a8ac8b0d28ac765d7e
  | 6, 14 => 0xe15651f5e0c471b8e0c02ca4e0823da2e0221cbbe002a614dfc971b9df3d5635de9c6949ddd3ac13dd734f83dc8a5345db3c061fdaa96d91da322574da2ef124d9af5a0fd94db765d8b15d8ad8a0ecbed888bab3d85bae87d8102e57d776ca02d7208f8ad6209a43d5d8361fd5571dedd555d26ed44f554ed34aae40d1267b13d0853c66d006234dce950d2dcdcfc436cc1f958fcb21a7facb1c4c97cb18ca29cb16c110cb125ab9cae2d399ca94a54eca5180ccc9f2a206c945fe97c8bcd3fdc73fff91c73579c0c6f642d9c6b917d3c6a433bbc680dba4c65a4764c650feaec5f86d6bc5736c6ac5650a23c54de09cc52c43f5c4b81a6bc4b67857c43ecf6e
  | 6, 15 => 0xfd4ecf59fc507666fc42f10ffc3bc9e9fb2fa769fb06b309fac52187fa401789f9e3036af9c0f926f9acd0faf9a10ca5f96feb04f8dbe547f8744bf7f7d9fb59f7767131f5fcd64df5bb4fb4f5b29c5ff5061260f47b805bf465566cf45cfbcff44935f4f318916ef2da6a70f2917365f25a5c53f2421a96f13a10def0f8df95ee13d9adedb06ad3ed80931eed2ae9e7ecae38b7ec899a00ec710b22ec1f29efec18ecc5ec164c1eebefca4beb922743eb1b78e9ea8804dcea70c2cfe8dd467ce82ca1a0e81c1783e7bdc11ae72131c3e6f5ef60e64bd45de4dd38a3e4849ba3e4102175e40c8193e389f5f5e2f6af66e2ac476ae2702555e239d3cee1e3cf1c
  | 6, 16 => 0xffcdc233fef0da51fdaa0749
  | 7, 0 => 0x3abb2f00375c6cf035eb4ec034762020341d11b033b05b5033a727c0330c812030d3b3003087e0402fa793702ecb58002eac56702e9d44b02e6b63e02e2bc3202dc927b02d6a72e02ce71bd02c16857029f514b029aef9e0296c1da0295a2700294122e027c6a3c02734c9f02620c310257db2702502c6702470b1b0240cfa3023f5c5b01f5db9e01c9b31e01bc332601b5ee8d01abdea401a6e4da019fd767019f361a019c9fad0198403d0185f46d01794b5f01652a32015fcb3e0159116c014ecf680146c416014268c7012a58400129b7550124c53e011c6a15011182d800f9b8fb00f5a3d200ea38dd00b9120700a87773006fb9d3006b9f230046618f
  | 7, 1 => 0x7ed8a3207c038b307a3436a079b7e0c0790b29f078c60020787d7a507492140071cbf990715437d0711d49e06fb5c5206c4413d06ad70f9068bc39d0681af190680b92c0665520c065dc92d065964650659598f065401810651b5d5064cb80906457cb906291d8306237d4e0622ad2105d4ab0b05c61dd605bbae7e05b8649705ad2f3405a9e53f057ed236057c0b7a05687e890555e1c60555b2b9053be8df0535f29d052cb0ff052aa4950525c62905169eb00507112004c982ab04bca65904aaa2b0048faf4c048cecaf04890ef504824cd40479bbe104608888046082770459b5e304427d3b043f87dd04253990041910f504015d6403cf5e0b03ae4e99
  | 7, 2 => 0xc2c14070c2ad96d0c232aad0c22507d0c0bf6ea0c03b9010bee5d4b0bd3d3cb0ba0f9160b985bbe0b88cc090b80dabe0b7f14bf0b76e6c50b5bfccf0b5376430b41c7720b2c8ce60b2912830b2179b20b09f3650b0896c40b05d34b0afb5dd30af89e950af197a60ae34fac0acf09dd0aca2ca20ab8b2690aad79ad0aa0caca0a83e0780a7e53d60a7e52a40a6c0b770a6426b20a5e33fe0a3f65910a0664f209ee1b6f09ede5f809e9743d09d9969709bd51ef0989c7c309643386093e7356092be94c092491bd08e6fd4608e4c69e08c6f6e608c6af2e08c5dc3f08b46af108739b70086d870f086695760865d84f085c29ce083004ee081c74db07f70b87
  | 7, 3 => 0xf808c130f8009980f7ac0e10f77871a0f56ffe60f53334a0f3a3da50f31b5270f1bfb200f1a8f2b0f115ba20f06017a0ee7b93a0ee271f80ee0af2a0ed86b730ed019dd0e90cf7c0e8414b20e7e15130e7dd0190e7515ed0e737a980e6855b40e67dc250e39d93f0e38b6fe0e1f184a0e05ccb20dfe576f0dfb96ef0df95f9f0df565b60df435510df1ea5d0df124ef0dcab45d0db9c7830da962390d9cbe430d9a92370d91ebc20d7f85ab0d61f2fb0d5a81df0d50aa5b0d49c4170d40e0e10d2d22890d05cbda0cf439bf0cedf22c0cedec0c0cea20e10cd4b54f0cc21f430cb5970c0cabde0a0ca165b80c825c970c6ff3780c6ed2f30c687b0e0c59d466
  | 7, 4 => 0x1308cd7712ff424112de738112ddb43412dbba7612bb814412b8ab4112b6672712ae5da312aabf8d12a8595d129e663b12763853125d0b7e1233466a12300b711228cbf912245a68122261f8120d1dd3120061e011f373c011d640d011c1f92a11bd50f411bbe12e11ae78c2118eca2111676f9f1160b3bd115b67ca114c695c1142fa4111408e9a11266cf51106ad5710de35ff10bf6ca610ba9063109ef9a3109bbfbb109410fb108ef5b91087cb5e107b573410720504105861cc1052a2c5103a9912102d648a102c2b4a102497a9101f34a2101595881004221f0ffdfe370ff073950fec104b0fe0ac610fcb33c20fb1a7760fa2a5570f9aa5fd0f8e38f6
  | 7, 5 => 0x16859a0f1673385e166385a0165ce3e916528f35164042a2163cc6661612f34116118174160c7aef15f4eac915f3a94215f022ce15e9498b15d3ee2015d3b4e415cb6ef015c9c2b915ba6e6315af65f1158c470e157b3ef61572207d156445b91561a43a15602014155ed0bb153fc09e151b16a515183b8314e2d7e014db292014db18b514cc203914c7c3fb14c0d43c14bb7bf814a3cc181490fa1e1488b1fd1480f23a14696ac21460a7d914466a8414338b5a1420fefd1415063f13ea83c213e0e2a713e030a013967e2f139302bf138402851375dc6513728f56136dc9041368a9861359be09133c08ef1330db9c132af56d1327edf61317dd2b130a5a89
  | 7, 6 => 0x1a3d73cc1a39c2a21a33b1c31a2594481a1cf3441a0dc40d19fd5caf19fc1ed919ccf3f619c7c79119b1d44819a917ce198d98701980bc29196a58b8196672e119399e181933a7b61921f28d19169d3318fa602618f302eb18ef4baf18e5fa2518e242ff18d274d918ccee3b18c40ebb18b0c2f618ac994f1882b1691871d5381860cf5518595dba18545dd6184ab457183afea71830634d18261f78181c7acd1813153418043d6917e170dd17ddd95917d9c21d17d64a9117bf920f17bcd81e17b7e34f17b77a5217aeb25017a3f1f5179c6b23177ea021175c2c75175a929b172938d71712096e1706ecff16d77b9d16d21d8816c91dcd16bceacf1691aff3
  | 7, 7 => 0x1e2d04af1e0aec781e08e1531e0576261de95c481de45f961dbe4d991db574801d98a19b1d948ff71d83b5c31d826c881d81c57f1d68e5f71d5bd8171d4a9d981d2d215e1d2a81d31d160c6b1d07cbc61cfd2fc91cd93b5f1cc5aa5e1cbf657e1ca81a3a1ca481c01ca0b1831c32bad41c1ffead1c193f401c0c1b4b1c03a2d41bf725aa1bf5be811bf04d8c1bea35011bc7d4b01baf8e761babf2e21b9935371b98c1901b8548e61b78d4bc1b55df541b52f3321b5233871b504a801b4b11361b3c1cc21b27d2611b25678b1ae9b4a21ac819931ac6e6c71ac6cf551ab658ae1aad97251a9f19ac1a87fcc01a6b63331a63b4731a5d20641a58a2341a426dce
  | 7, 8 => 0x233e51982325c90b22eade0a22d85c9a22c7351322c4f10a22b6a37c229eb02f229998fb22986b962289ec0b22805475227ea68b226fd9842257ddbb225693612241e41521e6cbde21de28f921d8db4721c636b821b9f7ae21b889b621b5c2d421b135b521a5f9682177d4282145ca59213bddeb20e249a720df43cc2062e284205b0a2a203e86e9203dbfd6203ca24720292edb1fed21a51fecb1011fd3c25f1fcb8bd31fb72b911fa565611fa432931fa23c8a1f9874111f87b1c01f5f0d481f4cfea11f49539e1f47d9851f3e5d811f3387171f3108e21f15ac8f1f0bc3bf1f06a07c1efe2b8f1ed94da01ec0fa371ea663541ea60e4c1e8c48a51e3c357a
  | 7, 9 => 0x27c1256227b32aa8279f070c27795cd1276d7c64275d8171275b976e2753b5b4273e087b273a86802713cf00270f91b92707a0fd26eeeb7b26d0c80326beaf6f26bb2fef26ad119126640762265b050526580cbd265363bb26396ad4262a32f426146422260a164f260932412604931525f85c3825d992dc25b5bed225afebbc259a3137258a6ea4258a599a2578e98e256dcb2f25685a9d25471fea2517e46e250aba5724fedf5924f9d1c424f9338f24f59d0824f27cee24ef47cf24dd90d224c9ba2d24429b14241b265d2416c07e241577b923fe5bdc23f0c29e23f07cfd23d675a923cff39623aa74da2389374c237418ee2359c6d02353b18e2341f140
  | 7, 10 => 0x2b15a4b82b13e5c22b09ceab2b01a4c92afee4492afe09d52afda44c2af68de12aa00b9d2a9ddf912a9588c32a8e42722a8c3c9c2a6f28832a6cf0712a6540552a6347522a5617002a4993872a42cf9a2a4238582a2aa3142a222ab32a147f222a023a7d29faee4829f9c57229f5789c29ed6e3b29e942c429e8651229e188d329e0d67129da34ba29c478db29990f442992b93229740e86296b38aa296af49a2964176b295a32ef294399dc29428e4b29342757292af8b7291385ac290f977f28e1d56328bd116f28b13185286b03f0286028b1285879f1284514cc282d4cf428233034281a4d9f281909f628170bbb27fcc31727d2573727c4c54d27c3516e
  | 7, 11 => 0x2e8ed5cd2e8af7a22e8a65942e5a45e12e3b996a2e38cc412e28d5a52dfdbfd52df877932dda71352dd75a262dbac35e2db7c70f2d9f970e2d93a3d72d7fb2cd2d7d41f82d75a53d2d6d756d2d618f3b2d52d1502d4fca342d4b28f82d4518622d3ff5e92d3e70562d3a56d62d1bab3f2d1995702d06d0c22cfe0cfa2cf8cd042cebd1e12ceaccf62ce139a22cdf3e6c2cd4f0ce2cc795ae2cc4f9662ca929c32c8ade412c86b1b52c7afb6d2c658bc92c611b6b2c58dac22c50f8382c46203c2c1d4d1a2bfff1562bddfa782bb5fd6b2bb3707a2badab652b81faf52b81626d2b79d3f12b5f77182b5913022b4ef7cf2b2253022b20b3d82b19bbf42b190388
  | 7, 12 => 0x32ba82ac32a1bcd532854622326a54943264f194326007a83252e2e03247653132440aae3241705c3217690131f5eab331eba44231b1ab293196b9003177ea8831752de731660f0b3163f5333159aba1315024ba31389c993129ad3f3122199e30f0dff530eb45fe30ea9b5c30de567830ddf49130d5282030be0b3130a324b4303f34b83031f37d302ef15c302ca7773028fd26301b2a85300c1ad12fec250b2fc6445a2fbf35272fbf30b22fbbf89b2fb1aafd2f8f1ff32f8af2362f86b33f2f8141142f74af282f67316b2f5e6cbe2f599f622f3c81e32f3594f12f2cdf472f20329b2f1d2f5b2efbd9642ee5e2102ecd9b512ec68d272eba05a82ea52332
  | 7, 13 => 0x3615bd7836126244360938793601d28435f2a55735e7486435d89aaa35b550f335a0b6f0359f67e7359275fc358833f83583f204358164d83579865d35787e26357193a63555047a353aa3c63536fd9035239d6d35009d3534f524f934d2fbb734a750a9349995fb34886bc33481cae43481847a347c735e346ff1c93453b6c5345378db344f47aa34487e12341720a334171dd834064f6c33e6b2b633df688433dbf57633da662c33d93c6b33d8677333ce134333cd72f733b6f9a3339be830338e027c33864f1f336a01d2335d819533511330334a7e3633422da5332a82ad332a0277330bca3f330a8e3532fa2f9532e16b8932def36c32d045d132cae7bc
  | 7, 14 => 0x39f7e21b39e99ade39e1752a39de4fb639c6347939bb3ded39b5e92239a3fedd39a3264a399f4d1239731d65396f572d39631e873961b02b39579c0d3956e3ad3926b9f839234c0738eec90038ed825b38e1a69e38c8629238c6876638bbb164389cbe363899ed183896221738889640387c22163878ec6d38695c3f38422411383a0cba382f747e3821da66381fcf143819736d38120974380d7bfe37fdfb7837d8b58137b9fc1b37a4666c37997d533797a68e378ba63f377ee72537596ec33711116736fb367836e2575236de7a8736cd76be36cb597836c744ae36b5383e36b4de1a36aef877368990f73679dd0b366fa2723664870336273865361d6c38
  | 7, 15 => 0x3e277fff3e0be7f03df99e973de291263de1cf0e3dc32c533dbce7733db4ca0c3d9457913d8a3cae3d820b7b3d6b3d603d67d4943d3e89f93d2562093cfeefc53cee74523cedcf813ce437ac3cda06bb3cd396533cbde0b03c9643853c82fc633c7e70e63c38e0113c346cd83c34563c3c27f8ae3c1036413c0ce04f3be497a23be08ad93bd6ad1d3bcc8c933bbe60cd3ba7c5f03ba5ac113b999dec3b945c8c3b9031bd3b795ba03b5624293b4bea9a3b36b9843b1d6fda3b0db0ad3b0a44b33b08dcd23af6ada23ae826bb3aca75eb3a9a85bd3a8dc8da3a8cc1993a8b1a653a822ece3a6924c33a64e63a3a4766343a2d6c623a2d4b6439ff1f0a39fa66b0
  | 7, 16 => 0x41b8ea3b41b5ff64417fec1d416e44234164b8404149098f413206594119dfa14110f4a8410d769640f6a5f940d32ec340c96f0f40bbc12740a60e3740936de14079f6e6406f21e9406c7db8405ffdff405c8f3d4052419f40455b7a4042c3c840419ef2403af74d402fc56c400945b43ff4ef3e3fed881a3fe60be43fe000373fd72a663fd62b933fca826d3fc294503fb404613fb101cf3f6aee9b3f6a09b43f5ccddd3f5aa7ff3f5789763f55675e3f545ac33f4622693f4602c23f39b76f3f3721633f2f2fec3f2afc363f227ddf3f1c7b813f15457d3ef9b7083ef484683ee6de3d3ee3a83e3ecbdd503ebac68e3e8cd15e3e791ea93e3c0ae43e3a3ac4
  | 7, 17 => 0x46e4cd1646df279b46cefcc046c9322546c7cf0746a6e54b469949b54687df06467c9b5d466764c54646305546405d044626019546230322462000d24606ca5745fdca9c45f6b584459774c24526b4084518840f450ea01a450651ef44fe769744e5077444cd758b44ae84d94493839c448eda3a4486548a445fa72e4454cdd14421817343eb0c0643e53fd843aea1a44397d140437b17534356b11543555fb0434ac0324336d2af432dfd824325dcc44305883642ef746f42e7b5af42c7651642bebde742b779a342b451b04270b5be425bc8a4425327d7424d728e424b54c0424083084221143d4214fad14214c55a42100287420d2e5641e2fca641bef0b0
  | 7, 18 => 0x4b2472944b226b904b17d9624af8703d4aee81944aee73794ad1055a4acdf8d54aabf4e84a9a544d4a77d2104a463e7c4a44957f4a3ff2504a2e53494a20e91b4a1e61714a0d19744a0125c049f3d2f349e3bfbd49e125c649d9a14a49d72e8749b6983f49b3eade498effba49827473497e1ccf49787d01496fc9e4496885e5495445924951a0134939f530492acee949292ce2491e4f5449148db0490584c948f6d72e48f0ff0048ce78fe48b568f84850b42848401890483afab94833939947f8a88e47ee69e847d7f35a47ba59f747a3d52347946ea9478f9960476a5be9476086824755b8444727debc471a541a471718c446f43ede46ed067a46ec901e
  | 7, 19 => 0x4f19bfb24f159ccf4f135c524f086f2e4f0494734ed752244ea817a54ea4fa1c4e9d19034e7855394e7327324e6d16534e5372144e3cd4e24e3b68614e3b10334e3a3a904e2cfa994e2566f84e20ca5e4e1717654e086b364dffcf964de2370b4dc9c7c04dc27b5b4dc0f5744dace24a4d8cd6aa4d77b7814d3fd1c54d3c580d4d2f3d364d1d57c54d159afc4d0fc89b4cfd734b4cd6bec54cd4ecde4ccdf14b4cba876a4ca859dc4c9d92c64c77c2484c7463374c67af984c578d864c4ab93a4c46545e4c1e35cd4c173de94c1326ad4bff26be4bf147df4bd8a0d14bacc54f4b81ba084b77d19c4b6978864b6231954b5e75fd4b4dec0f4b4c4aa34b48acc9
  | 7, 20 => 0x53155c2b530ec13f52e71d0152dbe80452ce9ec252be5c11529e18cf5295c35652943af5528ce0195281620b5257aedf5253af2952534f94524e709e523dc211521d854b51ee61ea51e81d5151dd55d151dd438d51bb2a0f51b5c51351b50144519006da5184d1d451761d5f516b02655160844351501bab5136a9a35133fceb5122fc1951222313511f563e510a33e251099cc65102a7f450ef354250eca9cc50e499dd50e23594509f5416509f358a507c4096506b190f50694d92505beeb35059633d50490acd502b2686501f9e51500139404fff2dd54ff820184fb50f3e4faafd564fa260824f9d1e774f8c57c24f7141a24f5ddbaa4f49dd644f1ab65b
  | 7, 21 => 0x592e72415927b4ea591e47e658eb4e3858e3d83358b5610058b3c4b758ae4c9d58a9df50588df5d9588269ee58761ced585fd55058597183582969ea57b2600f57a487195795fc8d578e67bf576d4781573f8ef45727b7f45714852256d3b3db56ccc28056c5d00a567ee6cd567eb156567c7f515672b54a5672a487563580cb562261c85618ad1555f35c3e55c07eb85588bc46557f4cd9554910f15530a86c550188a454fd3cee54f251df54d9fe7754d1dacc54b8020854b47b9854a00c23546df95f545f13eb54324e155423f49e541e6d5154198a3e540a4dbd53cb534053ca9208537c0e455377f3e65372efcc536a15075361a43253466db853447d04
  | 7, 22 => 0x5d7bf2db5d5fdc975d5624535d53729c5d48a8d45d38329e5d0eae245d0b15675d05efb15cffc5445ce551125cde0cce5cb55e505cb45f9c5c9fbd605c91de815c7fd5c75c6fc8965c4918f65c3f74815c3b8dfc5c33c1815c32b9c95c1f443a5bf13ab45bc0ce6c5bb639285bb357745bb301c65bb03c075b6b6fdf5b65c3955b3bed485aea31985ac679ad5aa8a6b95aa52f8d5a9f5dfd5a97dc395a97a4eb5a9469955a859b925a8322685a6fa4e45a6d6fbe5a6afd255a255bc05a1dcce559fcbebe59f4dc3459b5104759a1fc3b5999c0685996f4f55992d367598cb1c5597bfa89597aa112596e2a09595c195259483db55944bdd65936765a592f0198
  | 7, 23 => 0x62623a35624ac82b6248b0fb6240770e62290a7962261eff62256876621d1ce6620aa7726202e0dd61fe39a261f427ee61de9b7b61d669a461d0c2e561878faf61874d906178b77d61761d2b616fe8b46169ffad613f4bb660fbe7f960f47f6c60cef2b260bd229660b772cb607f1ebe60778b6b6058ad0a604693fd601d48af6012a1605fff9ba05fd7d1ae5fd0ae2c5fbe37825fbac6fd5fa8e5035fa001255f9873855f871fd25f416ceb5f27f51b5ef408b65edbff035ed6a3f15ed000cb5ec5fd9a5ebac33b5eb5ede35ea93e185e82f8175e8158065e5e95475e441ef45e22a7545e13ada65dfe16575df48b685debf6475de083ce5da6d4765d7d6e2d
  | 7, 24 => 0x672edba167240676671066ce66fd841f66fc748866e5ae6b66c97e4e66c9726066b3abb5669a488666730cef6654ed6d6644c8f8663dd1146639b9d8661f8dfe661dc2cd6617db0a660b8442660a815d6604d30365d6d88f65b3f9f765a82696659df39f658f322f6566e4ba65524fc6653364ff6532bf6465291588651f0368651506a464e6ab0264e5083664bb002464a0c73f649ea5e064789948646b28aa643ac4066433ac9f642e54a0642d74f3641ca4e763fb6a7f63e50b4763c9dda363bad2eb63b3242b637c7ea663669d95633b61f76320cbf7631fb15363020dca62dfa08f62da87e162d73fc862c980fc62c7c6f462a49cbc628e144f6285bfff
  | 7, 25 => 0x6bb065b86b76748c6b67104f6b37a4776b22b0746b0959bc6ae97d196ae5c9b86ac5c8b56aa508c56a92584e6a923d956a91b37d6a8f01346a8281de6a8097696a7ff6686a610cd96a4320db6a2e06a76a0829146a00c0a569edc24469da0c1f69bac96869b37b9c69b2eaed69b08c9069ac572569a63de4694fc71e693c91ca69250df3691674076909bb4668e9f86868c3ac2e689dea7d6899ba5d6885fcc0687ad6bb685b66c76854735f68439ee9683daa90682efe61682a009568201ef1680dfb0f6807b67667fd902f67faa20867f05e3367e0419367d9415267a3bf0d67891a306785247967841837677d84d867770155676bd0616733942567322581
  | 7, 26 => 0x705b5d9f703b7bb4701fd290701d07ab701838507005f1236fe598a66fbb45706f9a15cd6f97884f6f7770976f7090bd6f6fa41c6f6a8dfb6f30b76b6f1deb2a6f13e0ff6f0f44366f0638c96ef1af446eeb6aab6ee8713b6edb0ec36ec28c856e9f9b6a6e7acf386e5e503d6e4a87c96e16b7eb6e0e67d66e0d4a906dec12c46de93f766dd08b0e6dc17e2d6db3cd8b6d916c166d7e78d66d7b510a6d79ee906d65318d6d5f3c0d6d483b2f6d3b7e216d35546a6d1c77766cfdbf986cd622c66cd111a66c96b4706c6129046c4b6e046c49cc986c41d5016c2bf7316c22b4c46c0eb07c6bf899566be9fecc6be54dcf6be1bd3a6bd3e8686bcb63fb6bba0480
  | 7, 27 => 0x761a42bc7613d46a760760367603a98f75cfa8b475cf5cc1758d3ff4756ef7e9756b3d6c756948e67557aff175576ffc7554e38675404ca07539d269751532dd74ae2b34749998787485a1e9746a0e0a744ac9477408724473fa28f273f993ba73ea5b6e73be3a8b73bb0159739a99807396326d7393454b736647aa734eaa0d73275b5973251f9b7317072172f6a99872e9411572bb7e8b72b28339727f14f3727daf3d727718da7262aa5172542ac6724693b77239d99b72301b0f72286c4f721cd83371fa161671e12dcc71d8f93471ca317b71b7c8f2718aa31d7180018f717f4ee07166cf87715dd49f71442cec70f943ac70e34a0670c13a81709d46b9
  | 7, 28 => 0x7a2055bb7a1945af79f05dc079e5550479e15a2879d3e13a79c2eecc79c02f7279952bdb797abaaa79717a8d796fc1e1796deb3979684f627961f727791c125478efdc9278e9916b78e4358b78b54ae2789257757877b053786ea1ff78493a7f7847c1c27819d385781289727812071777d135d077ae3ab077abcbfa77a5fcd4778560f7778424c2777d8546777652a77753784a7746c8397730263a7723c8d077231e6a771f39f8770f6ecc7705d5e176fe097576f0de3376f096c376ef06c676e1a5f076da66f976d6e32176c379d576b871ac76ac7aab769ee490769e1cc8768e81ea766e04be765bdd327654909976509acf764e5f6176461d7276374491
  | 7, 29 => 0x7fa5b96c7fa0b5d97f9245e67f8776eb7f7ed9fb7f7db79c7f7c17707f7b54597f75ea277f65878f7f5f0e0b7f4ff8037f36f7307f24c13b7f0df4cc7edbceae7ed513f37eadd0e57e7a7cc27e4b58517e28295a7e1a8a567e0b20667e05acff7e0371a67dffd2af7dfd47397dfb85ac7ddeb6337dd765af7dd747b97dc60fd37db1e1917d7d57bc7d7b98ea7d76052a7d303bbe7cea112d7ca8786f7c8532d27c70c09e7c69c65e7c4bfba17c1abb197c170b2e7c140d477c08287b7bf865d47bf0d3337be9041f7bb2ffa97bae10da7b86605a7b03a1367aface357aef43a17ae6a9707ada8ab67aa157477a8ef3507a7f40357a5b787a7a36543c7a2bf436
  | 7, 30 => 0x86bb689486bad95e86ade39786a525ae869b7594867726a1863f7c59861a00e9859d9b7c858e52b8857f1b66855ab5528527bd3a85184ada8505aadd8504759484f5077184d7d6fc84b02f74849e475c848fc39c84594c5e8450d9fa840799a683fe99eb83ea69c583a2a62e83a21eb1838341f48376102a83629097833df9038323a63b82de711782d3eb9982b3ae8082a904af82a1ab69829ec1d68295aa1e82585f9481e62af881b76e8e817be6a28155958581303d8c8123ee8880bd751880b8cef280b2da9b80977014808528c4806ec49b8068a9ba806266ad80478751804124a9802ef197800c7ccf7fe516d97fdec0a27fd8b9667fca544a7fbacdd5
  | 7, 31 => 0x8ee425888ed973b68e9fcbf58e965ddb8e3f8c778e2302ba8ddbc8d68dc0b2f38da6f0c78d5eaaf98d1b84e68ca456c68c47b39e8c3f36198bee01d98bc68b508b8fda438b4da15b8b1fd6d78b080e6a8ae7ae958adfa09e8abb56b98aa94ae58aa3b04f8a59424c8a4b2c568a0b34fc8a01f36a89e77a5d89ba9fdf89aca4de8983c187897c1ede8974814d895920a1894ebb5e88fc0ae588f823fd88ede02888d9be1688c15bf788ade08988a4fc21888f7ea48866fcf1884d6a8e8824c1658816e94987ea0dcf87e75edb87c7d78887b2ceb4878343c2877779c387648dca87526f628749a55b8733e75f872dc005870803528703169686fcb5f186be95e9
  | 7, 32 => 0x960bb76c95fda25095e12b3f95c0f43f955aec719547a30995397fd29520bde994e8477894d4832a94c3179a94b8834e94ad8e5d94ad81c7949f308d949bdb7e947d9aae9473849994302b6c942a4f2093f91dd793f42b8d93f0934d93e24993936159ab93602c46932ed1f79322c346931be89e93064ed592fea01592d773ea92cd311e92a8f8d2927fc7e7927d8384923130829222139b921c7d4492002a6a91e8ccbe919ac8ae917fb21d915bff5891503a30913f5441913e5b3c90e225fa906d26119066fa269049058a9022657e90061e318fe77d2d8fb5d0938fa972eb8f980bea8f82febf8f76ecae8f74f0a98f5f11de8f4809be8f34486f8f20258d
  | 7, 33 => 0x9d235cf89d1f09df9ce7c5ba9cd916209cd0c7aa9c70cc409c20d3b29bcb613f9bc7f7b09b6cf8b59b58bf3b9b42e6359b34b1219b0094939ae5da449ab78fed9ab52eeb9a8abc959a6914bc9a07492d99f80ac699eaf18f99d7582f99d6685399d3056b99ce680e99ce129a99bed3f9998cf53c998829a39978ab009977a4e199265abf99004fbf98e2892c989a8dc3988d75f4986d00ac986b97ef9854b6199848d5ba9848610497ec88bb97d41f8597a9fca097a53cfb97a4f3879791a64097885ff99775269297708ba5973a7c869713ecb197012b8496f60d7996af9ef8969aeb72968ac1e996867f0f967fbfcb9667f9e59661aced965531e69630ff51
  | 7, 34 => 0xa39ec2eea390017ea3814b1aa376dcaca33b889ca3219133a30d2ce2a2f7e86ca2b3fd1fa29af479a296a4d8a284b47ea27f4475a26534afa21dede4a1f16defa1b25c0ca170cb80a16c4690a1662bafa1558ee5a1521c33a13f99cfa12818cfa1034345a0d05094a099d7c2a081de7aa07b3991a070175aa041465da030bf87a0178350a00b64c3a0092fe09fd738f39fada3039fa7e8e29fa2555f9f726bb59f6868319f307a4a9f22e88e9f1c706f9ec9ae489ea7d34d9e93ebe99e64b9f29e5fc6b79e5adc459e4b2ef19e43f1059e418da49e3e2dc49e1370af9debfd949dac490d9daae7359d9a91c89d99351f9d6bcef59d609f369d413caf9d33d63f
  | 7, 35 => 0xaae6feafaaacc2cbaa90e0daaa8df529aa75a9a3aa732844aa43ea8eaa1f6e87aa0d8b20a99c3196a9647ee6a9501df1a946035da8e78fc4a8c9d8aaa8bca6e0a8afe02ea89eb231a893279da828f69ba81a824fa7e69d5ca7b45be4a7470e27a7060bf0a6e98352a6910249a65c3616a657cb39a656ba0ba6563cc3a634fa8aa6193286a603d2e3a6002f5da5fb7157a5f12d82a5d7dbfea5d7b751a5b36a13a5ae8250a5a6ca44a57519cca56effffa54a6a95a54844d2a5160ad5a5141b3ba4c7accca4c4fe3ba4ae7b11a4a20be6a4a02823a494c22fa4943c01a48c1ccba47a3dd7a44634c2a43fb431a411e8baa40b50aca3f2435da3c1ab4ba3a56a26
  | 7, 36 => 0xb2e06130b27690e8b27560a3b266fd64b258530ab20f961db1ff7463b1bbd0a8b18c7b6cb154aaceb0e1dcffb0d67463b0d5dbb4b08e74bcb08080b4b06379a0b02ed722b028f5a0b0231954b017831cb006be1aaf9cc68aaf80d0deaeec8abdaecc875cae9f7f72ae97cff6ae948155ae919a49ae68ce65ae55a6dcae42a19bae1bf85dae18ff3dae11518cae064aa9adf1a5e6ad9c65faad4120a3ad3bbe89ad3b090dacec63f0acb48d9bacb48a93aca9b064ac9944f7ac7b9e87ac765d7eac623d5aac5d1b18ac59c64aac54c35bac517041ac41cfbeabe5308aabdf356cabbe6e52abbd86cdaba1a31cab9f69a8ab81f633ab227451ab213bb8ab193334
  | 7, 37 => 0xbb584dc2bb13bee6bae1c4e0bad4da24ba88bda4ba231cbbba044b94b9fe2647b9e4f0ccb9e29b05b9df8830b9d7cf39b99d8907b985ccd1b932cbabb91d4ce9b90994d0b8ef4caeb8d90467b8a7f061b88c0434b862d891b7a667eab79ef288b78864c3b782175db7694f48b75d88c1b751bcc3b7186549b6fcccb8b6fb2445b6f964b2b69c07f9b691c424b66e795fb668942eb62fb22db62922e8b623fb60b60f96a1b5f36f3fb5e82352b5b29b6bb5995d73b5417191b4fc8e64b4e939afb4b954c9b43f5990b435aab5b432738eb4309820b41b0a9db40478deb3e7728fb3c1e194b3b09514b38e0f43b33f92c7b322ff62b3152a51b30843b8b2fc9eca
  | 7, 38 => 0xc496691ec48fe98ec4789a6bc4038d0dc3f9cfc3c3e38b32c3e2d77bc3e02969c3b9c3cac3ad2618c364d83bc3606443c31b6fd9c2d42780c2afde01c27c2edfc25c674ac20018d3c1fa1783c1ebf1e0c1a3757dc154e976c12c896ec1053da7c0d8bcdac088640ac019afebbfcb863bbfa35d49bfa2d939bf8705ebbf7db259bf08b98fbefa2055bede1fbabec33186bec0a575beb5a966beb226a6be584277be4be64fbe3add0dbe110a0dbe0ade22bde0f6a6bd9159b9bd82ee2abd712593bd6a8f7fbd686373bd386403bd376e02bd20e303bd1c3529bcdd2ef2bcc91ac8bca06181bc87e6edbc5031b5bc0c7999bbe49247bba66d37bb80d0edbb6820b3
  | 7, 39 => 0xce1ee8e6cd93f135cd4f96bbcd4ef236cd28ef85cd19d01fccb4b64fcc9fe01acc6e82bfcc5ce581cc5be40acc1a159bcbfd28a9cbb9f257cbb8df08cb868911cb5221cfcb46a5f8cb2f7209cb20c46ecb09853fcac2eddbca8e6379ca5180ccc9f2a206c9be5be9c9ba28d5c9a3b4fac996b3b6c96f57afc93c7368c927feb1c922e551c8d8951dc85e0905c80b3ca5c7dc9478c7d22c68c7bdffc1c7b65101c79abe3bc77b3c2bc7718d50c7327c7fc6f83f69c6d0b208c6a9d361c682e025c667cc40c63e6ab8c62aba48c5ff83fec5eadd1ec5c1d047c54fca04c5368674c52f7576c5275d01c5057f75c501ec89c4ffdd0ac4e09fabc4d20e6dc4a50f80
  | 7, 40 => 0xd6de8f0bd6c78025d68b73c0d5f3eb55d5e66ef7d568ff65d568b144d5583fe0d50e1adcd44635d3d41db420d4001a12d3f10f9fd3acc11dd3a84f1fd3a13996d3958842d3647f59d317dc6dd3039b18d2e0b7d0d2c6073ad2aeea40d2a62dd6d29440d5d28d9f00d26e2c13d2440c1fd231461dd22c953bd222b1abd2069bacd1f83001d1d3f658d19a03c6d17bf5cfd173caa4d14cf655d130dacfd12bc740d0c5752fd08863c9d02e62c1d0188098d00c244bd006234dd004fd63cfca0951cfbda896cfaaeb5dcfa1a4c1cf9551ebcf8f1c3ecf402390cf1f3ed4cf18dd1fcf010deccee24fd2cec46a5ece8ab657ce816823ce540370ce515e0ece1f1d8d
  | 7, 41 => 0xe1283faae1151f08e0c471b8e0b9173ae0800c8de07b344ee050a6c1e01ebd33e0129c16dfe22038dfdba1afdfb32b5bdfafa89bdf8ae938df1659addeff409cdede789bde86f571de7f46b1de4eb049de312a05de272600ddf8e307dddb30c3ddd5ae60ddc64cabdd9de376dd1abbaedd1a865bdccf1ccddcc1922bdcaf7ec7dc1c3838db9e5b95db83fe16db6940c7db43194adb3a67f6db29855cdaf2339cdadff429dab03a9fda1bab7ed9fb6b94d9eccea3d9b71400d9891486d96359b3d93db002d920e647d8f7e852d84ccd00d84bd8e7d803eed7d7f9e631d7b99f14d7ab2662d7a5749ed7783301d76d9a26d70862e2d6f3fc90d6e908b3d6e8f3a9
  | 7, 42 => 0xed3bc136eccef605ecb660fdec9f3c4eec9d1042ec989f45ec297df4ec0915fdec04ee7feb6f4652eb1e533ceb15098feb104fbeeb06370ceaf7f023eabec0cdea81aee3ea6cc730ea630ca9ea5d5ff0ea44457dea39f55de9db2321e9500fafe93d2869e8da166de88e9a99e878be20e82d725ee7c700b7e7a75556e7283c3de6d0b57ee6ad2c24e6a5d5d4e65393cae5e351dce5cb74e9e5c2ba49e5b7261de5499e93e506db91e504ee61e4e88dfde491a641e4625a30e3d420a8e35f42cae34c8c7de2aad18ce298b8f8e281e22ce280ec37e277b2dee25ab921e23cf087e22a0b63e20f79eae1cc7a45e195a639e18ace26e15042f8e1489438e147418e
  | 7, 43 => 0xf755edc8f74f43f7f6f01bfdf6e5cf63f6e3f0ecf6d3dd00f6260c95f61ecacef5b78cf4f5ab4c3ff58f108cf582e6acf5735d60f4f2a0d9f4ebb8c3f4d74db7f4b53ab9f48476d3f4642245f3c06a7bf3a1e699f33384e5f32a1730f31deba9f317844af3165413f2f3ae00f2eb8b36f2c41b18f29b4df7f2854adff26e460df25e1f0ff20c2781f1fcdbc4f1ed8e22f1d45c2af1c51099f1bb294cf1b0dbaef1a59475f1856302f15a4793f1510a14f134c5a2f12be4b6f0796c34f02597d4eff86bc5efdfd1c7efd4f348ef831902ef013f34eec40f0ceebe9aeaee9ef80aee996037ee365bcfee02495bedf18711eda7feeced80931eed7d44f8ed56b179
  | 7, 44 => 0xfffb2919fff37a59ffcceadcff9ec55eff6dda91ff55b127ff3e3073ff0db492fef288ebfedfda0afece09defea58edcfe2a185cfd7e81a8fcfeb677fcf063cefcdf86a6fccb4487fc84438afc50f767fc43d33dfc1a4b00fc0b585bfbf6516cfbefb591fbe1c5f5fbe0f7e9fb2fa769fb227cb8fb195303fafc002efaea169efaba4034fab495f5fa7d76fdfa7b52c7fa641ed8fa55713dfa54b192fa27e596fa1c6652f9b99d75f9acd0faf96feb04f94691eaf8eb2a3df8c7e701f8ba5c5ff8b72109f8a016c6f87e7dd9f842bddaf83a440bf7e68aa8f7e6759ef7a45692
  | 8, 0 => 0x12b8ab41129997eb124e26351232479711eb7ccf11d748061187183a11761aa81142fa411134c93410d1aa96103ead2a0fc22fb60f5c5cfb0f3badb20edd17080ea68d810e783ebe0df078900db675560d52c9a60cf91d9f0c2cfbb60c167f100bd753a90bb2ffb10b989d440b41c7720acf09dd0ab7b9ae0ab0afbb0a9628be0a71f9560a172c490878675807d82e3c07bd347d07af559e075140fd06ecbabd06634425065223ce064612c705ad2f34059e8b170590310f05869eb105169eb003e36454036df150033a727c0296f5790291d00a024a740d023f103c01a603fb0198251c0188fb4b0129b75501013f3600dd496a0064991500368d3900103def
  | 8, 1 => 0x262d41fb25bece64258a6ea4255ffecb24cb7b292485a934233e51982310763b22c7351322543c1c2236825921b9f7ae21a5f9682179389d2064873a2046aaad203e530f203cd04e1fd3d3851fb72b911f608b651f3d31db1ee4e3db1ebb13731eb3facb1e8eec381e739d441e7359ed1e1aa3ae1e08e1531d73f5661c53b96d1bea35011bde45011b8548e61b61a0cd1b52f3321b325a461b2d157f1a5d39541a2bfa9c1a0ece7019f08aad19e360491979f4171923eb0b1900f42918e3fb0a183e830517d07b0017a820261729918f170db67f16e8db1815ff8a4715f86a801561a43a1528ba3c1415063f14121a0c13b5da6d136d10ac135211a21317dd2b
  | 8, 2 => 0x39de879e3950034038ad846e3899ed1837dd7e8037a1ed1c375fd1e83724f45b36f4981f36b6da9236ad5160368990f73678c0eb363c57f436224d1b361b1af435d89aaa359aee6d357bcd57355e29ce354bc4fd3518dab134e1dc0334746a9f342cdee933193e9a3294bf40326a0621315024ba31381b073122199e3055c0a62fa1c82a2f5be1482eedfa852ea0b9112e9e70832e8ed5cd2d770a592d6df75a2d014b912cf3c0ef2cf085992cae27f22ca821632c50f8382c1543872bdd94e82baacaed2ba0a43a2b0f56702af4104e2a5e00e129c478db2889888f284db2db2775450f2727707326d2458e26bb2fef26aa53c326a4b5bf264ea12126396ad4
  | 8, 3 => 0x4afc5e1e4aee73794ac0774d4a5928364a0d197449148db048fa38cc48f889f848f0bd7d48ebd2aa48b0ac9d484e6acf475141bb472e33c146e1bded46e149a2465e79d54609964845f6b58445c07cca457c5ed145179a8f44d9dfff44cd758b43cee64d43b9f0a343555fb0433f660a42b779a342815d8a4223bdb941d9fb7841d622d341a4b5d6413f306a413ca69640db2d8b40bb2834405c8f3d40455b7a4025ca0a3f49363a3ee6de3d3ebd45083e277fff3df1aaf13dc32c533d8620523d0124c93cedcf813cd7d7c23c9f3cdf3c8fe41f3c39fd5e3bf3e2703bd0b7833b3c318a3b23954e3afd7b253acd3e823a8b9b213a8b1a653a861c993a305add
  | 8, 4 => 0x5d6275f45d3a46645d2e415c5c91de815b4388f85af03eb05a73054d5a7078f85a437adf59f223e559e5330159d66aa059d395c75992adb05923c1c65916f5625905159658a5f17758905d1357c3519856dbe56f56da22f0567ee6cd55df5df855ab6c46558b875054ed1c7554b47b985342fdb75316929452f2fea452acbe7d528ca242520a3fab51d2062b51bb2a0f516924ff515c2919514f645451007c3a50c9577f50c4b4ed5059633d4f9b055d4f943bc44f8c57c24f490be64f0fba7a4e7327324e5bae794e1db72a4e00c0ea4de27c5e4dd111674d2b306b4cd8ba054ca60af44c4c79c44c173de94bf147df4bc969994b7591cb4b62f61f4b40518f
  | 8, 5 => 0x70c4152b707cee8d7005f1236fa6c90d6f3b46226e834bca6e38e6f66e1ad9ba6ddedbb86d9b14bb6d5cb0976d2657c06cd622c66c4b6e046bc490ee6b89f08a6b6909ce6b46b4d16b1be3666af785736a5eea176a510b386a4fc62d69c031bf69bac96869b2eaed692e70ee6920920f68ff5c7d688d1b55683fb3fc6709aa6166fb4c91668c47706659a12a6554bad164ffcc4e64e30e6464cf00c564789948638147926379a6766347643b6336351163275f156292bf226284e04362623a3561f427ee6129ea2960d158046001a2b65fd513de5fbac6fd5f5d13a95ec6f1c75ebcebc25e90082e5e22a7545e1657ce5e06e6065d9647d45d93d62e5d7bf2db
  | 8, 6 => 0x87080352869b7594868cb424862851b985f48e9f85e99b5485ba4fb98558bace85210b03850f030e83c5bc52838341f4833df90383233d80830766bf828511a482739f2082121d0d81b633a580f3ebfa7fe35f827fc0036d7f97da8d7f27d8097f1797dc7e1a8a567dad4e397d7d57bc7d776c2f7d33ff317d303bbe7cea112d7cd372a07c439fcf7b25f4ae7ae97d0f7ac854af7a85129f7a2bfc5d7952d274791d9b417900675a785a178977f10ba277d135d07770373f7733bc5377211a3f76f0de3376f0916b76db0b2e76bdf4b9766385db764e5f61745a681c73a4532b73a1eeb77396326d73227b8e72739f547260e48f71fb25a271be65bd714a8ba9
  | 8, 7 => 0xac23afedabe5308aab681b8eaa38618daa2867c5aa21bb6da9cb11c2a98c5b5da9647ee6a8e78fc4a80d4bfda8098f40a6563cc3a62fa927a36baaf7a302d5f5a1f16defa1662bafa141bf77a0c045e2a07b39919ffd08839eab30d29e6bbe4b9d3508f49c27c3cd9b34b1219ab47d5a99d7582f98d8396998553ede9721f5ed97012b8496fad256965f3458963c456d95c0f43f955a089894b8834e9396353d936159ab92a6c201928cbda5925c0be491426eab906d26119011f5828f7fd14d8f78512d8e27eed18d92f6958d7f04bb8d6fdaea8c8386ea8bedc1998aef68758a18c28889beef4c897643b68968a0cb88f823fd88ede028886bb2a5876b3203
  | 8, 8 => 0xd5d7c256d56748abd3b34341d355d4ffd27a66b2d229a3e5d1d3f658d0a7e5c1cf84bc20cf6e15b1ceecb93fceeb1ad8cecb96dfce6b8b90cda803e7cd5fbf4fcc0b8b0bc9d88a90c876c3bec5c226a0c4605fcec398766ec31b6fd9c30bd3fac1c6e06ec1c5a5bebf46884bbef5700abef4bb49bd5c9ba0bd2744b8bcc8e334bca06181bc5e25f5bbec3344bad4da24bab08b31ba2399e2b84d21e0b7610a65b6edc245b6be7634b69fded2b65f3e8fb5c9ec3db5195244b315333eb2f03ccbb210ca3fb1b17014b12375bdb0f51e5bb0ec7e1fb080f6ebb0480e0db031ca64b02268afaf935789af01b67aaee65ee3aec64c0eae8d3699ae5c9576ad85a160
  | 8, 9 => 0xfe12eeb4fd75d7f8fc3cf275fabc44b5fab495f5faa130d0f9b99d75f96feb04f9091127f8b72109f7e68aa8f772bfb1f734b506f646c3bff637ead7f62c0f9af5493ef0f50771aef2854adff22186e7f15a4793f11d8484f0f10dbef05fc8f2efeaeca8efdfd1c7ef0e3eb4ee6bbfe2ee22ff53ed71b5aeeca193e2eb7a065aeb3fcd10eaf7dac4ea555bf2ea39f55de9d3bc26e8b03ee3e878be20e86f0f45e7283c3de5d4dd4ce575a6eae4625a30e2f7dbbfe2f02cffe25263cde07b344ee04a17a1dfdba1afdf7fbf91dede789bdd9de376dc240579d9eccea3d8e7dfa1d87f9952d7d8277ed7c2c847d69e993fd697c1d4d6890d25d64007d5d62ad27f
  | 8, 10 => 0xff5a28fe
  | 9, 0 => 0xdd9de376bad4da24b6be763455df5df84f8c57c22eedfa851e7359ed1729918f1142fa41
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 5, 0 => 0x10d1070000051500201000000000a101000000000000f0000000000011000001044020100000000000120014d2148430100000520412000000000000003000000000000e0000000000000000000000000b000000010d10600000000841080000000000002000000008410800000434c12030000000000000000000000000f00000000000020000000000009000000010d106000000010d106000000010d107000000010d1070000000002101000000010d107000000000000e000005404120000000535002040000000084108
  | 5, 1 => 0x51500201000000008410800000000c9116000c9514c830100000535002040000000085102000005350020400000000851020000000000000000005010d204000000000000c00000540412000000000000012000000010d1060000000000004000000000000f000000000001100000535002040000000000009000000010d1060000040500201000000000000c00000000000020000053500204000000000610100000434c1203000000000000f0000041504201
  | 6, 0 => 0x1200000000000010000000000009000000000000f000000000e1010000010440201000000000e1000000000006100000000480e2000000000006102000000000e102000000000000600000000061020000000002102000000010d1060000000000009000000010d107000000000e101000000000000c000000000a10200000524c4201000000000a1040000000000005000000010d1040000001802201000000000000f000000010d10400000018022000000000012100000000000000b0000000000011000000000e104
  | 6, 1 => 0x5308520000000520c5201000000480a200000000010d1060000000006104000000008510200000000000000000000000009000000001210400000001051010000000006103000000000a1010000000000003000000000000e000000000001100000000000060000021484200000000380a200000000010d104000000000000b0000000000014000000010d10200000000000110000010440201000000000000c0000000000012000005344020100000028022000000000000007000000000210400000000061000000000000012
  | 6, 2 => 0x10d1040000000100104000000000001100000000021020000000000008000000000000b000000000001400000000121000000000000011000000000000900000028062000000000000004000000000001400000000411010000000006103000000000000f000000000210000000000c91160000000006100000000000a10400000000000060000000084108000000000000500000000841080000000000009000000000000a00000000841080000054440200000000000e103000000000000900000000000110000000000016
  | 6, 3 => 0x3000000000a100000000000000600000000061000000000000013000000480e201000000000000900000515002000000000000008000000000000f000000000a100000000000000e00000000000060000000000001000000010d10600000000000000000052500200000005110120100000000411020000000012104000000000a101000005304120000000000021000000000085102000000000e1030000000000009000000010d106000000000000200000000000070000000000006000000010d1040000010440200
  | 6, 4 => 0x10d106000000000000900000000000000000021484201000000480220000000524402000000000012104000000010d104000000480a2010000054440200000000000000500000000000110000010440201000000010d102000000000a10100000000851020000000085102000000000a1040000000000002000000010d107000000000e1020000010440200000000008510300000000000160000000000009000000000000900000000061040000052440201000000380220000000520c52000000000000009000000000e103
  | 6, 5 => 0x2104000005304120000000000801000000000000012000000010d107000000010d1060000052500200000000000a100000004250820000000000121010000000000001000000000610300000000061010000000006103000000000e1030000000000006000000380a200000000380620000000000000010000000000001000000000000900000511012000000000000011000000000a101000004350c200000000010d1060000001802200000000001210300000524c4201000000000a102000000000a1040000054041200
  | 6, 6 => 0x2048020000000038022010000003802200000000000000e00000524402000000002802200000000000000900000048022000000000000011000000380a201000000000a104000000000000c0000000000006000000001210200000304c02000000053101200000000000e104000000480e2000000000012104000000480e200000000480620000000038022000000000000007000002148420000000000000120000004806200000000280620100000000000070000000012102000000380a20100000000061040000000084108
  | 6, 7 => 0x8410800000000061040000000000006000000000610200000000000120000000000002000000280220000000000c911600000028062000014d214843010000000000001000000000e101000005310920000000214842000000000006100000000000001200000530852010000000006102000000010d1030000000006103000000000610100000304c0200000000000e103000000480a201000000000e10100000000000140000000012103000000480e2010000000002102000000380620100000000000090000000012100
  | 6, 8 => 0x480a2010000000000009000000380620000000534402000000000000014000000000000900000000000070000000012102000000000210300000000000090000000000008000000001210400000000061010000000000004000000000e10300000000000090000000000016000000000610100000000000160000000000000000000000000a000000000e1040000000002100000000010d10400000000000090000000002104000000000000f0000000000005000000000a102000000000610000000000061040000000100104
  | 6, 9 => 0x70000000000012000000000a1010000000100104000000010d10400000000021000000053440201000000010d104000000380620100000525002000000054440200000000001210000000000000050000000105101000000000000900149314c4301000000000610000000520c5200000000000a100000000000000f0000000000009000000000001100000000021030000000000009000000001210400000314c42000000000000009000000010c101000000000610000000324c82010000052500200000005210d200
  | 6, 10 => 0xa1000000000000011000000000000c000000000000800000000061020000000000004000000480620100000000000090000002806201000000010d104000000000a10100000000841080000000002102000000010d10700000000121040000000000000000000000000100000000000070000000000004000000000000c00000018022000000053500200000000000000e00000520c520000000000061030000004802200000001044020000000038062010000000002103000000001210100000000000010000000002103
  | 6, 11 => 0x105105000000000210100000434c120300000540412000000004802200000000000000f0000002806201000000000610200000000000070000053085201000000000000c000005310120000000000000070000002802201000000000210000000000021020000000000009000000000000c000000000001400000524c42000000000000005000000180220000000038022010000051500200000000380a2010000000002104000000000000c00000000000110000000000014000000000000e00000018022000000000002102
  | 6, 12 => 0xe102000000000610000000000000020000000000014000000000000a00000000411010000052440200000000000a102000000000000c0000002802200000000000000600000000000000000000000007000000001210200000048062010000000000011000000000a102000005010d204000000000000000000531012000000040500200000000010d10400000000401000000000000000000005110120000000524c42000000000000007000000010d1040000000000000000000000210300000000000000000004802201
  | 6, 13 => 0x12100000000000000700000038022010000000006101000000000000e000000010d1040000000000009000000000001100000324c820000000425082000000000002102000000000000000000540412000000000000009000000000a10400000324c82010000000000000000000010d103000000000e10000000000000110000000000001000000000610100000000000090000000000006000000010d10400000028062000000002806200000000000a1040000002806200000000000e10100000000000110000000000009
  | 6, 14 => 0x85102000000010d1030000003802200000000000000100000000061020000000085102000000380220100000000021000000000000013000000010d107000000180220100000000000020000000012101000000010d1020000004806201000000000210400000544402000000000000006000000010d1040000000000011000000380620100000000000070000000000005000000000e10400000000000050000000006100000000010d10200000028062000000000000000000000000a1040000000000011000000000a103
  | 6, 15 => 0x52041200000000000000800000511012010000054440201000000008510200000038022000000000002103000000010d10700000000000090000010440200000000000a10400000515002000000000000014000005010d20400000000061000000001802200000000010d10600000001011010000000104101000000000610200000415042010000000002104000005050420000000000000090000000000009000000480e20000000104402000000000000008000000000000500000000000040000000000016000000010d103
  | 6, 16 => 0x53101200000000380a20000000000021040000000002100000000000e10000000000021020000000000011000005110120000000104402010000003802200000000000210400000000c110300000214842000000003802200000000010d1060000004802200000000000000f000005404120000000000000140000004802200000000010d102000000000a1040000051500200000000010d10400000000000060000000000014000000000e100000000010d10400000000061040000000000006000000000a10000000324c8200
  | 6, 17 => 0x53440200000000000a10300000524c4201000000280620000000000061040000053085200000000001210400000520c52000000000000008000000010d104000000000001400000000000090000000000011000000000000a0000052440200000000000e100000000000a104000005210d2000000000000004000000380a20000000000000120000053085200000000000000f0000051101200000000000000000000214842000000052440200000000008410000000048062000000003802200000000000a100000000000000c
  | 6, 18 => 0x2104000000010d1030000000000001000000000610000000524c42000000000000009000000000e100000000000000900000000121040000041504201000000010d1040000000000005000000010d106000005344020000000324c82000000020480200000000180220000000000000060000000000009000000010d1060000000000005000000000a102000000000e1000000000104101000000000a1000000041504200000000000000f0000000000009000000000001100000000000110000000002102000000010d107
  | 6, 19 => 0x90000000002100000000000e100000000000000500000304c0201000000000a1010000000000005000005210120100000000121020000000000011000000000000900000000000060000000012100000000480a200000000000610400000000000000000000006104000005310120000000038062000000054041200000000010d1020000000000001000000000000000000000061000000000000008000000000000300000324c8200000004250820000000000000040000000000014000000010d1040000000002100
  | 6, 20 => 0xe10400000524c420100000000000000000000012100000000000a103000000000000200000000121020000000101103000000000a1000000000006100000000000a10100000000121040000000000012000000001210000000520412000000000000006000000010d104000000000000c000000000000f0000004806200000000010d1040000000000008000000010d104000000000e10400000000121010000000012102000000000a10000000524c42010000000006104000000280220100000000000070000000000009
  | 6, 21 => 0x80000004806200000000010d103000000000610200000000061000000040500200000000000e1030000000000008000000000000900000524c4200000000000e1040000000000009000000010d10400000028062000000000002100000000000000c000000480a2000000000000006000000010010400000000021030000054041200000000010d1060000000085102000005244020000000000000090000000000009000000000000d0000051500200000000010d104000000480a20000000511012000000000000001
  | 6, 22 => 0x2102000000000000c0000000000005000000000210400000000000140000000000001000000001210300000000000160000000084108000000000e10400000000000000000053085201000005348420000000524c420000000104402000000000000014000005444020000000000061000000000002104000000000000c000000180220100000000000050000000000007000000380a2010000000085103000000010d10300000000000000000000000006000000000001200000028062000000000000004000000000e100
  | 6, 23 => 0x380a20100000000021020000021484201000000000000900000000000140000000002100000000010d10300000324c8201000000010d107000000000000500000000061030000000002104000000010d10400000000021040000041504200000000000000500000000021040000000002100000000000000900000000c110300000000021020000000000006000000010410000000000021030000000108101000000000a10000000000851020000004806200000000000000e0000000006100000000000e1030000041504200
  | 6, 24 => 0x4806201000000000610100000000061000000004806200000000000a102000000010d103000000010d102000000380a201000000010d10400000000000000000000000014000000010d104000000000a100000000000000900000524402000000000006103000000000000000000304c0200000000000610000000530852010000000000000000000010d106000000010410000000000061030000000000008000000010d1040000000000014000000000610400000001001010000000000009000000000e102000000000e104
  | 6, 25 => 0x9000c9514c830100000000000050000010440201000000001210200000000000140000000000009000000001210000000304c0200000000380a2000000000012103000000000000f000000010d10200000524c4200000000000e104000000000000e00000520c5200000000000000a00000530852010000000000006000000000a102000000010d104000000000000100000000121030000000000014000000010d102000000000000000000544402010000000000014000000000000500000000061030000054041200
  | 6, 26 => 0x800000000000090000000002104000005308520000000324c820000000038062000000000000014000000000610400000000000110000000085102000000010d1060000053085200000002148420100000514c820100000000000040000000002104000000000e102000005404120000000000121010000000000008000000380a20000000324c82010000041504200000000010d106000000010d104000000010d102000000000000500000001011000000000000000000005308520000000000021000000000000000
  | 6, 27 => 0x180220000000000000040000000000001000000000610000000000061020000000002104000000000210300000000021000000000000005000000480620000000018022000000004806200000000010d104000000010d1030000001802200000005444020000000000121040000000000014000000480220000000324c8200000000280220100000000000090000054440201000000000000e0000000000009000000000001400000000841080000000002101000000000001500000000000090000000000003000000000000f
  | 6, 28 => 0x411000000000002100000000380220000000000000000000000000008000000000000f0000004802201000000380a2000000000000012000000010d10200000000000000000000002101000000000000200000524c4200000005304120000000000000020000000100104000000000001400000000021020000000000000000000000610100000000021000000000000008000000000000900000524c42000000000002102000000000210300000000061010000004806201000004250820000000000000000000001802201
  | 6, 29 => 0x5010d2040000000000000000000008510200000000000000000000000008000000010d10300000000000140000000085102000000000a1020000000000000000000480e200000005444020000000000000090000000000014000000010d102000000180220000000000121020000000000013000000000000b000000010d1030000004802201000000008410800000214842000000000000009000000000000f000000000e10400000000021040000053500204000000010d103000000010d1040000000006100000005010d204
  | 6, 30 => 0x10d104000000000000100000000021000000000002104000000000e1020000000000009000000000000f00000000000070000000000000000000380a2000000001802201000000000210100000000000060000000000008000000000000000000000121000000000006100000000380a2000000000002101000000000001200000524c42000000000006101000000000210000000304c020000000000000030000000000009000000000210400000000021040000000000001000000010d10300000048022010000000000008
  | 6, 31 => 0x610200000000000000000051101201000000000000900000000000020000000000000000000000210400000000000110000000000009000000001210000000324c820000000018022000000054041200000000000000000000000000090000052101200000000010d1040000000000011000000000000900000324c82000000000012104000000000e104000000000000b00000000061000000000000000000005444020100000018022010000000000009000000000610000000000c911600000000000000000000000005
  | 6, 32 => 0x900000000061000000001802200
  | 7, 0 => 0x21010000000000003000000010d102000000000000e000000000000b000000000e10100000000000010000000012100000000000210100000000c510000000000000090000000000005000000000000100000000c1101000000000e10300000000000140000002802200000000000000100000000021000000000000003000000000000100000000021030000000081100000000000000100000000061020000000000001000000000210000000000021040000000002100000000000000500000000000050000000000003
  | 7, 1 => 0x900000000000020000052440201000000000000100000000000020000000000000000000000000200000000000080000000000005000000000000b00000000000070000000101101000005308520000000000c410100000000121000000000104101000000000e101000000000000e000000000e10000000304c0200000000280620100000000000070000000000003000000000a10000000000021030000000000006000000000000100000000c8101000000010110000000000021000000000000001000000010d103
  | 7, 2 => 0x121000000000000004000000000e100000000480620100000324c820100000000c81000000000085102000000010d1020000000000004000000010d104000000000610200000000c010100000000811000000000000005000000000000600000000000060000000041100000000001210200000000061000000000000005000000001210400000000000070000002802200000000000a10200000000000160000000006101000000000000000000000000080000000012100000000010d10200000000000030000000084100
  | 7, 3 => 0xb000000000a1000000000000002000000000a1010000000002104000000000000400000544402000000000000008000000000000400000000000020000000105101000000000000400000000c81000000000000005000000000610000000324c82000000000000003000000000000700000001011010000000000004000000000e10000000000000000000000002103000000480220000000520c5200000000000a1040000000002104000000000000400000000000030000000000004000000000e1010000000000004
  | 7, 4 => 0x210000000000000060000000104100000000000a1000000000000007000000000e1000000000000007000000000a100000000000210100000000c810100000000000030000000000011000000000e1010000000002102000000000001600000000000080000000000002000000010510000000000000110000000012102000000010d104000000000a103000000000000c000000000210200000000000010000000101100000000000000f0000000002100000000000000000000000c010100000038062010000000000003
  | 7, 5 => 0x520c520100000000061010000001802201000000000a10400000000021030000000000005000000000000a000000000000300000000061030000000006104000000000000200000000061040000000006100000000000000e0000000006104000000010d10300000000061010000000000011000000000a102000000000000c000000000000200000000000020000000000002000000000000000000000121010000000002104000000000000200000000021020000000000003000000000000200000018022000000000000006
  | 7, 6 => 0xe1000000000000002000000000610100000000000050000000000003000000000000900000001051010000000000004000000000000600000000000000000000002104000000000a1000000000000002000000000000f0000000012103000000000000f00000000000010000000002102000000000000200000000411010000000000009000000000e10100000324c82000000000012101000000000a104000000000a101000000008010000000000021040000000000009000000000210000000038062000000000000007
  | 7, 7 => 0x21000000000000004000000000a1040000000002104000000000000800000000000080000000105100000000000000900000000021030000000000003000000000000400000000021000000000000008000000000000100000000000040000000000009000000000e101000000001210000000000000030000000002100000000000a103000000000e1040000000000002000000000610000000000000020000000006101000000000e1040000000006102000000000e10200000000c410000000000c01000000000101100
  | 7, 8 => 0x300000000000080000000000002000000000210000000000411000000000012101000000000e1000000000006101000000180220100000214842000000000000002000000000001100000000000030000000000007000000000a101000000010d10200000000c8100000000000e100000000010d104000000000000700000000000030000000000001000000000000000000000000000000000000016000000000000100000000000020000000006104000000000000400000000000110000000000003
  | 7, 9 => 0x411000000000000002000000010c1000000002802201000000000000c000000380620000000000000010000000000002000000000000600000000061010000000002101000000000000f000000000a1040000000000004000000000000200000000121020000000000000000000000e103000000000a100000000000a100000000000610300000524c4200000000004010000000000121000000003802200000000010d104000000000a1030000000000002000000000a100000000000a1000000000000002000000000a100
  | 7, 10 => 0x10000001802200000000480a201000000480220000000000c81000000000000004000000000e10000000000000090000000105101000000008010000000001091000000000012104000000000000700000000000000000000002100000000000001100000000000040000000006104000000000a1010000000000007000000000000f00000520c52000000000000000000000000000200000000c410000000000c810100000304c020100000000000050000053085200000000000000700000000021010000000000004
  | 7, 11 => 0xa0000000012101000000000610400000000000030000000000004000000380a2010000000000004000000000610000000314c4201000000480a20100000000000120000000000009000000010410000000000c9101000000000000300000038022010000000002104000000000000f000000480220100000000000110000000000004000000000000100000000801000000000000002000000000a10000000000000070000000000012000000000a10200000000000070000000000014000000000a1010000002802201
  | 7, 12 => 0x6103000000000a103000000000000400000000000090000000002101000000000a104000000000a104000000000e10200000000021020000000000004000000000000500000018022000000000000014000000000001100000000121010000054440201000000480220100000000000110000000104100000000000e101000000000a1000000000006100000000000e1030000000000003000000000000000000000000050000000002101000000001210000000000021010000000012104000000000e1040000000000000
  | 7, 13 => 0xc000000000210100000000000140000000000007000000010510100000000c4100000000000610100000000000000000000000005000000000a10200000000000110000000002101000000010d103000000480a200000000000000c0000000000011000000008410000000000c110000000000000020000000000000000000010d102000000000000a0000000000002000000010d1040000000000009000005210120100000000000000000000000014000000010d103000005404120000000000c11010000000040100
  | 7, 14 => 0x1000000000000900000000c110000000000000030000000000004000000000a101000000000000b0000000006101000000000000f00000000000020000000006100000000000000400000000021000000000000009000000000a1010000000000002000000000a100000000000a100000000000000400000000121020000000000011000000000000800000304c020100000000000160000000000007000000000a104000000000000600000000000050000000000014000000000a10000000000000050000000000002
  | 7, 15 => 0x12101000000010d10200000000c5100000000000000500000000061000000000000014000000000001200000000c51010000000002100000000000000400000000061000000000000009000000000210100000000121020000051101201000000000000000000000000000000000012100000000000000e000000000000400000000000020000000000001000000010d1020000000000005000000000e101000000000e102000000000000300000000811010000000002100000000001210400000000000080000000000000
  | 7, 16 => 0x214842000000000000003000000000e10300000001081000000000006101000000000000c0000000000012000000480a20000000000000010000000000003000000380a20000000000000040000000006103000000000000500000000000030000000006101000000000001200000000c1100000000010d103000000000610200000000000010000000000007000000000210400000000000050000000040100000000000210400000000021040000000000004000000000610200000000000020000000012101000000010d103
  | 7, 17 => 0x3000000000000a0000000012102000000004010100000000000020000000006103000000000000c0000000000007000000000e1010000000000002000000000e102000000004110100000000000090000000000003000000010d10300000000000140000000000000000000000a10000000000c11010000021484201000000000a10300000000000000000000105100000000000000600000000000110000000002100000000000a10000000000000090000000000002000000000000500000000061000000000000004
  | 7, 18 => 0x21010000000006100000000000000800000000000090000000105101000000280620100000000841000000000085100000000000000200000000000020000000000008000000000e1000000000006104000000000000000000001081010000000002102000000000610000000000000010000000080101000000000000900000000000030000000000002000000000a10400000520c5201000000000000800000000061010000000000004000000000000c000000000000600000000000030000000085102000000000a103
  | 7, 19 => 0x7000000010d1040000000012102000000000a102000000000000600000000021040000000000003000000000a101000000000e10100000000000020000000006101000000000001400000000000000000000012100000000000000100000000021010000000080100000000280620100000000c11000000001802201000000001210000000000c8100000000000000200000000000040000000012100000000000210100000000c410100000000000050000000000000000000000a10000000001011010000000000008
  | 7, 20 => 0x21040000000000008000000000000400000001051010000000000003000000010410000000000000080000000041101000000000a102000000000e10000000000000050000000002103000001044020000000000000050000000000002000000000e101000000000001200000000061020000000000002000000010d1040000000006101000000180220100000048062010000000012101000000000001200000001051000000000000006000000000a1010000000006103000000000e10400000000061000000000000007
  | 7, 21 => 0x5000000000000b000005344020000000000c410000000000c0100000000000000200000000000040000000000009000000000000f000000000000c0000000000003000000000000800000000c91010000000006101000000000a104000000000a1000000000000009000000000e10200000000021000000000000001000000000000400000000000080000000000001000000008410100000000000060000000000005000000000000e0000000000012000000000000c000000000210000000000000020000000000002
  | 7, 22 => 0xa1040000000000011000000000a102000000000a10100000000000070000000000005000000000000f000000000000a00000001081000000000002101000000000e101000000010d103000000000000100000000000030000000000003000000010d102000000000000000000000000050000000000009000000000000900000000000040000000000003000000000a10200000000021000000000000000000000010d1030000000000006000000010d1020000000000011000000000000f00000000061000000000084101
  | 7, 23 => 0x12100000000000e10300000000021000000000006104000000000000200000000021020000000000005000000000000700000000061000000000000009000000000210000000000c91000000000000005000000000a100000000000e1010000000000002000000000000100000001051010000000000005000000000001200000000061000000000012104000000000610200000000000060000000006104000000000000f000000010010000000000c410000000000c910100000048062000000000000006
  | 7, 24 => 0x4000000010d1040000000000003000000000a1020000000104101000000000e104000000004110000000000000070000000000006000000000000000000000000090000000012101000000000000c00000000000080000000000001000000000000700000544402010000000109100000000000a103000000004010000000000000140000000000004000000000e10300000000061010000053440201000000000610100000000c4100000000000a1010000000006101000000000000200000000000000000000006100
  | 7, 25 => 0x6103000000000000b000000000000a0000000000005000000000a100000000000000000000048022000000000000006000000001210300000000121020000000104100000000000000b00000000000090000000000002000000000000c00000000000060000020480200000000000000900000001091000000000000001000000000a1010000000000007000000000e1000000000040101000000000000f0000000006101000000000000c00000000061030000000000009000001044020100000000c41000000000000007
  | 7, 26 => 0x401000000000000004000000000a104000000000e101000000380a200000000004110000000000000030000000000011000000010c10000000304c020000000000000030000000000016000000000000700000000c9100000000010d104000000000000300000544402000000000000002000000000000800000000000070000004806200000000000a1020000000000009000000000610200000000000020000000012104000000000a10100000000000040000000000003000000000000000000000021000000000002101
  | 7, 27 => 0x140000000000007000000000001400000000000000000000000000000000001210100000000000010000000000006000000010510000000000000120000000101100000000000a10000000000c5100000000000210000000028022000000000006101000000000e1010000000000002000000000210000000000c410100000000000000000000000003000000000610000000000c5101000000000000a0000000000004000000000000300000000000000000000000007000000000000200000000021000000000002100
  | 7, 28 => 0x6101000000000a1020000000000012000000000a103000000010d1020000000000004000000000001400000000c01000000021484201000000000000200000000401010000000000004000000000e1000000000000004000000000001100000000c810000000000c41000000000000002000000000000800000000000020000000000003000000000000000000000000030000000000011000000000000500000000851000000000000000000000000000400000000801000000010440200000000000e1020000000000005
  | 7, 29 => 0x2000000000000400000038022010000000000008000000000001100000001081000000000000014000000000000f00000000c51000000000000005000000008410100000000401000000000041101000000000210200000000000070000000006100000000000000900000000021000000000000006000000000e103000000000a1010000000000004000000000a10300000000121040000003802201000000000a1000000000006102000000000e1020000000006100000000000210000000000000020000000000006
  | 7, 30 => 0xa1000000000000003000000280220000000000121010000000109100000005244020100000000c510000000000061010000000000005000000004010100000000c010100000000841010000000000001000000000e1000000000085103000000000000e0000000000007000000000610200000000c9100000000000000500000000000050000000000009000000000000a000000000000300000000000110000000040100000000000a100000000008410100000304c0200000000010d1000000000000002000000000a100
  | 7, 31 => 0x10d100000005210d20100000524c4200000000000610000000000000030000000000002000000010810100000000000030000000006100000000000001200000324c8201000000000e100000000000e103000000000001100000204802000000000000012000000000610000000000c1100000000008110100000000000140000000000003000000000e10000000000000070000000000011000000010d10300000000000010000000000011000000000000f0000000000008000000000000b000000000001300000000c8100
  | 7, 32 => 0x61020000000006103000000000e1020000000000001000000000001600000028062000000000002101000000000a1030000000002100000000000e101000000001210100000000000000000000000009000000001210400000000000020000000000003000000000e1000000000000002000000000610300000214842000000000000003000000000210200000000000040000000000001000000000610000000000021020000000000006000000000000a0000000000009000000000001400000000000030000000002101
  | 7, 33 => 0x2104000000010d1000000000000003000000000000a000000010d102000000000e100000000008410100000000000010000000006100000000000000000000000000000000000000012000000000001400000000021040000000000005000000000000500000000000030000000000012000000000000f000000000a1020000000006101000000000000800000000851010000000012103000000000e103000000480a200000000000001200000000000050000000000008000000000000000000000000100000000000008
  | 7, 34 => 0xf0000000006104000000001210000000000000050000000002102000000010d10400000000c8100000000000000300000000000040000000002102000000000000e0000000006101000000000610300000524402000000000002100000000000000a0000000000000000000000000000000000c5100000000000001400000000121030000000000001000000000e10100000000c0101000000000000b00000000000040000000002102000000000000300000524c4201000000000210000000000841000000000000005
  | 7, 35 => 0xe10000000104402010000000012102000000000000100000000061020000000000004000000000e10000000000061010000000085102000000000000f0000000000009000000000a100000000000e101000000000000900000000000030000000000005000000010d104000000000e100000000000000600000000000010000000000006000000000000100000000c81000000000000008000000000000700000000061010000000000000000000000001600000520c520000000000121040000000012100000000010d104
  | 7, 36 => 0xe10300000001051000000000012103000000001210100000000061020000000000009000000000a101000000000610000000018022000000000000004000000000000e000000000a10000000000000090000000000003000000000000a00000000000010000000084100000000000000400000000000090000000041101000000000a10200000038062000000000000000000000000210300000000000020000000000011000000000a100000000000a100000000000a101000000010110000000000000080000000002100
  | 7, 37 => 0xe1000000000041101000000000610000000000000050000000006100000000010110000000000061000000000000001000000000000c0000000006100000000000e10000000000121010000000000012000000000000200000000000090000000000003000000010d102000000000e1010000000000000000000001210100000000000090000000002102000000000000800000000c010100000314c420000000000000060000000000002000000000a1000000000000002000000000001400000000000090000000000004
  | 7, 38 => 0xa101000000000e101000000000a1040000000000009000000000610100000000021000000000000008000000000000000000000021000000000000002000000010d1020000000000016000000000000100000000000140000000006100000000000000f00000000000020000000000007000000000610000000000c810100000000c41000000000012100000000000e101000000000610200000000000040000000000003000000000210400000000000120000000002101000000010d10400000000000050000000006104
  | 7, 39 => 0x900000000000050000000084100000000000a1000000000000004000000000000600000000000070000000041101000000008410100000304c020100000000000010000000000005000000480a2010000000002103000000000e10200000000121000000000002102000000000e100000000000e104000000000000f00000000c4100000000000610300000000000030000000006100000001044020100000000000030000000105100000000000a10200000000000050000000006100000000000a1010000000000008
  | 7, 40 => 0x60000000000005000000000210000000000000070000000041100000000000a1030000000000008000000000000900000000000040000000006103000000000a101000000000000f00000000000080000000006102000000000000500000000401000000000000000000000480e200000000000000000000000401000000000000004000000000a1010000000006101000000000a1030000000000008000000000a100000002148420100000000000000000000000008000000000610000000018022000000000104100
  | 7, 41 => 0x12000000000e10100000000000060000000012101000000280220100000000061020000000080100000000010110000000000c81010000000000005000000000000c0000000000013000000000a1040000000002101000000000000a000000000000400000000c1100000000000000700000000000020000000006103000000010d1030000000105100000000000a10000000000000050000000012100000000000000f000000000000100000000000000000000000004000000000000100000000061010000000012104
  | 7, 42 => 0x60000000000011000000000210000000000811010000000000014000000000000000000000000000000000000007000000000000700000000000080000010440200000000000000b000000000000f000000000000400000000000040000000000002000000000000e0000000002104000000000210100000001081000000000000008000000008410100000000000020000000000006000000000000f0000000012101000000000000800000000801000000052440201000000000000300000000061010000000041100
  | 7, 43 => 0x841000000000000001000000000000900000000c4101000000000a10000000000121030000000080100000000000000200000001011010000000085103000000000000400000000000080000000000001000000000000a00000000000080000000000005000000000000b0000000000001000000000e1030000000002104000000000a100000000000a1000000000000005000000010d1020000000000002000000000a100000000000210000000531092000000000000002000000010d10200000000401000000000041101
  | 7, 44 => 0x40000000000002000000000e10200000000000040000000006100000000000000400000000000070000000006100000000000610100000000000040000002806201000000000000400000000401010000000000000000000000000e000000000000000000000061030000000006103000000000000a0000000101100000000000a101000000000e10100000000c11030000000000009000000000a1000000000000002000000000a103000000001210300000524c420100000000c41010000000002101000000000a102
  | 7, 45 => 0x3000000480620100000000000010000000012100000000000e10300000000000110000000109101000000000001100000000000140000000006100000000000a100000000000a1000000000000000000000000000500000000000080000000006101000000010d1040000000000003000000000e1040000000000009000000000210300000028022000000000006100000000000000200000000000040000000000006000000000000e0000000000014000000001210000000000000040000000012100000000000a102
  | 7, 46 => 0x2100000000001210300000000c010000000000000010000000000006000000000000000000000021010000000000015000000000000400000000000010000000101101000000000210100000028062010000000006102000000000001100000520c520100000000021040000000084100000000000000900000000000020000000000000000000000000f0000000000004000000000001300000000000000000000000007000000000a10100000000000050000000006100000000000a10000000000801010000052440201
  | 7, 47 => 0x200000000c8101000000010c100000000010d104000000010d10000000520412000000000000008000000000000000000000121000000000002101000000001210300000000000000000000012100000000000e100000000480620100000000021000000000000006000000010d103000000000e1000000000000000000000000000700000000000060000000000000000000000000300000000000090000000006101000000000000c00000000000040000000012100000000000e1030000000000003000000380a200
  | 7, 48 => 0xa10100000000000010000000041100000000000000300000000000020000000012104000000000000400000000000120000000000004000000380a20100000000000020000000006100000000000610100000000000040000000012101000005308520000000000000140000000000014000000000610100000000000030000000000003000000480a20000000000061000000000006103000000000000400000324c82000000000006104000000010d1020000000002102000000000000c00000000000020000000006100
  | 7, 49 => 0x121000000000000012000000480e201000000000000300000000000060000000081101000000000000000000000c410100000000c11000000000000001000000000a102000000010510000000000000070000002806200000000000000e000000000000000000524c4201000000480a201000000000a101000000000a101000000000000b000000000e101000000000e104000000000000500000000021010000000000001000000000a101000000000000400000000000130000000002103000000000000e0000000000007
  | 7, 50 => 0xa104000000000000a00000000000130000000000014000000000000e000000010d104000000000a10100000000000000000000000005000000000610000000000000070000000012101000000000001200000000061030000004806200000000000e100000000000000700000000000020000000006100000000010d104000000010d10400000530852010000000000008000000000000300000000021030000000000007000000000001100000104402000000000000008000000000e10000000000000030000000000002
  | 7, 51 => 0xc81010000000012101000000000610200000000000030000000000011000000000000200000000000050000000012101000000000000f000000000610000000000061000000000000008000000000610200000000401000000000000012000000000000f000000000a1000000000000007000000000610000000000000160000000000004000000000000a0000000000007000000000210000000000000000000000000001000000000a100000000000210100000000000140000000012100000000000e1020000000000009
  | 7, 52 => 0x61030000010440200000000008010000000324c820000000000061000000000000005000000000000200000000000130000000000014000000004010000000000000070000000000012000000000a10300000000000030000000000004000000000e101000000010010000000000121000000000006100000000000000300000000000050000003802200000000001210000000000061010000000000016000000000a10000000000c410000000000c0100000000000a101000000004110100000000061010000000012100
  | 7, 53 => 0x61000000021484200000000000000600000000000070000000104100000000000a1000000000000012000000000000300000000c4100000000000000c000000010d1030000000000006000000000a1000000000000004000000010d1040000000000002000000000a1040000000012102000000010d100000000000000f000000000000c000000000a102000000000610400000000121000000000000014000000010d1040000000012102000000000000f000000000a104000000000001200000000000090000000101101
  | 7, 54 => 0x12100000000004110000000000000090000000002100000000001210400000000061000000000041101000000000000200000000c81010000000000004000000000000f00000000c9100000000000000b0000000000007000000000e1010000003802201000000000210000000000000090000000006101000000000610000000324c8201000000000e104000000000e101000000000000c0000000006101000000000000500000000061000000000000005000000000610300000000061000000000085103000000010d104
  | 7, 55 => 0xe10200000000000140000000012100000000010d102000000000000700000000000070000000041100000000000000200000000801010000000000008000000000a1000000000012102000000000210300000514c82010000000006101000000000000f0000000002103000000000a1010000000006101000000000a10100000000021040000052440200000000000a1010000000002103000000000000100000324c8200000000010d10400000038062000000000000000000000010110000000000121000000000000002
  | 7, 56 => 0x8410000000000000040000000000008000000001210100000000000040000000012101000000000000700000000000120000000012103000000000a103000000000001600000001011010000000000003000000000210000000000c51010000000000014000000000001100000000000050000000012101000000000000300000028062010000000000001000000000000100000048062000000021484200000000000000200000000000000000000002104000000000000600000000c910000000000000010000000000014
  | 7, 57 => 0xc510000000000c810000000000061020000010440200000000000a100000000010010400000000851030000000081100000000480620100000000411010000000000000000000000a102000000000000b00000000c8101000000000000400000000000020000000040100000000000a1000000000006101000000000000b00000000061010000000000007000000010d103000000000a10000000000000130000000000001000000000001200000000000050000000000002000000000000200000000021000000000101100
  | 7, 58 => 0xe1010000000000004000000000000600000000000090000000006100000000004010000000000021040000000000005000000000001500000000000040000000000012000000000a1000000000006101000000000210100000000061020000000002103000000000a10200000000021010000000000008000000010d1020000000006101000000000000500000000000060000000006100000000000a101000000000000100000000061010000000000001000000000e103000005244020000000000000040000000084100
  | 7, 59 => 0xc41010000000000004000000000001100000000000020000000000007000000000e100000000000000700000000000020000000006100000000000e1020000000006101000000000000600000524c420000000000000040000000012100000000000210100000000000010000000000011000000000000f0000000081100000000000000800000000c51000000000000005000000000000000000000000140000000000008000000000610000000000000050000000000005000000000210000000000000010000000002102
  | 7, 60 => 0x121020000000000007000000000e100000000000a1000000000012100000000000210400000000000140000000000004000000000210400000000000040000000000004000000000e1040000000109100000000000a1000000053440200000000000000b0000000000008000000480a200000000000000400000000000020000000108100000000010d10400000000000080000000000004000000000000200000000c81000000000000005000000000000100000000121020000000000009000000000000400000520c5200
  | 7, 61 => 0x10000000006102000000000000c000000000000500000000021010000000000004000000000000400000000000080000000000006000005344020000000000000030000000084101000000000000700000000000060000000000009000000000001200000000000020000000000005000000004110100000204802000000051101200000000000a103000000000a101000000000000a000000000e1040000000000002000000000000f00000000000060000000006100000000001210000000000000020000000000004
  | 7, 62 => 0x40000000000004000000000e100000000000e10400000000121000000000080101000000000000400000000000000000000000000000000000a102000000000000400000000021000000000002101000000001210400000000021000000000006101000000010d103000000000610100000000c81010000000002100000000000a100000000000610100000524c4200000000010510000000000c8100000000000a1010000000000000000000000a1010000000000006000000380a2010000000040101
  | 7, 63 => 0xe10000000000000020000000006100000000000a10000000000000110000000002104000000010d10300000000021020000000000003000000000610000000000121040000000002100000000000000300000000000060000053085201000000000610000000000061000000000000004000000000610300000000021020000000000000000000000000800000000021000000053085201000000000001400000000061000000000000002000000000a1000000000006103000000000001400000000121040000000000005
  | 7, 64 => 0xc1100000000000000800000000c0101000000000001200000000000060000000002104000000000210000000000000010000000000004000000000000100000000000060000000002102000000001210000000000021000000000000006000000000a10000000000000010000000012102000000000610000000000061020000000000000000000000000a000000001210400000000061000000000000014000000001210100000000000020000000002100000000000000700000000811000000000002100
  | 7, 65 => 0x11000000000000500000534842010000000000000000000000a1040000000000011000000000000c00000000000070000000000009000000000e1020000000000000000000000000400000000061000000000000002000000000210400000001041000000000000004000000000e10200000048062000000000012103000000004010100000000021000000000000006000000000000100000000121000000000000002000000000001400000214842010000000002103000000000000a00000000000140000000012100
  | 7, 66 => 0x21020000000000001000000000a102000000000000400000000000090000000000006000000000001200000000000010000000000012000000000000800000000411010000000012100000000000000100000000000080000000000000000000000001200000000121010000000000009000000000000200000000801000000000000001000000000000200000048022000000000000011000000000210100000000411000000000000008000000000210000000531012000000000085101000000000a1000000000006100
  | 7, 67 => 0x14000000000000400000000061000000000000007000000010d10300000000000080000000000006000000000000000000000000040000000000004000000000000f00000544402000000000080100000000000610000000000000040000000000003000000000000a0000000012103000000000610400000000021020000000000009000000000000000000001041000000000000009000000000000a000000000e101000000008510300000000000010000000000001000000000e1000000000002103000000000000d
  | 7, 68 => 0x6101000000000000e0000000006100000000000e10000000000121000000000000008000000000a10100000000000010000000006100000000000000200000304c0201000000000210200000000000110000000000009000000000000200000524c4201000000000000900000000000040000000002103000000010d102000000000000400000000000090000000002100000000000000b0000000000002000000000000300000000021030000000000008000000000000500000000000140000000085102000000000000c
  | 7, 69 => 0x480220100000000121010000000000005000000010d1020000000000008000000000000800000000000080000000000009000000000000800000000000000000000000011000000000000400000000000090000000002101000000010d104000000000000000000000c810000000000000030000000108100000000000000400000000000000000000000009000000001210400000000121040000000012100000000001210200000000000030000000000014000000000e1000000000000002000000000e1040000000000003
  | 7, 70 => 0x610100000001051010000000108100000000000e104000000000e10400000000000060000000000000000000000000400000524c4200000000000000000000000061020000000012101000000010c1000000000000001000000000610400000000061020000000000012000000000610000000000021000000000000008000000000000300000000021040000000000005000000010d10200000000000000000000000004000000000000f0000000006102000000480a2010000000006102000000000000300000000c4100
  | 7, 71 => 0x12102000000000000400000000c81010000000002104000000000000100000000121010000000085102000000000000c00000000000140000000000001000000000210100000000c4101000000000000c0000000000003000000000610000000000000090000000041100000000000001100000000061000000000006101000000000000b000000000000500000000121000000000000006000000010d1040000000000009000000000000000000000061000000000085100000000000000900000000000000000000000005
  | 7, 72 => 0xc9101000000000210100000000000030000000000008000000000000400000000000090000000000002000000000610100000000411000000000000005000000010d10300000000000030000000000004000000000a103000000000e1040000000000000000000010d102000000000a10000000000000140000000000000000000000000500000000021020000000000000000000000000700000000061020000000040101000000000001200000000000080000000006100000000000a10300000000021040000000080100
  | 7, 73 => 0x40100000000000a1030000000000000000000000000900000000c910000000000121000000000000002000000000e104000000000e10100000001051010000000002104000000010d103000000000000400000000401000000000000014000000000000f00000000000070000001802200000000000210300000000061020000000000014000000000a103000000000000c000000008510200000000121000000000000009000000000610000000000000030000000000005000000000000900000000000000000000012100
  | 7, 74 => 0x16000000000210400000000021040000000000008000000000000f000000000000600000524c420100000000000140000000006101000000000a10400000000c5101000000000000000000001041000000000000002000000000a1010000000000004000000000000f00000018022010000000002100000000000000000000000061010000000000008000000000e102000000000001400000000000090000000000000000000004110000000000121010000000006103000000000000100000000121030000000006100
  | 7, 75 => 0x84100000000000610100000000401010000000104100000000000000000000000000060000000000012000000000000400000000c910000000000000040000000000009000000010d103000000000000300000000061000000000000004000000000000400000000c8100000000010d104000000000000e00000000000010000000000008000000000a100000000000000300000000000020000000041100000000010d104000000000a10100000000061020000000040100000000000210400000000061000000000104101
  | 7, 76 => 0x10d10400000000021010000000002100000000000e101000000000000300000000c8100000000010d10400000000000030000000002101000000000000400000028062000000000006101000000010d1040000000000002000000010d1010000000000001000000000000e000000000000b00000000000040000000000000000000000000400000000021040000000000005000000000210200000001081000000000000002000000010d10400000000841000000000000000000000000210000000000121000000054440201
  | 7, 77 => 0xa103000000000000600000000000000000000000005000000010d10400000000000070000000012104000000000610100000000000110000000002100000000000610000000000811000000000000004000000000001600000000c8100000000000000b00000000021040000000012103000000000000200000304c0201000000000000f0000000012103000000000001400000000061010000000000012000000380a20100000000000020000000000006000000000610000000000411000000000000004000000010d102
  | 7, 78 => 0xf000000000210400000000000050000000000004000000010d103000000380a20000000000000040000000000004000000000210100000000061010000000000000000000000000500000000c91010000054440200000000004110000000000021010000004802201000000000000200000000021000000000000016000000000e103000000000e10000000000061010000000002101000000000a101000000000a1010000000040100000000010d104000000010110000000000c110000000000000020000000006102
  | 7, 79 => 0x324c8201000000004010100000000021010000000000005000000000000a00000000000060000000000001000000000a101000000000000e00000000000010000054440200000000000a1010000000002100000000000000300000000000050000000000001000000000210100000000061010000000012100000000480220000000000000000000000002104000000000000b00000000000020000000000003000000480e200000000000000900000000000060000000000003000000000000400000000021000000000000009
  | 7, 80 => 0x20000000081101000000000000b0000000000005000000480220000000000000000000000000003000000000000000000000000080000000000005000000010d102000000001210100000000121000000000002100000000010d1020000000012100000000000000a00000000000020000000012100000000000610000000000000050000000012100000000000000400000000000040000000002103000000000000000000000c510100000000000050000000000006000000000000000000000000140000003806200
  | 7, 81 => 0x524c4200000000000610300000000000000000000000009000000000000100000324c8200000000480620000000000121000000000000000000000010510100000000061000000000012101000000010d104000000000001600000000411010000000006104000000000000900000000021000000000002101000000000a1000000010440201000005444020000000000401010000000000004000000000a10300000000000110000000000012000000000610100000000c810000000000061010000000100100
  | 7, 82 => 0x1000000010d10000000214842010000000000004000000000001100000000021040000000006100000000000000500000000000090000000000001000000010d102000000000a100000000000000400000000021010000000006100000000000000400000000c910000000000021000000000006100000000380a201000000000000800000000061040000000000002000000000210100000000000000000000006104000000000000400000214842000000001802201000000000000700000000000000000000000005
  | 7, 83 => 0x2103000000000000300000000000000000000006101000000000000500000000000020000000105100000000000e10400000000061000000000101100000000000210000000000c8100000000000000400000000000080000000000004000000004110100000000021010000000000001000000000210100000000000020000054440201000000000000900000000021030000000000000000000000610300000000061010000000108100000000000e10100000524c4200000000001210000000000121000000054440201
  | 7, 84 => 0x4010100000000000020000000000007000000000000400000324c820100000000021020000000002100000000380220000000000121000000000006101000000000610000000000021020000000006101000000000610000000000411010000000000005000000010d1040000000002101000000000210100000000061010000000000005000000000000500000000c9102000000010d10300000000000080000000000000000000000000600000000000090000000080100000000000000500000000000140000000041101
  | 7, 85 => 0x610400000000121000000000000005000000000000f000000000000c00000000061000000000000004000000004110000000000021000000000000008000000010410100000000061010000000006100000000000000500000000c9100000000004110100000000021010000000006100000000000e1020000000000014000000000610100000000021000000000012100000000000001400000000000090000000000003000000000001300000000061010000000000002000000000001100000000411000000000002100
  | 7, 86 => 0x9000000008010000000000000040000000000004000000000000300000000411000000000000001000000000000c0000000085102000000004110000000000401000000001802200000000010d10300000000000020000000000008000000000210000000000000010000000000000000000004010000000000c9100000000001210000000000000020000000000009000000000001300000001011010000000000005000000000000400000000121010000000000008000000000210000000000000010000000000004
  | 7, 87 => 0x800000000c5100000000000e10400000000000040000000101101000000010d104000000000000000000000401000000000000014000000000a1020000010440201000000000e104000000000000800000001041000000000006100000000000001100000001091000000000000005000000000a10000000000000040000000012101000000000000100000000c81000000000000011000000000210000000000000000000000006101000000010d10400000000c5100000000001210000000000121000000000000009
  | 7, 88 => 0x40101000000000e10400000000c8101000000000000200000000021000000000041101000000001210400000000000110000000000000000000000210100000000c81010000000006100000000000000000000000021000000000000009000000010d10400000000841080000000000004000000000000200000000000010000000041101000000380a2000000000002100000000000210000000000021010000000041100000000001210400000001001000000000101101000000000000000000000000050000000000000
  | 7, 89 => 0x1210100000048022010000000000004000000000000900000000121000000000012101000000380a200000000000210100000000021000000000002101000000000000100000000021000000000000000000000000e1020000000002102000000000000400000000000040000000006101000000000001400000000000060000000000003000000001210200000000000070000000000007
  | 8, 0 => 0x700000000000030000000041101000000000000500000000000080000000006101000000000000000000000000020000000000000000000000000c000000000000300000000121000000000081100000000000000000000000000020000000000003000000000000300000000c41010000000000003000000008410100000000411000000000000002000000000000a0000000000012000000000a1010000000000001000000000000100000000000000000000000000000000000000300000000000000000000000000
  | 8, 1 => 0x10000000000001000000000000200000000000030000000081100000000000210100000000000030000000000002000000000000000000000c910100000000000160000000000000000000004110000000001011010000000080100000000010d100000000000000000000000000020000000000001000000000000200000000000020000000000004000000000000200000000000020000000109100000000000000000000000000030000000006101000000000000400000000c410000000000c81000000000000001
  | 8, 2 => 0x3000000000000200000000000020000000000000000000000210000000000c41010000000000007000000000000000000000851010000000101101000000000e100000000010d1000000000101100000000000000200000000c510100000000000010000000081100000000004010100000000000140000000000001000000000000400000000000110000000000003000000000000000000000000030000000000003000000000000400000000000020000000000004000000000000000000000801010000000000004
  | 8, 3 => 0x1000000000000800000000061000000000084101000000010510100000000000050000000000003000000000000a00000000000020000000000001000000000a10000000000000000000000002100000000000000200000000000030000000105100000000000000000000000411010000000000000000000000000300000000000010000000000003000000000000000000000000010000000000002000000000e101000000010910100000000000000000000000004000000000000200000000000000000000000003
  | 8, 4 => 0x40000000000000000000000000100000000061000000000000002000000000000000000001051000000000000011000000000000000000000000000000000000001000000000000000000000000020000000000003000000000000000000000c8100000000000000900000000000020000000000013000000000000300000000000010000000000004000000000a100000000000610000000000000030000000041101000000000000200000000000040000000101100000000008410100000000000030000000000002
  | 8, 5 => 0x40000000000003000000000a1000000000109100000000008410000000000801010000000000001000000000000300000000c810000000000000080000000000000000000000000100000000c110100000000000040000000080101000000000000100000000000140000000000000000000000000300000000000040000000000002000000000000000000000000160000000012101000000000000100000000000010000000000004000000000a1010000000000002000000000000400000000c1100
  | 8, 6 => 0x40000000000003000000000000200000001091010000000041100000000010510100000000061010000000000003000000000001400000000000040000000006100000000000000000000000000010000000000001000000000000200000000c1100000000000000000000000000020000000101101000000000000000000001051010000000085100000000000000100000000c410000000000000000000000000008000000000001100000000c81010000000000011000000000000300000000121000000000000003
  | 8, 7 => 0x10d100000000000000100000000c91010000000000001000000000e101000000000a10100000000121000000000000003000000000a100000000008410100000000000040000000000004000000000000400000000411000000000000001000000000000900000000000010000000000012000000000e10000000000000040000000002100000000000000000000000c9100000000000610100000000000030000000000000000000000000300000000000000000000000000000000010910100000000c41000000000000002
  | 8, 8 => 0xc510100000000c91000000000000000000000000000100000000000020000000040101000000010d10000000000000020000000000005000000000001600000000000000000000002100000000000001200000000000000000000000005000000000001100000000000010000000000003000000000000200000000c1101000000000000100000000851000000000000001000000000000300000000c5100000000000000200000000061000000000012101000000000000a000000004010000000000021010000000000001
  | 8, 9 => 0xa100000000000000200000000000000000000006101000000000000200000000000020000000000001000000000000700000000000010000000000001000000000000600000000c5100000000000000100000000000010000000000008000000000000200000000841000000000040100000000000000a00000001011000000000000011000000000000000000000021000000000000000000000000000800000000c1101000000000000300000000000040000000041100000000004010100000000000030000000002100
  | 8, 10 => 0x4000000001210000000000000010000000000002000000000000200000001051000000000000002000000000000400000000000000000000006100000000000001100000000000040000000002101000000000000200000000c9101000000000000200000000000000000000002101000000010d101000000000000100000000000030000000000000000000000000a00000000000050000000000001000000010510000000000000000000000101100000000000e10000000000c810100000000000030000000000003
  | 8, 11 => 0x1011000000000000000000000000a1000000000080101000000000000500000000000160000000000004000000000e1010000000000003000000000000200000000000000000000000001000000000e1010000000000004000000000000000000000000120000000000003000000000000300000000000020000000000000000000000000200000000c5101000000000000200000000801000000000000000000000000a100000000000000800000000401010000000000003000000000000000000000000040000000000000
  | 8, 12 => 0x3000000000000700000000000000000000000005000000010910100000000000010000000000002000000000000500000000811000000000000003000000000001100000000000090000000000002000000000000200000000401000000000000000000000000000400000000801000000000000004000000000000800000001011010000000000002000000000000a000000000000100000000000040000000000000000000000000c00000000000010000000000014000000000000500000000000020000000000000
  | 8, 13 => 0xa10100000000021010000000000001000000010d10000000000000140000000000011000000000000500000000000000000000000004000000000000300000000021000000000006100000000000000400000000c910000000000c0100000000000210000000000000020000000000000000000000000500000000000000000000000002000000000000400000000000010000000000004000000000001200000000000020000000000000000000000000400000000c0100000000008110100000000061000000000000004
  | 8, 14 => 0x20000000000009000000000000e00000000000010000000000000000000000000300000000000040000000006101000000000000100000000000060000000109101000000000001400000000c5100000000000a10000000000401000000000006100000000000000400000001011010000000000006000000000a10100000000000010000000000004000000000001400000000c51000000000002100000000004010000000000c9100000000000a1000000000000004000000000000400000000000010000000080101
  | 8, 15 => 0x41101000000000000000000000000020000000000014000000000000a000000000000600000000c11000000000000011000000000210100000000000030000000041100000000008010000000000000000000000000002000000000000400000000c41000000000000000000000000000400000000811010000000000006000000000e1000000000081101000000000000400000000c8100000000000000200000000000090000000000004000000000001300000000000010000000000002000000000001400000000c8101
  | 8, 16 => 0x1000000000000000000000000000000000000001000000000000400000000c91010000000000011000000000000000000000000010000000000000000000000001400000000061010000000000009000000000000000000000000010000000080101000000000000000000000000020000000000004000000000000a000000000e1010000000000011000000000a101000000000000300000000000010000000000000000000008510100000000c81010000000000000000000000000a00000000801000000000000000
  | 8, 17 => 0xc8100000000000000400000000000030000000000002000000008410000000000000000000000000003000000000610000000000c8100000000000000400000000411010000000000004000000000000300000000c810100000000000050000000000002000000000000b000000000000100000001051010000000105100000000000000000000000000000000000000004000000000000100000000000000000000000004000000000000100000001011000000000000000000000000000000000000000040000000000000
  | 8, 18 => 0x105101000000000210000000000c91000000000002100000000000a101000000000001600000000061010000000000000000000000210000000000000010000000000003000000000610000000000000010000000002101000000000000100000000000020000000000009000000000000400000000000020000000000004000000000000100000000000040000000000004000000000000000000000000040000000012101000000000000300000000000010000000000016000000000000200000000000010000000000004
  | 8, 19 => 0x2000000000000000000000000040000000000001000000000210100000000121010000000000004000000000000100000000000010000000002101000000000000000000001051000000000006100000000000000200000000c5101000000000000100000000000090000000040101000000000000100000000c51000000000000004000000000a100000000004010000000000c910000000000061010000000000000000000000210100000000c91010000000000012000000000000200000000000010000000006101
  | 8, 20 => 0x12100
  | 9, 0 => 0x100000000000010000000000000000000000000000000000000000000000000001000000000000000000000000010000000000000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 13 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_47 roots_47 8 s ws hint
  | 1 => checkCutEntry dom_31 roots_31 8 s ws hint
  | 2 => checkCutEntry dom_55_8 roots_55_8 7 s ws hint
  | 3 => checkCutEntry dom_59_4 roots_59_4 7 s ws hint
  | 4 => checkCutEntry dom_62 roots_62 7 s ws hint
  | 5 => checkCutEntry dom_31_32 roots_31_32 6 s ws hint
  | 6 => checkCutEntry dom_55 roots_55 6 s ws hint
  | 7 => checkCutEntry dom_59 roots_59 6 s ws hint
  | 8 => checkCutEntry dom_61 roots_61 6 s ws hint
  | 9 => checkCutEntry dom_15_16 roots_15_16 5 s ws hint
  | 10 => checkCutEntry dom_15_48 roots_15_48 5 s ws hint
  | 11 => checkCutEntry dom_23 roots_23 5 s ws hint
  | 12 => checkCutEntry dom_39 roots_39 5 s ws hint
  | 13 => checkCutEntry dom_39_8 roots_39_8 5 s ws hint
  | 14 => checkCutEntry dom_27 roots_27 5 s ws hint
  | 15 => checkCutEntry dom_43 roots_43 5 s ws hint
  | 16 => checkCutEntry dom_43_4 roots_43_4 5 s ws hint
  | 17 => checkCutEntry dom_53_8 roots_53_8 5 s ws hint
  | 18 => checkCutEntry dom_57_4 roots_57_4 5 s ws hint
  | 19 => checkCutEntry dom_30 roots_30 5 s ws hint
  | 20 => checkCutEntry dom_30_32 roots_30_32 5 s ws hint
  | 21 => checkCutEntry dom_27_4 roots_27_4 5 s ws hint
  | 22 => checkCutEntry dom_51_8 roots_51_8 5 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_55_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_59_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_62 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31_32 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_55 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_59 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_61 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15_48 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_39 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_39_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_27 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_43 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_43_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_53_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_57_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_30 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_30_32 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_27_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_51_8 _ hc
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
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z1_0 : ∀ i, 0 ≤ i → i < 1 → Z 1 i = true := span_ok (by decide +kernel : span (Z 1) 1 0 = true)
private theorem z1 : ∀ i, 0 ≤ i → i < 1 → Z 1 i = true := z1_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z2_0 : ∀ i, 0 ≤ i → i < 2 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 2 0 = true)
private theorem z2 : ∀ i, 0 ≤ i → i < 2 → Z 2 i = true := z2_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 5 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 5 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 5 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 14 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 14 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 14 → Z 4 i = true := z4_0
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
private theorem z5_48 : ∀ i, 48 ≤ i → i < 61 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 13 48 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 61 → Z 5 i = true := (range_split (range_split z5_0 z5_16) (range_split z5_32 z5_48))
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
private theorem z6_208 : ∀ i, 208 ≤ i → i < 224 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 208 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_224 : ∀ i, 224 ≤ i → i < 240 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 224 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_240 : ∀ i, 240 ≤ i → i < 256 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 240 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_256 : ∀ i, 256 ≤ i → i < 272 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 256 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_272 : ∀ i, 272 ≤ i → i < 288 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 272 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_288 : ∀ i, 288 ≤ i → i < 304 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 288 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_304 : ∀ i, 304 ≤ i → i < 320 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 304 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_320 : ∀ i, 320 ≤ i → i < 336 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 320 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_336 : ∀ i, 336 ≤ i → i < 352 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 336 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_352 : ∀ i, 352 ≤ i → i < 358 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 352 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 358 → Z 6 i = true := (range_split (range_split (range_split (range_split (range_split z6_0 z6_16) (range_split z6_32 z6_48)) (range_split (range_split z6_64 z6_80) (range_split z6_96 z6_112))) (range_split (range_split (range_split z6_128 z6_144) (range_split z6_160 z6_176)) (range_split (range_split z6_192 z6_208) (range_split z6_224 z6_240)))) (range_split (range_split (range_split z6_256 z6_272) (range_split z6_288 z6_304)) (range_split (range_split z6_320 z6_336) z6_352)))
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
private theorem z7_576 : ∀ i, 576 ≤ i → i < 592 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 576 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_592 : ∀ i, 592 ≤ i → i < 608 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 592 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_608 : ∀ i, 608 ≤ i → i < 624 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 608 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_624 : ∀ i, 624 ≤ i → i < 640 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 624 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_640 : ∀ i, 640 ≤ i → i < 656 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 640 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_656 : ∀ i, 656 ≤ i → i < 672 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 656 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_672 : ∀ i, 672 ≤ i → i < 688 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 672 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_688 : ∀ i, 688 ≤ i → i < 704 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 688 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_704 : ∀ i, 704 ≤ i → i < 720 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 704 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_720 : ∀ i, 720 ≤ i → i < 736 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 720 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_736 : ∀ i, 736 ≤ i → i < 752 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 736 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_752 : ∀ i, 752 ≤ i → i < 768 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 752 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_768 : ∀ i, 768 ≤ i → i < 776 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 768 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 776 → Z 7 i = true := (range_split (range_split (range_split (range_split (range_split (range_split z7_0 z7_16) (range_split z7_32 z7_48)) (range_split (range_split z7_64 z7_80) (range_split z7_96 z7_112))) (range_split (range_split (range_split z7_128 z7_144) (range_split z7_160 z7_176)) (range_split (range_split z7_192 z7_208) (range_split z7_224 z7_240)))) (range_split (range_split (range_split (range_split z7_256 z7_272) (range_split z7_288 z7_304)) (range_split (range_split z7_320 z7_336) (range_split z7_352 z7_368))) (range_split (range_split (range_split z7_384 z7_400) (range_split z7_416 z7_432)) (range_split (range_split z7_448 z7_464) (range_split z7_480 z7_496))))) (range_split (range_split (range_split (range_split (range_split z7_512 z7_528) (range_split z7_544 z7_560)) (range_split (range_split z7_576 z7_592) (range_split z7_608 z7_624))) (range_split (range_split (range_split z7_640 z7_656) (range_split z7_672 z7_688)) (range_split (range_split z7_704 z7_720) (range_split z7_736 z7_752)))) z7_768))
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
private theorem z8_240 : ∀ i, 240 ≤ i → i < 256 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 240 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_256 : ∀ i, 256 ≤ i → i < 272 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 256 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_272 : ∀ i, 272 ≤ i → i < 288 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 272 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_288 : ∀ i, 288 ≤ i → i < 298 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 10 288 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 298 → Z 8 i = true := (range_split (range_split (range_split (range_split (range_split z8_0 z8_16) (range_split z8_32 z8_48)) (range_split (range_split z8_64 z8_80) (range_split z8_96 z8_112))) (range_split (range_split (range_split z8_128 z8_144) (range_split z8_160 z8_176)) (range_split (range_split z8_192 z8_208) (range_split z8_224 z8_240)))) (range_split (range_split z8_256 z8_272) z8_288))
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

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 15]⟩], 16⟩

theorem wit_mono : PEqualNP.MetaComplexity.Monotone2 wit := by
  simp [wit, PEqualNP.MetaComplexity.Monotone2]

theorem wit_sz : wit.size ≤ 11 := by decide

set_option maxRecDepth 40000 in
theorem wit_ev : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4276791432) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel

set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_63.testBit r.val = (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276791432) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) (pt6 r.val) := by decide +kernel

theorem lower : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276791432) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) t → 11 ≤ t :=
  lower_to_circuit6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276791432) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) goal_63 11 hT6 (by unfold IsConst; decide) low_63

end PEqualNP.Outside.L_meta_40545_aux

theorem PEqualNP.Outside.L_meta_40545 :
  ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276791432) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4276791432) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  exact ⟨PEqualNP.Outside.L_meta_40545_aux.wit, PEqualNP.Outside.L_meta_40545_aux.wit_mono, le_trans PEqualNP.Outside.L_meta_40545_aux.wit_sz (PEqualNP.Outside.L_meta_40545_aux.lower s hs), PEqualNP.Outside.L_meta_40545_aux.wit_ev⟩
