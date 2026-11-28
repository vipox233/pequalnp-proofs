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

namespace PEqualNP.Outside.L_meta_38987_aux

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
def goal_47 : Nat := 0xeac8eac8e888e888eac8eac8e888e888eac8eac8e888e888eac8eac8e888e888
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_31 : Nat := 0xffffffff
def goal_31 : Nat := 0xeae8e888eae8e888eae8e888eae8e888eae8e888eae8e888eae8e888eae8e888
def roots_31 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xaaaaaa88aa888888aaaaaa88aa888888aaaaaa88aa888888aaaaaa88aa888888
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_47_16 : Nat := 0xffff0000ffff0000
def goal_47_16 : Nat := 0xeaeaeaeaeae8eae8eaeaeaeaeae8eae8eaeaeaeaeae8eae8eaeaeaeaeae8eae8
def roots_47_16 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_59_4 : Nat := 0xf0f0f0f0f0f0f0f0
def goal_59_4 : Nat := 0xeeeeeecceeeeee88eeeeeecceeeeee88eeeeeecceeeeee88eeeeeecceeeeee88
def roots_59_4 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xaaaaaa00aaa0a000aaaaaa00aaa0a000aaaaaa00aaa0a000aaaaaa00aaa0a000
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_62_1 : Nat := 0xaaaaaaaaaaaaaaaa
def goal_62_1 : Nat := 0xffffffccfffcfcccffffffccfffcfcccffffffccfffcfcccffffffccfffcfccc
def roots_62_1 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_15_16 : Nat := 0xffff0000
def goal_15_16 : Nat := 0xeae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8
def roots_15_16 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0]

def dom_29 : Nat := 0x33333333
def goal_29 : Nat := 0xaaa0a000aaa0a000aaa0a000aaa0a000aaa0a000aaa0a000aaa0a000aaa0a000
def roots_29 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_30_1 : Nat := 0xaaaaaaaa
def goal_30_1 : Nat := 0xfffcfcccfffcfcccfffcfcccfffcfcccfffcfcccfffcfcccfffcfcccfffcfccc
def roots_30_1 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_15 : Nat := 0xffff
def goal_15 : Nat := 0xe888e888e888e888e888e888e888e888e888e888e888e888e888e888e888e888
def roots_15 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0]

def dom_27_4 : Nat := 0xf0f0f0f0
def goal_27_4 : Nat := 0xeeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88
def roots_27_4 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xeaeac8c8e8e88888eaeac8c8e8e88888eaeac8c8e8e88888eaeac8c8e8e88888
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_55_8 : Nat := 0xff00ff00ff00ff00
def goal_55_8 : Nat := 0xeaeaeaeaeaeae8e8eaeaeaeaeaeae8e8eaeaeaeaeaeae8e8eaeaeaeaeaeae8e8
def roots_55_8 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_23_8 : Nat := 0xff00ff00
def goal_23_8 : Nat := 0xeaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8
def roots_23_8 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0]

def dom_39_16 : Nat := 0xff000000ff0000
def goal_39_16 : Nat := 0xeaeaeaeae8e8e8e8eaeaeaeae8e8e8e8eaeaeaeae8e8e8e8eaeaeaeae8e8e8e8
def roots_39_16 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0]

def dom_39_8 : Nat := 0xff000000ff00
def goal_39_8 : Nat := 0xeaeaeaeae8e8e8e8eaeaeaeae8e8e8e8eaeaeaeae8e8e8e8eaeaeaeae8e8e8e8
def roots_39_8 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0]

def dom_43_4 : Nat := 0xf0f00000f0f0
def goal_43_4 : Nat := 0xeecceeccee88ee88eecceeccee88ee88eecceeccee88ee88eecceeccee88ee88
def roots_43_4 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_51_4 : Nat := 0xf000f000f000f0
def goal_51_4 : Nat := 0xeeeecccceeee8888eeeecccceeee8888eeeecccceeee8888eeeecccceeee8888
def roots_51_4 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_57 : Nat := 0x303030303030303
def goal_57 : Nat := 0xaaaaaa00aa000000aaaaaa00aa000000aaaaaa00aa000000aaaaaa00aa000000
def roots_57 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_58_1 : Nat := 0xa0a0a0a0a0a0a0a
def goal_58_1 : Nat := 0xffffffccffccccccffffffccffccccccffffffccffccccccffffffccffcccccc
def roots_58_1 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_23 : Nat := 0xff00ff
def goal_23 : Nat := 0xe8e88888e8e88888e8e88888e8e88888e8e88888e8e88888e8e88888e8e88888
def roots_23 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0]

def dom_60_1 : Nat := 0x2222222222222222
def goal_60_1 : Nat := 0xffffff00fff0f000ffffff00fff0f000ffffff00fff0f000ffffff00fff0f000
def roots_60_1 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xeaeaeac8eae8e888eaeaeac8eae8e888eaeaeac8eae8e888eaeaeac8eae8e888
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

namespace S_47
def pairsG : List (Nat × Nat) := [(1, 3), (2, 3), (5, 7), (5, 13), (6, 7), (6, 14), (6, 38), (9, 11), (9, 13), (9, 41), (10, 11), (10, 14), (12, 13), (12, 14), (33, 35), (33, 41), (34, 35), (34, 38), (36, 38), (37, 39), (37, 45), (40, 41), (42, 43), (42, 46), (44, 45), (44, 46)]
def r1sG : List Nat := [1, 2, 5, 5, 6, 6, 6, 9, 9, 9, 10, 10, 12, 12, 33, 33, 34, 34, 36, 37, 37, 40, 42, 42, 44, 44]
def r2sG : List Nat := [3, 3, 7, 13, 7, 14, 38, 11, 13, 41, 11, 14, 13, 14, 35, 41, 35, 38, 38, 39, 45, 41, 43, 46, 45, 46]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [2203520470275, 40828110963494, 13233501572621, 6601566981379, 2204059110915, 5506350320899, 13215715951373, 40707853714214, 13220532587790, 44002041529101, 44019222971177, 37525868383491]
def xsM : List Nat := roots_47.map (· &&& dom_47)
def goalM : Nat := goal_47 &&& dom_47
def NN : Nat → Nat
  | 4 => 3
  | 5 => 28
  | 6 => 19
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xa01735d87ae1bc6c0f1fce07
  | 5, 0 => 0xd4c9adb2a1c0b4b8947e0d9e915d40018cad584288e2183d71f40ace6fa9a6b367ae8f755ba073fa5b61388b54e97e2452ee9a9e4fada6a444dbae4a42c1d77f42829c103e9f5e0b3b21efc12a48ff95286448961b2929df1412d30a13645f700f1fce070afba44c03b0c7d70335d817
  | 6, 0 => 0xa7da18faa1c0b4b8a12a17a39f39fa527ea52a9a7445a6b572657d5c6b7180a36949f7d6686e9bda6594bfe25ba073fa5b61388b4d7877b92fef2b28270b03de160058940f1fce070da784ce
  | 7, 0 => 0xf1fce07
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xaaaa0000aaaa0000000000000000000000000000000000000000000000000000aa000000aa0000000000000000000000000000000000000000000000000000008888000088880000000000000000000000000000000000000000000000000000555500005555000000000000000000000000000000000000000000000000000033330000333300000000000000000000000000000000000000000000000000000f0f00000f0f000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000000000ffff
  | 0, 1 => 0xeeee0000eeee0000000000000000000000000000000000000000000000000000eeee000000000000000000000000000000000000000000000000000000000000e0e00000e0e00000000000000000000000000000000000000000000000000000cccc0000cccc0000000000000000000000000000000000000000000000000000cccc000000000000000000000000000000000000000000000000000000000000cc000000cc000000000000000000000000000000000000000000000000000000c8c80000c8c80000000000000000000000000000000000000000000000000000c0c00000c0c0
  | 0, 2 => 0xff000000f0000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000fafa0000fafa0000000000000000000000000000000000000000000000000000fa000000fa000000000000000000000000000000000000000000000000000000f8f80000f8f80000000000000000000000000000000000000000000000000000f0f00000f0f00000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000f0000000f000
  | 0, 3 => 0xffff000000000000000000000000000000000000000000000000000000000000fff00000fff00000000000000000000000000000000000000000000000000000fff0000000000000000000000000000000000000000000000000000000000000ffcc0000ffcc0000000000000000000000000000000000000000000000000000ffcc0000ff000000000000000000000000000000000000000000000000000000ffcc000000000000000000000000000000000000000000000000000000000000ffaa0000ffaa0000000000000000000000000000000000000000000000000000ff000000ff00
  | 0, 4 => 0xffff0000ff000000000000000000000000000000000000000000000000000000ffff0000f0f00000000000000000000000000000000000000000000000000000ffff0000f0000000000000000000000000000000000000000000000000000000ffff0000cccc0000000000000000000000000000000000000000000000000000ffff0000aaaa0000000000000000000000000000000000000000000000000000ffff0000a0a00000000000000000000000000000000000000000000000000000ffff00008888
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x5d1307401d40c1d1f6123075
  | 5, 0, 0 => 0x7d834c1d5f790307569848c1d5f30708157d2304055f6d230757d84891d5848e307581848c1d584870c0591848c1d5f51230757d848c1d5f652306599648c1d5f6133075
  | 5, 0, 1 => 0x7d84840d5848c1c0575848c1d636122c7585848c1d5230704057d848f155f4870c157dc48a1d5f60c1c257d848c115f5d23075
  | 6, 0, 0 => 0x7d848c1c567d848c1c067d961230767d848c28767d848c20767de61230767d849030767d848c2c7601f60c1c2501f61230457d848c1c4695f612307689f61230767d8592307601f61230757d848c1c16
  | 6, 0, 1 => 0x7d8552307601848c1c057d848f3076
  | 7, 0, 0 => 0x1f6123075
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
  | 0, 0 => 0x18c38d000000000000000000000000000000000000000000000000000000000000038000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003e73c7200000000000000000000000000000000000000000000000000000000033cf38d0000000000000000000000000000000000000000000000000000000000e3cf8300000000000000000000000000000000000000000000000000000000001fc07f0000000000000000000000000000000000000000000000000000000000003fff
  | 0, 1 => 0xdbcfff0000000000000000000000000000000000000000000000000000000000dbc000000000000000000000000000000000000000000000000000000000000018007c0000000000000000000000000000000000000000000000000000000000c30c720000000000000000000000000000000000000000000000000000000000c300000000000000000000000000000000000000000000000000000000000000c00c0000000000000000000000000000000000000000000000000000000000000000700000000000000000000000000000000000000000000000000000000000000070
  | 0, 2 => 0x3e030000000000000000000000000000000000000000000000000000000000003e0000000000000000000000000000000000000000000000000000000000000031cf3fd000000000000000000000000000000000000000000000000000000000300338000000000000000000000000000000000000000000000000000000000031c307c00000000000000000000000000000000000000000000000000000000031c307c00000000000000000000000000000000000000000000000000000000031c00000000000000000000000000000000000000000000000000000000000003003000
  | 0, 3 => 0x3ffc0000000000000000000000000000000000000000000000000000000000003fc3ffc0000000000000000000000000000000000000000000000000000000003fc00000000000000000000000000000000000000000000000000000000000003e33ff20000000000000000000000000000000000000000000000000000000003e33f800000000000000000000000000000000000000000000000000000000003e300000000000000000000000000000000000000000000000000000000000003f8ff8d0000000000000000000000000000000000000000000000000000000003e03f80
  | 0, 4 => 0x3ffff800000000000000000000000000000000000000000000000000000000003fff07c0000000000000000000000000000000000000000000000000000000003fff0000000000000000000000000000000000000000000000000000000000003ffcc720000000000000000000000000000000000000000000000000000000003ffc38d0000000000000000000000000000000000000000000000000000000003ffc00c0000000000000000000000000000000000000000000000000000000003ffc000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x179d79f0000000000000000000000000000000000000000000000000000000001709788000000000000000000000000000000000000000000000000000000000049449700000000000000000000000000000000000000000000000000000000028628600000000000000000000000000000000000000000000000000000000001309308000000000000000000000000000000000000000000000000000000000061c68300000000000000000000000000000000000000000000000000000000000f40570000000000000000000000000000000000000000000000000000000000003dbf
  | 0, 1 => 0x3ffffff0000000000000000000000000000000000000000000000000000000003ffc24000000000000000000000000000000000000000000000000000000000039e397c0000000000000000000000000000000000000000000000000000000002cf6cf70000000000000000000000000000000000000000000000000000000002cf40400000000000000000000000000000000000000000000000000000000002c02ca00000000000000000000000000000000000000000000000000000000002cf6cf700000000000000000000000000000000000000000000000000000000028e2874
  | 0, 2 => 0x3f0bb280000000000000000000000000000000000000000000000000000000003f082000000000000000000000000000000000000000000000000000000000003ffffff0000000000000000000000000000000000000000000000000000000003f0bfa80000000000000000000000000000000000000000000000000000000003df7dff00000000000000000000000000000000000000000000000000000000039e397c00000000000000000000000000000000000000000000000000000000039e00400000000000000000000000000000000000000000000000000000000003903928
  | 0, 3 => 0x3ffc2400000000000000000000000000000000000000000000000000000000003febffc0000000000000000000000000000000000000000000000000000000003fe82400000000000000000000000000000000000000000000000000000000003ffffff0000000000000000000000000000000000000000000000000000000003ffffe80000000000000000000000000000000000000000000000000000000003ffc2400000000000000000000000000000000000000000000000000000000003f9ffbf0000000000000000000000000000000000000000000000000000000003f0bfa8
  | 0, 4 => 0x3ffffe80000000000000000000000000000000000000000000000000000000003fffb7c0000000000000000000000000000000000000000000000000000000003fffb680000000000000000000000000000000000000000000000000000000003ffeef70000000000000000000000000000000000000000000000000000000003ffd7df0000000000000000000000000000000000000000000000000000000003ffd35c0000000000000000000000000000000000000000000000000000000003ffc6d7
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 39 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 39 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 39 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 39 then wireAt i else 0
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_47 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_47 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
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
private theorem z4_0 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_16 : ∀ i, 16 ≤ i → i < 28 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 16 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 28 → Z 5 i = true := (range_split z5_0 z5_16)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 16 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_16 : ∀ i, 16 ≤ i → i < 19 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 3 16 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 19 → Z 6 i = true := (range_split z6_0 z6_16)
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
def pairsG : List (Nat × Nat) := [(1, 3), (2, 3), (5, 7), (5, 13), (5, 21), (6, 7), (6, 14), (6, 22), (9, 11), (9, 13), (9, 25), (10, 11), (10, 14), (12, 13), (12, 14), (17, 19), (17, 21), (17, 25), (18, 19), (18, 22), (20, 21), (20, 22), (24, 25), (26, 27), (26, 30), (28, 29), (28, 30)]
def r1sG : List Nat := [1, 2, 5, 5, 5, 6, 6, 6, 9, 9, 9, 10, 10, 12, 12, 17, 17, 17, 18, 18, 20, 20, 24, 26, 26, 28, 28]
def r2sG : List Nat := [3, 3, 7, 13, 21, 7, 14, 22, 11, 13, 25, 11, 14, 13, 14, 19, 21, 25, 19, 22, 21, 22, 25, 27, 30, 29, 30]
def mpG : Nat := 0x7ffffff
def pool6G : List Nat := [2203520470275, 9917366342925, 2203789626883, 2203655214339, 5506350320899, 9904396832003, 18730437643545, 11033973230851, 13237241053966, 13219994075918, 18700624071939, 13215715951373, 18700624598275]
def xsM : List Nat := roots_31.map (· &&& dom_31)
def goalM : Nat := goal_31 &&& dom_31
def NN : Nat → Nat
  | 4 => 3
  | 5 => 29
  | 6 => 23
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xac05225e9b0612a372a18fee
  | 5, 0 => 0xf0b2ef13e1005450de66a692d591247cc6d1279cbe3fb924ac05225ea571db929e9c03b28c616cec81ea162e64d4803364ae694e5e1d4aa85d1936d05299e96d526e44fc4ca62407439e85fd4111cb143a6b8d4133a231ba32f633fb2637312d25e0cf661d973d961d34fcbf1ac7d7cf104f441f
  | 6, 0 => 0xfd575aabf27aa6a5d051f507be3fb924be3a6442b4992a82ac05225ea0508cfd93c0f7228c616cec818360617ecfa1837702c5a9744473ec554c825e5299e96d3a6b8d4130706e42276bea43206585ea1b8a7ef1126b25b70241d3e1
  | 7, 0 => 0xac05225e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xaa00aa0000000000000000000000000000000000000000000000000000000000a0a0a0a0000000000000000000000000000000000000000000000000000000008888888800000000000000000000000000000000000000000000000000000000555555550000000000000000000000000000000000000000000000000000000033333333000000000000000000000000000000000000000000000000000000000f0f0f0f0000000000000000000000000000000000000000000000000000000000ff00ff000000000000000000000000000000000000000000000000000000000000ffff
  | 0, 1 => 0xee00ee0000000000000000000000000000000000000000000000000000000000e0e0e0e000000000000000000000000000000000000000000000000000000000cccccccc00000000000000000000000000000000000000000000000000000000cc00cc0000000000000000000000000000000000000000000000000000000000c8c8c8c800000000000000000000000000000000000000000000000000000000c0c0c0c000000000000000000000000000000000000000000000000000000000aaaaaaaa00000000000000000000000000000000000000000000000000000000aaaa0000
  | 0, 2 => 0xfafafafa00000000000000000000000000000000000000000000000000000000fa00fa0000000000000000000000000000000000000000000000000000000000f8f8f8f800000000000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000f0f0f00000000000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000eeeeeeee
  | 0, 3 => 0xfff0ff0000000000000000000000000000000000000000000000000000000000ffccffcc00000000000000000000000000000000000000000000000000000000ffaaffaa00000000000000000000000000000000000000000000000000000000ff88ff8800000000000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000ff00f00000000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000fcfcfcfc
  | 0, 4 => 0xffffff0000000000000000000000000000000000000000000000000000000000fffff0f000000000000000000000000000000000000000000000000000000000ffffcc0000000000000000000000000000000000000000000000000000000000ffffaaaa00000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000fff0fff0
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x216d434950194cd25006923494
  | 5, 0, 0 => 0x86044d25636d4349585b34909616d4405585b5040d6171434958543cd25616d4344585b4cd2561349081585b5cd1961594349585a50d25616d42c9585434405617d43495
  | 5, 0, 1 => 0x216d8289585b3440965654349585d50d1d616ce349585b5090d616d4349550d24101615090c158543490561794309585b24309616d53495
  | 6, 0, 0 => 0x85b50d245685b614349602150d24159216d4349685b50d24369616d4349685b50d289685b50d24860216cd24250216d4344585e6d434968a16d4349685b5d4349685b50d240685b50d309685b5123496
  | 6, 0, 1 => 0x85b50d242685b50d246685b50d24460216d4243585b654349685b51034960216d43495
  | 7, 0, 0 => 0x216d43495
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
  | 0, 0 => 0x700000000000000000000000000000000000000000000000000000000000000001c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007fc78e2000000000000000000000000000000000000000000000000000000000673e71d0000000000000000000000000000000000000000000000000000000001cf9f0300000000000000000000000000000000000000000000000000000000003f80ff0000000000000000000000000000000000000000000000000000000000007fff
  | 0, 1 => 0x1801f0000000000000000000000000000000000000000000000000000000000000000fc00000000000000000000000000000000000000000000000000000000018c18e2000000000000000000000000000000000000000000000000000000000180180000000000000000000000000000000000000000000000000000000000000000e000000000000000000000000000000000000000000000000000000000000000e0000000000000000000000000000000000000000000000000000000000003871d0000000000000000000000000000000000000000000000000000000000038000
  | 0, 2 => 0x633e7fd000000000000000000000000000000000000000000000000000000000600670000000000000000000000000000000000000000000000000000000000063060fc00000000000000000000000000000000000000000000000000000000063060fc00000000000000000000000000000000000000000000000000000000063060000000000000000000000000000000000000000000000000000000000006300000000000000000000000000000000000000000000000000000000000000600600000000000000000000000000000000000000000000000000000000000018f9fff
  | 0, 3 => 0x7f07f000000000000000000000000000000000000000000000000000000000007cc7fe20000000000000000000000000000000000000000000000000000000007c3ff1d0000000000000000000000000000000000000000000000000000000007c07f000000000000000000000000000000000000000000000000000000000007c07f000000000000000000000000000000000000000000000000000000000007c060000000000000000000000000000000000000000000000000000000000007c000000000000000000000000000000000000000000000000000000000000007bc78fe
  | 0, 4 => 0x7ffff000000000000000000000000000000000000000000000000000000000007ffe0fc0000000000000000000000000000000000000000000000000000000007ff98000000000000000000000000000000000000000000000000000000000007ff871d0000000000000000000000000000000000000000000000000000000007ff80000000000000000000000000000000000000000000000000000000000007f07ffc
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x2c22f08000000000000000000000000000000000000000000000000000000000211223c000000000000000000000000000000000000000000000000000000000084892700000000000000000000000000000000000000000000000000000000052850c000000000000000000000000000000000000000000000000000000000025326180000000000000000000000000000000000000000000000000000000000c68d0300000000000000000000000000000000000000000000000000000000003d80b70000000000000000000000000000000000000000000000000000000000007b6f
  | 0, 1 => 0x7c27f4800000000000000000000000000000000000000000000000000000000073972fc0000000000000000000000000000000000000000000000000000000005acd9e700000000000000000000000000000000000000000000000000000000058059400000000000000000000000000000000000000000000000000000000005acd9e700000000000000000000000000000000000000000000000000000000052850e40000000000000000000000000000000000000000000000000000000002d7af3f0000000000000000000000000000000000000000000000000000000002d78410
  | 0, 2 => 0x7ffffff0000000000000000000000000000000000000000000000000000000007c27f480000000000000000000000000000000000000000000000000000000007bdfbff00000000000000000000000000000000000000000000000000000000073972fc00000000000000000000000000000000000000000000000000000000073972d8000000000000000000000000000000000000000000000000000000000739009000000000000000000000000000000000000000000000000000000000070072480000000000000000000000000000000000000000000000000000000007ffffff
  | 0, 3 => 0x7fb7fd80000000000000000000000000000000000000000000000000000000007eeffef0000000000000000000000000000000000000000000000000000000007d7ff7f0000000000000000000000000000000000000000000000000000000007c6ff6f0000000000000000000000000000000000000000000000000000000007c27f480000000000000000000000000000000000000000000000000000000007c276480000000000000000000000000000000000000000000000000000000007c204000000000000000000000000000000000000000000000000000000000007bdfbff
  | 0, 4 => 0x7ffffd80000000000000000000000000000000000000000000000000000000007fff6fc0000000000000000000000000000000000000000000000000000000007ffddd00000000000000000000000000000000000000000000000000000000007ffafbf0000000000000000000000000000000000000000000000000000000007ff84900000000000000000000000000000000000000000000000000000000007fb7ffc
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 38 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 38 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 38 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 38 then wireAt i else 0
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
def pairsG : List (Nat × Nat) := [(1, 3), (2, 3), (9, 11), (9, 25), (9, 41), (10, 11), (17, 19), (17, 25), (17, 49), (18, 19), (24, 25), (26, 27), (33, 35), (33, 41), (33, 49), (34, 35), (40, 41), (42, 43), (48, 49), (50, 51), (56, 57), (58, 59)]
def r1sG : List Nat := [1, 2, 9, 9, 9, 10, 17, 17, 17, 18, 24, 26, 33, 33, 33, 34, 40, 42, 48, 50, 56, 58]
def r2sG : List Nat := [3, 3, 11, 25, 41, 11, 19, 25, 49, 19, 25, 27, 35, 41, 49, 35, 41, 43, 49, 51, 57, 59]
def mpG : Nat := 0x3fffff
def pool6G : List Nat := [18730909247769]
def xsM : List Nat := roots_59.map (· &&& dom_59)
def goalM : Nat := goal_59 &&& dom_59
def NN : Nat → Nat
  | 4 => 1
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xc3827481
  | 5, 0 => 0xc3827481
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f0f0f000000000000000000000000000000000000000000000000000000000f0f00000f0f00000000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000c0c0c0c0c0c0c0c0000000000000000000000000000000000000000000000000a0a0a0a0a0a0a0a
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_59 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_59 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]]
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
  scr dom_59 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_59 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_59 roots_59 goal_59 6 := by
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

theorem low_59 : Lower dom_59 roots_59 goal_59 6 := S_59.noCircuit

namespace S_47_16
def pairsG : List (Nat × Nat) := [(17, 19), (17, 21), (17, 25), (17, 49), (18, 19), (18, 22), (20, 21), (20, 22), (24, 25), (26, 27), (26, 30), (28, 29), (28, 30), (48, 49), (50, 51), (50, 54), (52, 53), (52, 54), (56, 57), (58, 59), (58, 62), (60, 61), (60, 62)]
def r1sG : List Nat := [17, 17, 17, 17, 18, 18, 20, 20, 24, 26, 26, 28, 28, 48, 50, 50, 52, 52, 56, 58, 58, 60, 60]
def r2sG : List Nat := [19, 21, 25, 49, 19, 22, 21, 22, 25, 27, 30, 29, 30, 49, 51, 54, 53, 54, 57, 59, 62, 61, 62]
def mpG : Nat := 0x7fffff
def pool6G : List Nat := [19864560735507, 22063550436117]
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
  | 0, 0 => 0x7fff0000000000000000000000000000000000000000000000000000000000007fe00000000000000000000000000000000000000000000000000000000000007c1f0000000000000000000000000000000000000000000000000000000000006318c0000000000000000000000000000000000000000000000000000000000018c630000000000000000000000000000000000000000000000000000000000000000f
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x7fff0c00000000000000000000000000000000000000000000000000000000007fe00800000000000000000000000000000000000000000000000000000000007c1f040000000000000000000000000000000000000000000000000000000000739ce200000000000000000000000000000000000000000000000000000000005ad6b100000000000000000000000000000000000000000000000000000000002d6b5f
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

namespace S_59_4
def pairsG : List (Nat × Nat) := [(5, 7), (5, 13), (5, 21), (6, 7), (6, 14), (6, 22), (6, 38), (12, 13), (12, 14), (20, 21), (20, 22), (28, 29), (28, 30), (36, 38), (37, 39), (37, 45), (37, 53), (44, 45), (44, 46), (52, 53), (52, 54), (60, 61), (60, 62)]
def r1sG : List Nat := [5, 5, 5, 6, 6, 6, 6, 12, 12, 20, 20, 28, 28, 36, 37, 37, 37, 44, 44, 52, 52, 60, 60]
def r2sG : List Nat := [7, 13, 21, 7, 14, 22, 38, 13, 14, 21, 22, 29, 30, 38, 39, 45, 53, 45, 46, 53, 54, 61, 62]
def mpG : Nat := 0x7fffff
def pool6G : List Nat := [6618746850567, 13219994076942]
def xsM : List Nat := roots_59_4.map (· &&& dom_59_4)
def goalM : Nat := goal_59_4 &&& dom_59_4
def NN : Nat → Nat
  | 4 => 2
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x89a9a1a25417588c
  | 5, 0 => 0x89a9a1a2
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f0f0f000000000000000000000000000000000000000000000000000000000f0f0f000f0f0f000000000000000000000000000000000000000000000000000f0f00000f0f00000000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000c0c0c0c0c0c0c0c0000000000000000000000000000000000000000000000000a0a0a0a0a0a0a0a0
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
  | 0, 0 => 0x7fe00000000000000000000000000000000000000000000000000000000000007e1f800000000000000000000000000000000000000000000000000000000000781e0000000000000000000000000000000000000000000000000000000000006619800000000000000000000000000000000000000000000000000000000000000078000000000000000000000000000000000000000000000000000000000001c007
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x7fe04000000000000000000000000000000000000000000000000000000000007f9fb60000000000000000000000000000000000000000000000000000000000791e240000000000000000000000000000000000000000000000000000000000669992000000000000000000000000000000000000000000000000000000000054757900000000000000000000000000000000000000000000000000000000002bca8f
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_59_4 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_59_4 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_59_4 == dom_59_4) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_59_4 goalM u ys) : RunD dom_59_4 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_59_4 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_59_4 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_59_4 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_59_4 roots_59_4 goal_59_4 6 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_59_4 goal_59_4 := by
    have h0 : isConstB dom_59_4 goal_59_4 = false := by decide +kernel
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

end S_59_4

theorem low_59_4 : Lower dom_59_4 roots_59_4 goal_59_4 6 := S_59_4.noCircuit

namespace S_61
def pairsG : List (Nat × Nat) := [(5, 13), (5, 21), (9, 13), (9, 25), (9, 41), (12, 13), (17, 21), (17, 25), (17, 49), (20, 21), (24, 25), (28, 29), (33, 41), (33, 49), (37, 45), (37, 53), (40, 41), (44, 45), (48, 49), (52, 53), (56, 57), (60, 61)]
def r1sG : List Nat := [5, 5, 9, 9, 9, 12, 17, 17, 17, 20, 24, 28, 33, 33, 37, 37, 40, 44, 48, 52, 56, 60]
def r2sG : List Nat := [13, 21, 13, 25, 41, 13, 21, 25, 49, 21, 25, 29, 41, 49, 45, 53, 41, 45, 49, 53, 57, 61]
def mpG : Nat := 0x3fffff
def pool6G : List Nat := [9917366342925, 18730437643545]
def xsM : List Nat := roots_61.map (· &&& dom_61)
def goalM : Nat := goal_61 &&& dom_61
def NN : Nat → Nat
  | 4 => 2
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x995298d198cfc2de
  | 5, 0 => 0x995298d1
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x333333333030303000000000000000000000000000000000000000000000000033333333000000000000000000000000000000000000000000000000000000003333000033330000000000000000000000000000000000000000000000000000330033003300330000000000000000000000000000000000000000000000000030303030303030300000000000000000000000000000000000000000000000002222222222222222
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x234428ad04
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
  | 0, 0 => 0x3ffa2300000000000000000000000000000000000000000000000000000000003ff00000000000000000000000000000000000000000000000000000000000003c0fc00000000000000000000000000000000000000000000000000000000000330c3c00000000000000000000000000000000000000000000000000000000002aca23000000000000000000000000000000000000000000000000000000000000f1df
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3ffb7700000000000000000000000000000000000000000000000000000000003ff11000000000000000000000000000000000000000000000000000000000003cafca0000000000000000000000000000000000000000000000000000000000335cbd00000000000000000000000000000000000000000000000000000000002aca6700000000000000000000000000000000000000000000000000000000003fffff
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

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
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

namespace S_62_1
def pairsG : List (Nat × Nat) := [(1, 3), (5, 7), (5, 13), (5, 21), (9, 11), (9, 13), (9, 25), (9, 41), (17, 19), (17, 21), (17, 25), (17, 49), (33, 35), (33, 41), (33, 49), (37, 39), (37, 45), (37, 53)]
def r1sG : List Nat := [1, 5, 5, 5, 9, 9, 9, 9, 17, 17, 17, 17, 33, 33, 33, 37, 37, 37]
def r2sG : List Nat := [3, 7, 13, 21, 11, 13, 25, 41, 19, 21, 25, 49, 35, 41, 49, 39, 45, 53]
def mpG : Nat := 0x3ffff
def pool6G : List Nat := [9917366342925, 18730437643545]
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
  | 0, 0 => 0x3f00e000000000000000000000000000000000000000000000000000000000003f0000000000000000000000000000000000000000000000000000000000000000f0000000000000000000000000000000000000000000000000000000000000000f0000000000000000000000000000000000000000000000000000000000003800e0000000000000000000000000000000000000000000000000000000000000000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3faae000000000000000000000000000000000000000000000000000000000003f8800000000000000000000000000000000000000000000000000000000000024f4800000000000000000000000000000000000000000000000000000000000124f4000000000000000000000000000000000000000000000000000000000003822e0000000000000000000000000000000000000000000000000000000000009113
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

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
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

namespace S_15_16
def pairsG : List (Nat × Nat) := [(17, 19), (17, 21), (17, 25), (18, 19), (18, 22), (20, 21), (20, 22), (24, 25), (26, 27), (26, 30), (28, 29), (28, 30)]
def r1sG : List Nat := [17, 17, 17, 18, 18, 20, 20, 24, 26, 26, 28, 28]
def r2sG : List Nat := [19, 21, 25, 19, 22, 21, 22, 25, 27, 30, 29, 30]
def mpG : Nat := 0xfff
def pool6G : List Nat := [19864560735507, 22063550436117]
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_15_16 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_15_16 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]
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

namespace S_29
def pairsG : List (Nat × Nat) := [(5, 13), (5, 21), (9, 13), (9, 25), (12, 13), (17, 21), (17, 25), (20, 21), (24, 25), (28, 29)]
def r1sG : List Nat := [5, 5, 9, 9, 12, 17, 17, 20, 24, 28]
def r2sG : List Nat := [13, 21, 13, 25, 13, 21, 25, 21, 25, 29]
def mpG : Nat := 0x3ff
def pool6G : List Nat := [9917366342925]
def xsM : List Nat := roots_29.map (· &&& dom_29)
def goalM : Nat := goal_29 &&& dom_29
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x13ac53d7
  | 4, 0 => 0x13ac53d7
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x33330000000000000000000000000000000000000000000000000000000000003300330000000000000000000000000000000000000000000000000000000000303030300000000000000000000000000000000000000000000000000000000022222222
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_29 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_29 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_29 == dom_29) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_29 goalM u ys) : RunD dom_29 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_29 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_29 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_29 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_29 roots_29 goal_29 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_29 goal_29 := by
    have h0 : isConstB dom_29 goal_29 = false := by decide +kernel
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

end S_29

theorem low_29 : Lower dom_29 roots_29 goal_29 5 := S_29.noCircuit

namespace S_30_1
def pairsG : List (Nat × Nat) := [(1, 3), (5, 7), (5, 13), (5, 21), (9, 11), (9, 13), (9, 25), (17, 19), (17, 21), (17, 25)]
def r1sG : List Nat := [1, 5, 5, 5, 9, 9, 9, 17, 17, 17]
def r2sG : List Nat := [3, 7, 13, 21, 11, 13, 25, 19, 21, 25]
def mpG : Nat := 0x3ff
def pool6G : List Nat := [9917366342925]
def xsM : List Nat := roots_30_1.map (· &&& dom_30_1)
def goalM : Nat := goal_30_1 &&& dom_30_1
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xf9b308f5
  | 4, 0 => 0xf9b308f5
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xaaaa000000000000000000000000000000000000000000000000000000000000aa00aa0000000000000000000000000000000000000000000000000000000000a0a0a0a00000000000000000000000000000000000000000000000000000000088888888
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_30_1 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_30_1 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_30_1 == dom_30_1) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_30_1 goalM u ys) : RunD dom_30_1 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_30_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_30_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_30_1 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_30_1 roots_30_1 goal_30_1 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_30_1 goal_30_1 := by
    have h0 : isConstB dom_30_1 goal_30_1 = false := by decide +kernel
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

end S_30_1

theorem low_30_1 : Lower dom_30_1 roots_30_1 goal_30_1 5 := S_30_1.noCircuit

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

namespace S_27_4
def pairsG : List (Nat × Nat) := [(5, 7), (5, 13), (5, 21), (6, 7), (6, 14), (6, 22), (12, 13), (12, 14), (20, 21), (20, 22), (28, 29), (28, 30)]
def r1sG : List Nat := [5, 5, 5, 6, 6, 6, 12, 12, 20, 20, 28, 28]
def r2sG : List Nat := [7, 13, 21, 7, 14, 22, 13, 14, 21, 22, 29, 30]
def mpG : Nat := 0xfff
def pool6G : List Nat := [6618746850567]
def xsM : List Nat := roots_27_4.map (· &&& dom_27_4)
def goalM : Nat := goal_27_4 &&& dom_27_4
def NN : Nat → Nat
  | 3 => 2
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xde1ca231410f566f
  | 4, 0 => 0xde1ca231
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f0f00000000000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000c0c0c0c000000000000000000000000000000000000000000000000000000000a0a0a0a0
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_27_4 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_27_4 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
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

def isoMv_55 : List (Nat × Nat) := [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_55 : Lower dom_55 roots_55 goal_55 8 :=
  lower_iso isoMv_55 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47

def isoMv_55_8 : List (Nat × Nat) := [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_55_8 : Lower dom_55_8 roots_55_8 goal_55_8 6 :=
  lower_iso isoMv_55_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47_16

def isoMv_23_8 : List (Nat × Nat) := [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_23_8 : Lower dom_23_8 roots_23_8 goal_23_8 5 :=
  lower_iso isoMv_23_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15_16

def isoMv_39_16 : List (Nat × Nat) := [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]
theorem low_39_16 : Lower dom_39_16 roots_39_16 goal_39_16 5 :=
  lower_iso isoMv_39_16 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15_16

def isoMv_39_8 : List (Nat × Nat) := [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]
theorem low_39_8 : Lower dom_39_8 roots_39_8 goal_39_8 5 :=
  lower_iso isoMv_39_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15_16

def isoMv_43_4 : List (Nat × Nat) := [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]
theorem low_43_4 : Lower dom_43_4 roots_43_4 goal_43_4 5 :=
  lower_iso isoMv_43_4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15_16

def isoMv_51_4 : List (Nat × Nat) := [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]
theorem low_51_4 : Lower dom_51_4 roots_51_4 goal_51_4 5 :=
  lower_iso isoMv_51_4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15_16

def isoMv_57 : List (Nat × Nat) := [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_57 : Lower dom_57 roots_57 goal_57 5 :=
  lower_iso isoMv_57 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_29

def isoMv_58_1 : List (Nat × Nat) := [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_58_1 : Lower dom_58_1 roots_58_1 goal_58_1 5 :=
  lower_iso isoMv_58_1 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_30_1

def isoMv_23 : List (Nat × Nat) := [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_23 : Lower dom_23 roots_23 goal_23 5 :=
  lower_iso isoMv_23 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15

def isoMv_60_1 : List (Nat × Nat) := [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)]
theorem low_60_1 : Lower dom_60_1 roots_60_1 goal_60_1 5 :=
  lower_iso isoMv_60_1 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_27_4

namespace S_63
def pairsG : List (Nat × Nat) := [(1, 3), (2, 3), (5, 7), (5, 13), (5, 21), (6, 7), (6, 14), (6, 22), (6, 38), (9, 11), (9, 13), (9, 25), (9, 41), (10, 11), (10, 14), (12, 13), (12, 14), (17, 19), (17, 21), (17, 25), (17, 49), (18, 19), (18, 22), (20, 21), (20, 22), (24, 25), (26, 27), (26, 30), (28, 29), (28, 30), (33, 35), (33, 41), (33, 49), (34, 35), (34, 38), (36, 38), (37, 39), (37, 45), (37, 53), (40, 41), (42, 43), (42, 46), (44, 45), (44, 46), (48, 49), (50, 51), (50, 54), (52, 53), (52, 54), (56, 57), (58, 59), (58, 62), (60, 61), (60, 62)]
def r1sG : List Nat := [1, 2, 5, 5, 5, 6, 6, 6, 6, 9, 9, 9, 9, 10, 10, 12, 12, 17, 17, 17, 17, 18, 18, 20, 20, 24, 26, 26, 28, 28, 33, 33, 33, 34, 34, 36, 37, 37, 37, 40, 42, 42, 44, 44, 48, 50, 50, 52, 52, 56, 58, 58, 60, 60]
def r2sG : List Nat := [3, 3, 7, 13, 21, 7, 14, 22, 38, 11, 13, 25, 41, 11, 14, 13, 14, 19, 21, 25, 49, 19, 22, 21, 22, 25, 27, 30, 29, 30, 35, 41, 49, 35, 38, 38, 39, 45, 53, 41, 43, 46, 45, 46, 49, 51, 54, 53, 54, 57, 59, 62, 61, 62]
def mpG : Nat := 0x3fffffffffffff
def pool6G : List Nat := [5506350320899, 13215715951373, 9917366342925, 2203789626883, 2203655214339, 9904396832003, 28613224762646, 26427035878169, 28613358982414, 26461395092249, 40828110963494, 18730437643545, 2203756071683, 28626059133721, 6618746850563, 19864425991427, 37525331512579, 22063684851221, 13233232088589, 6601701725443, 9921576701187, 2204192085251, 2204057341187, 2204193854979, 2204059110915, 5506249656067, 5506485064963, 22011809497877, 40707853714214, 37409318833446, 28660418347801, 18713325145365, 11033973230851, 19864695148035, 13220532587790, 22016625612054, 37525466256643, 18730909247769, 18730454486553, 18717804467459, 44019222971177, 52918394159921, 37525868383491, 37422386974211, 37422387041539, 37457283650819, 37422789168387, 5502004955907]
def xsM : List Nat := roots_63.map (· &&& dom_63)
def goalM : Nat := goal_63 &&& dom_63
def NN : Nat → Nat
  | 5 => 14
  | 6 => 190
  | 7 => 667
  | 8 => 318
  | 9 => 23
  | 10 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0xdf0487c5d4bdaf90c83672dca7cb156a7edafcda7b30d805779a61b95704cfcd3d6a961f3294dd2632727b192c1c38e1173a1453006bff6a
  | 6, 0 => 0x3554a6da3404b2bb32973ec632938f05320e0faf318d3d04318221913037bc2b2fef84802f8051022e6465742cab1c642be61f7b2a74cf622a71da7129bed322293a08ea2937eecd2909654c2779c54f249d0b20240fb77123b5d9fe2248897b21fbc4142075da641fc65dff1ed15b311a85e0ab1a0f2ada19f789091878a82817ee431717e77c8415753090142a6855136f20cf12f8fd5912f11197126bf4011252f7d91120e2e30fa22a3f0e5d008b0dfc2cef0d3f24990d1e5eea0c4110400c236eef0a2e374109e76cd909cab3ef096e94380956f26708f317a506e4336306165d760407793401af582a0187745c01066dc7003a4c0c0026e37e00054bc7
  | 6, 1 => 0x71a3faaf710c539970de2b656e027d566d6fc82a6bc292956ae507fa6a8772f968e5d86667e8795567aab8ca6759339d67565d1c66cc164966b0725161d7af80606bbcf75f398d535e2d8aab5a657cac59be44955804cc7a57856ccf57530f6056488c3a55ea38c6550866b7550704485076c1ad4ffd7cef4f528bca4ea3fc3c4e5da3554e5a49ad4e19168a4d40ae504c30865f4ae0a75d4aae3b9e4a91368748558c3946cf2c524642c44a4610dfd6458b6080458570404478aa4f44081bfe43660a1b41d2b5e93fd62b0b3fb30c283c90e5203c86b61d3baa073b3ac40ac739c918c6390e3a143805244f375bb89236bd7d7436509f3435768dcd35704934
  | 6, 2 => 0xfe552278fe244c4dfdaf8bdcfd41013ffa36c6f9f6ff1a04f5061260eca992adea8c7e56ea742c98e8d9024ce85d85b9e368b210e2c800d1defb0a41db350d38d4e034e8cc64bb85c7cc907dc467b698c219efd3c116d5dfc042fab5c01708dcbb404d62b8e76ab4b7817fbcb0bea196af75e2bdaeaaea6baea42dd9ad99850eaa63c7b4a8531185a6f4ec37a6b1151ba5743486a35c9dd69e499af29ba661528b05cab08941d6398829108187cd13b98744a6f8842bd5eb8421f278829f3bf68250d0be820585ba7e89e7627dc38fba7cc7f1077c64872b7b41725c7afb0e9877de0af7744fc2e8734bd994722eeeb6721c8e4b71fea554
  | 7, 0 => 0x102497a90f9aa5fd0f1986a90f115ba20ee2d2210ecc23a60e974d5b0e7db3450e1f184a0dd633720db432850da46fb90d871bf50d7f85ab0d6e8d170d3586890d05cbda0cb5970c0c825c970c7bcab90c36bb900c13a5aa0c0bf6ea0bd70bfb0ba0f9160b80dabe0b76e6c50b2c8ce60af197a60a7677f50a53c4d609d9969709695d400964338609199978080f361f07d530e907ca96c507c20e27078179cf06fb5c5206237d4e060e01a40594ac960535f29d05223865050dc1e804aea85504824cd40459b5e30442bd8603d8385d0398ec0502b14372020567c901eac2890166035701551783015437cd013ad0c90124c53e00f9b8fb00d76e0200b91207
  | 7, 1 => 0x232c6add2325c90b22d2ddb122c96b3022afbece2288025421eaa96f21d562ba20e2e2e9204fb0ae1f9547f51f4cfea11edd0b6f1edba1481ed55caf1d160c6b1cd038361ccf54311cc101ab1c96ea491c193f401c0aecba1b25678b1afecaa01ac819931ab658ae1aa1953a1a63b4731a4dc7a419ba301a198e7f10194d51da18f302eb18734073186cfbda1860cf551836a7e61830634d182bf92618261f781813153417f938b617b77a521701656116c91dcd16bceacf16a0de49166385a016446b9c161648bc15af65f1153fc09e14b9a6ad1421b37a13ea83c213346ed1130a5a8912ec372612763853121c5c8e117804a41161181a109faa42105fce31
  | 7, 2 => 0x37a858aa3791ff6b3750913536b521a2369202bf364691d83615bd7835abdc113587494434d88c5e34a369a7345ddff534487e1233d8677333d25e6233cd017f33b85c43330bca3f32fa2f9532a889b1328e87083285462232113f4a3176335b3156fc533115c930309e6aff301b2a852fa88bf32f2d39052e9b5e9e2e3b996a2dcb18752dc5ce1f2d8de92d2d3e70562ce139a22c7c27652bbea46f2b87620c2b811d732ae913f02aa00b9d2a60e87e2a245e7b29f9c57229e188d329e0d67129af2b6429428e4b293f76f029259dd728cec22628bd116f28a4a83e2842fbd327d2573726f168c92648e3a824f59d08243e50102414ae9a23f0c29e234835d9
  | 7, 3 => 0x47703dcb476a5be9476086824755b8444700cb0e46de759446c7c6354625da8245a7f598459ecff744ed24264493839c445ca64c441e848e441caf3c43d1a48743c1fcc943686f9d434ac0324336d2af432dfd82431f7df7430c7f9b42c7651641b8ea3b40e5429a40e1c31a40bbc12740a60e37406a83da401a1c4f3fdba9f43fb404613f82b8df3f62ae583f3bf5403f2afc363f15457d3ebac68e3e6664c13d3e89f93d2c7c353cc696da3c9d75a23c346cd83c21f90f3c21b4153b9031bd3b34c0e23b0a44b33b05d6f73a8cc1993a8512d93a4fc20639c6347939b8a2b739a3fedd38bbb164382f747e3821da6638120974380d7bfe3803b6ee37b0076a
  | 7, 4 => 0x5a7ee5485a292fbd59a0c2fc592546695810d46d5802414f574ab38e56488c3a5618ad15551f842c54fb57fa54dbf01954d5ab8054bebf6d546df95f5467b4c65462936b53cbf68653ca920853c014995372c4795318541d52a2b5415253af295184d1d450e499dd509f358a506c7ad04fbdd0064f9ac8844f54e6cc4ebf453b4ea474154e2566f84e086b364de1baa04d86bbea4d84259f4d1a0f054ce115d74c77c2484c16af5f4bacc54f4ba1260e4b8c97694b50406a4b48acc94b25a97b4b0c2c394aeba8ec4acde2064ab9f0674a9428d24a55e6434a530fc24a3f5f3c4a0b380549c3e2a949bb2fc349ae952049292ce247ff7ab347c6c73247768264
  | 7, 5 => 0x6a2e06a76a00c0a56921832768c3ac2e68ade545689b9903684a9053682efe61680f79936805cfb767c6dab467ad21da6733942567288891671ea51e66e4732066d0a35666b2ba9b669e55736623177d65b3f9f76532bf646529158864edbd3264ec195f64c52366649ea5e064497e5c643609f56414205d63669d956332600f6318195562d73fc862a39a8161a45f8b60fe5bb260afae3b6049964d604411db601579706008d5905fd7fc205fd04d605f6139d15f411ea25edbff035ed6a3f15ecd913b5df837b25d71535d5d384f2c5d0b15675cbb87cc5cb746015c97debb5c3b8dfc5bf13ab45b8e88025b6fefcf5b65c3955b3bed485aa8a6b95a859b92
  | 7, 6 => 0x81b726b3817be6a280977014809286e3808751628069eaef7fca544a7f24c13b7eadd0e57ead80c27e9aa7927d5aa3917d300b997bd0c6937aaf2d897a2a8dff79df051878b0103578a6665978299fcd77e8b9bb77abf413773c94b176a070ea76863e3b765ba64375b7ea5c74d57dbf74cf39e4748af05a73437dc2733d888d7301de5f727718da7238707e71b7c8f27108872f70eea42e70ea335870607efa7018533270120e99700aec186fb8decd6f90c8936f56ded46f410f6b6ee314666edb0ec36ecfcc7c6e16b7eb6e0e67d66e027d566de93f766d72ad596c85f2fa6c3e88df6c3d1b7e6c2a7fa76ba0665d6b302ff16ac5c8b56a6a7ad66a41599e
  | 7, 7 => 0x9de5cf519d72dd149d648c2e9b258fe99a4655a29985a136997632ef98386cf69823da6497f306049742e105970d416896da145596d6a62494d77821949f308d9499c431947d9aae939a9e619372f1e3931be89e93104a2b92b8eaa091d9edf19196ca6a9190d39c916407a090f610e690b936008fa972eb8f0aa4bd8e3f8c778dc0b2f38d9c69668d1b84e68b7531c58b4da15b8a81f0ca8a4b8889894ebb5e894068d88934bc8a88e50a9488a4fc21884d6a8e8730fd4686c3fb2e8690a30e8680741c8663aea9865cbae885f1f72684a4c2e68475b5338436e17f84129c40840799a683fe99eb83c0be09831d6c2c831ab88982e2ff4782cfc521821853fe
  | 7, 8 => 0xc4e635f6c4070a2dc37daca1c2dde247c29bf8ddc1ad95ecc19d30e4c13e825dbf8705ebbf83682fbebb555abe18d688bd48b01bbd41015bbd2fc437bccba248bcbbca35bcb2b5b1bc62e41ebc268fe5bb75fc4ebaf70c47bab9a1bdb99d8907b9910a03b91d4ce9b859f422b796ed02b79618a9b6d8a086b69c07f9b64eb09ab5fc60c4b5f36f3fb5446adbb5406affb31e2f22b1522b5ab081bca1b06379a0adbaafa4ad58a5d0ab8bcb77aa6b2cfcaa2ce68ba9c3b08aa994b72fa94c64a9a8e5934da8a73885a72ca08ba61c678aa5141b3ba44634c2a411e8baa35b4fb5a31eb728a3147353a29e4ecda13c87fb9f1c706f9edbc97b9ec0d7899e4b2ef1
  | 7, 9 => 0xec53a50debefca4bebb11d4aeb7dc701e9cf7cc3e8f0997ae69515eae56d3923e4f80626e4f751b8e4842702e4299312e403206de3af474de2f6af66e2e44efbe28853e8e274b8a0e15042f8e1489438e1151f08e041dc16dfc3ff5bdfafb75ddf7909f5de356204ddf8e307dc891c35dbc7af05da410646d9ad9916d9924a17d9288e6bd872797ad86386c7d7783301d67f4dd9d53d3f77d4894f7ed3ab90abd31fe84fd282ff82d21f33e1d17bf5cfd0ad1508cfec020dcf7566e4cef767cfcd786ec8cd28ef85cc6e82bfcc452051cbedcfe9cb2d3d5ccb08702acad172fbca14a60bca129b92c7b65101c7b46166c731841fc69a9d6ec67fb4d4c5158df3
  | 7, 10 => 0xfdfab3d3fdf6b6b9fd904c97fce8b50efbec0709fb55f38cfad9fd75f9050bc6f87e7dd9f72a0023f7271afbf6535463f5e77c9bf568a6a7f341502cf2d35972f1a91aa5f0f8df95f0e86fe3f052953bf0479b38ef75fb71ed2ae9e7ed215bcfecca4defeca5df3cec6b46de
  | 8, 0 => 0x2310763b23038dd422d85c9a22c735132219ec0a20df43cc2064873a20292edb1fb72b911f3d31db1e1aa3ae1e08e1531d89743f1d81c57f1d29fe0a1ca0b1831c53b96d1c1ffead1bea35011b8548e61b78d4bc19b1d448198eb5651881f686175a929b170db67f16e8db1816b50ee91581f8c81561a43a141a4f1c1415063f1317dd2b12baa67712b8884a12324797119811441187183a10d1aa9610c280c50f8898390f79f41c0f3d84400e8414b20e7e15130e7dd0190e783ebe0d9cbe430d61f2fb0cabde0a0c2cfbb60c22507d0c167f100b989d440acf09dd0ab8b26f0a172c4909ee1b6f06291d8305c61dd605169eb0023f103c0086a50c00273479
  | 8, 1 => 0x4e2ce2974e1717654dc27b5b4cfd734b4c4c79c44c1e35cd4bc969994bb8974e4b0c2c394b02825d48b0ac9d484e6acf43555fb0434ac0324309ffd8430588364214fad141a83906413f306a40455b7a3cedcf813c9d75a23c21f90f3afd7b253a8b1a653a476634396f572d387c221636c744ae366fa272359f67e7358e7c1335743559354bc4fd3481847a34064f6c339be83032ba82ac3264f19431381b073129ad3f3122199e2fc976f62f7655c82f1362052e9c408b2d90db782d6df75a2cb7e2692ba0a43a2b81626d2a73350a2a6cf07129c478db2964176b291abe5628a4a83e2774c460275958f226beaf6f26bb2fef261c309d26093241246554a6
  | 8, 2 => 0x7ab597257aa157477a2bf43679e15a287952d27478925775785a178977d135d07770373f76f0de3375217693745a681c72b283397260e48f70cdf07470946692705b5d9f6f6c29a26ebe77696d483b2f6c4b6e046c3d1b7e6be1bd3a6bcb63fb6a7ff6686a4f220869c0add467f1c0d3679d352a6733942567044c4c66fb4c916554bad1651506a46478994863669d956347643b61aa336860b58bf55f5d13a95debf6475d7bf2db5d1e66bc5cde0cce5ba915895b2acd595af03eb05aa8a6b95916f56258905d13584e132a56abec62568ff7f15640306854b47b98531505d8530ec13f523dc21151099cc6505beeb34f490be64f0fba7a4ed5e3f64e9d1903
  | 8, 3 => 0xaa38618da98e4816a8e78fc4a8d69abba5103ec2a4a02823a494c22fa3f2435da309310ca1662bafa02ef21b9e58572e9c97dd089b34b1219b1dd7b09aec1f2b996c23f4992721c2981b7e929710a45896a4b77d94b8834e9409b1f0939a9e6191b98d129117715e9074f28c8fa4cc1f8f9d1d5f8f6e24048ebf00228e4941358d5eaaf98ce77a638bbc73f08b8fda438b7e195e8a8bfac78a81f0ca8a7994f88934bc8a89211e6a88f823fd88ede028877c8a9f867726a185f48e9f85e99b5485520fcd84e9742a8492c7cd83f048fb833df90382ddd8a581b633a5806266ad7f5f0e0b7f4590c97e8559377dfd47397d7d57bc7d356db97cea112d7bf0d333
  | 8, 4 => 0xffcceadcfe9afd92fe091979fbefb591fb7259a6f9b99d75f80fe67ff5210d0ef17a65ebeef3064deabec0cde73f702ce48a3599e3d420a8e1b1f408e1283faadede789bddfd151add4db3aadaf5c757d96359b3d7661623d58ce416d355d4ffd3152e0bd1d3f658d1786b89d0dd3a20cecb96dfcdd2d617cdb20f90cbfcbae9cb46a5f8c8d8951dc7554d2ec5e58a67c59d6c30c5690328c52f7576c31b6fd9bf8705ebbf01fb40be4be64fbe107ab6bde1cfb5bd3f82f8bc545819ba45dd7fb81d78f4b59a84ddb55b444cb52557b8b4e46fecb4d0d4a4b37ef559b0e1dcffb080f6ebae064aa9ace974c5aabfa2cbaa8df529aa87c3f1
  | 9, 0 => 0xf33b5fd0f2854adfc3d681ef9b34b1218a7994f87f4590c97cea112d76f0de33764e5f61705b5d9f61ca40085fbac6fd5cde0cce51bb2a0f5059633d4aee737942b779a33e277fff34064f6c1b78d4bc1561a43a0e7e151305169eb0
  | 10, 0 => 0x42b779a3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x57575757000000000000000000000000000000000000000000000000000000005555555500000000000000000000000000000000000000000000000000000000333333330000000000000000000000000000000000000000000000000000000022222222000000000000000000000000000000000000000000000000000000000f5f0f5f000000000000000000000000000000000000000000000000000000000f0f0fff000000000000000000000000000000000000000000000000000000000f0f0f0f0000000000000000000000000000000000000000000000000000000000ff00ff
  | 0, 1 => 0xf0f00000f0f000000000000000000000000000000000000000000000000000000ff000000ff00000000000000000000000000000000000000000000000000000000ffffffff00000000000000000000000000000000000000000000000000000000fafafafa00000000000000000000000000000000000000000000000000000000eeeeeeee00000000000000000000000000000000000000000000000000000000cfcfcfcf0000000000000000000000000000000000000000000000000000000077777777000000000000000000000000000000000000000000000000000000005f5f5f5f
  | 0, 2 => 0x550055005500550000000000000000000000000000000000000000000000000033003300330033000000000000000000000000000000000000000000000000000f000f000f000f0000000000000000000000000000000000000000000000000000ffff0000ffff0000000000000000000000000000000000000000000000000000fafa0000fafa0000000000000000000000000000000000000000000000000000eeee0000eeee00000000000000000000000000000000000000000000000000007777000077770000000000000000000000000000000000000000000000000000333300003333
  | 0, 3 => 0x7070707070707070000000000000000000000000000000000000000000000000505050505050505000000000000000000000000000000000000000000000000030303030303030300000000000000000000000000000000000000000000000000ff00ff00ff00ff00000000000000000000000000000000000000000000000000fa00fa00fa00fa00000000000000000000000000000000000000000000000000f300f300f300f300000000000000000000000000000000000000000000000000ee00ee00ee00ee0000000000000000000000000000000000000000000000000077007700770077
  | 0, 4 => 0x303030303030303000000000000000000000000000000000000000000000000022222222222222220000000000000000000000000000000000000000000000001f1f1f1f1f1f1f1f00000000000000000000000000000000000000000000000011111111111111110000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000000e0e0e0e0e0e0e0e0000000000000000000000000000000000000000000000000c0c0c0c0c0c0c0c0000000000000000000000000000000000000000000000000a0a0a0a0a0a0a0a
  | 0, 5 => 0x3c3c3c3c3c3c3c3c0000000000000000000000000000000000000000000000003737373737373737000000000000000000000000000000000000000000000000333333333333333300000000000000000000000000000000000000000000000033333333333300000000000000000000000000000000000000000000000000003333333330303030000000000000000000000000000000000000000000000000333333003333330000000000000000000000000000000000000000000000000033333030333330300000000000000000000000000000000000000000000000003232323232323232
  | 0, 6 => 0x5555777755557777000000000000000000000000000000000000000000000000555555ff555555ff0000000000000000000000000000000000000000000000005555557755555577000000000000000000000000000000000000000000000000555555555f5f5f5f0000000000000000000000000000000000000000000000005555555555555555000000000000000000000000000000000000000000000000505050505050505000000000000000000000000000000000000000000000000044444444444444440000000000000000000000000000000000000000000000003f3f3f3f3f3f3f3f
  | 0, 7 => 0x888888888888888800000000000000000000000000000000000000000000000080808080808080800000000000000000000000000000000000000000000000007777777777777777000000000000000000000000000000000000000000000000707070707070707000000000000000000000000000000000000000000000000066666666666666660000000000000000000000000000000000000000000000005f5f5f5f5f5f5f5f0000000000000000000000000000000000000000000000005a5a5a5a5a5a5a5a000000000000000000000000000000000000000000000000555f555f555f555f
  | 0, 8 => 0xaaaa8080aaaa8080000000000000000000000000000000000000000000000000aaa0aaa0aaa0aaa0000000000000000000000000000000000000000000000000aa88aa88aa88aa88000000000000000000000000000000000000000000000000a8a8a8a8a8a8a8a8000000000000000000000000000000000000000000000000a5a5a5a5a5a5a5a5000000000000000000000000000000000000000000000000a0a0a0a0a0a0a0a000000000000000000000000000000000000000000000000099999999999999990000000000000000000000000000000000000000000000008f8f8f8f8f8f8f8f
  | 0, 9 => 0xaaaaaaaaa0a0a0a0000000000000000000000000000000000000000000000000aaaaaaaa88888888000000000000000000000000000000000000000000000000aaaaaaa0aaaaaaa0000000000000000000000000000000000000000000000000aaaaaa88aaaaaa88000000000000000000000000000000000000000000000000aaaaaa00aaaaaa00000000000000000000000000000000000000000000000000aaaaa8a8aaaaa8a8000000000000000000000000000000000000000000000000aaaaa0a0aaaaa0a0000000000000000000000000000000000000000000000000aaaa8888aaaa8888
  | 0, 10 => 0xafafafafafafafaf000000000000000000000000000000000000000000000000aaaaaaaaaaaaaaaa000000000000000000000000000000000000000000000000aaaaaaaaaaaaaa00000000000000000000000000000000000000000000000000aaaaaaaaaaaa8888000000000000000000000000000000000000000000000000aaaaaaaaaaaa0000000000000000000000000000000000000000000000000000aaaaaaaaaaa0aaa0000000000000000000000000000000000000000000000000aaaaaaaaaa00aa00000000000000000000000000000000000000000000000000aaaaaaaaa8a8a8a8
  | 0, 11 => 0xccccc8c8ccccc8c8000000000000000000000000000000000000000000000000cccc8888cccc8888000000000000000000000000000000000000000000000000ccc0ccc0ccc0ccc0000000000000000000000000000000000000000000000000cc88cc88cc88cc88000000000000000000000000000000000000000000000000c8c8c8c8c8c8c8c8000000000000000000000000000000000000000000000000c3c3c3c3c3c3c3c3000000000000000000000000000000000000000000000000c0c0c0c0c0c0c0c0000000000000000000000000000000000000000000000000bbbbbbbbbbbbbbbb
  | 0, 12 => 0xcccccccccfcfcfcf000000000000000000000000000000000000000000000000cccccccccccccccc000000000000000000000000000000000000000000000000cccccccccccc0000000000000000000000000000000000000000000000000000cccccccccc00cc00000000000000000000000000000000000000000000000000ccccccccc8c8c8c8000000000000000000000000000000000000000000000000ccccccccc0c0c0c0000000000000000000000000000000000000000000000000cccccccc88888888000000000000000000000000000000000000000000000000cccccc00cccccc00
  | 0, 13 => 0xecececececececec000000000000000000000000000000000000000000000000eaeaeaeaeaeaeaea000000000000000000000000000000000000000000000000e0e0e0e0e0e0e0e0000000000000000000000000000000000000000000000000dddddddddddddddd000000000000000000000000000000000000000000000000cfcfcfcfcfcfcfcf000000000000000000000000000000000000000000000000cdcdcdcdcdcdcdcd000000000000000000000000000000000000000000000000cccccfcfcccccfcf000000000000000000000000000000000000000000000000ccccccffccccccff
  | 0, 14 => 0xeeeeeeeee0e0e0e0000000000000000000000000000000000000000000000000eeeeeeee00000000000000000000000000000000000000000000000000000000eeeeeecceeeeeecc000000000000000000000000000000000000000000000000eeeeee00eeeeee00000000000000000000000000000000000000000000000000eeee0000eeee0000000000000000000000000000000000000000000000000000eeeceeeceeeceeec000000000000000000000000000000000000000000000000eee0eee0eee0eee0000000000000000000000000000000000000000000000000ee00ee00ee00ee00
  | 0, 15 => 0xf0f0c0c0f0f0c0c0000000000000000000000000000000000000000000000000f0f0a0a0f0f0a0a0000000000000000000000000000000000000000000000000f0e0f0e0f0e0f0e0000000000000000000000000000000000000000000000000f0c0f0c0f0c0f0c0000000000000000000000000000000000000000000000000f0a0f0a0f0a0f0a0000000000000000000000000000000000000000000000000eeeeeeeeeeeeeeee000000000000000000000000000000000000000000000000eeeeeeeeeeeecccc000000000000000000000000000000000000000000000000eeeeeeeeecececec
  | 1, 0 => 0xf0f0f0f0f0f0f000000000000000000000000000000000000000000000000000f0f0f0f0f0f00000000000000000000000000000000000000000000000000000f0f0f0f0f000f000000000000000000000000000000000000000000000000000f0f0f0f0e0e0e0e0000000000000000000000000000000000000000000000000f0f0f0f0c0c0c0c0000000000000000000000000000000000000000000000000f0f0f0f0a0a0a0a0000000000000000000000000000000000000000000000000f0f0f0c0f0f0f0c0000000000000000000000000000000000000000000000000f0f0f000f0f0f000
  | 1, 1 => 0xfafa0000fafa0000000000000000000000000000000000000000000000000000fac8fac8fac8fac8000000000000000000000000000000000000000000000000fa00fa00fa00fa00000000000000000000000000000000000000000000000000f8f8f8f8f8f8f8f8000000000000000000000000000000000000000000000000f5f5f5f5f5f5f5f5000000000000000000000000000000000000000000000000f3f3f3f3f3f3f3f3000000000000000000000000000000000000000000000000f1f1f1f1f1f1f1f1000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0
  | 1, 2 => 0xff00ff00ff00ff00000000000000000000000000000000000000000000000000fefefefefefefefe000000000000000000000000000000000000000000000000fdfdfdfdfdfdfdfd000000000000000000000000000000000000000000000000fcfcfcfcfcfcfcfc000000000000000000000000000000000000000000000000fafafafafafafafa000000000000000000000000000000000000000000000000fafafafaf8f8f8f8000000000000000000000000000000000000000000000000fafafafa00000000000000000000000000000000000000000000000000000000fafafa00fafafa00
  | 1, 3 => 0xff80ff80ff80ff80000000000000000000000000000000000000000000000000ff55ff55ff55ff55000000000000000000000000000000000000000000000000ff50ff50ff50ff50000000000000000000000000000000000000000000000000ff44ff44ff44ff44000000000000000000000000000000000000000000000000ff30ff30ff30ff30000000000000000000000000000000000000000000000000ff11ff11ff11ff11000000000000000000000000000000000000000000000000ff0fff0fff0fff0f000000000000000000000000000000000000000000000000ff0cff0cff0cff0c
  | 1, 4 => 0xffccff88ffccff88000000000000000000000000000000000000000000000000ffccf0c0ffccf0c0000000000000000000000000000000000000000000000000ffc0ffc0ffc0ffc0000000000000000000000000000000000000000000000000ffaaffaaffaaffaa000000000000000000000000000000000000000000000000ffaaffaaf0a0f0a0000000000000000000000000000000000000000000000000ffaacc88ffaacc88000000000000000000000000000000000000000000000000ffa0ffa0ffa0ffa0000000000000000000000000000000000000000000000000ff88ff88ff88ff88
  | 1, 5 => 0xfffafffafffafffa000000000000000000000000000000000000000000000000fff0fff0fff0fff0000000000000000000000000000000000000000000000000fff0aaa0fff0aaa0000000000000000000000000000000000000000000000000ffeeffeeffeeffee000000000000000000000000000000000000000000000000ffddffddffddffdd000000000000000000000000000000000000000000000000ffccffccffccffcc000000000000000000000000000000000000000000000000ffccffccf0c0f0c0000000000000000000000000000000000000000000000000ffccffccaa88aa88
  | 1, 6 => 0xffffa0a0ffffa0a0000000000000000000000000000000000000000000000000ffff8888ffff8888000000000000000000000000000000000000000000000000ffff5555ffff5555000000000000000000000000000000000000000000000000ffff3333ffff3333000000000000000000000000000000000000000000000000ffff0f0fffff0f0f000000000000000000000000000000000000000000000000ffff0505ffff0505000000000000000000000000000000000000000000000000ffff0000ffff0000000000000000000000000000000000000000000000000000fffcfffcfffcfffc
  | 1, 7 => 0xffffe0e0ffffe0e0000000000000000000000000000000000000000000000000ffffccccffffcccc000000000000000000000000000000000000000000000000ffffccccffffcc00000000000000000000000000000000000000000000000000ffffccccffff8888000000000000000000000000000000000000000000000000ffffccccf0f0c0c0000000000000000000000000000000000000000000000000ffffc8c8ffffc8c8000000000000000000000000000000000000000000000000ffffc0c0ffffc0c0000000000000000000000000000000000000000000000000ffffaaaaffffaaaa
  | 1, 8 => 0xffffff55ffffff55000000000000000000000000000000000000000000000000ffffff00ffffff00000000000000000000000000000000000000000000000000ffffff00f0f0f000000000000000000000000000000000000000000000000000ffffff00aaaaaa00000000000000000000000000000000000000000000000000fffffcfcfffffcfc000000000000000000000000000000000000000000000000fffff5f5fffff5f5000000000000000000000000000000000000000000000000fffff0f0fffff0f0000000000000000000000000000000000000000000000000fffff0f0aaaaa0a0
  | 1, 9 => 0xffffffff11111111000000000000000000000000000000000000000000000000ffffffff0f0f0f0f000000000000000000000000000000000000000000000000ffffffff0c0c0c0c000000000000000000000000000000000000000000000000ffffffff05050505000000000000000000000000000000000000000000000000ffffffff00000000000000000000000000000000000000000000000000000000fffffff0fffffff0000000000000000000000000000000000000000000000000ffffffccffffffcc000000000000000000000000000000000000000000000000ffffffaaffffffaa
  | 1, 10 => 0xffffffffaaa0aaa0000000000000000000000000000000000000000000000000ffffffffa8a8a8a8000000000000000000000000000000000000000000000000ffffffffa0a0a0a0000000000000000000000000000000000000000000000000ffffffff88888888000000000000000000000000000000000000000000000000ffffffff80808080000000000000000000000000000000000000000000000000ffffffff55555555000000000000000000000000000000000000000000000000ffffffff33333333000000000000000000000000000000000000000000000000ffffffff30303030
  | 1, 11 => 0xffffffffdddddddd000000000000000000000000000000000000000000000000ffffffffcccccccc000000000000000000000000000000000000000000000000ffffffffcccccc00000000000000000000000000000000000000000000000000ffffffffcc88cc88000000000000000000000000000000000000000000000000ffffffffc0c0c0c0000000000000000000000000000000000000000000000000ffffffffaaaaaaaa000000000000000000000000000000000000000000000000ffffffffaaaaaa00000000000000000000000000000000000000000000000000ffffffffaaaa8888
  | 1, 12 => 0xfffffffff5f5f5f5000000000000000000000000000000000000000000000000fffffffff0f0f0f0000000000000000000000000000000000000000000000000fffffffff0f0f000000000000000000000000000000000000000000000000000fffffffff0c0f0c0000000000000000000000000000000000000000000000000fffffffff0a0f0a0000000000000000000000000000000000000000000000000ffffffffeeeeeeee000000000000000000000000000000000000000000000000ffffffffecececec000000000000000000000000000000000000000000000000ffffffffe0e0e0e0
  | 1, 13 => 0xfffffffffff0fff0000000000000000000000000000000000000000000000000ffffffffffa0ffa0000000000000000000000000000000000000000000000000ffffffffff88ff88000000000000000000000000000000000000000000000000ffffffffff55ff55000000000000000000000000000000000000000000000000ffffffffff00ff00000000000000000000000000000000000000000000000000fffffffffcfcfcfc000000000000000000000000000000000000000000000000fffffffffafafafa000000000000000000000000000000000000000000000000fffffffff8f8f8f8
  | 1, 14 => 0xffffffffffffff00000000000000000000000000000000000000000000000000fffffffffffff0f0000000000000000000000000000000000000000000000000ffffffffffffcccc000000000000000000000000000000000000000000000000ffffffffffffaaaa000000000000000000000000000000000000000000000000ffffffffffff0000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xb1975b5608500cbb68c7a1c500b1976e66085cbc6beaa6d56600cb97562f14500cb97884114500b19766390d500cbb166391c500cbb1975a33500cbb1883b1c5ebc5b1665956600cbb18c7a18500d5975b5614500d5976e66145
  | 6, 0, 0 => 0xcbb897664823600d49788562d14600b18866561c0c600deb18865561c60097936642140d600da9788664f146009788332d140d600cb887a3f1c14600b197332d230d600cbb17a3f231c600cbb1887a3d1c600cb97886e3f14600d4978c665614600b1975956440d600cbb688562d1c600cb97886633116
  | 6, 0, 1 => 0xcb706d665614600b1978866560a600cbb18866331b600cb9766562514600cb8c66561c14600cb887a733f1c600cb9788562d13600cb976e664214600d5b19366421c600f0c597886656600cb9459561c14600cbb18c7a3f1c600cf9788665614600b6976656230d600cbb897886637600cb9788562d126
  | 6, 0, 2 => 0xcb975b564214600cbb697663323600b1976656230b60097887a3f140d600b1977a3f230d600cbb18c562d1c600dab188664e1c600d5b19366561c600cbb166562319600cbc6a6886656600cbb1887a3f1960000cbb1976643500d4b18866331c600b19793422d0d600dab197884f2d600cb885b561c146
  | 6, 0, 3 => 0xcbb18856281c600978c6656140d600b1a08866330d600d5b16656231c600b1976656230a600ebc6886656536cbbeb1aa976d5670097945956140d600e39788665614600cb976d66561260097887a763f14600cbb16656401c60097886656140b600cbb688665618600cb9794563014600cbb1986633236
  | 6, 0, 4 => 0xb19766562309600cbb1887a3f18600cb6d66561c14600cb976d563f14600cbb18858261c600b19788562d0b600cbb6b1978c7a600cbb17a6d3f1c600b1978866330860097885b56140d600d6b197886633600b19782665601600cb562d231c14600cb9788562e14600d59766595614600d58866561c146
  | 6, 0, 5 => 0xcbb18c665618600d39788665614600dc9788665614600b1976656400d600cb9794593314600cbb19788753f600cbb18b66321c600cb9766563c14600cbb1886c311c600cbb18466561c600978866561409600d5b188562d1c600b19788562d0a60000cbb6978c7a500d0b18866561c600cbb1665623186
  | 6, 0, 6 => 0x976d6656140d600f0ebc688663360000cbb1978841500cbb193663a1c600ebb1a9886656600cbb197934f2d600cbb188562d1860097562d23140d600cbb197332d23600b1978856280d600f0eb8866564b600cb97885b3314600cbb16d562d1c600cb978c663314600d4b68866561c600b197886656036
  | 6, 0, 7 => 0xcbb1975a56500b1976d562d0d600d5b19793664f600b19788665608600cb9759564414600d48866561c14600cb976f5956146008866331c140d600d4b16656231c600b19793664208600b16633231c0d600de978861561460097766d665614600cbb188562d1a600d4b1887a3f1c60000cbb197562f5
  | 6, 0, 8 => 0xcb978a562714600d5b19788332d600b68866561c0d600e697856656146ebe6c6b1665956700887670665614600cbb197886635600cb976d663314600b19788665602600b19793663a0d600b19793665608600cbb197664c23600cb97332d2314600cbb1883f241c600d0b188562d1c600d597886633146
  | 6, 0, 9 => 0xdab197664e23600f0ebc6665623600cb9788663312600b19788562d0c600b1976656250d600d4b188665618600d4b19766332360000cbb197883b500cbb68866331c600b19788562d08600978866561408600d69788665614600b19766562308600cbb197884c2d600cb9793422d14600e697826656146
  | 6, 0, 10 => 0xb1979459330d6f0ebc688665956700cb6633231c1460088562d1c140d60000cbb1976639500b19788665607600cbb19759331d600f0ebc688562d600cbb197562823600dab197886634600cbb197562d226006656231c140d6cbc5b197665956700cdb197663323600cbb197926633600d0b19788332d6
  | 6, 0, 11 => 0xcbb19766331f600cbb197936634600b1976f59560d600b1976659560860000d5b1975b56500cbb68c66561c600b19788663309600cbb66656231c600dab197886650600cbb6887a3f1c600cb9366421c14600cb88332d1c1460000d5b1976e66500b1978c66330d6
  | 7, 0, 0 => 0xb197886c66330d700cbb1888666561c700cb978866332d1470000cbb1978c59566e6cbc6b197665956800cbb19788562726700cbc6beaa886656700e2cbb18866561c700cbb19766332d23700cbc1b18866331c70000e6b197866656600ebcbb1aa886633700f3cbb197886633700cbcab19788562d70097887a6656140d700cbb1978856452d7
  | 7, 0, 1 => 0xcbb19788796656700cbb1887f66561c70000cb6656231c14600ebdeb1aa88665670000cbb188665619600dacbb188562d1c70097887a76665614700f0cbb16656231c700dfcbb197886633700cbb1978856462d700b197886659330d700cbc6b188665651700cbb6b197886633700f0cbb597886633700d5b1a197886656700cbc6b1aa6656237
  | 7, 0, 2 => 0xcbb1978866330e700cbb68866563f1c700d2cbb19788332d700cbb1978866563770000cbb1975b5642600eadab197886656700eacbb197886633700cbb19788665652700e6cbb197562d23700cbb19766564823700b197888066560d700cbc6b197887a3f700cbb1978b88332d70000b197887a3f0d600e6d5b197886656700d1cbb188562d1c7
  | 7, 0, 3 => 0xf0b1978866564e700cbb1886658561c700cbb19788562d2c70000cbb69788663360000b1978866560b600cbb19788332d23700decbb188562d1c700e6cb9788562d14700cbb1b09788562d700cbc4b19788665670000cbb197936644600ebdbb19788665670000cbbc97886656600cbb5b19788332d70000cbb197945630600cbbeb188562d1c7
  | 7, 0, 4 => 0xcbb1ad97886656700d4cbb197665623700cbb1886656311c700cbb1a097665623700e6cbb1976d6656700cbb17a6d66561c700cbc6b19794595670000b1979459560d600cbb1a097887a3f70000e3b197886656600cbb1886656261c700ebe6b197665956700b197887a562d0d70000b197887a763f60000cbc197806656600cbc6b1ae88562d7
  | 7, 0, 5 => 0xd4cb978866561470000d5b19766595660000d5b18866561c600cbb19788562d0f700cbb1976659564f700cbb18866564f1c700cbc6b1aa88562d700cbb1886c66561c700cbb19788663315700e1d5b197886656700cbc6b1978c665670000b1978c66560d600b197886642330d700d4978866563f14700f0cb9788665648700cbb197665653237
  | 7, 0, 6 => 0xcb97887a6633147cbc6b19788665644800cbc6b197885b5670000cb88562d1c14600b197886656440d70000b197885b560d600cbb19788665654700f0cbb188562d1c700cbb4b188562d1c700cbb1888366561c700cbc1b1a0886656700dbcbb197886633700beb1976656230d70000cbb1562d231c600b197886f66560d70000cbb19788562e6
  | 7, 0, 7 => 0xcb886656331c14700d4c1b19788665670000cbb16d66561c600cb97887a663f1470000cbb1976d563f60000978876736656600c1b1978866330d700cbb19788696656700cbb1978866564d700cbb1665633231c700cbb1a0978c6656700d0cbb19788562d700e6dab18866561c700e6cbb197665933700e6cbb18866331c700b197886656270d7
  | 7, 0, 8 => 0x97665623140d600cbb1976633232170000b19788665609600cb8866563f1c147cbb197887f665648800cbb1a09788562d70000cbb197663323600cbc5b197886656700cb9e9788663314700ebcb9788663314700cbb166563f231c700cbb19e97663323700cbb19788756656700ebcbb197663323700cbb18866563d1c700cbb197665956017
  | 7, 0, 9 => 0xbeb19788562d0d700ebde978866561470000cbb19766563c600d2cbb197665623700cbb19766562316700cbc6c197886633700b1a4976656230d700cb979466595614700cb948866561c14700ebdeb197665623700cb97886656321470000cbb19793664f600cbb188562d271c700b197887f66560d70000cbb188665618600cbb1978856532d7
  | 7, 0, 10 => 0xdacb9788663314700b197886656260d70000cbb1978c6633600f0cbc69766562370000cbb19766561f600cb978866561405700f0e6b18866561c700cbbfb1976d665670000d3b19788665660000dcb197886656600cbb18c66563f1c700d2cb9788665614700cbb1976656230570000cbb197945933600a497886656140d700cbb5b1976656237
  | 7, 0, 11 => 0xdecbb197663323700ebcbb19788332d700f0ebb197665623700cb886659561c14700cb978859563f14700cbbeb197663323700f2cbb197886633700cbb1a597665623700cbb197886f663370000e6cbb1975b5660000cbb197876656600cb9788665b5614700cbb1936656421c700cbb1665956231c70000d4b1a0886656600cbb18856332d1c7
  | 7, 0, 12 => 0xdfcbb197886656700cbb1a397886656700cbc6b197562d23700deda9788665614700decb978866331470000b197562d230d600cbb188563f2d1c700d5c6b197886656700cb97886b665614700b197886c66560d700cbc9b197665623700e6cbb1a0886656700cbb19788664433700ebcbb19793664270000cbb197885b33600dedab1976656237
  | 7, 0, 13 => 0xcbb3b16656231c700cbc6b188665645700edd4b197886656700b1a49788562d0d700cbb1978b88562d700cbc7b197886633700ebcbb697886656700ebdeb19788562d700cbb18858562d1c700009788562d140d600cbb1978866562b70000cbb197936642600cbb1a59794595670000cbb19788332d600cbb19488562d1c700e8d4b1978866567
  | 7, 0, 14 => 0x9788665633140d70000b1976d66560d60000cbb697886656600cbb19788663300700b197887b66560d700ae97886656140d700cb978866645614700e6cbb1977f6656700cbb5b19788562d700b197665633230d700cbb19766564923700d2cbb19788562d700e6d4b197886656700cbb19788665629700cbb188562d261c700cb9788666156147
  | 7, 0, 15 => 0xcb886656421c14700cbb19795886633700cbb1a088665645700cbb18859562d1c70000cb97938f6642600b19766563f230d700cb978866563a14700f0cbc69788562d70000cb976633231460000cbb1a4886645600cbc6b188665646700cbb1665642231c700cb9788665d5614700cbc6b1976d6656700b1938866561c0d70000cbb1988866566
  | 7, 1, 0 => 0xcbb19794886633700aa97886656140d700f0ebb19788562d700b19788562d270d700cba4978866331470000deb19788615660000b197766d6656600cbbeb197936642700deb19788665600700cbbeb19788332d700978866563f140d70000cbb18866561b600cbb1a59788562d700ebb1978866564f700e5c6b197886656700cb9766595642147
  | 7, 1, 1 => 0xebe6b197886633700cb978866564e14700cbb19788562d2070000cbb1976f595660000deb19788645660000b18866331c0d600cbb1886e66561c700cbb19793562d23700cecbb18866561c7009794886656140d700cbc9b19788562d700decbb197936642700cbb1886656241c700cbb8b16656231c700cbb19766564e23700decbb19788332d7
  | 7, 1, 2 => 0xb1978856332d0d700e4cbb197886656700cb976b66562314700b1ae9788562d0d700cbb1a29788665670000cbb1977d6656600cb9766562d2314700cbb1887a563f1c700cb978866563014700cbb19788665647700cb97886657561470000cbb197595644600cb979388562d14700ebcbb1aa665623700e3cbb19788665670000d4b18866561c6
  | 7, 1, 3 => 0xb18866562d1c0d70000cbb19788664c60000cb979366421460000cb9788332d14600cbb18856422d1c700cbc6c1aa8866567009788665956140d70000cbb197332d23600ebcbb197887a3f700cbb1978866331070000d5b197886633600d5cbb197665956700d5cbb18866561c700cbb19788664f33700b197665956230d700b1886656231c0d7
  | 7, 1, 4 => 0xcbb8b188562d1c70000cbb19866562360000cbb697665623600f0e6c697886656700cbb18a88562d1c700cbb19788665634700b1979488562d0d700cbb19788716656700cbb1ae97663323700cbb197887a6645700d9cbb197886656700d8cbb197886656700cbb1976656230e70000cbb697887a3f60000cbb197887a3f600cbb7b1978866337
  | 7, 1, 5 => 0xebcbb1aa88562d700cbb197663f3323700ebcbb1978c6656700cbc2b197886633700cbb1a897886656700b19788562d260d700b3b1976656230d7f0cbc69788665956800cbb1938866331c700cb9788562d2314700dab19788665601700cbb1978866330170000cbb1976d6633600cbb19788665638700efcbb19788562d700ebcbb1979459567
  | 7, 1, 6 => 0xb1a08866560d600cbb19788332d27700cecbb16656231c70000cbb197935b42600cb9788663f3314700cbb19794663323700b197665642230d700cbb197886651337f0ebb19788665956800cbb1886662561c700b1978866564b0d700cbb9b197886633700cbb1978866562a700cbb18866563f1870000cbb197945956600cbc1b188562d1c7
  | 7, 1, 7 => 0xcbb1888266561c700d1cb9788665614700cb97886d665614700dbcbb197665623700e0cbb197886656700cbb1886633321c700cbbeb197887a3f700cbb197562d2320700cb9794886633147009788665642140d70000cbb6978c6656600ebcbb197885b5670000cbb1978c665660000e6b19782665660000cbb1978a5627600cbaa97886633147
  | 7, 1, 8 => 0xcbb1976c663323700c6b1978866330d700d2cbb18866331c700cbb19788562d2970000b19788665608600eacbb19788562d700e6dab19788664f700cbb18b8866331c70000d6b19788665660000cbb197885b56600ebcbb18866564b700dbcb9788665614700cb977a66562314700cb976657562314700cbb19788562d2b70000cbb19793422d6
  | 7, 1, 9 => 0xcbb1978e88665670000cbb197887a3d60000cbb1aa886456600cb97886c663314700cbbeb19794595670000cbb69788562d600d5b1886656421c700cbb1886633231c700e6cb9766595614700e6cb8866561c14700d4c6b197886656700cbb1ae9788332d700eed5b19788665670000cb8f8d886656600cb978866333114700cbb19788562d0e7
  | 7, 1, 10 => 0xcbbeb197885b56700cbb1979488332d700b1978856422d0d700f0b19788665651700d4b1a09788665670000cb97887a3f14600cbc6b19e88663370000cb978f885b56600f4cbb197886633700ebcbc6b188663370000cbb197886a56600cbbeb1978c665670000cbb1977a3f23600ddc6b197886656700cb978866593314700cbb1aaa46656237
  | 7, 1, 11 => 0xcbbbb197886656700cb978866563e14700cbb19788664b33700cbb1886656481c700cbb1978867665670000cb9794595614600cbb1978866560470000cbb1978c7a3f600cbb6aa97886656700cb97887a562d14700cbb19c97886633700f4deb197886656700ebdec6b1886656700cbb1977a562d2370000b1978866560c600ebe6b1aa8866567
  | 7, 1, 12 => 0xcbb1978866564a70000cbb1975b562360000b19793916642600ebcbb197562d23700ebd5b197886656700f2cbb19766562370000cb978c66561460000cbb19f886656600cb978866561406700cb97886642331470000cb97887a733f60000cbb197885f5660000d5b197936642600b197886656450d700cbc0b197886656700dacb97665623147
  | 7, 1, 13 => 0xcbb19d9788663370000cbb197665622600b1978b8866330d700cbb1886656531c70000d4b19788663360000cbb197562d23600cb978866562714700cb97886656441470000cb97885b561460000d5b197886656600decb9766562314700cbb7b197936642700b197886656460d700cbb19788665650700cb97886f665614700cbb19788664b3f7
  | 7, 1, 14 => 0xcbb1978866563670000dab19788664e60000cbb1976d665660000f0ebc6886656600cbc3b19788663370000d5b197936656600dacbb197562d23700cbb19788562d2a700cbb1976656230070000ccb197886656600d5cbb197886633700b197886633230d70000cbb1978c5b56600b5b1978866330d700ebcbb1976d6656700cbb1ae97887a3f7
  | 7, 1, 15 => 0xebd2b19788663370000cbb197665640600cbb19766562623700cb9788665c561470000cbb1aa886056600decbb197562d23700cbb19788786656700ded5b197886656700cbbeb197562d23700f2cbb19788562d70000e5b197886656600b1978866332d0d7000097918f886656600d5beb19788665670000cbb1978c562d600cbb1978842332d7
  | 7, 2, 0 => 0xcbb7b197665623700d6cbb19788665670000cbb19788635660000cbb197885628600cbb19788562d00700cbb19788664633700cbb19b9788562d70000d5b197665623600cbb19766564f23700cbb1976c665623700decbb1976d6656700cbbeb1976d6656700cbcab197886633700cbb19788664533700008866561c140d600e7cbb1978866337
  | 7, 2, 1 => 0xb19791885b56600cbb1886656491c700cbaa976656231470000d0b197886656600d7cbb197886656700cb938866561c14700ebe6b19788562d700cb97887b665614700cbb6b1a088665670000cbb19788582660000cbb1977a6d3f600cbb19788665608700cbb1a697886656700e6cbb197663323700cbb1a497562d23700cbb197908866567
  | 7, 2, 2 => 0xcbbe97885e5660000cb97736d6656600cbb7b19788562d700e6b1978866560070000cbb1978b6632600ebd4b19788665670000cb8866331c1460000cbb1976b5621600e0cbb1976d665670000cbb197886c31600cb887a7066561470000cbb19784665660000cbb6a088665660000d5b19788562d600cbb19788564f2d700cbc6b1aa8866337
  | 7, 2, 3 => 0xf4cbb19766562370000ddb197886656600cbbab197885b56700eccbb197886633700cbb1978866564c700cbb19788562d01700cb886656231c1470000cbb1976d562d60000d4b197886656600d5cbb197936642700cbb19756332d23700cbb1ae97562d23700e6dab19788562d700e6cbb19788332d700c6b1976656230d700d5b1ae978866567
  | 7, 2, 4 => 0xcbb19a886656600d4beb197886656700b197886b66560d700cbbeb197886f56700beb1978866330d70000cbb19793663a600cbb197562d262370000cdb197886656600cbb197887466567cbc6b1978859563f800d4cbb197886633700cb8866562d1c14700cbb1ae976d6656700decbb197846656700b197886656420870000cbb1a78866566
  | 7, 2, 5 => 0xcbc6b19766332370000b1976633230d600f4cbb19788562d70000d4b197887a3f600cbb1ab97886633700cbb19788726656700ebb19788665605700e5cbb19788665670000cb887370665660000cbb68866561c600ebd2b197886656700e1cbb197886656700c6b19788562d0d700cb97887a665612700d5b1978866564f700cbb19766564b237
  | 7, 2, 6 => 0xb1979388562d0d700cbb19788564b2d700dab19788665605700cbb1978866330570000cbb19766421e600cb887a66561c14700d5cbb197665623700cbb19788686656700cbb1978877665670000cbbd97886656600cbb1978866331d700ebdeb197886633700e6cbb197887a3f700b197665956420d70000d4b197665623600b1978866563a0d7
  | 7, 2, 7 => 0xdab19788664f60000b19788332d0d60000cbb197896656600cbb1978c886633700cbc9b197886633700f0ebb197886633700b1976b6656230d700b19766562d230d70000cdb197665623600cbb1978866565570000cbb197886e3f60000cbb19781665660000d4b1978c665660000cbb19792665660000cbb197883f2460000d0b19788562d6
  | 7, 2, 8 => 0xcbb19759561d60000cbb29788665660000cbb1976e6642600d5cbb19788562d700b19788562d230d700d0cbb19788665670000cfb197886656600d5b1978866560870000cbb19766572060000cbb197945b56600f4e6b19788665670000d4b19788562d600cbc6b1979366427ebcbb19788665648800cbc6b19788332d70000b1979366420d6
  | 7, 2, 9 => 0xb1977a6656230d700decb8866561c14700b197665756230d700cbb19788664e33700b197886d66560d700e6cbb19793562d700b197948866330d700d2cbb197663323700b19788663f330d700dacb8866561c1470000cbb1976656256
  | 8, 0, 0 => 0xcbc6b19766562370000b1976656230d6cbc6b19788806656800cbb18866563f1c7cbb1ae97886656468e6cbb19788665956800cbb19e97886633700cbc6be978866567e6cbb1978866564f800ebcbb197886633700cbb1886656331c700cbb197887a663f700cbb197938866567decbc6b1978866568ebcbb19793886656800beb1978866560d7
  | 8, 0, 1 => 0xd2cbb197886656700cbb197886656167cbbeb19793886656800cbb1978866561d700b1a4978866560d700cbb1978b8866567ebcbb19788665623800ebdeb1978866567000097886656140d600cb97938f886656700cbb19997886656700cbb1979466595670000cbb197886633600cbb1948866561c7cbb1aa9788665645800cbb197886656327
  | 8, 0, 2 => 0xe6cbb19788665642800cbbeb197886633700cbb19794885956700cbb1a597886656700cbb1978866562d700cbb1886659561c700cbb1978859563f700f0cbc697886656700cbb19788665b567cbb1a197886656428ebcbb1978866562d800dacbb197886633700cbb19788665605700cbb197886656237decbb19793886656800cbb5b1978866567
  | 8, 0, 3 => 0xe6cbb8b1978866568cbbeb19788665623800cbb19788666156700cbb19788665617700cb979388665614700cbc6b19788562d700cbb1978866562070000b19788562d0d600cbb1978c886656700cbb197936656237d5cbb19788665642800cbc9b197886656700dedab197886656700decbb197886633700f0ebb197886656700cbb197886b66567
  | 8, 0, 4 => 0xb1978866563f0d7cbb1aa97887c665680000cb9788663314600cbb19766595642700cbb1886656421c700cbb1978866563a700cbb199976656237cbbeb1978866562d80000cbb1976633236cbc6b19788665633800cbb19788665d56700b197886656330d700cbb19788665649700b1ae978866560d700cbb197886664567decbb197886656238
  | 8, 0, 5 => 0xebcbb1aa8866567cbb1a0978866563f800cbb19788665630700cbb197887a6656700cbb19788665756700cbb1979388562d700cb978866562314700efcbb197886656700cbb8b18866561c700cbb1978866564e7cbc6b197948866568ebcbb197887a6656800b197948866560d700cbb19793885b56700cbb1a4978866337cbc6b1978866563f8
  | 8, 0, 6 => 0xcbb1ae978866337cbbeb197887a6656800cbb1978866560e700eacbb197886656700cbc8b19788665670000cbb19793664260000cbb19788332d6cbc6b19788665956800cbb19766562320700b197886659560d700cbb6b197886656700cb978866562d14700cbb1976b665623700cbb197887e6656700cbb19766562d23700cbc1b18866561c7
  | 8, 0, 7 => 0xcbb1977a665623700cbb19788666056700cbb19766575623700d1cbb197886656700cbb19788665615700cbb197886d66567ebcbbeb1978866568cbc6b19788665642800cbb19794886633700b197886656420d700cbb19788663f337cbb5b19788665633800cbb1978866562170000cbb6978866566decbb197887a6656800cbb19788562d237
  | 8, 0, 8 => 0xcbb1aaa48866567dacbbeb197886656800ebcbb1976656237e6cbb19788666256800f1cbb197886656700cbb19788665933700cbb197886c6633700e6cbb197665956700e6cbb18866561c700cbb19788663331700cb97887a665614700cbb19788665e567eadecbb1978866568cbb1ae978866562d800b1979391886656700dbcbb1978866567
  | 8, 0, 9 => 0xcbc6b1978866564b800dacbb197665623700cbb1978866563e70000cbb1979459566cbb1a59788665956800cbb197887a562d700cbc6c1978866567decbbeb197886656800cbb4b197886656700cbb19766562321700cb97887a73665670000cbb197665623600cbb19788806656700ebcb97886656147cbb1ae9788665d5680000cbb197887a3f6
  | 8, 0, 10 => 0xcbb19788562d6cbbeb1a497886656800decb9788665614700cbb19788665627700cbb1978866564470000cbb197885b56600decbb197665623700ebcbb19788562d700cbbeb197665623700f2cbb197886656700cbb197886f6656700dacb97886656147cbb1ae97887a665680000cbb1978c6656600cbb19788665606700cbb197886642337
  | 8, 0, 11 => 0xebcbb19794886656800d1cbb19788562d700cbb197887f665670000cb97665623146f2decbb197886656800dacbb19788562d7ebcbb1978866563f800cbb1af97886656700cbb19788665600700cbb19788665633700cbb197888666567e6cbc6b197886656800e2cbb1978866567ebcbb197886656338decbb1a4978866568cbb19794887a66568
  | 8, 0, 12 => 0xdecbb1ae97886656800cbb1977a6d66567cbbeb197886656338cbbeb1ae97886656800cbb19788665626700ebe6b1978866567e2decbb197886656800cbb19788665856700decbb19788562d700cbb197948866567dacbb1ae97886656800cbbeb19788562d700cbb6978866563f7f0cbb1a497886656800cbb1978866563f700cbb1a4976656237
  | 8, 0, 13 => 0xcb9788562d146cbbeb197948866568cbbeb1aa97886656800cbb4b19788562d700cbb197888366567cbbeb1978866563f80000cbb197562d23600cbb1978866595670000d5b197886656600cbb19794936656700cbb1978866564f700cbb197886c66567dacbb19794886656800cbb197886656317decbb197886656338ebcbb197886659568
  | 8, 0, 14 => 0xcbb19794665623700cbb197886656517cbbeb19788665956800cbb19766563f237ebcbb19788665642800cbb1978866563d700cbb1978866560170000cbb1976d66566f0cbb1ae97886656800cbb19766563323700cbb1ae97665623700e6dab197886656700e6cbb197886633700cbb1a49788562d700cbb7b1978866567decbb197948866568
  | 8, 0, 15 => 0xdecbb19788665642800cbb1978866561e700cbb197968866567cbbeb19788665642800cbb19793665642700cbb19766595623700cbb1978856332d700cbb1ae9788562d700c6b1978866560d700cbb1978c66563f700cbb1978a8866567cbb1a497948866568e6cbb1978866562d800cbb19788665642700cbaa9788665614700cbb19788562d277
  | 8, 1, 0 => 0xcbb19788665624700cbb1ac97886656700cbb1978859562d7cbc6b19793886656800cbb197665642237e6cbb197887a6656800b197938866560d700cbb1978866564b7cbb1979488665633800cbb19788562d267cbb1ae978866563f800cbb1978858562d700cbb1979488562d700f4cbb197886656700cbb19788563f2d7cbb1ae97886656338
  | 8, 1, 1 => 0xe6cbb1979366567cbc6b1978866562d800b1978866562d0d700cbb1978856422d700cbc3b1978866567cbc6b19788665623800d5cbb1978866567cbc1b1a497886656800b197886656230d700cbb197887a563f70000d4b197886656600cbc6b19788663370000b1978866330d6cbb1ae9788665956800cbb197886e6656700cecbb1978866567
  | 8, 1, 2 => 0xd5b19788665642700cbb19788663323700d2cbb197886633700e6cbb197665623700cbb1978b886633700cbb19788826656700cbb19788663332700cecbb197665623700cbb19788666256700cbcab197886656700cbb19788665645700e9cbb1978866567e6cbbeb197886656800cbb197938866337cbb1ae9788665642800cbb1978a88562d7
  | 8, 1, 3 => 0xcbb197887a66337cbc6b197886660568e6cbb1978866563f800d4cbb1978866567dacbc6b197886656800d4b1978866563f7e6cbb19788665633800cbb19793886642700e6cbb19788562d70000cb8866561c14600b197887a766656700cbb1978866332d7cbc6b197887a6656800b197887a66560d7
  | 9, 0, 0 => 0xcbb197886656337cbb1ae97886656700cbb19788562d6cbb1a497886656700cb9788665614600cbb1976656236decbb1978866567cbbeb1978866567dacbb197886656700cbb1978866566ebcbb1978866567cbb197887a66567cbb1978866562d7cbb19788665623700cbb1978866336cbb197938866567
  | 9, 0, 1 => 0xcbc6b197886656700b1978866560d6e6cbb1978866567cbb197886656427cbb197886659567cbb197948866567cbb1978866563f7
  | 10, 0, 0 => 0xcbb1978866566
  | _, _, _ => 0
def stateW : Nat → Nat
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
  | 0, 0 => 0x3fffffe3000000000000000000000000000000000000000000000000000000003fe1e1e200000000000000000000000000000000000000000000000000000000339f9e1d00000000000000000000000000000000000000000000000000000000001e1e1d000000000000000000000000000000000000000000000000000000000ffe7fe3000000000000000000000000000000000000000000000000000000000e7e7fff000000000000000000000000000000000000000000000000000000000e7e7e030000000000000000000000000000000000000000000000000000000001fe01ff
  | 0, 1 => 0x387c0007e030000000000000000000000000000000000000000000000000000007fc00001ff000000000000000000000000000000000000000000000000000000003fffffff00000000000000000000000000000000000000000000000000000000319f9ffd000000000000000000000000000000000000000000000000000000000c7e7fff000000000000000000000000000000000000000000000000000000000e7e7fe3000000000000000000000000000000000000000000000000000000003fffffff000000000000000000000000000000000000000000000000000000003fffffe3
  | 0, 2 => 0x1f00e01e001e200000000000000000000000000000000000000000000000000019079c19e001d00000000000000000000000000000000000000000000000000007007c07e000300000000000000000000000000000000000000000000000000000fffc001ffff00000000000000000000000000000000000000000000000000000c79c0019ffd00000000000000000000000000000000000000000000000000000377c0007fff00000000000000000000000000000000000000000000000000000fffc001ffff00000000000000000000000000000000000000000000000000000cf9c0019e1d
  | 0, 3 => 0xe7387ce7e7e03000000000000000000000000000000000000000000000000000e73860e60600200000000000000000000000000000000000000000000000000021081c21e1e010000000000000000000000000000000000000000000000000001f07fc1fe01ff00000000000000000000000000000000000000000000000000018079c19e01fd00000000000000000000000000000000000000000000000000019079c19e01fd00000000000000000000000000000000000000000000000000006077c07e01ff0000000000000000000000000000000000000000000000000001f07fc1fe01ff
  | 0, 4 => 0x318c783181801c00000000000000000000000000000000000000000000000000000071c01e1e1d000000000000000000000000000000000000000000000000003fff8ffffffe0300000000000000000000000000000000000000000000000000339c8833818000000000000000000000000000000000000000000000000000000e7387ce7e7e03000000000000000000000000000000000000000000000000000c6307cc7e7e03000000000000000000000000000000000000000000000000000c63060c60600200000000000000000000000000000000000000000000000000000001c01e1e01
  | 0, 5 => 0x3def7e3de1e01e000000000000000000000000000000000000000000000000003ffffffffffe1f00000000000000000000000000000000000000000000000000339cf9f39f9e1d00000000000000000000000000000000000000000000000000339cf9f39e000000000000000000000000000000000000000000000000000000339cf9f181801c00000000000000000000000000000000000000000000000000339c80339f9e0000000000000000000000000000000000000000000000000000339c78339f801c00000000000000000000000000000000000000000000000000318c79f19f9e1d
  | 0, 6 => 0x3fffffffe1ffff000000000000000000000000000000000000000000000000003fffffffe1e1ff000000000000000000000000000000000000000000000000003fffffffe1e1ff000000000000000000000000000000000000000000000000003fff8e3fffffe3000000000000000000000000000000000000000000000000003fff8e3fe1e1e200000000000000000000000000000000000000000000000000318c08318181e0000000000000000000000000000000000000000000000000000c63060c6061e2000000000000000000000000000000000000000000000000003ffffffffffe1f
  | 0, 7 => 0x3fffffffffffff00000000000000000000000000000000000000000000000000318c78318181fc000000000000000000000000000000000000000000000000000c6377cc7e7fff000000000000000000000000000000000000000000000000003fff8fffffffe300000000000000000000000000000000000000000000000000318c09f19f9fe1000000000000000000000000000000000000000000000000003fff8fffffe1e3
  | 0, 8 => 0x1e00000000000000000000000000000000000000000000000000000000007000001e1c0000000000000000000000000000000000000000000000000000000000001e00000000000000000000000000000000000000000000000000000000700000001c000000000000000000000000000000000000000000000000000e73f60e60601e000000000000000000000000000000000000000000000000000000700000001c00000000000000000000000000000000000000000000000000339c8833818000000000000000000000000000000000000000000000000000000e7387ce7e7e03
  | 0, 9 => 0x71c000001c00000000000000000000000000000000000000000000000000000071c000000000000000000000000000000000000000000000000000000000000070001e1e1c00000000000000000000000000000000000000000000000000000000001e1e0000000000000000000000000000000000000000000000000000000000001e1e0000000000000000000000000000000000000000000000000000000070001e001c00000000000000000000000000000000000000000000000000000070001e001c00000000000000000000000000000000000000000000000000000000001e0000
  | 0, 10 => 0xe73f7ce7e7e1f00000000000000000000000000000000000000000000000000000071c01e1e1d00000000000000000000000000000000000000000000000000000071c01e1e0000000000000000000000000000000000000000000000000000000071c01e000000000000000000000000000000000000000000000000000000000071c01e000000000000000000000000000000000000000000000000000000000071c0001e1c00000000000000000000000000000000000000000000000000000071c0001e0000000000000000000000000000000000000000000000000000000071c000001c
  | 0, 11 => 0xc60000c6001e0000000000000000000000000000000000000000000000000000c60000c600000000000000000000000000000000000000000000000000000000c03000c0061e0000000000000000000000000000000000000000000000000000c03000c00600000000000000000000000000000000000000000000000000000000000000001e000000000000000000000000000000000000000000000000000021081c21e1fe100000000000000000000000000000000000000000000000000000000000001e000000000000000000000000000000000000000000000000000339cf9f39f9e1d
  | 0, 12 => 0xc63060e7e7fe3000000000000000000000000000000000000000000000000000c63060c6061e2000000000000000000000000000000000000000000000000000c63060c600000000000000000000000000000000000000000000000000000000c63060c006000000000000000000000000000000000000000000000000000000c6306000001e0000000000000000000000000000000000000000000000000000c6306000001e0000000000000000000000000000000000000000000000000000c630600000000000000000000000000000000000000000000000000000000000c63000c606000
  | 0, 13 => 0xc63760c6061fe00000000000000000000000000000000000000000000000000000071c01e1ffd00000000000000000000000000000000000000000000000000000070000001fc000000000000000000000000000000000000000000000000003fff8e3fe1e1e2000000000000000000000000000000000000000000000000000e7387ce7e7fe3000000000000000000000000000000000000000000000000000e73860e6061e2000000000000000000000000000000000000000000000000000c6387cc607fe3000000000000000000000000000000000000000000000000000c637fcc6061ff
  | 0, 14 => 0xc6377c00001fc000000000000000000000000000000000000000000000000000c6377c0000000000000000000000000000000000000000000000000000000000c63060c7e7fe2000000000000000000000000000000000000000000000000000c63000c7e7e00000000000000000000000000000000000000000000000000000c60000c7e0000000000000000000000000000000000000000000000000000000c63760c607ffe000000000000000000000000000000000000000000000000000c03700c007ffc000000000000000000000000000000000000000000000000000c03000c007e00
  | 0, 15 => 0x318000318001e0000000000000000000000000000000000000000000000000003180703180001c00000000000000000000000000000000000000000000000000300c70300181fc00000000000000000000000000000000000000000000000000300c00300181e000000000000000000000000000000000000000000000000000300c703001801c000000000000000000000000000000000000000000000000000c6377cc7e7fff000000000000000000000000000000000000000000000000000c6377cc7e61e2000000000000000000000000000000000000000000000000000c6377cc6061fe
  | 1, 0 => 0x318c783181800000000000000000000000000000000000000000000000000000318c783180000000000000000000000000000000000000000000000000000000318c783001800000000000000000000000000000000000000000000000000000318c78000001fc00000000000000000000000000000000000000000000000000318c78000001e000000000000000000000000000000000000000000000000000318c780000001c00000000000000000000000000000000000000000000000000318c00318181e000000000000000000000000000000000000000000000000000318c0031818000
  | 1, 1 => 0x318000319e000000000000000000000000000000000000000000000000000000300c0030019fe000000000000000000000000000000000000000000000000000300c0030019e0000000000000000000000000000000000000000000000000000318c78318181fc000000000000000000000000000000000000000000000000003ffffe3fe1e1fe00000000000000000000000000000000000000000000000000339cf9f39f9ffd00000000000000000000000000000000000000000000000000339cf8338181fc00000000000000000000000000000000000000000000000000318c78318181fc
  | 1, 2 => 0x3e0f803e01fe00000000000000000000000000000000000000000000000000003def7ffdffffff000000000000000000000000000000000000000000000000003ffffe3fe1e1fe000000000000000000000000000000000000000000000000003def7e3de1e1fe00000000000000000000000000000000000000000000000000318c79f19f9ffd00000000000000000000000000000000000000000000000000318c79f18181fc00000000000000000000000000000000000000000000000000318c79c000000000000000000000000000000000000000000000000000000000318c00319f9e00
  | 1, 3 => 0x3e0f803e01fe00000000000000000000000000000000000000000000000000003fff8e3fe1ffe2000000000000000000000000000000000000000000000000003f8f883f81ffe0000000000000000000000000000000000000000000000000003e6f863e61ffe2000000000000000000000000000000000000000000000000003f8ff83f81fe1c000000000000000000000000000000000000000000000000003f9f883f81fe00000000000000000000000000000000000000000000000000003e7f87fe7ffe03000000000000000000000000000000000000000000000000003e6f863e61fe02
  | 1, 4 => 0x3e6f803e61fe00000000000000000000000000000000000000000000000000003e6c003e6181e0000000000000000000000000000000000000000000000000003e0f803e01ffe0000000000000000000000000000000000000000000000000003e0ff1fe1ffe1d000000000000000000000000000000000000000000000000003e0ff1f001801c000000000000000000000000000000000000000000000000003e03003e1e6000000000000000000000000000000000000000000000000000003e0ff03e01fe1c000000000000000000000000000000000000000000000000003e0f803e01fe00
  | 1, 5 => 0x3f8ff9ff9ffffd000000000000000000000000000000000000000000000000003f8ff83f81fffc000000000000000000000000000000000000000000000000003f80703f801e1c000000000000000000000000000000000000000000000000003e6ff7fe7fffff000000000000000000000000000000000000000000000000003fff8e3fe1ffe2000000000000000000000000000000000000000000000000003e6f863e61ffe2000000000000000000000000000000000000000000000000003e6f86300181e0000000000000000000000000000000000000000000000000003e6f8600001e00
  | 1, 6 => 0x3ff0703ffe001c000000000000000000000000000000000000000000000000003ff0003ffe0000000000000000000000000000000000000000000000000000003fff8e3fffe1e2000000000000000000000000000000000000000000000000003ffcf9ffff9e1d000000000000000000000000000000000000000000000000003ff387fffe7e03000000000000000000000000000000000000000000000000003ff3863ffe6002000000000000000000000000000000000000000000000000003ff0003ffe0000000000000000000000000000000000000000000000000000003feffe3fe1fffe
  | 1, 7 => 0x3ff0703ffe01fc000000000000000000000000000000000000000000000000003ff3063ffe61e2000000000000000000000000000000000000000000000000003ff3063ffe6000000000000000000000000000000000000000000000000000003ff3063ffe0000000000000000000000000000000000000000000000000000003ff306318001e0000000000000000000000000000000000000000000000000003ff0003ffe01e0000000000000000000000000000000000000000000000000003ff0003ffe01e0000000000000000000000000000000000000000000000000003ff071fffe1e1d
  | 1, 8 => 0x3fff8e3fffffe2000000000000000000000000000000000000000000000000003fff803ffffe00000000000000000000000000000000000000000000000000003fff8031818000000000000000000000000000000000000000000000000000003fff80001e1e00000000000000000000000000000000000000000000000000003fff7e3fffe1fe000000000000000000000000000000000000000000000000003ffffe3fffe1fe000000000000000000000000000000000000000000000000003ffc783fff81fc000000000000000000000000000000000000000000000000003ffc78001e001c
  | 1, 9 => 0x3ffffff3818000000000000000000000000000000000000000000000000000003fffffce7e7e03000000000000000000000000000000000000000000000000003fffffcc606002000000000000000000000000000000000000000000000000003fffffce606002000000000000000000000000000000000000000000000000003fffffc0000000000000000000000000000000000000000000000000000000003ffff83ffffffc000000000000000000000000000000000000000000000000003fff863fffffe2000000000000000000000000000000000000000000000000003ffff1fffffe1d
  | 1, 10 => 0x3fffffc0001e1c000000000000000000000000000000000000000000000000003fffffc000001c000000000000000000000000000000000000000000000000003fffffc000001c000000000000000000000000000000000000000000000000003fffffc0000000000000000000000000000000000000000000000000000000003fffffc0000000000000000000000000000000000000000000000000000000003fffffffe1e1e2000000000000000000000000000000000000000000000000003ffffff39f9e1d000000000000000000000000000000000000000000000000003ffffff181801c
  | 1, 11 => 0x3fffffffe1e1e2000000000000000000000000000000000000000000000000003fffffcc6061e2000000000000000000000000000000000000000000000000003fffffcc606000000000000000000000000000000000000000000000000000003fffffcc006000000000000000000000000000000000000000000000000000003fffffc00001e0000000000000000000000000000000000000000000000000003fffffc01e1e1d000000000000000000000000000000000000000000000000003fffffc01e1e00000000000000000000000000000000000000000000000000003fffffc01e0000
  | 1, 12 => 0x3fffffffe1e1fe000000000000000000000000000000000000000000000000003ffffff18181fc000000000000000000000000000000000000000000000000003ffffff1818000000000000000000000000000000000000000000000000000003ffffff00181e0000000000000000000000000000000000000000000000000003ffffff001801c000000000000000000000000000000000000000000000000003fffffcc7e7fff000000000000000000000000000000000000000000000000003fffffcc6061fe000000000000000000000000000000000000000000000000003fffffc00001fc
  | 1, 13 => 0x3fffffff81fffc000000000000000000000000000000000000000000000000003ffffffe01fe1c000000000000000000000000000000000000000000000000003ffffffe01fe00000000000000000000000000000000000000000000000000003fffffffe1ffe2000000000000000000000000000000000000000000000000003ffffffe01fe00000000000000000000000000000000000000000000000000003ffffffde1e1fe000000000000000000000000000000000000000000000000003ffffff19f9ffd000000000000000000000000000000000000000000000000003ffffff18181fc
  | 1, 14 => 0x3ffffffffffe00000000000000000000000000000000000000000000000000003fffffffff81fc000000000000000000000000000000000000000000000000003ffffffffe61e2000000000000000000000000000000000000000000000000003ffffffffe1e1d000000000000000000000000000000000000000000000000003ffffffffe0000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x2b4948c000000000000000000000000000000000000000000000000000000000294140c000000000000000000000000000000000000000000000000000000000128c8c1800000000000000000000000000000000000000000000000000000000128c8c1800000000000000000000000000000000000000000000000000000000076a2a8300000000000000000000000000000000000000000000000000000000062a2a2700000000000000000000000000000000000000000000000000000000062a2a030000000000000000000000000000000000000000000000000000000001e600b7
  | 0, 1 => 0x182c00032030000000000000000000000000000000000000000000000000000001e40000127000000000000000000000000000000000000000000000000000000003fefeeff000000000000000000000000000000000000000000000000000000003fefeeff000000000000000000000000000000000000000000000000000000003fefeeff000000000000000000000000000000000000000000000000000000002f6b6ae7000000000000000000000000000000000000000000000000000000003bcdccd8000000000000000000000000000000000000000000000000000000002f6b6ac3
  | 0, 2 => 0x1400c014001800000000000000000000000000000000000000000000000000000904100940010000000000000000000000000000000000000000000000000000030034032000300000000000000000000000000000000000000000000000000000fbec001f76f00000000000000000000000000000000000000000000000000000fbec001f76f00000000000000000000000000000000000000000000000000000fbec001f76f00000000000000000000000000000000000000000000000000000eac8001d548000000000000000000000000000000000000000000000000000004a080009408
  | 0, 3 => 0x2108182181800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000021081821818000000000000000000000000000000000000000000000000000001f05f41f601b70000000000000000000000000000000000000000000000000001f05f41f601b70000000000000000000000000000000000000000000000000001d05d01d401b40000000000000000000000000000000000000000000000000001f05f41f601b70000000000000000000000000000000000000000000000000001d04d01d40190
  | 0, 4 => 0x10846010848418000000000000000000000000000000000000000000000000001294e1929c9c1800000000000000000000000000000000000000000000000000063183c63a3a03000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000063183c63a3a0300000000000000000000000000000000000000000000000000063183c63a3a03000000000000000000000000000000000000000000000000000421024422220300000000000000000000000000000000000000000000000000063183c63a3a03
  | 0, 5 => 0x14a56254a6a61b000000000000000000000000000000000000000000000000001294e1929c9c18000000000000000000000000000000000000000000000000001294e1929c9c18000000000000000000000000000000000000000000000000001294e1929c1810000000000000000000000000000000000000000000000000001294e190949418000000000000000000000000000000000000000000000000001294e1929c9c1800000000000000000000000000000000000000000000000000129461129c8c18000000000000000000000000000000000000000000000000001294e1929c9c18
  | 0, 6 => 0x294eaca941d5c800000000000000000000000000000000000000000000000000294a1e694141e700000000000000000000000000000000000000000000000000294a0c294141c000000000000000000000000000000000000000000000000000294a0c2f6b6bc300000000000000000000000000000000000000000000000000294a0c294141c000000000000000000000000000000000000000000000000000294a0c294141c000000000000000000000000000000000000000000000000000294a0c294141c00000000000000000000000000000000000000000000000000016b5e3d6bebe1b
  | 0, 7 => 0x42112442222270000000000000000000000000000000000000000000000000000001000000024000000000000000000000000000000000000000000000000003bdeedbbddddd80000000000000000000000000000000000000000000000000039ce6c39c5c5d8000000000000000000000000000000000000000000000000003bdeedbbddddd8000000000000000000000000000000000000000000000000002f7b8fef7b7bc3000000000000000000000000000000000000000000000000002f7b8fef7b7bc300000000000000000000000000000000000000000000000000297a0f697341c3
  | 0, 8 => 0x16b05116be0834000000000000000000000000000000000000000000000000001685f0968cbe3c000000000000000000000000000000000000000000000000001625b2d62abe2f0000000000000000000000000000000000000000000000000014a57254a6a63f000000000000000000000000000000000000000000000000001084701084843c000000000000000000000000000000000000000000000000001084701084843c000000000000000000000000000000000000000000000000000421124422222700000000000000000000000000000000000000000000000000063193c63a3a27
  | 0, 9 => 0x16b5f3d094943c0000000000000000000000000000000000000000000000000016b5f3c43232270000000000000000000000000000000000000000000000000016b5f196bebe3c0000000000000000000000000000000000000000000000000016b5f3d6bebe3f0000000000000000000000000000000000000000000000000016b5e196bebe180000000000000000000000000000000000000000000000000016b57356beae3f0000000000000000000000000000000000000000000000000016b47116be8c3c0000000000000000000000000000000000000000000000000016b15356be2a37
  | 0, 10 => 0x16b5f3d6bebe3f0000000000000000000000000000000000000000000000000016b5f3d6bebe3f0000000000000000000000000000000000000000000000000016b5f3d6bebe180000000000000000000000000000000000000000000000000016b5f3d6be3a370000000000000000000000000000000000000000000000000016b5f3d6be18100000000000000000000000000000000000000000000000000016b5f3d69cbe3c0000000000000000000000000000000000000000000000000016b5f3d618be080000000000000000000000000000000000000000000000000016b5f3d4b6b63f
  | 0, 11 => 0x2d6b1e6d6363e7000000000000000000000000000000000000000000000000002d61126d6222a7000000000000000000000000000000000000000000000000002d4b1c2d4163e4000000000000000000000000000000000000000000000000002c2b126c236267000000000000000000000000000000000000000000000000002d6b1e6d6363e7000000000000000000000000000000000000000000000000002b5a9dab5959e400000000000000000000000000000000000000000000000000294a1c294141e40000000000000000000000000000000000000000000000000016b5f3d6bebe3f
  | 0, 12 => 0x2d6b1e6f6b6be7000000000000000000000000000000000000000000000000002d6b1e6d6363e7000000000000000000000000000000000000000000000000002d6b1e6d620180000000000000000000000000000000000000000000000000002d6b1e6c016340000000000000000000000000000000000000000000000000002d6b1e6d6363e7000000000000000000000000000000000000000000000000002d6b1e694141e4000000000000000000000000000000000000000000000000002d6b1e44222327000000000000000000000000000000000000000000000000002d6b002d6362c0
  | 0, 13 => 0x3def7e7de7e7ff000000000000000000000000000000000000000000000000003fffffffffffff0000000000000000000000000000000000000000000000000039ce7c39c5c5fc000000000000000000000000000000000000000000000000002d6b1e6d6363e7000000000000000000000000000000000000000000000000002f7b9fef7b7be7000000000000000000000000000000000000000000000000002d6b1e6d6363e7000000000000000000000000000000000000000000000000002d6b9eed6373e7000000000000000000000000000000000000000000000000002d6b1e6d6363e7
  | 0, 14 => 0x3ffffff9d5d5fc000000000000000000000000000000000000000000000000003fffffc0101100000000000000000000000000000000000000000000000000003fffffffffffff000000000000000000000000000000000000000000000000003fffe1bffffed8000000000000000000000000000000000000000000000000003ff0413ffe0890000000000000000000000000000000000000000000000000003feffeffefffff000000000000000000000000000000000000000000000000003fcffcbfcdfffc000000000000000000000000000000000000000000000000003e0fa0be09fe48
  | 0, 15 => 0x39ca5c39c541f40000000000000000000000000000000000000000000000000039c47039c484bc0000000000000000000000000000000000000000000000000039ce7c39c5c5fc00000000000000000000000000000000000000000000000000394e3c3941c5ec00000000000000000000000000000000000000000000000000388e703885c47c000000000000000000000000000000000000000000000000003fffffffffffff000000000000000000000000000000000000000000000000003fffffffff7bf7000000000000000000000000000000000000000000000000003ffffffdf7f7ff
  | 1, 0 => 0x39ce7c39c5c5d80000000000000000000000000000000000000000000000000039ce7c39c401900000000000000000000000000000000000000000000000000039ce7c3801c5480000000000000000000000000000000000000000000000000039ce7c39c5c5fc0000000000000000000000000000000000000000000000000039ce7c294141e40000000000000000000000000000000000000000000000000039ce7c1084853c0000000000000000000000000000000000000000000000000039ce7c39c5c5fc0000000000000000000000000000000000000000000000000039ce6039c5c4d8
  | 1, 1 => 0x3ff0413ffe0890000000000000000000000000000000000000000000000000003f6fbeff6bffef000000000000000000000000000000000000000000000000003e0fa0be09fe48000000000000000000000000000000000000000000000000003def7e7de7e7ff0000000000000000000000000000000000000000000000000039ce7c39c5c5fc000000000000000000000000000000000000000000000000003bdefdbbddddfc0000000000000000000000000000000000000000000000000039ce7c39c5c5fc0000000000000000000000000000000000000000000000000039ce7c39c5c5fc
  | 1, 2 => 0x3e0fa0be09fe48000000000000000000000000000000000000000000000000003fffffffffffff000000000000000000000000000000000000000000000000003def7e7de7e7ff000000000000000000000000000000000000000000000000003def7e7de7e7ff000000000000000000000000000000000000000000000000003fffffffffffff000000000000000000000000000000000000000000000000003ffffffdf7f7ff000000000000000000000000000000000000000000000000003fffffc0101100000000000000000000000000000000000000000000000000003fffe1bffffed8
  | 1, 3 => 0x3e0fb0be09fe6c000000000000000000000000000000000000000000000000003f4facbf49ffc8000000000000000000000000000000000000000000000000003f4facbf49ffc8000000000000000000000000000000000000000000000000003f4facbf49ffc8000000000000000000000000000000000000000000000000003e8fe0be8dfe58000000000000000000000000000000000000000000000000003e0fa0be09fe48000000000000000000000000000000000000000000000000003e3fa3fe3bfe4b000000000000000000000000000000000000000000000000003e2fa2fe2bfe4b
  | 1, 4 => 0x3f6fb2ff6bfeef000000000000000000000000000000000000000000000000003f6e3c3f6bcdec000000000000000000000000000000000000000000000000003f4fbcbf49ffec000000000000000000000000000000000000000000000000003ebff3febffe7f000000000000000000000000000000000000000000000000003ebff3f895d47c000000000000000000000000000000000000000000000000003ebb537ebf6a77000000000000000000000000000000000000000000000000003e8ff0be8dfe7c000000000000000000000000000000000000000000000000003e2fb2fe2bfe6f
  | 1, 5 => 0x3fffffffffffff000000000000000000000000000000000000000000000000003fcffcbfcdfffc000000000000000000000000000000000000000000000000003fc5f0bfccbebc000000000000000000000000000000000000000000000000003fffffffffffff000000000000000000000000000000000000000000000000003f6fbeff6bffef000000000000000000000000000000000000000000000000003f6fbeff6bffef000000000000000000000000000000000000000000000000003f6fbef941d5ec000000000000000000000000000000000000000000000000003f6fbed62abf2f
  | 1, 6 => 0x3ff4713ffe8cbc000000000000000000000000000000000000000000000000003ff1537ffe2ab7000000000000000000000000000000000000000000000000003ffa4d3fff49d0000000000000000000000000000000000000000000000000003ff4e1bffe9c98000000000000000000000000000000000000000000000000003ff1c3fffe3a93000000000000000000000000000000000000000000000000003ff0413ffe0890000000000000000000000000000000000000000000000000003ff0413ffe0890000000000000000000000000000000000000000000000000003feffeffefffff
  | 1, 7 => 0x3ffe7d3fffcdfc000000000000000000000000000000000000000000000000003ffb5f7fff6bf7000000000000000000000000000000000000000000000000003ffb5f7fff6bd0000000000000000000000000000000000000000000000000003ffb5f7ffe2bb7000000000000000000000000000000000000000000000000003ffb5f79d541f4000000000000000000000000000000000000000000000000003ffb5f7fff6bf7000000000000000000000000000000000000000000000000003ffa5d3fff49f4000000000000000000000000000000000000000000000000003ff5f3fffebebf
  | 1, 8 => 0x3fffedbfffffd8000000000000000000000000000000000000000000000000003fffe1bffffed8000000000000000000000000000000000000000000000000003fffe1b9d5d4d8000000000000000000000000000000000000000000000000003fffe196bebe18000000000000000000000000000000000000000000000000003fff7f7fffefff000000000000000000000000000000000000000000000000003ffe7d3fffcdfc000000000000000000000000000000000000000000000000003ffe7d3fffcdfc000000000000000000000000000000000000000000000000003ffe7d16be8d3c
  | 1, 9 => 0x3fffffc0101100000000000000000000000000000000000000000000000000003fffffc63a3b03000000000000000000000000000000000000000000000000003fffffc4323303000000000000000000000000000000000000000000000000003fffffc0101100000000000000000000000000000000000000000000000000003fffffc0101100000000000000000000000000000000000000000000000000003ffffdbffffffc000000000000000000000000000000000000000000000000003fffffffffffff000000000000000000000000000000000000000000000000003ffff3fffffeff
  | 1, 10 => 0x3fffffd69cbf3c000000000000000000000000000000000000000000000000003fffffd4b6b73f000000000000000000000000000000000000000000000000003fffffd094953c000000000000000000000000000000000000000000000000003fffffc4323327000000000000000000000000000000000000000000000000003fffffc0101124000000000000000000000000000000000000000000000000003fffffe95151c0000000000000000000000000000000000000000000000000003fffffd29c9d18000000000000000000000000000000000000000000000000003fffffd0949518
  | 1, 11 => 0x3fffffed7373e7000000000000000000000000000000000000000000000000003fffffed7373e7000000000000000000000000000000000000000000000000003fffffed7373c0000000000000000000000000000000000000000000000000003fffffec337367000000000000000000000000000000000000000000000000003fffffe95151e4000000000000000000000000000000000000000000000000003fffffd6bebf3f000000000000000000000000000000000000000000000000003fffffd6bebf18000000000000000000000000000000000000000000000000003fffffd6be3b37
  | 1, 12 => 0x3ffffff9d5d5fc000000000000000000000000000000000000000000000000003ffffff9d5d5fc000000000000000000000000000000000000000000000000003ffffff9d5d5d8000000000000000000000000000000000000000000000000003ffffff951d5ec000000000000000000000000000000000000000000000000003ffffff895d57c000000000000000000000000000000000000000000000000003fffffffffffff000000000000000000000000000000000000000000000000003ffffffdf7f7ff000000000000000000000000000000000000000000000000003ffffff9d5d5fc
  | 1, 13 => 0x3fffffffddfffc000000000000000000000000000000000000000000000000003ffffffe9dff7c000000000000000000000000000000000000000000000000003ffffffe3bff6f000000000000000000000000000000000000000000000000003fffffff59ffc8000000000000000000000000000000000000000000000000003ffffffe19ff48000000000000000000000000000000000000000000000000003ffffffdf7f7ff000000000000000000000000000000000000000000000000003fffffffffffff000000000000000000000000000000000000000000000000003ffffffdf7f7ff
  | 1, 14 => 0x3fffffffffffd8000000000000000000000000000000000000000000000000003fffffffffddfc000000000000000000000000000000000000000000000000003fffffffff7bf7000000000000000000000000000000000000000000000000003ffffffffebfbf000000000000000000000000000000000000000000000000003ffffffffe1990
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 245 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 245 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 245 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 245 then wireAt i else 0
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
  | 5 => 50
  | 6 => 1092
  | 7 => 2876
  | 8 => 545
  | 9 => 10
  | _ => 0
def CH : Nat → Nat → Nat
  | 5, 0 => 0xf5707479ef4b64b6ef49de1aee25de7ded94e533e860c1ead75ad3f1ce9f2c6dc9a8ffaac7cc907dc5fd6269bd833101b560754eacd5c79ca746fd55a35c9dd68f8bfb7a7c0eaaa97b72b17778541dd6751613f1740f1b3f71a3faaf6ff5f389690b536461d7af806198c3205e2d8aab532a6f124ed2c8b44c753f2d468f8d1242b779a3425c660d418b8ad53bd4a88b2daeb2ee2d9e4af029d98e842171cbeb1ed15b311dcb86b71338cb6511a580bc111aa896110c960c10e063230dfb5be70cee53eb00dc39ff
  | 6, 0 => 0xbd946000b1f72c00b09be840a9ac0e30a7677f50a75789c0a55e5540a4bb82b0a4512b30a41d8c40a38ec8009f700f909f6f25b096366890922d0980900418408b46aa408697de008259fb107ec5f9c07d530e90772c9e807517d12073e6a6d06f72c6106d88c9f069bc502067a3838064bab2605de753505d8b03a05ca702105a805b705a197e905941c820548dc99053f9f86050bbc5f05048e7704f029ac04ae044e04773d45042b1f1e03512ecd034b623b02e62559026fd5be0269762b01fb5380017c2aac01373cfc012ce06c011daf4c0111388400fa914700d6864300c3cc4b00bbc06900b294a700a6d68e009f27ce00904a51006a05170025d314
  | 6, 1 => 0x1525469b14ec82a2149b001d14158fc113db0a691356a1bd13346ed113334dd912ee29ce12ec372612dc22d312c0971a129bea22126bfdab1255ab7c12361d88121b1123121a326811f9841911f45ea911cd770e11aee07211aa804311a70469119dfe101182dac01161181a11532b49114d8aa31101e76810d9018f10886e18100e0fc60fe749af0f983ff70f8898390f807fc40f2f0b0d0f1848110f124bee0f115ba20ee2d2210eb903040ea808060ea756a30e7e15130e44c68c0e1cb4fc0dc608ee0db658df0d88c2480d871bf50d6e8d170d55e2950d4ae8920d34e9280ccf58020cc70a280cb6d1e10cabde0a0c4d73f60c36bb900c0ec6b60be37329
  | 6, 2 => 0x1f426e131f24b0101eee48821edeef8d1e9cc3911e5785271e4a11701e3c15ab1e1b8df81df679371d600c9e1d03b18a1cd4a8b61cc7c4c71cb15bcf1c94b7df1c3316401c0aecba1bec56d41b95e62c1b6d57411b35e26c1b00133e1acbab401abf43c11a3fc2e519e9242f19d5fa5019ba301a19a85610197c44521977c4d919550146194d575a194d51da1937f12c18f26c4c18d18a6c18c37efc18ae0c7e18734073186cfbda1828bb38181787f11794abf0173f3e791734bd561701656116ec765a16eb0e0416c88223169a10fc16771b7216718ae7161c81b31619ab32160c315a15f0e8b9159bedf91594fa3815756a7b15711243152e636e15258895
  | 6, 3 => 0x28abb43f28a4a83e2899c1c7288ed9b92873acb2287147fc28627e8a285b57bf280064ef27fc79e327adaf20279261ef2775a76427320b4f26d3ff3726c09f4926acc7fc268164ee267b2055266e4226263de7eb2629ae6e261253a525d32ac22585bb98257d59b8256725372566dfcd24d87e4324cafef724c87e642496c8bb23fc2cd323e3e51a23cb565123b0a746238b6097234c018c2343055d231a9d2d230c8aa322ebbaaa22d2ddb122afbece2244ea16220641ba21b0632821b04b48213869ba20db85b720c912ec20bc756a20924f10203fef5c203f324b20292edb1ff175501fd723ee1fd161b61fa0bfc01f916b441f6f6fc41f6acb631f63f828
  | 6, 4 => 0x33d9d424338e8f45338d7624337c3f773373e505333d305e3335888b3321cd97330ebc1533084b5432fe99e432fa2f9532ef240132eb3d6832e5408e32df0cd0328e870831c4a7fe3156fc53311bd08830ed483930e70b6e30d6e2d830c8d3d03099cb893093efd23081025b30378bbb2fee79012fc2afe42f2d39052ef81bc92ef292772ee671c32edae5ed2e816dca2e418d672df03b792d8de92d2d6e8c932d12ca512cadc4612c86ddd02bf01f012bd9e6b92bcd5b7f2baabff12b8b68b52b87ab452b81626d2b2acd652ad4644e2ab77fdf2aa964312a8c84472a86e1112a0c3e3929eedbb829e188d329d2bd7f293f76f0292f8a3b2903a6a428acf457
  | 6, 5 => 0x3e1ce6143e0fc03d3dff0bee3dc96c5c3da400e63d9419de3d8de62c3d7f544c3d6a3aa23d513e8d3d4e5b033cec7dca3cb53f9e3cae957f3c9d75a23c4a4fba3c2e6bee3c21f90f3bf19aa63be5e98e3b5816813b2afff13b1d7a443b0f2c583a84e7713a7e30ef3a792f6a3a71b7533a4fc2063a126d2a39f21efe39614ab83928324d38dd990138bbbf8c38b24b93387c1086385fd6033844218c380458523803b6ee3787f39137809ff0376135eb373b41c13739d460369f769f369d00c93664dfdb36317fe53608db3935dd329c35c3f55a35bdfb0a35abd85b3575685835674bc0355171d63535686134d88c5e34c43dea34a369a7343ac70233e06d7c
  | 6, 6 => 0x49af323749aecf0b49ae952049a16b184952e2354941462b493de9d248d5c85748cbb65d47fc3637477e821d47722ff5476435d84734e63a4724ee6c4700cb0e46e4d62d46ba812f46a2d1704675c8f94617246f45a7f598459ecff74565005f4534a014451f7c0844d3714444a5495d447eeee84454025044171c5a43d1a4874394911f43686f9d434ac03243091b4242e2365142b779a3429d7e914273d9be4272d6fa42670c5a42590cb5424ad53e422278a2420ed6bf41edeb0441e96fc341cdfba641b7825f417e85cc413a622b4130a406411ec8a340c43b94409a484b40901b224087073c3fc0c4623f3be1ca3f19de853ebd5be63e938f913e438e3e
  | 6, 7 => 0x577377cb574207dd5731d72c56fa71c756e35aec55f600d6558ca698557c9ff5550658d854fb57fa54f25555546ec5c4543abce15407fd7253fe39fb53fd228653e68a5953a1ba57534ec578533f497d52b3fe77529a8d7a528c302c527bcb80523d749b522a4a195219ec9451e463f451dbd9b851a6b70151a6b53c518d110e51872e0e50e03eeb506c7ad0502be6504fd937b04f91d4624f1bb8244ee4079c4ebf453b4ead05c84ea88e884e4fbe194df8f18d4dbd72324dbb91724d6f6fcf4d1acf0f4cf40f144cf152134bf409854bdb7b304bc7d61e4bc38b784bb582524b841acd4b7d8f7e4b3c5c5b4b24895f4ab48cbc4a7fb41e4a1426de49efd3cd
  | 6, 8 => 0x630c972063097c7562fe35e162a21d5162a0afc562517acc62511d2362474da362443cd861e8177e6176425e615a47cb6153b34a6118463c60d4f1e160b5bb09609e1391608535a560326b045fc63bae5fac40685f8669bf5f6139d15efae04f5ef19ced5ed6e59b5ec3da555eb9ad2c5e6ca3f25e2f68925df837b25d903ee95d8fa8905d71535d5d576f0c5d4d88645d26770c5cf23e625cde0cce5cbef0b25c7fd1705c1428e35bcc81925b599cb35b3bed485b31cd295ad187dc5aa8a6b95a66dc565a292fbd5a09b24b59a0c2fc59a0445d596304d659254669592313ff5901c7ff58e2513058cf7f79583465bb57f5134d57a686cf57a2ba825796e9b0
  | 6, 9 => 0x7175888370eea42e70866ce9705b5d9f704d5e58700ba7156fa4e6c26f80bd776f21eb256ecfff346db7a48b6d6da1546cdf2d166ca601836c899b716c8086ed6c3e88df6c3d1b7e6be0137f6bcf90f36b43cd8a6aae745d6a77f36a6a63eb3f6a41599e6a30f69969715719696b5a43693cdad369397884692ba2fb68eb1e2568716f406862f30467c32d2c67ad4f1567a7b8ad67854e436764be3e6763e9e5675d052e674ed8ac673394256728889166d0a35666b1e27a6623177d66159959660cf112654b05bf654a77cb652b11a464f1f4576481e479647c796e645af94563f3cb9d63d5284b6378df7f63669d95633b241c6326bdca632407c2631341c8
  | 6, 10 => 0x8107066f80f4c63780d8ca6280bc38198069eaef7fb807ca7f369d637f24c13b7dd0cb7e7d4640047cf1acd57cc7ef177ca8f3cc7c95abe27c347e527c2f9e497c039c0f7bdcd2c17bc1fe837b9228f67b4794bc7b34cd0f7aaf2d897a1c424c79f38a0c79e15a2879e0727979a5b36c7982a2c1796b687f7959c24d791c8705791205e277f6f3be77abf413774e92af772c7d1776d8ef9576b2d3b6765bdd32763eca4a761a168075b7ea5c7592030a7578bdb5756280737540a7b3751113a0750d544474e35f2f74cf39e474a4af0a749699f17495298874202dc4730a5f6972f33bfb729c0386727718da71e302fa71dfcdf671c1199471ae7c9b71acb963
  | 6, 11 => 0x8f818ca58e8f965f8e8df0778e6afd808e4d0a488e0333408da2bbf28d9c69668d8701a48d7e0df58d5eaaf98d051dcd8c9dac058c5f03a98c0d1a1c8bf0530d8be0e7ea8b9c1bae8b5a7bfa8b4da15b8b1537598a81f0ca8a2bb58a897d71ff894068d88934bc8a892ed109890f53db88e0387f888265a58879512187d8300787d2433f86651c0a8663aea9865cbae8864f5914863c3b6886195457860d8df385c9991385a829a4857778ec85732cb6856559dd8564247785353ca28436e17f842ebc3f84129c4083f86e6183c0be09835d8872835cb41983345206832664d7831ab88982edb98b82e1f31882b613c58250cfc081c2fc3481c1d1c681556ecc
  | 6, 12 => 0x9e392f6b9de751349d739f979d72dd149d57d1949d43ff579d0886439cfac2d09cefd78c9cbf5b459b8f302a9b7eee869b7186cd9b1c8b6c9b09f1a29ad7f7b49ac6834a9ac0defe9a92183299e26cdb99af20c799743874993f0a3898602235980162d397ac0d109795c1f99742e10596f3335c96980e6b95d3ea0895559da5951afed794e5463694d8a57994d7782194d5c0b494cc6c8d94ab739f9451f83e9445220093f7644e93ba7c3b939a9e61937d188993104a2b92d1b9c992c480a292ab9dea91eb64cd91e820069190d39c916691a9913815589122717090fd764c90e2f04490dc296390c7041590c0105490b936009082705d8fde7d878fcda59d
  | 6, 13 => 0xb22bdbebb1c3a841b1b6803cb1697430b14765e9b100a780b0d062cab0be9c85b0937381b085d714aff02e82afe25cc3afc9bbddaf7d917daf5e1350aed98fb5ade027dfaddf8c5cad1f97e2ad0897dcaca05a64ac970227ac70ae9eabb766c7ab8bcb77ab7eb3a4aa745c12a9fbfd74a84edc83a83cd88ba78860e0a73ef941a621259fa61c678aa5b54dd7a5ab77aea58d967ca5543e16a53677e3a5019823a4dfb6b9a47ac71da3ffc12ea3dc97b0a3ab4432a35b4fb5a2b69e03a22abb0fa1caad00a11e6ea6a11b2e51a05b43e5a045292fa0206677a0156c74a00263899fd7e9929fa732239f9f6c979f90bc989f7f4b169f339c1d9ee683bf9e65c6a6
  | 6, 14 => 0xc91b2316c83f9268c7ed84edc77f38fbc76b6ab0c73fff91c5158df3c4e6c501c47df851c4230668c4070a2dc3678056c35a3d98c2edb66bc2eb35d8c28c44a4c27b2ff5c24f89c6c2217eaac1ae180bc19593abc15333b6c13e825dc0b42e27c0b25433c03fc5b1c000d47dbfa40e66bf8705ebbf34b798bf1bf8a0beb30907be4be64fbe407366bd8203c1bd3c5e53bcbf7b05bc95ec06bc8a5b6cbc0e36a8bc048cccbb53bf87bab7b3ebb9fd5190b9eab265b9661604b946f1ecb8f18557b8afd059b796ed02b777b8bab759e881b712440fb6d8a086b6a4cf19b5640a2ab5406affb48d7b1eb46ce8cdb4009ee4b3a60999b39a081ab36d65c4b3088cf5
  | 6, 15 => 0xe25c5844e1e8c2bae176c27de175263be1151f08df49fcc4df3c211edeb2d296de72f46ede625519de2d9d58dd5bba69dd4d7873dce2c5e4dc385fccdbf98ad8daa96d91da9cd2d6da787b46da2eb9bad9e37c2dd9af5a0fd9ad9916d9a7967ad968302fd9352887d872797ad7fd5700d7da8571d7ca6921d7783301d6e25d60d6455af1d59092c8d582175ed4413610d3f48989d343e014d282ff82d27d900ad1bcabd4d14f0b2bd1317389d0ff33b1d022f3efcf9ed3cdcf8745bfcf66fe2acf332b40ced891e4cea3b9cfce3d1e94cd786ec8cd0d5f86ccbba923ccacd1edccab1ff8cbfe463fcb2d3d5ccb256f71cb16c110caf5a39dcad172fbca536b4e
  | 6, 16 => 0xfd1d97c3fd1d4291fd0ae226fc529923fbf44d83fb7d0cc8fae73b35fac52187fa7a2939fa746a52fa6bbea2f9fa2e6cf96feb04f954849df8d12158f87556f7f85bf52ff7e9aa22f7271afbf6535463f5e77c9bf55da781f50a4d50f4b2df37f3d6a6a3f1aaee29f19ec62cf10b6452f0f8df95f07e4c7aef46a522ef41536feef3064dee765a3eed467b7aed2ae9e7ecf6acadecbfdc9cec6b46deec53a50dec3f1209ebefca4bebcac5bbebb11d4aeb7a34c6eb4fcf47eb111565ea2e3f68e919e04ae82c56a1e7d1882ae6ee6dd1e6a6de94e53ad0fee539fca5e513ed4ae4f80626e4a65d9ae4713ae3e439dbe3e3af474de32c1983e2f6af66e2e44efb
  | 6, 17 => 0xfecd2018feaaba2dfe142fe9fdc77755
  | 7, 0 => 0x3d4cc4103cf5e0b03ae4e9903abb2f00375c6cf0369e6ec035eb4ec035987fe0355cd5803476202033b05b5033a727c0330c812030a418d02e2d71402e2bc3202dd1e5f02dc927b02d6a72e029f514b029bda2f029aef9e0295a2700294122e028de01e026249d20249a99b0240dc18023f5c5b02363de20219fdf8020b934d01f5db9e01e3cad001cde88101abdea401a5e674019fd767019f361a019c9fad0198403d0191869801794b5f01652a32015fcb3e01521d0b0146c416014268c7012a58400129b755011182d800f5a3d200ea38dd00c4d48b00955441008dd725006fb9d3006c268400481fea003e83f9003b1ab40031a7ea002d875e0029bfef
  | 7, 1 => 0x844bf83081c74db081be466080a8eb7080280eb07f70b8707f1b6d607ed8a3207c038b3079b7e0c0790b29f078b62840787d7a50772bb3e075d246607492140073a22a1072385510711d49e0709752007073daf06c4413d06bb49ae06a8768f068bc39d068a399a067d884b06735b220665520c065dc92d065d568506596465065401810651b5d5064cb80906457cb90638a75e06291d83060f596e060e91e705e9221005c61dd605b43f6005ad2f3405a9e53f0590ddec057ed236057c0b7a056ad819055f0adf0559d199052aa49505169eb00509fa1f04e553f804e37e8404d8394304d32ad804bca65904aaa2b00460888804427d3b042d77d503f1b952
  | 7, 2 => 0xc498d8c0c2ad96d0c232aad0c22507d0c0dba2d0c03b9010bf0d0900bd3d3cb0bb7fee20ba77e000b9beb890b8ad6cc0b88cc090b7f14bf0b5bfccf0b5334f40b41c7720b2912830b29023d0b28f6400b2179b20b1a7d630b09f3650afb5dd30af89e950af23e1b0ae653d70ae34fac0acf09dd0ab8b2690aad79ad0aa0caca0aa03d900a87ffcd0a7a55280a6426b20a5e33fe0a0664f209ee1b6f09ea0c3209bd51ef09a8f0e60989c7c309723fd90966c06b093e73560938390c092d20e8092be94c090dfc840903dbc508f0123c08e4c69e08df973908c7c03908c5dc3f08b46af108b0816608a5e43f0899ab5308739b7008683c450865d84f0856ca26
  | 7, 3 => 0xf808c130f8009980f79f41c0f799f850f77871a0f7093b80f56ffe60f55d8040f53334a0f47a0390f3d84400f3a3da50f21afa70f1c66040f1bfb200f1a8f2b0f16fff20f06017a0ef737100ee7b93a0edf18670ed86b730ed019dd0ec4f4730e90cf7c0e8414b20e7e15130e7dd0190e737a980e67dc250e5d94ed0e4ddd170e39d93f0e1ee4940e05ccb20dfbaa4f0dfb96ef0df565b60df435510df1ea5d0ddd4aa00dcd46f30db9c7830da962390da6941f0d9cbe430d92daa50d7510870d61f2fb0d5a81df0d570f570d49c4170d377cd70d2d22890d2aded90cf439bf0cec37f80cd896110cabde0a0ca165b80c867e660c6d8e9c0c687b0e0c60dcf8
  | 7, 4 => 0x13aad82f13967e2f139302bf138cad00132f4ac71317dd2b12ff424112ddb43412bb814412b8ab4112ae5da312aabf8d12a8595d126ef838125d0b7e124d6d63124888761233466a123247971228cbf912245a68121617f5120061e011d640d011c1f92a11bd50f411af78a8119b91ab118eca21118d0e1d11880f961187183a1160b3bd115e1032115b67ca114c695c1142fa4111408e9a110f8d8e1106ad5710de35ff109bbfbb109410fb108ef5b9108bef5710835d31106ef5981052a2c5104862a5103a99121037e7201015aee71004efa21004221f0ffdfe370ff073950fec104b0fceabe00fcb33c20fb1a7760faa77070f9788b90f8e38f60f889918
  | 7, 5 => 0x17c5c22e17bf920f17bcd81e17b7e34f17a3f1f5179c6b23177154d6175d1cd3175a929b173643a81729918f172938d71712096e16d77b9d16d21d8816b50ee916b01e5416995adb168bc85d1673385e165ce3e9164f38e0164042a2163cc6661612f341160c7aef15f71c1b15f4eac915f022ce15e9498b15d3b4e415cb6ef015ba6e6315b18426158c470e157b3ef615776f951575dcf91561a43a15602014155ed0bb154b39521517feab14e907ff14e2d7e014db292014db18b514c7c3fb14c15aa41499cfe51480f23a1476b36414696ac21461a25714466a841437977c1420fefd1415063f1413d60813fe949713e90d2b13e0e2a713e030a013d6d81d
  | 7, 6 => 0x1b52f3321b504a801b3c1cc21b27d2611b16f5ed1ae9b4a21ac6e6c71a9c7f661a9329761a90e4691a87fcc01a6b63331a548add1a4058c31a33b1c31a2660db1a2594481a21fbf41a1cf3441a13ea6d1a0dc40d1a04d97919ff9c8019fd5caf19fc1ed919f37e0719f2db1c19e5257c19e220af19ddb2d519d2796319c7c79119b1d44819b1c5f519a917ce198eb565198916cb1980bc2919774199196672e119403fcf19399e181921f28d19169d3318ef4baf18e4a1d018e3fb0a18e16a7f18c40ebb18ac994f1891280c18787ffd1862a4c918595dba185955ec183afea7181c7acd181c0a6c18129d1b18103f8818043d6917e4d13d17ddd95917d64a91
  | 7, 7 => 0x1f06a07c1f0286b71ef6cca31ee350081ee07af31edb86661ed94da01ec0fa371eb6c6781ea6aee91ea663541e8c48a51e5ad6651e35b7f71e2d04af1e08e1531e0576261df73f721de177831dbe4d991db574801da019151d9945271d98a19b1d948ff71d85da9b1d85cfcc1d83b5c31d826c881d825b1b1d81c57f1d55e79b1d4a9d981d2d215e1d2a81d31d07cbc61cfd2fc91cbf657e1ca81a3a1ca481c01ca0b1831c8e80241c676f431c5d3d531c5377201c397d011c32bad41c228a231c1ffead1c1c6ec91c0dd5381c0c1b4b1bf5be811bea35011bc210541baf8e761baefe391ba7dc291b9d622f1b9935371b8548e61b78d4bc1b62a5db1b55df54
  | 7, 8 => 0x23a4af752341f140233e519823057c1922ec6a8722d85c9a22c4f10a22baad2d229eb02f22986b962289ec0b22805475227ea68b225693612238f6422219ec0a21e6cbde21dae13221d8db4721ce372521c636b821bde80721a5f96821997fae2177d42821730a3e2161be9a2160b5cc2145ca5920eebdc420eb96a220e970f520e249a720df43cc20d5617920bb659020b0ccc520a84c142089ff20206bd013206a118a2064873a205b0a2a204a7220203ca24720292edb2014c6441fed21a51fecb1011fe29d3b1fd3c25f1fcb8bd31fb72b911fad31dc1fac1ffd1fa939b01fa23c8a1f9874111f87b1c01f5f0d481f47d9851f3e5d811f3d31db1f2ee985
  | 7, 9 => 0x281909f62803ddcb27fd4ed027f9aa2127c3516e27bb223c279f070c27795cd1276fb0f9275d8171275b976e275958f22753b5b42750b4f6273e087b2738adc82713cf002710b40c2707a0fd26eeeb7b26d16b4626d0c80326beaf6f26bb2fef26ad1191269ac23a267c3f2426640762265b05052639a0bd262a32f426146422260a164f2604931525c5c2a225bf78b925afebbc259a313725928460258d7136258a599a256dcb2f25685a9d255fdd5125471fea253ef9ad250aba5724fedf5924ef47cf24dd90d224c9ba2d24bcbbe924ae713a24429b14243971d52437f8a9241b265d2416c07e241577b92409402823e92d1223e6546623bb3be323aa74da
  | 7, 10 => 0x2b19bbf42b0fca262b09ceab2b08f8cc2afe09d52af8e8dd2af68de12ad9fd9b2ac54d632aab8c952a9588c32a95810c2a8c3c9c2a8999b02a73350a2a6f28832a6cf0712a6bc7352a6540552a6347522a5617002a4238582a4014db2a3198e02a2aa3142a222ab329f0b1cd29ed6e3b29da34ba29d4eeb929c478db29b291b729a0874729990f442993998d2992b9322989cbc0297c99f829740e86296b38aa2964176b295678be29366e0829342757292af8b7291d2a9e291385ac2912a74928e5022c28e1d56328d3f68428c73e9828c04ce028bc54b328b1318528a4634428a2086128777069286658d0286028b1285879f1284514cc28233034281a4d9f
  | 7, 11 => 0x2efbd9642ee5e2102ede35262ecd9b512ea523322e9c408b2e8af7a22e8a65942e8108342e7ac5422e5e2aa72e3ae3492df877932df741622dec4b6b2de6358a2dd75a262dbac35e2d98c7d02d93a3d72d90db782d7d41f82d70ced82d6d756d2d618f3b2d5ab92f2d52d1502d4fca342d4f458b2d4b28f82d4518622d3ff5e92d3ea4312d2f16c62d17f6e82d06d0c22cf8cd042cf085992cdf3e6c2cc795ae2cb7e2692c97836b2c8140062c7dc05e2c7afb6d2c611b6b2c58dac22c4642572c42325c2c2937292c18d8712be8c6dd2be239292baf6f8f2badab652b81faf52b81626d2b79d3f12b77b9702b698d6c2b5913022b3e6d342b27b74c2b26d94b
  | 7, 12 => 0x330961a632e16b8932d045d132cae7bc32ba82ac32b9632332a1bcd5329fbf893294f0e0326bf53f3264f194326007a8324417603241705c3228b42331ffed8331f21e3331b603e131b1ab29318b16ac318125c63177ea8831752de7315d27863159aba1315024ba314b726931389c993122199e3118539930eb45fe30ddf49130dba21430d5282030bfbacf30a5e21830762b3f303f34b8303037e9302ca7773028fd26301f3bcc301052cd300601422fed21612fc6445a2fc5bf282fbbf89b2fb1aafd2fb10f502f954dd02f8f1ff32f86b33f2f8141142f7a8db12f74af282f67316b2f48cad42f3594f12f2cdf472f20329b2f1d2f5b2f1abea52f136205
  | 7, 13 => 0x37d8b58137d59bc637a858a737a4666c379c2c9437962c63378f31e83766c8503743a61d36e2575236de7a8736cd76be36cb597836c744ae36b5383e366fa2723669c03b3664870336491d403644f7dd3610c82c360938793601d28435fe022a35f2a55735e7486435d89aaa35bf14c335a0b6f0359f67e7359e211635974020358ad894357ce107357a976d35787e26357193a6353aa3c635169f3a35009d3534f524f934ceb8d134b7456634a771a7349995fb3481cae43481847a347c735e3466ebee3453b6c5343a84db34064f6c33d93c6b33ce134333c3d97933b5489033a0067c339be830338d060c336a01d233511330332a82ad3311d70d330a8e35
  | 7, 14 => 0x3b5dab7f3b4bea9a3b40a23f3b36b9843b33d6c03b1550ef3b1004203b0c2ead3b08dcd23afd7b253af6ada23ae826bb3acf9b4b3acedf3f3ac89c1c3aace7f43a9a85bd3a97b4d03a8b1a653a822ece3a64e63a3a4766343a2d4b643a03d4b139ffcc7c39fa66b039f7e21b39e16a4739de4fb639ddbebc39b5e92239ae44eb39a3264a399f4d1239731d65396f572d395b9cf5394f14203926b9f839234c07390ed69f390153ab38ff95f738facf2638eeefa638ed825b38eb527838e1a69e38da452b38c8629238c6876638c5f53938a80b97389cbe363899ed1838962217388be5c4388012b1387c221638695c3f3866c394383a0cba381fcf143808c782
  | 7, 15 => 0x3f6aee9b3f5aa7ff3f5789763f55675e3f4622693f45ce053f291ad13f227ddf3f0151163ef9b7083ef484683ee746153ee6de3d3ee052543e8cd15e3e791ea93e7091ea3e444aad3e3c0ae43e3a3ac43e2e73473e277fff3e0be7f03e0acfe73de291263dbce7733d9457913d8f565c3d8a3cae3d7dc3333d6d79af3d67d4943d60158c3d5c32c83d2c0f443d2ac1fc3d2562093d1dd8183d0e52963d0b3b903d0124c93cfeefc53cfaa5163cedc83e3ce460d63ce1683c3cda06bb3cd396533cbde0b03cba78eb3c9643853c407f353c38e0113c27f8ae3c26260f3bd6ad1d3bcc8c933bbe60cd3ba7c5f03ba5ac113ba1e58b3b9e4ff53b8aa58d3b795ba0
  | 7, 16 => 0x43c469ce43be7d4943b837ee43a9f8484397d1404389d59343555fb0434f7809434bdc18433f660a433cb82e4329eeaf4325dcc44305883642f2e46442e7b5af42e7ad3142e6e00b42c90b1142bebde742b779a342b451b0429e73194291ffc94270b5be425327d7424d728e424083084214fad1420d2e5641ec4f6f41d387bf4183d887417515864149098f412c1b384110f4a8410d769640fe085a40e8120340c96f0f40af336a40936de140846bf64079f6e6406f21e9405ffdff405e8a73405c8f3d404b301340455b7a4042c3c8403af74d402fc56c4028922d3ff4ef3e3fed881a3feafc213fe60be43fe000373fd62b933f8bb6273f7f6a493f71238c
  | 7, 17 => 0x49226c8f49148db04901a2e248f6c24648f4f2fe48f0ff0048ed4cc248c35a8b48c2d3b648b0ac9d48a6ffde488ad56b4850b42848360ca147e43cbf47bc775947b76ea347a3d5234795ee6d4727debc471a541a471718c447154d3e46f1b31146ed067a46ec901e46df279b46c9322546b112e246a6e54b469461624687df064667f2b7464630554626019546230322460f5a0845f5ff6d45f28fa645e00ffb459774c2457c8acd456daacd4563ccbf4529a6cb4526b408450ea01a44fe769744df840d44d46f7844cd758b44ae84d94486548a446f8a944458f2e544578d0c4455fbcf440913f44408d56743f5039043eb0c0643df582343db6ae443d7832c
  | 7, 18 => 0x4d3fd1c54d3c580d4d2ff4d14d1acf0f4cfd734b4cf6f0224ce8bf224cd6bec54ccdf14b4ca859dc4c8a818c4c7e06e14c7463374c70a3534c46545e4c4491e44c29021d4c1e35cd4c1326ad4bf147df4ba2e5bf4b9f8de54b9665454b93e1974b81ba084b78a3094b77d19c4b6e21e64b6978864b6231954b5eae324b2d583b4b299fee4b2472944b226b904b02825d4aee81944aee73794ad80f2f4ad1055a4acc75434aca3bcf4ac64d7b4aabf4e84a9a544d4a83c1d64a5a47c34a44957f4a4249ab4a3ff2504a20e91b49f3d2f349e579ed49e0f04f49af3f14498effba4987e828496885e54943f32c493ccd6c493c34104939f5304939e1cf492acee9
  | 7, 19 => 0x51e93bed51dd55d151bb2a0f51b5c513519006da5136a9a35133fceb510a33e251099cc650f1eca350ef354250eca9cc50dc89c550b00f9a509f54165096359d507c409650754638506b190f505beeb35059633d50490acd504513215036165a502b2686501f9e51500139404fff2dd54ffcc3574ff9d5294ff820184fc71f074fb50f3e4faafd564fa260824f9d1e774f86a4154f29237a4f135c524f050fd04f0494734ef7acb24ed5e3f64ecc8e064ea817a54e9d19034e9caf7c4e8d54f14e6d16534e5372144e3b68614e3a3a904e2ce2974decf5114de2370b4dd542384dc9c7c04dc8be514dc27b5b4dc0f5744d77b7814d74a6104d5b0f8d4d43a231
  | 7, 20 => 0x5707fb6756f411bd56c5d00a56a94294568d8c7e567ee6cd5672b54a5672a487566430dc564030685600570755f9c36e55d8ab8a557f4cd95548eb3e5530a86c55122fc955067f9c550188a454fdc76d54f251df54e7b9da54de0ffe54c66e2d54b8020854b5735e54b47b9854b25c7054afff1c54acafc454a96c0954a16d3c5459014c54324e155427678854198a3e540a4dbd53f747b753ec72ba53e18f1b53dd4ed053b7436653b2be7253ad163d5377f3e6536a150753185b0d53181bf8531505d8531108a652f5cae352e71d0152e2321e52dbe80452d64d8252ce9ec252a439b5528ce019526177285257aedf52534f94524e709e524a17a8523dc211
  | 7, 21 => 0x5bdee7215bb226b25bb03c075ba3354b5b6b6fdf5b6b678f5b4dbe2c5b34bf745b1f7a795aecd9575abcb8a95aadae925aa52f8d5a9f5dfd5a97a4eb5a9469955a8d74075a8322685a73054d5a6fa4e45a6d6fbe5a6beea55a6afd255a62dc0f5a5bc66559fcbebe59f11cdb59e9114a59b3a05959aeef8f5996f4f5597e76b4597bfa89595c1952593939625936765a5927b4ea591e47e658e6c54658d7b5fd58c55e5b58bad09958b56100588269ee58817b3f5875705b58739c60584e132a583d5a59583019b95817addf5817190657a487195795fc8d578e67bf578c8c39576d478157685cd7576751eb575675b35744b4ce573f8ef45727b7f4571462ac
  | 7, 22 => 0x613fcc2c613f4bb66119d7e1610c35a86108511860f47f6c60c0e6cc60bd229660a44355609eba3e609e4fcb607f1ebe60638fc46058ad0a604fd85a604693fd60205a02601d48af5fce787b5fbe37825fbac6fd5fa8e5035fa001255f871fd25f4d90645ef408b65ef0b1fa5ec5fd9a5ebac33b5eb5ede35e961dbf5e5e95475e56e6485e427dc45e0e53495dfe16575debf6475de083ce5ddb6fc75dd41be55dd08b735da6d4765da6006b5d8bf1475d7d6e2d5d7bf2db5d6dd96d5d65f9355d5fdc975d48a8d45d1e66bc5cea4ee05ce551125cde0cce5cbe4b0e5c9fbd605c9b90375c9649305c91de815c8357335c4918f65c33c1815c1e7f7b5c0bbbc7
  | 7, 23 => 0x678eb54067891a306786b847677701556741623a673f974f67322581672edba16725e9c567240676671066ce66fd841f66fc748866fb4c9166e9390a66e5ae6b669a48866685c7206644c8f86625b9e96617db0a65d6d88f65a826966584a32a657b75cf654dfbc0653364ff651506a4650bdfd764ea33b664c8c42e64bb002464a2048364a0c73f64789948646b28aa643ac4066433ac9f642e54a0641ca4e76413866e640f62e363e50b4763a6a9d363939f33637c7ea663720e7a631fb153630aea4562dfa08f628e144f62256876621bcd566212b35a61f617a361f5a73b61f427ee61de9b7b61d0c2e561ca400861b8723761aa3368617d3f4b6169ffad
  | 7, 24 => 0x6c9c25686c96b4706c8c37936c80921c6c79ed6a6c64553c6c5bf97a6c4b6e046c41d5016c2bf7316c2229556bf899566bf58d8b6be1bd3a6bd931506bcf90f36bcb63fb6bba30316b9d976b6b70d1e96b67104f6b3d4c3a6b1a64bf6b0d63fc6b0959bc6abf8ae76abcdfc56aa508c56a9be0a66a95be0b6a91b37d6a8281de6a7ff6686a610cd96a4f22086a344b406a2068546a13aebb6a08291469edc24469da0c1f69cd7e5369ca649769c0add469b0c44b69b08c9069ac5725694fc71e6909bb466909578d68fc772168ca62fb68ab8c4a687ed5db687b8c9768576a0d683daa90682a0095680cb64d68090f896807b67667eb4a3067d9415267a71cda
  | 7, 25 => 0x71959758718aa31d717f4ee07179360f7166cf87715dd49f70fe4ee070f943ac70f077f170e34a0670d6da3270bb677e70a579f8708b912d7066c393705b5d9f7041bbc2703b0e0870345b60701d07ab701a846e701838506fb3739e6f7090bd6f6f7e696f6a8dfb6f5f82676f4ebd9a6f4c3cf56f43e1be6f1873fa6eed418f6ed8ef9b6ec28c856ebcec996ea4ed216e6dcf996e0d4a906e04f5ec6def4db26dec12c46dcc76296dbfabf96dafa0f16dab2ce86da876da6d916c166d7e78d66d748c516d65318d6d483b2f6d35546a6d2cc71f6d0d54346cfdbf986cf9e7a76ce170276cd6ca796ccc398e6ccc2d286ccacce06cc507e56cc11e926cbace20
  | 7, 26 => 0x76c6508b76c3631076bcdc5b76b871ac769ee490766e04be766c8457765bdd327654909976509acf764e5f61764692e676461d72763744917626fba576109d49760760367601ef8775cfa8b475cf5cc175791c4b756f4a91756b3d6c7554e38675447afa7539d26975364d1d752306507502d39f74ae2b34749998787485a1e97481ccfa74741554746a0e0a744ac9477448134173ffb2f573f993ba739c3b75739a99807393454b736647aa734eaa0d73275b59731a9a37730cc97a72ff2f9d72e9411572b283397295730272739f54726a4e0172301b0f7229b8f672286c4f71ffefc671ff99de71e12dcc71d78ca271c52b6a71c4843571b731cf71a6de3f
  | 7, 27 => 0x7c40fcff7c1bbc077c140d477bff7fac7bfa0c557bf0d3337bc5288a7bbafb617bb2ffa97ba3c0797b86605a7b665f577b5e52fc7b40cbea7aef43a17aea77727adc1f207ad3415f7abeb30b7ab1cd807aa157477a8ef3507a8392537a7f40357a399f0c7a2bf43679ed579e79e15a2879d3e13a79cce61979c219c979bb6d1e79952bdb797234ad79717a8d796deb39795cf9c5795acc8c792b8cc8791c125478e9916b78d1319678ac62e3789257757877b053785b85d17847c1c27812897277d135d077cf9740778424c2777652a777728e4a7768e8a77746c8397744f9e7772c48f47723c8d077231e6a771f39f876f0de3376df94a676d6e32176d00d2c
  | 7, 28 => 0x8220478281f6d6c281e62af881b76e8e81a1c794817106db814d04b7812adf778121dfbc8101e0aa80b8e9d480ab0b5c808b00fd808a241e808528c4807ff039806266ad8042819180381ef17fe516d97fe1a60d7fdefe227fda9b807fd8d7587fd11f437fb866157f8ef2d87f75ea277f75d2d77f65878f7f5f0e0b7f4af1e47f4590c97f2c02b87f172bf77f0df4cc7eff2d3a7ef20d5d7eeb3f2f7eddc2a37edbceae7e9f2c737e704a887e4b07f87e05acff7dffd2af7dfd47397dfb85ac7ddeb6337ddacfa87dd765af7db1e1917da0a7537d7fe0cc7d7d57bc7d3371107cea112d7ca8786f7c79c7f27c69c65e7c4faf817c4c7c107c4bfba17c426081
  | 7, 29 => 0x8826fc39881af3898816e94987e75edb87e6c54587e152af87e088dd87a030ec878be23f876ece5a8752d38b874f9269873abea48733e75f8708035287062e3086d3f20a86be95e986bbbf6886bb689486bad95e869b7594867d4095867726a18672012f86465a8a861a00e9860c78ef85fc244f85f6241e85d3fdb585c32ecb858e52b8857f1b6685644eea855ab552854276918527bd3a85260ae18519787e85184ada84fb0b2c84e9742a84e1769f849e475c847e77b1845f90f7844c64498422cac983e740ff83e4146483b0d4c88362909783621177833df9038323a63b82e1f31882de711782b3ae8082a1ab698295aa1e827963fa82585f9482348b3c
  | 7, 30 => 0x8dcae6568da6f0c78d88441d8d5eaaf98d5c788f8cfeab508cfa91f68cde80148cd916648cd7ccae8cb966468caed4eb8cae17488cad401e8ca442688ca14df68c9ec9328c9a327f8c76bee98c66e23c8c47b39e8b8fda438b7e195e8b4fe1e38b4b91ec8b4b712b8b1fd6d78b0cdb878aef77aa8ac398938ac24ab88abb56b98aa44b2d8aa3b04f8a7994f88a553e488a51c9de8a37c65d8a2ec80d8a01f36a89efee9189ef6b9089e4bd8189d9702089ba9fdf89b6048589b52b5089a86b25899788de895726ae894cf985893fe42c89312aef89211e6a89061e6888f823fd88ede02888e36b1588cd013b88c15bf7888f7ea4885c1c98882e82c9882be4e1
  | 7, 31 => 0x94aba5ca94a8304894a609ff947da14a947012d39419634b93f91dd793f38d2a93e24993938473d69322c34692e04bde92d649fa92d5a09492d3b19e92cd311e92beb26492904ad8928e17b2927fc7e792313082921c7d4492002a6a91f7c8fb91ed9b5991c9a37991b3cbf191aecc4091a73dfd919ac8ae919a80f8918c7c03917adf6f916bb6609147ad6a9117715e9112800b90c788869074f28c906d26119066fa269037307490104b5a8fda83be8fa19e1f8f9fd3cb8f9d1d5f8f7b76b18f74f0a98f6e24048f6057d08f5f11de8f4809be8f20258d8ee20b498ec9b6b38ebf00228eac49d78e9fcbf58e92684e8e7679718e2302ba8e1426838dce939b
  | 7, 32 => 0x9b7a6f559b71352a9b6cf8b59b6512559b4d17b59b34b1219aec1f2b9ae5da449aca79e39ab78fed9aabbbef9a8abc959a88f9d89a8554239a6914bc9a55e6669a18a8839a07492d99f80ac699ef520099ce680e999971879998b674998059c09978ab00997374ef996c23f498e9771598bfc76298a19efa9854b6199848610497d41f8597aa9cac97a00225979895179791a640977488ac976491d0975a043b9736bddf9710a45897012b8496fd835396a2e0f9969aeb7296964552968d4d5f967fbfcb966e46f7965e41ad9630ff519625511595d992d495d4c56f95d27d409566b56d9551aacc954c87d9951cbb3294e56e8494de200194c7ea7294b8834e
  | 7, 33 => 0xa16c4690a1662bafa156d7aba1537f86a1483727a11662b6a0fec4d5a0f04834a0c59c23a0c208bfa09db9cca099d7c2a076800ea05f25a9a0566735a02ef21ba0219339a0178350a0092fe09fd4013c9fada3039fa7e8e29fa2555f9f8732b19f77feb79f726bb59f6868319f5ea4e59f4a44a19f0809ca9efebd529efaea139ec315a79ebfb44d9e75c3909e5f4b7a9e418da49e14ab229e1370af9e0a09409de53f919daae7359da5a5db9d9a91c89d99351f9d1f09df9d0504429d046bd09cf2a1969ce7c5ba9ce0c3739cd8b9f79cccd4969cbb54e09cad2a7e9cab92cf9c86b7d99c32deb99bf3d47a9bde01b99bd198379bca9a899bbf435b9b906021
  | 7, 34 => 0xa828f69ba7fbc882a7ba35d6a7aed748a7966e15a732a1a6a71e49bea6f3a76da6e98352a6bc62c7a69d5214a6910249a68eae9aa685bbbaa66fb308a65ef21ea63c52c1a6193286a5d3bbe5a5c2748aa5b66d6ea5a4ac89a57519cca55beef2a5323c56a51c3a8ba5160ad5a5103ec2a4ef705ca4eede4aa4eb786ea4e8963ea4dede88a4c7accca4c4fe3ba4b188daa4b0cd10a4ae7b11a4a02823a494c22fa4647cd9a434b4b6a4033c3aa3f2435da3ea76e2a3c1ab4ba3913837a38922d9a3814b1aa3744415a32cb193a2cd8bc3a2a97873a29245d0a284b47ea26ac20ea26534afa256c1a0a2487bd3a20c5825a1feca93a1f783b5a1f2e5c7a170cb80
  | 7, 35 => 0xae61e220ae55a6dcae30451bae265fb5ae1bf85dae18ff3dae11518cae064aa9ae018b7aadf1a5e6adec3e13adeaf2e8ade6658dad9c65faad9683faad965e55ad90c81dad788f78ad34d12aad1ad330acf3c449ace974c5aca9b064ac7b9e87ac610a62ac5d1b18ac59c64aac0421faabdf356cabd053b4abcb65acabbd86cdabbaa4f2abb5d1f0ab9f69a8ab7ff0caab75f941ab676f4fab3f45e1aaf5dc2faae6feafaabd8836aaacc2cbaaa935daaa904610aa8df529aa75a9a3aa0116e9aa00aaa3a9f3d131a9cb5f4aa9983258a98e4816a9679bafa9647ee6a8e78fc4a8cb32a4a8c9d8aaa8b83798a8b61457a89d0c9ca85da819a85b062fa84782ef
  | 7, 36 => 0xb5995d73b593ef12b55daf2bb55b444cb512b256b4fc8e64b4e46fecb4bad623b4abe74eb47be621b4520808b43f5990b43ded38b435aab5b432738eb41b0a9db3ff36d3b3f19d82b3c1e194b35f854ab34ae530b33f92c7b325de37b322ff62b2fd0e45b2ad64c6b2a6c045b28d5826b2794cefb1ce22c6b192c005b14c7d40b127beafb0e1dcffb0de38b8b0d5dbb4b0cf1072b09b89e2b08e74bcb03df0bbb0377981b0347cebb0114f0aafaab267afa8260bafa30b23afa1d792af9abc18af80d0deaf79b774af777a6aaf75ff26af73942eaf6b3d75af647c31af3465dfaf332a10aef5af7aaeefd66faeeb3210aedf1679aed6ebcfae9f7f72ae68ce65
  | 7, 37 => 0xbdc979a2bdbc7deebd82ee2abd6e211abd6a8f7fbd3f82f8bcdd2ef2bc87e6edbc7e8f37bc5bcfc9bc545819bc398ae1bc19ed6dbc0c7999bbe3d513bbcc115cbba66d37bae1c4e0badd43f2bad4da24bac49c6dbaa3d292baa1ccbcba701036ba558546ba45dd7fba231cbbba1aa2e5b9fe2647b9e4f0ccb9bbecabb998fee0b9885577b97b0eeab94d1047b93ba479b9349dd0b932cbabb921fd5ab902fcc4b89c56bbb88c0434b85c2f59b84d5911b8405c07b81d78f4b7f92244b7f88c30b7b92ec7b7a667eab793d28db7892a55b78864c3b7694f48b75432adb72e368bb72628a3b71329c5b6c50266b691c424b6855c3db60f96a1b601f9d2b5bed785
  | 7, 38 => 0xc60d321bc5f22483c5dc651bc5c2d3b0c59d6c30c58038e5c54fca04c5368674c52f7576c5275d01c4ba52fcc4b48854c4acd4d8c4949487c46ebe18c46ac8f7c416706bc3e2d77bc3d681efc3b4db41c396a4e7c395a7f7c38b1211c3675414c3651e39c3606443c3347db3c31b6fd9c30e22efc2fcbfd2c2e5ae67c2c56a8ec25c674ac24ddc2ec22701b7c20018d3c1fa1783c1f12b01c1eeb825c1907b16c1871aa2c154e976c13d7091c111313ec0e08b57c0d8bcdabfda4f41bfb4dd66bfb0cba3bf7d00d2bf7afac2bf662c09bf57afedbf47c558bf01fb40befa2055beea5a39bec33186bec0a575be51e5eebe4be64fbe129a87be0ade22bde1cfb5
  | 7, 39 => 0xce95e09dce8ab657ce844c52ce3dbbbecdf98342cdd6b28fcdd3764dcdd2d617cdcd35ebcdb20f90cd4f96bbcd3bc669ccf052c5ccc7daa6ccb4b64fcc9fe01acc994278cc8d2a32cc6d1337cc639849cc396419cc375d6acbd77c2fcbb9f257cbb8063dcb7281a8cb6f5908cb6178aacb5221cfcb51ce3acb46a5f8caebcd8acae6a019cac2eddbca740502ca5f7767ca0e29ffc9f553bac9c52835c996b3b6c96f57afc95c86a1c934441dc8df6e8fc8d8951dc89efc22c86a7b32c837e4b7c82cddd4c7fcec2ec7d402f1c7d3f23bc7bdffc1c75fdf6ac7554d2ec72863d7c71b1099c71007f0c70b1e59c6e5027ac6c77138c682e025c63e6ab8c637c9f1
  | 7, 40 => 0xd735f252d7322c12d70862e2d6f3fc90d68b73c0d67aeb44d6382f23d5dffed2d58ce416d52b0a13d51e93e4d4fb6d4fd47b248cd445852fd41d6596d3dd3852d3ab69cdd3a13996d3980975d3958842d383a931d342c3fbd3152e0bd313e9f1d3039b18d2f3e9f1d2e9db6bd2e063b0d2c6073ad2b422bed2a62dd6d2849381d282c284d27af234d2440c1fd2370a95d2290b9fd222b1abd219e748d1d3f658d1c001f7d1816a5dd1358e44d1293c1cd1145570d0f6d7dfd0e64a54d0dd3a20d0c08da1d08863c9d0325876d028b587cfdba189cfbe62cbcf96c9c3cf84fccdcf83df63cf78f9d1cf6e5413cf66a7efcf1f3ed4cf0b0317cf0a0fabcea2794c
  | 7, 41 => 0xe105ec43e0efeadae0bc3fc9e0b9173ae0932adae04e0661dffa03e8dff6037bdfe045a4dfd12c8bdfb2a488df7206c2df50f4a6df33ac1cdf204264deff409cdee6275bdede789bdec9dac1dea9617cde90f3a7de7f46b1de6a11c7de0187fcddfd151addf155d3dddcc838dd9de376dd53a98ddd4db3aadd420304dc8eb8cfdc374bc4dc16fe65dbac76e7db9d6b3ddb9b701bdb83fe16db5f2a96db5cb9b6db408f8cdb3a67f6db33563adb29872fdb23cb92db15c90ddaf5c757dae9e1fada650bedda60bae0da4ab022da411fa3d9c29a4fd96359b3d9597615d94ad137d8f800a3d89de169d81564fcd80862e0d7a5749ed786c099d783df75d7661623
  | 7, 42 => 0xea81aee3ea58eba1e9f83c15e96ff558e9500fafe878be20e875f0c4e8674cf3e863d8b7e8529c71e816d1b4e7f96942e7b0d071e7978a5be791f698e775de2ae7677190e73f702ce729414be6d0b57ee6118099e606f433e5cc13a1e595ec33e55550d5e52d0e51e506db91e4d154f8e4b5bc3ce4aa967ae491a641e485a5e1e48548d0e45a7bffe44f55b6e3d420a8e3cc7821e3a5ddcee369b96ce35f42cae358b1ffe34effc2e33cbff7e3212e0be30601bae2ff2848e2f02cffe2ef9098e2ee6b60e2e47feae2bb0fede2aad18ce298b8f8e281e22ce277b2dee22a2645e21fca1de1d99749e1b1f408e1808a81e17be059e152e27ee1482590e1283faa
  | 7, 43 => 0xf58f108cf58b144bf5735d60f5277aadf5210d0ef51c5a82f4f3fc00f48bd63cf3c06a7bf389ecdef3828995f3716462f34d8d5cf33b5fd0f33384e5f32330ecf30a602ff2f3ae00f2a6d50af2876c1df2854adff27d326af265106af25014fff1c8b033f17a65ebf1591fd0f12be4b6f10d01a6f0c52c6af0556ec8f0132cb6efedcb45efb37741efaf60deeecf8408ee9ef80aee5bfb02ee1ad78cedf06ad2edd0785cedb71183ed7d44f8ed7c682aed7abd14ed74eae1ed5c23caed56b179ed270113ecbba0bdec2d7d95ec2b22aaec17d5dfebfa8983ebc28ee5eb93c63beb8d81a9eb85b3b1eb6a4ac1eb121e74eb03cd4beae79972eae366f4eabec0cd
  | 7, 44 => 0xffcceadcff8b865fff8b32caff77da54ff6283a0ff0db492feb8db38fe89ee6dfe811e1cfe6aea3ffe69481bfe4d0768fde4e8a1fd1e6eeafd1cf55afd16c02afcf063cefccb4487fca60f23fc86bf18fc78f6f8fc6afe7dfc5d5b9cfc50f767fc465d48fc375910fc151d11fc0b585bfbefb591fbd88733fb89f1edfb599833fb195303fafc002efaf92908fab495f5fa62dbfbfa3689a5fa209713f9b99d75f96feb04f8ff31bdf8d5ce41f8b72109f8aa5a14f886c565f867a20ff84fd4fbf80299a1f7e041b5f7c476a1f77446d5f74120e2f737b16bf6875a6cf683528bf639d07af6281cb5f5c3fe68f5a05a19
  | 8, 0 => 0x15ff8a4715f86a801528ba3c14121a0c13b5da6d136d10ac135211a2131bfefa12b8ab4112ae5da3129997eb12798028124e263511ed84b711eb7ccf11d7480611761aa81142fa411134c934103ead2a0fc22fb60f5c5cfb0edd17080ea68d810df078900d52c9a60d4d98860cf91d9f0cea20e10cc7aa850cb3009d0c867e660bd753a90b41c7720a9628be0a71f9560878675807d82e3c07bd347d07af559e0754ea15075140fd06ecbabd06b07a0306634425064612c705ad2f3405a3eb0a059e8b170590310f05869eb1040745c603e3645402e9d44b0296f5790291d00a01a603fb0198251c0188fb4b0129b75501013f3600dd496a0064991500103def
  | 8, 1 => 0x2b0f56702a7c85282a6bdfc02a5e00e128c04ce02889888f2775450f272770732705880d26d2458e26aa53c326a4b5bf265363bb264ea12126488ebe26396ad4262d41fb25bece64255ffecb2509c4b824cb7b292485a9342429651523afce9223a7fde622543c1c21e9d24d21a5f9682179389d20e970f5204aaf2d2046aaad203e530f203cd04e1fd3d3851f608b651ee4e3db1ebb13731eb3facb1e739d441e7359ed1e3d0e221d989e101bde45011b70b1901b52f3321b2d157f1a5d39541a45ab1d1a4058c31a2bfa9c1a0ece7019e360491979f417196672e1191531f41900f42918e3fb0a183e8305181aa94117d07b0017a820261729918f1606144c
  | 8, 2 => 0x41a4b5d640bb2834405c8f3d4025ca0a3f8b9abe3f49363a3ee6de3d3e277fff3dff89d03df1aaf13dc32c533d8620523d6d0b963d18fbc93d0124c93cd7d7c23c9f3cdf3c9dc2fe3c8fe41f3c3d49423c39fd5e3bf3e2703b3c318a3a8b9b213a861c993a305add39de879e3950034038ad846e3899ed1837a1ed1c378f31e8375fd1e83732d33a3724f45b36ad51603678c0eb363c57f436224d1b361b1af435d89aaa359aee6d357bcd573518dab134746a9f342cdee933d93c6b33193e9a330961a6326a0621317141fd315024ba302ca7772efbd9642eedfa852ea0b9112d770a592d014b912cf3c0ef2cf085992cae27f22ca821632baacaed2b698d6c
  | 8, 3 => 0x53b7a8b55342fdb7531915d15316929452f2fea452943af552942b7251efbb6051d2062b51bb2a0f516924ff515c29195059633d5038abd64fb2394c4f943bc44ec05ebd4e79bd534e5bae794e1db72a4e0e9fc94e00c0ea4de27c5e4dd111674d2b306b4d1acf0f4d17706a4cd8ba054ca60af44bff26be4bf147df4b7591cb4b62f61f4aee73794ac0774d4a6707154a3f78dc4a0d1974499cfa0a499b08ca49226c8f49148db048f889f848f0bd7d48ebd2aa475141bb46e1bded46e149a24696c818465e79d54609964845f6b58445c07cca457c5ed145179a8f44cd758b43cee64d43b9f0a343a9f848433f660a42b779a342815d8a41d9fb7841d622d3
  | 8, 4 => 0x6f3b46226e9f1e276e834bca6e38e6f66e34ebde6ddedbb86ce170276cd622c66bed6d236bd591246bcf90f36bc490ee6b89f08a6b7c11ab6b58c0516b46b4d16b1be3666a0139de69d0a4b0692e70ee6920920f68ff5c7d688d1b55683fb3fc64ffcc4e64cf00c56449b75d640159026379a676633af01163353df463275f156292bf226284e04361f427ee61ca40086129ea2960d158046001a2b65fbac6fd5eebace45ec2fe405ebcebc25dc82fa15d93d62e5d6275f45d3a46645d2e415c5d23bf8f5c9fbd605c91de815c0095e65bff541c5b4388f85a73054d5a437adf59f223e559e9c31b59d66aa05992adb05923c1c65806ebe2567ee6cd55ab6c46
  | 8, 5 => 0x8fe9ad8f8f6680978e7679718e21c9a38d7f04bb8d6fdaea8d3d413a8c8386ea8c76bee98bedc1998b3e939c8ab84b5d89f226db886bb2a5877910e2876b3203872610b887080352869b75948635a6fc862851b985210b03850f030e83d9bb2c83233d808241b059804281917f27d8097ebd26667dd5c4a57dad4e397d33ff317cd372a07c439fcf7c0721267bc86ac17b2b17a17b25f4ae7ae97d0f7a85129f7a2bfc5d79a4d76c78f04d3477f10ba27733bc5377211a3f76db0b2e76bdf4b976b015da764e5f61764692e674f2245d74e1bd6173f60c3a73a4532b7333c42e72e03d9b727daf3d72739f5471fb25a271be65bd70c4152b707cee8d6fa6c90d
  | 8, 6 => 0xb65f3e8fb644e080b47be621b315333eb2f03ccbb2dc7687b2572353b22e7c90b210ca3fb1b17014b18cc501b12375bdb04d71d7b0480e0db038e43cb01ae1b0b00d02d1afebec7daf01b67aadab993dada32de2ac3ab49dac23afedab94b348ab681b8eaaa935daa9cb11c2a98c5b5da9647ee6a8d9852aa6395456a62fa927a5cabbeaa4dede88a36baaf7a141bf77a07b39919ffd08839eab30d29de9f1209d42bc1d9d3508f49d2d50bb9bfcd7929b71391a9a81c9ca9a36658d99bbfbc9997d4564985a34f7984899db97251c9896e3fc359680ac86965f34589603a49895a996be955a089894331b659396353d92ef453392b08ece908ca444906d2611
  | 8, 7 => 0xe32cc12de2f7dbbfe2f6cc76e2f02cffe25263cde21fca1ddf71e0b2dec9aaa0ddd7f9c9dd9de376da0af02ed9ed2281d9b9b7a8d988b69cd90de9d2d7c2c847d7c0c947d69e993fd630e845d56748abd4fb6d4fd2da325bd27a66b2cf6e15b1ceecb93fceeb1ad8cea2794cce8cc780cc0d7bc5ca5eb5a5c9d88a90c8df6e8fc876c3bec7ad77bcc7466283c707ac1ec6398efac4eae2e7c4ac2c82c483e9fec4605fcec3d681efc398766ec37f968dc30bd3fac23de552c21dcfbbc16463c6c1043454bf46884bbef4bb49bef1afedbeb2f988be4f311bbd2744b8bcf5d0c6bcb2dff7bad4da24bab08b31ba477786b9782853b85c2f59b7a3f583b6edc245
  | 8, 8 => 0xff8b32cafc3e0176fabc44b5fab495f5f96feb04f8b72109f7c476a1f762f14af6657479f5493ef0f50771aef33b5fd0f30eb1d1f2854adff1c31697f14d1f92f109fd47efeaeca8ef4adc1aef0e3eb4eeae7dabee22ff53ed71b5aeeca193e2ebc28ee5eb7a065ae9d3bc26e8b54ab1e878be20e606f433e5d4dd4ce575a6eae33582db
  | 9, 0 => 0xdd9de376bad4da24b47be6218ab84b5d2efbd9642eedfa851e7359ed1729918f1606144c1142fa41
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 5, 0 => 0x160000000000012000000000610000000000000160000000000006000000000000f000000000000f0000000000003000000000a1000000000000008000000000000f000000000001600000000000160000000000016000000000000000000000000010000000000016000000000000d0000000002101000000000001200000000000100000000000015000000000000600000001051080000000002100000000000000f00000001051080000000000010000000000001000000000000110000000105108000000000000e
  | 5, 1 => 0x100000000000012000000000001200000001051080000000000016000000000001000000000000100000000000011000000000000f00000000000030000000105108000000000001000000000000100000000000016000000000001000000000000070000000006101000000000a101
  | 6, 0 => 0x21000000010440202000000000e100000000000e102000000480e20000000000000060000000000007000000000000e00000000000010000004806201000000000001000000000000060000000000016000000000000a00000000121000000054480200000000000000d0000020480202000002048020000000520c5200000000000a10100000038062000000000000005000000000000600000000000160000001802200000000000000d00000001051080000000000011000000000001600000000000120000000000008
  | 6, 1 => 0x70000000000012000000000000f00000000000060000010440202000005250020100000534402010000000000007000000000000300000314c4202000000000001000000000000090000003806200000000000000d00000000000070000000000007000000000000d000000000001200000000000030000000000010000000004110100000000000160000000000010000000000001000000000000010000000000005000000000000500000000000120000000000016000000000000e000000000000e0000002802202
  | 6, 2 => 0x6000001044020100000000000160000000012100000000480a2020000000000011000000000001000000028062000000000000016000000004110200000000000160000052041202000000000001100000000021000000051081202000000000000f00000000000150000000000007000000000000700000544402020000000000003000000000000d000000000000d00000000000060000052041200000000000000b0000054480200000000480a2000000000000009000000000000800000000000080000053504201
  | 6, 3 => 0x544c8200000000000001200000000061010000000000006000000000000d000000000000d00000214842020000000000010000000000000200000544802010000000000008000000000001200000000000100000000000001000000000000b00000000000080000000000000000000000e1020000054081202000000000000f0000000000010000000000000500000000000030000000000007000001044020100000000000050000010440202000000000000f000000000000f0000000000007000000000000800000324c8200
  | 6, 4 => 0x1600000000000160000000000007000001044020200000104402000000000000010000000000000700000500c52010000000000003000005448020100000314c42000000000000006000000000000f000000000210200000000021020000052440202000000000000f0000003802200000005404120200000000000080000000000006000000000a10000000000000160000000000008000000480e2020000000000011000000000000e000000000000e00000000021000000000000000000000380a2000000000000007
  | 6, 5 => 0x10440200000000000001100000000000080000000000008000000000001600000425082000000000012102000000000000f000000000000200000000000100000003802200000000000a102000000000000e0000000105108000000000000c000000000e1020000000000012000005108120200000001051080000000000007000000000a102000000000000100000000000070000003802200000000000000200000000000000000054041201000000480220100000028062010000000000012000000480a2020000000000003
  | 6, 6 => 0x7000000380a2020000000105108000000000001600000000000160000000000001000000000001000000000000080000000000010000000000001000000520412010000000000008000000000000f00000314c4202000002148420000000000000160000003802200000000000000d000000000000e000000000000f0000000000000000005344020200000000000120000004806200000000000000e000000000001000000000000110000000000016000000000a102000000380a20200000000000020000052440202
  | 6, 7 => 0x38062000000002802200000000000000600000000000160000021484200000000000210200000000000070000000000010000002148420000000000c410000000000000100000000000012000005444020100000048022000000000000011000000480e2020000003806202000000000000300000544c8201000000000001100000000000160000000012100000000000000e00000038022020000000000011000005244020000000000121000000000002100000000000000c00000000000100000000006101000000000000f
  | 6, 8 => 0xf0000000000005000002048020000000544802010000000000010000000000000500000000000030000052440202000000000000300000544c82000000000000008000000000000500000000000070000052440200000000000000300000000000120000000000012000000000210000000000000030000000000006000000000000d000000000610100000048062000000051081200000001044020000000000061000000000000005000000000000f000000000000f000000000000f00000000000160000054440201
  | 6, 9 => 0x80000000000011000000000001600000000000010000000000010000000000a1000000052041202000000000001000000000061020000000000003000000000e100000000000001600000000000120000000000009000000000001600000000000000000000000006000000480e20100000000000030000051081202000000000000c000000000000800000510812000000000000012000000480a2020000000000000000000000610200000534402000000000000006000000000000600000000000120000000000010
  | 6, 10 => 0x500000000000080000054440200000000480e20200000038062000000000000003000000280620000000534402020000000000008000000010510800000048022000000003806202000000000001000000000000060000000000011000000000000f000000000000e00000000000150000053109200000000000000f000000480a200000000000e1020000000000000000000000000f00000000000080000003806202000000000000e00000510812020000000000006000005210d2000000000002102000000000000a
  | 6, 11 => 0xa1010000000000016000000000000700000000000050000000000003000000000e100000000000000200000000000150000003802202000000000610100000000000000000000000016000000000001200000204802000000000000016000000000000f000000180220000000000000020000000000003000000000001000000000000070000000000008000000000000200000534402000000000000010000000000000800000000000010000002806202000000000000b000000000a102000000000000f
  | 6, 12 => 0xe000005204120200000000401000000054440200000000010d10000000000000000000003802201000000000000a000005204120200000000000080000020480202000000000000000000000021000000020480201000000000210000000544c42000000004802200000000000000600000000000080000002806202000000000000f0000000000006000000000000200000544802010000000000010000000000000f000000280220100000000000060000000000007000000000001500000520412020000000000010
  | 6, 13 => 0x314c4201000000000000000000000811010000000002101000000380620200000048062000000000000004000000000000e0000002806200000000480e20100000544802000000000000000000000000000d000000001210200000000021000000020480200000000000000c000000000610000000000000020000000000011000000000001000000028022000000000040101000000000a102000000000000e000000480a2010000000000007000000000000f0000000000003000000380620100000048062020000000000005
  | 6, 14 => 0x40000000000003000000000001000000000000160000000000012000000000000d000000280620000000000000080000054440201000000000000b0000000002102000000000000800000000000100000003802201000000000000f0000000006102000000000000000000000c81010000000000004000000000000b0000000105108000000000000800000000000070000000000007000005448020000000000000030000000000010000000000000000000000000160000000000010000000000000a000000480a201
  | 6, 15 => 0x6000000000001600000520412020000051081202000000000000f000000000000800000544c820000000000021000000000000004000000000001200000500c520000000038022020000000000007000000000a1000000000000012000000000001600000000000060000000000003000000000000e00000544c420100000000000100000004802202000005308120100000048062020000000000010000000000001200000048062020000052041200000000000000d000005210d20000000000000100000000006101
  | 6, 16 => 0xa102000000000001000000000000080000000000007000000000000f0000000000006000000000a100000000000000700000000000160000000000006000000000001000000000000110000000000007000000000000700000000000070000010440200000005344020100000500c5200000000000000e00000204802000000000000000000000000001200000018022000000000002102000001044020100000000061020000000000007000005204120000000510812010000000104102000000000e1020000051081200
  | 6, 17 => 0xf00000000000120000052041200000000000000c0000000000008000005210d20100000000000030000000000010000000000000800000000000010000000000007000000000000600000000000070000002802201000000000000c00000000061000000000000016000000000e10000000000000100000000000016000000010d10000000000000100000000000008000000000000700000000000050000000105108000005444020100000000000070000000000012000000380a20100000000000060000000002101
  | 6, 18 => 0x52500200000000000210100000000000040000000000010000000280620200000000061000000052041202000000000000f00000001051080000000000007000005244020000000000801020000053440202000000000000c000000000000600000204802020000000000016000000380a2000000000000007000000000000300000000021020000000000002000000000001000000000000070000000105108000000000000e000000000001000000214842000000001802202000000000000300000000000100000000000009
  | 6, 19 => 0x7000000000000700000000000060000000006100000000000000e00000000000000000000000012000000000000f0000000000012000000280620100000000000080000053504201000000000000700000000000030000000000009000000000001100000000000100000051081200000005344020100000000000000000000000011000000010d104000000000e101000005444020200000000000100000051081200000000000000c000000000001500000000000060000000000012000000380a2000000000000011
  | 6, 20 => 0x610200000000000160000010440200000000000001200000500c5200000000480e2010000000012100000000000000000000544c420200000000c11160000000000006000000480a20000000048022020000000000010000000480220200000204802010000000000010000000000000a00000000000100000000000016000000000000300000000000110000020480202000000000000700000000000080000002802202000000000000700000000000160000001802202000000000001000000510812010000003806201
  | 6, 21 => 0x12000000000000f0000000000002000000000001000000214842000000000000007000004250820000000000000070000054440200000000000000a0000000000016000002048020200000038062000000004802200000000000000000000000000000000000002100000000000000d000000000000f000000000001200000000000070000041504201000000008110200000000021000000000000010000000000a1000000000000010000005210d2020000000000006000005304120000000000000030000000006102
  | 6, 22 => 0xb0000000000010000000000000600000204802020000000002100000000000001000000018022020000000000007000000000000300000000000060000053504200000005204120200000000000000000000000012000000000001000000524402000000002802201000000000000300000000000030000010440200000000000000800000000000160000000000006000000000000d000000000000300000000000110000000000002000000000610200000544c420000000000000080000010440202000000480a200
  | 6, 23 => 0x21010000000000010000000480e2020000000000009000001044020000000544c420200000000000100000000000006000005444020000000000000120000000006100000000000001600000000000100000000000010000000000000000000000000080000000000016000000000001000000000000070000000000016000000000001000000028062000000000000012000000000000600000510812000000054480200000000000000300000048062000000000002101000000000001600000000000080000000105107
  | 6, 24 => 0x9000000280620000000510812020000000000007000000000001500000000000100000000000016000000000000f0000000000006000000000000900000500c5200000005204120000000524402020000000105108000000380220100000000000110000000002100000000008010200000540812010000000000006000000000000600000000000080000000000012000000380a20100000000000110000000000016000000000000600000000000060000000000006000000000a10000000000000060000000000016
  | 6, 25 => 0x300000000000120000000105108000000000000300000000000070000000000006000000000a10200000000000160000000002100000000000000b00000000000160000000000011000000280220100000000000060000052041201000005244020000000000000100000000000010000005204120000000000000100000000000008000000000000800000000000080000000000016000000000a1010000001802201000004150420000000544c82000000000000007000000000001600000001041000000000000009
  | 6, 26 => 0x1500000000000160000000000009000000480e2020000000000012000000000001000000000000110000000000010000000000001600000038062010000000006100000000000a10000000048062000000000000003000000000000e0000000000003000000000000900000000000120000000000001000000000001000000000000000000000000015000000000000f000000000001600000324c82010000052440201000000010d10400000540812020000000000010000000000000300000000000080000000000010
  | 6, 27 => 0x600000000000070000000000007000000000000300000000000060000000000006000000000000700000000000100000000000016000000000610200000000000120000000000006000000000001600000000c11160000000000010000000000000300000000000070000000000012000000000000f0000000000007000000000001000000000000070000053440201000000000000600000000000080000000006101000000380a2000000000000016000000000e100000000000001600000000000100000000000007
  | 6, 28 => 0x4802200000000010d1040000000000015000000000000f000000000000800000001051080000000000002000000000001600000000000110000000000007000000000000600000000000070000000000001000000000001000000000000100000000000016000000000000700000520412020000000000008000000000610000000530812000000000000010000000000e10100000000000100000000000003000000000000700000000000100000000000016000000000000f000000280620000000000000070000000000008
  | 6, 29 => 0xf0000002802202000000000001000000000000100000000000001000000000000f000005344020000000000000100000000000016000005204120000000544c42000000000000002000000000001000000000000120000000002101000000000001600000000000030000002806202000000000000f000000000000800000000000030000000000006000000000001000000000c111600000018022000000002806202000000000000300000018022000000054440200000000000001600000000000120000051081202
  | 6, 30 => 0x7000000000001200000000000070000002806202000000000000700000000000120000053440201000000000001100000000000100000000000010000000000210200000000000100000000000006000000000001200000000000070000000000003000000000000600000000000060000000002102000005210d20200000000000050000000002102000000010d105000005210d20200000000000100000000000008000000000000300000000000030000000000010000000480a20000000000000060000000000003
  | 6, 31 => 0x15000000000000f000000010d10400000000000060000000000006000000000000100000000000100000000000012000000480620000000000000000000000000010000000000000f000000000001000000000000080000020480202000000000610000000000000110000000000010000000000000600000204802020000000002102000000000000a0000000000010000000000001000000000000080000000000012000000280220200000000000080000053041200000000000000800000000000070000000000010
  | 6, 32 => 0xe100000000000000800000000000120000000000007000000000000300000000c11160000020480202000000008010200000000021020000001802202000000000000300000000000060000052041202000000000a100000000000000800000000061020000000000016000000000001000000000000110000002802200000000000001000000000000100000000000007000000000001600000000000060000051081202000005210d20200000000000120000052440202000000000001100000000000080000000000010
  | 6, 33 => 0x1200000000000120000000000010000000000000700000000000070000000000010000002048020000000000000160000000000008000000000001000000018022000000000000011000005404120000000000000120000000000010000000000000700000000000100000000000003000000000000300000000000060000000000004000000000000700000000801020000000000010000000480e2010000000000007000000000001000000000061020000000000008000000000000600000000000070000000000008
  | 6, 34 => 0x6100000000000001000000000000030000000000016
  | 7, 0 => 0x300000001011010000000000012000000000e10200000000000080000000012100000000000210200000000c510000000000000040000000000006000000000000200000000c1102000000380a20100000000801020000000000002000000000210000000000000060000000000002000000000000200000000000020000000002100000000000a10000000000021000000000000003000000000000f00000000401000000000000012000000000000600000000c910100000000000110000002802201000000000000f
  | 7, 1 => 0x61020000000000003000000008410000000000000040000000000004000000004110000000524402010000000012100000000000210000000000000020000000000000000000000000100000000000070000003802201000000008410200000001041020000000000002000000000e1020000000000012000000280620200000000000010000000000003000000000a10000000000000120000000000012000000010d101000000000000500000000000120000000002102000000000001200000524402020000000000011
  | 7, 2 => 0x12000000480220000000520c5200000000000000400000000021010000010440201000000000000f000000000a1010000000000007000000000000200000000121000000000000016000000000a102000000000e10000000048062020000000000002000005204120100000000000100000000000007000000008110000000000000100000000000012000000000a100000000000000b0000000000002000000000000100000000411000000002802200000000000610200000000000050000000000002
  | 7, 3 => 0xa1010000000006101000000000a1020000000040100000000000000a000000000000600000000000160000000012101000000000a100000000000a102000000000610100000000c51000000054440200000000000000200000000000000000000000007000000000000f000005108120200000001051020000000081101000000000001600000000c81000000000000007000000001210100000000061000000000000005000000010810100000000000100000000000003000000010110200000000000130000000000007
  | 7, 4 => 0xa100000000008110100000028062010000000000003000000000e100000000000a10000000000021010000000105102000000000e10200000000061000000000002101000000000610000000000811020000000000007000000010110000000544802010000000000005000000000000100000000000070000000000010000000000000a00000000021000000000002100000000000e10100000000000080000000105101000005108120200000000000100000000000002000005108120100000000021000000000000001
  | 7, 5 => 0x5000000000610200000018022020000000040101000000000000e000000000000400000000000060000000000006000005204120200000000000050000000000003000000000000200000000401010000000006100000000000001000000520412020000000006102000000000a10100000000000080000020480200000000000e10100000000000010000000000005000000000000000000000121020000000000005000000000000800000000000040000000002101000000000000500000018022000000000000001
  | 7, 6 => 0x61020000000000004000000000e101000000008410000000000c0100000000000e10000000001051010000000006102000000000000000000000811020000000000009000000010510200000000c9101000000000000300000000000030000000000010000000000a100000000004010100000038062010000000000015000000000000800000000000020000000108102000000000000500000000000110000000000000000000000a102000000008010000000000061010000004806201000000380620000000000c4100
  | 7, 7 => 0x210000000000000100000000081100000000000e102000000000000700000018022010000000000007000000000001000000000000070000000000003000000000a10100000001051000000054480201000000000000000000000000160000000000006000000001210100000000021000000000040101000000000000700000000000140000000000004000000000e102000000000000800000000121000000000000007000000000210000000000851010000000080101000000004010100000000401000000000000009
  | 7, 8 => 0xa10000000000021010000000000003000000000a10000000000000000000000000010000002048020200000000000100000000002100000000000610200000018022020000021484200000000000a10100000000000090000000000003000000000a102000000000000b000000000000c0000000000008000000000000200000001051000000000000002000000000000000000000000000000020480201000000000000a000000000610100000000000120000000000001000000000a1000000000000006000000000000f
  | 7, 9 => 0x1802201000000000a1020000052041201000000000000100000000000030000000002102000000010d1010000002802202000000380620000000000000020000000000001000000000610200000048022010000000000006000000000000100000000411020000000000004000000000000500000000000060000000000000000000000000d00000001091010000002806201000000004010000000000121000000003802200000000008010100000000000010000000000005000000000000100000000000070000000000006
  | 7, 10 => 0x480220200000000000070000000000007000000000000200000000000010000051081201000000000a100000000000000300000000000100000000000016000000010d1010000002802201000000000a10200000028022020000000000002000000480a202000000001210100000000000040000000105102000000000000c00000000801000000000080101000000000000f000000000a10000000000000000000000002100000000000000000000000000080000000000004000000000000f00000000000100000000000008
  | 7, 11 => 0x3802201000000001210200000544402020000004802202000000000e102000000000a1000000000081102000000000000600000000000070000053041201000000010010000000000000000000000000003000000001210000000000021020000000002102000000000e10100000534402010000000002102000000001210200000000000100000000000001000000380a20200000000000160000000006100000000380a20100000000c81010000000000010000000010410000000000c910200000038022020000000000016
  | 7, 12 => 0x84101000000000a102000000000210200000000000070000000000012000000480a200000005444020200000000061010000000100100000000008410000000000000050000000000000000000000000400000000000030000000000002000000000210000000000000160000054041200000000000000b00000000000000000000000016000000000000e00000204802000000000002102000000000000c0000000000006000000000000700000000000100000000000010000000000001200000018022000000000000016
  | 7, 13 => 0x2100000000000a102000000000a100000000000a10000000000000100000000012101000000000000700000000000080000000002102000000000000200000000000010000000000012000000010d10200000000000010000000000011000000000e100000000000000300000000000070000000105102000000000000500000000c41000000000000005000000000000500000000061020000000000000000000000001200000000c8100000000000000500000001051000000000000016000000000a1000000000000012
  | 7, 14 => 0x12100000000000000800000000811010000000000013000000000e102000000000000c000000000000300000000121020000000000012000000008510100000000000000000000006101000000008110100000000000160000000002100000000000000300000000000060000000000007000000000000400000000000030000000006101000000000a102000000000e1020000000000001000000001210000000000061020000000084101000000000610000000000000060000000000003
  | 7, 15 => 0x401000000000000001000000000000500000000000120000000085102000000000001600000000000070000000000016000000008010000000000000060000000006101000000001210200000000021010000000000007000000001210200000000c51000000000000003000000000000b0000000000010000000000000800000000c51020000000000001000000000000f000000000210000000000000070000000000011000000000000300000000061000000000000004000000008010000000000021020000000000007
  | 7, 16 => 0x3000000000610000000000000160000000109100000000000001000000000000000000000000004000000000000f0000054480201000000000000600000214842000000000000010000000010810000000000061020000000000001000000000e10100000000000100000000000016000000480a20000000000000020000000000006000000000a101000000000000300000000021000000000000010000000000000700000000000060000000006102000000000000d000000000610100000000000060000000109101
  | 7, 17 => 0x8000000000000e00000000000010000000000004000000000000000000000401020000000000010000000000210100000000000030000000080101000000000e10100000000411020000000000004000000000000800000000000030000000081100000000000a100000000000000500000214842020000000000005000000000000b000000000001600000000021000000000000010000000000a10000000000000030000000000000000000000001500000000000040000000000012000000001210000000000c0100
  | 7, 18 => 0x2102000000000000400000000000060000000000007000000000000700000000021010000000000012000000000000b00000000000070000000105102000000280620200000544802010000000084100000000000000200000000000050000000000005000000010810200000000000160000000006100000000000a102000000000000400000000000020000000000006000000000000700000000801020000000000004000000000000600000000061010000000000001000000000210100000000000060000000000003
  | 7, 19 => 0x1000000000a100000000000000600000520412000000000000003000000000000b000000000000a000000000a1010000000000012000000000000700000000000060000000084101000000000a1020000000006101000000001210100000000000080000000006102000000000a10100000000000000000000012100000000000000100000000000020000000002102000000008010000000028062010000000000000000000000001200000000c11000000001802202000000000210200000000000010000000012100
  | 7, 20 => 0x60000000105102000000000000f00000000000060000003806201000000000000400000001041000000000000004000000000a101000000000000b0000000000000000001044020000000000000160000000000002000000000000500000000000050000000000008000002048020100000204802020000000040101000000000000000000000801020000000084101000000000000e000000010d100000000010d100000000180220100000000061020000001802202000000480620200000000000100000000105100
  | 7, 21 => 0x610000000000021010000053440200000000010d1020000000000005000000001210100000000000040000000000008000000000210000000001051010000000000003000005344020100000000c910200000000021000000000000003000000000610200000000801010000000000008000000000a1000000000000004000000000e101000000000000700000000000060000000000002000000000000700000000000020000000000000000000000e1010000000000007000000000001200000000000030000000000016
  | 7, 22 => 0x30000000006102000000000000100000000c910200000000000010000000000002000000000a1020000000000003000000004010200000000021000000000084102000000000a101000000000e10200000000000020000000000006000000000000700000000000080000000000007000000000210100000000000020000000000000000000000000000000000000060000000000003000000000210000000000000000000000000003000000000a1000000000000001000000000000200000000000060000000109101
  | 7, 23 => 0xc4100000000000a10200000000000160000000006102000000000610000000000000060000000012100000000000000d0000052041202000000010d100000000000a10000000000000070000000000003000001044020100000000000080000000002101000000000000400000000021000000000000006000000000a100000000000210100000000000030000000000016000000010510200000000000110000000000007000000000001000000000061000000000101101000000000000f00000000000160000000000001
  | 7, 24 => 0x1200000104402020000000000005000000000000000000000000000000000000012000000000000f000000000a10100000001041020000000012100000000480220100000000000000000000105101000000000000100000520412010000000012102000000000e1010000000000003000000000000600000534402010000000000003000005444020200000000000020000000109100000000000000e00000000c4101000000000000d00000000061020000053440202000000000610200000104402020000000085102
  | 7, 25 => 0xe100000000000000600000000021000000000002102000000000001600000000000130000000012101000000000000100000000061010000000000006000000000a1000000000000000000000000000800000000121010000000040101000000000000600000214842000000000000006000000000000300000000c510100000000000100000000000001000002048020000000000000070000000000002000000000a102000005444020100000000000030000000040102000000000210000000000061020000000000009
  | 7, 26 => 0x200000000000040000000006102000000000e10200000000021000000000006102000000000000600000000061000000000000000000000000001100000000c51010000000000016000000000000000000000000030000000000005000000000a10100000000021000000000000005000000004110000000000000010000000000003000000000000400000000000100000000000012000000000000300000028062010000000000007000000480620000000000061010000000000000000000000a102
  | 7, 27 => 0x214842020000000000010000000000001000000000401020000000002101000000000210000000000000000000000000016000000000e1010000000000007000000000000500000000000060000000000000000000000000300000214842010000000080100000000380620100000104402000000000000006000000000000f000000000000300000001051010000000000000000000008510200000000000000000000012102000000000000200000524402000000000105100000000000001000000000000070000000002102
  | 7, 28 => 0xc5100000000000001600000000841020000000040100000000000000400000000000020000000000009000000000210000000000000120000000000002000000000000600000000801020000000000015000000000000d00000000c0102000000000a102000000000000f0000000000001000000000000e000000008010200000000021020000003802202000000000a1000000000000016000000000000500000001091000000000006100000000000000500000000c51010000000006102000000000000e0000052440201
  | 7, 29 => 0xf00000000841020000000000010000000000000200000000401000000000000012000000000a10100000000c510000000000000030000000084100000000000610100000000c91000000000080102000000000a100000005108120000000544402010000000000008000000000000100000000000060000052440201000000000a1000000000084102000000010d100000000000a1020000000000010000000000a100000000010d10100000000000000000000000007000000000000600000000000080000000000006
  | 7, 30 => 0x524402020000000002102000000000000d0000000000003000002048020000000000000160000000000011000000010910000000000000000000000000010000000010d10200000000000120000000002100000000000001000000000000080000000000006000000000e100000000000000d000005210d201000000000000d000000000000100000000000070000000000003000000000000700000028022000000000012102000000010910000000524402020000000000008000000000000300000000021000000000040102
  | 7, 31 => 0x2102000000000e1020000000012102000000000000000000000121010000000000002000000000000800000214842000000052041201000000000000100000000000020000000000006000000000610000000000000060000000000009000000000000800000001051010000004802201000000000000600000000021020000000012101000000010d100000005210d20200000000000070000000006100000000010810200000000061000000000085100000000008110100000000000050000000002102000000000000d
  | 7, 32 => 0x40100000000000000b000000000e100000000000a10100000000061000000000000000000000000000600000000000120000000000011000005108120200000000000080000000002101000000000a101000000000a101000000000a10100000000061010000000006102000000000000800000000851020000000000015000000480a20000000000000100000000000010000000000000700000000000000000000000016000000000000d0000000000007000000000001000000510812010000054440201000000000e102
  | 7, 33 => 0x50000000080100000000000000400000000061010000000000008000000000000100000000000060000000000004000000000e1010000000000000000000000e101000000000000500000000061020000000000010000000000001100000000021000000000000001000000000a100000000010d1020000000000000000000000000000000000c5100000000010d1020000000006102000000010d1010000000000002000000000e10200000000121010000000002101000000000210000000000000160000000000002
  | 7, 34 => 0x160000000000004000000000e1020000000000009000000000a1020000000000002000000000001200000000000020000000000001000000000000400000000000010000000000007000000000e1000000000000002000000000000200000000000070000000000007000000000000800000000061020000000000000000000000000f000000000000600000000000160000000000012000000000000d00000000c0101000000000e1010000000000002000000000000300000000851000000000000002000000000a102
  | 7, 35 => 0xa101000000000a1020000000000010000000000001400000000c010200000000000080000000000005000000008410000000000000060000000000016000000000000b000000010d1000000000000009000000000000400000000061010000000000010000000000001200000000000030000000000002000000000a100000000000a100000000000a1020000000000008000000000210100000104402010000000002100000001044020200000000000020000000002101000000000001600000000000040000000006102
  | 7, 36 => 0x3000000000e1000000000041101000000008010200000000061000000000101100000000010d1010000000006100000000000a1000000000000005000000000000000000000000100000000006100000000000210000000000401010000000000010000000000000600000000000050000000000006000000001210200000000000020000000000001000000010d102000000000000400000000000080000000000004000000000001600000000000060000000000006000000000001500000000000060000000012102
  | 7, 37 => 0xa1020000000000007000000380a201000000000000000000000061020000000000008000000000000500000000021000000000000000000000000000500000000000080000000000003000000000000200000000021010000000000004000000000000500000000000080000000000003000000000000100000000121000000000000008000000000000d000000000e100000000000001200000000000160000000000002000000000000600000000000020000000000008000000000001600000000000060000000000016
  | 7, 38 => 0xe0000021484201000000000a1000000021484202000000008410000000000000030000000084100000000000e10000000000000160000000000008000000008110200000000021020000000000003000000008410200000000061010000000006101000000000000f000000480a202000000000000c0000000002101000000000001200000000000100000000006100000000000a10100000104402020000000080101000000000000300000001051000000000006100000000000000100000000000100000000000005
  | 7, 39 => 0x5344020200000000000070000000105100000000000a10000000000121000000000006102000000000000f00000000000030000000041100000000000a10000000000000070000000000004000000000e1010000000000008000000000a102000000000000300000000000070000000002101000000000001600000000401000000000000000000000480e200000000000000800000000c9106000000000000000000000401000000000000001000000000a102000000000000f000000000000300000000061020000000100101
  | 7, 40 => 0x2048020200000000021020000000000004000000008410200000000c1101000000000610100000000061010000000006101000000000610100000001041010000000002102000000000000700000524402010000052440202000000000000600000000000030000000084102000000000000e0000000000010000000000000100000000000040000000012102000000000a102000000280220200000000000040000000000016000000010910000000000000100000000002102000000000000f00000000000070000000000008
  | 7, 41 => 0x100000000000001000000000a1000000000000010000000000000b0000000002100000000000000c0000000040100000000000610000000000000120000000000001000000000000800000000000030000000000000000000000a1020000000000003000000000000200000000000120000000000003000000000000700000104402000000000000016000000000001100000000000120000000000004000000000001200000000000160000000000000000000000e100000000480a20000000000061010000000000002
  | 7, 42 => 0xa1000000000000011000000000000600000000021020000000000002000000000000400000000c110100000000121010000000000012000000000000000000000000110000000000016000005108120100000000021020000051081202000000000a10100000000021020000000000001000000000e102000000000001000000000000140000000000002000000000000d000000008110200000000000080000000000010000000008410100000000000160000000000012000000000a100000000000a1000000000000012
  | 7, 43 => 0x300000544402010000000000008000000000000200000000121000000000000012000000000000a000000000001600000000411020000000000000000000000000000000000000160000000006100000000000000700000000061000000000006102000000010d102000000280620200000000000020000000000016000000004010200000000000060000000000000000000010d102000000000000f000000000001000000000c1100000000000000300000000000000000000000005000000000e1020000000080100
  | 7, 44 => 0x2102000000000e1000000000000003000000000a1020000000006100000000000a1000000000000008000000000000f0000002806201000000008010200000000000080000000000008000005244020200000000000060000000000016000000000a1000000004806202000000000000d0000000041100000000000000e000000000a100000000000a100000000000000600000000061010000000000008000000000000e00000000061020000054480201000000000000400000028022000000000105100000000000000c
  | 7, 45 => 0x100000000000001000000000000f000000000000e000000480a20100000000000060000000000000000000000610200000000c9101000000000001000000000c910000000000000160000000000001000000000000d000000000610100000000000060000000000003000000380a200000000008010000000000000010000000000000000000000210200000000000080000000000002000000000610100000028062020000054041202000000000000f0000000084100000000000000400000000000060000000000003
  | 7, 46 => 0x70000000000005000000000000300000000000100000000000016000000380a2020000000000005000000000610200000000000100000000000010000000480e201000000000001000000000851010000000006102000000000000f00000000061000000000000002000000000000800000000c91010000000000007000000000001200000000000010000000000010000000000000000000000000000000000012100000000480620200000000c11000000000000008000000000001600000524402000000000000003
  | 7, 47 => 0x10000000000000300000000000050000000000007000000000a100000000010d1000000000101101000000001210000000000801000000000000010000000480e20200000000000060000000000001000000000001200000520412010000000081102000000000000200000000000040000000000003000000380a201000000480a202000000000e102000000000000f000000000001200000530812000000000000008000000000000f000000000a1020000000000007000000000000600000000000070000000000010
  | 7, 48 => 0xa1000000000000003000000010510000000000000030000000000003000000000000a00000000021010000000000003000000000210000000000000020000000012101000000000001000000000000160000000002101000000000000f000000000000c00000000000080000000002102000000000000600000000000060000000084101000000000000600000000000160000000000007000000000001000000048062000000052041202000000000a1020000000108101000000000000f00000000000070000000000002
  | 7, 49 => 0x40000000012100000000000001200000000000070000000041101000000000001200000000000100000000000010000000380220000000000121000000000000011000000000a1000000000000016000000000a102000000000000d000000000000000000000061010000000002102000000000001200000000c01010000000006101000000000e10000000000c41000000000012100000000008010100000000000100000000006100000000000610000000000c1101000000000000800000000000160000000000010
  | 7, 50 => 0xa10000000000121000000000000005000000000000600000000c510000000000000040000000000007000000000000800000001011020000000000010000000000000f0000000000011000000001210100000000000050000000006100000000000000f000000000000200000000000080000000000003000000000000e0000000000016000000000a10200000000000030000000000001000000000000200000000401020000000000007000000000a101000000000000d00000510812000000000000010000000000a101
  | 7, 51 => 0x2102000000000e102000000000610200000000000040000000000004000000000610000000000000080000000000007000000000000300000000061000000000000008000000000000200000028022000000000006101000000000001200000000061000000000000003000000000000f000000000000600000000000030000000000003000000010410000000000851010000000000001000000000a102000000000001600000000000120000000000000000000000000f00000000000000000000000002000000000e101
  | 7, 52 => 0x80000000000008000000000a102000000000001600000000000100000000006102000000000001200000000000160000003806200000000010110000000000121000000000000004000000001210000000000c0100000000000000800000000801020000000000011000000004110200000000c51010000000000002000000000000f000000000e102000000000000600000038022020000000002102000000000000800000000061020000000000006000000000e101000000000000000000000000060000000000002
  | 7, 53 => 0x28062010000000000008000000000000e000000280620200000000000020000000000005000000000a10200000000000000000000000016000000000000100000000c910000000000000000000000000002000000000000f000000000001600000000000020000000012100000000001210100000000000030000000000003000005448020100000000000010000000080102000000000000800000000c510000000000061020000000000012000000000e10100000000000110000000000008000000000a1020000004806201
  | 7, 54 => 0x48062020000003802200000000000000000000000121010000000000008000000000000300000000000060000000000005000000000a100000000000000600000000c8100000000000610200000000000030000000000006000000000001600000000000100000000081101000000000000200000000000160000000012102000000010510200000000000000000000012102000000000001200000000000070000000000012000000000000900000000000010000000002100000000000000b000000000e1010000000000010
  | 7, 55 => 0xf0000000000002000000000210200000000021020000000085102000000000a10100000000c4101000000000000700000000000070000000000006000000000610200000000000100000000000000000000000000f00000000061000000000002101000000000000e000000010510000000000061000000000000016000000000610200000000000020000000000012000000000000d000000000001300000000841000000000000010000000000a1000000000000008000000000001600000000000100000000000008
  | 7, 56 => 0x85100000000000000100000000021020000000012100000000000000600000000000010000000000012000000000001600000000021020000000000003000000480a201000000000000400000000000000000000000007000000000610000000000000070000000000009000000000000100000000021000000000000001000000000000f00000000811020000000000007000000000000200000000401000000000000016000000000001600000000000070000000000002000000000e10100000000000100000000000012
  | 7, 57 => 0x109100000000000e1010000000000016000000000001200000000811020000000000003000000480e201000000000001200000000000120000000000005000000000000f000000000001100000000061010000000109100000000000000300000000000080000000000007000000000210100000000061010000000000002000000000001600000520412010000000000000000000000001000000520412020000000084100000000000000700000000061000000000084101000000000000c0000000006102000000000e100
  | 7, 58 => 0x534402000000000000004000000000e1020000000084102000000000a1010000000000003000000010d1000000000000007000000000000100000000000040000000000008000000000000800000204802000000000000008000000000000300000000021000000001802200000000000001000000000000160000000000003000000000000400000001011010000000000016000000000000900000000000020000000000003000000000a10000000000000070000000000007000000000001200000000000160000000000006
  | 7, 59 => 0x105102000000000000800000000061020000000006102000000000000200000000000020000000002102000000000000100000000000070000000000003000000000000700000000000020000000000000000000000a102000000000a1020000000002100000000001210200000000401020000052041202000000000000200000000000160000000002102000000000001100000000000070000000000010000000000001600000000000070000000000008000000000a101000000000a10000000000061010000000002101
  | 7, 60 => 0xc91010000000000008000000008410000000000000160000000084102000000000000300000001051010000000000003000000000000400000000c41020000000012102000000480e2020000000012101000000000000000000000401010000000000008000000010d10000000000c8101000000000001000000000000030000000000011000000000000600000000000120000000080102000000000001600000000c110200000000c5101000000000000000000000021000000000000003000000000a1010000000000002
  | 7, 61 => 0xa102000000000000600000000000030000000006100000000000000200000540812000000000000010000000010510100000000000120000000000008000000000000e0000000002102000000000e1000000000000004000000480a20100000000000050000000000010000000000a10200000000000020000000006100000000000000300000000061000000000084102000000000000800000000401000000000000007000000000001000000000000070000000000012000000008010200000000000160000000002100
  | 7, 62 => 0x20000000000012000000000a100000000000001200000000000140000000000010000000000a101000000000a1000000000000002000000000a10200000000061010000000000010000000000000700000000401020000000002102000000000001200000000801010000000006101000000000000400000000021000000000000003000000000210000000000000080000000084102000000008010000000000021020000000006100000000480e2000000000002101000000000001600000000000160000000100100
  | 7, 63 => 0xa10200000000000160000000002102000000000000200000000000120000000000001000000004010200000000000020000000000002000000000000600000214842020000000000006000000010d1020000054440201000000000001100000000000000000053440200000000000000200000000000070000000000007000000000001000000000000070000000002100000000000000600000048062010000000000001000000000001000000000801020000000000010000000000000700000048022010000000000008
  | 7, 64 => 0x1210000000000c110200000000000120000000000008000000000001000000000061020000000000010000000000a102000000000001000000000000100000000000001000000000000600000000000140000000002102000000010d10100000000000080000000002100000000000000f0000000000007000000000610000000000021020000000000010000000480220100000000000100000000002101000000000a101000000000a100000000000000f000000480e200000000000210200000000000100000000000007
  | 7, 65 => 0x2000000000000400000000000160000000000007000000000000f0000000080100000000000001000000000000080000000000006000000000000600000000000030000000000009000000000001000000000061020000002802201000000000000a0000000105102000000000210100000000000040000000000010000000000e10200000000000160000000000006000000010510800000000000110000000006100000000000000600000000000030000000006101000000000000000000000000020000000000007
  | 7, 66 => 0x851020000000000006000000000a101000000000610200000000021010000000012101000000000210000000000021020000000000006000000000000400000000000050000000000008000000000000700000000000160000000000003000000000000e00000000061000000000006100000000000000600000000000010000000000004000000000000300000000000030000000000004000000000001000000000000060000000000003000000000001200000000000080000000000008000000000000c0000000012101
  | 7, 67 => 0x108100000000000000700000000000060000000000016000000000610200000000000080000000000004000000008010200000000000120000002802202000000000001000000000000060000000000008000000000000600000000000160000000000006000000480620100000000061020000000006100000000000000600000000121000000000000007000000000a102000000008510100000000000030000000000002000000000610000000000000080000000002101000000000001200000000000030000000006100
  | 7, 68 => 0xa100000000000001600000000061000000000081102000000000000400000000021000000000000003000000000001600000000021020000000000006000000004010200000000061010000000006100000000000000600000000801020000000006101000000000000f0000000000006000000000001200000000000060000010440200000000000a1020000000000004000000000000700000000021020000000000002000000000000200000000000050000000000011000000000210200000000061010000000000010
  | 7, 69 => 0x6102000000000000f000000010d1010000000000003000000000a10200000000c51000000000081102000000001210000000000000040000000000012000000000a102000000000000000000000000030000000000002000000000000700000000000030000000000004000000000610200000000000030000000108101000000000001000000000000030000000000016000000000000800000000000070000000000004000000000001200000000000080000000012102000000000001500000000000080000054440201
  | 7, 70 => 0x120000000000010000000000000700000000000060000000000005000002148420000000000000030000000000003000000000000a00000000841010000000000008000000000210100000048022010000000000007000000000000200000000000100000000000006000000010d10200000000000120000000000005000000000000600000000000020000000002102000000000000600000000000060000000006100000000000000600000000000060000002802201000000008510000000000000010000000000012
  | 7, 71 => 0x204802010000000000000000000000a102000000000001600000000c91020000000002102000000000000300000000000070000000000008000000000000f00000000000030000000000003000000180220100000000000040000000000016000000000000300000000000100000000000012000000010d1010000000084102000000000a10000000000000100000000000007000000000e1010000000006100000000000a1000000000000008000000000000f0000000000003000000004010100000544402010000000040102
  | 7, 72 => 0xa101000000000001600000038022000000000000016000000001210000000000c41000000000040100000000000001000000000000000000000000003000000008010200000000000030000000000012000000000001200000000000060000000000011000000000e10100000000121000000000000003000000000e101000000000000800000000000050000000002101000005244020000000000841000000000000007000000000000f00000000000100000000000010000000000000600000000000040000000000004
  | 7, 73 => 0x104100000000000000f000000004010100000000000030000000000010000000000a10200000000811020000020480202000000280620200000000c0100000000008010000000018022020000051081200000000000210000000000000000000000000007000000000000700000000000060000000000004000000000a1020000000000006000000000e1010000000000010000000000000700000000021010000000000008000000000000600000000000160000000000002000000000000300000000841020000053440200
  | 7, 74 => 0x10000000010d1010000000040101000000000000600000000000070000000000007000000000000f0000000000003000000000a101000000000000700000000061000000000000004000005344020200000000000070000000000016000000000e10000000000851010000000000010000000000000700000000021010000000041100000000000a1020000000000010000000000000900000000000060000000085102000000000001600000000000160000000000008000000000610200000000000060000000000016
  | 7, 75 => 0x40000000000006000000010d10200000000000120000000000011000000000a10200000000000070000000000005000000000000f00000000000060000000000008000000000e1000000000000002000000008410000000000000030000000000003000000000210000000000401020000000000007000000010410000000000841020000000000010000000380a20000000000000020000000000006000000004110100000000000010000000006102000000000000f00000000c91000000000002102000000000a102
  | 7, 76 => 0x7000000008010200000000000060000000000015000000000000500000000000010000000000008000000000000600000000000070000000000015000000000000f00000000000080000000000010000000000000800000000000060000000000002000000000001000000000000070000000000004000000000000f0000000000010000000000001100000000021000000000002102000000000000600000000121010000000000006000000000000f000000000210200000000c410200000000061020000000000008
  | 7, 77 => 0xe1010000000000003000000000001000000000000100000000080102000000000001600000000061020000000002102000000000a102000000000a10200000000000100000000000010000000008010200000000000020000000000008000000000000700000000000120000000000009000000010910000000000000060000000000007000000000000800000028022020000000000010000000480e2020000000081100000000000000300000000000080000000000006000000000000300000000021020000020480202
  | 7, 78 => 0x61020000000000016000000000a102000000000a10200000000121010000000081102000000000000200000000000060000000000016000000000000f0000004806201000000000000200000000000100000000000008000000000000200000000000030000000000010000000000001600000000000080000000000000000000000001600000000000060000000085100000000000000f00000000000120000000000010000000000e1010000000000000000000000e100000000000210200000000000050000000000006
  | 7, 79 => 0x8000000000000f000000000000600000000000070000000000011000000000000900000000000100000000000007000000000001000000000811020000000002102000000000a102000000000210200000000021000000000000002000000000a102000000010d100000000000000200000104402010000000000007000000000e100000000000a100000000000e100000000000000600000000000150000000002100000000000000600000000000000000000002102000000000210200000000061020000000000007
  | 7, 80 => 0x280620000000000021010000000000010000000000000800000000000060000000006102000000000000f00000000811020000000000002000000000000f00000544802000000000000000000000000a1020000000000003000000004010200000000000080000000000007000000000000f00000000000150000000000010000000010d102000000000a10200000000061010000000000015000000000000f000000000001100000000000000000000000007000000000000800000000000150000000000007000000000a101
  | 7, 81 => 0x40000000000016000000180220200000000000030000000000016000000000001200000000000110000000000001000000008410200000214842010000000084102000000000a1020000000000003000000000000800000000021010000000006102000000000a100000000004110200000000000030000000000003000000000000100000540812020000000040101000000000000600000000021020000000000004000000000e10000000000000060000010440202000000000001600000000401020000000000006
  | 7, 82 => 0x60000000000004000000000001600000000000020000052041200000002148420200000000801020000000000003000000000000800000000000160000000000010000000480e202000000004110100000000000000000000080102000000000001600000000c110100000000000070000000000016000000008510200000000061000000000000008000000000001100000000000070000052440201000000000000200000000000060000000000012000000000001000000000000050000020480202000000000a102
  | 7, 83 => 0xc9102000000004010200000000000040000000006102000000000000800000000000020000000000003000000000000f000000008510200000000000030000000000004000000000001000000524402020000000002100000000000000200000000411020000000000008000000000210200000000c910100000500c52000000000000012000000000210200000000000110000051081201000000000a1020000000006102000000000610200000001081000000000002101000000000001200000000000120000000000006
  | 7, 84 => 0xa1020000051081202000000000000f0000000041102000000000001000000000000160000000000011000000000000f0000000000001000000000001000000000000060000000000016000000000a102000000000001000000000021020000000000007000000000000200000000000060000000000001000000000210200000000021020000000006102000000000000f000000000000f00000000061010000000000004000000000000300000000000010000000000006000000000000800000000000070000000000012
  | 7, 85 => 0x21020000000000015000000000001600000000000100000000000016000000000610200000000000120000000000012000000000000300000000000060000000000004000000000001000000000000120000000000016000000000000800000000801020000000000008000000000001600000000000080000000040102000000000000300000000021010000000000000000000000000600000000000120000001802201000000000610200000000000080000000000013000000000210200000000061020000000000006
  | 7, 86 => 0xc910100000000000100000000000008000000000000800000000000160000000000006000000000210200000000000070000000000006000000000000500000000000020000000000006000000000e1000000000000002000000000000600000000000080000000000003000000000000900000000000060000000000012000000000000300000000000060000000000001000000000000800000000000120000000000016000000000000200000000000060000000000012000000000000300000000000100000000041102
  | 7, 87 => 0x1044020200000000000120000000000007000000000001000000000000030000000000003000000000000600000000000080000000000016000000000001200000000000070000000000010000000000000600000000000000000000000002000000000000f000000000000700000000061020000000000006000000000a1020000000012100000000000a1020000051081202000000004110000000000000070000000006102000000000001200000000000040000000000009000000000a10200000000000040000000085102
  | 7, 88 => 0x40102000000000000300000000000100000000000006000000004110200000000000080000054480201000000000210200000000000080000000000001000000000000300000000000070000000000002000000000001000000000000100000000002102000000000000f00000000000070000000000006000000000000700000000061020000000000002000000000a1020000000000012000000000000200000000000060000000000002000000000610200000000000120000000000008000000000a1020000000000003
  | 7, 89 => 0x800000000000020000000000002000000000001600000000000080000000002102000000000000300000000000060000000000016000000008410200000000000020000021484202000000000000f000000000a102000000000000f00000028022020000000000016000000000610200000000841020000000000003000000000a1020000000000006000000000001000000000000010000002806201000000000001100000000000100000000000003
  | 8, 0 => 0x10910000000000061020000000000002000000008410100000000411020000000000008000000000610100000000061020000000041101000000000000000000000000050000000000012000000000000000000000000030000000012100000000000001200000000811000000000000000000000000000100000000c51010000000000006000000000000100000000841020000000041100000000000a101000000000a102000000000000200000000000020000000000000000000000000000000000000060000000000000
  | 8, 1 => 0x600000000000000000000000006000000000000500000000c1101000000000000000000000801020000000002101000000000000200000000000010000000000002000000000000100000000000010000000105101000000008110000000000021020000000000001000000000000000000000c9102000000000000000000000411000000000101102000000010d1000000000000000000000000000200000000000010000000000008000000008010100000000000010000000000016000000010d1000000000006101
  | 8, 2 => 0x41102000000000000000000000000020000000000000000000000000200000000000050000000109102000000000000000000001011010000000000012000000000000500000000851010000000002100000000008010100000000000000000000000001000000000000100000000851020000000101102000000010d10000000001011000000000006101000000004010100000000c51020000000000002000000008110000000000c91010000000040102000000000001300000000000020000000000001
  | 8, 3 => 0x16000000000000f000000000000100000000000020000000000000000000000a100000000000000600000000411020000000000001000000000000100000001011000000000084101000000000000100000000c91010000000000001000000000000100000000000020000000000007000000008410200000001051010000000105102000000000000f0000000000008000000000001600000000c5101000000000000200000000c110100000000021000000000000014000000000000100000000411010000000105100
  | 8, 4 => 0x80101000000010110100000000000020000000000007000000000000200000000c1102000000000000f000000008010200000000000020000000109101000000000000000000000000010000000000012000000001210200000000000010000000000002000000000e1010000000080101000000010d101000000000a102000000000a1010000000000001000000000000200000000061000000000105100000000000000000000000000000000000000002000000000000000000000000050000000000004000000000a100
  | 8, 5 => 0x600000001051020000000006102000000000000f000000000a10200000000000160000000006100000000000000100000001051010000000000002000000000000100000000c11000000000000012000000000000000000000000000000000101102000000000000000000000c510100000001051020000000000008000000008510000000000000020000000000000000000000001600000000121000000000000006000000000000000000000000080000000000006000000000a10000000000841000000000000000
  | 8, 6 => 0x2102000000000000200000000c9102000000010d1010000000002101000000000e10200000000000010000000000012000000000a101000000000a1020000000000006000000000a1000000000084102000000000001100000000121010000000000004000000010910000000000000020000000000010000000000e10000000000000120000000002100000000000000000000000061020000000109101000000000000000000000061010000000000000000000000000000000000c910100000000000050000000000008
  | 8, 7 => 0x851020000000041100000000000000800000000401020000000000006000000000000100000000851010000000000006000000000000000000000000020000000000001000000004010200000000000000000000040101000000000001600000000000100000000000006000000000210100000000000040000000000005000000000000100000000c110200000000000020000000085100000000000000200000000000000000000081100000000000001200000000c5100000000000e10100000000121020000000040100
  | 8, 8 => 0x100000000c9102000000000000000000000000010000000002102000000010d1020000000109101000000000000000000000841020000000000000000000000000200000000841010000000000012000000000a10000000000000010000000000000000000000000300000000061010000000006102000000000000500000000000160000000000004000000000000200000000000020000000000002000000000001000000000c510000000000000020000000000007000000000001000000000021000000000000007
  | 8, 9 => 0x800000000c110000000000801010000000000016000000010910200000000000030000000000002000000000e102000000000000600000000000010000000000000000000000000000000000851010000000085102000000010d10200000000000060000000000001000000000000800000000000020000000040101000000004010200000000000030000000000000000000000000800000000000010000000000005000000001210100000000000080000000006100000000000000700000000021010000000002102
  | 8, 10 => 0x60000000000003000000004110000000000000120000000000001000000000000000000000000080000000000002000000000000500000000c910100000000000070000000000004000000004010000000000000000000000081101000000008410100000000841020000000000001000000000000000000000c1100000000000000000000000000100000000000002000000000000100000000000050000000012101000000000000200000000000040000000000001000000010110000000000000000000000080102
  | 8, 11 => 0x300000000000010000000002101000000010d102000000000a1020000000000002000000000610100000000000120000000000002000000000000f0000000081102000000000000000000000c9101000000000000200000000801010000000080102000000000a101000000000a10200000000021020000000000006000000010d10000000000000160000000081101000000000000400000000c9100000000000000300000000021010000000000008000000000000000000000c110000000000000000000000081102
  | 8, 12 => 0x41101000000000a10000000000000120000000081101000000000e10000000000811020000000000007000000000000100000000000020000000000016000000000000100000000000160000000006101000000000000f00000000000080000000105100000000000000f00000000000000000000000002000000010910100000000000050000000000006000000000000f00000000000080000000000012000000000a10100000000000060000000006102000000010110000000000000120000000000013000000000a100
  | 8, 13 => 0x6102000000000000200000000000010000000000002000000008010200000000000060000000000006000000010d10000000000000000000000000001000000000a10100000000000160000000000002000000000a10200000000000020000000109101000000000000200000000000010000000085102000000000e10000000000000080000000000003000000004110200000000000080000000000005000000000210100000000c110000000000000120000000002102000000000001000000000000020000000000005
  | 8, 14 => 0x105102000000010d10200000000851000000000000010000000000000000000000401000000000000007000000000610100000000000000000000000002000000000000000000001051010000000000002000000000001000000000c510100000000000060000000000008000000000000200000000000000000000002100000000000001200000000c91000000000000016000000000000300000001011010000000000002000000000000800000000000120000000000010000000000610000000000061010000000000002
  | 8, 15 => 0x1200000000000020000000000003000000000210200000000000020000000006101000000010d1020000000012101000000000001600000000000020000000000008000000000000600000000000160000000081102000000000000200000000000100000000000006000000000000200000000000020000000000010000000000a10200000000000020000000084100000000000001200000000411020000000000007000000000a10100000000000040000000000002000000000000200000000000020000000000002
  | 8, 16 => 0x841010000000000002000000000210200000000000020000000002102000000000a1020000000085102000000000000800000000000040000000040102000000000000000000000000060000000000002000000000000400000000811020000000085101000000000610200000000000030000000002102000000004010100000000000100000000000004000000000000200000000000010000000006102000000000a102000000000210100000000061020000000002101000000000000200000000000060000000080100
  | 8, 17 => 0x2
  | 9, 0 => 0x2000000000000200000000000010000000000000000000000000100000000000020000000000000000000000000200000000000010000000000000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 13 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_47 roots_47 8 s ws hint
  | 1 => checkCutEntry dom_55 roots_55 8 s ws hint
  | 2 => checkCutEntry dom_31 roots_31 8 s ws hint
  | 3 => checkCutEntry dom_59 roots_59 6 s ws hint
  | 4 => checkCutEntry dom_47_16 roots_47_16 6 s ws hint
  | 5 => checkCutEntry dom_55_8 roots_55_8 6 s ws hint
  | 6 => checkCutEntry dom_59_4 roots_59_4 6 s ws hint
  | 7 => checkCutEntry dom_61 roots_61 6 s ws hint
  | 8 => checkCutEntry dom_62_1 roots_62_1 6 s ws hint
  | 9 => checkCutEntry dom_15_16 roots_15_16 5 s ws hint
  | 10 => checkCutEntry dom_23_8 roots_23_8 5 s ws hint
  | 11 => checkCutEntry dom_39_16 roots_39_16 5 s ws hint
  | 12 => checkCutEntry dom_39_8 roots_39_8 5 s ws hint
  | 13 => checkCutEntry dom_43_4 roots_43_4 5 s ws hint
  | 14 => checkCutEntry dom_51_4 roots_51_4 5 s ws hint
  | 15 => checkCutEntry dom_29 roots_29 5 s ws hint
  | 16 => checkCutEntry dom_57 roots_57 5 s ws hint
  | 17 => checkCutEntry dom_30_1 roots_30_1 5 s ws hint
  | 18 => checkCutEntry dom_58_1 roots_58_1 5 s ws hint
  | 19 => checkCutEntry dom_15 roots_15 5 s ws hint
  | 20 => checkCutEntry dom_23 roots_23 5 s ws hint
  | 21 => checkCutEntry dom_27_4 roots_27_4 5 s ws hint
  | 22 => checkCutEntry dom_60_1 roots_60_1 5 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_55 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_59 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_55_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_59_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_61 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_62_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_39_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_39_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_43_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_51_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_29 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_57 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_30_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_58_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_27_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_60_1 _ hc
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
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
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
private theorem z6_176 : ∀ i, 176 ≤ i → i < 190 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 14 176 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 190 → Z 6 i = true := (range_split (range_split (range_split (range_split z6_0 z6_16) (range_split z6_32 z6_48)) (range_split (range_split z6_64 z6_80) (range_split z6_96 z6_112))) (range_split (range_split z6_128 z6_144) (range_split z6_160 z6_176)))
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
private theorem z7_656 : ∀ i, 656 ≤ i → i < 667 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 11 656 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 667 → Z 7 i = true := (range_split (range_split (range_split (range_split (range_split (range_split z7_0 z7_16) (range_split z7_32 z7_48)) (range_split (range_split z7_64 z7_80) (range_split z7_96 z7_112))) (range_split (range_split (range_split z7_128 z7_144) (range_split z7_160 z7_176)) (range_split (range_split z7_192 z7_208) (range_split z7_224 z7_240)))) (range_split (range_split (range_split (range_split z7_256 z7_272) (range_split z7_288 z7_304)) (range_split (range_split z7_320 z7_336) (range_split z7_352 z7_368))) (range_split (range_split (range_split z7_384 z7_400) (range_split z7_416 z7_432)) (range_split (range_split z7_448 z7_464) (range_split z7_480 z7_496))))) (range_split (range_split (range_split (range_split z7_512 z7_528) (range_split z7_544 z7_560)) (range_split (range_split z7_576 z7_592) (range_split z7_608 z7_624))) (range_split z7_640 z7_656)))
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
private theorem z8_288 : ∀ i, 288 ≤ i → i < 304 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 288 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_304 : ∀ i, 304 ≤ i → i < 318 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 14 304 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 318 → Z 8 i = true := (range_split (range_split (range_split (range_split (range_split z8_0 z8_16) (range_split z8_32 z8_48)) (range_split (range_split z8_64 z8_80) (range_split z8_96 z8_112))) (range_split (range_split (range_split z8_128 z8_144) (range_split z8_160 z8_176)) (range_split (range_split z8_192 z8_208) (range_split z8_224 z8_240)))) (range_split (range_split z8_256 z8_272) (range_split z8_288 z8_304)))
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

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 15]⟩], 16⟩

theorem wit_mono : PEqualNP.MetaComplexity.Monotone2 wit := by
  simp [wit, PEqualNP.MetaComplexity.Monotone2]

theorem wit_sz : wit.size ≤ 11 := by decide

set_option maxRecDepth 40000 in
theorem wit_ev : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = Nat.testBit (3941264072 * 2 ^ 32 + 3941132424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel

set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_63.testBit r.val = (fun x : Fin 6 → Bool => Nat.testBit (3941264072 * 2 ^ 32 + 3941132424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) (pt6 r.val) := by decide +kernel

theorem lower : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941264072 * 2 ^ 32 + 3941132424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) t → 11 ≤ t :=
  lower_to_circuit6 (fun x : Fin 6 → Bool => Nat.testBit (3941264072 * 2 ^ 32 + 3941132424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) goal_63 11 hT6 (by unfold IsConst; decide) low_63

end PEqualNP.Outside.L_meta_38987_aux

theorem PEqualNP.Outside.L_meta_38987 :
  ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941264072 * 2 ^ 32 + 3941132424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941264072 * 2 ^ 32 + 3941132424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  exact ⟨PEqualNP.Outside.L_meta_38987_aux.wit, PEqualNP.Outside.L_meta_38987_aux.wit_mono, le_trans PEqualNP.Outside.L_meta_38987_aux.wit_sz (PEqualNP.Outside.L_meta_38987_aux.lower s hs), PEqualNP.Outside.L_meta_38987_aux.wit_ev⟩
