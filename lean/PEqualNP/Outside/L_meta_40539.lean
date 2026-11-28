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

namespace PEqualNP.Outside.L_meta_40539_aux

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
def goal_31 : Nat := 0xfee8ecc0fee8ecc0fee8ecc0fee8ecc0fee8ecc0fee8ecc0fee8ecc0fee8ecc0
def roots_31 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_62_1 : Nat := 0xaaaaaaaaaaaaaaaa
def goal_62_1 : Nat := 0xfffffffffffcfcc0fffffffffffcfcc0fffffffffffcfcc0fffffffffffcfcc0
def roots_62_1 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfaaaaaaafaa0a000faaaaaaafaa0a000faaaaaaafaa0a000faaaaaaafaa0a000
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_47_16 : Nat := 0xffff0000ffff0000
def goal_47_16 : Nat := 0xfeeafeeafee8fee8feeafeeafee8fee8feeafeeafee8fee8feeafeeafee8fee8
def roots_47_16 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_15_16 : Nat := 0xffff0000
def goal_15_16 : Nat := 0xfee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8
def roots_15_16 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0]

def dom_31_32 : Nat := 0xffffffff00000000
def goal_31_32 : Nat := 0xfeeaeeeafeeaeeeafeeaeeeafeeaeeeafeeaeeeafeeaeeeafeeaeeeafeeaeeea
def roots_31_32 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xeeeaeeeaecc0ecc0eeeaeeeaecc0ecc0eeeaeeeaecc0ecc0eeeaeeeaecc0ecc0
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xeaeaeaeae8e8c0c0eaeaeaeae8e8c0c0eaeaeaeae8e8c0c0eaeaeaeae8e8c0c0
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_55_8 : Nat := 0xff00ff00ff00ff00
def goal_55_8 : Nat := 0xfefeeeeefefeececfefeeeeefefeececfefeeeeefefeececfefeeeeefefeecec
def roots_55_8 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_15 : Nat := 0xffff
def goal_15 : Nat := 0xecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0
def roots_15 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0]

def dom_15_48 : Nat := 0xffff000000000000
def goal_15_48 : Nat := 0xfeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeea
def roots_15_48 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0]

def dom_39_16 : Nat := 0xff000000ff0000
def goal_39_16 : Nat := 0xeaeaeaeae8e8e8e8eaeaeaeae8e8e8e8eaeaeaeae8e8e8e8eaeaeaeae8e8e8e8
def roots_39_16 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0]

def dom_30_32 : Nat := 0x5555555500000000
def goal_30_32 : Nat := 0xfcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0
def roots_30_32 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xeeaaeeaaee88cc00eeaaeeaaee88cc00eeaaeeaaee88cc00eeaaeeaaee88cc00
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_59_4 : Nat := 0xf0f0f0f0f0f0f0f0
def goal_59_4 : Nat := 0xffeeeeeeffeeeeccffeeeeeeffeeeeccffeeeeeeffeeeeccffeeeeeeffeeeecc
def roots_59_4 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_43_16 : Nat := 0xf0f00000f0f0000
def goal_43_16 : Nat := 0xeeaaeeaaee88ee88eeaaeeaaee88ee88eeaaeeaaee88ee88eeaaeeaaee88ee88
def roots_43_16 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_53_8 : Nat := 0x3300330033003300
def goal_53_8 : Nat := 0xfafaaaaafafaa0a0fafaaaaafafaa0a0fafaaaaafafaa0a0fafaaaaafafaa0a0
def roots_53_8 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_57_4 : Nat := 0x3030303030303030
def goal_57_4 : Nat := 0xffaaaaaaffaaaa00ffaaaaaaffaaaa00ffaaaaaaffaaaa00ffaaaaaaffaaaa00
def roots_57_4 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_30 : Nat := 0x55555555
def goal_30 : Nat := 0xfcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0
def roots_30 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfeeaeeeafee8ecc0feeaeeeafee8ecc0feeaeeeafee8ecc0feeaeeeafee8ecc0
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

namespace S_31
def pairsG : List (Nat × Nat) := [(2, 6), (2, 10), (3, 7), (3, 11), (3, 19), (4, 6), (5, 7), (5, 13), (5, 21), (8, 10), (9, 11), (9, 13), (9, 25), (12, 13), (12, 14), (12, 28), (17, 19), (17, 21), (17, 25), (18, 19), (18, 22), (18, 26), (20, 21), (20, 22), (20, 28), (24, 25), (24, 26), (24, 28)]
def r1sG : List Nat := [2, 2, 3, 3, 3, 4, 5, 5, 5, 8, 9, 9, 9, 12, 12, 12, 17, 17, 17, 18, 18, 18, 20, 20, 20, 24, 24, 24]
def r2sG : List Nat := [6, 10, 7, 11, 19, 6, 7, 13, 21, 10, 11, 13, 25, 13, 14, 28, 19, 21, 25, 19, 22, 26, 21, 22, 28, 25, 26, 28]
def mpG : Nat := 0xfffffff
def pool6G : List Nat := [4406788295174, 4406788295430, 5506299922950, 4411083262470, 4407040936454, 13202814207498, 8804969812746, 13202881317382, 4406923039494, 21999109083910, 13215951754509, 9917113697805, 19804297366803, 9904279324170, 21999226980870, 18730403957273, 18713224087061, 18704667837971, 9904481440522, 13203066848778, 13233198733581, 22063550236181, 26461596748313, 13203133958662, 18704735210003]
def xsM : List Nat := roots_31.map (· &&& dom_31)
def goalM : Nat := goal_31 &&& dom_31
def NN : Nat → Nat
  | 4 => 15
  | 5 => 108
  | 6 => 166
  | 7 => 17
  | 8 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xfbcf6739f027b0a1d329020fac05225e9cec98d6958de81d75cd60046060086d3cc879143af66a742894ea9222d83a722183067317cfa2c2124ca3ae
  | 5, 0 => 0x4dce11e94ca624074c06a2a1490fe38a48d2b8864530cac14465f0b4423bf0db41bd48f240ee66113fa5c9f03f712a6f3f64d17b3f479fd33d75815e3c7381e53b937b233a6b8d41388067753871c7f333d8467532f633fb32ca8f8a30ad3e4c2f45860b2e96a12d2e5ed7872d026e952ce96b6d2ce412202c5907dd2c4c2c0a287edd3d27c0c94d26955b4a2645d0af2637312d24d7c038237e1ed621c32ccb218257c4211ef9b12009466d1ac7d7cf1586328712f0140510a03d580dceafa70c54e2630bd9fad80bbb08d10b3763f30a70c17309c35db908884c85085f815d06a21b3d06937bbb0678929705c4e98005488ef703bfabb103adfddf01e87b28
  | 5, 1 => 0xf6928b56ee67464de457f490d7e0e6e7c9f9e606be3fb924bc1af996ac05225eaa8c6e39a54b23629ba675cd8aecbb9f89b26e9182fb0ac481ea162e81093b97801cdf4e7e4ee7887d45fffa7bdcb981772db94e756b003d729d58de71f0c0b770913e637057e16e6cbd261c663e433965b692ad65ae3aa3658e581a64d480335e1d4aa85a33ff3c57b4840456ba86e85560996153d47dca53b6e0ef537bfbe75299e96d526e44fc4f8b67664e81b97b
  | 6, 0 => 0x28182770276bea432645d0af2637312d262ad7ad2596f9112564689225303d3724e2e5ac24a5bc7d2392784f2227620520d33bcc206585ea1fee0db01cd6e59f1be300d41b8a7ef11b5242871ad93afb1ac7d7cf18c41cbb1863781a172f56661667c9511586328715436e1314e5b487148cee9c141aecf112fe2d5b12e5db13126b25b712530086120e900110ccb8d00fd672800f91f1710f6bda8c0e148d100de1e4bc0d360c660c1ef63c0b8b154b0a8209a909873cd908dabbe607c834d1074368e8067329db061a7d5105db9edf058c87c50569308c04b53d6b049ac07003d2ccb1034963b102aadecf0241d3e1015024be00c1d07800b965fd004a583e
  | 6, 1 => 0x81ea162e81dc41027f29e3097ecfa18376e6bc16755161bc741d41b072727efe724f2eeb71f3b0a46fa1aa3c6f1d831c6e5cf10469e2a5956787192464d4803364cf2b5162f275ca62b9685c5f5bd41b5e1d4aa85d1295e95c67349c5b2df191589810f1560409b8554c825e54a0be7a537bfbe752c874c85299e96d526e44fc4fad09974f3cfc264d02a4384ca6240748ddacbb46e5540c42ff956542ab05084279fe8d407c58e93e40abdd3b937b233acce27d3a6b8d4139a681093903b34638f45b7f388fb024376ad3fd361753d635a8ccec32f633fb32a01cb030706e422fe12a1b2eb6f7e02dc515b72db5e6222d5135c82d02a0a62acf390e29ed978a
  | 6, 2 => 0xfb15c6cef646aae1e457f490e40c141be0bddffae00c76efdd7a0a3ed83a9daad6f33033ca1ce8d5c91e1443c6d3c148be3fb924bb95578cb9bdbc07b9a98887b4992a82b28b23c3b23af57dacac4a33ac05225ea9f0e9d4a8a24dcda84fd52fa77ac5c5a76ef1c1a0508cfd9f4f7b3f9b706051990f6db49812ced296153e6995402eff8d53741b8aa0db2a8752a7098551ba5b830aadb3
  | 7, 0 => 0xe40c141be0bddffabe3fb924b4992a82ac05225ea0508cfd7ecfa183554c825e5299e96d3a6b8d4130706e42276bea4325303d37206585ea1b8a7ef1126b25b70241d3e1
  | 8, 0 => 0xac05225e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f0000000000000000000000000000000000000000000000000000000000000cccc000000000000000000000000000000000000000000000000000000000000aaaa00000000000000000000000000000000000000000000000000000000000055550000000000000000000000000000000000000000000000000000000000003f3f00000000000000000000000000000000000000000000000000000000000033330000000000000000000000000000000000000000000000000000000000000f0f00000000000000000000000000000000000000000000000000000000000000ff
  | 0, 1 => 0xf000f00000000000000000000000000000000000000000000000000000000000cc00cc0000000000000000000000000000000000000000000000000000000000aa00aa000000000000000000000000000000000000000000000000000000000033003300000000000000000000000000000000000000000000000000000000000f000f000000000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000fafa
  | 0, 2 => 0xff00ff0000000000000000000000000000000000000000000000000000000000f0ff0f0000000000000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000c0c0c0c00000000000000000000000000000000000000000000000000000000030f030f0000000000000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000ff0000
  | 0, 3 => 0x3333cccc000000000000000000000000000000000000000000000000000000003333333300000000000000000000000000000000000000000000000000000000333300000000000000000000000000000000000000000000000000000000000030303030000000000000000000000000000000000000000000000000000000002a2a2a2a00000000000000000000000000000000000000000000000000000000222222220000000000000000000000000000000000000000000000000000000011111111000000000000000000000000000000000000000000000000000000000fff0fff
  | 0, 4 => 0x55555555000000000000000000000000000000000000000000000000000000005555000000000000000000000000000000000000000000000000000000000000505050500000000000000000000000000000000000000000000000000000000044444444000000000000000000000000000000000000000000000000000000003f3f3f3f000000000000000000000000000000000000000000000000000000003f003f000000000000000000000000000000000000000000000000000000000033cc33cc000000000000000000000000000000000000000000000000000000003333ffff
  | 0, 5 => 0xa000a0000000000000000000000000000000000000000000000000000000000088888888000000000000000000000000000000000000000000000000000000008888000000000000000000000000000000000000000000000000000000000000880088000000000000000000000000000000000000000000000000000000000055ff55ff000000000000000000000000000000000000000000000000000000005555ffff000000000000000000000000000000000000000000000000000000005555aaaa0000000000000000000000000000000000000000000000000000000055555f5f
  | 0, 6 => 0xaaaa555500000000000000000000000000000000000000000000000000000000aaaa222200000000000000000000000000000000000000000000000000000000aaaa000000000000000000000000000000000000000000000000000000000000aaa8aaa800000000000000000000000000000000000000000000000000000000aa00aa0000000000000000000000000000000000000000000000000000000000a8a8a8a800000000000000000000000000000000000000000000000000000000a0a0a0a000000000000000000000000000000000000000000000000000000000a0a00000
  | 0, 7 => 0xaaaaeeee00000000000000000000000000000000000000000000000000000000aaaaaaff00000000000000000000000000000000000000000000000000000000aaaaaaaa00000000000000000000000000000000000000000000000000000000aaaaaaa000000000000000000000000000000000000000000000000000000000aaaaaa8800000000000000000000000000000000000000000000000000000000aaaaaa0000000000000000000000000000000000000000000000000000000000aaaaa0a000000000000000000000000000000000000000000000000000000000aaaa8888
  | 0, 8 => 0xc0ffc0ff00000000000000000000000000000000000000000000000000000000c0c0ffff00000000000000000000000000000000000000000000000000000000c0c0c0c000000000000000000000000000000000000000000000000000000000c000c00000000000000000000000000000000000000000000000000000000000bbbbbbbb00000000000000000000000000000000000000000000000000000000afafafaf00000000000000000000000000000000000000000000000000000000aaffaaff00000000000000000000000000000000000000000000000000000000aaaaffff
  | 0, 9 => 0xcccccc0000000000000000000000000000000000000000000000000000000000cccc888800000000000000000000000000000000000000000000000000000000cccc333300000000000000000000000000000000000000000000000000000000cccc000000000000000000000000000000000000000000000000000000000000ccc0ccc000000000000000000000000000000000000000000000000000000000cc88cc8800000000000000000000000000000000000000000000000000000000cc00cc0000000000000000000000000000000000000000000000000000000000c3c3c3c3
  | 0, 10 => 0xeaeaeaea00000000000000000000000000000000000000000000000000000000eaaaeaaa00000000000000000000000000000000000000000000000000000000e0e0e0e000000000000000000000000000000000000000000000000000000000dddddddd00000000000000000000000000000000000000000000000000000000ccffccff00000000000000000000000000000000000000000000000000000000ccccffff00000000000000000000000000000000000000000000000000000000cccccccc00000000000000000000000000000000000000000000000000000000ccccccc0
  | 0, 11 => 0xf00ff00f00000000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000eeeeeeee00000000000000000000000000000000000000000000000000000000eeeecccc00000000000000000000000000000000000000000000000000000000eeeaeeea00000000000000000000000000000000000000000000000000000000eecceecc00000000000000000000000000000000000000000000000000000000eecccccc00000000000000000000000000000000000000000000000000000000eccceccc
  | 0, 12 => 0xf0f0ffff00000000000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000f0f0e0e000000000000000000000000000000000000000000000000000000000f0f0c0c000000000000000000000000000000000000000000000000000000000f0f0a0a000000000000000000000000000000000000000000000000000000000f0f00f0f00000000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000f0c0f0c0
  | 0, 13 => 0xfafa000000000000000000000000000000000000000000000000000000000000faf0faf000000000000000000000000000000000000000000000000000000000faaaaaaa00000000000000000000000000000000000000000000000000000000faaa000000000000000000000000000000000000000000000000000000000000f8f8f8f800000000000000000000000000000000000000000000000000000000f5f5f5f500000000000000000000000000000000000000000000000000000000f3f3f3f300000000000000000000000000000000000000000000000000000000f0fff0ff
  | 0, 14 => 0xff00aa0000000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000fcfcfcfc00000000000000000000000000000000000000000000000000000000fcf0fcf000000000000000000000000000000000000000000000000000000000fcccfccc00000000000000000000000000000000000000000000000000000000fafafafa00000000000000000000000000000000000000000000000000000000fafaf0f000000000000000000000000000000000000000000000000000000000fafaaaaa
  | 0, 15 => 0xffa0ff0000000000000000000000000000000000000000000000000000000000ff88ff0000000000000000000000000000000000000000000000000000000000ff80ff8000000000000000000000000000000000000000000000000000000000ff33ff3300000000000000000000000000000000000000000000000000000000ff0fff0f00000000000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000ff00fc0000000000000000000000000000000000000000000000000000000000ff00f000
  | 1, 0 => 0xfffafffa00000000000000000000000000000000000000000000000000000000fff0fff000000000000000000000000000000000000000000000000000000000fff0000000000000000000000000000000000000000000000000000000000000ffccffcc00000000000000000000000000000000000000000000000000000000ffc0ffc000000000000000000000000000000000000000000000000000000000ffaaffaa00000000000000000000000000000000000000000000000000000000ffaaff0000000000000000000000000000000000000000000000000000000000ffaaaaaa
  | 1, 1 => 0xffffcccc00000000000000000000000000000000000000000000000000000000ffffcc0000000000000000000000000000000000000000000000000000000000ffffc0c000000000000000000000000000000000000000000000000000000000ffffaaaa00000000000000000000000000000000000000000000000000000000ffff888800000000000000000000000000000000000000000000000000000000ffff880000000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000fffcfffc
  | 1, 2 => 0xffffff0000000000000000000000000000000000000000000000000000000000fffffcfc00000000000000000000000000000000000000000000000000000000fffffafa00000000000000000000000000000000000000000000000000000000fffff0f000000000000000000000000000000000000000000000000000000000fffff00000000000000000000000000000000000000000000000000000000000ffffeeee
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x7a66512940089513d174008d7a75574897a66513d500897a483d4007a664d3d40089663d214007a663d1f400895f513d4007a6651374007a513d164007a6f55514008d83753d4007a62513d4007a6551354
  | 5, 0, 0 => 0x897a6651345897a75574557a61513d0158966493d0c5898166513357a75453d0a5897d66513d5896651410d58966513a115897251311157a66513d085897a513d125897a66513b5927a61513958e7a513d155807a6651355
  | 5, 0, 1 => 0x8984493d1558983663d1e5897a66513f5897a66513a5897a72513157a665140055897a66513c5898266512b58a7a66513d57a66513d035897a66361e589665127115898366513d57a6651350457a6f665d515897a6651365
  | 5, 0, 2 => 0x8d7a66513d5897a6651275897a663a1e5897a72311e5665127110a589513d1511589665d2e115898366575158968513d0f58366513d0a5896651473d58966271e115897a66511b57a67513d0757a6f6651275895e513d0b5
  | 5, 0, 3 => 0x8d7a663d1e5897a66271e5513d15110a5897a693d1c5898474513d5893d1e15115897a6651285897a665b515897a662e1957a6651463d57a66513f0a5897a66513e58966513d2257a7251310a58e66513d115897a6654245
  | 5, 0, 4 => 0x7a66271e0a5897a66593d5907a6651355897a3d1e15589865e513d5898375453d5897a66583d58d7a6657515897a65513d58f7a664c2758f7a664f3d57a6651270a5897a513d155897a665d2e58984664b3d57a6f6651315
  | 5, 0, 5 => 0x7a776651355897a6d66515898466493d5897a753d235897f66513d56f66513d1158f7a663d205897a66431a5865e513d0a5897a66503d5897966513d5898673513d5897e66513d589865e3d1e5897a66565158986513d185
  | 5, 0, 6 => 0x8c7a66351e58c7a66512a58c7a66513557a6c66513d58d7a6651275897a663d1e58983513d155897a66513d58966533d0e5897a7255515898660513d58c7a5135155
  | 6, 0, 0 => 0x94897a66513d600897a66513d30600897a66513d00600897a6651353160089665e513d1160095897a665127600897a663d311e600897a66513d236008d7a6651453d60089877a66513d600897a66514527600897a6661513d6007a66513d0a09600897266513d11600897a6663513d6008966513d11106
  | 6, 0, 1 => 0x897a6651493d6007a726f66513d6007a6652513d0a600898466513d11600897b7a66513d600897a663d1e15600897a6b66513d600896866513d11600897a66513d2b600897a6651271e6008b897a66513d6007a66513d310a600897a6651403d600897a51423d156008986665e513d6008c8966513d116
  | 6, 0, 2 => 0x8f897a664c3d600897a66513d0a6007a6661513d0a600897a51453d15600008966512711500897a6654513d600897a6664513d600897a66513d326007a66513d150a60000898366513d500897a66514a3d600897a665a513d600897a66513d2560089868466513d600897a665d512e600897a66513d0e6
  | 6, 0, 3 => 0x92897a513d156008c897a66513d60000897a66513a50000897a725131500897a66513d24600897a7066513d600897a513d1e15600897a665e513d600897a66513d2c600897a66493d1e6007a6651403d0a600897a756651276008f7a66513d35600897a7266513d600897a66513d1060089827a665d516
  | 6, 0, 4 => 0x896653513d1160089827a665127600897a665e3d1e600897a6e66513d6008966513d35116000089513d1511500897a72663d1e60089847a66513d600897a66514e3d600897a66512e27600897a663d1e0a600897a66512726600897a66513d1860092897a61513d600897a665c513d60089827a6651336
  | 6, 0, 5 => 0x7a66513d0a0660089857a66513d600897a6a66512760000897a66271e500897a66514c27600897a513d2e15600897a665d512760089847a663d1e60089846651493d6008c7a66513d0a6007a665e513d0a600008d7a66513d5008c897a66513560000897a6651275008c897a663d1e600897a7366513d6
  | 6, 0, 6 => 0x897a76513d15600897a6651423d600897a6660513d600897a66513d2a6000089865e513d500897a6657513d6008f897a665127600897a5d513d15600897a6653513d600897a66513d04600897a66513d35600896651453d11600007a6651270a500897a6766513d60000897a513d1550000897a665d2e5
  | 6, 0, 7 => 0x898466493d500897a663d1e1d600897a7451493d600897a66513d1e600897a513d2715600897a66513d02600897566513d1160089867a665127600897a66513d20600897a7866513d600897a66513d1d600897a66513d396007a66513d350a60089837a66513d600897a663d351e60000897a3d1e155
  | 6, 0, 8 => 0x90897a66513d600897a663d1e1c600897a66433d1e600897c7a66513d600897a66513d2e600897a66513d26600897a7566453d600897a513d311560091897a66513d600897a66513d1c600897a6651433d689867a66513d3570089867a513d15600897a513d1511600897a513d1514600897a66513d386
  | 6, 0, 9 => 0x897a7166513d600897a66513d2f60089887a66513d60093897a66513d600897a513d1513600897a665d3d1e60000897a663d1e500897a6651443d600897a66513d0c600897c7a663d1e600897a665d513d600897a663d2e1e600897a66513d0b600897a66513d0f60000897a66513d500897a6651270a6
  | 6, 0, 10 => 0x897a66513d2d60089867a663d1e600008c7a66513550089867a66513d600897a66513d11600897a66514b3d6
  | 7, 0, 0 => 0x897a66513d11600897a663d1e5897a665d513d600897a66513d5897a66513d2e6897a66513d1e6897a66513d35600897a513d15500897a665127589847a66513d68c897a66513d6897a665e513d6897a7266513d6897a66513d0a6897a6651493d6897a6661513d6
  | 7, 0, 1 => 0x89867a66513d6
  | 8, 0, 0 => 0x897a66513d5
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
  | 0, 0 => 0xe1e0000000000000000000000000000000000000000000000000000000000000001f0000000000000000000000000000000000000000000000000000000000001ddc000000000000000000000000000000000000000000000000000000000000e223000000000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000ffe00000000000000000000000000000000000000000000000000000000000001e1f00000000000000000000000000000000000000000000000000000000000001ff
  | 0, 1 => 0x1c001e0000000000000000000000000000000000000000000000000000000000038001f00000000000000000000000000000000000000000000000000000000000701dc0000000000000000000000000000000000000000000000000000000001c701e000000000000000000000000000000000000000000000000000000000003f001f000000000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000fe00000000000000000000000000000000000000000000000000000000000000fdfc
  | 0, 2 => 0xfc01fe0000000000000000000000000000000000000000000000000000000000e3fe1e0000000000000000000000000000000000000000000000000000000000e3f1e1f000000000000000000000000000000000000000000000000000000000e001e00000000000000000000000000000000000000000000000000000000000038001f000000000000000000000000000000000000000000000000000000000e3f1e1f0000000000000000000000000000000000000000000000000000000001ff01ff0000000000000000000000000000000000000000000000000000000001ff0000
  | 0, 3 => 0xfc7001f000000000000000000000000000000000000000000000000000000000fc7ffe0000000000000000000000000000000000000000000000000000000000fc700000000000000000000000000000000000000000000000000000000000001c0e1e00000000000000000000000000000000000000000000000000000000000071ddc0000000000000000000000000000000000000000000000000000000000071dc0000000000000000000000000000000000000000000000000000000000fc0e220000000000000000000000000000000000000000000000000000000000fff1fff
  | 0, 4 => 0xff8e223000000000000000000000000000000000000000000000000000000000ff800000000000000000000000000000000000000000000000000000000000001c0e0200000000000000000000000000000000000000000000000000000000000380003000000000000000000000000000000000000000000000000000000000fffffff000000000000000000000000000000000000000000000000000000000e00fe00000000000000000000000000000000000000000000000000000000000e38fe1f000000000000000000000000000000000000000000000000000000000fc7ffff
  | 0, 5 => 0x1c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000fffe3ff000000000000000000000000000000000000000000000000000000000ff8ffff000000000000000000000000000000000000000000000000000000000ff81ddc000000000000000000000000000000000000000000000000000000000ff8fe3f
  | 0, 6 => 0x7e2230000000000000000000000000000000000000000000000000000000000071dc000000000000000000000000000000000000000000000000000000000000700000000000000000000000000000000000000000000000000000000000000001ddc0000000000000000000000000000000000000000000000000000000000001c0000000000000000000000000000000000000000000000000000000000000001dc00000000000000000000000000000000000000000000000000000000000001c00000000000000000000000000000000000000000000000000000000000000000
  | 0, 7 => 0x71ddf0000000000000000000000000000000000000000000000000000000000071dff0000000000000000000000000000000000000000000000000000000000071ddc0000000000000000000000000000000000000000000000000000000000071dc00000000000000000000000000000000000000000000000000000000000071c1c0000000000000000000000000000000000000000000000000000000000071c0000000000000000000000000000000000000000000000000000000000000701c0000000000000000000000000000000000000000000000000000000000007001c
  | 0, 8 => 0x1ff01ff000000000000000000000000000000000000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000fc7fffc000000000000000000000000000000000000000000000000000000000e3f1fdf0000000000000000000000000000000000000000000000000000000001ff1dff000000000000000000000000000000000000000000000000000000000007ffff
  | 0, 9 => 0x380000000000000000000000000000000000000000000000000000000000000038001c000000000000000000000000000000000000000000000000000000000038ffe000000000000000000000000000000000000000000000000000000000003800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e071e00
  | 0, 10 => 0x71ddc0000000000000000000000000000000000000000000000000000000000071ddc00000000000000000000000000000000000000000000000000000000000001c0000000000000000000000000000000000000000000000000000000000ff8e23f0000000000000000000000000000000000000000000000000000000001ff01ff000000000000000000000000000000000000000000000000000000000038ffff000000000000000000000000000000000000000000000000000000000038001f0000000000000000000000000000000000000000000000000000000000380000
  | 0, 11 => 0x3fe01f000000000000000000000000000000000000000000000000000000000000e00000000000000000000000000000000000000000000000000000000000003f1ddf00000000000000000000000000000000000000000000000000000000003f001f0000000000000000000000000000000000000000000000000000000000071ddc0000000000000000000000000000000000000000000000000000000000381c1f000000000000000000000000000000000000000000000000000000000038001f000000000000000000000000000000000000000000000000000000000038001f
  | 0, 12 => 0x1c0ffff0000000000000000000000000000000000000000000000000000000001c0e1e00000000000000000000000000000000000000000000000000000000001c001c00000000000000000000000000000000000000000000000000000000001c000000000000000000000000000000000000000000000000000000000000001c001c00000000000000000000000000000000000000000000000000000000001c01e1f0000000000000000000000000000000000000000000000000000000001c00000000000000000000000000000000000000000000000000000000000000000e000
  | 0, 13 => 0x1c700000000000000000000000000000000000000000000000000000000000001c0fde00000000000000000000000000000000000000000000000000000000000071ddc00000000000000000000000000000000000000000000000000000000000700000000000000000000000000000000000000000000000000000000000001c0e1fc000000000000000000000000000000000000000000000000000000000ff8e3e3000000000000000000000000000000000000000000000000000000000fc7ffe00000000000000000000000000000000000000000000000000000000001ffe1ff
  | 0, 14 => 0xe001c00000000000000000000000000000000000000000000000000000000000e0000000000000000000000000000000000000000000000000000000000000001f8e1ff0000000000000000000000000000000000000000000000000000000001c0e1e0000000000000000000000000000000000000000000000000000000000038e01f0000000000000000000000000000000000000000000000000000000001c7fdfc0000000000000000000000000000000000000000000000000000000001c7e1e00000000000000000000000000000000000000000000000000000000001c71ddc
  | 0, 15 => 0xe00fe00000000000000000000000000000000000000000000000000000000000e00fe00000000000000000000000000000000000000000000000000000000000e00fe00000000000000000000000000000000000000000000000000000000000fc7ffe0000000000000000000000000000000000000000000000000000000000e3ffe1f000000000000000000000000000000000000000000000000000000000e00fe00000000000000000000000000000000000000000000000000000000000e00e000000000000000000000000000000000000000000000000000000000000e00e000
  | 1, 0 => 0xfc7fffc000000000000000000000000000000000000000000000000000000000fc0ffe0000000000000000000000000000000000000000000000000000000000fc00000000000000000000000000000000000000000000000000000000000000e38fe1f000000000000000000000000000000000000000000000000000000000e00fe00000000000000000000000000000000000000000000000000000000000e07ffdc000000000000000000000000000000000000000000000000000000000e07fe00000000000000000000000000000000000000000000000000000000000e071ddc
  | 1, 1 => 0xfff001f000000000000000000000000000000000000000000000000000000000fff0000000000000000000000000000000000000000000000000000000000000fff0000000000000000000000000000000000000000000000000000000000000fff1ddc000000000000000000000000000000000000000000000000000000000fff001c000000000000000000000000000000000000000000000000000000000fff0000000000000000000000000000000000000000000000000000000000000fff0000000000000000000000000000000000000000000000000000000000000ff8ffff
  | 1, 2 => 0xffffe00000000000000000000000000000000000000000000000000000000000fffe1ff000000000000000000000000000000000000000000000000000000000ffffdfc000000000000000000000000000000000000000000000000000000000fffe1e0000000000000000000000000000000000000000000000000000000000fffe000000000000000000000000000000000000000000000000000000000000fff1ddf
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x68e5000000000000000000000000000000000000000000000000000000000000466f0000000000000000000000000000000000000000000000000000000000002ccc00000000000000000000000000000000000000000000000000000000000042230000000000000000000000000000000000000000000000000000000000002e8a0000000000000000000000000000000000000000000000000000000000002880000000000000000000000000000000000000000000000000000000000000060a0000000000000000000000000000000000000000000000000000000000000065
  | 0, 1 => 0xd20165000000000000000000000000000000000000000000000000000000000099007500000000000000000000000000000000000000000000000000000000004b0154000000000000000000000000000000000000000000000000000000000042010000000000000000000000000000000000000000000000000000000000000900100000000000000000000000000000000000000000000000000000000000006eef0000000000000000000000000000000000000000000000000000000000006e8a0000000000000000000000000000000000000000000000000000000000006ced
  | 0, 2 => 0x6f6176f00000000000000000000000000000000000000000000000000000000062d78f500000000000000000000000000000000000000000000000000000000062d161a000000000000000000000000000000000000000000000000000000000624160a000000000000000000000000000000000000000000000000000000000429061a00000000000000000000000000000000000000000000000000000000020d10100000000000000000000000000000000000000000000000000000000000db01750000000000000000000000000000000000000000000000000000000000db0110
  | 0, 3 => 0xb46d76f000000000000000000000000000000000000000000000000000000000b46b980000000000000000000000000000000000000000000000000000000000b469100000000000000000000000000000000000000000000000000000000000942a98000000000000000000000000000000000000000000000000000000000024f3d98000000000000000000000000000000000000000000000000000000000246398000000000000000000000000000000000000000000000000000000000090080000000000000000000000000000000000000000000000000000000000006ff177f
  | 0, 4 => 0xdb0c223000000000000000000000000000000000000000000000000000000000db08000000000000000000000000000000000000000000000000000000000000990c0210000000000000000000000000000000000000000000000000000000004b04223000000000000000000000000000000000000000000000000000000000f6fbf9a000000000000000000000000000000000000000000000000000000000f24be8a000000000000000000000000000000000000000000000000000000000b9db8f5000000000000000000000000000000000000000000000000000000000b46ffef
  | 0, 5 => 0x2880000000000000000000000000000000000000000000000000000000000009045c00000000000000000000000000000000000000000000000000000000000900100000000000000000000000000000000000000000000000000000000000000408000000000000000000000000000000000000000000000000000000000dfbc377000000000000000000000000000000000000000000000000000000000db0eeef000000000000000000000000000000000000000000000000000000000db0accc000000000000000000000000000000000000000000000000000000000db0c62b
  | 0, 6 => 0x24f533300000000000000000000000000000000000000000000000000000000024f399000000000000000000000000000000000000000000000000000000000024f111000000000000000000000000000000000000000000000000000000000024f3ddc0000000000000000000000000000000000000000000000000000000002043c8800000000000000000000000000000000000000000000000000000000004b2ddc00000000000000000000000000000000000000000000000000000000004229c40000000000000000000000000000000000000000000000000000000000420100
  | 0, 7 => 0x24f7fff00000000000000000000000000000000000000000000000000000000024f3dfd00000000000000000000000000000000000000000000000000000000024f3ddc00000000000000000000000000000000000000000000000000000000024f3ddc00000000000000000000000000000000000000000000000000000000024f3ddc00000000000000000000000000000000000000000000000000000000024f3d9800000000000000000000000000000000000000000000000000000000024f39d400000000000000000000000000000000000000000000000000000000024f155c
  | 0, 8 => 0xdb41750000000000000000000000000000000000000000000000000000000000906eef00000000000000000000000000000000000000000000000000000000009040650000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000b4fbddc00000000000000000000000000000000000000000000000000000000066f3fde0000000000000000000000000000000000000000000000000000000002df3dfd00000000000000000000000000000000000000000000000000000000024f7fff
  | 0, 9 => 0x4b9461a0000000000000000000000000000000000000000000000000000000004b9045c0000000000000000000000000000000000000000000000000000000004b928900000000000000000000000000000000000000000000000000000000004b900100000000000000000000000000000000000000000000000000000000004b0466f000000000000000000000000000000000000000000000000000000000429465e000000000000000000000000000000000000000000000000000000000420460a0000000000000000000000000000000000000000000000000000000002945065
  | 0, 10 => 0x2df7dfd00000000000000000000000000000000000000000000000000000000024f7ddc0000000000000000000000000000000000000000000000000000000000d269e5000000000000000000000000000000000000000000000000000000000db9c67f0000000000000000000000000000000000000000000000000000000004fb477f0000000000000000000000000000000000000000000000000000000004b96eff0000000000000000000000000000000000000000000000000000000004b9467f0000000000000000000000000000000000000000000000000000000004b9467f
  | 0, 11 => 0x909e890000000000000000000000000000000000000000000000000000000000900e8800000000000000000000000000000000000000000000000000000000006ff7fff0000000000000000000000000000000000000000000000000000000006ff577f0000000000000000000000000000000000000000000000000000000006ff7fff0000000000000000000000000000000000000000000000000000000006bd7eff0000000000000000000000000000000000000000000000000000000006bd567f0000000000000000000000000000000000000000000000000000000004b96eff
  | 0, 12 => 0x9d2efef0000000000000000000000000000000000000000000000000000000009d2e9e50000000000000000000000000000000000000000000000000000000009d2e9e50000000000000000000000000000000000000000000000000000000009d2c1650000000000000000000000000000000000000000000000000000000009d2a9c40000000000000000000000000000000000000000000000000000000009d2870a0000000000000000000000000000000000000000000000000000000009d28100000000000000000000000000000000000000000000000000000000000990e8e5
  | 0, 13 => 0xbdf9110000000000000000000000000000000000000000000000000000000000bd6fded000000000000000000000000000000000000000000000000000000000b4fbddc000000000000000000000000000000000000000000000000000000000b4f91100000000000000000000000000000000000000000000000000000000009dbedfd000000000000000000000000000000000000000000000000000000000df2ebe7000000000000000000000000000000000000000000000000000000000bd6f9e50000000000000000000000000000000000000000000000000000000009dbe9f5
  | 0, 14 => 0xf24bc88000000000000000000000000000000000000000000000000000000000f249000000000000000000000000000000000000000000000000000000000000dfbefff000000000000000000000000000000000000000000000000000000000df2efef000000000000000000000000000000000000000000000000000000000db9eeff000000000000000000000000000000000000000000000000000000000bdffdfd000000000000000000000000000000000000000000000000000000000bdff9f5000000000000000000000000000000000000000000000000000000000bdfbddc
  | 0, 15 => 0xf66ff8a000000000000000000000000000000000000000000000000000000000f2dfe9a000000000000000000000000000000000000000000000000000000000f24fece000000000000000000000000000000000000000000000000000000000f66ff8a000000000000000000000000000000000000000000000000000000000f2dfe9a000000000000000000000000000000000000000000000000000000000f24fe8a000000000000000000000000000000000000000000000000000000000f24fe8a000000000000000000000000000000000000000000000000000000000f24f880
  | 1, 0 => 0xfffffff000000000000000000000000000000000000000000000000000000000ff6ffef000000000000000000000000000000000000000000000000000000000ff69100000000000000000000000000000000000000000000000000000000000fbdfeff000000000000000000000000000000000000000000000000000000000fb4feef000000000000000000000000000000000000000000000000000000000f6fffde000000000000000000000000000000000000000000000000000000000f6fff9a000000000000000000000000000000000000000000000000000000000f6fbddc
  | 1, 1 => 0xfffd77f000000000000000000000000000000000000000000000000000000000fffd71a000000000000000000000000000000000000000000000000000000000fffd175000000000000000000000000000000000000000000000000000000000fffbddc000000000000000000000000000000000000000000000000000000000fff955c000000000000000000000000000000000000000000000000000000000fff9518000000000000000000000000000000000000000000000000000000000fff9110000000000000000000000000000000000000000000000000000000000fffffff
  | 1, 2 => 0xfffff9a000000000000000000000000000000000000000000000000000000000fffffff000000000000000000000000000000000000000000000000000000000ffffdfd000000000000000000000000000000000000000000000000000000000ffff9f5000000000000000000000000000000000000000000000000000000000ffff990000000000000000000000000000000000000000000000000000000000fffffff
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 150 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 150 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 150 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 150 then wireAt i else 0
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
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 15 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 15 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 15 → Z 4 i = true := z4_0
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
private theorem z5_96 : ∀ i, 96 ≤ i → i < 108 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 96 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 108 → Z 5 i = true := (range_split (range_split (range_split z5_0 z5_16) (range_split z5_32 z5_48)) (range_split (range_split z5_64 z5_80) z5_96))
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
private theorem z6_160 : ∀ i, 160 ≤ i → i < 166 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 160 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 166 → Z 6 i = true := (range_split (range_split (range_split (range_split z6_0 z6_16) (range_split z6_32 z6_48)) (range_split (range_split z6_64 z6_80) (range_split z6_96 z6_112))) (range_split (range_split z6_128 z6_144) z6_160))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : ∀ i, 0 ≤ i → i < 16 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_16 : ∀ i, 16 ≤ i → i < 17 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 16 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 17 → Z 7 i = true := (range_split z7_0 z7_16)
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
  scr dom_31 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 8) (h : RunD dom_31 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_31 roots_31 goal_31 9 := by
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

theorem low_31 : Lower dom_31 roots_31 goal_31 9 := S_31.noCircuit

namespace S_62_1
def pairsG : List (Nat × Nat) := [(1, 33), (3, 7), (3, 11), (3, 19), (3, 35), (5, 7), (5, 13), (5, 21), (5, 37), (9, 11), (9, 13), (9, 25), (9, 41), (17, 19), (17, 21), (17, 25), (17, 49)]
def r1sG : List Nat := [1, 3, 3, 3, 3, 5, 5, 5, 5, 9, 9, 9, 9, 17, 17, 17, 17]
def r2sG : List Nat := [33, 7, 11, 19, 35, 7, 13, 21, 37, 11, 13, 25, 41, 19, 21, 25, 49]
def mpG : Nat := 0x1ffff
def pool6G : List Nat := [5510594890503, 18730403957529, 18713224087317, 9917130540813, 18704667838227, 9908574291723, 18704735209235, 9908776404747, 5510729634573, 9917366342925]
def xsM : List Nat := roots_62_1.map (· &&& dom_62_1)
def goalM : Nat := goal_62_1 &&& dom_62_1
def NN : Nat → Nat
  | 4 => 9
  | 5 => 21
  | 6 => 10
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x56dcf86a4ced50033533fb6f27d4c612115e7c290e9bd6fe0ddf36350b27fa1c0270fd07
  | 5, 0 => 0x6d5d3bc753e01c1e534137d9502d68b94fcd93204ced500343a2034c3ca8168c1f5bfe8014b587b312331113115e7c290e619fdd089d877d0706231805929501043a5eb202dfc1ef014eb79c01255874009dedba
  | 6, 0 => 0xe2d3b7c9534137d94ced500330f1064f2a9a5d9a2319d16a15e8d6110e619fdd0672c8d501255874
  | 7, 0 => 0x4ced5003
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xa0a0a0a0a0a0a0a00000000000000000000000000000000000000000000000000aa00aa00aa00aa0000000000000000000000000000000000000000000000000000aaaa0000aaaa00000000000000000000000000000000000000000000000000000000aaaaaaaa00000000000000000000000000000000000000000000000000000000aaaa000000000000000000000000000000000000000000000000000000000000888888880000000000000000000000000000000000000000000000000000000022222222000000000000000000000000000000000000000000000000000000000a0a0a0a
  | 0, 1 => 0xa8a8a8a8a8a8a8a8000000000000000000000000000000000000000000000000a8a8a8a8a0a0a0a0000000000000000000000000000000000000000000000000a8a0a8a0a8a0a8a0000000000000000000000000000000000000000000000000a0a0a0a0a0a0a0a00000000000000000000000000000000000000000000000008888888888888888000000000000000000000000000000000000000000000000888888880000000000000000000000000000000000000000000000000000000080808080808080800000000000000000000000000000000000000000000000002222222222222222
  | 0, 2 => 0xaaaa8888aaaa8888000000000000000000000000000000000000000000000000aaaa0000aaaa0000000000000000000000000000000000000000000000000000aaa0aaa0aaa0aaa0000000000000000000000000000000000000000000000000aa88aa88aa88aa88000000000000000000000000000000000000000000000000aa88aa8888888888000000000000000000000000000000000000000000000000aa80aa80aa80aa80000000000000000000000000000000000000000000000000aa00aa00aa00aa00000000000000000000000000000000000000000000000000aa000000aa000000
  | 0, 3 => 0xaaaaaaaaaa00aa00000000000000000000000000000000000000000000000000aaaaaaaaa0a0a0a0000000000000000000000000000000000000000000000000aaaaaaaaa0a00000000000000000000000000000000000000000000000000000aaaaaaaa88888888000000000000000000000000000000000000000000000000aaaaaaaa88008800000000000000000000000000000000000000000000000000aaaaaaaa0a0a0a0a000000000000000000000000000000000000000000000000aaaaaaaa00000000000000000000000000000000000000000000000000000000aaaaa0a0aaaaa0a0
  | 0, 4 => 0xaaaaaaaaaaaa0000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x81f70c465644c2d408112c040207cb1d007dc58c401d6112d0071644e4019594351961744f5
  | 5, 0, 0 => 0x1959130b501130b103501a65644b501f79958b501644c204501c65630650007dc58c401644c2c4501959344c501959130250195913c9502079130b501c59130a565655430b601c65644c501959230b5
  | 5, 0, 1 => 0x1b59130b502044c2c45019591308501944b1c550195913015
  | 6, 0, 0 => 0x65644c2c46019591308501959130b565859130b665644c2c7665644c2ca665645030b601644c2c4581959130b601c65644c5
  | 7, 0, 0 => 0x1959130b5
  | _, _, _ => 0
def stateW : Nat → Nat
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
  | 0, 0 => 0x1fe1f000000000000000000000000000000000000000000000000000000000001e1ff0000000000000000000000000000000000000000000000000000000000001fff000000000000000000000000000000000000000000000000000000000001ffff000000000000000000000000000000000000000000000000000000000001e000000000000000000000000000000000000000000000000000000000000000001e000000000000000000000000000000000000000000000000000000000001ffe1000000000000000000000000000000000000000000000000000000000001fe1f
  | 0, 1 => 0x1fe00000000000000000000000000000000000000000000000000000000000001e000000000000000000000000000000000000000000000000000000000000001e000000000000000000000000000000000000000000000000000000000000001e0000000000000000000000000000000000000000000000000000000000000001e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001ffe1
  | 0, 2 => 0x1e01e000000000000000000000000000000000000000000000000000000000001e0000000000000000000000000000000000000000000000000000000000000001fe00000000000000000000000000000000000000000000000000000000000001e1e000000000000000000000000000000000000000000000000000000000000001e0000000000000000000000000000000000000000000000000000000000001e000000000000000000000000000000000000000000000000000000000000001e000000000000000000000000000000000000000000000000000000000000000000
  | 0, 3 => 0x1e0000000000000000000000000000000000000000000000000000000000000001e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001fe1f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001e1e0
  | 0, 4 => 0x1e000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x1ba1d00000000000000000000000000000000000000000000000000000000000161bb0000000000000000000000000000000000000000000000000000000000001777000000000000000000000000000000000000000000000000000000000000eeee000000000000000000000000000000000000000000000000000000000000e888000000000000000000000000000000000000000000000000000000000000222e000000000000000000000000000000000000000000000000000000000000ccc0000000000000000000000000000000000000000000000000000000000000aa0c
  | 0, 1 => 0x67fe00000000000000000000000000000000000000000000000000000000000045f200000000000000000000000000000000000000000000000000000000000047e600000000000000000000000000000000000000000000000000000000000045e2000000000000000000000000000000000000000000000000000000000000223e00000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000022000000000000000000000000000000000000000000000000000000000001ddc1
  | 0, 2 => 0x1eabe000000000000000000000000000000000000000000000000000000000001e888000000000000000000000000000000000000000000000000000000000000dfe6000000000000000000000000000000000000000000000000000000000000be7e000000000000000000000000000000000000000000000000000000000000323e0000000000000000000000000000000000000000000000000000000000009e660000000000000000000000000000000000000000000000000000000000009e440000000000000000000000000000000000000000000000000000000000008800
  | 0, 3 => 0x19f5500000000000000000000000000000000000000000000000000000000000155f30000000000000000000000000000000000000000000000000000000000015191000000000000000000000000000000000000000000000000000000000001333f0000000000000000000000000000000000000000000000000000000000011315000000000000000000000000000000000000000000000000000000000001bb1d0000000000000000000000000000000000000000000000000000000000011111000000000000000000000000000000000000000000000000000000000001edea
  | 0, 4 => 0x1f999
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 33 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 33 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 33 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 33 then wireAt i else 0
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_62_1 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_62_1 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
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
private theorem z4_0 : ∀ i, 0 ≤ i → i < 9 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 9 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 9 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_16 : ∀ i, 16 ≤ i → i < 21 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 5 16 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 21 → Z 5 i = true := (range_split z5_0 z5_16)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 10 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 10 0 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 10 → Z 6 i = true := z6_0
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
  scr dom_62_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_62_1 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_62_1 roots_62_1 goal_62_1 8 := by
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

theorem low_62_1 : Lower dom_62_1 roots_62_1 goal_62_1 8 := S_62_1.noCircuit

namespace S_61
def pairsG : List (Nat × Nat) := [(1, 33), (5, 13), (5, 21), (5, 37), (9, 13), (9, 25), (9, 41), (12, 13), (12, 28), (17, 21), (17, 25), (17, 49), (20, 21), (20, 28), (24, 25), (24, 28), (32, 33), (36, 37), (40, 41), (44, 45), (44, 60), (48, 49), (52, 53), (52, 60), (56, 57), (56, 60)]
def r1sG : List Nat := [1, 5, 5, 5, 9, 9, 9, 12, 12, 17, 17, 17, 20, 20, 24, 24, 32, 36, 40, 44, 44, 48, 52, 52, 56, 56]
def r2sG : List Nat := [33, 13, 21, 37, 13, 25, 41, 13, 28, 21, 25, 49, 21, 28, 25, 28, 33, 37, 41, 45, 60, 49, 53, 60, 57, 60]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [9917366342925, 18730437643545, 18713325145365, 13215951754509, 22011910556949, 13233198733581, 22063651494165, 26427674139673, 26462168095769, 26405611572508, 22041857428764, 22064188693525, 13233735932941, 13199308756237, 13216488625421]
def xsM : List Nat := roots_61.map (· &&& dom_61)
def goalM : Nat := goal_61 &&& dom_61
def NN : Nat → Nat
  | 4 => 4
  | 5 => 26
  | 6 => 16
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xa5c15f57995298d141f30158162781e1
  | 5, 0 => 0xd532456ed268f7e7ce2fdbfd9c1be658995298d186fec3497694e7897432112863db55fb62db99cd5fa23a115577e84451bd0e773b1bb21236664f9c2dfe56a12d8e446c2ac4f6e52ab8b07027e97e3b268603ed223f80a817823e150f92b19f07463b13066441da
  | 6, 0 => 0xd268f7e7ce2fdbfdb3507d7e9e310d9b9c1be658995298d192a7ff7d6c1d17f668cd66c540cd85c33810c1db36e9258f2ac4f6e51dce88e912ef7747086941f4
  | 7, 0 => 0x995298d1
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x20202020202020200000000000000000000000000000000000000000000000001111111133333333000000000000000000000000000000000000000000000000111111111111111100000000000000000000000000000000000000000000000003030303030303030000000000000000000000000000000000000000000000000033003300330033000000000000000000000000000000000000000000000000000033330000333300000000000000000000000000000000000000000000000000000000333333330000000000000000000000000000000000000000000000000000000022222222
  | 0, 1 => 0x30303030303030300000000000000000000000000000000000000000000000003030303000000000000000000000000000000000000000000000000000000000303000003030000000000000000000000000000000000000000000000000000030203020302030200000000000000000000000000000000000000000000000003000300030003000000000000000000000000000000000000000000000000000222222222222222200000000000000000000000000000000000000000000000022222222000000000000000000000000000000000000000000000000000000002222000022220000
  | 0, 2 => 0x33330000333300000000000000000000000000000000000000000000000000003330333033303330000000000000000000000000000000000000000000000000333000003330000000000000000000000000000000000000000000000000000033223322332233220000000000000000000000000000000000000000000000003322332233003300000000000000000000000000000000000000000000000000330033003300330000000000000000000000000000000000000000000000000033003000330030000000000000000000000000000000000000000000000000003300000033000000
  | 0, 3 => 0x33333333303000000000000000000000000000000000000000000000000000003333333322222222000000000000000000000000000000000000000000000000333333331111111100000000000000000000000000000000000000000000000033333333000000000000000000000000000000000000000000000000000000003333330033333300000000000000000000000000000000000000000000000000333322223333222200000000000000000000000000000000000000000000000033332222333300000000000000000000000000000000000000000000000000003333222200000000
  | 0, 4 => 0x33333333333300000000000000000000000000000000000000000000000000003333333330303030
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x71034b295c5d23ca50194cf290071134a4
  | 5, 0, 0 => 0x123ca242501748f286501c3ca0c2501d5d23ca50205d238a501c6523ca50123ca081501c48f282571240f34a601f5d23ca501c5d230a501c5523ca50185d23ca501c6923c8501748f245501748f2805
  | 5, 0, 1 => 0x1748f141501c5d23c5501748f289501748f281501c5d23ca501e5d23c9501c6d03ca501d5d23c5501c48f142501948f2895
  | 6, 0, 0 => 0x1c5d23c5501748f28957174903ca671748f289601748f281501c5d23ca579c5d23ca671748f281671748f28467175123ca685c5d23ca671748f38a601c48f28257175923ca671748f285671748f2876
  | 7, 0, 0 => 0x1c5d23ca5
  | _, _, _ => 0
def stateW : Nat → Nat
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
  | 0, 0 => 0xe0000000000000000000000000000000000000000000000000000000003ffffff0000000000000000000000000000000000000000000000000000000003fff180000000000000000000000000000000000000000000000000000000000325ce710000000000000000000000000000000000000000000000000000000000e33e0f00000000000000000000000000000000000000000000000000000000001f01ff000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000000000000000000000000000000000000e7f
  | 0, 1 => 0xda318e0000000000000000000000000000000000000000000000000000000000da00000000000000000000000000000000000000000000000000000000000000c03000000000000000000000000000000000000000000000000000000000000018018e00000000000000000000000000000000000000000000000000000000001801800000000000000000000000000000000000000000000000000000000000000e7f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e00
  | 0, 2 => 0x3e0fe000000000000000000000000000000000000000000000000000000000003def1fe0000000000000000000000000000000000000000000000000000000003c0f00000000000000000000000000000000000000000000000000000000000031ccfff00000000000000000000000000000000000000000000000000000000031cc1f000000000000000000000000000000000000000000000000000000000031cc1f0000000000000000000000000000000000000000000000000000000000318c180000000000000000000000000000000000000000000000000000000000300c000
  | 0, 3 => 0x3ff30000000000000000000000000000000000000000000000000000000000003ff0e7f0000000000000000000000000000000000000000000000000000000003fff1800000000000000000000000000000000000000000000000000000000003ff00000000000000000000000000000000000000000000000000000000000003fcfff00000000000000000000000000000000000000000000000000000000003e0fe7f0000000000000000000000000000000000000000000000000000000003e0fe000000000000000000000000000000000000000000000000000000000003e00000
  | 0, 4 => 0x3fffe000000000000000000000000000000000000000000000000000000000003ff318e
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x4a129e000000000000000000000000000000000000000000000000000000000290f7b6000000000000000000000000000000000000000000000000000000000290a1000000000000000000000000000000000000000000000000000000000001254c610000000000000000000000000000000000000000000000000000000000631a0d00000000000000000000000000000000000000000000000000000000000f00db000000000000000000000000000000000000000000000000000000000000f7b600000000000000000000000000000000000000000000000000000000000056b6
  | 0, 1 => 0x2dab39e0000000000000000000000000000000000000000000000000000000002da00080000000000000000000000000000000000000000000000000000000002d0b3040000000000000000000000000000000000000000000000000000000002dab39e000000000000000000000000000000000000000000000000000000000298a19200000000000000000000000000000000000000000000000000000000016f5eff00000000000000000000000000000000000000000000000000000000016f08490000000000000000000000000000000000000000000000000000000001605e24
  | 0, 2 => 0x3f0ff240000000000000000000000000000000000000000000000000000000003def7fe0000000000000000000000000000000000000000000000000000000003d0f7240000000000000000000000000000000000000000000000000000000003ffffff0000000000000000000000000000000000000000000000000000000003ffedfb00000000000000000000000000000000000000000000000000000000039ce5f2000000000000000000000000000000000000000000000000000000000398e5b2000000000000000000000000000000000000000000000000000000000390e520
  | 0, 3 => 0x3ffbb4d0000000000000000000000000000000000000000000000000000000003ff5eff0000000000000000000000000000000000000000000000000000000003ffa9490000000000000000000000000000000000000000000000000000000003ff08490000000000000000000000000000000000000000000000000000000003fcfff60000000000000000000000000000000000000000000000000000000003ffffff0000000000000000000000000000000000000000000000000000000003ffff6d0000000000000000000000000000000000000000000000000000000003ff0849
  | 0, 4 => 0x3ffff6d0000000000000000000000000000000000000000000000000000000003ffbbdf
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 34 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 34 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 34 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 34 then wireAt i else 0
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_61 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_61 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)]]
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
private theorem z4_0 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_16 : ∀ i, 16 ≤ i → i < 26 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 16 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 26 → Z 5 i = true := (range_split z5_0 z5_16)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 16 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 0 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 16 → Z 6 i = true := z6_0
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

namespace S_47_16
def pairsG : List (Nat × Nat) := [(17, 19), (17, 21), (17, 25), (17, 49), (18, 19), (18, 22), (18, 26), (20, 21), (20, 22), (20, 28), (24, 25), (24, 26), (24, 28), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [17, 17, 17, 17, 18, 18, 18, 20, 20, 20, 24, 24, 24, 48, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [19, 21, 25, 49, 19, 22, 26, 21, 22, 28, 25, 26, 28, 49, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0x7fffff
def pool6G : List Nat := [19864560735507, 22063550436117, 26474465269020, 26465875333914, 22067828560662, 26461597209369, 55062422100243, 19865065959699, 22068483332627, 55061885098262, 55078997595418, 57252318550550, 57277987296028, 55061885229590, 61650834822682, 55079534859802, 19864628041235, 19864628107539, 61659391071772, 55062422100502]
def xsM : List Nat := roots_47_16.map (· &&& dom_47_16)
def goalM : Nat := goal_47_16 &&& dom_47_16
def NN : Nat → Nat
  | 3 => 1
  | 4 => 13
  | 5 => 44
  | 6 => 17
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x552483e
  | 4, 0 => 0x8605132e7b57f3a873240d52665cd1f1623820ac335d3dad14c61d48109e81a30d17dbc007b17cb407a9afcc01b9a7580075b94b
  | 5, 0 => 0xeddd1af5d7c737ebc55fbe6fb5819b607f2c0bd67ecb9dca7de2939e7894b1f3783443e773b692c173240d526ae3500052e0b39a5280458e51fd9d194ff0bc2c4c0e0adf40af8d083ccad0903c2876f433320f703152eda52615a1f4251230a620e49f441eae5e501d226cf71bb081c51b543d561a2873311a24c5f91391194e1077f6f70bda6bc40bce8c130b73653d0b51185a09e8339c07261408066cda4905dfb75b01e0734e01b9a75801141bf7
  | 6, 0 => 0xef4cf998eddd1af5d7c737ebc998fb3f98f9af0473abf9b973240d524bce347c3c1f9360301879e728531e57204c65761a287331195e30fe18dba2f41391194e05dfb75b
  | 7, 0 => 0x73240d52
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x333300000000000000000000000000000000000000000000000000000000000011110000333300000000000000000000000000000000000000000000000000000f0f00000f0f000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000aaaa00000000000000000000000000000000000000000000000000000000000000ff0000
  | 0, 1 => 0xaaaa0000aaaa0000000000000000000000000000000000000000000000000000aaaa0000aa000000000000000000000000000000000000000000000000000000aaaa000000000000000000000000000000000000000000000000000000000000aa000000aa000000000000000000000000000000000000000000000000000000888800008888000000000000000000000000000000000000000000000000000055550000ffff000000000000000000000000000000000000000000000000000055550000555500000000000000000000000000000000000000000000000000003333000033330000
  | 0, 2 => 0xf0f00000f0f00000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000eeee0000eeee0000000000000000000000000000000000000000000000000000eeee0000eecc0000000000000000000000000000000000000000000000000000eeee0000cccc0000000000000000000000000000000000000000000000000000eaea0000eaea0000000000000000000000000000000000000000000000000000cccc0000cccc0000000000000000000000000000000000000000000000000000c0c00000c0c00000
  | 0, 3 => 0xff00000000000000000000000000000000000000000000000000000000000000fcfc0000fcfc0000000000000000000000000000000000000000000000000000fafa0000fafa0000000000000000000000000000000000000000000000000000fafa0000f8f80000000000000000000000000000000000000000000000000000fafa0000f0f00000000000000000000000000000000000000000000000000000faf00000faf00000000000000000000000000000000000000000000000000000faaa0000faaa0000000000000000000000000000000000000000000000000000f8f80000f8f80000
  | 0, 4 => 0xfff00000fff00000000000000000000000000000000000000000000000000000ffcc0000ffcc0000000000000000000000000000000000000000000000000000ffc00000ffc00000000000000000000000000000000000000000000000000000ffaa0000ffaa0000000000000000000000000000000000000000000000000000ffaa0000ff000000000000000000000000000000000000000000000000000000ffaa000000000000000000000000000000000000000000000000000000000000ff000000ffff0000000000000000000000000000000000000000000000000000ff000000ff000000
  | 0, 5 => 0xffff0000fcfc0000000000000000000000000000000000000000000000000000ffff0000f0f00000000000000000000000000000000000000000000000000000ffff0000f0000000000000000000000000000000000000000000000000000000ffff0000cccc0000000000000000000000000000000000000000000000000000ffff0000aaaa0000000000000000000000000000000000000000000000000000ffff0000aa000000000000000000000000000000000000000000000000000000ffff000055550000000000000000000000000000000000000000000000000000ffff000000000000
  | 0, 6 => 0xffff0000ff000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x207153
  | 4, 0, 0 => 0x8173c640245d1392881744f50206d12500a2061540289d94500a2578f40205d43d008d74cf40235cf21289e678f50206d13d2881e7555
  | 5, 0, 0 => 0x205d13ce502e81744f502981744950205d13cd50308173c850205d13ca502881754b501744f10350205d13c0502f81744f502d81744f5a2681754f60285d13c4502881e40f500081b44f40288174915
  | 5, 0, 1 => 0x2044f14250205d124250205d344f50205d13c7502e81644f50205d13c15028811245503091744f502895744f502181744f5a2799744f6c2079744f60288174cf502881a44f502a81744f5a2481d5d16
  | 5, 0, 2 => 0x205d13c25028817449502b81744d502981744f502e8113c5502e81744950206d13cd502044f34550205d1349502281744f502881744f502844f1445
  | 6, 0, 0 => 0x205d13c250288174495a205d13c26ae881744f6a2075744f602881744f5a205d13c96a205d13cc6a2079744f6a205d13c86a205d140f602e81744f5a207d744f6b2881744f60205d13cd50285d13c45
  | 6, 0, 1 => 0xa205d13cd6
  | 7, 0, 0 => 0x2881744f5
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
  | 0, 0 => 0x7e200000000000000000000000000000000000000000000000000000000000007e3f8f000000000000000000000000000000000000000000000000000000000071fc7f00000000000000000000000000000000000000000000000000000000000fe3ff00000000000000000000000000000000000000000000000000000000000fe0000000000000000000000000000000000000000000000000000000000000001fff000000000000000000000000000000000000000000000000000000000000000f00000000000000000000000000000000000000000000000000000000000003ff
  | 0, 1 => 0xf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007fffff00000000000000000000000000000000000000000000000000000000007ffff000000000000000000000000000000000000000000000000000000000007e3f8f
  | 0, 2 => 0xe038000000000000000000000000000000000000000000000000000000000000e0000000000000000000000000000000000000000000000000000000000000001c07f000000000000000000000000000000000000000000000000000000000001c070000000000000000000000000000000000000000000000000000000000001c070000000000000000000000000000000000000000000000000000000000000000f000000000000000000000000000000000000000000000000000000000001c0700000000000000000000000000000000000000000000000000000000000000000
  | 0, 3 => 0x70000000000000000000000000000000000000000000000000000000000000000fc3f000000000000000000000000000000000000000000000000000000000000e038f00000000000000000000000000000000000000000000000000000000000e038000000000000000000000000000000000000000000000000000000000000e038000000000000000000000000000000000000000000000000000000000000e0380000000000000000000000000000000000000000000000000000000000000000f00000000000000000000000000000000000000000000000000000000000e0380
  | 0, 4 => 0x7e1f80000000000000000000000000000000000000000000000000000000000071dc700000000000000000000000000000000000000000000000000000000000701c000000000000000000000000000000000000000000000000000000000000701c0f0000000000000000000000000000000000000000000000000000000000701c0000000000000000000000000000000000000000000000000000000000007000000000000000000000000000000000000000000000000000000000000000701fff0000000000000000000000000000000000000000000000000000000000701c00
  | 0, 5 => 0x7fe3f000000000000000000000000000000000000000000000000000000000007fe38000000000000000000000000000000000000000000000000000000000007fe00000000000000000000000000000000000000000000000000000000000007fe07000000000000000000000000000000000000000000000000000000000007fe00f00000000000000000000000000000000000000000000000000000000007fe00000000000000000000000000000000000000000000000000000000000007ffff000000000000000000000000000000000000000000000000000000000007fe000
  | 0, 6 => 0x7ffc00
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x5a200800000000000000000000000000000000000000000000000000000000004816860000000000000000000000000000000000000000000000000000000000316c5d000000000000000000000000000000000000000000000000000000000006e1bb000000000000000000000000000000000000000000000000000000000006e0080000000000000000000000000000000000000000000000000000000000001ff7000000000000000000000000000000000000000000000000000000000000049700000000000000000000000000000000000000000000000000000000000001b3
  | 0, 1 => 0x12649f000000000000000000000000000000000000000000000000000000000012640c00000000000000000000000000000000000000000000000000000000001260080000000000000000000000000000000000000000000000000000000000100404000000000000000000000000000000000000000000000000000000000000401100000000000000000000000000000000000000000000000000000000006d9ff700000000000000000000000000000000000000000000000000000000006d9b6000000000000000000000000000000000000000000000000000000000005a368e
  | 0, 2 => 0x4e93a200000000000000000000000000000000000000000000000000000000004e8000000000000000000000000000000000000000000000000000000000000037edff000000000000000000000000000000000000000000000000000000000037ed7d000000000000000000000000000000000000000000000000000000000037e979000000000000000000000000000000000000000000000000000000000016e5bf000000000000000000000000000000000000000000000000000000000025c9710000000000000000000000000000000000000000000000000000000000048120
  | 0, 3 => 0x79000000000000000000000000000000000000000000000000000000000000006fdbf300000000000000000000000000000000000000000000000000000000005ef7bf00000000000000000000000000000000000000000000000000000000005ef3bb00000000000000000000000000000000000000000000000000000000005ef3aa00000000000000000000000000000000000000000000000000000000005e97a600000000000000000000000000000000000000000000000000000000005a769f00000000000000000000000000000000000000000000000000000000004ed3b3
  | 0, 4 => 0x7f9fe600000000000000000000000000000000000000000000000000000000007ddf7500000000000000000000000000000000000000000000000000000000007d9f6400000000000000000000000000000000000000000000000000000000007b7edf00000000000000000000000000000000000000000000000000000000007b7e4c00000000000000000000000000000000000000000000000000000000007b60080000000000000000000000000000000000000000000000000000000000791ff70000000000000000000000000000000000000000000000000000000000791e44
  | 0, 5 => 0x7ffbfb00000000000000000000000000000000000000000000000000000000007ff3aa00000000000000000000000000000000000000000000000000000000007ff20800000000000000000000000000000000000000000000000000000000007fe97900000000000000000000000000000000000000000000000000000000007fe49f00000000000000000000000000000000000000000000000000000000007fe40c00000000000000000000000000000000000000000000000000000000007ffb6800000000000000000000000000000000000000000000000000000000007fe008
  | 0, 6 => 0x7ffe4c
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 49 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 49 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 49 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 49 then wireAt i else 0
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_47_16 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_47_16 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]]
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
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
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
private theorem z5_32 : ∀ i, 32 ≤ i → i < 44 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 32 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 44 → Z 5 i = true := (range_split (range_split z5_0 z5_16) z5_32)
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
  scr dom_47_16 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_47_16 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_47_16 roots_47_16 goal_47_16 8 := by
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

theorem low_47_16 : Lower dom_47_16 roots_47_16 goal_47_16 8 := S_47_16.noCircuit

namespace S_15_16
def pairsG : List (Nat × Nat) := [(17, 19), (17, 21), (17, 25), (18, 19), (18, 22), (18, 26), (20, 21), (20, 22), (20, 28), (24, 25), (24, 26), (24, 28)]
def r1sG : List Nat := [17, 17, 17, 18, 18, 18, 20, 20, 20, 24, 24, 24]
def r2sG : List Nat := [19, 21, 25, 19, 22, 26, 21, 22, 28, 25, 26, 28]
def mpG : Nat := 0xfff
def pool6G : List Nat := [19864560735507, 26474465269020, 26465875333914, 22067828560662, 26461597209369, 22063550436117, 26461630894873, 22063651492629, 19864628107539]
def xsM : List Nat := roots_15_16.map (· &&& dom_15_16)
def goalM : Nat := goal_15_16 &&& dom_15_16
def NN : Nat → Nat
  | 3 => 3
  | 4 => 6
  | 5 => 5
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x5f52b8b3202b72e10619aa1d
  | 4, 0 => 0x6a2e6bc2202b72e11f58d4260d8d20b506dd279c05c93d22
  | 5, 0 => 0x6a2e6bc2202b72e119ec07501375cbc2111eaaac
  | 6, 0 => 0x202b72e1
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xeeee000000000000000000000000000000000000000000000000000000000000eaea000000000000000000000000000000000000000000000000000000000000cccc000000000000000000000000000000000000000000000000000000000000c0c0000000000000000000000000000000000000000000000000000000000000aaaa0000000000000000000000000000000000000000000000000000000000008888000000000000000000000000000000000000000000000000000000000000555500000000000000000000000000000000000000000000000000000000000033330000
  | 0, 1 => 0xffcc000000000000000000000000000000000000000000000000000000000000ffc0000000000000000000000000000000000000000000000000000000000000ffaa000000000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000fcfc000000000000000000000000000000000000000000000000000000000000fafa000000000000000000000000000000000000000000000000000000000000f0f00000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xec874b85340da33
  | 4, 0, 0 => 0xb85140b85340b8104b987550b86540b8724
  | 5, 0, 0 => 0xb85140b8534b85435b85315cb8535
  | 6, 0, 0 => 0xb8534
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
  | 0, 0 => 0x3f000000000000000000000000000000000000000000000000000000000000000700000000000000000000000000000000000000000000000000000000000000380000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ff80000000000000000000000000000000000000000000000000000000000000fc7
  | 0, 1 => 0xe380000000000000000000000000000000000000000000000000000000000000e000000000000000000000000000000000000000000000000000000000000000e070000000000000000000000000000000000000000000000000000000000000e0000000000000000000000000000000000000000000000000000000000000001f800000000000000000000000000000000000000000000000000000000000001c700000000000000000000000000000000000000000000000000000000000001c0
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x6ff00000000000000000000000000000000000000000000000000000000000002df00000000000000000000000000000000000000000000000000000000000004b90000000000000000000000000000000000000000000000000000000000000090000000000000000000000000000000000000000000000000000000000000024f00000000000000000000000000000000000000000000000000000000000000090000000000000000000000000000000000000000000000000000000000000db00000000000000000000000000000000000000000000000000000000000000b46
  | 0, 1 => 0xfbd0000000000000000000000000000000000000000000000000000000000000fb40000000000000000000000000000000000000000000000000000000000000f6f0000000000000000000000000000000000000000000000000000000000000f240000000000000000000000000000000000000000000000000000000000000dfb0000000000000000000000000000000000000000000000000000000000000bdf00000000000000000000000000000000000000000000000000000000000009d2
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 15 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 15 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 15 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 15 then wireAt i else 0
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_15_16 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_15_16 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]
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
  scr dom_15_16 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_15_16 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_15_16 roots_15_16 goal_15_16 7 := by
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

theorem low_15_16 : Lower dom_15_16 roots_15_16 goal_15_16 7 := S_15_16.noCircuit

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

namespace S_47
def pairsG : List (Nat × Nat) := [(1, 33), (2, 6), (2, 10), (3, 7), (3, 11), (3, 35), (4, 6), (5, 7), (5, 13), (5, 37), (8, 10), (9, 11), (9, 13), (9, 41), (12, 13), (12, 14), (32, 33), (34, 35), (34, 38), (34, 42), (36, 37), (36, 38), (40, 41), (40, 42), (44, 45), (44, 46)]
def r1sG : List Nat := [1, 2, 2, 3, 3, 3, 4, 5, 5, 5, 8, 9, 9, 9, 12, 12, 32, 34, 34, 34, 36, 36, 40, 40, 44, 44]
def r2sG : List Nat := [33, 6, 10, 7, 11, 35, 6, 7, 13, 37, 10, 11, 13, 41, 13, 14, 33, 35, 38, 42, 37, 38, 41, 42, 45, 46]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [4406788295174]
def xsM : List Nat := roots_47.map (· &&& dom_47)
def goalM : Nat := goal_47 &&& dom_47
def NN : Nat → Nat
  | 4 => 1
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xf1fce07
  | 5, 0 => 0xf1fce07
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffff000000000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000f0f00000f0f00000000000000000000000000000000000000000000000000000cccc0000cccc0000000000000000000000000000000000000000000000000000aaaa0000aaaa
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
  | 0, 0 => 0x3ff00000000000000000000000000000000000000000000000000000000000003c0fc00000000000000000000000000000000000000000000000000000000000330c3c000000000000000000000000000000000000000000000000000000000000e003e0000000000000000000000000000000000000000000000000000000000003bb9
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3ff22210000000000000000000000000000000000000000000000000000000003c8fd14000000000000000000000000000000000000000000000000000000000334d3ca0000000000000000000000000000000000000000000000000000000002ae8cfe0000000000000000000000000000000000000000000000000000000001537bb9
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

namespace S_55
def pairsG : List (Nat × Nat) := [(1, 33), (2, 6), (3, 7), (3, 19), (3, 35), (4, 6), (5, 7), (5, 21), (5, 37), (17, 19), (17, 21), (17, 49), (18, 19), (18, 22), (20, 21), (20, 22), (32, 33), (34, 35), (34, 38), (36, 37), (36, 38), (48, 49), (50, 51), (50, 54), (52, 53), (52, 54)]
def r1sG : List Nat := [1, 2, 3, 3, 3, 4, 5, 5, 5, 17, 17, 17, 18, 18, 20, 20, 32, 34, 34, 36, 36, 48, 50, 50, 52, 52]
def r2sG : List Nat := [33, 6, 7, 19, 35, 6, 7, 21, 37, 19, 21, 49, 19, 22, 21, 22, 33, 35, 38, 37, 38, 49, 51, 54, 53, 54]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [4406923039494]
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
  | 0, 0 => 0x3ff00000000000000000000000000000000000000000000000000000000000003e0fe00000000000000000000000000000000000000000000000000000000000318c1e00000000000000000000000000000000000000000000000000000000000c6301e0000000000000000000000000000000000000000000000000000000000000fdd
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3ff09110000000000000000000000000000000000000000000000000000000003e0fe8800000000000000000000000000000000000000000000000000000000039ce5e60000000000000000000000000000000000000000000000000000000002d6b27e00000000000000000000000000000000000000000000000000000000016b5fdd
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

namespace S_55_8
def pairsG : List (Nat × Nat) := [(8, 10), (9, 11), (9, 13), (9, 25), (9, 41), (12, 13), (12, 14), (12, 28), (24, 25), (24, 26), (24, 28), (40, 41), (40, 42), (44, 45), (44, 46), (44, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [8, 9, 9, 9, 9, 12, 12, 12, 24, 24, 24, 40, 40, 44, 44, 44, 56, 56, 56]
def r2sG : List Nat := [10, 11, 13, 25, 41, 13, 14, 28, 25, 26, 28, 41, 42, 45, 46, 60, 57, 58, 60]
def mpG : Nat := 0x7ffff
def pool6G : List Nat := [13233198733581, 26427136937241]
def xsM : List Nat := roots_55_8.map (· &&& dom_55_8)
def goalM : Nat := goal_55_8 &&& dom_55_8
def NN : Nat → Nat
  | 4 => 1
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xc22d231e
  | 5, 0 => 0xc22d231e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00ff0000000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000cc00cc00cc00cc00000000000000000000000000000000000000000000000000aa00aa00aa00aa00
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
  | 0, 0 => 0x7f8000000000000000000000000000000000000000000000000000000000000070700000000000000000000000000000000000000000000000000000000000000e0e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001e
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x7f8100000000000000000000000000000000000000000000000000000000000078788000000000000000000000000000000000000000000000000000000000004e4e40000000000000000000000000000000000000000000000000000000000025243000000000000000000000000000000000000000000000000000000000001293e
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

namespace S_15
def pairsG : List (Nat × Nat) := [(2, 6), (2, 10), (3, 7), (3, 11), (4, 6), (5, 7), (5, 13), (8, 10), (9, 11), (9, 13), (12, 13), (12, 14)]
def r1sG : List Nat := [2, 2, 3, 3, 4, 5, 5, 8, 9, 9, 12, 12]
def r2sG : List Nat := [6, 10, 7, 11, 6, 7, 13, 10, 11, 13, 13, 14]
def mpG : Nat := 0xfff
def pool6G : List Nat := [5506299922950, 8804767696394]
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
  | 0, 0 => 0xf800000000000000000000000000000000000000000000000000000000000000c70000000000000000000000000000000000000000000000000000000000000000f000000000000000000000000000000000000000000000000000000000000036c
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfca0000000000000000000000000000000000000000000000000000000000000e7500000000000000000000000000000000000000000000000000000000000009bf000000000000000000000000000000000000000000000000000000000000076c
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

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
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

namespace S_39_16
def pairsG : List (Nat × Nat) := [(17, 19), (17, 21), (17, 49), (18, 19), (18, 22), (20, 21), (20, 22), (48, 49), (50, 51), (50, 54), (52, 53), (52, 54)]
def r1sG : List Nat := [17, 17, 17, 18, 18, 20, 20, 48, 50, 50, 52, 52]
def r2sG : List Nat := [19, 21, 49, 19, 22, 21, 22, 49, 51, 54, 53, 54]
def mpG : Nat := 0xfff
def pool6G : List Nat := [19864560735507, 22063550436117]
def xsM : List Nat := roots_39_16.map (· &&& dom_39_16)
def goalM : Nat := goal_39_16 &&& dom_39_16
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xd0e4fa84
  | 4, 0 => 0xd0e4fa84
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00000000000000000000000000000000000000000000000000000000000000f0000000f0000000000000000000000000000000000000000000000000000000cc000000cc000000000000000000000000000000000000000000000000000000aa000000aa0000
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_39_16 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_39_16 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]
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
  scr dom_39_16 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_39_16 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_39_16 roots_39_16 goal_39_16 5 := by
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

theorem low_39_16 : Lower dom_39_16 roots_39_16 goal_39_16 5 := S_39_16.noCircuit

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

def isoMv_59 : List (Nat × Nat) := [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem low_59 : Lower dom_59 roots_59 goal_59 6 :=
  lower_iso isoMv_59 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_55

def isoMv_59_4 : List (Nat × Nat) := [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem low_59_4 : Lower dom_59_4 roots_59_4 goal_59_4 6 :=
  lower_iso isoMv_59_4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_55_8

def isoMv_43_16 : List (Nat × Nat) := [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem low_43_16 : Lower dom_43_16 roots_43_16 goal_43_16 5 :=
  lower_iso isoMv_43_16 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_39_16

def isoMv_53_8 : List (Nat × Nat) := [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)]
theorem low_53_8 : Lower dom_53_8 roots_53_8 goal_53_8 5 :=
  lower_iso isoMv_53_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_39_16

def isoMv_57_4 : List (Nat × Nat) := [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)]
theorem low_57_4 : Lower dom_57_4 roots_57_4 goal_57_4 5 :=
  lower_iso isoMv_57_4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_39_16

def isoMv_30 : List (Nat × Nat) := [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]
theorem low_30 : Lower dom_30 roots_30 goal_30 5 :=
  lower_iso isoMv_30 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15

namespace S_63
def pairsG : List (Nat × Nat) := [(1, 33), (2, 6), (2, 10), (3, 7), (3, 11), (3, 19), (3, 35), (4, 6), (5, 7), (5, 13), (5, 21), (5, 37), (8, 10), (9, 11), (9, 13), (9, 25), (9, 41), (12, 13), (12, 14), (12, 28), (17, 19), (17, 21), (17, 25), (17, 49), (18, 19), (18, 22), (18, 26), (20, 21), (20, 22), (20, 28), (24, 25), (24, 26), (24, 28), (32, 33), (34, 35), (34, 38), (34, 42), (36, 37), (36, 38), (40, 41), (40, 42), (44, 45), (44, 46), (44, 60), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [1, 2, 2, 3, 3, 3, 3, 4, 5, 5, 5, 5, 8, 9, 9, 9, 9, 12, 12, 12, 17, 17, 17, 17, 18, 18, 18, 20, 20, 20, 24, 24, 24, 32, 34, 34, 34, 36, 36, 40, 40, 44, 44, 44, 48, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [33, 6, 10, 7, 11, 19, 35, 6, 7, 13, 21, 37, 10, 11, 13, 25, 41, 13, 14, 28, 19, 21, 25, 49, 19, 22, 26, 21, 22, 28, 25, 26, 28, 33, 35, 38, 42, 37, 38, 41, 42, 45, 46, 60, 49, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0x3fffffffffffff
def pool6G : List Nat := [4406788295174, 13202881317638, 4406923039494, 8804969812746, 13215951754509, 19804297366803, 5510594890247, 19804834569235, 22063550236181, 3307276732934, 13203066848778, 18713224087061, 26474212623900, 21998974339590, 8809062663690, 9904279324170, 19825906419210, 4407040936454, 18704735208979, 19864560666131, 18704667837971, 13203133958662, 19799850223366, 9917130475021, 13215917607437, 13233097475597, 13216186960397, 13233366828557, 22011910556949, 26427136937241, 19808675762950, 13216488954893, 5515545616646, 21999109083910, 26461596748313, 13233198733581, 22012447427861, 37435876313606, 48430068730374, 18730403957273, 18730437643545, 26427674139673, 22012447759381, 37435809203722, 22041857428764]
def xsM : List Nat := roots_63.map (· &&& dom_63)
def goalM : Nat := goal_63 &&& dom_63
def NN : Nat → Nat
  | 5 => 5
  | 6 => 68
  | 7 => 201
  | 8 => 102
  | 9 => 11
  | 10 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0xd8a96787a50bf42676cc1efb54fba43053cf423c
  | 6, 0 => 0xecae38b7eb1fa881e580cb8ae276b9c4de9c6949ddf6cc47dd0b5773da5cc8afd4e034e8bb6e1816b9094982b53ec163b476428fb3f33d10b293caa3ad7847e4ac305399abf5bd73ab3e8d4bab05838bab03f1a5a3f576889c9de8c19b7186cd926669ce8808a6cc734bd994723b692c700b04826e9326386aa951c763e7901f5a51a85d5774ee2e4454025040a6ab343e9034be36bd7d74369ccad4326968742c2816dc2b24cf3426b0cd082596955e21ed19f01e3b02061a959f931a84389218f3b34317a77e6316d31cb7162b6fd3158798641433c99a142825f7105e20a00e6fc91f0bbba35a0b6cbda20914f67308bd4ac908010b2a025334cb0169a0a4
  | 6, 1 => 0xfc40a38ff8745fd1f443b25af3175066
  | 7, 0 => 0x350ff6a134171dd82f3594f12e2327552ce139a22cadc4612b811d732a9cb57b2a56170029d10a3227e01bb227795cd12750b4f6273a868025d992dc2521f0fe247367df22a61e2c2289ec0b1ffd86e11fad31dc1fa565611f15ac8f1e8cb9de1e62464a1e5d9f271e4008941daeb8c11c96ea491c475fcd1a9f19ac19d2796319ba301a18556ec7184c7d9218131534176346e0175c2c75171f64aa16b01e54136dc904109d1e430ecc23a60db753420d570f570c8c4ccf0b985bbe0b7002330aad79ad0a7a55280989c7c309199978079341c50790b29f062e761d06237d4e057ed23604c5847804c021da03f8e99a028de01e02867f1c015fcb3e00b34936
  | 7, 1 => 0x6db3cd8b6d04869a6c41d5016c0eb07c6a27cc6b69a1a2a4694fc71e67b7d8a266e47320657fa7266532bf646407b8f162c7c6f4624d6d5b60617b6c601d48af6008d5905f35ba935f18482b5e394d3c5dd08b735c3b8dfc5c33c1815b6976d55aea31985ad883ea592546695810d46d578e67bf570c318b5707fb6756488c3a54dad9b2548e6dd84dffcf964d2ff4d14c0122844b24895f4b0d87ba4abd1d0b49c0fcf447946ea947703dcb46cdf1d245a7f598449785304493839c43415cc542672086420d2e5640ef423c405ffdff40419ef23d67d4943d4e5b033b3e76333961b02b3956e3ad3778a28c36d69bdf36816bd0363e94ef361d50e735c94199
  | 7, 2 => 0xe82ca1a0e5dbe277e5b7261de171d949df3d5635ddf8e307dd36d6a1db711277d9891486d9612da7d53d3f77cfaaeb5dcf010decce1f1d8dc69fce5ec5ff83fec5736c6ac543b096c0f590b7bd46bf61bc1a5d6dbc042ef7b7dce78eb6f964b2b27690e8b18a5954b052e84bb0231954af9cc68aac9944f7ac41cfbeab79c6cb9ed600aa97d2f0438f74f0a98f5f11de8ee425888e183c1b8dd7584d8d94f5ad894ebb5e888f7ea4879add67864f591484efe6a783e740ff8229ac847d794f967b494d3177abcbfa753360a074f8ca7a74e00fc47406feac73d644c773be3a8b739a99807369c76672579db97158096d711e905270607efa6fb8decd6ee8713b
  | 7, 3 => 0xfe2b8d04fd80eb38fd7e81a8f5ab4c3ff582e6acf44935f4efa77ca6ed3bc136ea6cc730
  | 8, 0 => 0x8e7679718d5eaaf98a81f0ca8968a0cb830766bf79e15a286e834bca6d9b14bb6c4b6e045d6275f4567ee6cd51e81d5150c4b4ed500139404dd111674ca60af44c4c79c449e125c645f6b58444d9dfff43b42571430588364214fad13ee6de3d3dc32c533c39fd5e3c21f90f3a8b1a6536c744ae36b6da9233d93c6b33ab0d083264f194302ca7772ba0a43a2b81626d2a6cf07129c478db2964176b28a4a83e2838c79a26396ad4233e519822521a042064873a1d73f5661ca0b18319f08aad19deb3e2192a0dd6170db67f123247970fd4c3f50faa77070e7dd0190e783ebe0d9a92370d52c9a60c167f100bb2ffb10afb5dd3089ab0f305869eb1033a727c
  | 8, 1 => 0xfe12eeb4fcf8d17ff9acd0faf646c3bff22186e7f05fc8f2f053c1fdec164c1eea555bf2e8b03ee3e4625a30e1283faae07b344edfb32b5bd9eccea3d986de71d87f9952d7c2c847d697c1d4cecb96dfc8d8951dc398766ec1c5a5bebfa41077bcc8e334ba88bda4b837fe7babe5308aa840633ca6910249a5d7b751a3f2435da07b39919b1dd7b097012b849351acbb906d26118fa2db65
  | 9, 0 => 0xc2afde01b6be76349b34b1217e1a8a56764e5f61705b5d9f5fbac6fd5cde0cce1561a43a1142fa410e7e1513
  | 10, 0 => 0x42b779a3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf000f000f000f000000000000000000000000000000000000000000000000000aa00aa00aa00aa0000000000000000000000000000000000000000000000000033003300330033000000000000000000000000000000000000000000000000000f000f000f000f0000000000000000000000000000000000000000000000000000ffff0000ffff000000000000000000000000000000000000000000000000000000000fff0fff000000000000000000000000000000000000000000000000000000000f0fffff0000000000000000000000000000000000000000000000000000000000ffffff
  | 0, 1 => 0xa0a0a0a0a0a0a0a000000000000000000000000000000000000000000000000033333330333333300000000000000000000000000000000000000000000000003330333033303330000000000000000000000000000000000000000000000000303333303033333000000000000000000000000000000000000000000000000030303030303030300000000000000000000000000000000000000000000000000ffffff00ffffff00000000000000000000000000000000000000000000000000ff00ff00ff00ff00000000000000000000000000000000000000000000000000ff000000ff0000
  | 0, 2 => 0x113311331133113300000000000000000000000000000000000000000000000011113333111133330000000000000000000000000000000000000000000000000fff0fff0fff0fff0000000000000000000000000000000000000000000000000ff00ff00ff00ff00000000000000000000000000000000000000000000000000f0fffff0f0fffff0000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000000f0f00000f0f00000000000000000000000000000000000000000000000000000f000f000f000f00
  | 0, 3 => 0xa000a000a000a0000000000000000000000000000000000000000000000000005f5f5f5f5f5f5f5f00000000000000000000000000000000000000000000000055ff55ff55ff55ff0000000000000000000000000000000000000000000000005555ffff5555ffff0000000000000000000000000000000000000000000000005555555555555555000000000000000000000000000000000000000000000000333333333333333300000000000000000000000000000000000000000000000013331333133313330000000000000000000000000000000000000000000000001133333311333333
  | 0, 4 => 0xaaaa0000aaaa0000000000000000000000000000000000000000000000000000aaa0aaa0aaa0aaa0000000000000000000000000000000000000000000000000aa88aa88aa88aa88000000000000000000000000000000000000000000000000aa00aa00aa00aa00000000000000000000000000000000000000000000000000aa000000aa000000000000000000000000000000000000000000000000000000a8a8a8a8a8a8a8a8000000000000000000000000000000000000000000000000a0aaa0aaa0aaa0aa000000000000000000000000000000000000000000000000a0a0a0a0a0a0a0a0
  | 0, 5 => 0xeccceccceccceccc000000000000000000000000000000000000000000000000cfcfcfcfcfcfcfcf000000000000000000000000000000000000000000000000ccffccffccffccff000000000000000000000000000000000000000000000000cccccccccccccccc000000000000000000000000000000000000000000000000aaaaaaaaaaaaaaaa000000000000000000000000000000000000000000000000aaaaaaaaaa000000000000000000000000000000000000000000000000000000aaaaaaaaa0a00000000000000000000000000000000000000000000000000000aaaaaaaaa000a000
  | 0, 6 => 0xf000f000f000f000000000000000000000000000000000000000000000000000f0000000f0000000000000000000000000000000000000000000000000000000eeeecccceeeecccc000000000000000000000000000000000000000000000000eeeceeeceeeceeec000000000000000000000000000000000000000000000000eecceecceecceecc000000000000000000000000000000000000000000000000eecccccceecccccc000000000000000000000000000000000000000000000000ecececececececec000000000000000000000000000000000000000000000000ececccccececcccc
  | 0, 7 => 0xfaf0faf0faf0faf0000000000000000000000000000000000000000000000000faf0aa00faf0aa00000000000000000000000000000000000000000000000000faaaf000faaaf000000000000000000000000000000000000000000000000000f0fff0fff0fff0ff000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000000f0f00000f0f00000000000000000000000000000000000000000000000000000f0c0f0c0f0c0f0c0000000000000000000000000000000000000000000000000f00ff00ff00ff00f
  | 0, 8 => 0xff000000ff000000000000000000000000000000000000000000000000000000fcfcfcfcfcfcfcfc000000000000000000000000000000000000000000000000fcfcccccfcfccccc000000000000000000000000000000000000000000000000fcfc0000fcfc0000000000000000000000000000000000000000000000000000fcccfcccfcccfccc000000000000000000000000000000000000000000000000fcccccccfccccccc000000000000000000000000000000000000000000000000fc00fc00fc00fc00000000000000000000000000000000000000000000000000fafaf0f0fafaf0f0
  | 0, 9 => 0xffccccccffcccccc000000000000000000000000000000000000000000000000ffcc0000ffcc0000000000000000000000000000000000000000000000000000ffaaff00ffaaff00000000000000000000000000000000000000000000000000ffa0ffa0ffa0ffa0000000000000000000000000000000000000000000000000ffa0ff00ffa0ff00000000000000000000000000000000000000000000000000ff0fff0fff0fff0f000000000000000000000000000000000000000000000000ff0aff0aff0aff0a000000000000000000000000000000000000000000000000ff00ff00ff00ff00
  | 0, 10 => 0xfffcfffcfffcfffc000000000000000000000000000000000000000000000000fffcccccfffccccc000000000000000000000000000000000000000000000000fffc0000fffc0000000000000000000000000000000000000000000000000000fff0fff0fff0fff0000000000000000000000000000000000000000000000000fff0ff00fff0ff00000000000000000000000000000000000000000000000000fff0f0f0fff0f0f0000000000000000000000000000000000000000000000000fff00000fff00000000000000000000000000000000000000000000000000000ffccffccffccffcc
  | 0, 11 => 0xfffffffff0c0f0c0000000000000000000000000000000000000000000000000fffffffff000f000000000000000000000000000000000000000000000000000fffffffff0000000000000000000000000000000000000000000000000000000ffffffffaa000000000000000000000000000000000000000000000000000000ffffffffa0a00000000000000000000000000000000000000000000000000000ffffffffa000a000000000000000000000000000000000000000000000000000ffffffff00000000000000000000000000000000000000000000000000000000ffff0000ffff0000
  | 0, 12 => 0xfffffffffff00000000000000000000000000000000000000000000000000000ffffffffffcc0000000000000000000000000000000000000000000000000000ffffffffff000000000000000000000000000000000000000000000000000000fffffffffcfc0000000000000000000000000000000000000000000000000000fffffffffc00fc00000000000000000000000000000000000000000000000000fffffffff0f00000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x59b0acd145b2e162b06b66c2c36516f5870b15ad9b0e161b5
  | 6, 0, 0 => 0x18ec4856689300b12162b5049805876b158904c02c3b58ad50960182c3b586c4b00b362a3d58ad805876b15a912c02cd8a8b0d9560196c4858ac9300c36242c5649805bb0ed62b12c02f5890ecd9a6b36244576cd5b80b361c3758ad8060b12159a24c0325890b15926
  | 6, 0, 1 => 0x17a43b56681b00bd6242b34498059a8dd59a06c02cd89109d9b60162a3758ac1300b2acd12120d8059b1520ac36c02ed890ed59a6018ec3b586c4b00b121dab50698059b0f161b0ec0315890b159260196c4876acd300b36243b56658059b0b159508c0243b58ad4036
  | 6, 0, 2 => 0x17ac5486b15b00b362a2c56358065b151bac56c00059b0b159450166c5486b0db00b12162b2401805eb0dd62b08c02cd86eb0d846017ac546eb0db000166c3858ad4059906cd1206c02cd8a8acd156016243b56680b00b96243b5669805eb0ed61b12c0305858ac9096
  | 6, 0, 3 => 0x165bac56101b00b36243b56618059b06cd1212c02cd46eb0d8360166c5458aca300b56243b56698059b121dab1cc02cd876c15896016561b24241b00b35643b586d805eb0b159212c02c4876acd0260162a3758ad4300c16243b3669805890ed5a934c02cc074b15896
  | 6, 0, 4 => 0x166a4358ac1b00bd21dac360d805eb151bab34c02cd8a8dcd9a6
  | 7, 0, 0 => 0x166c4876e8d9a70166c486eacd1270166c5490dd61b70002cac56484836016243b6eb158270166c4876acf9a70166c4876b561b70166c4876ad31a70166c3b58ac88970002ed890ed62b6018ec5490ed62b70166c4876b158c70166c485cb0d9270166c5690ed62b7016642c564880370166c4876acd0a7
  | 7, 0, 1 => 0x2cd856689096b36244576b15a480182c3b74b158970166c4876b0d8470002fd890ed62b60166a488cb158370166c4858ace1270002cd46eb158360166c3c76b158770166c4876bd62b70166c48766cd127018ec488ced62b7016643b6eacd037018ec5090ed62b70166c4858ace927000315890ed62b6
  | 7, 0, 2 => 0x16644576b15a770192c5090ed62b70166a3b58ac48370166c4884ed62b70166c5458ac90970166c2c564888970166c4876ace9a7b36243b74cd62b80182c488aed62b70165dba58ad38970002cc880e962b60166c3b6eb0d8970002cbb56684836b36244376b15a780166c3b58ad08970166c4888b15927
  | 7, 0, 3 => 0x166c3b6ab158970166c4758ac9097016643b58ac58370186c488ced62b70166c4858ac90570002f4876b15836016633b58ac48370166c4876ace1a7016683b58ac48370002f5890b159260196c5490ed62b70166c5058ac90970002cd8a8dd59a60002cd8a8e562b60166c4858ad19270166c5390b15927
  | 7, 0, 4 => 0x2c4876b158160166c4876b0d9170002e5890ed62b60166c2c56484877016643f76b15837016643b58ac78370002f5890ed59a60166c4876acd1570166c54a0ed61b70166c4876ad19a70166c4376b158970166c509115dab7018ec5290ed62b7016644776ad39a70166c5090edaab70166c4576b15897
  | 7, 0, 5 => 0x182c4876e961b70166c485ab159270166c4882b15927016642c564848370166c5176b158970002cd890ed82b6017ac5090ed62b70166c4876b15977000305876b158960166c4776acd0970165dac56804837018ec488eed59a70002cc8586c90360002cd8a8b159560166c2c56809097017ac5490ed62b7
  | 7, 0, 6 => 0x16643b566890370166c5486dd62b70166a4876b0d8370166c3c76b0d8970166c48566890970166c5490b0d9270166c48586c9117017ac4876dd61b70002cd878b158760166c4876b159670002cc8766cd0360166c3b5680d097016642c564878370166c4f76b158970166c4a90acd1270002cd8906cd126
  | 7, 0, 7 => 0x166c546eb15a77016643b66b158370166c3b74b0d8970166c3758ac90970166c4866b159270166c4990b15927016643b58ac20370166c3b58ad3097016684876b0d8370002cd890ed7ab60166c488cb0d9270166c5090b0d9270166c4876b0d8770166c3b58ad289700031d876b158960166c2c569c9097
  | 7, 0, 8 => 0xb3626c880ed62b80166c4876d961b7017ac4886ed62b70166c4876b158d70002cd89109dab60166c4886ed61b70166c5290ed61b70166c54a2dd62b70166c3b569cd0970166c487ced62b70166c488aed61b70166c3b5690d097b36274876e562b80166c3b586c90970166c5490ecd9a70166c2c56484867
  | 7, 0, 9 => 0x166c4876b0d8a701663bb58ad38970166c546eb15a670166c4e90ed61b70166c4476b158970166c4876c962b70182c4876b158970166c4076b15897016643b58ad10370166c5190ed61b70002c4876b15826000305890ed61b60002c4876b15a960166c4862b159270002cd896ed62b6016243b6eb15a87
  | 7, 0, 10 => 0x2cd8a8dd61b6016644376b158370166a4876acd037017ac4876dd59a70166c4876dcd9a70166c4876e561b70002cd8586c90960166c2c565490970166c3f76b158970166c3b58ac98970002d5890ed62b60166c48586c91070166c3b58ac78970166c3c58ac90970166c5790ed61b7016643b6eb0d837
  | 7, 0, 11 => 0x305890ed59a6016643b5680d0370166c4776b0d8970166c488ced9ab70002cd8a90d62b60166c4876b0d8b70166c487aed62b70002f5890ed61b60166c4876d959a70166c4876b0d9570166c4876d162b70002cd86eb158460166c4878ed61b70166c3b74acd0970002f58a8dd62b60166c2e58ac9097
  | 7, 0, 12 => 0x16643b586c90370002c4876b15a860166bc876b158370166c2c56484847016643b58ad303700032d890ed62b60002cd590ed62b60166c4858ad29270166c5190ed59a7
  | 8, 0, 0 => 0xb36243b6ab15a78018ec488eed62b7b36264876b15a080166c4876b158b7b3627c88eed62b80002f5890ed62b60166c4676b15897b36284876b15a580166c4876b159570166c5076b15897b362a4876b15a680166c4876b15a370166c5390ed62b7016644776b15a770166c5476b158970166c4878ed62b7
  | 8, 0, 1 => 0x16643b58ac90370166c4858ac9097b36284876e562b80002cc876b0d8360166c3b58ad00970166c4876b159e70166c4a90b159270002cd890b0d926b36244376dd62b80166c3b58ac48770166c487eed62b70166c4876b159370166c4876b158f70166c4876b158870166c4876b962b70166c4776b15897
  | 8, 0, 2 => 0x166c4876b158470166c5090ed61b70166c3b58ad3897b362a4876e962b80166c3b58ad20970166c4876acd1270166c5490ed61b70166c4876e959a70166c5490dd62b7b36244688ed62b80002cd890ecd9a60166c4858ac90f70166c485cb15927b36243b6eb15a780166c4882ed62b7b3626c876b15a78
  | 8, 0, 3 => 0x166c4876dd61b70002cc876acd0360002cd890acd126b36243b58ad3928b36243b74b15a480002cc858ac9036b36243b58ad00980166c54a0ed62b70166c4876b15a27b36244776b159280166c488eed61b70166c3b6eb15897b36284876b159280166c4876cd62b7b36244676e962b8b36284876e962b8
  | 8, 0, 4 => 0xb36243b66b15a480166c4d90ed62b70166c5190ed62b7000305890ed62b6016643b58ad00370166c4876d962b70166c4886ed62b70166c488aed62b70166c4876d562b70166c5490ed59a70166c3b74b15897016684876b158370166c4876b158770166a4876b158370166c4858ac9117017ac4876dd62b7
  | 8, 0, 5 => 0x166c4876dd59a70002cd858ac9096b362a4876b15a78b36243b58ac90980166c4876ad39a70166c4876b0d9270166c5790ed62b7016643b6eb158370166c4876b159f7b3629c876e962b80166c4876b15a67b36244676b15a08b36284876b15a08b362a4876b15a080166c4876ad01a70166c4e90ed62b7
  | 8, 0, 6 => 0xb36284876dd62b80166c4876b159c70002cd8a8dd62b6b362a4876dd62b8b36284876b15a78b362a5190ed62b8
  | 9, 0, 0 => 0x59b121db758adecd890ed62b4ef66c4876b15a07b36284876b15bd9b15243b58adc059b121dab34c02cc876b158360166c4858ac9359b121dac5649ecd890edd2c56e02cd890ed61b6
  | 10, 0, 0 => 0x2cd890ed62b6
  | _, _, _ => 0
def stateW : Nat → Nat
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
  | 0, 0 => 0x7006038000f800000000000000000000000000000000000000000000000000000000000f00f790000000000000000000000000000000000000000000000000007106238f00f810000000000000000000000000000000000000000000000000000f01e07f0007f00000000000000000000000000000000000000000000000000000ffe000fffff00000000000000000000000000000000000000000000000000000001fff1ffff00000000000000000000000000000000000000000000000000000001c7ffffff000000000000000000000000000000000000000000000000000000003fffffff
  | 0, 1 => 0xf1e079000000000000000000000000000000000000000000000000003f1fe3f8ffff81000000000000000000000000000000000000000000000000003f11e3f8f1ff8100000000000000000000000000000000000000000000000000381fe3c0ffff8100000000000000000000000000000000000000000000000000381183c0f1f0010000000000000000000000000000000000000000000000000007fffe3fffffff0000000000000000000000000000000000000000000000000007f07e3ff00fff0000000000000000000000000000000000000000000000000007f0003ff00000
  | 0, 2 => 0x3f1fe3f8fe1f81000000000000000000000000000000000000000000000000003f1fe3f80fff81000000000000000000000000000000000000000000000000003ff1fffff1ffff000000000000000000000000000000000000000000000000003f01e1f801ff800000000000000000000000000000000000000000000000000038ffffc7ffffff0000000000000000000000000000000000000000000000000038f19fc7f1f07f0000000000000000000000000000000000000000000000000038f001c7f0000000000000000000000000000000000000000000000000000000380181c001f000
  | 0, 3 => 0x3ffffffffff0ff000000000000000000000000000000000000000000000000003ffffffffe1fff000000000000000000000000000000000000000000000000003fffffff0fffff000000000000000000000000000000000000000000000000003fffffff0e1086000000000000000000000000000000000000000000000000003f1fe3f8ffff81000000000000000000000000000000000000000000000000003f1fe3f8ffff81000000000000000000000000000000000000000000000000003f1fe3f8ffff81
  | 0, 4 => 0xf00000000000000000000000000000000000000000000000000000000000000001ef00000000000000000000000000000000000000000000000000000000000001e078000000000000000000000000000000000000000000000000000000000001e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f780000000000000000000000000000000000000000000000000000000000f00f790000000000000000000000000000000000000000000000000000000000000f00
  | 0, 5 => 0xe01c0700007e0000000000000000000000000000000000000000000000000038f19fc7f1f07f0000000000000000000000000000000000000000000000000007f07e3ff00fff0000000000000000000000000000000000000000000000000000e01c0700007e0000000000000000000000000000000000000000000000000000000000f1ef79000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 0, 6 => 0xe00000e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e01c07f0007e0000000000000000000000000000000000000000000000000000e01c0701ef7e0000000000000000000000000000000000000000000000000000e01c0701e07e0000000000000000000000000000000000000000000000000000e01c0700007e0000000000000000000000000000000000000000000000000000e01c07000f7e0000000000000000000000000000000000000000000000000000e01c0700007e
  | 0, 7 => 0x70e60380fef80000000000000000000000000000000000000000000000000000700003801e00000000000000000000000000000000000000000000000000000000e0000fe00000000000000000000000000000000000000000000000000000007fe7e3ffe0fff00000000000000000000000000000000000000000000000000070e60380e0f80000000000000000000000000000000000000000000000000000700003800000000000000000000000000000000000000000000000000000000000e00000e00000000000000000000000000000000000000000000000000000000fe1e07fe007f
  | 0, 8 => 0x380001c00000000000000000000000000000000000000000000000000000000007ee7c3f0e0ffe0000000000000000000000000000000000000000000000000007e01c3f00007e0000000000000000000000000000000000000000000000000007e0003f0000000000000000000000000000000000000000000000000000000000ee1c070e007e0000000000000000000000000000000000000000000000000000e01c0700007e00000000000000000000000000000000000000000000000000000e00000e000000000000000000000000000000000000000000000000000000070e6038fe0f80
  | 0, 9 => 0x38e01dc700007e0000000000000000000000000000000000000000000000000038e001c700000000000000000000000000000000000000000000000000000000380f81c0fff00000000000000000000000000000000000000000000000000000380f81c00fff0000000000000000000000000000000000000000000000000000380f81c00ff0000000000000000000000000000000000000000000000000000038ff9fc7fff07f00000000000000000000000000000000000000000000000000380f81c0fff07900000000000000000000000000000000000000000000000000380f81c00ff000
  | 0, 10 => 0x3feffdff0ffffe000000000000000000000000000000000000000000000000003fe01dff00007e000000000000000000000000000000000000000000000000003fe001ff000000000000000000000000000000000000000000000000000000003f0fe1f80fff80000000000000000000000000000000000000000000000000003f0f81f80ff000000000000000000000000000000000000000000000000000003f0e61f80e0f80000000000000000000000000000000000000000000000000003f0001f80000000000000000000000000000000000000000000000000000000038ef9dc70ff07e
  | 0, 11 => 0x3ffffe000e0000000000000000000000000000000000000000000000000000003ffffe000e0000000000000000000000000000000000000000000000000000003ffffe00000000000000000000000000000000000000000000000000000000003ffffe00000000000000000000000000000000000000000000000000000000003ffffe00000000000000000000000000000000000000000000000000000000003ffffe00000000000000000000000000000000000000000000000000000000003ffffe00000000000000000000000000000000000000000000000000000000003ff001fff00000
  | 0, 12 => 0x3ffffff8000000000000000000000000000000000000000000000000000000003fffffc7000000000000000000000000000000000000000000000000000000003fffffc0000000000000000000000000000000000000000000000000000000003ffffe3f000000000000000000000000000000000000000000000000000000003ffffe000e0000000000000000000000000000000000000000000000000000003ffffe38000000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x340681a200d8a0000000000000000000000000000000000000000000000000001302609b00d690000000000000000000000000000000000000000000000000001102208a00c010000000000000000000000000000000000000000000000000000300601900061000000000000000000000000000000000000000000000000000007fe00077bdf00000000000000000000000000000000000000000000000000000000df70b5be00000000000000000000000000000000000000000000000000000000c556f3be000000000000000000000000000000000000000000000000000000001b3677be
  | 0, 1 => 0x8308641d1a071000000000000000000000000000000000000000000000000000912a248e3ce01000000000000000000000000000000000000000000000000000910a248e18c01000000000000000000000000000000000000000000000000000812a240c3ca010000000000000000000000000000000000000000000000000008108240c18001000000000000000000000000000000000000000000000000000377fe1bb77fff0000000000000000000000000000000000000000000000000003706e1bb00deb000000000000000000000000000000000000000000000000000370001bb00420
  | 0, 2 => 0x25182328a80c0100000000000000000000000000000000000000000000000000240aa3200b4a01000000000000000000000000000000000000000000000000001bf1fedff1bdff000000000000000000000000000000000000000000000000001bc1f8de61bd9e0000000000000000000000000000000000000000000000000018b7fec5d7fbff0000000000000000000000000000000000000000000000000018b196c5d1b0750000000000000000000000000000000000000000000000000018b000c5d0802000000000000000000000000000000000000000000000000000188190c441b014
  | 0, 3 => 0x20000024200000000000000000000000000000000000000000000000000003efddff7ddb0f70000000000000000000000000000000000000000000000000037fd7fbfbc1def0000000000000000000000000000000000000000000000000036cfffb60f7bdf0000000000000000000000000000000000000000000000000036cd59b60c1086000000000000000000000000000000000000000000000000002d1aa368ebce01000000000000000000000000000000000000000000000000002d18a368e98c0100000000000000000000000000000000000000000000000000251aa328ab4e01
  | 0, 4 => 0x9300049f08420000000000000000000000000000000000000000000000000000902a04863ef18000000000000000000000000000000000000000000000000000822844153e378000000000000000000000000000000000000000000000000000802804043e21000000000000000000000000000000000000000000000000000080000404080000000000000000000000000000000000000000000000000000001222409326f780000000000000000000000000000000000000000000000000001322609b24f690000000000000000000000000000000000000000000000000001022008224f08
  | 0, 5 => 0x12e75c971673fe000000000000000000000000000000000000000000000000001af5ded7d5b1ff0000000000000000000000000000000000000000000000000013f57e9fb43dff0000000000000000000000000000000000000000000000000012e55c971431fe000000000000000000000000000000000000000000000000000932a649f3ef79000000000000000000000000000000000000000000000000000932a640c18841000000000000000000000000000000000000000000000000000932a608a10c41000000000000000000000000000000000000000000000000000932a600834a41
  | 0, 6 => 0x240e01200e42000000000000000000000000000000000000000000000000000024080120080000000000000000000000000000000000000000000000000000001bf55cdff4b5fe000000000000000000000000000000000000000000000000001be7fcdf77fffe000000000000000000000000000000000000000000000000001ae7dcd757f3fe000000000000000000000000000000000000000000000000001ae55cd754b1fe0000000000000000000000000000000000000000000000000013e77c9f367ffe0000000000000000000000000000000000000000000000000013e55c9f3435fe
  | 0, 7 => 0x2f4ee97a6fef9a000000000000000000000000000000000000000000000000002f4a817a6be610000000000000000000000000000000000000000000000000002d3e0169fec62000000000000000000000000000000000000000000000000000277e6f3bbe4feb00000000000000000000000000000000000000000000000000274e693a2e4f8a000000000000000000000000000000000000000000000000002748013a28040000000000000000000000000000000000000000000000000000264e49320e438a00000000000000000000000000000000000000000000000000243e07219e4261
  | 0, 8 => 0x3c8801e44880000000000000000000000000000000000000000000000000000037ef7dbf3e7ffe0000000000000000000000000000000000000000000000000037ed5dbf3c35fe0000000000000000000000000000000000000000000000000037e801bf3804200000000000000000000000000000000000000000000000000036ef5db71e73fe0000000000000000000000000000000000000000000000000036ed5db71c31fe00000000000000000000000000000000000000000000000000348f11a40e7214000000000000000000000000000000000000000000000000002f7e697bfecfaa
  | 0, 9 => 0x3eed5df75cb1fe000000000000000000000000000000000000000000000000003ee801f7588020000000000000000000000000000000000000000000000000003dbf91edfff634000000000000000000000000000000000000000000000000003d8fb1ec6fff1c000000000000000000000000000000000000000000000000003d8f91ec6ff614000000000000000000000000000000000000000000000000003cbf97e5dff275000000000000000000000000000000000000000000000000003cbf97e5dff275000000000000000000000000000000000000000000000000003c8f91e44ff214
  | 0, 10 => 0x3feffdff7ffffe000000000000000000000000000000000000000000000000003fed5dff7cb5fe000000000000000000000000000000000000000000000000003fe801ff788420000000000000000000000000000000000000000000000000003fcff9fe6fff9e000000000000000000000000000000000000000000000000003fcf91fe6ff614000000000000000000000000000000000000000000000000003fce69fe6ecf8a000000000000000000000000000000000000000000000000003fc801fe688400000000000000000000000000000000000000000000000000003eefddf75ff3fe
  | 0, 11 => 0x3fffff328f4bcb000000000000000000000000000000000000000000000000003fffff208f4a41000000000000000000000000000000000000000000000000003fffff20890841000000000000000000000000000000000000000000000000003ffffe40c18841000000000000000000000000000000000000000000000000003ffffe08a10c41000000000000000000000000000000000000000000000000003ffffe00834a41000000000000000000000000000000000000000000000000003ffffe00810841000000000000000000000000000000000000000000000000003ff801fff88420
  | 0, 12 => 0x3ffffffee98c41000000000000000000000000000000000000000000000000003ffffff7d98861000000000000000000000000000000000000000000000000003fffffe4c98841000000000000000000000000000000000000000000000000003fffffbfb90c61000000000000000000000000000000000000000000000000003fffffa48f7a55000000000000000000000000000000000000000000000000003fffff3aa90c41
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 102 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 102 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 102 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 102 then wireAt i else 0
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 9 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 5 => 12
  | 6 => 252
  | 7 => 1205
  | 8 => 392
  | 9 => 23
  | _ => 0
def CH : Nat → Nat → Nat
  | 5, 0 => 0xc808d0e5b5ac8ac8ab05838ba96861b28808a6cc5ad354c7430eebd142b779a337d678083159b7c220120f1214d65dcb
  | 6, 0 => 0x2404b6a122ed54d2220e446c22019fc721e5a9d521c8d1d2213869ba1fb6ab771f38f42b1eec17a31e6206c71d4df85b1d4b60a21d49aee91d1bbc4e1aa400a01a3314ca19b3c5f0190722ad18c1be671814a6cb17c1f8db1702d2d716eb24cf15c109ba154d78621542e32e151ef48314e6f1751370a1b11356a1bd12443421118a8294116dadca114c834e11027a490faa77070fa22a3f0e985d890e2dbbf60d55e2950ce9780a0ce13a310cb5ddac0b953d340b931def0ab802d40a8596bb09d16e6b09ce0fd1099cda1a09151ea908f317a508531ca106ff5f220646c5fa0637937b06165d76052feefa04ec92b904465ad304184f140416c31802df97aa
  | 6, 1 => 0x654b1c8a637eec3e619ad28a6118463c60bfdce05fe3d1285f6a6de05f51ec415e2f68925df28f965d4c3cf25bdbb2565a657cac596b204c57530f6054de6a7c54b15716536178d752ceb4a251ef299250b682174eb1559f4df047f44c30865f4be3ec904bd49b704b24895f48d5c85748cbb65d46d4578c4545237444978530443dd3da42b779a341c1c8b240d449c74089014b40722d163f8ea66a3f8b279b3f4f329f3c4ccf4d3c21f90f3a86eed13564c8b7355d8c93322b6ad731f77dc03189da0b3146429630599af92e270de82deeb1d52b81626d2b3f49ac29f1c6ed28a4a83e2884fdf828605c1f2812ed9e28009fa525cdfa3e256eb4e124ade100
  | 6, 2 => 0x9a26a67a99308b4d982206ac971615d0965b117d95b93d7692c8963a9218353891e35d1e91d13869919f4e7b919da6ed8f0b27718dca4a668da68eea8d5eaaf98ac846398a81f0ca8a01964f89a88ca9888e159487b0e4ec862ff0fc8576a6048564247784efe6a783bd844e83a29fc082ecdd3b82c4fa708282f4807fa63a517f8ad48b7f78bc997e34a38b7d64c8c67d37c1197c1983bb7b042d447abeb30b79e15a2877ed7ef27746be7b75e89c1f75413da674e00fc4743d2db1739a2d4a726b6eb971acb963717e14fb6f696f746ecfff346e5661bc6e194f236baeb6f76a8772f96827d6b967db214e67b453a367aab8ca6741623a657fa72665735823
  | 6, 3 => 0xfd890f6cfd80eb38fd4ecf59fa5cc4c9f9acd0faf9645a73f5fcd64df465566cf3ae80f5f2c2755af1d8600ef0e25af6efa77ca6ed1cfa4bec164c1ee6f5ef60e3a31bb8e07d350ddf3d5635ddd96ad2dca0ed76daa1192ed9e269a4d71e8632d3268a54d08c1fe8cfaaeb5dcd5635a5ccb6340fcc1db0e2c9c1e28dc9880156c94786a8c7eaa886c69fce5ec67def90c4cc944bc219efd3c00fd164bfa40e66bf5a1d3cbd5bab9fba88bda4b8e76ab4b53b7098b309a8e9b1c39860afd520e7aeb9869aab7eff28aa745c12a99994daa49e2ac1a352a66ea1f33401a12301bea052a6009f754de29c1a785f9ac7e58a
  | 7, 0 => 0x709752007073daf06f6a3d806dc984206a13685068bc39d0681af190680b92c0665520c0659598f0651b5d5064cb80906457cb9063d522406291d830617f3be05fc8ebd05a47d0105687e890562a0ac05169eb00509fa1f04d32ad8048faf4c046088880454d64a0442bd86042d77d50355cd580341d11b033a727c0318307a030a418d03087e0402c7a620029bda2f02898f5e02734c9f02502c67024ad8f90248132d0240dc18023b30dc01f00f2c01e3cad001ca161a01b5ee8d01abdea4019c9fad0185f46d016603570165a78a015842e801551783014ecf68014268c700f9b8fb00f94cd000ea38dd00b9120700b6512f0046618f003e83f9002d875e
  | 7, 1 => 0xf1bfb200eef2d5f0ee5d4340ee271f80e7e15130e7db3450e7515ed0e4ffb2c0e1f184a0e05ccb20e0550e70df565b60df435510de1cc4b0ddd4aa00dc23f740d9cbe430d9a92370d86001e0d7f85ab0d50aa5b0d40e0e10d40405c0cfc43180cd4b54f0c825c970c232aad0c18c4240c0bf6ea0bd124900ba0f9160b8ad6cc0b88cc090b5bd3a60b2912830b1a7d630b05d34b0afb5dd30af197a60ac4d5b90ab629b70a6426b20a0664f209eac84a09d9969709cc529509bdf0a008fadadf08e6fd4608c00bc908b08166089307fc0865d84f0848694b081c74db0815b7f907f70b8707ca96c507c038b307a3436a078f1e53078c6002078179cf074eba94
  | 7, 2 => 0x18bf975f1883498818787ffd181c0a6c18103f8817ddd95917d9c21d17c5c22e17b7e34f17353650172938d7172462521706ecff1695814b16573f00164042a2160c7aef15da08fc15d3b4e415c4f37415ba6e631587591d1561a43a1517feab14e907ff14db292014cc203914c7c3fb1499cfe51476241e146bdca814649f8f1437977c140b2e6e13c146b6139b02df1305f52212ddb43412bb814412245a68122261f8120061e011eac26e11bd50f41187183a11804b36116b47241160b3bd115b67ca114c695c1142fa41113ec3a41120d6461118007510f2a12410de35ff106ef598104ef361102d4a7a0fec104b0fcb33c20fb1a7760f7ac0e10f1c6604
  | 7, 3 => 0x226e2d532259989721e6cbde21a5f9682161be9a213f904520eebdc420e249a720cdfb2c20a84c142064873a2063e54f205b0a2a204fb0ae203e86e9203dbfd62009a42c1fb72b911f8738591f3e5d811f3387171efda3231edb1ab51ed55caf1ea663541ea60e4c1e3a97551e2780c41df73f721de177831d826c881d73f5661d68e5f71d6105a71d4c60a11caf33921ca0b1831c7f55261c676f431c193f401bee157b1bc7d4b01bb1776b1ba64fad1b8548e61b61a0cd1b6003b71b55df541b3c1cc21b27d2611b0bab3e1afecaa01ac819931a8148131a6a04de1a39c2a21a1f1cf019fc1ed919c2b1f0198e7f10192a0dd618ef4baf18eb577118ccee3b
  | 7, 4 => 0x2a7c1a122a430f592a4014db2a245e7b2a14d0f72a1317a029f0b1cd29ed6e3b29e8651229c7962029af2b6429a6739a297c99f82964176b295a32ef29428e4b29259dd7291385ac2912a74928b64d0b28b13185287e5ad228768e57285879f1284514cc2803ddcb27feab2d27fcc31727d2573727c1256227b87eed272ec81d2710b40c26f168c926dd32d726bb2fef26ad119126a8a450265b0505265363bb2648e3a826396ad42616b6002614642225e030e425a00ed525685a9d2568133f24f59d0824f27cee24c9ba2d24955146245fcad923d675a923b6748b23abbd1f2359c6d02353b18e233e5198232c6add23057c1922d25b5c22c4f10a228b5910
  | 7, 5 => 0x349824f43492c5e834886bc3344f47aa344da13934487e12342f69f634064f6c33df688433dd474d33d93c6b33d8677333cd017f33a8219a33a0067c33864f1f332a82ad33273ff63316827432eb626b326bf53f3264f19431f21e3331b7dc6e31ae084531758c3a31470cdc3130272030de567830b1e59a30a324b4304a85c7302ca7773012b9612fbf35272fb1aafd2fb10f502f2d39052f0a93ca2efbd9642ec68d272ebd3d6c2ea523322e8fba352e3a69332e38cc412dfdbfd52de6358a2d7d41f82d4fca342cebd1e12cd4f0ce2c58dac22c009a592badab652b87620c2b81faf52b5b15012b5913022b25f1c52afe09d52ad9fd9b2a9ddf912a9588c3
  | 7, 6 => 0x3ca34bd03c78ad2f3c61cde53c26260f3c21b4153bfbaba33bcc8c933ba7c5f03b9f7aeb3b1d6fda3b1550ef3b08dcd23b05d6f73af6ada23ab0d7363aab48ca3a8b1a653a8512d93a8122023a7742c03a64e63a3a4fc2063a3c419a3a3b596f39fa66b039e1752a39a3fedd39a3264a392f38243929da4e38eec90038ed825b38c86292389f41cf389cbe363884a1d7387c221638658553382f747e382eb67e381fcf143812097437fdfb7837a858aa3797a68e3791ff6b37596ec336f3d80736cb597836c744ae36b5383e36b521a23669c03b364691d8362d5b3035f2a557359f67e73579865d350fe1ad350d0fa434f1480534ecd7be34ceb8d134c7ff3c
  | 7, 7 => 0x4727debc471a541a46dd66d846cefcc0469949b54667f2b7466764c54549390b44e50774445ca64c440fd5ef4408d56743ee98d043eb0c0643e3db9743992f1e433f660a431f7df74305883642e7b5af42b779a34240830841b7ba0441ada2b4417fec1d417adc044170ec6e416eec4f412e341e412c1b384119dfa140fe085a406f21e94049cb824042c3c8403af74d401a1c4f4019119d3ffc41a43fed8a9b3fd62b933fb404613fb101cf3f7cf00e3f732d3d3f55675e3f3721633f1c7b813ef331133e9a6a8f3e70a48c3e444aad3e3a3ac43e247c763e0ad2fb3de1cf0e3de11f973d820b7b3d64e4c33d4903cd3d3e89f93d2c7c353d18139e3cbde0b0
  | 7, 8 => 0x522a087851b5c513518820f7517e9cbd51501bab5102a7f450f1cad050e23594509f358a5065979f5059633d50490acd504166c1500139404fbdd0064fb50f3e4fa260824f8c57c24f49dd644ed50c3e4ead7c894e9a87094e65ab694e5372144e3b68614e3a3a904e18a5394e086b364de2370b4dc27b5b4db8aa404dace24a4d9bad584d84259f4d77b7814d64ac924d3d159f4d1acf0f4d159afc4c77c2484c6ebdd84c4c79c44c2f2a6b4c1e35cd4b5eae324b50406a4b17d9624aeba8ec4a77d2104a44957f4a39d0ac4a0ea61149dd0e9149b6983f497e1ccf49787d01495859134939f530480eeebd47d7f35a47a3d5234798b0ba47883d4b476a5be9
  | 7, 9 => 0x5cde0cce5c9649305bf13ab45bea2b975be9d2375bccb9a15bb301c65ba3354b5ba1deb45aecd9575aebfb475ac679ad5a9c6dcb5a8322685a1dcce559fcbebe59e9114a59e5b3935999c0685992d367597bfa89596e2a09591e47e658e6c54658597183580e347857dd7a9357ad78bd57ab48c1578d26c0576c925c575675b35742a795573f8ef45727b7f456c5d00a5699e747565ed38556569ab455f5a32a55a5888d55739b7c54d5ab8054d391cb54d24b7a54c9884054b25c7054a96c0954a9557c5467b4c6544bdb3153e18f1b53cb534053ca920853c01499539e79b6537b674553155c2b530ba7bc52e38bef52ce9ec252a2b541526b84d852534f94
  | 7, 10 => 0x66abe19266730cef66596eea663dd1146639b9d86624d4f6661f8dfe6617db0a660e2ed065f010c76566e4ba65438d016529158864bb002464b23f0e64b153c164aa6b44646b28aa6433ac9f642e54a0642d74f363fb6a7f63939f33631fb15362fa02de62da87e1629d9733628e144f626898c062623a3562256876621d1ce6621bcd5661fe39a261f427ee61d0c2e561ab00a961a9824361874d90618127b3616fe8b4613fcc2c60e1fd6360b772cb6058ad0a60205a025fbc9c4c5fbac6fd5f4ce3e85f411ea25ef408b65edbff035ecd913b5d994f8a5d9307065d7bf2db5d7408235d5fdc975d4f251a5d4b941a5d48a8d45d46331d5d19fb115d0b1567
  | 7, 11 => 0x71d3d74b71ca317b71b7c8f2719e52c171014993708901987066c393705b5d9f701fd29070120e997005f1236fe598a66fb3739e6f71e1b36f410f6b6f13e0ff6eeb6aab6ee46b536edb0ec36e5e503d6e5a9f856e16b7eb6df33b5f6d916c166d483b2f6d35546a6d26125d6d18b8176c96b4706c64553c6c4b6e046bf899566b76748c6b67104f6b302ff16b18cd806b0959bc6aefcfd96ac5c8b56a729fe46a4320db6a08bb0569da0c1f6996f12369575adf69250df36916740768fa082568ee71a568d40fb46899ba5d68439ee9682efe61682a00956827ae8568240a4468201ef16805cfb767b115c867852479676bd061671066ce66fc748866b2ba9b
  | 7, 12 => 0x80b2da9b80b2a53b808528c48069eaef7fd2c9987f75ea277f685e077f4ff8037e704a887e4dc0ce7e1a8a567e05acff7dc60fd37da51d3c7d57f1e27d3371107cea112d7ce7e2b17c6bc2767c65e62a7c4bfba17c170b2e7b665f577aface357acbd9467a7f40357a2bf43679f05dc079b70aa979952bdb797004af796fc1e1796deb3978e4358b78d82dee78d1319678a6665978849c9477bc93a1778509c2777d8546777652a7771f39f8770164c976fdbb7a76b871ac76a139dd764e5f6175ea2a0475576ffc7554e386753f3383751ff38c74dfd972749998787433e09b73e9209c73823427736647aa73493a2772bb7e8b727f14f372464c2171f636e9
  | 7, 13 => 0x931be89e92bb0e5892002a6a91b6394091503a3090f68a7190f610e690edb58d90e225fa906d26119049058a8fd5443a8fa2db658f80fc978f76ecae8e2522c88e2302ba8d869bbd8d6eb46c8d6b37518d32e83b8c47b39e8b6aabe78b080e6a8a59424c8a571a718a4b2c568a2917998a0b34fc89ba9fdf89b52b50897b30d989357b2988e50a9488ade089885d2a43884d6a8e8846fbcd8824c1658816e9498803a86a87c1a7e6871506e986fcb5f1869d478d84f50771849e475c846b9cfe84594c5e8450d9fa841fb46483fe99eb83b1739883b0d4c8838341f4837dee0a82de711782dd367682d3eb9982673617825ec438821853fe81b76e8e817be6a2
  | 7, 14 => 0xa4ae7b11a494c22fa44634c2a40b50aca3bc67f7a39ec2eea390017ea36cd43aa35287eda33ad16da32cb193a3098384a2d3422fa170cb80a1558ee5a13f99cfa0219339a00b64c39fce48649fc0bc2f9f307a4a9f281e6a9f1c706f9ed6de7b9e56566f9d33d63f9ce7c5ba9c787fac9c20d3b29be41d5a9b43dac29b430ccd9b34b1219af887159ab52eeb9a6914bc9a339d239a24c22a9a07492d99c74fee998829a399265abf98f4208d98e2892c97a4a4a197708ba597012b849595a4cf95872ae69551aacc9520bde9950239c594d4832a949f308d94933acd94302b6c942a4f209405ef3093f42b8d938861299381e4a093602c46934a18bd934803fa
  | 7, 15 => 0xb72628a3b7186549b6be7634b5bed785b4aa19c9b4309820b40478deb3e7728fb365558ab31e2f22b30843b8b2d95111b2ce525eb285abbdb1f9f2f3b1eb36f8b077cf95b028f5a0b017831caf73e99baeec8abdaee89f20ae11518cad7309f1ad70736bad4120a3ad148ffdad096b8bacedf7dcacc6a2bbaca628bfac7b9e87ac5d1b18abdf356cabd7936dab671e17ab55c58dab559622ab227451aa43ea8eaa3bafddaa1f6e87a994b72fa97aa236a9679bafa8fde80ca89eb231a89be350a840633ca7ea78b0a748d152a72e629ca6dfcc07a6910249a65f5d23a6563cc3a61bfe94a5f8bd8ca5b36a13a5a3fa7da57519cca54a6a95a5268c5fa4c4fe3b
  | 7, 16 => 0xcbd798ffcb099803ca8e6379ca6e59dac9f2a206c9be5be9c9bdabcac9a3b4fac8e87de4c8c1bbacc8bf6cefc82aa73ec7d22c68c75da4c0c75d9bc3c667cc40c63e6ab8c60a9cf9c5eadd1ec5c1d047c548d783c4e960c4c4d7a737c4a50f80c48fe98ec398766ec3944fa3c367270ec337f1aac2db04abc2d42780c2b808bac2afde01c219e413c20018d3c1eeb825c1a3757dc1980f89c121cba0c088640ac01d1494bf79164fbeffe354bef0b2a0be269a7bbe110a0dbd7e86ebbd686373bd386403bd376e02bd1c3529bccd4b3fbcc8e334bc591900bbe3d513bba66d37bb80d0edb9e4f0ccb99d8907b90994d0b8d90467b871b7fdb86243b6b75d88c1
  | 7, 17 => 0xe504ee61e4e88dfde455e20ae41e5447e35f01f3e280ec37e254a19ee232c2d0e20f79eae1283faadfa15b07df9dc7dcdf7e61aedf1659adde74f913de4eb049de0dc6abddd8d9a8dd6521e7db6940c7db4f33a9db29855cdb0ef07cda8d8f9bda4ab022d9cc308ed8811cb7d87f9952d84ccd00d803eed7d7c4b6a3d78c0afed76d9a26d70a1d9bd70862e2d6de8f0bd60caeb3d5f3eb55d5e44738d568b144d4feb950d4890869d434e645d4001a12d3a84f1fd3958842d3895d08d37b9b4dd3792a58d29482abd28d9f00d26e2c13d17bf5cfd12bc740d0c5752fd019acf1ce3bc8d3ce1ee8e6cde52a59cdb0a1f9cd19d01fcc9fe01acc6e82bfcc56fb91
  | 7, 18 => 0xff3e3073fe2a185cfd9b65b0fcfeb677fcb4fc26fc50f767fc1a4b00fbe1c5f5fb19fc8af9b835b8f9aef702f8eb2a3df8c7e701f8bf6874f8ba5c5ff808cdccf6f01bfdf6e5cf63f503eb5af4d74db7f44d45f4f3bffcabf31ff462f2d35972f2c41b18f20c2781f1e2cc0df1d45c2af1a59475f15a4793f1510a14f0886534ef459853eec40f0cee71c1e8ee622b56ee02495bed07c3a8ecbb97f1ec8449e5ebefca4beafba6c3eaf7f023eab31e8aea70c2cfea630ca9e86bd220e82d725ee73f702ce65393cae5e351dce5cc13a1e5c2ba49
  | 8, 0 => 0x1e17d8601e08e1531d989e101d81c57f1c53b96d1c1ffead1bea35011bde45011b78d4bc1b52f3321b2d157f1b1036f41a5d39541a2bfa9c19b1d4481979f417196672e11900f429181aa9411623f29c15ff8a4715f86a801561a43a1413d60814121a0c13b5da6d135211a212ae5da311b4128d11761aa81134c93410d1aa960f8898390f3badb20e8414b20e57c7a70dfb96ef0db675560d91ebc20d61f2fb0cf91d9f0cea20e10cabde0a0c22507d0bd753a90b41c7720acf09dd0ab0afbb0a71f95609ee1b6f0864c5e506ecbabd06b07a03064612c706291d83061ab28603e3645402d5abde0291d00a024a740d01a603fb0198251c01013f3600649915
  | 8, 1 => 0x3b3c318a3acd3e823a861c9938ad846e3899ed18387c221637dd7e80375fd1e8368990f7361b1af4359f67e7359aee6d357bcd573518dab134746a9f342cdee9339be830333e196732e7627a32ba82ac326a0621315024ba31381b073129ad3f30ccd1eb3055c0a62fc976f62fa1c82a2edbd6b52e9e70832e46479b2de85b922d014b912cf3c0ef2cae27f22bdd94e829e942c42889888f275958f22705880d26e36c2426d2458e264ea121261c309d259eb530258a6ea4246ade96246554a623038dd422c1b3a3223682592219ec0a21e9d24d21a5f96820df43cc2046aaad203e530f20292edb2014c6441fd3d3851f3d31db1ee4e3db1e8eec381e1aa3ae
  | 8, 2 => 0x6284e0435f2a63495e06e6065d9647d45d93d62e5d7bf2db5c91de815b2acd595af03eb05ab946475a73054d59e5330159d66aa05943cbfb5905159656dbe56f5640306855df5df85592bd7c54b47b98530ec13f528ca242523dc211520a3fab51d2062b51a4e007516924ff51099cc651007c3a4f943bc44f0fba7a4ec7de7a4e7327324e2ce2974e1db72a4dc27b5b4c173de94c1326ad4bff26be4bf147df4b7591cb4b40518f4b02825d4ac0774d4a0d1974499b08ca49148db048f889f848f0bd7d457c5ed145179a8f44cd758b43cee64d43555fb0432891ef42b779a341a4b5d64079af63405c8f3d40455b7a3ffca0873d0124c93c9f3cdf3b562429
  | 8, 3 => 0x82739f207fe35f827fc0036d7fb9fc427e8559377db1e1917d776c2f7cd372a07bf0d3337ab597257aa157477a70b12879a4d76c791d9b417900675a7892577578493a7f77d135d077211a3f76f0de3376f0916b76eecc3f76db0b2e749b988673f60c3a73227b8e727daf3d72739f54721cd83371be65bd70ffce10707cee8d7005f1236fa6c90d6f69601f6ebe77696e1ad9ba6ddedbb86cd622c66be1bd3a6bcb63fb6b89f08a6b1be3666a7ff6686a5eea176a510b386a4fc62d69f9213969c031bf69b2eaed68ff5c7d67f1c0d3679d352a66fb4c91668c477066742ba7651506a464ffcc4e64cf00c5647899486379a67663669d95633635116292bf22
  | 8, 4 => 0xad85a160ad6b0c80abbe6e52ab681b8eaa87c3f1aa38618da9cb11c2a9647ee6a8e78fc4a8d69abba80d4bfda8098f40a4a02823a494c22fa36baaf7a302d5f5a2f4f716a275c8f5a0c045e2a00d2aa29e6bbe4b9b71391a99ed5e879985b80798d8396997a4f3879721f5ed965531e6955a089893f42b8d92a6c201927a567e91bec62691b98d1291426eab90061e318f7fd14d8f78512d8d92f6958d7f04bb8d1e3ac28c8386ea8bc68b508bbc73f08b8fda438b308e208aef6875897643b6881ad299877910e2876b320387080352869b7594868cb4248651842c862851b985520fcd8549f6d2850f030e83f048fb838341f483233d8082d3eb99828511a4
  | 8, 5 => 0xf11d8484f0f10dbeefdfd1c7ee6bbfe2ee22ff53eaf7dac4ea39f55de9d3bc26e73f702ce7283c3de575a6eadfdba1afdede789bde1b0bb2dd547ea2d96359b3d8e7dfa1d7d8277ed6890d25d5d7c256d58853add56748abd3c1c38ed355d4ffd27a66b2d229a3e5d1b38e6dd051c79bcf9551ebcf84bc20cf6e15b1ce6b8b90ce3bc8d3cd5fbf4fcc0b8b0bcae6d7d7c9e65a89c5c226a0c52f7576c4605fcec3935453c1c6e06ebef5700abee065e9be4be64fbc5e25f5baa8a17cba2399e2b84d21e0b7610a65b69fded2b3feb3cab2f03ccbb253eee6b1b17014b108215ab0ec7e1fb0e1dcffb080f6ebb0480e0daf01b67aaee65ee3ae5c9576ae064aa9
  | 8, 6 => 0xfce2758bfab495f5faa130d0f8b72109f7c42f43f6e94291f637ead7f32a1730
  | 9, 0 => 0xf2854adfdd9de376dac0e1e9bad4da24a6563cc3a1f16def7cea112d76f0de335e22a75455df5df851bb2a0f5059633d4f8c57c24aee737942b779a33e277fff34064f6c2efbd9642eedfa851e7359ed1b78d4bc1729918f05169eb0
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 5, 0 => 0xd000000000000f76016324c840000151214843017541a324c840076016324c840076016324c840000000000000007541a324c840000000324c82007541a324c84000014d21484301
  | 6, 0 => 0x700000524c020300000544c9203000000000000500000000c8100000000380a202000000000000c0000000000012000000380620100185540c8300000002148420200000544c820100000000000050000021484202001495200e300000000000000f0000000909203000000000000a00000544c820200000000000110001201802300000000290d2030000000000007000000000210100000530802000000a018023000000001909203000000280620300000544c520300000000000070000021484202000c953085300
  | 6, 1 => 0x1512148430100000544c420200000000000100000000000011000000000000700000544c8203000000380220300000544c820200000544842020000000000009000000000000b00190504c83000000053085202000000000e102000000000000b000c9530853000018d540803000000000000007000000000e104000002148420200000000021010000003806201000000000000700000504c420100000000000060018553080300000000000000b000000380220300000544c820200000544c420100000038062020000054484202
  | 6, 2 => 0xe0000000000000000c9514c8303000000000000a00000000000110000000000009000120280630000000000000070000000002102000000000a1010000001802200000000000000b000000000000b00000000021000014d5300a3000018d54080300000000000000900000504842010000054484202000000000000200000000000110000004802200000000380220100000028062020000002802200000002148420100000524c0203000000000000200000000000050000000006100000855048430100185540c8300
  | 6, 3 => 0x9000000380a203000000000000d00000018022020000002806201000000380220300000059092030000002802201000000380620100000544c020300000000000060000000000006000000280620100000214842010001202806300000002148420200000000000090000000000012000000000000a000000000000700000544c4201000000380a20100000524c4201000000380220200000000000100000002806201001855408030000000028062020000002806203000000000000e000000000000600016324c8300
  | 6, 4 => 0x28062010001a324c83000000000000007000000390d2030014d43100300000005448420100185540c03000000654081300000000480a200000000000000d000c9514c8300000000000000700002324c830000185540c830000000028022010000000000000000005448420100000038022010000000000009000000380a200000000180220100000214842010000053085202000000190920300012038023000000051480203000000000a1010001a324c83000000e028023000000a5408130000185530803000014d43100300
  | 6, 5 => 0x185540c830000000324c820100000000000030000000000005000000000000900002524c430000185540c0300000000000000500000514c8203000000000210000000028022010000000000008000c9514c83000000000000011000005408020000000048062000000000000007000000280620000000514c8201000000000000b000000000000f00190534853000000000000006000000000000600000018022020000054080200000000000a100000000000000700000000000020000a540c1300000000000000d0000000000009
  | 6, 6 => 0x5000000000000900000000000070000e02806300000005448420100016324c830000000324c820000012324c8300000000000001100000018022020000000000012000000180220300006324c830000000000000120000000108100000120380a300000000000000f00000000000120000e02806300000000000000700012324c83000000000000006000000380a203000000290d203000000000000c00000009092030000050109203000120380a3000000000000005001905348530000000000000060000000000008
  | 6, 7 => 0x185530803000000053080200000000000000f00000000c810000000324c82000000000000005000002148420200016324c83000000000006100000000000000600000544c8202000005448420100190534853000000003802201000000380a20000012524c4300000000000000d0000000006103000c9514c8300000005348420100016324c830000000324c8203000005408020000006324c8300000000000000800000000000120001a324c8300000000000000c
  | 7, 0 => 0xe10100000324c82000000000085103000000000000700000001091030000000000000000000090820000000544c42020000000000008000005000a2000000000000008000000000000700000324c8200000005148020000000038c8200000000000e10000000000c510300000058c82000000001802202000000000610300000000000070000003802203000000000610100000000021030000000006103000005448420100000000000010000000080102000000000e1030000000000002000000000000a0000000006101
  | 7, 1 => 0xa10100000000021010000000000006000000000001200000000811010000004806200000002148420200000000000020000000040102000000000e1030000000006101000000090c2000000000000009000000000000000000038022000000000000007000000000000700000324c520000000324c820000000544c8201000000008110000000028062000000000000000000005000e200000000280220000000500852000000003802202000000000000800000000c41010000000000008000005240e200000000000a100
  | 7, 2 => 0x8010200000544c8202000000280620100000000c810000000000851020000053508200000000000210100000514c8203000000000000700000000000090000000006102000000000000600000038062000000005900200000005150020000000000c8102000000008510200000000c510100000324c8200000000000a103000000480220000000000c410200000038062000000000000000000000000610200000038062000000000000003000000000a10100000000c01020000000085101000000380a20000000324c8203
  | 7, 3 => 0x2102000000000210000000000c9103000000000000000000000021000000004806200000000000000d000005400a2000000000085102000000380a20100000504c8201000000000e10300000038c520000000000000070000000000002000000000a103000005200220000000058c820000000000000070000000002101000000000a103000000000000e000000000000100000544c820300000324c82030000001802200000000180220000000000000020000000885200000000000000700000028062000000000000000
  | 7, 4 => 0x3000000008510300000000000080000000000007000000000000900000028022000000003806203000000000e10100000000061020000000000010000000480a200000000000a101000005240220000000000000080000000000008000000000a1030000000000003000000000a10300000001081000000000000006000005250c2000000002908200000000000000b0000000002103000000000000900000000000080000000000000000000000a101000000000a1020000000006101000000000a1010000000000006
  | 7, 5 => 0x21484201000000000000a0000053412200000000000000a0000005885200000000180220000000008c820000000038022020000004802200000000000001100000000c4102000000000e100000000000210000000000061000000000000009000000380a200000000480a20000000000811030000003802200000000000e10000000048022000000000000001000000000a10000000324c8200000000180220200000028022000000000002101000000480a20000000000000030000000002103000000000000b0000000081103
  | 7, 6 => 0x324c5200000000000000a00000544c82030000000085103000005140a2000000054484202000005000a200000005008520000000000000010000000081101000000000000600000000c41010000053484200000005400220000000000811030000000000009000000000a103000000000a103000000000000f0000003806200000000000a10200000000c1101000000000000800000000021000000000000001000000000e10100000544c42010000051480200000000010c100000000000000300000544c820200000000c8103
  | 7, 7 => 0x841010000000000001000000000a1030000004802200000000000a10300000000061030000000000010000005140a20000000000061030000000000006000005000a200000000000a10000000000c410200000028062010000000000009000000000000d0000000080102000005244020000000000c8100000000000a10200000000000000000052500200000000000000700000038022000000002802201000000000000200000000000000000000109103000000000e10300000000841020000000000003000005400e200
  | 7, 8 => 0x380a2000000004802200000000000a101000005010920000000028062000000000000009000000180220000000531092000000002806202000005200e20000000544c8201000005400a2000000000000001000000000000600000028062000000004806200000000000610100000540852000000000006103000000190820000000000000020000000000002000000000000600000540c5200000000000000a000000000000f00000524c0200000000380a201000000000000300000544c820300000000021010000002806200
  | 7, 9 => 0x5240e20000000000c91030000000006101000000000a102000000000000200000000851030000000000006000000480e200000000000000f0000000000006000000480a20000000000000120000000000003000005340a200000000000000d0000001802202000000380a2020000053480200000000000000800000000c0103000000008410200000028c9200000005400a20000000018022000000004806200000000000610200000000c91030000000085102000000000e1010000000000009000000290c2000000042100200
  | 7, 10 => 0x380a20000000000000060000000000006000000000e10200000000000030000000002102000005200e20000000000c410000000214842010000054484201000000000610300000001091030000002900200000000000000700000530852000000021484201000005340a20000000000c4102000000000000f0000000006102000000000610200000000000100000000006101000000000e102000000000a10300000048c9200000000000e103000000008410200000534802030000000000001000000000000d0000000000009
  | 7, 11 => 0xc910300000000000000000000000003000000008110100000000c9101000000000a1010000000109103000000004110000000214842020000000085102000005308520000000028062020000002802201000005150c20000000000061010000000000001000000000000f00000048c52000000000000000000000000000a0000000085101000000480a20000000000c410200000000c8101000000000a1010000002885200000000000e1030000000000000000000000001000000540c9200000000000000900000028c5200
  | 7, 12 => 0x2000000000000f0000003802200000000390820000000048062000000000000000000000000a103000000000e100000000000a101000000004110100000000c01030000002802200000000000000d00000018022000000000084101000000000e1030000000000006000005140a200000000000a102000000380a202000000000e1020000002802203000000010d10300000000000020000002806200000000180220200000000000080000000000006000000000e10300000000c11010000050012200000000010d103
  | 7, 13 => 0x380a200000000000a10300000000000110000000006101000000000a10200000018c920000000028022030000000108100000000000610300000000000070000000000010000005140a2000000002806203000000000a10200000000000060000000000006000005000a20000000048022000000000000009000000000e10300000038062010000002806200000000000a103000000000610100000000061010000003802200000000000000e000000000000300000544c8202000000000000b0000000000007000000000e102
  | 7, 14 => 0x610200000514c820000000028c9200000005400a200000000000a102000005250c2000000000000006000000000000a0000000006102000000380a2030000000006102000000000e1030000000000000000000000a103000000390c200000000000000700000421002000000051508200000000010c10000000008c82000000000002100000000000000f0000000109103000000000000a000005150020000000324c8200000000000000a000000010810000000028022010000004806200000000000e101000000000a101
  | 7, 15 => 0xa10300000038062020000000000009000005200e200000000000a1010000001802200000000000000e00000000000070000000084102000000000e1020000002802200000000000e10100000540c8200000000000610100000544842010000000000008000005408120000000048c9200000000280620000000000021030000000000000000005240e20000000019002000000000000007000000000610200000000000060000000000006000002148420200000540c820000000000061010000000000000000000000000a
  | 7, 16 => 0x1000000380220000000000021010000002880200000000000a1000000054081200000000000a102000000380a200000005200e20000000058c92000000000000000000005204120000000028c92000000002806201000000000000f00000048c5200000000000e103000000000610200000324c82000000000000007000005448420200000000c4102000000000a1010000003802200000000000e103000000288520000000028c52000000000000003000005340a200000000590820000000000000070000000041101
  | 7, 17 => 0x90000000000009000000000000600000000000060000000000000000000000000700000000000060000000000010000000000e101000000190c20000000001051000000003908200000000488020000000514c02000000003802201000000380a203000000000a10300000001041000000001802203000000000000600000000000060000003802203000000000a101000000480a20000000048c92000000003802203000000000e10000000000000100000003802201000005040a20000000000021010000000006101
  | 7, 18 => 0xc9103000000000a1030000000006102000000480a2000000053480200000005150820000000000000090000000000011000005150020000000000000010000003880200000000000000800000540c9200000005300a200000000000000600000000021010000000000005000000380a2000000000000008000000000a1020000000000007000000000000e00000018c92000000000000006000000000000b0000000000010000000000000d000000000000100000028022000000003806202000000000a1010000000002100
  | 7, 19 => 0xa1000000000000011000000008110100000000061030000000000002000000000210200000540c8200000000000000000000540c5200000000000000600000000c4101000000000000d000000008510100000028062000000053012200000000000610200000058802000000000000007000000000a1000000021441201000000000a10300000000000070000000000003000002148420100000048c020000000514c8200000005250c20000000535002000000000000007000000180220000000544842020000000002102
  | 7, 20 => 0x210300000324c82000000054041200000000480620000000544c4201000005140e20000000000000070000000000006000000000000600000000021010000001880200000000000000d000000000e10200000000000090000000000006000000001210000000000000070000000000011000000280620000000018c920000000028022010000000000002000005000e200000005100a200000000000e1030000004806200000000000a10000000324c82030000004885200000000000000d0000000000008000000000a102
  | 7, 21 => 0x28c0200000000000000a00000000c9103000000280620000000028c820000000000000050000000000006000000480a200000000000e1010000043100200000000000a1000000000000009000000288020000000000061020000000000000000000000000300000000000020000000006102000000380a20000000534852000000001908200000000000a10100000000411010000000006103000000000e10300000000000070000000000008000000000e10300000000811010000053406200000000000000200000000c9103
  | 7, 22 => 0x12100000000000000f0000003806201000000590c200000000000000800000000000010000003806201000000000000200000048062000000000041101000000000e1010000000000000000005400a200000000000000700000048c820000000018c020000000029002000000000000009000000000a10000000000121000000000000010000000190c20000000000000090000000000006000000480e200000000488020000000544c42020000000000009000000000e103000000480e200000000000a1010000000002102
  | 7, 23 => 0x500c520000000324c8200000000000e10100000000c110100000000c410100000500c9200000000180220200000000061000000000000003000000480e200000000480a200000000000610200000000000080000053500200000000000e101000000000a101000000000000d000005448420100000000061010000053480200000000000000600000038022000000000000006000000000e1020000052006200000000380a2000000000085103000000000000700000540c920000000000061010000050085200000000000a103
  | 7, 24 => 0x5140e20000000000061000000000000007000000000000a0000001880200000005348520000000048c82000000000002102000000000000200000000121000000000000007000000000000600000535002000000002806200000000000000000000000c91000000053480200000005000e2000000000000001000000000a101000000000610100000028c8200000000000a10000000000000060000000000008000000000210300000540c520000000544c82030000000006103000000000a10100000028062010000053080200
  | 7, 25 => 0x290020000000038062000000000000008000000000e10200000000000060000000006103000000000000c000000000000100000028c0200000000000000700000000c51000000052504200000000000a101000000008010200000540c02000000000000000000000004010000000544c42010000001900200000005300a200000000000610200000000061000000001802201000000000a10200000324c820000000038062020000052105200000000000000f00000018c82000000004806200000000000000a0000002806202
  | 7, 26 => 0x6101000000480a200000000000000700000018c820000000500c920000000520c520000000000021030000000006100000000000000000000000000100000000000001000000380a2000000000002103000000008410200000000c81010000000000006000000000a101000000000a100000000380a200000000000e101000000000001200000000061010000004806200000005400a2000000000000001000000590c200000005440e200000000000000a0000032500200000000480a2000000000000010000000000e102
  | 7, 27 => 0x21030000000000003000000000210300000324c8200000000000a1010000000000005000000280220000000058c82000000000000007000005400a2000000053485200000000000000200000000c810000000048c8200000000001210000000000851030000000002101000000000000a000000000e10300000000000080000000000009000000000610200000000c9101000000000210200000000c8102000000008510100000324c8203000000000000700000000061010000053080200000000008110100000058c0200
  | 7, 28 => 0x801000000000000008000000480e200000000000610100000000000080000000000006000000000a101000000000000a000000000e1030000003802200000000380620100000028c520000000048062000000000000008000005200e20000000048062000000000000007000000000610200000000000090000005900200000000000e101000000000210100000324c82000000001900200000005300a2000000000000006000000480220000000544c8201000000000000a00000520c120000000544c4202000000000000f
  | 7, 29 => 0x480220000000018022000000000085101000000480a20000000540c02000000004802200000000001210000000000c0102000000000001000000000000090000002802200000000000000000000000000070000000006102000000000000600000058c020000000018c820000000520c520000000000000000000001802203000000000a10100000000000060000000002103000000000000200000000c5101000000000e10300000000c0102000000000a1010000000000003000000380a200000005240e2000000000000006
  | 7, 30 => 0x3000000000610200000544c4201000000000000300000038062000000000000000000000000a102000000000000f000000588520000000324c8203000000180220100000324c820000000000000000000000000003000000000a10200000000c410200000514c8200000000000a103000000000000a00000000c410100000000000070000051508200000000000e103000000010910000000000000010000000000000000000008410100000058c82000000000002101000000010c10000000000851010000000006103
  | 7, 31 => 0x6102000000008010200000001001000000000002101000005140a2000000000006100000000000000e00000514c0200000000000000700000500c9200000005240e2000000000000003000000000000f00000514c0203000000390c20000000514c820100000038062030000000002101000000380620300000000000050000000000007000000000000600000000000090000054484201000000000a103000000000e1030000000000001000000000e102000000000000a0000005900200000000000000d000000000e101
  | 7, 32 => 0xc8100000000000000500000058852000000000000001000000380620200000038022010000000000001000000380a20000000544c8203000000000e1010000000084102000000000210300000000000110000000000010000000000e10300000058c8200000000000a10100000000c51030000000002101000000000000600000540c920000000058c92000000000040102000000000210200000540c020000000000000030000000006102000000000000300000520c5200000000000000200000544842020000000000002
  | 7, 33 => 0x51508200000000380220100000038c0200000000480a20000000524c4200000000390c2000000000000002000002148420200000000c8103000000000e102000000000e1010000000109103000000380a200000000000000200000544c4202000000480220000000000000010000000000000000000000e1010000003908200000000000210100000000000090000002806202000000000000f000000000000700000540c52000000000085103000000000610100000000851010000000041103000000000a1010000000908200
  | 7, 34 => 0xc010200000214842010000001802200000000000000200000000851010000000108100000000008410200000324c8200000000000000e000000000001100000000c4102000000000e10200000000401020000000000001000000010d10300000000c01020000053085202000005000a200000000000a1020000021484202000005148020000000540c820000000000000020000000002101000004150020000000324c8200000000000e10200000001091030000000084102000000000a100000005140a2000000000000009
  | 7, 35 => 0x2101000000008510100000058c92000000000000008000000008410200000514c82000000000000009000000480a20000000540c9200000000280220000000544842020000000000002000000000e10100000000811010000000002102000002148420200000000000060000000081101000000280620100000000841010000004802200000000000210100000028062000000000000007000000000210200000000c910300000000c810100000500c9200000000380a200000000000610200000059082000000000109103
  | 7, 36 => 0xe101000000000210200000028062000000000081101000000000000300000008c9200000000000610200000000851020000050105200000000000210200000000000020000005908200000000000000800000504842010000051500200000000000000200000544842010000053080200000000000610000000018022000000021484201000000008510100000000000070000000000001000000480e200000005448420200000324c82000000001802200000000000001100000324c82000000000000006000000000e101
  | 7, 37 => 0x380a2030000000080103000000000e10100000008c92000000000000007000000000000700000058c92000000004802200000000380a200000000380a20300000008c520000000028062020000000002103000000000000100000038022020000000000001000000000000d000000000001100000000c01020000000085102000000380a200
  | 8, 0 => 0x121000000000000001000000000000200000000c910000000000000030000000000007000000010c100000000000a1030000000000001000000000e100000000000a100000000000a102000000010c10000000000061000000000000001000000000000700000000841020000000002100000000000610000000000c910300000000061010000000006101000000000a10100000000000060000000085103000000010c10000000000c4101000000000a1020000000006102000000000a10000000000000030000000085100
  | 8, 1 => 0xc41020000000000003000000000a10000000000021000000000080100000000000210300000000000020000000000008000000000610000000000021020000000000009000000000000600000000000030000000085100000000000a1020000000108100000000000000200000000c510000000000c010300000000c510000000000061020000000000001000000000a100000000010010000000000000080000000000001000000008010000000000000020000000108100000000000e10000000000c9100000000000a100
  | 8, 2 => 0x3000000000e102000000010810000000000000070000000002100000000000a10300000000000020000000000001000000010c10000000000c910300000000c810300000000c9100000000010c10000000000000020000000000003000000000a100000000000a103000000010c1000000000006102000000000e1010000000084101000000000210300000000061030000000108100000000000e10100000000061000000000000001000000000000100000000061010000000000003000000000e1000000000080100
  | 8, 3 => 0x300000000c8100000000010c1000000000085101000000000a100000000000e1020000000100100000000008010000000001081000000000080100000000000610200000000c01000000000000003000000000a1010000000006101000000001210000000000000010000000080100000000010010000000000021010000000000009000000000a10000000000c9100000000000a101000000000a10000000000c410100000000851030000000080102000000010010000000000c5103000000000000300000000c5100
  | 8, 4 => 0x610100000000000080000000006101000000000610000000000c8100000000000e102000000001210000000000c41020000000000000000000008010000000000c9100000000000e1000000000006101000000000a100000000000000a000000000000a00000000c41010000000000003000000000610000000000c8100000000000000200000000000000000000000000000000004110100000000811010000000006100000000008510000000000c81020000000000002000000001210000000000c0100
  | 8, 5 => 0xc9100000000010c100000000000000700000000c81000000000000001000000000610200000000061000000000012100000000008510200000000c81000000000000000000000000000700000000c5100000000000000300000000c4102000000000000200000000021020000000012100000000010c1000000000000001000000000e10000000000c5100000000000000100000000c9100000000000000300000001001000000000000008000000000e101000000000e100000000000610200000000851020000000100100
  | 8, 6 => 0xa103000000008010000000000811010000000012100000000000e1000000000000009000000000e100000000000a100000000000610000000000000020000000000001000000000a103000000000000200000000c51000000000000008000000000e10000000000000090000000006102000000000a1030000000012100000000008510100000000000010000000100100000000010c100000000000a10000000000c010300000000c9100000000000000200000000c8102000000000000200000000000070000000085102
  | 8, 7 => 0xe103000000000000800000000c0103000000000000600000000c9100000000000e100000000000000700000000851000000000006101000000008510000000000061000000000000006000000000e1030000000000001000000000a1030000000006100000000000a1000000000000001000000000000300000000021000000000080100000000010c10000000000000010000000006101000000004010200000000c810300000000c81000000000000000000000000210300000000c9100000000000000600000000c4101
  | 8, 8 => 0xc410100000000c910000000000c5103000000000000200000000c010200000000000010000000000007000000000a10000000000c510000000000000010000000006100000000000000200000000000020000000100100000000000000200000000c9103000000010010000000000401020000000080100000000000a1000000000002100000000000000000000000c5100000000010c10000000000c91000000000000003000000008410100000000c910300000000061030000000085102000000000e1030000000000001
  | 8, 9 => 0x1000000000a100000000000000200000000851010000000085101000000008010000000000c81010000000002100000000000000100000000801030000000000001000000004010200000000061020000000002101000000008010000000000c0102000000010010000000000000010000000080102000000008410100000000c81000000000084102000000000e10200000000c51000000000000008000000000000100000000c810000000000000030000000000009000000000e10100000000841020000000100100
  | 8, 10 => 0x3000000000e10000000000c810000000000c810000000000000030000000100100000000000a100000000000000300000000c010200000000000030000000100100000000000000000000000021000000000000003000000000000200000000c9100000000000000200000000000010000000080100000000008410100000000801000000000081101000000000000800000000c0102000000000e10000000000000020000000085102000000000a100000000008510000000000c810000000000801030000000002101
  | 8, 11 => 0xa1000000000000001000000000000200000000c9100000000000610200000000000010000000002100000000000a1000000000002102000000000000100000000411010000000000001000000000210000000000c81000000000081101000000000000100000000121000000000012100000000000000700000000c8103000000008510100000000000010000000000003000000000000300000000c8102000000010010000000000c810000000000c810300000000021010000000084102000000000000100000000c8100
  | 8, 12 => 0x841020000000002100000000001210000000000021000000000012100000000008410100000000c51000000000000003
  | 9, 0 => 0x3000000000000100000000000020000000000001000000000000000000000000030000000000000000000000000300000000000020000000000000000000000000000000000000000000000000001000000000000200000000000000000000000000000000000000200000000000000000000000001
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 12 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_31 roots_31 9 s ws hint
  | 1 => checkCutEntry dom_62_1 roots_62_1 8 s ws hint
  | 2 => checkCutEntry dom_61 roots_61 8 s ws hint
  | 3 => checkCutEntry dom_47_16 roots_47_16 8 s ws hint
  | 4 => checkCutEntry dom_15_16 roots_15_16 7 s ws hint
  | 5 => checkCutEntry dom_31_32 roots_31_32 6 s ws hint
  | 6 => checkCutEntry dom_47 roots_47 6 s ws hint
  | 7 => checkCutEntry dom_55 roots_55 6 s ws hint
  | 8 => checkCutEntry dom_55_8 roots_55_8 6 s ws hint
  | 9 => checkCutEntry dom_59 roots_59 6 s ws hint
  | 10 => checkCutEntry dom_59_4 roots_59_4 6 s ws hint
  | 11 => checkCutEntry dom_15 roots_15 5 s ws hint
  | 12 => checkCutEntry dom_15_48 roots_15_48 5 s ws hint
  | 13 => checkCutEntry dom_39_16 roots_39_16 5 s ws hint
  | 14 => checkCutEntry dom_43_16 roots_43_16 5 s ws hint
  | 15 => checkCutEntry dom_53_8 roots_53_8 5 s ws hint
  | 16 => checkCutEntry dom_57_4 roots_57_4 5 s ws hint
  | 17 => checkCutEntry dom_30 roots_30 5 s ws hint
  | 18 => checkCutEntry dom_30_32 roots_30_32 5 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_62_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_61 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31_32 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_55 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_55_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_59 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_59_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15_48 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_39_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_43_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_53_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_57_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_30 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_30_32 _ hc
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
private theorem z5_0 : ∀ i, 0 ≤ i → i < 5 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 5 0 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 5 → Z 5 i = true := z5_0
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
private theorem z6_64 : ∀ i, 64 ≤ i → i < 68 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 64 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 68 → Z 6 i = true := (range_split (range_split (range_split z6_0 z6_16) (range_split z6_32 z6_48)) z6_64)
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
private theorem z7_192 : ∀ i, 192 ≤ i → i < 201 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 9 192 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 201 → Z 7 i = true := (range_split (range_split (range_split (range_split z7_0 z7_16) (range_split z7_32 z7_48)) (range_split (range_split z7_64 z7_80) (range_split z7_96 z7_112))) (range_split (range_split (range_split z7_128 z7_144) (range_split z7_160 z7_176)) z7_192))
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
private theorem z8_96 : ∀ i, 96 ≤ i → i < 102 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 6 96 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 102 → Z 8 i = true := (range_split (range_split (range_split z8_0 z8_16) (range_split z8_32 z8_48)) (range_split (range_split z8_64 z8_80) z8_96))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_0 : ∀ i, 0 ≤ i → i < 11 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 11 0 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 11 → Z 9 i = true := z9_0
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

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 14]⟩], 16⟩

theorem wit_mono : PEqualNP.MetaComplexity.Monotone2 wit := by
  simp [wit, PEqualNP.MetaComplexity.Monotone2]

theorem wit_sz : wit.size ≤ 11 := by decide

set_option maxRecDepth 40000 in
theorem wit_ev : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4276677824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel

set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_63.testBit r.val = (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276677824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) (pt6 r.val) := by decide +kernel

theorem lower : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276677824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) t → 11 ≤ t :=
  lower_to_circuit6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276677824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) goal_63 11 hT6 (by unfold IsConst; decide) low_63

end PEqualNP.Outside.L_meta_40539_aux

theorem PEqualNP.Outside.L_meta_40539 :
  ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276677824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4276677824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  exact ⟨PEqualNP.Outside.L_meta_40539_aux.wit, PEqualNP.Outside.L_meta_40539_aux.wit_mono, le_trans PEqualNP.Outside.L_meta_40539_aux.wit_sz (PEqualNP.Outside.L_meta_40539_aux.lower s hs), PEqualNP.Outside.L_meta_40539_aux.wit_ev⟩
