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

namespace PEqualNP.Outside.L_meta_38135_aux

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
def goal_47 : Nat := 0xfeeafeeafc88fc88feeafeeafc88fc88feeafeeafc88fc88feeafeeafc88fc88
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_31 : Nat := 0xffffffff
def goal_31 : Nat := 0xfefcfc88fefcfc88fefcfc88fefcfc88fefcfc88fefcfc88fefcfc88fefcfc88
def roots_31 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xeeeeeeaaeecccc88eeeeeeaaeecccc88eeeeeeaaeecccc88eeeeeeaaeecccc88
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_27 : Nat := 0xf0f0f0f
def goal_27 : Nat := 0xeecccc88eecccc88eecccc88eecccc88eecccc88eecccc88eecccc88eecccc88
def roots_27 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfafafaaafaf0f000fafafaaafaf0f000fafafaaafaf0f000fafafaaafaf0f000
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_31_32 : Nat := 0xffffffff00000000
def goal_31_32 : Nat := 0xfefefeeafefefeeafefefeeafefefeeafefefeeafefefeeafefefeeafefefeea
def roots_31_32 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_59_4 : Nat := 0xf0f0f0f0f0f0f0f0
def goal_59_4 : Nat := 0xffffffeeffffff88ffffffeeffffff88ffffffeeffffff88ffffffeeffffff88
def roots_59_4 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_62 : Nat := 0x5555555555555555
def goal_62 : Nat := 0xfcfcfcc0fcfcfc00fcfcfcc0fcfcfc00fcfcfcc0fcfcfc00fcfcfcc0fcfcfc00
def roots_62 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_15_32 : Nat := 0xffff00000000
def goal_15_32 : Nat := 0xfeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeea
def roots_15_32 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0]

def dom_39 : Nat := 0xff000000ff
def goal_39 : Nat := 0xeaeaeaea88888888eaeaeaea88888888eaeaeaea88888888eaeaeaea88888888
def roots_39 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0]

def dom_30_32 : Nat := 0x5555555500000000
def goal_30_32 : Nat := 0xfcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0
def roots_30_32 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xfefeeaeafcfc8888fefeeaeafcfc8888fefeeaeafcfc8888fefeeaeafcfc8888
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_62_1 : Nat := 0xaaaaaaaaaaaaaaaa
def goal_62_1 : Nat := 0xfffffffffffcfcccfffffffffffcfcccfffffffffffcfcccfffffffffffcfccc
def roots_62_1 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_23_32 : Nat := 0xff00ff00000000
def goal_23_32 : Nat := 0xfefeeaeafefeeaeafefeeaeafefeeaeafefeeaeafefeeaeafefeeaeafefeeaea
def roots_23_32 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0]

def dom_43_4 : Nat := 0xf0f00000f0f0
def goal_43_4 : Nat := 0xffeeffeeff88ff88ffeeffeeff88ff88ffeeffeeff88ff88ffeeffeeff88ff88
def roots_43_4 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_51_4 : Nat := 0xf000f000f000f0
def goal_51_4 : Nat := 0xffffeeeeffff8888ffffeeeeffff8888ffffeeeeffff8888ffffeeeeffff8888
def roots_51_4 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_29 : Nat := 0x33333333
def goal_29 : Nat := 0xfaf0f000faf0f000faf0f000faf0f000faf0f000faf0f000faf0f000faf0f000
def roots_29 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_30_1 : Nat := 0xaaaaaaaa
def goal_30_1 : Nat := 0xfffcfcccfffcfcccfffcfcccfffcfcccfffcfcccfffcfcccfffcfcccfffcfccc
def roots_30_1 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_46 : Nat := 0x555500005555
def goal_46 : Nat := 0xfcc0fcc0fc00fc00fcc0fcc0fc00fc00fcc0fcc0fc00fc00fcc0fcc0fc00fc00
def roots_46 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_54 : Nat := 0x55005500550055
def goal_54 : Nat := 0xfcfcc0c0fcfc0000fcfcc0c0fcfc0000fcfcc0c0fcfc0000fcfcc0c0fcfc0000
def roots_54 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_60_1 : Nat := 0x2222222222222222
def goal_60_1 : Nat := 0xfffffffffff0f000fffffffffff0f000fffffffffff0f000fffffffffff0f000
def roots_60_1 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfefefeeafefcfc88fefefeeafefcfc88fefefeeafefcfc88fefefeeafefcfc88
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

namespace S_47
def pairsG : List (Nat × Nat) := [(1, 3), (1, 33), (2, 3), (2, 10), (4, 12), (5, 7), (5, 13), (5, 37), (6, 7), (6, 14), (6, 38), (8, 10), (8, 12), (9, 11), (9, 13), (9, 41), (32, 33), (34, 35), (34, 38), (34, 42), (36, 37), (36, 38), (36, 44), (40, 41), (40, 42), (40, 44)]
def r1sG : List Nat := [1, 1, 2, 2, 4, 5, 5, 5, 6, 6, 6, 8, 8, 9, 9, 9, 32, 34, 34, 34, 36, 36, 36, 40, 40, 40]
def r2sG : List Nat := [3, 33, 3, 10, 12, 7, 13, 37, 7, 14, 38, 10, 12, 11, 13, 41, 33, 35, 38, 42, 37, 38, 44, 41, 42, 44]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [2203924701443, 9904279257866, 8805289430026, 39608207344422, 5506754552067, 9904867838467, 43989661518858, 8813845809676, 37387793466145, 6619151081731, 37388296790275, 39728582492966, 37418361555978, 37409318308902]
def xsM : List Nat := roots_47.map (· &&& dom_47)
def goalM : Nat := goal_47 &&& dom_47
def NN : Nat → Nat
  | 4 => 1
  | 5 => 25
  | 6 => 19
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xf1fce07
  | 5, 0 => 0xee415aabe1aee2a6bc1fa3ec915d400188e2183d8888432e7b1ce2dc6fa9a6b367ae8f7561862ddf5d37001f5ba073fa5b61388b4fada6a442c1d77f42829c102a48ff95286448961b2929df1412d30a0fdea1890f1fce070afba44c03b0c7d70335d817
  | 6, 0 => 0xaf535e0ea7da18faa12a17a395fc1c0b92b6c7608888432e7ea52a9a7445a6b572657d5c686e9bda6594bfe25ba073fa5b61388b55c13d202fef2b28270b03de160058940f1fce070da784ce
  | 7, 0 => 0xf1fce07
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xcc000000cc000000000000000000000000000000000000000000000000000000aaaa0000aaaa0000000000000000000000000000000000000000000000000000aa000000aa000000000000000000000000000000000000000000000000000000555500005555000000000000000000000000000000000000000000000000000033330000333300000000000000000000000000000000000000000000000000000f0f00000f0f000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000000000ffff
  | 0, 1 => 0xf8f80000f8f80000000000000000000000000000000000000000000000000000f0f00000f0f00000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000f0000000f0000000000000000000000000000000000000000000000000000000eeee0000eeee0000000000000000000000000000000000000000000000000000eeee000000000000000000000000000000000000000000000000000000000000cccc0000cccc0000000000000000000000000000000000000000000000000000cccc00000000
  | 0, 2 => 0xff880000ff880000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000fcfc0000fcfc0000000000000000000000000000000000000000000000000000fccc0000fccc0000000000000000000000000000000000000000000000000000fc000000fc000000000000000000000000000000000000000000000000000000fafa0000fafa0000000000000000000000000000000000000000000000000000fafa00000000
  | 0, 3 => 0xffff0000cccc0000000000000000000000000000000000000000000000000000ffff0000aaaa0000000000000000000000000000000000000000000000000000ffff000088880000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000fff00000fff00000000000000000000000000000000000000000000000000000ffcc0000ffcc0000000000000000000000000000000000000000000000000000ffaa0000ffaa0000000000000000000000000000000000000000000000000000ffaa0000ff00
  | 0, 4 => 0xffff0000ff000000000000000000000000000000000000000000000000000000ffff0000f0f00000000000000000000000000000000000000000000000000000ffff0000f000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x1c58e2465
  | 5, 0, 0 => 0x718389195c5ce2465716246095c58e244571b309195c246081570e244055638a246575638919563860c05816389195c5933865716389195c64e2455895389195c58f2465
  | 5, 0, 1 => 0x162460805590389195c48e24657d6388194e24604057163860d6158d246570e183055c68e1c65
  | 6, 0, 0 => 0x71650e246671638d246601c58e1835716389180671958e24667163891c6671638c2466716389206601c589182501c58e2445716389183685c58e246679c58e246671654e246601c58e24657163891816
  | 6, 0, 1 => 0x716389185671644e246671638b2466
  | 7, 0, 0 => 0x1c58e2465
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
  | 0, 0 => 0xe0e3000000000000000000000000000000000000000000000000000000000000e0000000000000000000000000000000000000000000000000000000000003ff1f1c0000000000000000000000000000000000000000000000000000000003f1f8f300000000000000000000000000000000000000000000000000000000038ff80f00000000000000000000000000000000000000000000000000000000007f07ff000000000000000000000000000000000000000000000000000000000000ffff
  | 0, 1 => 0x7007f000000000000000000000000000000000000000000000000000000000007007f00000000000000000000000000000000000000000000000000000000000700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ee7ef00000000000000000000000000000000000000000000000000000000000e000000000000000000000000000000000000000000000000000000000000000e070c00000000000000000000000000000000000000000000000000000000000e0000
  | 0, 2 => 0x380f800000000000000000000000000000000000000000000000000000000000380f800000000000000000000000000000000000000000000000000000000000380000000000000000000000000000000000000000000000000000000000000007e07fc00000000000000000000000000000000000000000000000000000000000e070c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000070e7f30000000000000000000000000000000000000000000000000000000000700000
  | 0, 3 => 0x3ff070c0000000000000000000000000000000000000000000000000000000003ffe0e30000000000000000000000000000000000000000000000000000000003ff00000000000000000000000000000000000000000000000000000000000003ff00000000000000000000000000000000000000000000000000000000000003f0fff000000000000000000000000000000000000000000000000000000000038eff0c000000000000000000000000000000000000000000000000000000000380f8e3000000000000000000000000000000000000000000000000000000000380f800
  | 0, 4 => 0x3fff8000000000000000000000000000000000000000000000000000000000003ff07f00000000000000000000000000000000000000000000000000000000003ff0000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x1082a08000000000000000000000000000000000000000000000000000000000093e1e7000000000000000000000000000000000000000000000000000000000080e04000000000000000000000000000000000000000000000000000000000036c1e180000000000000000000000000000000000000000000000000000000002d1d0d200000000000000000000000000000000000000000000000000000000018ba80f00000000000000000000000000000000000000000000000000000000003705a70000000000000000000000000000000000000000000000000000000000007b7d
  | 0, 1 => 0x27677f500000000000000000000000000000000000000000000000000000000027457f0000000000000000000000000000000000000000000000000000000000274048000000000000000000000000000000000000000000000000000000000024052500000000000000000000000000000000000000000000000000000000001bfefef0000000000000000000000000000000000000000000000000000000001bf848200000000000000000000000000000000000000000000000000000000012e2f2d00000000000000000000000000000000000000000000000000000000012e0400
  | 0, 2 => 0x3cafb7d0000000000000000000000000000000000000000000000000000000003c8fa580000000000000000000000000000000000000000000000000000000003c8800000000000000000000000000000000000000000000000000000000000037e7ffd00000000000000000000000000000000000000000000000000000000036e7f7d0000000000000000000000000000000000000000000000000000000003487a580000000000000000000000000000000000000000000000000000000002f7f7f70000000000000000000000000000000000000000000000000000000002f78482
  | 0, 3 => 0x3ffafaf0000000000000000000000000000000000000000000000000000000003ffe5e70000000000000000000000000000000000000000000000000000000003ffa5a70000000000000000000000000000000000000000000000000000000003ff84820000000000000000000000000000000000000000000000000000000003fcfff80000000000000000000000000000000000000000000000000000000003eeff7d0000000000000000000000000000000000000000000000000000000003dbfbff0000000000000000000000000000000000000000000000000000000003dbfada
  | 0, 4 => 0x3fffeda0000000000000000000000000000000000000000000000000000000003ffd7f20000000000000000000000000000000000000000000000000000000003ffd6d2
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 35 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 35 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 35 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 35 then wireAt i else 0
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

def symsG : List (List (Nat × Nat)) := [[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)]]
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
private theorem z5_16 : ∀ i, 16 ≤ i → i < 25 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 9 16 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 25 → Z 5 i = true := (range_split z5_0 z5_16)
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
def pairsG : List (Nat × Nat) := [(1, 3), (2, 3), (2, 10), (2, 18), (4, 12), (4, 20), (5, 7), (5, 13), (5, 21), (6, 7), (6, 14), (6, 22), (8, 10), (8, 12), (9, 11), (9, 13), (9, 25), (16, 18), (16, 20), (17, 19), (17, 21), (17, 25), (24, 25), (24, 26), (24, 28)]
def r1sG : List Nat := [1, 2, 2, 2, 4, 4, 5, 5, 5, 6, 6, 6, 8, 8, 9, 9, 9, 16, 16, 17, 17, 17, 24, 24, 24]
def r2sG : List Nat := [3, 3, 10, 18, 12, 20, 7, 13, 21, 7, 14, 22, 10, 12, 11, 13, 25, 18, 20, 19, 21, 25, 25, 26, 28]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := [8804969813004, 2203722516995, 9904279257866, 8804969812490, 8817854714892, 9904598878723, 26461327721241]
def xsM : List Nat := roots_31.map (· &&& dom_31)
def goalM : Nat := goal_31 &&& dom_31
def NN : Nat → Nat
  | 4 => 1
  | 5 => 6
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xac05225e
  | 5, 0 => 0xe90385e4be3fb924ac05225e8c616cec5299e96d3a6b8d41
  | 6, 0 => 0xac05225e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xfcfcfcfc00000000000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000cccccccc00000000000000000000000000000000000000000000000000000000aaaaaaaa00000000000000000000000000000000000000000000000000000000555555550000000000000000000000000000000000000000000000000000000033333333000000000000000000000000000000000000000000000000000000000f0f0f0f0000000000000000000000000000000000000000000000000000000000ff00ff
  | 0, 1 => 0xffff000000000000000000000000000000000000000000000000000000000000ff00ff00
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x986545
  | 5, 0, 0 => 0x987545986425986545965405985415986535
  | 6, 0, 0 => 0x986545
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
  | 0, 0 => 0xffe0000000000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000e0e000000000000000000000000000000000000000000000000000000000039c1c10000000000000000000000000000000000000000000000000000000001c63e3e0000000000000000000000000000000000000000000000000000000001fff1f10000000000000000000000000000000000000000000000000000000001fff00f00000000000000000000000000000000000000000000000000000000003e0fff
  | 0, 1 => 0x1fe00000000000000000000000000000000000000000000000000000000000001c1f000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x19effff000000000000000000000000000000000000000000000000000000000114aff000000000000000000000000000000000000000000000000000000000008a5e4f000000000000000000000000000000000000000000000000000000000079c3c30000000000000000000000000000000000000000000000000000000001863c3c000000000000000000000000000000000000000000000000000000000175a1b00000000000000000000000000000000000000000000000000000000000eb500f00000000000000000000000000000000000000000000000000000000001e0b6b
  | 0, 1 => 0x1ff09280000000000000000000000000000000000000000000000000000000001e1f494
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 10 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 10 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 10 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 10 then wireAt i else 0
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
private theorem z4_0 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := z4_0
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

namespace S_59
def pairsG : List (Nat × Nat) := [(1, 3), (1, 33), (2, 3), (2, 10), (2, 18), (8, 10), (9, 11), (9, 25), (9, 41), (16, 18), (17, 19), (17, 25), (17, 49), (24, 25), (24, 26), (32, 33), (34, 35), (34, 42), (34, 50), (40, 41), (40, 42), (48, 49), (48, 50), (56, 57), (56, 58)]
def r1sG : List Nat := [1, 1, 2, 2, 2, 8, 9, 9, 9, 16, 17, 17, 17, 24, 24, 32, 34, 34, 34, 40, 40, 48, 48, 56, 56]
def r2sG : List Nat := [3, 33, 3, 10, 18, 10, 11, 25, 41, 18, 19, 25, 49, 25, 26, 33, 35, 42, 50, 41, 42, 49, 50, 57, 58]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := [2203722516995, 26461327721241, 9904481436426, 8804969812490, 17600928613138, 9904598878723]
def xsM : List Nat := roots_59.map (· &&& dom_59)
def goalM : Nat := goal_59 &&& dom_59
def NN : Nat → Nat
  | 4 => 2
  | 5 => 7
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xc38274818fab6c8c
  | 5, 0 => 0xeaaab64ad3d4756ac3827481925f5c684cac355d4b95005a37f8ccf4
  | 6, 0 => 0xc3827481
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xe0e0e0e0c0c0c0c0000000000000000000000000000000000000000000000000c0c0c0c0c0c0c0c0000000000000000000000000000000000000000000000000a0a0a0a0a0a0a0a0000000000000000000000000000000000000000000000000a0a0a0a000000000000000000000000000000000000000000000000000000000505050505050505000000000000000000000000000000000000000000000000030303030303030300000000000000000000000000000000000000000000000000000f0f00000f0f000000000000000000000000000000000000000000000000000000000f0f0f0f
  | 0, 1 => 0xf0f0f0f0c0c0c0c0000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000f0f00000f0f00000000000000000000000000000000000000000000000000000f000f000f000f00
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0xa98655098754
  | 5, 0, 0 => 0x986505986545a98655a98525a98635b98655a86515
  | 6, 0, 0 => 0xa98655
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
  | 0, 0 => 0x7001c000000000000000000000000000000000000000000000000000000000007001c0000000000000000000000000000000000000000000000000000000000001dc300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001ffe23c0000000000000000000000000000000000000000000000000000000001f8ffe300000000000000000000000000000000000000000000000000000000001f81ff0000000000000000000000000000000000000000000000000000000000007fff
  | 0, 1 => 0x1ff801c0000000000000000000000000000000000000000000000000000000001ff80000000000000000000000000000000000000000000000000000000000001e07e0000000000000000000000000000000000000000000000000000000000019861e0
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x1ffd77f000000000000000000000000000000000000000000000000000000000157467d0000000000000000000000000000000000000000000000000000000000a9bdc70000000000000000000000000000000000000000000000000000000000a9910200000000000000000000000000000000000000000000000000000000015642380000000000000000000000000000000000000000000000000000000000a8b98200000000000000000000000000000000000000000000000000000000001b816f0000000000000000000000000000000000000000000000000000000000006efd
  | 0, 1 => 0x1ffd77f0000000000000000000000000000000000000000000000000000000001ff91020000000000000000000000000000000000000000000000000000000001e47e9000000000000000000000000000000000000000000000000000000000019a69e8
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
  scr dom_59 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_59 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_59 roots_59 goal_59 7 := by
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

theorem low_59 : Lower dom_59 roots_59 goal_59 7 := S_59.noCircuit

namespace S_27
def pairsG : List (Nat × Nat) := [(1, 3), (2, 3), (2, 10), (2, 18), (8, 10), (9, 11), (9, 25), (16, 18), (17, 19), (17, 25), (24, 25), (24, 26)]
def r1sG : List Nat := [1, 2, 2, 2, 8, 9, 9, 16, 17, 17, 24, 24]
def r2sG : List Nat := [3, 3, 10, 18, 10, 11, 25, 18, 19, 25, 25, 26]
def mpG : Nat := 0xfff
def pool6G : List Nat := [2203722516995, 9904481436426, 8804969812490, 17600928613138, 9904598878723, 18700691900931]
def xsM : List Nat := roots_27.map (· &&& dom_27)
def goalM : Nat := goal_27 &&& dom_27
def NN : Nat → Nat
  | 3 => 1
  | 4 => 3
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x317f6efe
  | 4, 0 => 0xf742f7bf317f6efe04fd712f
  | 5, 0 => 0x317f6efe
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f0000000000000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000c0c0c0c000000000000000000000000000000000000000000000000000000000a0a0a0a000000000000000000000000000000000000000000000000000000000303030300000000000000000000000000000000000000000000000000000000000f000f
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xb1a4
  | 4, 0, 0 => 0xb114b1a4ad04
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
  | 0, 0 => 0xf800000000000000000000000000000000000000000000000000000000000000c70000000000000000000000000000000000000000000000000000000000000000e00000000000000000000000000000000000000000000000000000000000003610000000000000000000000000000000000000000000000000000000000000ff1000000000000000000000000000000000000000000000000000000000000038f
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfc80000000000000000000000000000000000000000000000000000000000000e7400000000000000000000000000000000000000000000000000000000000009bf00000000000000000000000000000000000000000000000000000000000007630000000000000000000000000000000000000000000000000000000000000640000000000000000000000000000000000000000000000000000000000000018b
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_27 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_27 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]]
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
  scr dom_27 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_27 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_27 roots_27 goal_27 6 := by
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

theorem low_27 : Lower dom_27 roots_27 goal_27 6 := S_27.noCircuit

namespace S_61
def pairsG : List (Nat × Nat) := [(1, 33), (4, 12), (4, 20), (5, 13), (5, 21), (5, 37), (8, 12), (9, 13), (9, 25), (9, 41), (16, 20), (17, 21), (17, 25), (17, 49), (24, 25), (24, 28), (32, 33), (36, 37), (36, 44), (36, 52), (40, 41), (40, 44), (48, 49), (48, 52), (56, 57), (56, 60)]
def r1sG : List Nat := [1, 4, 4, 5, 5, 5, 8, 9, 9, 9, 16, 17, 17, 17, 24, 24, 32, 36, 36, 36, 40, 40, 48, 48, 56, 56]
def r2sG : List Nat := [33, 12, 20, 13, 21, 37, 12, 13, 25, 41, 20, 21, 25, 49, 25, 28, 33, 37, 44, 52, 41, 44, 49, 52, 57, 60]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [8813559747596]
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

namespace S_31_32
def pairsG : List (Nat × Nat) := [(32, 33), (34, 35), (34, 38), (34, 42), (34, 50), (36, 37), (36, 38), (36, 44), (36, 52), (40, 41), (40, 42), (40, 44), (48, 49), (48, 50), (48, 52), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [32, 34, 34, 34, 34, 36, 36, 36, 36, 40, 40, 40, 48, 48, 48, 56, 56, 56]
def r2sG : List Nat := [33, 35, 38, 42, 50, 37, 38, 44, 52, 41, 42, 44, 49, 50, 52, 57, 58, 60]
def mpG : Nat := 0x3ffff
def pool6G : List Nat := [39729121471014]
def xsM : List Nat := roots_31_32.map (· &&& dom_31_32)
def goalM : Nat := goal_31_32 &&& dom_31_32
def NN : Nat → Nat
  | 4 => 2
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x5f5ce351550bda74
  | 5, 0 => 0x5f5ce351
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffffff0000000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000cccccccc00000000000000000000000000000000000000000000000000000000aaaaaaaa00000000
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_31_32 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_31_32 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
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

namespace S_59_4
def pairsG : List (Nat × Nat) := [(4, 12), (4, 20), (5, 7), (5, 13), (5, 21), (5, 37), (6, 7), (6, 14), (6, 22), (6, 38), (36, 37), (36, 38), (36, 44), (36, 52)]
def r1sG : List Nat := [4, 4, 5, 5, 5, 5, 6, 6, 6, 6, 36, 36, 36, 36]
def r2sG : List Nat := [12, 20, 7, 13, 21, 37, 7, 14, 22, 38, 37, 38, 44, 52]
def mpG : Nat := 0x3fff
def pool6G : List Nat := [6619151082759]
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
  | 0, 0 => 0x3c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003c0000000000000000000000000000000000000000000000000000000000000003c
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3e20000000000000000000000000000000000000000000000000000000000000319b000000000000000000000000000000000000000000000000000000000000211200000000000000000000000000000000000000000000000000000000000010890000000000000000000000000000000000000000000000000000000000000bc4000000000000000000000000000000000000000000000000000000000000047c
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

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
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

namespace S_62
def pairsG : List (Nat × Nat) := [(2, 10), (2, 18), (4, 12), (4, 20), (6, 14), (6, 22), (6, 38), (8, 10), (8, 12), (16, 18), (16, 20), (24, 26), (24, 28), (34, 38), (34, 42), (34, 50), (36, 38), (36, 44), (36, 52), (40, 42), (40, 44), (48, 50), (48, 52), (56, 58), (56, 60)]
def r1sG : List Nat := [2, 2, 4, 4, 6, 6, 6, 8, 8, 16, 16, 24, 24, 34, 34, 34, 36, 36, 36, 40, 40, 48, 48, 56, 56]
def r2sG : List Nat := [10, 18, 12, 20, 14, 22, 38, 10, 12, 18, 20, 26, 28, 38, 42, 50, 38, 44, 52, 42, 44, 50, 52, 58, 60]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := [8805289430026, 8813845809676, 37418361555978, 8805289432082]
def xsM : List Nat := roots_62.map (· &&& dom_62)
def goalM : Nat := goal_62 &&& dom_62
def NN : Nat → Nat
  | 4 => 2
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xa91103de7737b52f
  | 5, 0 => 0xa91103de
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x555555550000000000000000000000000000000000000000000000000000000055555500555555000000000000000000000000000000000000000000000000005555000055550000000000000000000000000000000000000000000000000000550055005500550000000000000000000000000000000000000000000000000050505050505050500000000000000000000000000000000000000000000000004444444444444444
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
  | 0, 0 => 0x1ffe0000000000000000000000000000000000000000000000000000000000001f81f800000000000000000000000000000000000000000000000000000000001e01e000000000000000000000000000000000000000000000000000000000001981980000000000000000000000000000000000000000000000000000000000007007c000000000000000000000000000000000000000000000000000000000000e073
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x1ffe0400000000000000000000000000000000000000000000000000000000001fedfbf0000000000000000000000000000000000000000000000000000000001e49e2a00000000000000000000000000000000000000000000000000000000019a5995000000000000000000000000000000000000000000000000000000000157357c0000000000000000000000000000000000000000000000000000000000a9eaf3
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

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
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

namespace S_15_32
def pairsG : List (Nat × Nat) := [(32, 33), (34, 35), (34, 38), (34, 42), (36, 37), (36, 38), (36, 44), (40, 41), (40, 42), (40, 44)]
def r1sG : List Nat := [32, 34, 34, 34, 36, 36, 36, 40, 40, 40]
def r2sG : List Nat := [33, 35, 38, 42, 37, 38, 44, 41, 42, 44]
def mpG : Nat := 0x3ff
def pool6G : List Nat := [39729121471014]
def xsM : List Nat := roots_15_32.map (· &&& dom_15_32)
def goalM : Nat := goal_15_32 &&& dom_15_32
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x5e2aba2c
  | 4, 0 => 0x5e2aba2c
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00000000000000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000cccc000000000000000000000000000000000000000000000000000000000000aaaa00000000
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_15_32 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_15_32 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_15_32 == dom_15_32) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_15_32 goalM u ys) : RunD dom_15_32 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_15_32 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_15_32 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_15_32 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_15_32 roots_15_32 goal_15_32 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_15_32 goal_15_32 := by
    have h0 : isConstB dom_15_32 goal_15_32 = false := by decide +kernel
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

end S_15_32

theorem low_15_32 : Lower dom_15_32 roots_15_32 goal_15_32 5 := S_15_32.noCircuit

namespace S_39
def pairsG : List (Nat × Nat) := [(1, 3), (1, 33), (2, 3), (5, 7), (5, 37), (6, 7), (6, 38), (32, 33), (34, 35), (34, 38), (36, 37), (36, 38)]
def r1sG : List Nat := [1, 1, 2, 5, 5, 6, 6, 32, 34, 34, 36, 36]
def r2sG : List Nat := [3, 33, 3, 7, 37, 7, 38, 33, 35, 38, 37, 38]
def mpG : Nat := 0xfff
def pool6G : List Nat := [6601971212547, 35188770210593]
def xsM : List Nat := roots_39.map (· &&& dom_39)
def goalM : Nat := goal_39 &&& dom_39
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x257ee561
  | 4, 0 => 0x257ee561
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00000000000000000000000000000000000000000000000000000000000000f0000000f0000000000000000000000000000000000000000000000000000000cc000000cc000000000000000000000000000000000000000000000000000000aa000000aa
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_39 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_39 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_39 == dom_39) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_39 goalM u ys) : RunD dom_39 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_39 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_39 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_39 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_39 roots_39 goal_39 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_39 goal_39 := by
    have h0 : isConstB dom_39 goal_39 = false := by decide +kernel
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

end S_39

theorem low_39 : Lower dom_39 roots_39 goal_39 5 := S_39.noCircuit

namespace S_30_32
def pairsG : List (Nat × Nat) := [(34, 38), (34, 42), (34, 50), (36, 38), (36, 44), (36, 52), (40, 42), (40, 44), (48, 50), (48, 52), (56, 58), (56, 60)]
def r1sG : List Nat := [34, 34, 34, 36, 36, 36, 40, 40, 48, 48, 56, 56]
def r2sG : List Nat := [38, 42, 50, 38, 44, 52, 42, 44, 50, 52, 58, 60]
def mpG : Nat := 0xfff
def pool6G : List Nat := [39729121471014]
def xsM : List Nat := roots_30_32.map (· &&& dom_30_32)
def goalM : Nat := goal_30_32 &&& dom_30_32
def NN : Nat → Nat
  | 3 => 2
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xe3dcb3504b5c3f1e
  | 4, 0 => 0x4b5c3f1e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x55555500000000000000000000000000000000000000000000000000000000005555000000000000000000000000000000000000000000000000000000000000550055000000000000000000000000000000000000000000000000000000000050505050000000000000000000000000000000000000000000000000000000004444444400000000
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_30_32 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_30_32 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
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

def isoMv_55 : List (Nat × Nat) := [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_55 : Lower dom_55 roots_55 goal_55 8 :=
  lower_iso isoMv_55 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47

def isoMv_62_1 : List (Nat × Nat) := [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]
theorem low_62_1 : Lower dom_62_1 roots_62_1 goal_62_1 6 :=
  lower_iso isoMv_62_1 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_59_4

def isoMv_23_32 : List (Nat × Nat) := [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_23_32 : Lower dom_23_32 roots_23_32 goal_23_32 5 :=
  lower_iso isoMv_23_32 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15_32

def isoMv_43_4 : List (Nat × Nat) := [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]
theorem low_43_4 : Lower dom_43_4 roots_43_4 goal_43_4 5 :=
  lower_iso isoMv_43_4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15_32

def isoMv_51_4 : List (Nat × Nat) := [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]
theorem low_51_4 : Lower dom_51_4 roots_51_4 goal_51_4 5 :=
  lower_iso isoMv_51_4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15_32

def isoMv_29 : List (Nat × Nat) := [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]
theorem low_29 : Lower dom_29 roots_29 goal_29 5 :=
  lower_iso isoMv_29 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_39

def isoMv_30_1 : List (Nat × Nat) := [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_30_1 : Lower dom_30_1 roots_30_1 goal_30_1 5 :=
  lower_iso isoMv_30_1 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15_32

def isoMv_46 : List (Nat × Nat) := [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)]
theorem low_46 : Lower dom_46 roots_46 goal_46 5 :=
  lower_iso isoMv_46 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_39

def isoMv_54 : List (Nat × Nat) := [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]
theorem low_54 : Lower dom_54 roots_54 goal_54 5 :=
  lower_iso isoMv_54 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_39

def isoMv_60_1 : List (Nat × Nat) := [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem low_60_1 : Lower dom_60_1 roots_60_1 goal_60_1 5 :=
  lower_iso isoMv_60_1 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15_32

namespace S_63
def pairsG : List (Nat × Nat) := [(1, 3), (1, 33), (2, 3), (2, 10), (2, 18), (4, 12), (4, 20), (5, 7), (5, 13), (5, 21), (5, 37), (6, 7), (6, 14), (6, 22), (6, 38), (8, 10), (8, 12), (9, 11), (9, 13), (9, 25), (9, 41), (16, 18), (16, 20), (17, 19), (17, 21), (17, 25), (17, 49), (24, 25), (24, 26), (24, 28), (32, 33), (34, 35), (34, 38), (34, 42), (34, 50), (36, 37), (36, 38), (36, 44), (36, 52), (40, 41), (40, 42), (40, 44), (48, 49), (48, 50), (48, 52), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [1, 1, 2, 2, 2, 4, 4, 5, 5, 5, 5, 6, 6, 6, 6, 8, 8, 9, 9, 9, 9, 16, 16, 17, 17, 17, 17, 24, 24, 24, 32, 34, 34, 34, 34, 36, 36, 36, 36, 40, 40, 40, 48, 48, 48, 56, 56, 56]
def r2sG : List Nat := [3, 33, 3, 10, 18, 12, 20, 7, 13, 21, 37, 7, 14, 22, 38, 10, 12, 11, 13, 25, 41, 18, 20, 19, 21, 25, 49, 25, 26, 28, 33, 35, 38, 42, 50, 37, 38, 44, 52, 41, 42, 44, 49, 50, 52, 57, 58, 60]
def mpG : Nat := 0xffffffffffff
def pool6G : List Nat := [5506754552067, 8805289430026, 8813559747852, 9917366342925, 9904598878723, 9904279257866, 18700372804370, 9930234139146, 18730387114521, 8822435744268, 37387793466145, 8822469299210, 39728582494758, 26397021635346, 6601971212547, 18730437577753, 44006841388042, 44127100472330, 39729119365670, 39617351256588, 9900186010378, 9900186472970, 9930537246988, 52785754543122, 39651710997012, 26397155853066, 17618528768532, 26397021637138, 26405745792012, 26405611572244, 17618562323474, 26461866101273, 26427506364953, 18700691900931, 6619151081731, 18709030177812, 39586816721697, 17613813517332, 26410040759308, 26409906539540, 39608207344422, 39608274453286, 37456814082563, 37422454344195, 26461327721241, 26426968507161, 37456512942881, 37409318308902]
def xsM : List Nat := roots_63.map (· &&& dom_63)
def goalM : Nat := goal_63 &&& dom_63
def NN : Nat → Nat
  | 5 => 8
  | 6 => 178
  | 7 => 628
  | 8 => 324
  | 9 => 27
  | 10 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0xbd833101af7b41608d1ca8dc7b30d80578541dd63d6a961f2bb7871910e06323
  | 6, 0 => 0x3d3686f93c90e5203c86b61d38b24b9338195c98376135eb36bd7d74362870953404b2bb3321cd972ee671c32e6696882e6465742df03b792cdbd8fc2bcf3abb2b87ab452ad8cf3a2a836aa229462f522937eecd2909654c290742552779c54f2778c5f626c09f4926acc7fc249d0b20240fb771215ad64c2075da641fdef7c21ed15b311cc171cc1a42695c18a598b0175b7e69170619d1160c315a136f20cf129bea2211be358b1190f3ee112237ac0fa22a3f0ef4efd40d3f24990cebd4d20c236eef0b1f72c00a2e37410a0bf17108f317a5084a45320752e66507517d1206e4336306165d760600e4f7045c95cf0407793402c301a200a82ad90026e37e
  | 6, 1 => 0x8b1537598a7a77118744a6f88421f2788250d0be7a454d6578e4257577a12a99777e023776e30370756280737540a7b374cf39e4734bd994722eeeb671c1199471a3faaf6e464e246bc292956a8772f968e5d86667ad4f1567aab8ca64bae295647c796e646547fe633b241c60326b045ef19ced5e2d8aab5d976ce45d71535d5c6c66715c4f99345b5f0c2b5a0571ee57856ccf57530f6056488c3a54861fec546ec5c4529a8d7a527bcb805219ec944fcffd714df8f18d4c30865f4bf409854b3c5c5b4a7fb41e4952e2354841176a46e4d62d4585704045767ad544d8a15244171c5a44081bfe43660a1b4266a0bd40f14f1240c3d0f13ebd5be63d513e8d
  | 6, 2 => 0xfe552278fd1d4291f7a9ae90f19ec62cef8ecdc7ef871f07eca992adebefca4be91adb21e8d9024ce85d85b9e49ceb8de3f7e16be25c5844e176c27ddf3c211ede2d9d58daa4c961d9af5a0fd9ad9916d6e25d60d4e034e8d343e014d1bcabd4cc64bb85c77f38fbc219efd3c1c1b5f9c116d5dfb8e76ab4b5640a2ab46ce8cdb2bd957cb0bea196af5e1350aea42dd9ad99850ea8531185a5ab77aea5743486a35c9dd6a2ea72c69554ae35911edd149094fad8905b8c8c8f95c6338e8df0778caeea318c9dac05
  | 7, 0 => 0x109410fb10835d3110813ea3105fce31104862a50fceabe00fa345310f9aa5fd0f1986a90f115ba20ee2d2210ee0af2a0edf18670ecc23a60e974d5b0e7db3450e1f184a0db432850d7f85ab0d3586890d1802ee0d05cbda0c825c970c232aad0bb0c3ae0b80dabe0b5bfccf0b2c8ce60af197a60a7677f50a75789c09d9969709bd51ef09695d40092be94c0919997808e4c69e080280eb07ca96c507c20e2707a99a0b078179cf0711d49e0651b5d50641c56506237d4e05b86497057c0b7a04e553f804ccdfdc04aea855048dacd70442bd8603d4cc4103abb2f00294122e020567c901cde881016603570155178300f9b8fb00d76e0200b912070046618f
  | 7, 1 => 0x21d562ba21997fae20eebdc4204fb0ae204a722020292edb1fecb1011f8ca3c51f5f0d481ed55caf1e4837591df8f12c1df73f721db574801d826c881d06d2eb1cd038361ca81a3a1c96ea491c8d62a61c1250521bbaa2fd1baefe391b9935371b7eaebf1afecaa01ac988c51ac819931aa1953a1a548add1a4dc7a419f37e0719c7c79119ba301a18f811bf1891280c1860cf55182bf926181c7acd1813153417b7e34f17b77a521734bd5617016561167fda5b1673385e166385a0165ce3e9161648bc15ff6d7d15f4eac915f3a7e415d3b4e415ba6e6315af65f1156a912f153fc09e14446e3c13ea83c213e030a0119557c6118eca21117804a41161181a
  | 7, 2 => 0x32fa2f9532a889b1328e8708318125c63115c93030dba21430bfbacf30b4f53230ad467230a485e02fa88bf32f2d39052e9b5e9e2e3b996a2e1a843f2dd75a262dcb18752d6efea02d52d1502d3e70562d076f792ce139a22c8e77b92c7c27652bbea46f2b87620c2b811d732b08f8cc2afe09d52ae913f02a245e7b29e188d329e0d67129af2b64297c99f829428e4b293f76f029259dd728bd116f28a4a83e28732d7b286028b1285879f1284514cc27fcc31727bb223c2724c80b2713cf0026f168c926e23bf026ae43ee2648e3a82576c64a24fedf5924f59d08243e50102416c07e2414ae9a23ee01b823c08397232c6add2325c90b22c96b3021eaa96f
  | 7, 3 => 0x43c1fcc943b837ee439406ca434ac032431f7df7430c7f9b429e731941b8ea3b40e5429a40e1c31a40bbc127406a83da402fc56c401a1c4f3fdedec33fdba9f43fd62b933f8aca813f71238c3f3bf5403f2afc363e6664c13df3c1173d3e89f93d2c7c353cfeefc53cfaa5163cedc83e3c21f90f3c21b4153b1550ef3b05d6f73a8512d93a4fc20639c634793926b9f838eeefa638cb099b389cbe363897fbf1388be5c4382f747e37b0076a37a858aa37a858a73791ff6b37509135373f4ec136c1640236b521a2364691d83627386535a96a46359f67e7359740203587494435787e2635169f3a345ddff533d25e6233cd017f33b85c4333a9e629334a7e36
  | 7, 4 => 0x5b3bed485aa8a6b95a7ee54859fcbebe59c5935f59a0c2fc5925466959100b805875705b583d5a595810d46d5802414f57a48719571462ac56488c3a551f842c5462936b53c0149952e2321e52a2b5415257aedf50eca9cc4fbdd0064ebf453b4e2ce2974e086b364d86bbea4d84259f4d5b0f8d4d1a0f054ce115d74cd5ea514ca859dc4c16af5f4bd15be94bacc54f4b8c97694b50406a4b48acc94b25a97b4b0c2c394aeba8ec4adf60974acde2064a9428d24a55e6434a3f5f3c49fd469d49c3e2a949bb2fc349292ce248a6ffde47b76ea347703dcb4755b84446de759446c7cf07464630554625da8245a7f598459ecff7445ca64c441caf3c43fdf1ec
  | 7, 5 => 0x727718da718aa31d7179360f716feb897108872f70eea42e70607efa70120e99700aec186fb93c616fb8decd6f410f6b6ee314666edb0ec36ecfcc7c6e65b5e26e0e67d66e01622c6e008d486de93f766d32e2006cc11e926c64553c6b302ff16a8281de6a41599e689b990368716f40684a9053683daa90682efe61680f799367c6dab46786b8476733942567240676671ea51e671066ce66e4732066d0a35666b2ba9b6685c7206532bf6464a0c73f64497e5c640f62e36332600f62d73fc861d0c2e560fe5bb260bcca6960afae3b601579706008d5905edbff035ecd913b5d71535d5d5fdc975d0b15675cb746015c97debb5c3b8dfc5bf13ab45b65c395
  | 7, 6 => 0x9117715e9112800b8f7b76b18e3f8c778dc0b2f38cfa91f68cd916648b4da15b8b1fd6d78b16092c8b0e758b8a81f0ca89d9702088e50a948826fc3987c3e76586d3f20a86c3fb2e8672012f85f1f72685644eea8475b5338436e17f83f53a1c836290978323a63b82cfc521821853fe820b9a5f81e9f85c812adf778101e0aa8069eaef7fd8d7587f65878f7f2587b17f24c13b7eadd0e57ead80c27eabb08a7e9aa7927bff7fac7bf8b5337bd0c6937aaf2d897a399f0c79952bdb791205e278b01035789cb22c7851225b7812897277abf41377728e4a77231e6a76df94a6765ba64374d57dbf74cf39e47407475673437dc2733d888d7301de5f7288949c
  | 7, 7 => 0xae68ce65ae18ff3dad9c65faad909eb6ad58a5d0ace974c5aae6feafaa2ce68baa26b057a9f3d131a994b72fa828f69ba6e98352a63c52c1a6193286a5b66d6ea54be63aa528621ea5141b3ba411e8baa3147353a23d1ba0a170cb80a09db9cc9f1c706f9f0809ca9ec0d7899d648c2e9cf112e89c86b7d99b258fe99a8abc959a88f9d89a55e6669a4655a29a18a88399f80ac699ef52009985a136989eac8e9823da6497f30604977488ac976491d09736bddf9710a458970d416896a2e0f9969aeb7294d7782194c7ea7294ad793f949f308d947d9aae9372f1e3931be89e92f43a3092d649fa92b8eaa09231308291d9edf19197d4829196ca6a9190d39c
  | 7, 8 => 0xd735f252d70862e2d67aeb44d53d3f77d4bbded6d35c42c7d282ff82d0ad1508cf84fccdcf102a8ccf0b78d5cef767cfcdd6b28fcd28ef85cc452051cbedcfe9cb08702acad172fbc9d14e40c82cddd4c7b46166c71007f0c61f7a8bc5368674c5158df3c4e635f6c4b48854c42cd5adc4070a2dc3651e39c307bc52c20018d3c19d30e4c0e08b57c088084cbf8705ebbf7afac2bebb555abe4be64fbe18d688bd41015bbd2fc437bcbbca35bc62e41ebb75fc4ebb727797bab9a1bdba1aa2e5b91d4ce9b79618a9b64eb09ab60f96a1b5446adbb448fca3b3c1e194b2b29e6bb2131be6b18d6e74b17989ffb1522b5ab081bca1b06a21d7af79815caedf1679
  | 7, 9 => 0xfdfab3d3fdf6b6b9fc151d11fbf20813fb55f38cfad9fd75f9050bc6f77446d5f72a0023f6535463f5277aadf49519fef10d01a6f0f8df95f0556ec8f0479b38ef5c9650edb71183ed2ae9e7ed215bcfeca5df3cebefca4beb7dc701eb03cd4bea4f990be9cf7cc3e7f96942e63f7e3be56d3923e5274fd4e4f80626e4b5bc3ce403206de3af474de2f6af66e28853e8e274b8a0e1151f08e041dc16df0e0ed4ddf8e307ddb9d253dd420304dbcabd8fdb29872fd9ad9916d9288e6bd872797ad86386c7d7f61629d7a5749ed7783301
  | 8, 0 => 0x24cb7b292310763b23038dd422d85c9a22c735132219ec0a2179389d20df43cc2064873a20292edb1fb72b911f3d31db1e08e1531d89743f1d81c57f1d29fe0a1c1ffead1bde45011b8548e61b78d4bc19b1d4481923eb0b1900f4291881f686175a929b16e8db1816b50ee915f022ce1581f8c8141a4f1c1415063f1317dd2b12baa67712b8884a12324797119811441187183a10c280c51004221f0f8b2a5f0f8898390e8414b20e7e15130e7dd0190e783ebe0df078900d61f2fb0cabde0a0c22507d0c167f100b41c7720acf09dd0ab8b26f09ee1b6f06b07a0306291d8305c61dd605169eb003476202023f103c0188fb4b00f5a3d20086a50c00273479
  | 8, 1 => 0x4e1db72a4e1717654cfd734b4c4c79c44bf147df4bc969994bb8974e4b6e21e64b0c2c394aee73794a0d1974499b08ca48b0ac9d4609964844cd758b43555fb0434ac0324309ffd8430588364214fad141a83906413f306a40bb2834405c8f3d40455b7a3d6d0b963cedcf813c9d75a23c8fe41f3c21f90f3afd7b253a8b1a65396f572d387c2216359f67e7358e7c1334746a9f342cdee934064f6c32ba82ac3264f19431381b073129ad3f3122199e2fc976f62f7655c82f1362052d90db782d6df75a2cb7e2692baacaed2ba0a43a2b81626d2acd7a982a6cf0712a60bc7d291abe5628a4a83e2774c460275958f226beaf6f26bb2fef261c309d26093241
  | 8, 2 => 0x7ab597257aa157477a85129f79e15a287892577577f10ba277d135d07770373f76f0de33745a681c73f60c3a72b2833970cdf07470946692705b5d9f6f6c29a26ebe77696cd622c66c4b6e046be1bd3a6bcb63fb6b58c0516afac8926a7ff6686a4f220869d0a4b069c0add467f1c0d3679d352a6733942567044c4c66fb4c91651506a464e6ab0263669d9561aa336861a8633060b58bf55f5d13a95debf6475d7bf2db5cde0cce5c91de815b4388f85b2acd595af03eb05aa8a6b959e9c31b5916f56258905d13584e132a5806ebe2568ff7f15640306854b47b98530ec13f523dc21151bb2a0f51099cc6505beeb34f943bc44f0fba7a4ed5e3f64e2ce297
  | 8, 3 => 0xaa8df529aa87c3f1a98e4816a9647ee6a8e78fc4a8d9852aa8d69abba5103ec2a494c22fa3f2435da309310ca16c4690a1662bafa02ef21b9e58572e9c97dd089b1dd7b09aec1f2b996c23f4992721c2981b7e9297ec88bb9710a45894b8834e91b98d129117715e9074f28c8f9d1d5f8f6e24048ebf00228e4941358e21c9a38dce939b8d6fdaea8d5eaaf98ce77a638c8386ea8c76bee98bbc73f08b8fda438a8bfac78a81f0ca89211e6a88ede028886bb2a5877c8a9f86bb6894869b7594867726a185520fcd8492c7cd83f048fb83d9bb2c833df90382ddd8a5806266ad7f5f0e0b7f4590c97e8559377dfd47397d7d57bc7d356db97cea112d7bf0d333
  | 8, 4 => 0xfab495f5f9b99d75f96feb04f8b72109f74120e2f5493ef0f2854adff17a65ebeef3064dee22ff53ed71b5aeeabec0cde878be20e73f702ce48a3599e3d420a8e2f7dbbfe2f02cffe25263cde1283faadf71e0b2dede789bdd4db3aad96359b3d89de169d630e845d355d4ffd3152e0bd1d3f658d1786b89d0dd3a20ce8cc780cdd2d617cdb20f90cbfcbae9cb46a5f8c8d8951dc876c3bec7ad77bcc7554d2ec5e58a67c5690328c31b6fd9bf8705ebbf01fb40be4be64fbde1cfb5bc545819bbb69bf5ba45dd7fb9782853b81d78f4b59a84ddb52557b8b4e46fecb4d0d4a4b37ef559b315333eb0e1dcffb080f6ebb038e43cae064aa9ace974c5aabfa2cb
  | 8, 5 => 0xffcceadcfbefb591fb7259a6fabc44b5
  | 9, 0 => 0xf33b5fd0f2854adfdd9de376c3d681efbad4da249b34b1218a7994f87f4590c97cea112d76f0de33764e5f61705b5d9f61ca40085fbac6fd5cde0cce51bb2a0f5059633d4aee737942b779a33e277fff34064f6c2eedfa851b78d4bc1729918f1561a43a0e7e151305169eb0
  | 10, 0 => 0x42b779a3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf3f3f3f300000000000000000000000000000000000000000000000000000000eeeeeeee00000000000000000000000000000000000000000000000000000000cccccccc00000000000000000000000000000000000000000000000000000000aaaaaaaa0000000000000000000000000000000000000000000000000000000077777777000000000000000000000000000000000000000000000000000000005555555500000000000000000000000000000000000000000000000000000000333333330000000000000000000000000000000000000000000000000000000000ff00ff
  | 0, 1 => 0x33330000ffff000000000000000000000000000000000000000000000000000033330000333300000000000000000000000000000000000000000000000000000f0f0000ffff00000000000000000000000000000000000000000000000000000f0f00000f0f000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000330000003300000000000000000000000000000000000000000000000000000000ffffffff00000000000000000000000000000000000000000000000000000000fafafafa
  | 0, 2 => 0x5500550055005500000000000000000000000000000000000000000000000000330077003300770000000000000000000000000000000000000000000000000033003300330033000000000000000000000000000000000000000000000000000f000f000f000f0000000000000000000000000000000000000000000000000000ffff0000ffff000000000000000000000000000000000000000000000000000055550000ffff000000000000000000000000000000000000000000000000000055550000555500000000000000000000000000000000000000000000000000003f3f00003f3f
  | 0, 3 => 0xc0c0c0c0c0c0c0c0000000000000000000000000000000000000000000000000a0a0a0a0a0a0a0a00000000000000000000000000000000000000000000000007070707070707070000000000000000000000000000000000000000000000000505050505050505000000000000000000000000000000000000000000000000030303030303030300000000000000000000000000000000000000000000000000ff00ff00ff00ff00000000000000000000000000000000000000000000000000770077007700770000000000000000000000000000000000000000000000000055005500ff00ff
  | 0, 4 => 0x3333303033333030000000000000000000000000000000000000000000000000303030303030303000000000000000000000000000000000000000000000000022222222222222220000000000000000000000000000000000000000000000001313131313131313000000000000000000000000000000000000000000000000111111113333333300000000000000000000000000000000000000000000000011111111111111110000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000000f0f0f0f03030303
  | 0, 5 => 0x55555555000000000000000000000000000000000000000000000000000000005050505050505050000000000000000000000000000000000000000000000000444444444444444400000000000000000000000000000000000000000000000033333333333333330000000000000000000000000000000000000000000000003333333333330000000000000000000000000000000000000000000000000000333333333300330000000000000000000000000000000000000000000000000033333333000000000000000000000000000000000000000000000000000000003333330033333300
  | 0, 6 => 0xa5a5a5a5a5a5a5a5000000000000000000000000000000000000000000000000a0a0a0a0a0a0a0a000000000000000000000000000000000000000000000000099999999999999990000000000000000000000000000000000000000000000008f8f8f8f8f8f8f8f0000000000000000000000000000000000000000000000008888888888888888000000000000000000000000000000000000000000000000777777777777777700000000000000000000000000000000000000000000000066666666666666660000000000000000000000000000000000000000000000005555555555555555
  | 0, 7 => 0xaaaaaaaa55555555000000000000000000000000000000000000000000000000aaaaaaaa00000000000000000000000000000000000000000000000000000000aaaaaa00aaaaaa00000000000000000000000000000000000000000000000000aaaaa0a0aaaaa0a0000000000000000000000000000000000000000000000000aaaa8888aaaa8888000000000000000000000000000000000000000000000000aaa0aaa0aaa0aaa0000000000000000000000000000000000000000000000000aa88aa88aa88aa88000000000000000000000000000000000000000000000000a8a8a8a8a8a8a8a8
  | 0, 8 => 0xbbbbbbbb33333333000000000000000000000000000000000000000000000000aeaeaeaeaeaeaeae000000000000000000000000000000000000000000000000aaaaaaaaaaaaaaaa000000000000000000000000000000000000000000000000aaaaaaaaaaaa8888000000000000000000000000000000000000000000000000aaaaaaaaaaaa0000000000000000000000000000000000000000000000000000aaaaaaaaaa88aa88000000000000000000000000000000000000000000000000aaaaaaaaaa00aa00000000000000000000000000000000000000000000000000aaaaaaaa88888888
  | 0, 9 => 0xccccc0c0ccccc0c0000000000000000000000000000000000000000000000000cccc8888cccc8888000000000000000000000000000000000000000000000000ccc0ccc0ccc0ccc0000000000000000000000000000000000000000000000000cc88cc88cc88cc88000000000000000000000000000000000000000000000000c8c8c8c8c8c8c8c8000000000000000000000000000000000000000000000000c3c3c3c3c3c3c3c3000000000000000000000000000000000000000000000000c0c0c0c0c0c0c0c0000000000000000000000000000000000000000000000000bbbbbbbbbbbbbbbb
  | 0, 10 => 0xccccccccccffccff000000000000000000000000000000000000000000000000cccccccccccccccc000000000000000000000000000000000000000000000000cccccccccccccc00000000000000000000000000000000000000000000000000cccccccccc00cc00000000000000000000000000000000000000000000000000cccccccc88888888000000000000000000000000000000000000000000000000cccccccc33333333000000000000000000000000000000000000000000000000cccccccc00000000000000000000000000000000000000000000000000000000cccccc00cccccc00
  | 0, 11 => 0xeeeceeeceeeceeec000000000000000000000000000000000000000000000000eee0eee0eee0eee0000000000000000000000000000000000000000000000000ecececececececec000000000000000000000000000000000000000000000000eaeaeaeaeaeaeaea000000000000000000000000000000000000000000000000e0e0e0e0e0e0e0e0000000000000000000000000000000000000000000000000dddddddddddddddd000000000000000000000000000000000000000000000000cececececececece000000000000000000000000000000000000000000000000cccccfcfcccccfcf
  | 0, 12 => 0xeeeeeeeeeeeeeeee000000000000000000000000000000000000000000000000eeeeeeeeeeeecccc000000000000000000000000000000000000000000000000eeeeeeeeee00ee00000000000000000000000000000000000000000000000000eeeeeeeecccccccc000000000000000000000000000000000000000000000000eeeeeeeeaaaaaaaa000000000000000000000000000000000000000000000000eeeeeeee00000000000000000000000000000000000000000000000000000000eeeeeecceeeeeecc000000000000000000000000000000000000000000000000eeeeeeaaeeeeeeaa
  | 0, 13 => 0xf0f0f0f0fcfcfcfc000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000000f0f0f0f0f0f0f000000000000000000000000000000000000000000000000000f0f0f0f030303030000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000f0f0f0c0f0f0f0c0000000000000000000000000000000000000000000000000f0f0c0c0f0f0c0c0000000000000000000000000000000000000000000000000f0c0f0c0f0c0f0c0
  | 0, 14 => 0xfafafafaaaaaaaaa000000000000000000000000000000000000000000000000fafafafa00000000000000000000000000000000000000000000000000000000fac8fac8fac8fac8000000000000000000000000000000000000000000000000f8f8f8f8f8f8f8f8000000000000000000000000000000000000000000000000f5f5f5f5f5f5f5f5000000000000000000000000000000000000000000000000f4f4f4f4f4f4f4f4000000000000000000000000000000000000000000000000f3f3f3f3f3f3f3f3000000000000000000000000000000000000000000000000f3f3f3f300000000
  | 0, 15 => 0xfcfcfcfccccccccc000000000000000000000000000000000000000000000000fcfcfcfca8a8a8a8000000000000000000000000000000000000000000000000fcfcfcf0fcfcfcf0000000000000000000000000000000000000000000000000fcf8fcf8fcf8fcf8000000000000000000000000000000000000000000000000fafafafafafafafa000000000000000000000000000000000000000000000000fafafafafafa0000000000000000000000000000000000000000000000000000fafafafaf8f8f8f8000000000000000000000000000000000000000000000000fafafafaf0f0f0f0
  | 1, 0 => 0xff44ff44ff44ff44000000000000000000000000000000000000000000000000ff33ff33ff33ff33000000000000000000000000000000000000000000000000ff30ff30ff30ff30000000000000000000000000000000000000000000000000ff11ff11ff11ff11000000000000000000000000000000000000000000000000ff00ff00ff00ff00000000000000000000000000000000000000000000000000fefefefefefefefe000000000000000000000000000000000000000000000000fcfcfcfcfcfcfcfc000000000000000000000000000000000000000000000000fcfcfcfcfcfc0000
  | 1, 1 => 0xffc0ffc0ffc0ffc0000000000000000000000000000000000000000000000000ffaaffaaffaaffaa000000000000000000000000000000000000000000000000ffaaffaaff88ff88000000000000000000000000000000000000000000000000ffaaffaaff00ff00000000000000000000000000000000000000000000000000ffa0ffa0ffa0ffa0000000000000000000000000000000000000000000000000ff88ff88ff88ff88000000000000000000000000000000000000000000000000ff55ff55ff55ff55000000000000000000000000000000000000000000000000ff50ff50ff50ff50
  | 1, 2 => 0xffeeffee00000000000000000000000000000000000000000000000000000000ffccffccffccffcc000000000000000000000000000000000000000000000000ffccffccffccff00000000000000000000000000000000000000000000000000ffccffccff00ff00000000000000000000000000000000000000000000000000ffccffccaa88aa88000000000000000000000000000000000000000000000000ffccffcc00000000000000000000000000000000000000000000000000000000ffccff88ffccff88000000000000000000000000000000000000000000000000ffccf0c0ffccf0c0
  | 1, 3 => 0xfffcfffcfffcfffc000000000000000000000000000000000000000000000000fffafffafffafffa000000000000000000000000000000000000000000000000fff8fff8fff8fff8000000000000000000000000000000000000000000000000fff0fff0fff0fff0000000000000000000000000000000000000000000000000fff0fff0fff00000000000000000000000000000000000000000000000000000fff0fff0ff00ff00000000000000000000000000000000000000000000000000ffeeffeeffeeffee000000000000000000000000000000000000000000000000ffeeffeeffccffcc
  | 1, 4 => 0xffffa0a0ffffa0a0000000000000000000000000000000000000000000000000ffff8888ffff8888000000000000000000000000000000000000000000000000ffff5555ffff5555000000000000000000000000000000000000000000000000ffff4444ffff4444000000000000000000000000000000000000000000000000ffff3333ffff3333000000000000000000000000000000000000000000000000ffff3333ffff0000000000000000000000000000000000000000000000000000ffff0033ffff0033000000000000000000000000000000000000000000000000ffff0000ffff0000
  | 1, 5 => 0xffffccccffff0000000000000000000000000000000000000000000000000000ffffccccff00cc00000000000000000000000000000000000000000000000000ffffcccc00000000000000000000000000000000000000000000000000000000ffffccc0ffffccc0000000000000000000000000000000000000000000000000ffffc8c8ffffc8c8000000000000000000000000000000000000000000000000ffffc0c0ffffc0c0000000000000000000000000000000000000000000000000ffffaaaaffffaaaa000000000000000000000000000000000000000000000000ffffaaaaffff0000
  | 1, 6 => 0xfffff0f0ff00f000000000000000000000000000000000000000000000000000fffff0f0aaaaa0a0000000000000000000000000000000000000000000000000ffffeeeeffffeeee000000000000000000000000000000000000000000000000ffffeeeeffffcccc000000000000000000000000000000000000000000000000ffffeeee00000000000000000000000000000000000000000000000000000000ffffececffffecec000000000000000000000000000000000000000000000000ffffccccffffcccc000000000000000000000000000000000000000000000000ffffccccffff8888
  | 1, 7 => 0xffffffaaffffff00000000000000000000000000000000000000000000000000ffffffa0ffffffa0000000000000000000000000000000000000000000000000ffffff88ffffff88000000000000000000000000000000000000000000000000ffffff00ffffff00000000000000000000000000000000000000000000000000fffffcfcfffffcfc000000000000000000000000000000000000000000000000fffffcfcffffcccc000000000000000000000000000000000000000000000000fffff0f0fffff0f0000000000000000000000000000000000000000000000000fffff0f0ffff0000
  | 1, 8 => 0xffffffff05050505000000000000000000000000000000000000000000000000ffffffff00000000000000000000000000000000000000000000000000000000fffffff0fffffff0000000000000000000000000000000000000000000000000fffffff0ffffff00000000000000000000000000000000000000000000000000ffffffccffffffcc000000000000000000000000000000000000000000000000ffffffccffffff00000000000000000000000000000000000000000000000000ffffffc0ffffffc0000000000000000000000000000000000000000000000000ffffffaaffffffaa
  | 1, 9 => 0xffffffffcccccc00000000000000000000000000000000000000000000000000ffffffffcc88cc88000000000000000000000000000000000000000000000000ffffffffaaaaaaaa000000000000000000000000000000000000000000000000ffffffff88888888000000000000000000000000000000000000000000000000ffffffff55555555000000000000000000000000000000000000000000000000ffffffff33333333000000000000000000000000000000000000000000000000ffffffff11111111000000000000000000000000000000000000000000000000ffffffff0c0c0c0c
  | 1, 10 => 0xfffffffffff0fff0000000000000000000000000000000000000000000000000ffffffffffaaffaa000000000000000000000000000000000000000000000000ffffffffff00ff00000000000000000000000000000000000000000000000000fffffffffcfcfcfc000000000000000000000000000000000000000000000000fffffffffafafafa000000000000000000000000000000000000000000000000fffffffff0f0f0f0000000000000000000000000000000000000000000000000ffffffffeeeeeeee000000000000000000000000000000000000000000000000ffffffffcccccccc
  | 1, 11 => 0xffffffffffffff00000000000000000000000000000000000000000000000000ffffffffffffcccc000000000000000000000000000000000000000000000000ffffffffffffaaaa000000000000000000000000000000000000000000000000ffffffffffff0000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xc6a08331215c6a68a67215cca083671d5c6836e35135c6a08335215c6a0834a305cca08a67215c6a683671d5
  | 6, 0, 0 => 0xc6a983563b21600c9a083564521600cc836e452c13600c6a9836e6656600836e302c1309600c6a078452c1a600c6836e474513600cca083452c21600c66e67331a13600a083302c2109600a092836e5642600d8bc8c6e5645600c6a06733211a600d8a0836e4523600c6aaa081451a600c6a66e452c1a6
  | 6, 0, 1 => 0xc6a0835637500c6a083564a45600cca083564534600c66e56451813600c6a083564221600c6a983564321600d26b56451a13600c67456451a13600c8a083452c21600c6a08a56453460000cca08a6e67500c66e64451a13600c68149451a13600c6a083452c20600a68356452109600c6bcae6e56456
  | 6, 0, 2 => 0xa08367623321600c6a0836e422c600c6a9836e432c600c6a06e452c18600c6a683563021600a08356452106600c6a083674021600836e67331309600d58378564513600cd6e563e1a13600d2a06b452c1a600a08367332109600c6a074452c1a600a0836e625639600c6bc906e5645600cca0836745216
  | 6, 0, 3 => 0xc6aaa0838130600c6a06e48251a600a0836e452c06600766e56451a13600d5a08378452c600cda06e3e2c1a600c6452c211a13600b3a0836e563b600837456451309600c6a68356451d600c6a06e5045156d0bcb8836e5645700836e67623313600c6a06e564516600d8bf8c6e5645600c6bcaa8381456
  | 6, 0, 4 => 0xcea083564521600c6a08367331d600a0766e452c1a600c6a083674e21600c66e5645191360000c6a6837467500d0836e634513600c6a08378302c600836e62452c13600c6a056452119600a0835645210360000a0836e5245500d5836e644513600c6836e452313600a08356452107600d0a06e51301a6
  | 6, 0, 5 => 0xc6a696836e67600c6c1a0838145600c6a66e67561a600c6a08a675621600c6a06e452c1960083452c211309600c6a083302c21600c6a86e452c1a600a06e6256301a600d2836b563013600ca836e45291360083706e452c13600c6a08d564521600cca08a564521600c68381493013600c6b16e4e451a6
  | 6, 0, 6 => 0xc6a0834a45500c6a06c452c1a600cc6e56451a136006e56301a1309600cca05645211a600d0a083544521600a05630211a09600c6bcb76e5645600d0a083534521600c6a08c6e302c600d2a0836b302c600c6a083452c1d600c6a06e4c451560000c6a0836e35500c6a683816e67600c6a6835645216
  | 6, 0, 7 => 0xc6a683452c21600c6a09a968145600c6837b362c13600c68371452613600a66e56451a09600cca083746e67600c6836e674c13600d8a08c6e452c600c7a083563021600d5bca0785645600c6a68367332160083766e563013600c6a083673321600c683302c2113600c6a06e33221a600c6a08a746e676
  | 6, 0, 8 => 0xcca08356451d600cda083564021600d8d5bc564521600a0836e452c086006e6256451a13600cca08356302160000c6a0836e315d0bcaf836e564570000c6a68a6e67500a08356452009600a093836e563e600d5bca06e6445600c6a08d7b6e56600d06e51451a13600c6a083814510600c6a0836732216
  | 6, 0, 9 => 0xa06e56451909600cca083564521600c6b1834e4521600c65630211a13600c6a0835a2d21600c6a68a5645216006e452c1a1309600c6a083482521600c6a08349301b60000cca0837467500d8d5bc6e452c6005645211a1309600c6a083673433600c6a096504521600c6a06e675619600c8a0835630216
  | 6, 0, 10 => 0xc67856451a13600cca083673321600cda0836e4523600c6a0836e3023600c6a65645211a600a0836e302c096d0c4a0836e5645700c67b56361a13600c66e302c1a1360000a0836e563f500c6a083605621600a08356451d09600d8d56e56450b600c6a091564521600cfa083564521600d8a06e5645186
  | 6, 0, 11 => 0xc6a08356301d600c6a0833322216
  | 7, 0, 0 => 0xa0836762564521700c6a08e83675621700c6bca096564521700c6a09683816845700c6836e56302c13700d5a0836e453e2c700c6b0a0836e5645700c6a083726e5630700c6bcb1966e5645700c6b5a083564521700c6a08356302c21700c6b9a06e56301a700c6c5a0836e452c700836e6756451309700c6a0836e45392c70000c6a083814d456
  | 7, 0, 1 => 0xcda06e563e1a600c6a0836e665645700c6a091836e564570000c65645211a13600a0968e6e564509700d8c6bc9c6e5645700cdc6a06e452c1a700836e6762564513700c68e836e675613700d8c6a05645211a700b1a0836e625645700c6a0835630211e700c6a0836e452c04700c6a0836e453a2c70000cca0836e6745600c6836e51452c137
  | 7, 0, 2 => 0xc6a09f836e452c70000c6a0837b5638600c6a5a0836e302c700c6b1a06e452c1a700c6a0836e56450d700c6a0836e56300b700cbc6a0836e302c700c6a0836e302c2970000c6a08e6e5641600c6a08356453b21700c6a08a56453321700c6bca0836e6733700c6a083736e302c70000a0836e67330960000d5a083785645600cac6a06e452c1a7
  | 7, 0, 3 => 0xc6a0836e3e302c700bcb9836e56450970000a08381765645600c6bca09c6e452c700c6a06e56451a11700d8c6bc966e56457c6a083816e564539800c6a06e5648451a700c6a0836e452c2b70000c6a6836e563060000a0836e56450660000c6a0836e6740600c6a0836e56452a700c6a0836e302c21700d0c6a06e452c1a700d2c6836e452c137
  | 7, 0, 4 => 0xccc6a083564521700c6a09c83452c26700c6a6836e564521700c6a0776e56451a700c6a06e5651301a700c6836e56302f13700c6a06e56452d1a700c6bca0836e6445700c6a08a83564521700c6837f6e564513700c6bca083814945700cca08356453321700c6baa0836e5645700c6a084836e5645700a0836e67452c0970000a0836e6762336
  | 7, 0, 5 => 0xd6c6a08356452170000c6a0452c211a600c6bca0946e5645700c6a06e56451a0e700c6a0836e452c0c700c6bca0966e452c700c68a836e564513700c6a0836e563014700c6836e56301309700c6bca08374564570000c6a08378563060000a08374564509600c6c4a0836e564570000836e62564513600c6a08356454321700c6a083564f45217
  | 7, 0, 6 => 0xc6836e67563013700d0a06e5651451a70000c66e452c1a13600c6aaa08381564570000c6836e564512600c6bfa0836e564570000a0766e56451a600d5a0836e452c09700c6bca08c6e5645700d8c6a06e452c1a700c6a083816e450e700c6a3a06e452c1a700c6b9a08a6e5645700d2bca0836b5645700b1a08356452109700c6a083675630217
  | 7, 0, 7 => 0xc6a0836e585645700c6a083806e5645700c6a0836e595645700c6a0564530211a700c6a683746e564570000a0836e452c09600c6a08367563321700c6a096836a5645700d8a0836e452c29700d2c6a06e56301a700daada0836e5645700c6836e63564513700c6a7a06e56451a700d0a096836e5145700c6b2a0836e5645700c6a8a06e56451a7
  | 7, 0, 8 => 0xd5c6836e56301370000c6a86e56451a600c6bca09a6e5645700c6a0564533211a700c6b8a083815645700c6a095836e5645700c6a08983563021700c6a0836e615645700c6a4a0836e5645700d5c6a08356302170000d5a0836e644560000c6a0836e4523600c66e5645301a13700ccb9a0836e5645700c6836e67563313700b9a0836e5630097
  | 7, 0, 9 => 0xc6a0836e45432c70000835645211309600c6a1a0836e5645700c6a0835630211f70000a0836e564503600c66e5645331a13700c6a08a836e452c70000c6a08356302160000d0a0836e6345600cda0836e452c09700c6a0836e302c09700c6836e6b452c13700c6a09c8381452c700c6aaa06e56451a700d0c6a06e67451a70000a0836e62452c6
  | 7, 0, 10 => 0xb1a0836e452c09700c6a083816b5630700c6a0836e673321700cbc6a083564521700c6836e64564513700c6a08356452115700c69683816e4513700c6bcb9836e5630700a08e8356452109700c6838156494513700c6816e56451a13700cdbca0836e563e700c6bca08b6e5645700d5d0a083564521700c6a06e452c261a70000c6a06e5645196
  | 7, 0, 11 => 0xc6a083745630600d8c6bc8356452170000c6a08356451d600c6a083564b452170000cea0836e5645600cdc6a083563021700c6a09c6e56450b70000cda0836e644560000c6a0836e6430600c6b8a06e56451a700c6a0835645210170000c6a0838149306008e836e56451309700c6a5a08356452170000c6a0836e674e600c6b5a0836e563b7
  | 7, 0, 12 => 0xc6a08c6e5630600c66e5649451a13700c6b1a083563021700d5c68e6e56451370000c6a08d6e5645600c6a08356452c2170000d2a0836b5630600c6a0836e5d563070000caa0836e452960000a083706e452c600c6836e564b451370000cca08a6e5645600c6a06e45302c1a700cdc6836e56301370000c6a0837d5645600d5c6a08e5645217
  | 7, 0, 13 => 0xd0c6836e56301370000a083452c2109600c6a06e45332c1a700a0836e56450e09700a083817b5645097c6a083816e564543800c6a06e6b56301a700c6a096836e5642700c6a0966e56450b700c6c3a083564521700d0cda083564521700d0c6a083563021700c6a083746e6733700d5c6a0836e302c700d8d5a0835645217c6bca083776e56458
  | 7, 0, 14 => 0xc6a0836e452c1b700c6a2a0836e452c700d0a06e6b56451a700a08e836e452c09700c6a083736e452c700d5d0a0836e452c7d0bca0836e565145800c6a06e48452c1a70000836e452c1309600c6a08356534521700bca083766e5645700c6a0835645211770000c6a0836e302c600c6a0816e452c1a700c6a08359564521700c6bca083452c217
  | 7, 0, 15 => 0x836e5645301309700c6bc836e56450e700c6afa0836e452c70000c6a6836e56456009c836e56451309700c6836e56544513700d5bca06e56453e700c6a5a0836e452c700a0835645302109700c6a08356453c21700cbc6a0836e452c700c6a0836e564527700c6a08356544521700c6a06e452c251a70000c6a08a6e6756600c6836e565345137
  | 7, 1, 0 => 0xc6b1a0836e302c700836e5645331309700c6a08f836e452c700c6b1a96e56451a700c6a08e83563021700c66e5645361a13700c6a06e49452c1a700a0835645332109700d5c6a08e6e452c700c6bba083695645700d8c6bc836e452c70000c6835630211360000c6a08e6e5639600c6836e564d4513700a07b6e56451a09700c6bfa08c6e56457
  | 7, 1, 1 => 0xc6a09d8a6e564570083816e56451309700c6b4a0836e5645700c6c3a0836e452c700c6a06e5645221a700c6a9a05645211a700c6a08356454021700d0c6a0836e302c700c6a083816e563070096836e56451309700c6b1a983816e45700d8d5a0836e452c700c68e836e56301370000d0a0836e5345600c6b1a0837b563670000d8a08c6e56456
  | 7, 1, 2 => 0xa0836e45302c09700a09c836e452c09700c6bcaa836e5645700c68356452c2113700c6a0837e6e5645700c6b1a6836e5645700c6837b6e452c1370000cca06e56451a600c6a08367564521700c6a0836e452c1e70000d0a0836e544560000a06e56301a09600c6a083746e452c700c6a06e5c56451a700c6a0837b452c21700d5a8a0836e56457
  | 7, 1, 3 => 0xc6a6836e673360000c6a0836e6733600a06e56452c1a09700c6a083452c211b700c6b1a0837f6e4570000c6837b56361360000c6836e302c13600c6b1a08378564570000cba0836e562f60000a083766e5630600c6a06e45362c1a700c6bcb9966e5645700c6a0836e655645700c6c0a08356452170000c6a083302c21600c6a0836e56300e7
  | 7, 1, 4 => 0xc6836e453e2c13700c6a093836e56457d0bca0836e6b5645800a0836e452c2509700c6a07b6e56301a700c6836e452c2113700d7c6a0836e452c700c6a9a06e452c1a70000c6a683564521600c6836e452c2913700c6a0716e452c1a700a083816e452c09700c6a0836e5e5645700c6a09c83563021700c6a0836e675639700c6a0835645210b7
  | 7, 1, 5 => 0xc6a683745645600c6bca08a6e564570000c6a083745645600cac6a08356452170000c6a083714526600c66e5651451a13700c696836e56301370000a08a6e564509600c6a0836e302c26700d8c6836e56450b700c6a08381563021700c6bda08a6e5645700c6aaa0836e5630700c6a0836e675b33700c6b9a06e452c1a700c6a083563330217
  | 7, 1, 6 => 0xc6a0836e452c27700c6a5a0837b6e56700c6b4a0836e6445700d4c6a0836e452c700c6b8a0836e5630700c6a0835645331d700c6a08356302d21700c6836756452113700c6a083564e452170000c6a0837b362c600c6a06e56302e1a70000c68378564513600c6b1a0836e6733700c6a08356504521700c6a083452c211e700c683816e5630137
  | 7, 1, 7 => 0xc6a0836e673260000d0a06e51451a600c6bea0836e564570000c6aaa0838145600c6b1a08381494570000c6a6836e452c600c6a06e5630211a700d2c66e56451a13700ccbca0836e56457d0c6bcb9836e5645800c6a09c836e302c700c6836e56302d13700c6a0836e452c0b700c6a0835a563021700bca0836e5630097c6bca0836e5c56458
  | 7, 1, 8 => 0xc6a083816e302c700c6b1a08c6e5645700c6a094836e5630700c6a3a08356452170000c6836e673313600d2b1a0836b5645700bba0836e564509700c6b5a06e56451a700d5c6bca06e5630700c6b1a08374564570000c6a083673321600d0b8a0836e5645700c6836e56493013700c6a0968e564521700c6a083756e5645700c6b1a0836e64457
  | 7, 1, 9 => 0xc68381494513600c6a683816e5645700c686836e564513700d0a094836e564570000c6a083746733600c6a696836e5645700c6836e67452c13700c683816b564513700c6a087836e5630700d0a0836e6b5630700c6bca096816e45700c6a08367452c2170000a0836e564508600c6a09b836e5645700c6836e452c130970000c6a08378452c6
  | 7, 1, 10 => 0xd2836b564513600c6836e5d564513700c6a08356453821700d5c6a083452c21700d8a06e56453e1a700dac6a08356452170000c68374564513600c6a08a836e6756700c6c1a0836e5645700c5a0836e564509700c6b6a0836e5645700cdc68356452113700c6a0988c6e564570000c6836e644513600c6a08356452102700c6a0968e6e56397
  | 7, 1, 11 => 0xc6a08356453021700c6a0836e575645700c6a0835630211c700c6a09c836e6733700c6a088836e5630700c6a08381494538700d1c6a08356452170000cca0836e5630600c6a083452c211f700c6a9a07b6e561a700c6a0837b6e564070000c6a083452c21600c66e6b56451a13700d0c68356452113700cdb1a0836e563e70000a0836f5645096
  | 7, 1, 12 => 0xa0836e563e0260000c6a08374452c600cac6a083452c21700c6bca0836a5645700c6a0836e36302c70000cda0836e564060000d8d5bc6e5645600c6bba0836e563070000c6a0837c5645600d0bca0836e5145700cdc6a083452c21700cca0836e564521700c6a0836e452c28700b1a083816e4509700c6a0835645210070000c7a0836e56456
  | 7, 1, 13 => 0xc6a08356484521700bca0966e56450970000c6a0966e5045600b1a083766e5645700c6aba0836e5645700c6a0836e45382c700d0c6a083452c2170000c6a08c6e452c600c6b1a083452c21700dac6a0836e452c70000d2a0836b452c600c6a0836e5d452c700c6a083816e6733700c6a08356453321700a0836e56302c09700c6aea0836e56457
  | 7, 1, 14 => 0xc6b1a8836e5645700c6afa06e56451a700c6a0836e452c00700c6a085836e452c700c6a0835a564521700c6a0836e56450f700c6a0835649451b700c6a08356452d21700c6c5a0836e5630700c6a08356464521700006e56451a1309600c6a08356452521700c6a5a0836e6756700cca083746e5645700c6836e564c4513700a0836e56450c097
  | 7, 1, 15 => 0xc6a3836e56450e70000d0a0836e5130600c6aca0836e5645700c6b1a083816e3070000c6a0836e4825600c6a083816e452c700a08a836e564509700c6a090836e5645700a09c8381564509700bca0836e625645700c6a08e83452c2170000cda0836e3e2c600c6b9a6836e5645700c6b1a7836e564570000a0836e514501600c6a3a083452c217
  | 7, 2, 0 => 0xc6a0836e5a2d60000c6a68a6e5645600c6bca0966e5630700a0836e452c0904700c6968356452113700c6a083816e5345700c6a0836e56451070000c6a0836e5644600d0c6a083674521700c6a09a966e56457c6bca0836e635645800c67b6e56451a13700d5d2a0836e452c700c6c2a0836e5645700c6c3a083816e45700c6a083564532217
  | 7, 2, 1 => 0xc66e5645211a13700c6a0836e5645247c6bca0836e64564580000cca0836e5645600c6c3a0836a5645700c6a08345302c2170000a0836e563009600c6a09c83452c21700d2c6a0836e302c700bca0835645210970000c6b1836e4e45600c6a7a0836e452c70000c6a08373562e600c6a8a0836e452c70000c66e56301a1360000a083766e452c6
  | 7, 2, 2 => 0xc6a083452c252170000c8a0836e564560000c6a0836e6056600c6a08348452c21700c66e56452c1a13700c6a08381452c21700c6a09c8381563070000a0836e62563060000c6a0916e5645600dbc6a083564521700c6a08345332c21700c6b1a083816b4570000cfa0836e5645600c66e56453e1a13700c6a0837f6e5630700a0836e56451b097
  | 7, 2, 3 => 0xc6a0836e56450a700c6a0836e6b302c700c6a08356452221700c6a0836e5f56457c6bca0836e5655458c6bca0836e56534580000c6a66e56451a600bca0836e452c09700a083746e564509700c6b8a0836e452c700d5a0836e645645700c6a08356453d21700c3a0836e564509700ccb1a0836e5645700c6b1a0836e5d45700b1a0836e5630097
  | 7, 2, 4 => 0xc6a0836e453d2c70000c6a08356361c600c66e6756451a1370000c6a0836c452c600c6a0836e56301b700a09796836e5645700c6a08367453321700c6a0836e645630700c66e56451a130970000cca083564521600c6bca08356302170000a08356302109600dbc6a0836e452c70000c6a0836f5645600c6a0835645343370000cca0836e67336
  | 7, 2, 5 => 0xc6bca0836e302c70000a0836e302c09600c6a083746e5630700c6a0837b56302170000c6a0836e4745600c6c3a0836e5630700c6a08371452c2170000d4a0836b5645600a08356452c2109700c6bca0836d564570000c8a083564521600c6a0837a6e564570000cca08374564560000c6a08379564560000c6a0836e3322600a0837b6e452c097
  | 7, 2, 6 => 0xd2c6a0837b452c700a083816e563009700cbc6a083563021700c6a08373563021700cdc66e56451a1370000c6a08349451b600c6a0836e675638700c6a0836b56451b700a0836e56450b0970000c9a0836e5645600c6bda0836e564570000c6a083814b45600c6a3a083816e45700c6a08e6e56451570000cca0836e452c600c6bca0837b56367
  | 7, 2, 7 => 0xa0836756452109700d0c66e56451a13700cca083816e5645700c6bca0837856457
  | 8, 0, 0 => 0xc6a06e5645331a7c6a09c836e56453a800c6a0836e6b452c700c6a089836e5630700c6bcb1836e5645700d5c6a0836e56307c6a0836e67564521800c6a06e5645301a700c6a0836e675633700c6a0837b6e5645700c6a0836e5645057d0c6bca0836e5645800d0a0836e564509700c6a0836e6356457d5c6a0837b6e5645800b1a0836e5645097
  | 8, 0, 1 => 0xc6a0836e5645157c6b1a0837b6e5645800c6a0836e56451b700a08e836e564509700c6a083736e5645700d5d0a0836e5645700c6a0836e645645700c6a09683816e4570000836e56451309600c6a0838156494570000c6a0836e5630600c6a0816e56451a7c6a096836e564539800d8a0836e564509700c6bca08356452170000a083564521096
  | 8, 0, 2 => 0xc6b1a0836e56307c6a09f96836e5645800c6a08f836e5645700c6a0836e56452c700c6a06e5649451a700d5c6a08e6e56457c6a096836e6b5645800d8c6bc836e5645700c6a0836e564b457d5c6a0836e56452c800cdc6a0836e5630700c6afa0836e5645700c6a0836e5645017d0c6a0837b6e5645800c6a5a0836e5645700cbc6a0836e56457
  | 8, 0, 3 => 0xc6b1a0836e56453e8d2c6a9a0836e56458c6b1a0836e564521800c6a0836e565345700c6a0836e564517700c6837b6e5645137d5c6a0836e565445800c6bca0836e452c700c6a0836e56451e70000a0836e452c09600c6a083746e5645700c6a0837b564521700c6c3a0836e5645700d0cda0836e5645700d0c6a0836e5630700d8d5a0836e56457
  | 8, 0, 4 => 0xc6bca0836e564533800a0836e564533097c6c3b1a0836e56458c6a096836e68564580000c6836e563013600c6a9a0836e6756700c6a06e5645361a700c6b9a0838156457c6b1a0836e56452c80000c6a0835630216c6bca0836e564530800c6a0836e564d45700a0836e56453009700c6a0836e56453c700a09c836e564509700c6a0836e5654457
  | 8, 0, 5 => 0xc6a6a0836e5645700c6836e56452c13700c6a08356452c21700c6b9a06e56451a7c6a08e836e564521800c6836e56453e13700c6a0836e675645700c6a0837b6e452c700c6836e56452113700d7c6a0836e5645700c6a9a06e56451a700c6a0836e5645407c6bca083816e56458d5c6a0836e675645800a083816e564509700c6a08e836e56307
  | 8, 0, 6 => 0xc6a6836e56456d0c6a0836e675645800c6a0836e452c21700c6a09c836e56307c6b1a0836e675645800c6a0836e56450b7c6b1ada0836e5645800c6a0836e452c29700d4c6a0836e56457c6a0836e675b5645800c6c0a0836e564570000c6a0837b56366c6b1a0836e56450980000c6a0836e302c6c6bca0836e564945800c6a0835645211e7
  | 8, 0, 7 => 0xc6a096836e564515800c6a0836e565045700cac6a0836e5645700c6a0836e564514700c6836e564513097d5c6b1a0836e56458c6bca0836e56453680000c6a083785645600c6a083816e5630700cdc6a0836e5645700c6a06e5651451a7c6a0836e56453021800c6a0836e5633307c6a0836e56452c26800c6a0836e453e2c700c6a0836e56451f7
  | 8, 0, 8 => 0xc6a0968e6e56457cdc6b1a0836e5645800d5c6a0835645217c6a083816e56452c800d9c6a0836e5645700c6a0836e564930700c6a0836e5a5630700d2c6a06e56451a700c6a0836e56302d700d0c6a0836e5645700c6836e67564513700c6a0836e564e457c6a0836e564533218c6a09c836e56452c800a0837b766e5645700c6a083675645217
  | 8, 0, 9 => 0xcdc6a08356452170000c6a0836e644560000c6a083814945600c6a0836e67452c700c6a083816b5645700c6bcb9836e56457d0c6b1a0836e5645800c6a3a0836e5645700c6a0835645211f70000c6a083564521600c6a0836e452c097dbc6bca0836e5645800d5c6836e5645137c6a09c836e564d4580000c6a0836e67336c6a083746e5645338
  | 8, 0, 10 => 0xd0c6836e564513700c6a06e6b56451a700c6a0836e564538700d0c6a083564521700d5c6a0836e452c7c6bca0836e56514580000c6a08c6e5645600c6b1a083564521700dac6a0836e564570000d2a0836b5645600c6a0836e5d5645700cdc6836e5645137c6a09c836e67564580000c6a083745645600c6a0836e564502700c6a0836e5636307
  | 8, 0, 11 => 0xd5c6a083816e5645800cac6a0836e452c70000cda0836e563e60000c68356452113600cdc6a0836e452c7dac6b1a0836e5645800c6a09e836e5645700c6a0836e564500700c6a0836e5645307d2c6bca0836e56458c6a0836e5645362c800d1c6a0836e56457d0c6a08e836e56458c6a083816e67564580000c6a0836e452c6c6b1a08e836e56458
  | 8, 0, 12 => 0xc6a0836e56452d7d0c6a09c836e56458c6b1a0836e5645308c6b1a09c836e56458c6c5bca0836e5645800c6a0836e564525700d5d2a0836e5645700c6a0836e564845700d0c6a0836e452c700c6a083816e56457cdc6a09c836e5645800c6b1a0836e452c700c6a6836e5645337d8c6a08e836e5645800c6a0836e564533700c6a08e835645217
  | 8, 0, 13 => 0xc6a8a0836e5645700d0a0836e56514570000c6836e452c136c6b1a083816e56458c6a0836e6756453680000a083766e56456c6b1a096836e5645800c6a3a0836e452c7c6b1a0836e56453380000c6a083452c21600c6a083817b5645700c6a0836e5a5645700a0836e564509047cdc6a083816e5645800c6a083776e5645700c6a0836e5651307
  | 8, 0, 14 => 0xc696836e564513700c6a0836e452c26700c6a08381564521700c6a0836e5645417c6b1a0836e564945800d0c6a0836e6745700c6a08356453321700c6a0836e5645327d8c6a09c836e5645800c6a08356453021700c6a09c83564521700d2c6a0836e5630700c6a08e836e452c700c6a7a0836e56457d0c6a083816e56458c6bca0836e6b56458
  | 8, 0, 15 => 0xc6a0836e45332c7c6a09c836e564530800c6a0836e56451c700c6a0836e6b5630700c6a083826e56457c6a083816e5645388c6b1a0836e564536800c6a0837b564536700c6a0836e45302c700c6a09c836e452c700bca0836e564509700c6b8a0836e5645700c6a08374564533700c6a083716e56457c6a08e83816e56458d2c6a0836e56452c8
  | 8, 1, 0 => 0xc6a08e837b6e56700c6a099836e56457c6a083816e564533800c6a0836e49452c7c6bca0837b6e56458d2c6a0836e675645800a0837b6e564509700c6a0836e56453d7c6a083816e564530800a0836e56450905700c6a0836e452c257c6a09c836e564533800d0a0836e6b5645700c6a0836e48452c700c6a083816e452c700dbc6a0836e56457
  | 8, 1, 1 => 0xc6a083716e452c700d2c6a0837b56457c6bca0836e56452c800a0836e56452c09700c6a0836e45362c7c6b1a0836e5651458c6bca0836e56453e800c6bba0836e56457c6bca0836e5645218c6b9a08e836e5645800c6a0836e67453370000cca0836e5645600c6bca0836e563070000a0836e563009600c6a0836e5c5645700c6a0836e5645227
  | 8, 1, 2 => 0xcda0836e56453e700c6a0836e563e3070000d0a0836e5145600c6a0836e5630217c6bca0836e564509800cbc6a0836e5630700c6a083736e5630700c6a0836e56302e700c6a0836e564504700d5a0836e56453e700c6c5a0836e5645700c6a0836e564539700d3c6a0836e56457d2c6b1a0836e5645800c6a0837b6e56307c6c3bca0836e56458
  | 8, 1, 3 => 0xc6a0836e563009700cca0836e56453370000a0836e625645600c6a0836e56302f700c6a0837f6e56457c6b5b1a0836e564580000a0836e564509600d2c6a0836e452c70000c66e56451a136c6a0836e56452c218c6c0bca0836e5645800a0836e67625645700c6a0836e51452c700c6a0836e56302c7c6bca0836e675645800a0836e675645097
  | 8, 1, 4 => 0xc6a0836e675630700ccc6a0836e56457cdc6bca0836e5645800cda0836e5645097
  | 9, 0, 0 => 0xc6a0836e452c6c6a08e836e5645700c6836e564513600c6a0835645216d0c6a0836e56457c6b1a0836e56457cdc6a0836e5645700c6a0836e56456d5c6a0836e56457c6a0836e6756457c6a0836e5645097c6a0836e56452c7c6a0836e56453e7c6a0836e564521700c6a0836e56306c6a0837b6e56457
  | 9, 0, 1 => 0xc6bca0836e5645700a0836e5645096c6a0836e6b56457d2c6a0836e56457c6a0836e5651457c6a0836e5645367c6a0836e5649457c6a083816e56457c6a0836e5645337c6a0836e5645307c6a09c836e56457
  | 10, 0, 0 => 0xc6a0836e56456
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
  | 0, 0 => 0x3fffffe300000000000000000000000000000000000000000000000000000000079e7f9f000000000000000000000000000000000000000000000000000000000000781c00000000000000000000000000000000000000000000000000000000079e0783000000000000000000000000000000000000000000000000000000003fffffff000000000000000000000000000000000000000000000000000000003861f87c000000000000000000000000000000000000000000000000000000003fff87e30000000000000000000000000000000000000000000000000000000007e07fff
  | 0, 1 => 0x3f8401fffff000000000000000000000000000000000000000000000000000003f8401f87e300000000000000000000000000000000000000000000000000000387c01fffff00000000000000000000000000000000000000000000000000000387c01f801f0000000000000000000000000000000000000000000000000000007fc0007fff00000000000000000000000000000000000000000000000000000078400007e3000000000000000000000000000000000000000000000000000000003fffffff00000000000000000000000000000000000000000000000000000000079e7fe3
  | 0, 2 => 0x1c7fc060787c00000000000000000000000000000000000000000000000000001c7fc7e07fff00000000000000000000000000000000000000000000000000001c7847e007e300000000000000000000000000000000000000000000000000001c07c7e0001f000000000000000000000000000000000000000000000000000003ffc01fffff000000000000000000000000000000000000000000000000000003ffc01fffff000000000000000000000000000000000000000000000000000003ffc001f87c000000000000000000000000000000000000000000000000000003ffc01f87ff
  | 0, 3 => 0x78000001c00000000000000000000000000000000000000000000000000000000079e00030000000000000000000000000000000000000000000000000000ff87ffff801f0000000000000000000000000000000000000000000000000000ff87f861801c0000000000000000000000000000000000000000000000000000ff807fff800300000000000000000000000000000000000000000000000000001c7fc7e07fff00000000000000000000000000000000000000000000000000001c7fc7e07fff00000000000000000000000000000000000000000000000000001c7fc7e07fff
  | 0, 4 => 0xfc783fe007e000000000000000000000000000000000000000000000000000000078000007e000000000000000000000000000000000000000000000000000000000079e07830000000000000000000000000000000000000000000000000000fff87fff80630000000000000000000000000000000000000000000000000000fff87fff87e30000000000000000000000000000000000000000000000000000fff8786180600000000000000000000000000000000000000000000000000000ff87ffff801f0000000000000000000000000000000000000000000000000000ff87ffff8003
  | 0, 5 => 0xffffc00000000000000000000000000000000000000000000000000000000000007800007860000000000000000000000000000000000000000000000000000000078000781c0000000000000000000000000000000000000000000000000000fff87fff87e30000000000000000000000000000000000000000000000000000fff87fe000000000000000000000000000000000000000000000000000000000fff8781f80000000000000000000000000000000000000000000000000000000fff8400000000000000000000000000000000000000000000000000000000000ff803fff8000
  | 0, 6 => 0xff87f861879c00000000000000000000000000000000000000000000000000000000000007800000000000000000000000000000000000000000000000000000fff8786180600000000000000000000000000000000000000000000000000000ff87ffff801f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffff00000000000000000000000000000000000000000000000000000007879e7f9f0000000000000000000000000000000000000000000000000000fffff861f87c
  | 0, 7 => 0x3861f87c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000079e00000000000000000000000000000000000000000000000000000000000007800780000000000000000000000000000000000000000000000000000000000780000000000000000000000000000000000000000000000000000000000000001e078000000000000000000000000000000000000000000000000000000000001e00000000000000000000000000000000000000000000000000000000000000000780
  | 0, 8 => 0xfff87fff87e300000000000000000000000000000000000000000000000000000007879e079f00000000000000000000000000000000000000000000000000000000079e07830000000000000000000000000000000000000000000000000000000007800000000000000000000000000000000000000000000000000000000000000780000000000000000000000000000000000000000000000000000000000000001e000000000000000000000000000000000000000000000000000000000000001e00000000000000000000000000000000000000000000000000000000000000000000
  | 0, 9 => 0x780000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000078000000000000000000000000000000000000000000000000000000ff807ffff80300000000000000000000000000000000000000000000000000000000000078000000000000000000000000000000000000000000000000000000fff87fff87e3
  | 0, 10 => 0x787e07fff000000000000000000000000000000000000000000000000000000078000781c00000000000000000000000000000000000000000000000000000007800000000000000000000000000000000000000000000000000000000000000780000000000000000000000000000000000000000000000000000000000000078000000000000000000000000000000000000000000000000000000000000007bfff87e300000000000000000000000000000000000000000000000000000007800000000000000000000000000000000000000000000000000000000000000000000000
  | 0, 11 => 0x7801e7f9c00000000000000000000000000000000000000000000000000000000001e7f800000000000000000000000000000000000000000000000000000000780007f9c00000000000000000000000000000000000000000000000000000000079e7f830000000000000000000000000000000000000000000000000000000000007f800000000000000000000000000000000000000000000000000000fffff861f87c00000000000000000000000000000000000000000000000000000007879e781f00000000000000000000000000000000000000000000000000000387c01ff81f
  | 0, 12 => 0x7879e7f9f000000000000000000000000000000000000000000000000000000078780781c00000000000000000000000000000000000000000000000000000007801e0000000000000000000000000000000000000000000000000000000000078000781c00000000000000000000000000000000000000000000000000000007879e0783000000000000000000000000000000000000000000000000000000078000000000000000000000000000000000000000000000000000000000000007879e781c00000000000000000000000000000000000000000000000000000000079e0783
  | 0, 13 => 0x7800007ffc0000000000000000000000000000000000000000000000000000007800007fe0000000000000000000000000000000000000000000000000000000780000000000000000000000000000000000000000000000000000000000000078000007e00000000000000000000000000000000000000000000000000000007800000000000000000000000000000000000000000000000000000000000000000000780000000000000000000000000000000000000000000000000000000000000078000000000000000000000000000000000000000000000000000000000000007800
  | 0, 14 => 0x78079e0783000000000000000000000000000000000000000000000000000000780000000000000000000000000000000000000000000000000000000000000000001e78000000000000000000000000000000000000000000000000000000007800007fe00000000000000000000000000000000000000000000000000000fffff861fffc0000000000000000000000000000000000000000000000000000007f80007ffc0000000000000000000000000000000000000000000000000000fff87fffffe30000000000000000000000000000000000000000000000000000fff840000000
  | 0, 15 => 0x7f8000781c0000000000000000000000000000000000000000000000000000007f800007800000000000000000000000000000000000000000000000000000007800007fe00000000000000000000000000000000000000000000000000000007800007fe000000000000000000000000000000000000000000000000000000078079e7fe300000000000000000000000000000000000000000000000000000078078000000000000000000000000000000000000000000000000000000000007800007fe00000000000000000000000000000000000000000000000000000007800007fe0
  | 1, 0 => 0xe387b81ff81c0000000000000000000000000000000000000000000000000000fff87fff87e30000000000000000000000000000000000000000000000000000e3f8381f87e00000000000000000000000000000000000000000000000000000fff8787f80600000000000000000000000000000000000000000000000000000e380381f80000000000000000000000000000000000000000000000000000000007f879e7fff0000000000000000000000000000000000000000000000000000007f80007ffc0000000000000000000000000000000000000000000000000000007f80000000
  | 1, 1 => 0xe380381ff8000000000000000000000000000000000000000000000000000000e3803f9f87830000000000000000000000000000000000000000000000000000e380381f80000000000000000000000000000000000000000000000000000000e380381f80000000000000000000000000000000000000000000000000000000e380381f87800000000000000000000000000000000000000000000000000000e380381f80000000000000000000000000000000000000000000000000000000fffff87ff87c0000000000000000000000000000000000000000000000000000e3f8381ff860
  | 1, 2 => 0xe387800000000000000000000000000000000000000000000000000000000000e387b81ff81c0000000000000000000000000000000000000000000000000000e387b81f80000000000000000000000000000000000000000000000000000000e387b81f80000000000000000000000000000000000000000000000000000000e387801e00000000000000000000000000000000000000000000000000000000e387800000000000000000000000000000000000000000000000000000000000e380381f80000000000000000000000000000000000000000000000000000000e00038007800
  | 1, 3 => 0xe3ffb81ffffc0000000000000000000000000000000000000000000000000000e3f83f9fffe30000000000000000000000000000000000000000000000000000e3f8381fffe00000000000000000000000000000000000000000000000000000e3f8381fffe00000000000000000000000000000000000000000000000000000e3f8380000000000000000000000000000000000000000000000000000000000e3f8381f80000000000000000000000000000000000000000000000000000000e387bf9fff9f0000000000000000000000000000000000000000000000000000e387b81ff81c
  | 1, 4 => 0xfc003fe007800000000000000000000000000000000000000000000000000000fc003fe000000000000000000000000000000000000000000000000000000000ffffffe1f87c0000000000000000000000000000000000000000000000000000fc07bfe0781c0000000000000000000000000000000000000000000000000000fff87fff87e30000000000000000000000000000000000000000000000000000fff87fe000000000000000000000000000000000000000000000000000000000fc787fe007e30000000000000000000000000000000000000000000000000000fc003fe00000
  | 1, 5 => 0xfc07bfe000000000000000000000000000000000000000000000000000000000fc07b80000000000000000000000000000000000000000000000000000000000fc07800000000000000000000000000000000000000000000000000000000000fc003fe078000000000000000000000000000000000000000000000000000000fc003fe078000000000000000000000000000000000000000000000000000000fc003fe078000000000000000000000000000000000000000000000000000000fc003ffe07830000000000000000000000000000000000000000000000000000fc003fe00000
  | 1, 6 => 0xfc78380000000000000000000000000000000000000000000000000000000000fc78078007800000000000000000000000000000000000000000000000000000fc07bffe7f9f0000000000000000000000000000000000000000000000000000fc07bfe0781c0000000000000000000000000000000000000000000000000000fc07800000000000000000000000000000000000000000000000000000000000fc07bfe07f9c0000000000000000000000000000000000000000000000000000fc07bfe0781c0000000000000000000000000000000000000000000000000000fc07bfe00000
  | 1, 7 => 0xff803fff80000000000000000000000000000000000000000000000000000000ff803fff87800000000000000000000000000000000000000000000000000000ff803fff80000000000000000000000000000000000000000000000000000000ff803fff80000000000000000000000000000000000000000000000000000000fc7fbfe07ffc0000000000000000000000000000000000000000000000000000fc7fbfe0781c0000000000000000000000000000000000000000000000000000fc783fe07fe00000000000000000000000000000000000000000000000000000fc783fe00000
  | 1, 8 => 0xfffff861801c0000000000000000000000000000000000000000000000000000ffffc00000000000000000000000000000000000000000000000000000000000fff83fffffe00000000000000000000000000000000000000000000000000000fff83fff80000000000000000000000000000000000000000000000000000000ff87bffff81c0000000000000000000000000000000000000000000000000000ff87bfff80000000000000000000000000000000000000000000000000000000ff803ffff8000000000000000000000000000000000000000000000000000000ff803fff8783
  | 1, 9 => 0xffffc00000000000000000000000000000000000000000000000000000000000ffffc00000000000000000000000000000000000000000000000000000000000ffffc79e07830000000000000000000000000000000000000000000000000000ffffc00000000000000000000000000000000000000000000000000000000000fffff861f87c0000000000000000000000000000000000000000000000000000ffffffff87e30000000000000000000000000000000000000000000000000000fffff86180600000000000000000000000000000000000000000000000000000ffffc000001c
  | 1, 10 => 0xfffff81fffe00000000000000000000000000000000000000000000000000000ffffff9f87830000000000000000000000000000000000000000000000000000fffff81f80000000000000000000000000000000000000000000000000000000ffffc0007ffc0000000000000000000000000000000000000000000000000000ffffc79e7fe30000000000000000000000000000000000000000000000000000ffffc0007fe00000000000000000000000000000000000000000000000000000ffffc79e7f9f0000000000000000000000000000000000000000000000000000ffffc000781c
  | 1, 11 => 0xffffffff80000000000000000000000000000000000000000000000000000000ffffffe0781c0000000000000000000000000000000000000000000000000000fffffffe07830000000000000000000000000000000000000000000000000000ffffffe00000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x2b4d3be0000000000000000000000000000000000000000000000000000000001baebb9d0000000000000000000000000000000000000000000000000000000010a2b89d000000000000000000000000000000000000000000000000000000000b8e0b85000000000000000000000000000000000000000000000000000000003b6db378000000000000000000000000000000000000000000000000000000003061b078000000000000000000000000000000000000000000000000000000002b4d03600000000000000000000000000000000000000000000000000000000001e02ad5
  | 0, 1 => 0x2a840179daf000000000000000000000000000000000000000000000000000002a84015052200000000000000000000000000000000000000000000000000000182c01799af00000000000000000000000000000000000000000000000000000182c012800f00000000000000000000000000000000000000000000000000000019c0004c870000000000000000000000000000000000000000000000000000000840000402000000000000000000000000000000000000000000000000000000003befbbfd000000000000000000000000000000000000000000000000000000002bcf3be5
  | 0, 2 => 0x1855006060500000000000000000000000000000000000000000000000000000145945404642000000000000000000000000000000000000000000000000000014484540064200000000000000000000000000000000000000000000000000000c04c4a00017000000000000000000000000000000000000000000000000000003bbc017ddaf000000000000000000000000000000000000000000000000000003330007d9ad000000000000000000000000000000000000000000000000000003330001d028000000000000000000000000000000000000000000000000000003aac017852f
  | 0, 3 => 0x490690a2801d00000000000000000000000000000000000000000000000000002480ce9a000700000000000000000000000000000000000000000000000000006d865e38801a0000000000000000000000000000000000000000000000000000490610208018000000000000000000000000000000000000000000000000000024804e18000200000000000000000000000000000000000000000000000000001c5dc5e06ed700000000000000000000000000000000000000000000000000001c5d456066520000000000000000000000000000000000000000000000000000185501e06ad5
  | 0, 4 => 0xb6682f4d07600000000000000000000000000000000000000000000000000000926821450760000000000000000000000000000000000000000000000000000024884f1c07020000000000000000000000000000000000000000000000000000b6e06e590062000000000000000000000000000000000000000000000000000092602b4d0360000000000000000000000000000000000000000000000000000092602041006000000000000000000000000000000000000000000000000000006d86deba801f00000000000000000000000000000000000000000000000000006d86ce180002
  | 0, 5 => 0xdb77000040000000000000000000000000000000000000000000000000000000927120417060000000000000000000000000000000000000000000000000000049171020f0180000000000000000000000000000000000000000000000000000b6e86f5d07620000000000000000000000000000000000000000000000000000b6e86f5806420000000000000000000000000000000000000000000000000000b6e86e1d05220000000000000000000000000000000000000000000000000000b6e8441004020000000000000000000000000000000000000000000000000000b6e02f5d0360
  | 0, 6 => 0x490e11248f980000000000000000000000000000000000000000000000000000000801040f8000000000000000000000000000000000000000000000000000009260a0c308e500000000000000000000000000000000000000000000000000006d86deba889f00000000000000000000000000000000000000000000000000000000808208850000000000000000000000000000000000000000000000000000ffff7f7df77a00000000000000000000000000000000000000000000000000006d9f5f3cf71a0000000000000000000000000000000000000000000000000000db773061f078
  | 0, 7 => 0x2488f471b47a00000000000000000000000000000000000000000000000000002488c4100402000000000000000000000000000000000000000000000000000024800f9e0300000000000000000000000000000000000000000000000000000024080f8c0f80000000000000000000000000000000000000000000000000000024008f8a0a85000000000000000000000000000000000000000000000000000020880b1e0f80000000000000000000000000000000000000000000000000000020808a9e09850000000000000000000000000000000000000000000000000000000881860f85
  | 0, 8 => 0xb6e8ef5d076200000000000000000000000000000000000000000000000000006d8edfbe8f9f00000000000000000000000000000000000000000000000000002488cf9e0f8700000000000000000000000000000000000000000000000000002488cf9a0e8700000000000000000000000000000000000000000000000000002488cf98060200000000000000000000000000000000000000000000000000002488ce9e0d8700000000000000000000000000000000000000000000000000002488ce1e050200000000000000000000000000000000000000000000000000002488c4920c87
  | 0, 9 => 0x481510a078900000000000000000000000000000000000000000000000000000480490a22895000000000000000000000000000000000000000000000000000041131002f888000000000000000000000000000000000000000000000000000041029082988d0000000000000000000000000000000000000000000000000000001180827885000000000000000000000000000000000000000000000000000024914e18788200000000000000000000000000000000000000000000000000000011000078800000000000000000000000000000000000000000000000000000b6e8efdf0fe7
  | 0, 10 => 0x491791e2fadd0000000000000000000000000000000000000000000000000000491790a2f89d0000000000000000000000000000000000000000000000000000491790a2f018000000000000000000000000000000000000000000000000000049179002d008000000000000000000000000000000000000000000000000000049178082488500000000000000000000000000000000000000000000000000004917ab4d436000000000000000000000000000000000000000000000000000004917800040000000000000000000000000000000000000000000000000000000490610a2b018
  | 0, 11 => 0x699f9bbeff9d0000000000000000000000000000000000000000000000000000619b1b1eff880000000000000000000000000000000000000000000000000000491f91a6ff9d00000000000000000000000000000000000000000000000000002499cf9e7f870000000000000000000000000000000000000000000000000000001901047f800000000000000000000000000000000000000000000000000000db77b0e3f8fd00000000000000000000000000000000000000000000000000006d97debaf89f00000000000000000000000000000000000000000000000000004997d0b2f89f
  | 0, 12 => 0x6d9fdfbeff9f00000000000000000000000000000000000000000000000000006d9fdfbafe9f00000000000000000000000000000000000000000000000000006d9fde1ed50a00000000000000000000000000000000000000000000000000006d9fd4b2fc9f00000000000000000000000000000000000000000000000000006d9fcf9e4f8700000000000000000000000000000000000000000000000000006d9fc410440200000000000000000000000000000000000000000000000000006d979fbefb9d00000000000000000000000000000000000000000000000000006d8edfbebf9f
  | 0, 13 => 0x927931e7fffd0000000000000000000000000000000000000000000000000000927921457fe00000000000000000000000000000000000000000000000000000927921457760000000000000000000000000000000000000000000000000000092792145476000000000000000000000000000000000000000000000000000009279000044000000000000000000000000000000000000000000000000000000927121457be00000000000000000000000000000000000000000000000000000905121407ac000000000000000000000000000000000000000000000000000008231200579a0
  | 0, 14 => 0xb6f9cf9e4f870000000000000000000000000000000000000000000000000000b6f9c41044020000000000000000000000000000000000000000000000000000a2b1aa9f79a500000000000000000000000000000000000000000000000000009279a1c77fe50000000000000000000000000000000000000000000000000000db7f3165fff80000000000000000000000000000000000000000000000000000db7f3165fff80000000000000000000000000000000000000000000000000000b6f96f5d7fe20000000000000000000000000000000000000000000000000000b6f944104402
  | 0, 15 => 0xdb7f90a2fc9d0000000000000000000000000000000000000000000000000000db7f81864f850000000000000000000000000000000000000000000000000000db7f31e7fff80000000000000000000000000000000000000000000000000000d37bb1c7ffed0000000000000000000000000000000000000000000000000000b6f9efdf7fe70000000000000000000000000000000000000000000000000000b6f9efd866420000000000000000000000000000000000000000000000000000b6f9e5d77fe70000000000000000000000000000000000000000000000000000b6f9e5557fe2
  | 1, 0 => 0xebb73a3ff1380000000000000000000000000000000000000000000000000000f7ea7f5f976a0000000000000000000000000000000000000000000000000000f3ea3b5f97680000000000000000000000000000000000000000000000000000f3e23a5f91680000000000000000000000000000000000000000000000000000e3a23a1f91280000000000000000000000000000000000000000000000000000ffffffffffff0000000000000000000000000000000000000000000000000000db7fb1e7fffd0000000000000000000000000000000000000000000000000000db7fb1e06650
  | 1, 1 => 0xe3b33a1ff9a80000000000000000000000000000000000000000000000000000e7aaff9f9faf0000000000000000000000000000000000000000000000000000e7aafe9f9daf0000000000000000000000000000000000000000000000000000e7aafe1f952a0000000000000000000000000000000000000000000000000000e3aa3b1f9fa80000000000000000000000000000000000000000000000000000e3a2ba9f99ad0000000000000000000000000000000000000000000000000000fbf73a7ff1780000000000000000000000000000000000000000000000000000f3f33a5ff168
  | 1, 2 => 0xefbfc41044020000000000000000000000000000000000000000000000000000ebb7babff9bd0000000000000000000000000000000000000000000000000000ebb7babff1380000000000000000000000000000000000000000000000000000ebb7ba1fd1280000000000000000000000000000000000000000000000000000ebb78a9e49850000000000000000000000000000000000000000000000000000ebb7801040000000000000000000000000000000000000000000000000000000eba6babfb9bd0000000000000000000000000000000000000000000000000000ea353aad79b0
  | 1, 3 => 0xfbffbbfffffd0000000000000000000000000000000000000000000000000000f7fbffdfffef0000000000000000000000000000000000000000000000000000f3fbbbdfffed0000000000000000000000000000000000000000000000000000f3fb3b5fffe80000000000000000000000000000000000000000000000000000f3fb3b5866400000000000000000000000000000000000000000000000000000f3fb3a1fd5280000000000000000000000000000000000000000000000000000efbfffbfffbf0000000000000000000000000000000000000000000000000000efbffebffdbf
  | 1, 4 => 0xfc4c3fec2fd00000000000000000000000000000000000000000000000000000fc44bfea2ad50000000000000000000000000000000000000000000000000000ff773fe9f2780000000000000000000000000000000000000000000000000000fd573fe8f2580000000000000000000000000000000000000000000000000000feec7ffd27720000000000000000000000000000000000000000000000000000feec7ff826520000000000000000000000000000000000000000000000000000fc4c7fe826520000000000000000000000000000000000000000000000000000fc443fe82250
  | 1, 5 => 0xfd57bfe862500000000000000000000000000000000000000000000000000000fd57be0ad0080000000000000000000000000000000000000000000000000000fd57840040000000000000000000000000000000000000000000000000000000fd573feafad80000000000000000000000000000000000000000000000000000fc55bfea7ad50000000000000000000000000000000000000000000000000000fc553fe87ad00000000000000000000000000000000000000000000000000000fcccfffe2fd70000000000000000000000000000000000000000000000000000fcccfff82652
  | 1, 6 => 0xfe7d3e0d55200000000000000000000000000000000000000000000000000000fe7d0f8c4f800000000000000000000000000000000000000000000000000000fddffffeffdf0000000000000000000000000000000000000000000000000000fddffffafedf0000000000000000000000000000000000000000000000000000fddfc41044020000000000000000000000000000000000000000000000000000fd5fbfeeffdd0000000000000000000000000000000000000000000000000000fd57bfeafadd0000000000000000000000000000000000000000000000000000fd57bfea6ad5
  | 1, 7 => 0xffeeffffb77a0000000000000000000000000000000000000000000000000000ffee3fffbff80000000000000000000000000000000000000000000000000000ffe6bfffbbfd0000000000000000000000000000000000000000000000000000ffe63fffb3780000000000000000000000000000000000000000000000000000ff7fbfeffffd0000000000000000000000000000000000000000000000000000ff7fbfeafedd0000000000000000000000000000000000000000000000000000fe7d3fed7ff00000000000000000000000000000000000000000000000000000fe7d3fe86650
  | 1, 8 => 0xffffd430c41a0000000000000000000000000000000000000000000000000000ffffc41044020000000000000000000000000000000000000000000000000000ffff3ffffff80000000000000000000000000000000000000000000000000000ffff3ffff7780000000000000000000000000000000000000000000000000000fff7bffffbfd0000000000000000000000000000000000000000000000000000fff7bffff3780000000000000000000000000000000000000000000000000000fff73ffffbf80000000000000000000000000000000000000000000000000000ffeeffffbfff
  | 1, 9 => 0xffffd4b2f41a0000000000000000000000000000000000000000000000000000ffffd492dc8f0000000000000000000000000000000000000000000000000000ffffcf9e4f870000000000000000000000000000000000000000000000000000ffffc4924c870000000000000000000000000000000000000000000000000000fffff471f47a0000000000000000000000000000000000000000000000000000ffffef5d47620000000000000000000000000000000000000000000000000000ffffe45144620000000000000000000000000000000000000000000000000000ffffd4b2c41f
  | 1, 10 => 0xffffff5fffea0000000000000000000000000000000000000000000000000000ffffff9fdfaf0000000000000000000000000000000000000000000000000000fffffe1fd52a0000000000000000000000000000000000000000000000000000fffff5f7ffff0000000000000000000000000000000000000000000000000000ffffefdf7fe70000000000000000000000000000000000000000000000000000ffffe5557fe20000000000000000000000000000000000000000000000000000ffffdfbeff9f0000000000000000000000000000000000000000000000000000ffffd4b2fc9f
  | 1, 11 => 0xfffffffff77a0000000000000000000000000000000000000000000000000000fffffffafedf0000000000000000000000000000000000000000000000000000fffffffe6fd70000000000000000000000000000000000000000000000000000fffffff86652
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 220 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 220 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 220 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 220 then wireAt i else 0
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
  | 5 => 49
  | 6 => 849
  | 7 => 2953
  | 8 => 622
  | 9 => 6
  | _ => 0
def CH : Nat → Nat → Nat
  | 5, 0 => 0xfec37eb8d4bdaf90ce9f2c6dc9a8ffaac7cc907db1898289a35c9dd69576008f8f8bfb7a846faaa77c0eaaa9751613f16ff5f3896a9229cd690b536461d7af806198c3205f69ee175e2d8aab5e2487c25d8c01525c8d33e8532a6f1250f9f5494c753f2d4c0d1f964a0fbea6468f8d1245227f7142b779a3418b8ad54186b8173bd4a88b3bceecb53294dd262d1121562c1c38e12b7a26fe2626eab32171cbeb1da2b6e21240cf890e2d3c2d0dfb5be7083364ee0791530b01a038e70158c07e00dc39ff
  | 6, 0 => 0xe457d7d0e1cb4fc0dfc2cef0d6e8d170d4ae8920d1e5eea0cbb1be00cabde0a0bd4ce730bcfb3fa0bb5b40f0baea9570b7002330b09be840ab3b82d0a7677f50a4bb82b0a4512b30a1efef009e76cd909cab3ef09b7e779096e94380922d09808ed357c08e9be360861431c07a521680772c9e80772bb3e069bc50206519409064bab2605ca702105b8649705ab788a05a805b705a197e90599fa2505941c82053f9f860505ca7204a0f63a04773d4504762c36045ca2570342cb9502e6ce0f02cc506b0229104301fb538001d29fcd01af582a017005b6013f1996011daf4c0111388401066dc700dd3aaa00d6864300bbc06900b294a70046618f00054bc7
  | 6, 1 => 0x1b35e26c1ae2b9091acbab401aa400a01a8e41591a85e0ab1a3fc2e51a3838981a2639791a0f2ada19ba301a197c4452194d575a1937f12c18f26c4c18dfc053183f407c1794abf01755591d1701656116fc26b516ec765a16eb0e0416771b721673385e16718ae7161c81b315c8de8115c3e20d1594fa3815311fe214a896c9149b001d144f729613e3623713967e2f1356a1bd133e694c13350bca12aced291299497c1273fa32126bfdab12279d2411f45ea911cd770e11a70469119dfe101161181a11532b49114d8aa310c3800910649d970fcb33c20fafc47d0f8898390f173e660f124bee0f115ba20ee2d2210eb903040e7e15130e5f4a880e5d008b
  | 6, 2 => 0x2a347f1929eedbb829e188d329d2bd7f29808263293f76f0293b50d2292f8a3b28dfd71e28b4110828a4a83e2879dc2828732d7b28388f0f281a6a4327fc79e3277c205e26e23bf026d3ff372629ae6e2626b09b25d32ac2257d59b824f94ffb24997c072496c8bb2465a67c23efd73c23e3e51a23b5d9fe2330709522bbb1f12265be982244ea16222c7980221d320721b0632821b04b4821602a3f213dbcc5213869ba210e5d9720c912ec20bc756a206d0bcf2036b16120292edb1fa0bfc01f641c9d1f3a58a71edf98431e9cc3911e4a11701dfb74991df679371d4b60a21d49aee91c9d31101c7c21411bd992f61baefe391b95e62c1b6d57411b544ecf
  | 6, 3 => 0x37d25d2a37cbe72837809ff0369ccad4369aefab3660102c35f9740935dd329c35d5916435c6e9dd357568583556e607355171d6353a12a93515beef34a369a7347134c634380ab0338d7624337c3f77335bf754333d305e32fa2f9532e5408e32973ec6328e87083241f77231e3890231b7c99831adbe62318d3d0430ef49ec3099cb893037bc2b30378bbb300d062a300bb48d2fee79012fd39b2d2f653d432f2d39052ef81bc92ef292772eadcace2e1a843f2dde33dd2d848bfd2d6e8c932cce811c2cab1c642ca4cf072c27cd052bec834e2be7580c2be61f7b2be3fc842bd9e6b92b81626d2ae434a82ab77fdf2aa964312a74cf622a71da712a438fa1
  | 6, 4 => 0x46ba812f4675c8f94642c44a45a7f598458a470a457f9aff4565005f451f7c0844ef9f3c44eaeec244a5495d44540250440925f043be2fdc434ac03243091b4242e2365142c20b6c42b779a342b49765429d7e914299c0a64273d9be41d2b5e941cdfba6413a622b4130a406411ec8a34108cf1b407225523fdedec33fc0c4623fb888503f19de853e438e3e3e25229f3e1ce6143e1494e33e0fc03d3de716c23db5cccb3d99f2943d4e5b033d2c7c353cefd2853cb53f9e3c9d75a23c5679aa3c4a4fba3c21f90f3bc70d473bad5cf53baa073b3b5816813a84e7713a4fc20639b5ed2139614ab838ced83238bbbf8c38a269bd3896d4073844218c383fc123
  | 6, 5 => 0x53c11a42538a82d5533f497d52acb7a0529efe08529ca47f5267761a5255b2c552147bd851cc3e21518d110e516907d050e7f72d50ad33834ffd7cef4fb16bbf4f9f11514f91d4624f528bca4f3d32654f1bb8244ebf453b4e5da3554e29c7d14e19168a4df9a3944df19a9c4dbb91724db8428c4db093cc4d8f90524d86bbea4d84259f4d40ae504ccace054c6a28d04c4df3974beee6fc4bc38b784ba311f14b6e21e64b24895f4b1dd1994adb885d4ad3d99d4ac0847c4aae3b9e4a3f27a84a1426de49af323749025a6e48f9254548f6592348cbb65d48bb892a48b438cc486c7dca48558c3947fc36374773ed4b47722ff5473a9a8b4734e63a4724ee6c
  | 6, 6 => 0x66b3495666b07251660cf112654b05bf654a77cb64f1f45764e6ab02645af9456423d9c863f9e42463669d95634d4e4263474bf462a21d5162806fa762474da361e8177e6176425e614dca256118463c60f4029c60ec766760b5bb09609e1391600ad1db5fc63bae5fac40685fa4c0845f398d535ebad5a05eb9ad2c5eafd4ec5e9e51945e6ca3f25e2f68925d576f0c5d4d88645d36b8f85d26770c5cde0cce5b3bed485ae7f84c5aa8a6b95a657cac5a09b24b5925466959098d9058e2513058986d8f5856ba0b5804cc7a577377cb574207dd5707220b56f8c50256e35aec56d8d8bb55a74f47557c9ff554ba54e35474d588541df39b5407fd7253c4b15c
  | 6, 7 => 0x779fe72f777cb77e774e92af774727dc7717771a770d9b6876b2d3b675af2d3a759a331b7592030a7578bdb57563d287754fe6cf751113a074e35f2f730a5f697305b12072e5136372a690cc729c03867297ce7f727718da7263ed8471dfcdf671b9f52171acb963716feb8970eea42e70e87d76705b5d9f704d5e58701596636fa4e6c26f70d59c6ecfff346d82c2bf6d76322f6d66356b6d5e69576cdf2d166c899b716c61f74d6be0137f6b43cd8a6afac8926adec8c96aae745d69d0a4b069a2761269397884692d2566692ba2fb68eb1e256862f3046810102967a7b8ad67854e436777ddc06763e9e56759339d67339425672e5579670093f766d0a356
  | 6, 8 => 0x888265a588672a82882032ad87e53ae187c3e765876f8b5186896e978642587286195457860d8df385e13e5585a829a48564247785353ca285215bbd84f12a9784987d058436e17f842ebc3f841919e084129c4083e1bfe483c8f6ab83aa90d38370a7f4835cb41983345206832189ea8319ef2882df3e3c82b613c5825f8968823e3dc48229ac8481e9f85c81556ecc8115a7a780f4c637803b98e27fb807ca7f78bc997f30ab157f24c13b7f2210c27f1c9e7d7f0d3e2d7dd0cb7e7dab1b9e7d029aeb7ca8f3cc7c95abe27c039c0f7bf49e177bc1fe837b4794bc7ace616f7aaf2d897a85129f7a5971ad79e15a28799f1f7c7982a2c1791205e277abf413
  | 6, 9 => 0x9f9f6c979f5193b59e499af29d72dd149d57d1949d0bc8029b7186cd9a1d6a4799af20c7996a2a2d989eac8e987a136098602235980162d397dbe83897ac0d109795c1f9972eb7d7970c2c4f96f3335c96db332596b6823f96980e6b962e58a694f9823694d7782194d5c0b494ab739f93f7644e9385fd42937d188992e5b3da92c480a292ab9dea9190d39c9148b1039138155890fd764c90e2f04490dc2963908624849082705d8ffa0a968fcda59d8f7ea0df8f2b009f8edbe0108e4d0a488e066d448d8701a48d5eaaf98cd1964a8c76bee98c6d2a8e8bf059ec8be0e7ea8bb03b728ba0ae678b7945308b4da15b8b38c2288aa1511f8a81f0ca890f53db
  | 6, 10 => 0xb8afd059b7b9b097b759e881b6accc0db6688cecb616347bb5814321b567cb61b4009ee4b36d65c4b326e2eab3088cf5b2f8b09db2c53fb9b2b29e6bb22bdbebb20619abb1d9005cb1c3a841b16a2ad8b149ef60b0df9edeb0c17e9db0937381b078988faff02e82afd87cd4afc9bbddafbae177af75e2bdae6b0456acfe865eacad57e2ac970227abb766c7ab7eb3a4ab701c92ab415c68aad4aa44a84edc83a723c95aa6b1151ba67a4b82a621259fa4b989ffa47ac71da42b2f5ba3ffc12ea3dc97b0a3bcb199a3ab4432a36df571a30cd68fa2b69e03a27358a5a256c1a0a24442aea1caad00a0e9f4cba09c2960a05b43e5a033f13ca0156c749fa73223
  | 6, 11 => 0xd38e54d3d37920bfd35cca1dd282ff82d1fa8926d17f0007d17e03dad06c458ad01d9a9ecf8745bfcf6ebc8fcde805e0cd357c88ccbba923ccadb8b9cb2d3d5ccb256f71cb16c110caf5a39dcad172fbca536b4ec8c018fec83f9268c768e6c6c73fff91c73a269cc7028e92c6a433bbc599208bc5368674c43ecf6ec2d70d8cc2d14b28c24f89c6c2217eaac11e039ac10f4154c0bc4910c0b25433c0ac4ee5c0981e2cc03fc5b1bfb2731bbfa40e66bf8705ebbf53189abf34b798bede3a61beae8066be8576efbe4be64fbd8203c1bcbf7b05bcbbca35bc5861dcbc0e36a8bbe6dd5cba84013eb9fd5190b9770643b9661604b90f0379b8f18557b8ca1cd1
  | 6, 12 => 0xf682c6c7f5803127f55da781f5061260f44935f4f439c8ebf3d6a6a3f325f98ff2ed2f3af2da6a70f2854adff1aaee29f19dcd99f0f8df95f07e4c7aef46a522eef3064ded2ae9e7ece4c363ec39fc34ebc26cddeb4fcf47ea742c98ea70ab0be919e04ae831b648e765b7d3e6ee6dd1e5a63f37e58b804be5773b82e539fca5e4f80626e4299312e377b765e2f6af66e2c800d1e25263cde2513c23e175263be1510bd8e07b17aee03629dddf5d199fdefb0a41de7da2c2de72f46eddb16651dd256194dc47da13dbf98ad8daa96d91d9352887d872797ad7f61629d7ca6921d7b9d51fd7783301d6455af1d63c140cd4a54a7ed46518b5d4413610d3f48989
  | 6, 13 => 0xff708199fed2e10cfecd2018fe2a659ffe1b4e2efdc77755fc7b90a2fbf44d83fb57dab3fae73b35fac52187fa6bbea2f96feb04f8d12158f87556f7f775323cf6ff1a04
  | 7, 0 => 0x355cd5803476202033b05b5033a727c0330c812030a418d02e9d44b02e2bc3202dc927b02d6a72e02b36498029f514b029bda2f029aef9e0295a270028de01e028da25d026d0a5f026249d20249a99b0240dc18023f5c5b02363de20219fdf802102cb9020b934d01eac28901e3cad001abdea401a5e674019fd767019f361a019c9fad0198403d019186980188fb4b01866a3601794b5f01652a32015fcb3e015437cd014fcec70146c416014268c7012a58400124c53e0111cbc9011182d800f76a5900f5a3d200ea38dd00c4d48b00955441007dbb7a006fb9d3006c2684005b006f00481fea003e83f9003b1ab40031a7ea002d875e0029bfef00273479
  | 7, 1 => 0x78b62840787d7a50772bb3e07492140073a22a10725e9590720ca0a0709752007073daf06fe4f3806fb5c5206a8768f068d7fe1068bc39d06735b220665520c065dc92d065d56850659646506540181064cb8090644c92306411f480638a75e06291d83060f596e060e91e7060e01a405e9221005e1326505c61dd605b43f6005ad2f3405a9e53f0594ac960590ddec057ed236057729b60575e13b053c27610535f29d052aa49505270d1e051f5e5e05169eb00514ebac0509fa1f04e37e8404df8b0c04bca65904aaa2b0049f4c5904824cd4046088880459b5e304427d3b042d77d5041237e503ae4e990398d123038177850375c6cf035eb4ec035987fe
  | 7, 2 => 0xb7f14bf0b76e6c50b41c7720b3b2aae0b337bee0b2912830b2179b20b1a7d630b15b2110af89e950af6cb310af23e1b0ae653d70ae34fac0acf09dd0ac986c50ac5e84e0ab8b2690aad79ad0aa0caca0aa03d900a9733de0a9628be0a81a3e10a7a55280a78383b0a6426b20a5e33fe0a4eea960a3d884a09ee1b6f09ec2ffe09ea0c3209d1727609a18f540989c7c3096e691e09643386093e73560938390c091574c6090dfc840903dbc508df973908c7c03908c5dc3f08b46af108b081660899ab53087a815b08739b700865d84f0856ca26084e43660844bf83083004ee081c74db081be46607f70b8707f1b6d607ed8a3207c038b307962ead0790b29f
  | 7, 3 => 0xf1c66040f1bfb200f1a8f2b0f16fff20f06017a0ef5604a0eef2d5f0ee7b93a0ed019dd0e90cf7c0e8414b20e7e15130e7dd0190e67dc250e5d94ed0e4ddd170e39d93f0e1ee4940e19c3470e05ccb20dfb96ef0df565b60df435510df1ea5d0ddd4aa00dd633720dcd46f30db9c7830db51cee0d9cbe430d92daa50d6e8d170d61f2fb0d5a81df0d570f570d49c4170d2aded90cf439bf0cedf22c0cd896110cb5970c0cabde0a0ca165b80c97cf590c867e660c7bcab90c6f23470c6ed2f30c6d8e9c0c687b0e0c2ad96d0c22507d0c0bf6ea0c03b9010bee5d4b0bd70bfb0bd3d3cb0bb0f9310ba77e000ba0f9160b9c943f0b9beb890b8ad6cc0b88cc09
  | 7, 4 => 0x12488876123c1c3b1236e74d1233466a123247971228cbf912245a68121617f5120061e011d640d011c1f92a11bd50f4119b91ab11981144118d0e1d11880f961187183a1176346c1167b40d115e1032115b67ca114c695c11408e9a110f8d8e1106ad5710de35ff10c280c5109faa42109bbfbb108ef5b9108bef57106ef5981052a2c51045f7a2103a9912102497a91015aee71004efa21004221f0ffdfe370ff073950fec104b0fcb33c20fc7e3a30fc75d210fb1a7760faa77070f9788b90f97753d0f8e38f60f8b2a5f0f8899180f8898390f808c130f8009980f799f850f77871a0f7093b80f56ffe60f53334a0f3d84400f3a3da50f33fdd90f2c4f19
  | 7, 5 => 0x16987722168bc85d164f38e016446b9c164042a2163cc6661612f34116118174160c7aef16045d0715f022ce15e9498b15cb6ef015b3f79d15b18426158c470e1581f8c8157b3ef615776f951561a43a15602014155ed0bb154b3952153eaa181517feab14e907ff14e2d7e014db292014db18b514c7c3fb14b47c3e1499cfe51480f23a14696ac21452924414466a841444661f1420fefd1415063f1413d60813e90d2b13e0e2a713bf6c0813aad82f13967e2f138cad00135b1c7b13346ed1132f5cf4132f4ac71320e8dc1317dd2b130a5a8912ff424112ddb43412c3605312bb814412b8ab4112aabf8d12a8595d12763853125d0b7e12557e88124d6d63
  | 7, 6 => 0x19ddb2d519d2796319b64fa119a917ce198e7f10198916cb1980bc29197741991966b800196672e119403fcf19399e181921f28d19169d3318f302eb18ef4baf18eed24c18e4a1d018e3fb0a18e1173618c904ec18c40ebb18ac994f1882b169187cdaee18787ffd186366e31862a4c9185b40f9185aec9118595dba185955ec184a30ad183afea71830634d18261f78181c0a6c18129d1b18103f8818043d6917e4d13d17ddd95917dbb70317d64a9117c5c22e17bf920f17bcd81e17aeb25017a3f1f517a260fe179c6b23177154d6175c2c75175a929b172bb2661729918f172938d716d77b9d16d21d8816c91dcd16bceacf16b50ee916b01e5416995adb
  | 7, 7 => 0x1d89743f1d85da9b1d85cfcc1d83b5c31d825b1b1d81c57f1d7215931d6df52d1d4a9d981d2a81d31d1fa1751d160c6b1d07cbc61cfd2fc91ccc0bd21cbf657e1ca481c01ca3f4021ca0b1831c84fb571c676f431c5377201c397d011c32bad41c228a231c1ffead1c193f401c0dd5381c0c1b4b1bf5be811bea35011bc210541baf8e761b9f1c631b9386ad1b8548e61b78d4bc1b62a5db1b55df541b52f3321b5233871b27d2611b25678b1b1c36fd1b18cedd1b16f5ed1ae9b4a21ac899ce1ab658ae1a9c7f661a9329761a63b4731a5fb1a01a4058c31a33b1c31a2660db1a1cf3441a13ea6d1a0dc40d1a04d97919ff9c8019fd5caf19fc1ed919e5257c
  | 7, 8 => 0x21d8db4721ce372521c636b821a5f9682177d4282161be9a2160b5cc2145ca59213dff812124609220f506ac20eb96a220e2e2e920df43cc20d5617920a84c142089ff20206bd0132064873a205b0a2a204aaf5c203a91681ff58b481fed21a51fe039d21fd3c25f1fb72b911fad31dc1fa939b01fa23c8a1f9874111f9547f51f4cfea11f47d9851f3e5d811f3d31db1f2ee9851f06a07c1f0286b71ee07af31edb86661ed94da01ec4d0da1ec0fa371ebcbc8f1ebb13731eaa0f9b1ea663541ea4ddda1e95def71e8c48a51e8465841e6f5e891e5ad6651e5a4bef1e35b7f71e2d04af1e08e1531e0576261de45f961de177831d9945271d98a19b1d948ff7
  | 7, 9 => 0x2750b4f62745d00f273e087b272a02302710b40c26eeeb7b26d16b4626d0c80326beaf6f26bb2fef26b6387026ad1191269ac23a267c3f2426640762265b05052639a0bd262a32f4261c309d260a164f260932412604931525afebbc259a3137258d7136258a599a25685a9d253ef9ad250aba5724f27cee24ef47cf24e504de24dd90d224c9ba2d24bcbbe924ae713a24467ae924429b14243971d52437f8a9242f7cff241577b924140a412409402823f0c29e23e92d1223e6546623bb3be323aa74da2341f140233e519823057c1922ec6a8722d85c9a22cd956122c4f10a22baad2d22a82de12289ec0b22805475225693612219ec0a21e6cbde21de28f9
  | 7, 10 => 0x2a6540552a6347522a60e87e2a60bc7d2a5617002a5335872a4238582a4014db2a3198e02a2ab54a2a2aa3142a222ab32a147f2229f9c57229f382f529f0b1cd29ed6e3b29da34ba29d4eeb929c478db29b291b729b1bd8a2993998d2992b9322989cbc02981add829740e86296b38aa2964176b295678be2947c17129366e082934275729319d85292af8b72920d8b3291d2a9e291385ac2912a74928e3ecc328e1d56328df87aa28d3f68428c73e9828b1318528a4634428777069286658d02864a6e02842fbd32842e26228233034281a4d9f281909f62803ddcb27d2573727c3516e279f070c27795cd1276fb0f9275d8171275d28bc275b976e275958f2
  | 7, 11 => 0x2e9ce25c2e9987ce2e8af7a22e8a65942e7ac5422e3ae3492df877932df741622dec4b6b2de6358a2dc5ce1f2dbac35e2da94f942d98c7d02d93a3d72d90db782d8de92d2d70ced82d618f3b2d5ab92f2d59ed9f2d4fca342d4b28f82d4518622d17f6e82d06d0c22cf085992cdf3e6c2cc795ae2cb7e2692ca069f22c97836b2c86b1b52c7afb6d2c6cb9a92c611b6b2c58dac22c42325c2c2937292c18d8712be239292baf6f8f2badab652b81faf52b81626d2b7b467f2b5913022b3e6d342b27b74c2b19bbf42b1903882b0fca262b0a8d592b09ceab2af8e8dd2af68de12af3c5ea2ad9fd9b2acd7a982aa00b9d2a95810c2a8c3c9c2a8999b02a6f2883
  | 7, 12 => 0x330a8e35330961a632f3702832e16b8932d045d132cae7bc32ba82ac32b9632332a1bcd53294f0e032854622326bf53f3264f194326007a8324417603241705c32113f4a31ffed8331959d4e318b16ac3177ea8831752de73159aba131524591315024ba314b726931389c993122199e3118539930eb45fe30ddf49130d5282030a5e218309e6aff308c42f8303f34b8303037e9302ca777301b2a853016b5f9301052cd300601422fbbf89b2fb1aafd2f954dd02f8f1ff32f86b33f2f8141142f7a8db12f74af282f67316b2f48cad42f3594f12f2cdf472f20329b2f1d2f5b2f1abea52f15a0e52f1362052efbd9642eedfa852ecd9b512eaecdd02ea52332
  | 7, 13 => 0x3702e44236e2575236de7a8736cd76be36c744ae36b5383e368939d03678c0eb366fa2723669c03b366946d0366487033644f7dd3615bd78360938793601d28435fe022a35f2a55735f0e23f35e7486435d89aaa35bf14c335abdc1135a0b6f0359e2116358ad894357193a6356512d0353aa3c635009d3534f524f934ceb8d134c8f0c734a771a734a369a7349995fb3481cae43481847a347c735e3466ebee3453b6c53451707d34487e12344363f6343a84db340993c534064f6c33dd474d33d93c6b33d8677333d51d6733ce134333c3d97933a2828e33a0067c339be830338d060c33722ba0336a01d233511330332a82ad33193e9a3311d70d330bca3f
  | 7, 14 => 0x3a861c993a822ece3a73bcfc3a64e63a3a4766343a2d4b643a0691363a03d4b139fa66b039f7e21b39e16a4739de4fb639ddf64839ddbebc39b5e92239ae44eb39ade8f339a3fedd39a3264a399f4d12397752013975aed6396f572d3958c2ee394f14203939679c39234c07390ed69f390153ab38facf2638ed9e2f38ed825b38eb527838e1a69e38da452b38c6876638bbb16438a80b973899ed1838962217388012b1387c22163866c394383a0cba383545ab382eb67e3821da66381fcf1438120974380d7bfe3808c7823801a25237d8b58137b9f43e37b281a737a4a2c837a4666c379431c33790d599376ecd623766c8503743a61d371b9b9637125b3f
  | 7, 15 => 0x3e277fff3e0be7f03de291263da8061b3da4f3293d9c64d73d9457913d8f565c3d8a3cae3d7dc3333d727f8e3d67d4943d60158c3d5c32c83d5b65d93d2c0f443d2562093d1f3f593d0e52963d0b3b903d0124c93ce460d63ce437ac3ce3872c3ce1683c3cda06bb3cd396533cc696da3cbde0b03cbcf7af3cba78eb3c9d75a23c47e00f3c407f353c38e0113c35f2033c346cd83c27f8ae3bd6ad1d3bcc8c933bbf524e3bbe60cd3ba7c5f03ba5ac113b9031bd3b795ba03b5dab7f3b4bea9a3b40a23f3b34c0e23b33d6c03b1004203b0c2ead3b0a44b33b08dcd23af6ada23ae826bb3acf9b4b3acedf3f3aace7f43a9a85bd3a97b4d03a8cc1993a8b1a65
  | 7, 16 => 0x424acd37424083084221143d4214fad1420d2e5641ec4f6f41d387bf417515864170bcbe416de72c4149098f41320659412c1b384110f4a8410d769640fe085a40e8120340c96f0f40a60e3740936de140846bf64079f6e6406f21e9405ffdff405e8a73405c8f3d40477ed140455b7a4042c3c8403af74d3ff4ef3e3fed881a3feafc213fe000373fd24e333fc11baf3fb404613f98a6d63f8ddd6d3f82b8df3f7f6a493f6ce07e3f6aee9b3f62ae583f5aa7ff3f5789763f55675e3f4a127a3f4622693f291ad13f227ddf3f15457d3f147cd73f0983eb3ef484683ee6de3d3ee052543ebac68e3e8cd15e3e791ea93e49633b3e444aad3e3c0ae43e3a3ac4
  | 7, 17 => 0x46ec901e46e1bded46df279b46de284246c9322546c7c63546a6e54b469461624687df064667f2b746260195462000d2460f5a0845f5ff6d45f28fa6459774c2457c8acd456daacd4563ccbf4529a6cb4526b408450ea01a44fe769744ed242644df840d44d46f7844cd758b44ae84d9449d30354493ef314493839c4486548a447f91b14458f2e5440913f44408d56743f5039043eb0c0643df582343db6ae443d4155d43c469ce43be7d4943bc23ab43a9f8484397d14043555fb0434bdc18433f660a433cb82e4336d2af432dfd824329eeaf4325dcc44305883642f2e46442e7b5af42c90b1142b779a342b451b04291ffc94270b5be425ac010424d728e
  | 7, 18 => 0x4b299fee4b2472944b226b904b1e92974b1168534b02825d4aee81944aee73794acc75434aca3bcf4ac64d7b4ab9f0674aabf4e84a9a544d4a83c1d64a44957f4a4249ab4a20e91b4a0b380549f3d2f349e579ed49af3f14498effba4987e8284978f86a4978c0ae49697f42496885e54943f32c493c34104939f5304939e1cf492acee949226c8f49148db04910933d48f6c24648f4f2fe48f0ff0048ed4cc248d2e75b48c35a8b48b0ac9d4853cfc44850b42848360ca14834c86547ff7ab347e43cbf47d1bb1b47d0c7f247bc775947ba59f747a3d5234795ee6d476a5be9476409d7476086824727debc471a541a471718c446f2a30146f1b31146ed067a
  | 7, 19 => 0x4ffcc3574ff820184fc71f074fb50f3e4faafd564fa260824f9d2f8d4f9d1e774f56d9744f050fd04f0494734ed5e3f64ecc8e064ea817a54ea4fa1c4ea474154e8d54f14e8c86004e6d16534e69355f4e5372144e3b68614e3a3a904e2566f84e18a5394de27c5e4de2370b4dd542384dd3ad484dc9c7c04dc8be514dc27b5b4dc0f5744db0fe984d841dce4d77b7814d3fd1c54d3c580d4d2ff4d14d2f3d364cfd734b4ce9ee494ce8bf224cd6bec54c8a818c4c77c2484c7463374c70a3534c46545e4c4491e44c29021d4c2571154c1e35cd4bf147df4bb8d2fa4ba1260e4b9665454b81ba084b77d19c4b6e21e64b6978864b6231954b5eae324b2d583b
  | 7, 20 => 0x53de825653dd4ed053ca920853b2be7253ad163d53a51bbc5377f3e65372c479536a150753514afd53466db85318fcd3531108a652e8c50e52e71d0152dc9cdc52dbe80452ce9ec252a439b5528ce01952820404526177285253af2952534f94524e709e524a17a8523dc21151f6a40d51ed228251e93bed51dd55d151bb2a0f519006da5184d1d45143b19c513a17cc5136a9a35133fceb512f7572512b0ac35129991d511d2be451099cc650ef354250e499dd50dc89c550b1940650a97304509f5416509f358a5096359d507c409650754638506b190f505beeb35059633d50490acd504513215036165a502b2686501f9e515014114e500139404fff2dd5
  | 7, 21 => 0x58514614584e132a583019b95817addf5807cc095795fc8d578e67bf578c8c39576d478157685cd7576751eb576054b9575675b3574ab38e5744b4ce573f8ef4573f2853573149745727b7f45707fb6756f411bd56f3df7156c5d00a568ff7f1568d8c7e567ee6cd567c7f515672b54a5672a487565c104856403068563580cb562fa21b561b43675618ad15561504715600570755f6748055d8ab8a557f4cd95530a86c55122fc955067f9c54fdc76d54f251df54e7b9da54de0ffe54d5ab8054b8020854b5735e54b47b9854afff1c54acafc454a96c0954a16d3c5474abff5467b4c65459014c54324e155416d04b540a4dbd53f747b753ec72ba53e18f1b
  | 7, 22 => 0x5cdd51985cd9f6e05cc51a225c9fbd605c9b90375c91de815c702dd85c5858275c499e5b5c4918f65c33c1815c0bbbc75bb357745bb226b25bb03c075ba3354b5b8e88025b6fefcf5b6b6fdf5b4dbe2c5b34bf745b1f7a795aecd9575ae1ffbf5ac07c685aadae925aa5f5965aa52f8d5a97a4eb5a9469955a8d74075a859b925a8322685a7707165a71d2525a6fa4e45a6d6fbe5a6beea55a6afd255a62dc0f5a5bc6655a437adf59f11cdb59b8610d59b3a05959aeef8f5996f4f559952f0b597e76b4597bfa8959737dfd595c19525956695a5936765a593250225927b4ea58e6c54658d7b5fd58c55e5b58bb531a58bad09958b56100588269ee586233b2
  | 7, 23 => 0x61a45f8b617d3f4b613fcc2c6119d7e1610c35a86108511860f47f6c60e8d6d560dc0ef760c0e6cc60bd229660a7ce4460a44355609e4fcb607f1ebe606901036058ad0a6056b15e604fd85a6049964d604693fd602e455b601d48af601b43135fd04d605fc559925fbe37825fbac6fd5fa8e5035fa001255f878d095f5675315f4d90645f416ceb5f411ea25f20e9805f0248a15f0047115ef408b65ed6a3f15ec5fd9a5ebac33b5eb5ede35e5e95475e56e6485e427dc45e0e53495dfe16575debf6475de083ce5dd41be55dd08b735da6006b5d8bf1475d7d6e2d5d7bf2db5d796a795d6dd96d5d65f9355d5624535d48a8d45d384f2c5cea4ee05cde0cce
  | 7, 24 => 0x66e5ae6b66c9726066c669ef669e5573669a4886666aceee6644c8f866357d3e6625b9e96617db0a65d6d88f65b3f9f765a826966584a32a65524fc665381a02653364ff651506a4650bdfd764edbd3264ea33b664e6ab0264dbdd2164c8c42e64c5236664bb002464b320fe649ea5e064789948646b28aa6449b75d643ac406643609f56433ac9f642e54a0641ca4e76414205d6413866e63e50b4763bad2eb63b3242b63a6a9d363939f33637c7ea663720e7a63669d95631fb153630aea4562dfa08f62da882162a39a81628e144f624ac82b62346637623058b562256876621bcd566212b35a61f427ee61de9b7b61ca400861b8723761aa336861a86330
  | 7, 25 => 0x6b76748c6b70d1e96b67104f6b3934176b3457826b1a64bf6b0d63fc6b0959bc6afac8926af897496ae6f02c6ad62f646ac5c8b56abcdfc56aa508c56a9be0a66a95be0b6a91b37d6a80e84b6a7ff6686a6a7ad66a4f22086a41bcfc6a2e06a76a22b4f86a13aebb6a08bb056a0829146a00c0a569edc24469db469269da0c1f69cd7e5369c0add469b0c44b69b08c9069ac5725697d0059694fc71e692183276909bb466909685e6909578d68fc7721688d1b55682a009568090f896805cfb767f1c0d367eb4a3067d9415267d620b967a71cda67891a306781da4467619883675e868767322581672edba167296a4a6725e9c567044c4c66fc748866fb4c91
  | 7, 26 => 0x70a579f87066c393705b5d9f703b0e08701d07ab701a846e70183850700050ab6ff70bd36fe18fc46fb5ec216fb3739e6f6a8dfb6f4c3cf56f43e1be6eed418f6ec911ee6ec76b136ec28c856ebe77696eaec77d6ea4ed216e81dc4c6e6dcf996e16b7eb6e04f5ec6dec12c46dafa0f16dab2ce86d916c166d7e78d66d748c516d65318d6d483b2f6d35546a6d2cc71f6d1da4d86d10c47a6cfdbf986cf4f29e6cd6ca796ccc398e6ccacce06ccaab146c9c25686c96b4706c85f2fa6c80921c6c79ed6a6c4b6e046c41d5016c2bf7316c2229556c0bc1ba6bf899566bf58d8b6be1bd3a6bd931506bd3e8686bcb63fb6bba30316ba0665d6b9d976b6b846d31
  | 7, 27 => 0x7626fba5760760367601ef8775ea2a0475cfa8b475cf5cc17554e38675447afa7539d269752306507521769374b6ba1474ae2b347485a1e97481ccfa746a0e0a744ac9477448134173ffb2f573f993ba73ea5b6e73a48879739c3b75739a99807393454b736647aa734eaa0d7331c26873275b59730cc97a72ff2f9d72f4555e72e9411572b28339728270b47281f925727daf3d72739f54726a4e0172301b0f7229b8f672286c4f71ffefc671e12dcc71c52b6a71c4843571b7c8f271b731cf71959758718d4b85717f4ee07166cf87715dd49f714b8ec871288197710997a570ff386970fe4ee070f943ac70e34a0670d6da3270cc75eb70bb677e70afabe8
  | 7, 28 => 0x7b334ca57af39e807aef43a17aeab7127adc1f207ab1cd807aa157477a8ef3507a85129f7a7f40357a71dbb67a2bf43679fe78fe79e15a2879d3e13a79d3303379cce61979c219c979bb6d1e79ad6602797234ad79717a8d796deb3979684f62795cf9c5795acc8c792903cc791e9fb778e9916b78d1319678bb1eaa78a66659789257757847c1c278299fcd77e8b9bb77d135d077cfa6b1778424c2777652a77768e8a77753784a7746c839773c94b1772c48f4771f39f87705d5e176f0de3376d6e32176d00d2c76c6508b76c5d6f276b871ac769ee49076863e3b7662c9f5765bdd327654909976509acf764e5f6176461d727643f3d3763c451376374491
  | 7, 29 => 0x8040d07880381ef17fe516d97fe1a60d7fda9b807fca544a7fb866157fa786767f8ef2d87f75ea277f5f0e0b7f4f5e1f7f4af1e47f4590c97f2c02b87f172bf77f0df4cc7f0d3e2d7f05801f7f00ecae7eff2d3a7ef20d5d7eddc2a37edbceae7e9f2c737e704a887e4b07f87e05acff7dffd2af7dfd47397dfb85ac7ddeb6337ddacfa87dd765af7dc594b27db1e1917da0a7537d7fe0cc7d7d57bc7d5aa3917d4ef1927d3371107d300b997d2e7cf97d17292d7cea112d7cb391007ca8786f7c79c7f27c69c65e7c4faf817c4d5ffc7c4c7c107c4bfba17c4260817c40fcff7c140d477c1140187bf0d3337bbafb617ba3c0797b86605a7b665f577b5e52fc
  | 7, 30 => 0x86be95e986bad95e869b75948680741c867726a18665f643865cbae886465a8a863f5b5b861a00e9860c78ef85d3fdb585a0b970858e52b8857f1b66854276918534370f8527bd3a85260ae185215bbd8519787e84fb0b2c84e1769f849e475c84520cd5844c64498422cac9840799a683fe99eb83f9716783e740ff83e41464837f6b3f836a4ef383621177833df903833bbae282e2ff4782de711782b3ae8082a1ab698295aa1e827963fa82585f948220478281e62af881b726b381a1c794818c305a817be6a2814d04b78121dfbc80b3c20480ab0b5c80977014809286e3808b00fd808a241e808528c480822666807ff039806266ad804e802380428191
  | 7, 31 => 0x8c9a327f8c76bee98c66e23c8c47b39e8b8fda438b7e195e8b7531c58b4b91ec8b0cdb878ac398938abb56b98aa44b2d8aa3b04f8a9e78b18a7994f88a553e488a4b88898a46621b8a37c65d8a2ec80d8a0d8ef78a0b34fc89efee9189ef6b9089e4bd8189b6048589b52b5089a86b25899788de894ebb5e894cf985893fe42c89312aef892cfdea89211e6a89061e6888f4b3ca88ede02888e36b1588cd013b88c15bf788b5b0dd88a4fc21888f7ea4886bb2a5885c1c98884d6a8e882e82c9882be4e1881af3898816e9498809f96f87e75edb87e6c54587e152af87e088dd87a5f8ba87a030ec878be23f876ece5a8752d38b8730fd468708035287062e30
  | 7, 32 => 0x92904ad8928e17b2927fc7e792409e49921c7d4492002a6a91f7c8fb91ed9b5991c9a37991aecc4091a73dfd919f9a92919ac8ae919a80f8918c7c03917adf6f916407a09147ad6a90f610e690c7888690c0894f9079ad95906d26119066fa26905bfe5f8fee4cee8fcad59a8fa972eb8fa19e1f8f9fd3cb8f9d1d5f8f74f0a98f6e24048f6057d08f5f11de8f4c472c8f26b32c8f20258d8ee20b498ebf00228eac49d78e9fcbf58e92684e8e7679718e63fa418e2302ba8e1426838dce939b8dbe23998da6f0c78da068838d6fdaea8d5eaaf98d4595e98d395ff68d1b84e68cfeab508cde80148cd7ccae8cb966468caed4eb8cae17488cad401e8ca14df6
  | 7, 33 => 0x99d3056b99ce680e99bed3f9999971879998b6749997d9049978ab00996c23f4992721c299200f9299004fbf98ff0c1898e9771598bfc76298a19efa9885fe88987d90c09854b6199848610498468f5c983ce08197ec88bb97e2d59297d41f8597ce2acb97b3ffd597aa9cac97a5381f97a002259791a640975a043b974d430d96da2b6e96964552968d4d5f967fbfcb9630ff5196255115960d324a95d4c56f9566b56d9551aacc954c87d9952d672c951cbb3294e56e8494de200194b8834e94aba5ca94a8304894a609ff9499c431947da14a93f91dd793e5c51a936ef3a0932ed1f79322c34692fea01592e04bde92d5a09492d3b19e92beb26492bdfe3b
  | 7, 34 => 0xa0178350a0092fe09fa7e8e29f8732b19f77feb79f6868319f5ea4e59f4a44a19f342d229f19428c9efaea139edbc97b9eda496a9ed1e5489ec369af9ec315a79ebfb44d9e91ae509e5f4b7a9e4b2ef19e418da49e1860da9e14ab229e1370af9e0a09409de5cf519de53f919daae7359da5a5db9d9a91c89d99351f9d72dd149d42bc1d9d1f09df9d0504429d046bd09cf2a1969ce7c5ba9ce0c3739cd8b9f79cccd4969cbb54e09cb443fe9cad2a7e9cab92cf9c32deb99bf3d47a9be7a9099bbf435b9b9060219b7a6f559b6cf8b59b6512559b50ca489b34b1219aec1f2b9ae5da449aca79e39ab78fed9aabbbef9a8554239a741ded9a6914bc9a07492d
  | 7, 35 => 0xa685bbbaa656ba0ba5d9d22da592a0a9a57519cca55beef2a5323c56a52d601ca51c3a8ba5103ec2a4ef705ca4eede4aa4e8963ea4dede88a4c7accca4c4fe3ba4b188daa4b0cd10a4ae7b11a494c22fa46c2b99a4647cd9a44634c2a434b4b6a410b11aa4033c3aa3f2435da3ea76e2a3c1ab4ba38922d9a3814b1aa3744415a34b2fb8a32cb193a309310ca2cd8bc3a2c8618ea2a97873a29245d0a284b47ea26ac20ea26534afa263fdeea256c1a0a2487bd3a1feca93a1f7dfcba1f783b5a1f2e5c7a174c228a1662bafa15ebe12a1537f86a1483727a0e1fbbfa0c4a17fa0c208bfa09b5bdda099d7c2a0908dfca05ab451a0566735a02ef21ba0219339
  | 7, 36 => 0xadd493a1adbaafa4ad9683faad90c81dad34d12aace77cbcaca9b064aca8c657ac7b9e87ac610a62ac59c64aac4df83bac0421faabcb65acabbe6218abbd86cdab9f69a8ab89854eab7ff0caab75f941ab676f4fab3f45e1aac711ecaabd8836aaacc2cbaaa935daaa904610aa8df529aa801c35aa75a9a3aa0116e9aa00aaa3a9c3b08aa9983258a98efbbea98e4816a9679bafa9647ee6a94c64a9a8e78fc4a8e5934da8cb32a4a8c9d8aaa8b83798a8b61457a8a73885a89d0c9ca899d8e0a884f245a85b062fa7fbc882a7f526c6a7ba35d6a7aed748a7966e15a788dfb8a764468aa71e49bea70ef21ea6f3a76da6c134b9a6bc62c7a69d5214a6910249
  | 7, 37 => 0xb5a0fe76b5995d73b593ef12b55daf2bb51ce2f2b512b256b4fc8e64b4e46fecb4bad623b4b7aa29b4abe74eb47be621b45f4c90b43f5990b435aab5b432738eb41b0a9db379f728b33f92c7b325de37b322ff62b31e2f22b315333eb2fb9a4cb2f25cf9b2bce3e7b2a6c045b1d1766ab1ce22c6b16a2ad8b14c7d40b0e1dcffb0de38b8b0d5dbb4b0cf1072b0c3750eb09b89e2b08e74bcb06379a0b038e43cb0377981b0114f0aafda19bbafa8260baf9abc18af80d0deaf79b774af75ff26af6b3d75af647c31af3465dfaf332a10aef5af7aaed6ebcfaebe772fae61e220ae55a6dcae265fb5ae1bf85dae064aa9adf1a5e6adec3e13adeaf2e8ade6658d
  | 7, 38 => 0xbc19ed6dbc0c7999bbcf1011bbcc115cbbb69bf5bbb02480bba66d37bb92d9bbbb22dcfdbb13bee6bb0f98aebaf70c47bae1c4e0badd43f2bad4da24bac49c6dbaa1ccbcba558546ba45dd7fba231cbbb9fe2647b9fa70b4b9e4f0ccb9bbecabb99d8907b97b0eeab94d1047b93b8651b9349dd0b932cbabb921fd5ab88c0434b87ee534b85c2f59b84d5911b8485297b8405c07b81d78f4b8025b3bb7f92244b7b92ec7b7ae1533b7aa0c84b7a667eab795a117b793d28db7892a55b78864c3b72f93ffb72e368bb72628a3b71329c5b6f03782b6edc245b6c50266b6bcc305b69c07f9b691c424b6855c3db65207bab623fb60b601f9d2b5f36f3fb5bed785
  | 7, 39 => 0xc38b1211c3780010c364652fc3606443c33ae1e8c3347db3c31b6fd9c31aba35c310f424c30e22efc2fcbfd2c2f91008c2e5ae67c2dde247c2c56a8ec29bf8ddc285e459c2755bb0c25c674ac2472df4c22701b7c1f12b01c1eeb825c1ad95ecc1907b16c154e976c13d7091c111313ec0d8bcdac0b02379c00feba7c00da4a7c0006558bfda4f41bfd1f35bbfb4dd66bfb0cba3bf83682fbf662c09bf1537f5bf01fb40befa2055beea5a39bec33186bec1b0f7bec0a575be6460f8be51e5eebe29b42ebe129a87be0ade22bde1cfb5bdc979a2bd82ee2abd6a8f7fbd63e280bd328e64bcdd2ef2bc87e6edbc7e8f37bc545819bc544fa2bc398ae1bc268fe5
  | 7, 40 => 0xcc639849cc396419cc375d6acc1a159bcbd77c2fcbb9f257cbb88f1ecbb8063dcb7281a8cb6f5908cb6178aacb5221cfcb46a5f8cb40e25ecb2d3d5ccae6a019cac2eddbca740502ca5f7767ca5eb5a5ca14a60bca0e29ffc9f553bac996b3b6c96f57afc934441dc904d60fc8df6e8fc8d8951dc885719dc837e4b7c7fcec2ec7d3f23bc7bdffc1c7b65101c75fdf6ac7554d2ec72863d7c71b1099c71b0c31c6e5027ac6c77138c6bc9380c6a95673c682e025c63e6ab8c63e11c5c637c9f1c60d321bc5c9dc2ac59c2c97c5821593c58038e5c54fca04c52f7576c4b7d0adc4949487c46ac8f7c4410a46c416706bc3e2d77bc3d681efc3b4db41c38b8267
  | 7, 41 => 0xd383a931d3152e0bd3039b18d3024a1dd2e9db6bd2e063b0d2c6073ad2b5723cd2b422bed2a62dd6d2849381d282c284d2440c1fd2370a95d231461dd222b1abd21f33e1d219e748d1d3f658d1c001f7d19616d2d17bf5cfd1293c1cd1145570d0e64a54d0dd3a20d0dcf85bd0bd03c8d07c82add07aaddad0474b66d0325876d028b587cfdba189cfd1b474cfb854c2cf96c9c3cf78f9d1cf66a7efcf1f3ed4cf0dfd72cf0b0317cf0a0fabceddfab4cea2794cce96c38ece8ab657ce844c52ce3dbbbecdf98342cde202f0cdd2d617cdb20f90cda6e723cd6ae6ebcd4f96bbcd3bc669ccf052c5ccc7daa6ccbc3f42ccb4b64fcc994278cc8d2a32cc6d1337
  | 7, 42 => 0xdee6275bdede789bdec9dac1dec9aaa0de90f3a7de7f46b1de622395ddf155d3dddcc838dd9de376dd53a98ddd4db3aadd040b83dc891c35dc52a6e6dbeceb59dbd26c4fdbc7af05db95112edb83fe16db3a67f6db23cb92db15c90ddaf5c757dae9e1fadaae12d4da650bedda60bae0da4ab022da411fa3d9c29a4fd9983b1fd96359b3d9597615d8f800a3d89de169d8198d9fd80862e0d786c099d7661623d7322c12d6ab1780d69e993fd68b73c0d68409acd67f4dd9d5e262c8d5dffed2d5735722d568ff65d530ec02d52b0a13d4fb6d4fd4894f7ed47790a3d445852fd438da3ed41d6596d3dd3852d3c4b81bd3ab69cdd3a13996d3980975d390a498
  | 7, 43 => 0xe729414be6d0b57ee69515eae6577fd9e6229f36e6118099e606f433e605b34ee5cc13a1e595ec33e52d0e51e506db91e4f751b8e4f3f667e4aa967ae491a641e4489ffce4299312e3d420a8e3cc7821e3a5ddcee35f42cae358b1ffe351c056e33cbff7e3212e0be30601bae2ff2848e2f7dbbfe2f02cffe2ef9098e2ee6b60e2aad18ce298b8f8e281e22ce277b2dee25263cde21fca1de1ee1201e1d99749e1808a81e17be059e152e27ee15042f8e1489438e1482590e1283faae105ec43e0efeadae0d18bdae0b9173adffa03e8dfe44f4adfe045a4dfb2a488dfafb75ddf8ae938df7909f5df7206c2df50f4a6df33ac1cdf204264deff409cdee79088
  | 7, 44 => 0xf2976373f2854adff25014fff1c8b033f17a65ebf146644df12be4b6f10d2c13f0ebefe1f0c52c6af052953bf02a6079f0132cb6efedcb45efaf60deef75fb71eecf8408ee9ef80aee5bfb02ee1ad78cedd0785cedb44362edb06ad3ed7d44f8ed7c682aed7abd14ed56b179ed37c018ed270113ecbba0bdec6b46deec497f1dec2d7d95ec2b22aaebfa8983ebc28ee5ebae8402eba6d542eb93c63beb85b3b1eb6a4ac1eb121e74eae79972eae366f4eabec0cdea81aee3ea5d5ff0ea58eba1e9f83c15e96ff558e954087ce9500fafe94a3d90e9145f57e8f0997ae8e680b2e878be20e8674cf3e863d8b7e8529c71e816d1b4e7b0d071e7978a5be73f702c
  | 7, 45 => 0xfe69481bfde4e8a1fd904c97fd1e6eeafd16c02afcf063cefce8b50efccb4487fca60f23fc78f6f8fc6afe7dfc50f767fc465d48fbefb591fbec0709fb738b2cfb3bf322fb379514fb195303fafc002efabc44b5fab495f5fa3689a5f9cab482f9b99d75f9b1cb76f96feb04f96bc8c9f94691eaf8ed2165f8d5ce41f8b72109f886c565f87e7dd9f867a20ff84fd4fbf80299a1f7963571f74120e2f6875a6cf683528bf66a42e8f6281cb5f5c3fe68f58f108cf58b144bf5735d60f5432ea7f5210d0ef49b46c7f48bd63cf3c06a7bf389ecdef34d8d5cf341502cf33b5fd0f33384e5f32330ecf30a602ff2f3ae00f2d35972f2c47494f2bab760f2a6d50a
  | 7, 46 => 0xffcd14d5ffcceadcff77da54ff6283a0ff0db492feb8db38fe89ee6dfe811e1cfe6a9ac7
  | 8, 0 => 0x12ae5da3129997eb12798028124e263511ed84b711eb7ccf11d7480611761aa81142fa411134c93410d1aa96103ead2a0fc22fb60f5c5cfb0f3d84400edd17080ea68d810d9cbe430d52c9a60d4d98860cf91d9f0cea20e10cc7aa850cb3009d0c867e660c2cfbb60bd753a90b989d440aa9dacf0a9628be0a71f9560a172c490878675807d82e3c07bd347d07af559e0754ea15075140fd06ecbabd06c7654b06634425064612c705ad2f3405a3eb0a059e8b170590310f05869eb1040745c603f1b95203e36454036df1500360127102e9d44b02d5abde0296f5790291d00a023c952e01a603fb0198251c0129b75501013f3600dd496a0064991500103def
  | 8, 1 => 0x24a7e76c2485a934246554a62429651523afce9223a7fde6225c733222543c1c21e9d24d21a5f96821a1d26720e970f5204aaf2d2046aaad203e530f203cd04e1fe039d21fd3d3851f608b651ee4e3db1ebb13731eb3facb1e739d441e7359ed1e3d0e221e1aa3ae1d989e101ca0b1831c53b96d1bea35011b70b1901b52f3321b325a461b2d157f1a90e4691a5d39541a45ab1d1a4058c31a2bfa9c1a0ece7019e360491979f417196672e1191531f418e3fb0a183e8305181aa94117d7cb9517d07b0017a820261729918f170db67f1606144c15ff8a4715f86a801561a43a1528ba3c14121a0c13b5da6d136d10ac135211a2131bfefa130748e512b8ab41
  | 8, 2 => 0x3899ed1837a1ed1c378f31e8375fd1e83732d33a3724f45b36c744ae36ad51603678c0eb366fa272363c57f436224d1b361b1af435d89aaa359aee6d357bcd57354bc4fd3518dab13481847a33d93c6b339be83033193e9a330961a6326a0621317141fd315024ba302ca7772efbd9642eedfa852ee51d392ea0b9112d770a592d014b912cf3c0ef2cf085992cae27f22ca821632c9946a22bcf9a012b698d6c2b0f56702a7c85282a6bdfc02a5e00e12a5175e429c478db2964176b2889888f2775450f272770732705880d26d2458e26d0c80326aa53c326a4b5bf265363bb264ea12126488ebe26396ad4262d41fb25bece64259eb530255ffecb2509c4b8
  | 8, 3 => 0x4b7591cb4b62f61f4b02825d4ac0774d4a6707154a3f78dc499cfa0a49226c8f49148db048f889f848f0bd7d48ebd2aa484e6acf475141bb46e1bded46e149a24696c818465e79d545f6b58445c07cca457c5ed145179a8f43cee64d43b9f0a343a9f8484365b3a9433f660a432891ef42b779a342815d8a425327d741d9fb7841d622d341a4b5d64025ca0a3f8b9abe3f6ce07e3f49363a3ee6de3d3e9c5ebb3e277fff3dff89d03df1aaf13dc32c533d8620523d18fbc93d0124c93cd7d7c23c9f3cdf3c9dc2fe3c52b0633c3d49423c39fd5e3bf3e2703b3c318a3acd3e823a8b9b213a861c993a4766343a305add39de879e3958c2ee3950034038ad846e
  | 8, 4 => 0x6129ea2960d1580460c016456001a2b65fbac6fd5f2a63495eebace45ec2fe405ebcebc25dc82fa15d9647d45d93d62e5d6275f45d3a46645d2e415c5d23bf8f5c9fbd605c0095e65bff541c5ba915895a73054d5a437adf59f223e559d66aa05992adb05923c1c656fffaeb56abec62567ee6cd55bb43f755ab6c4653b7a8b55342fdb7531915d15316929452f2fea452de426a52943af552942b7251efbb6051d2062b51ab7a23516924ff515c29195059633d5038abd64fb2394c4f624ff44f490be64ec05ebd4e9d19034e79bd534e5bae794e0e9fc94e00c0ea4de27c5e4dd111674dc27b5b4d2b306b4d17706a4cd8ba054ca60af44c1e35cd4bff26be
  | 8, 5 => 0x7913045378f04d34785a17897733bc5377211a3f76eecc3f76db0b2e76bdf4b976b015da764e5f61764692e675a74bbc7521769374f2245d74e1bd6173a4532b7333c42e72e03d9b727daf3d72739f547260e48f71fb25a271be65bd70c4152b707cee8d6fa6c90d6f3b46226e9f1e276e834bca6e38e6f66e34ebde6ddedbb86d483b2f6ce170276bed6d236bc490ee6b89f08a6b7c11ab6b46b4d16b1be3666aa2ab606a2a46cf6a0139de692e70ee6920920f68ff5c7d688d1b55683fb3fc6554bad164ffcc4e64cf00c5647899486449b75d640159026379a6766347643b633af01163353df463275f156292bf226284e0436240ab8761f427ee61ca4008
  | 8, 6 => 0x965f34589603a49895a996be955a089894331b659409b1f09396353d92ef453392b08ece92278ab591015b8b908ca444906d26118fe9ad8f8f6680978f46f2108eb06ba68e7679718e2374cd8d7f04bb8d6bb4b28d3d413a8bedc1998b7e195e8b3e939c8ab84b5d8a7994f88a4b2c0489f226db88f823fd88edfe0d877910e2876b3203872610b8870803528635a6fc862851b985f48e9f85e99b5485210b03850f030e834a6d9383233d808241b05981b633a5804281917f27d8097ebd26667dd5c4a57dad4e397d33ff317cd372a07c439fcf7c0721267bc86ac17b2b17a17b25f4ae7ae97d0f7a2bfc5d7a2bf43679c9043d79a4d76c7952d274794717d6
  | 8, 7 => 0xb354b256b2f03ccbb2dc7687b2572353b22e7c90b210ca3fb20ffb62b1b17014b18cc501b12375bdb0ec7e1fb04d71d7b0480e0db01ae1b0b00d02d1afebec7daf01b67aaee65ee3adab993dada32de2ac3ab49dac23afedab94b348ab681b8eaaa935daaa75a9a3aa38618da9cb11c2a98c5b5da71939e5a70b5b06a6395456a62fa927a5cabbeaa4dede88a4a02823a36baaf7a141bf77a0b26703a07b39919ffd08839eab30d29e14ab229de9f1209d42bc1d9d3508f49d2d50bb9c1021289bfcd7929b71391a9b34b1219a81c9ca9a36658d99bbfbc9997d4564985a34f7984899db97251c989721f5ed9713ecb196e3fc3596ac2a8596a4b77d9680ac86
  | 8, 8 => 0xd90de9d2d863d13ed7c2c847d7c0c947d7661623d69e993fd58ce416d56748abd4fb6d4fd2da325bd27a66b2cf6e15b1ceecb93fceeb1ad8cecb96dfcea2794ccc0d7bc5ca5eb5a5c9e24337c9d88a90c9d46458c9c8daa4c8df6e8fc7466283c707ac1ec6f762cbc6b603d4c6398efac59d6c30c52f7576c4eae2e7c4d4624bc4ac2c82c483e9fec4605fcec3d681efc398766ec37f968dc30bd3fac23de552c21dcfbbc16463c6c1043454bf46884bbef4bb49bef1afedbeb2f988be4f311bbe107ab6bd3f82f8bd2744b8bcf5d0c6bcb2dff7bad4da24bab08b31ba708858ba477786b85c2f59b7a3f583b6edc245b65f3e8fb644e080b55b444cb47be621
  | 8, 9 => 0xfe9afd92fe091979fc3e0176f80fe67ff7c476a1f762f14af6657479f5596f20f5210d0ef50771aef33b5fd0f30eb1d1f1c31697f14d1f92f109fd47efeaeca8ef7de2e4ef4adc1aef0e3eb4eeae7dabed74eae1ed5612f6eca193e2ebc28ee5eb7a065ae9d3bc26e8b54ab1e606f433e5d4dd4ce575a6eae4763a0be33582dbe32cc12de2f6cc76e21fca1ddec9aaa0de0efbc2ddfd151addd7f9c9dd9de376daf5c757da0af02ed9ed2281d9b9b7a8d9ab6bc3d988b69c
  | 9, 0 => 0xb47be6218ab84b5d2efbd9641e7359ed1606144c1142fa41
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 5, 0 => 0xa0000000000009000000000000200000000000000000000006104000000000000f00000000000120000000000013000000000000f00000000000130000000000013000000000000f00000000000000000000000013000000000000d000000000000d0000000000002000000000001200000000000120000000000012000000000000f0000000000013000000000610400000000000130000000000013000000000001400000000000100000000000012000000000000f000000000000a000000000000f000000000000e
  | 5, 1 => 0x210400000000000120000000002104000000000000f0000000000003000000000000f0000000000005000000000e10000000000061010000000000012000000000a1010000000006100000000000000f0000000000000000000000000f0000000000003000000000a100
  | 6, 0 => 0x80000000002104000000000000800000540812000000000002100000000000000f0000000000005000000000e100000000480e2000000003802201000000000000500000048062010000000006104000000000000d000000000000a000000001210300000000000030000002802201000000000000d0000000000008000000000001200000000000080000000000013000000000a10100000038062000000000000011000000000001300000000000070000001802200000000000000d00000214842010000000000011
  | 6, 1 => 0xa1040000000000006000000000000a0000000000003000000000000d00000000000080000000000003000000480a200000000000e100000000000000f0000000000003000000000000f0000000000000000000000000f0000000012102000000000000f00000000000050000000000003000000000a102000000000000b000000000000b0000052500200000000000e104000000000000500000525002000000000000006000000000e10200000000000080000000000013000000000000200000000000120000000000001
  | 6, 2 => 0x61010000000000002000000000000f000000000a102000000000000d0000000002102000000000000f00000544c42000000000000009000000000e10200000000000010000000000002000000000000f0000000006103000000000000500000104402010000000000009000000000000f00000000000060000051500201000000000610400000000061010000000000011000000001210000000000000010000002806200000000000000800000000000060000000000013000000000210000000000000120000000000012
  | 6, 3 => 0x1000000000000000000038022000000000012101000000000000500000000000120000000000000000000000000a00000514c820000000000061040000002806201000000000e1040000000000013000000000000f000001044020000000000000020000000012102000000000000f0000052440200000000000000f000000000000b0000000006104000000380220000000000061030000054041200000000000a1000000000000013000000000a1040000000000011000000000a10400000000000060000000006101
  | 6, 4 => 0x51500200000000000000f00000524402010000000006102000002148420000000000000080000000000005000000000000400000038022000000000000008000000000000b000000000000f000000000000900000000000050000004806200000000000001300000000000080000000101109000000000210300000000000130000000012102000000000000200000000061030000000006100000000000000d00000520c52010000000012101000000001210000000540812010000000000005000000000a1020000000006102
  | 6, 5 => 0x800000000061000000000000012000000000000f000005350020000000000000060000000000001000000000000f00000000061020000000000011000000280220000000535002000000000000002000000000e102000004250820000000000c410000000001011090000053500201000000000001000000000121000000000006102000000000000b0000052440200000000000000600000000121020000000000006000000000e1020000000000008000000000a104000000000000b00000515002000000000000011
  | 6, 6 => 0xe104000000000e1040000053440200000000000000f00000000000080000000000007000000000e102000000000a10100000000021030000000006103000000000000f000000000000500000104402000000010440200000000000000d00000000000070000003806201000000000a10300000000000050000000006104000000000e1020000050105200000000000000a0000000000011000000000610400000000021000000000000007000000000000d00000000061010000000000012000000000e1030000000000004
  | 6, 7 => 0x210000000000121020000004802200000000000210100000520c52010000002806201000000000e102000000000000f000000000a104000000000001200000000000080000000000002000000000000b00000000061020000000000001000005210d20000000000851020000000000011000000000000800000000000010000000000008000000000a100000000000000800000000000130000000000014000000000000700000504c42000000054041201000000001210200000000000100000000000012000000000000e
  | 6, 8 => 0x210200000000000050000000006103000000000000f00000000000000000000000004000000000a101000000000610400000000000050000000000002000000000610100000048062000000000006102000000000001300000204802000000000101109000000000001100000018022000000000000001000000000e104000000000001100000000000130000053440200000000000610400000000000000000000000006000004050020000000544402000000000012102000000000e10100000028062000000021484200
  | 6, 9 => 0x61000000000000010000000000000a0000002802200000000000e1020000000006102000000000a102000000480a20100000000021020000000000002000000000000f0000003806201000000000000e000000000001400000000401000000054440200000000010d100000000000000f00000000000000000000000000000000380220100000000000040000000012103000000000001200000048022000000000006104000000000000f0000000000007000000000a104000000000000500000000000050000002802201
  | 6, 10 => 0x48022010000000012103000000010110900000000121010000000006104000000000000e0000000000005000000000000200000525002000000000000000000001044020000000000000040000000002104000005408120000000000000120000000000005000000000000f00000314c420100000000000050000000000007000000000000500000028062000000000101109000000000000000000000061020000000000012000000480e20100000525002000000000000000000000000e10200000000121020000000002100
  | 6, 11 => 0x520c5201000000000001400000544c420100000000000110000000040100000000000e102000000000000800000000021020000000000005000000000e10300000000061010000000000012000000000210400000524c42000000000000011000000000a1000000000006104000000000000d000000000001200000000061040000002806200000005444020100000000000120000000000007000000000000a000000000000f0000000000005000000000000f0000000000011000000000001100000000121020000041504201
  | 6, 12 => 0x30000000002103000000380a201000000000000900000000000050000000000014000000000000f000000000a100000000000000500000515002030000010440200000000000a103000000000000b000000180220000000504c4201000000000610200000000061020000000085102000000000610400000000000070000000000013000000000e1040000000000001000000000000f000005150020100000000000120000000002100000000000e10000000000000130000041504200000000000a1000000000000011
  | 6, 13 => 0x500000000000120000000000013000000380a2000000000000005000000000210200000515002000000000000005000000000000400000000000050000021484200000000000000f00000000000100000000000011000000000000600000000061030000000000001000000000000500000000000050000002802201000000000210200000515002000000000006100000000000001300000000121000000000000013000000010d100000000010110900000000c911400000000000120000000000005000000000e102
  | 6, 14 => 0x210300000000000140000002806201000000000000500000000061010000000000001000000000000f0000000000005000000000000f00000000021020000053440201000000000210400000535002000000000006101000000010d1060000042508200000000000000a00000000021030000054041200000000380a200000000000001000000000021010000000000007000000000610400000000061000000000012101000000000000f000000000000a0000052440200000000000000b0000053500200000000000000f
  | 6, 15 => 0x40500201000000000a1020000000002103000000010110900000000061040000000000014000000001210000000520c52010000000000003000000480a2000000000000011000000000000500000000121000000020480201000000000000f0000000000005000000000000d000000000000d0000000006104000000000210400000000000030000000000005000000000210400000000000140000000000006000000380620100000214842000000000000005000000000000d0000000006100000000000000e0000000000012
  | 6, 16 => 0x610200000000000000000051500200000000480a200000000000e100000000000000800000534402000000000000005000000480a201000000000e102000000000000500000000000140000000000010000000000a1020000054440200000000000e1010000000006103000000380620000000048022000000000002100000000000000f00000000000060000000000005000000000a101000000000000400000405002000000000012102000000000a100000000000000f000000000000700000000061020000010440200
  | 6, 17 => 0x1100000000000030000021484200000000000e10000000000851020000000000008000000000000d0000000000009000000000001300000000000050000000000013000000000000700000000021030000000000008000000000a102000000000000f000004150420100000524402000000002802201000000010110900000000000030000052500201000000000210200000214842010000000002101000000000000800000000000070000000000000000000000000e000000000000f00000000061020000000000004
  | 6, 18 => 0x100000000002100000000000000600000000021000000000000009000000380a201000000000210400000000000110000000000014000000000a100000000000001400000000000130000021484201000000000210200000000061040000010440200000000010110900000544402000000000006100000000000000800000540812000000050105201000000000000e000000000000800000000000080000000085102000000000001100000000000080000000000005000000000000400000028062000000004806200
  | 6, 19 => 0x10d1060000000002102000000000001200000000000030000000000005000000000e1010000002802201000000000610200000000000090000010440200000000000610200000000061010000000000013000000000a101000000000001000000018022010000041504200000000000001000000214842000000000000005000000000000c0000000000004000000000001300000524c4200000002148420000000000000050000000000004000000000001300000000121030000000000010000000000000f0000000000008
  | 6, 20 => 0x10000000000000500000000000070000000006101000000000e10200000000121000000000000013000000000e10000000000061040000000000012000000000000000000000061040000004806200000000380620100000000061040000000006100000000000a1000000000000013000000480620000000000000070000000000003000000000000e00000520c52000000054041201000004250820100000000000140000000000013000004150420000000000061030000000000005000000000000f0000052440201
  | 6, 21 => 0x50000054041200000000000610000000000000080000000000009000000000001300000514c8200000000000000f00000000061040000000000005000000000a1020000000000009000004050020100000000061040000050105200000000000000700000000000140000021484200000000000000500000000000030000054041200000000000610200000000021040000000000006000000000000500000000021030000000000008000000000000800000000000000000000000008000000000000f0000000000010
  | 6, 22 => 0x61020000000006104000000000000f0000000000005000000000000000000515002030000001802200000000000a10200000000000050000000006104000000000000100000018022000000054440200000000000000800000000000130000000002102000000000000f000000000000f00000048022000000000000014000000000000900000000401000000000101109000000000001300000000000120000000006102000000000000500000000021020000000006103000000000210200000000000130000000002102
  | 6, 23 => 0x6102000000000000f00000000021020000053440201000000000000f0000000000008000000000000f000000000610200000535002010000000000005000000000001300000000000120000000006102000000010d1060000000000010000000000000300000000000030000000006103000000480a20000000001051030000000000003000000000000700000000021040000000000012000000000000f000000000210000000000021020000000006102000000000000f000000000210200000000000130000000002102
  | 6, 24 => 0x10510300000520c5200000000000000f000000000000900000000000140000041504200000000000a10300000000021030000000000007000000000210200000000000050000000002104000000000210400000000021020000004806200000000000000400000000000100000000000013000000000610000000000000100000000002103000000000210400000000851020000000000009000000000e10000000000000050000000000005000000000001200000504c8200000000000610200000000061040000000000005
  | 6, 25 => 0x900000001011090000000000005000000000001400000000000000000000101109000000480e2010000000006100000005210d200000000000001300000000121000000000000005000000000000f000000000000600000000000070000000000005000000000e1000000000000005000000010010300000000000140000000000002000000000a10000000000000120000000002104000000000001300000535002010000000002102000000280220000000000061020000000000013000000000000f0000000000005
  | 6, 26 => 0x13000000480e2000000000006100000000000000f0000053440200000000000000800000000000080000000000005000000000000800000204802000000000000013000000180220000000540412000000000006103000000000000500000000000050000000000012
  | 7, 0 => 0xc5100000000000001300000000021030000000000002000005404120100000000000020000000000010000000380a20100000000000030000000000001000000000000200000000021000000000000007000000000001400000515002010000000000002000000001210000000000000020000000002100000000000a100000000000210000000540812000000000000006000000004010000000415042010000000002103000000000000700000000c910100000000000100000002802201000000000000f0000000012100
  | 7, 1 => 0x2100000000000000200000000000000000000000001000000000610400000038022010000000000001000000000000f000000000a1040000000000004000000000000d000000000610400000000000010000000000003000000000a100000000000210300000000061000000000000002000000010d1010000000000009000000000000400000000021020000000002103000000000000f00000000851000000000000010000000000000b0000000101101000000000e102000000000000900000000121000000000002102
  | 7, 2 => 0x1210000000000000130000000000011000000000a102000000000e1000000000000004000000000000900000000000020000000000011000000000000500000000000020000000002102000000008110000000000000020000000006103000000000a100000000000e10200000000000010000000041100000000010410100000000000140000002802200000000000a103000000000610200000000000120000000000002000000008410000000001041000000000000001000000000000600000524402010000000012100
  | 7, 3 => 0xc51000000054440200000000000000200000000000050000000000004000000010010100000000000140000000081101000000000001300000000000050000000000008000000001210100000000411010000000006100000000000610300000000000030000000000006000000000001200000000000050000000000000000000480220000000540412000000000081100000000000000a00000000021010000010440201000000000000f0000000002104000000000a101000000000000200000000000050000000000002
  | 7, 4 => 0x60000000104101000000000000400000000021010000053500201000000000a1030000000000005000000010110000000000000000000000000001000000000000500000000021000000000002100000000000e1010000000000009000000010510100000000061030000000000009000000000000200000000021000000000000001000000000000d000000000a101000000001210100000000061010000000000004000000000000700000000000110000000012101000000000a10000000000000020000000006101
  | 7, 5 => 0x61000000000012103000000000610200000000000020000000002102000000000a101000000000e10100000000000010000051500201000000000000a0000000000003000000000001200000000000090000000000006000000000210100000000000010000000000013000000000000800000018022000000000000001000000000a1000000000085102000000010810000000000000100000002806201000000000e1030000000000003000000000e1000000000000009000000000000300000000021010000000000009
  | 7, 6 => 0xa1000000000040101000000380620100000000000040000000100103000000000001100000000000100000000000000000000000001200000000000040000000080100000005404120000000000061010000000000008000005408120100000000021000000004806201000000380620000000000000130000000040101000000000001400000000000060000000000014000000000000800000000000070000000100100000000000001200000000061040000000000003000000000000300000000000020000000040101
  | 7, 7 => 0x13000000000000400000000121010000000002100000000000000100000000021000000000000005000000000e1020000000012100000000000000300000000021000000000085101000000004010100000000401000000000000006000000000000500000000000070000000002104000000000e10100000000c0100000000000e100000000010510100000000061020000000000000000000000000c0000000000004000000000000f0000000000006000000000000300000000000030000000000003
  | 7, 8 => 0x400000000000050000000000006000000000001100000000000020000000105100000000000000200000000000000000000000000000002048020100000000061010000000000004000000000000200000000021030000000000001000000000a100000000000000900000000000070000000085101000000000000300000000121000000000002100000000000000800000000000140000000000005000000180220100000000000050000000000005000000000a101000000010510000000000000020000000002102
  | 7, 9 => 0x700000000000050000000000011000000000000500000000000070000000000000000000000e10300000001091010000002806201000000004010000000000121000000003802200000000000000100000000121010000000000001000000000000500000000000070000000085102000000000000300000000021010000000000003000000000a10000000000000130000000000004000000000001200000000021000000000105101000000000000300000000000130000021484200000000000a1010000000000003
  | 7, 10 => 0x600000000801000000000000002000000001210300000001001010000000000000000000000210000000000000000000000000006000000000000f00000000000000000001802201000000000000400000000000010000000000013000000000000400000001001000000000000003000000000000100000000000060000000000012000000010d1010000000002104000000000000400000038062000000000000002000000000000f00000048022010000000000012000000000000100000001081010000000000006
  | 7, 11 => 0x7000000000001000000000000010000000000011000000000a104000000000001100000000061000000000108101000000380a201000000000000d000000010410000000000000040000000000013000000000000500000000000050000000000005000000000000600000000000020000000000001000000000a1000000000000003000000000001300000000000130000000000001000000010d1010000002802201000000000000400000000021040000000000002000000000e1030000000000002000000000000d
  | 7, 12 => 0x130000000002102000000000a1040000000000012000000000000700000000000050000000000006000000000000800000000021030000001802200000000000000200000000000130000003802201000000000000a00000000000080000000104100000000000000b0000053500201000000000a1000000000000004000000000000d0000000000005000000000000d0000000100100000000000000000000000121000000000000006000000000210400000000000110000000000009000000000e1010000053440201
  | 7, 13 => 0x13000000000a1000000000000000000000000210200000000000040000000002103000000480a2000000000000005000000000000e00000000061010000000100100000000008410000000000000070000000000000000000000000a000000000000700000000851010000000000003000000000000200000000811000000000000002000000000001300000540412000000000000009000000000000300000000000000000000000003000000000001300000000000020000000012100000000000000e0000020480200
  | 7, 14 => 0x400000000000020000000000001000000008410100000000061000000000000007000000000000300000000021000000000000014000000000a100000000000000800000000000040000000006103000000000001100000000121010000000000002000000000a103000000000000900000000000100000000002104000000000000300000000000010000000000010000000000e1000000000000006000000000001300000000c410000000000000080000000000007000000000610200000000000000000000000009
  | 7, 15 => 0x6000000000001000000000000030000000006100000000008010000000000000140000000002102000000000000400000000000000000000012100000000008110000000000121030000000000009000000008110100000000000080000000000004000000000000a000000000e10200000000000030000000000005000000000000400000000000000000000006101000000008110100000000000110000000002100000000000001400000000000070000000000005000000000001100000000000030000000006101
  | 7, 16 => 0x610400000000000060000000006101000000000000300000001091010000000040100000000000000100000000000040000000000013000000000000500000000000020000000000011000005250020100000000000020000000000004000000000610100000000021020000000000014000000000000a000000000000b0000000000002000000000210100000000000020000000000005000000001210200000000c51000000000000003000000000000f0000000006103000000000000800000000021000000000000005
  | 7, 17 => 0x30000000000007000000000000e0000000002100000000000a10000000000000000000000000004000000000000a00000000000090000000000010000000000e104000000001210000000000000080000000006100000000000001300000000000000000000000011000000000000f00000000000030000021484200000000000000a00000000000100000000000002000000000e1010000000000002000000480a2000000000000007000000000a1010000000002100000000000610300000000000050000000000012
  | 7, 18 => 0x130000000006100000000000a102000000000000b0000000000002000000000000200000000000050000000000005000000000000f00000000000070000000000008000000000610100000000000120000000000001000000000210100000000000070000000000003000000000a1040000000000001000000000000d000000000000000000000000050000000000007000000000610300000000021010000000085102000000000e101000000000000600000000000090000000081100000000000a1000000000012101
  | 7, 19 => 0x6101000000000000400000000121010000052500200000000000a10100000000121000000000000001000000000000200000000000100000000080100000000000001000000028062010000000000000000000000000300000000c1100000000000001300000000021020000000000001000000001210100000000021020000000104101000000000000400000000000050000000002101000000000a103000000000000500000000061030000000000002000000000000600000000000000000000012103000000000000f
  | 7, 20 => 0x10440200000000000000100000000000060000000000000000000000000200000000000040000000000007000000000610000000204802010000000000002000000000000400000000401010000000084101000000000000e000000010d1000000001802201000000000e10000000000000040000000000002000000000610300000001051000000000000001000000000a100000000000001100000000000030000000000010000000000a10100000000021030000000000005000000000000200000000000070000000084101
  | 7, 21 => 0xa100000000000001100000000000040000000085100000000000e10100000415042000000000000005000000000000700000000000020000000000004000000000610300000000000020000000000004000000001210300000000000030000000000000000000000e1010000000000005000000000210300000000000030000000000013000000000000e000000000000f00000000000070000003806201000000000001300000001041000000000000005000000000a101000000000000600000000000020000000000000
  | 7, 22 => 0x2101000000000a10400000000000040000000000002000000000000700000000000090000000000005000000000210100000000000000000000000000000000000000700000000000030000000002100000000000000800000000000010000000000002000000000000700000000061000000000000004000000000210100000000c5100000005344020000000000121010000000000011000000001210000000000000090000000041100000000000e103000005344020100000000000040000000002100000000000000f
  | 7, 23 => 0x200000000000130000000012100000000000000d000000010d10000000000000050000000000003000001044020100000000000090000000002101000000000000a000000000210000000000000090000000000007000000000a1000000000002101000000000000300000000000130000000000006000000000000500000000000040000000006100000000000000f0000000000013000000000000100000000000040000000000002000000000a1020000000000003000000000000f00000001041000000000002100
  | 7, 24 => 0x1200000000000020000000002103000000000000f000000000a101000000000000a0000000000004000000480220100000000000000000000012102000000000e101000000000000700000534402010000000000003000000000000f00000000000020000000109100000000000000e00000000c4101000000000000d000000000000f0000000000005000000000610200000000000080000000000007000000000000400000000c410000000000121000000000006102000000000000a0000000006100
  | 7, 25 => 0xa102000000000e10000000001041000000000000007000000000210000000000000090000000000013000000000000800000000121010000000006101000000000000a0000000000007000000000a100000000000000000000000000090000000012101000000000000b0000000002103000000000610400000000c5101000000000000100000204802000000000000002000000000000d000000000a1020000054440201000000000000300000000000080000000002100000000000000500000000000100000000000005
  | 7, 26 => 0x300000000c510100000000000030000000000013000000000000000000000000030000000000009000000000a101000000000210000000000000010000000000012000000000000f00000000000130000000104100000000004110000000000000070000000000001000000000a10300000535002010000000000003000000000000c000000000000f0000000000003000000000000300000028062010000051500200000000000000500000048062000000000006101000000010410000000000000000000000000014
  | 7, 27 => 0x500000000000050000000000014000000000000700000000000030000021484201000000000000200000001001010000000080100000000380620100000000021020000010440200000000000000f0000000000014000000010510100000000000000000000000004000000000000000000000021010000000012102000000000000200000524402000000000000003000000010510000000000000050000000000000000000000e10200000000000020000000002100000000000000700000000061000000000000000
  | 7, 28 => 0x6000000000a1020000000000006000000000000e00000000000140000000002102000000000a10000000000000130000000109100000000000610000000000c51010000000006102000005150020100000001001010000000000014000000000000e0000000000008000000000000400000524402010000000085100000000000000400000000000020000052500201000000000000200000000000050000000012102000000000000400000000000060000000000008000000000e10100000000000020000000000009
  | 7, 29 => 0x1210000000524402010000050105201000000000a1000000000012103000000010d10000000000000000000000000004000000000a100000000010d101000000000000000000000000050000000000012000000000000700000000000090000000000004000000000e102000000000e10300000000c51000000000000006000000000e100000000000000200000000401000000000000002000000000000200000000000060000000002100000000000210300000000000020000000012103000000000000f000000000e103
  | 7, 30 => 0x7000000000000d00000000000010000000000002000000000000300000000000050000000000005000000280220000000000000020000000012102000000010910000000000000080000000000006000000000000f000000000000f0000000012103000000000610300000000000060000000040100000000000a10100000000c510000000000000040000000000003000000000610100000000c91000000000000004000000000a100000005444020100000000000060000000000001000000000000a0000000000003
  | 7, 31 => 0x10d10000000000000030000000006100000000000000f0000000000004000000000000200000000061000000000085100000000008110100000000000120000000000010000000000000d000000000000500000000000100000000000009000000000000d000002048020000000425082010000000000010000000010910000000000000000000000002100000000000000400000000121020000000006103000000000000900000000061030000000000004000000000e1000000000000010000000000000d0000000000003
  | 7, 32 => 0x800000000000050000000000001000000000000e000000000a103000000000000a000000000001200000000000110000054440201000000000000200000000021040000000000006000000000e102000000000e103000000000000000000000851000000000012101000000000000900000214842000000000000008000000000000800000000000050000000000002000000000610000000001001030000000000014000000000000400000000000090000000100101000000480220100000000000070000000002102
  | 7, 33 => 0x13000000001210100000000000100000000002101000000000210000000000000130000000000002000000000000b00000540412000000000002102000000000e1000000000000004000000000a10100000000061000000000000000000000000610300000000021030000000002104000000000000600000000000040000000002101000000000a101000000000a101000000000a10100000000061010000000006102000000000000400000000000040000000000004000000480a20000000000000050000000000000
  | 7, 34 => 0x52500201000000000001300000000c0101000000000e10100000000000020000000000003000000008510000000000000020000000012102000000000000e0000000080100000000000000f000000000610100000000000090000000000003000000000e1010000000000000000000000e10100000000000140000000012103000000000000c000000000000f0000000006103000000000001000000000021000000000000014000000000000000000000c5100000000000000f000000010d1010000000000004000000000000b
  | 7, 35 => 0x21000000000012101000000000000f00000000000020000000000002000000000e1030000000000008000000000000c00000000061020000000000013000000000e10200000000000070000000000004000000000000200000000021030000000000001000000000001100000000000010000000000005000000000e1000000000000002000000000000200000000000050000000000011000000000000500000000000040000000006102000000000000000000000000020000000000002000000000a103000000000000f
  | 7, 36 => 0x12102000000000a101000000000a1020000040500200000000000000600000000000140000000000008000000000000600000000121020000000084100000000000000800000000000060000000000004000000000e103000000000610200000000000040000000006101000000000000200000000411000000000105103000000000001000000000000030000000000002000000000000800000000851000000000000008000000000a100000000000a100000000000a102000000000000400000000021010000010440201
  | 7, 37 => 0x3000000000e100000000004110100000000000020000000000004000000001210300000000061000000000101100000000000a100000000000000c00000000000000000000006104000000000000c00000000061000000000002100000000000610300000000000070000000000007000000000000600000000121020000000000002000000000000c0000000000009000000000000900000001081010000000000010000000000000100000000000060000000000008000000000000700000000000040000000000006
  | 7, 38 => 0x105100000000000000200000000061020000000006100000000000a1020000000000005000000380a201000000000000400000000000050000000085102000000000000d00000000021000000000000009000000000a103000000000000200000000021010000000000007000000000000b000000000000900000000000020000000000003000000001210000000000000020000000000004000000000e1000000000000013000000000000700000000000020000000000009000000000001300000000000040000000000013
  | 7, 39 => 0xf00000000061030000000100101000000000000e0000021484201000000000a100000000010010100000000000040000000000002000000000e1000000000000008000000000000400000000000100000000000003000000000001000000000000140000000006101000000000001000000000000060000000085102000000000e104000000000000a00000000021010000000000011000000000e10000000000121010000000006100000000000a1010000040500201000000000000f00000000801010000000000003
  | 7, 40 => 0x12100000000000e10300000000000020000000000002000000000000f000000000000f0000000000008000005150020100000000000000000000000002000000004110000000000000050000000000008000000000e10100000000000020000000040101000000000a102000000000e103000000000000300000000000050000000002101000000000001300000000401000000000000000000000480e200000000000210400000000c91070000000000000000000004010000000000000100000000000001000000000a102
  | 7, 41 => 0x40000000006101000000000e10300000000021020000000000005000000000000200000524402010000000000012000000000000f0000000000008000000000000f0000000000003000000000000400000000000020000000000001000000000000400000000121020000000002104000000000000d00000000000060000000000009000000010910000000000000120000000002102000000000000f0000000000005000000000000900000000411010000000000004000000000000f00000000000050000000105100
  | 7, 42 => 0xe10200000000000010000000000014000004250820100000000000010000000000003000000000000300000000000000000000000003000000000000200000000021030000000000005000001044020000000000000130000000000004000000000a104000000000000800000000000130000000000008000000000e100000000480a200000000000610100000000000020000000006102000000000a10400000000000030000000000010000004150420100000000c1101000000000610100000000061010000000006101
  | 7, 43 => 0x4000000000a1010000000000001000000000e10200000000000020000000000002000000000000d000000000000400000000000090000000006103000000008410100000000000070000000000013000000000e1040000000002103000000000a10000000001001010000000000002000000000a100000000000610300000000000010000000000014000000000a1000000000101100000000000000e000000000210000000000c510100000000000060000000040100000000001210200000000021030000000000010
  | 7, 44 => 0x6104000000480220100000000000020000000000008000000000000f00000000000040000000000000000000000000a000000000000f000000000000200000000c1100000000000001400000000000000000000000005000000000e10200000000000110000000080100000000000a10000000000061020000000000010000000000001300000000000130000000002102000000000000200000000c11010000000012101000000000000300000000000000000000000000000000000001000000000000130000000000001
  | 7, 45 => 0xd0000000000003000000000000600000000061010000000000009000000000610200000000121020000000000002000000000001000000000000090000002802200000000000001100000000000140000054440201000000000000900000000000020000000000006000000000000600000000121000000000000006000000000001300000000000100000000000000000000000000400000000000000000000000008000000000000f00000000061000000000006100000000000610200000000000060000000000011
  | 7, 46 => 0x6101000000000001000000000000080000000100103000000000e102000000000000300000000061040000000000004000000000000f0000000084100000000000001400000000000030000000002102000000000e100000000000000300000000000040000000006100000000000a100000000000000f000000280620100000000000040000000000009000000000000f0000000000003000000480e2000000000000013000000000a1000000000000002000000000000a000000000000b000000000000e000000000a100
  | 7, 47 => 0x800000524402000000000006103000000000000f000000000000b000000480a20100000000000040000000000002000000004110000000000000000000000006102000000000000100000000c910100000000c910000000000000080000000012102000000000000d00000000000020000000006101000000001210300000000000070000000000009000000380a20000000000000020000000002104000005408120100000000000010000000000000000000000210200000000000090000000000009000000000e104
  | 7, 48 => 0xc000000000a1040000000000006000000000610200000000000120000000006103000000480e20100000001011090000000000010000000000000300000000851010000000006102000000000000f00000000000030000000006100000000000000200000000000090000000002101000000000001400000000c91010000041504201000000000001000000000000000000000006103000000000210300000000000010000000000000000000001210000000000c1100000000000000900000000000130000000085102
  | 7, 49 => 0x40000040500201000000000000d000000000a1030000000000002000000000000200000000000030000000100100000000380a201000000000e104000000000e1020000000000011000000000000600000000000030000000000008000000000000f000000000000f0000000000004000000000000500000000000080000000000005000000000000200000000000020000000000005000000000a1040000000000003000000000000600000000000140000000000003000000000610300000000121010000000000013
  | 7, 50 => 0x2000000000000300000000000130000000002101000000000000f0000000000002000000000000d000000000e1030000000000009000000010d1000000000002104000000000000400000000000000000004806200000000000a102000000000e104000000010110000000000061040000000000005000000000000b000000000000200000000000030000000000013000000001210100000000000040000000101101000000001210000000000000110000000080100000000000000600000000000010000000002103
  | 7, 51 => 0xe10100000000c010100000000061010000000002100000005404120100000000c4100000000001210000000000801010000000000002000005350020100000000000080000000000001000000000e1030000000006100000000000610000000000c1101000000000000900000000000130000000000010000000000a100000000000610400000001051000000042508200000000000a1030000000000005000000000001000000000000070000000002101000000000000a000000000000300000000021020000000002100
  | 7, 52 => 0x90000000000003000000000a10400000000000080000000000002000000000610200000000000030000000000002000000000000f0000000000005000000000000d0000000000008000000000000b000000001210000000000000120000000000005000000004110100000000000080000003802200000000001210000000000000100000000000000000000000a10000000000000130000000000004000000000000d000000000000900000000061010000000002102000000000e10400000000000040000000000010
  | 7, 53 => 0x280220000000000021030000000006100000000000000f00000000000030000000000003000000010410000000000000020000000006104000000001210200000000000020000000085101000000000001300000000000030000000000000000000000e101000000000000900000000000070000000012100000000010510000000000121020000000000007000000000000200000000c510000000000000120000000000005000000000000600000000000040000000012101000000000610000000000000060000000000002
  | 7, 54 => 0x1000000000000060000000000000000000010010100000000121010000000000002000000000000400000000000120000000000007000000000001200000000021020000000006102000000000e1010000000000000000000000001100000000000070000000000010000000000000200000000061020000000000006000000000610000000000000030000000000002000000000610200000000000000000000000009000000000000500000000061000000000000008000000000610000000000000020000000000002
  | 7, 55 => 0x800000000121000000000012101000000000000400000000000030000000000003000000000000900000000c51000000000006102000000000e1010000000108100000000000000d000000000000900000048062010000000000009000000000a10200000000000130000000000003000000000000f0000000002103000000000000200000000000030000000000013000000380620000000001011000000000012100000000000000800000000000020000000012100000000000000900000001001030000000000009
  | 7, 56 => 0x13000000000001300000000000110000000000012000000008110100000535002000000000000008000000001210200000000000000000000000008000000001210200000000000110000000000005000000000000100000000000100000000002100000000000e101000000000000800000028062010000000000003000000000610400000000000020000000000014000000000000200000000000000000000000013000000000000100000000c9100000000000000200000000000020000000002102000000000000f
  | 7, 57 => 0x2000000000000900000000061000000053500200000000000000e0000000000013000000000000500000000000020000000000002000000000000d000000000000800000000841000000000000002000000000a10000000000000090000000108100000000000001300000000061030000000000009000004250820100000038022000000000000000000000001210100000540412010000000002103000000000000300000000000020000000104100000000000a100000000000000700000540812010000000006104
  | 7, 58 => 0x1000000000210000000000000090000000000001000000000000f00000000000040000000000005000000000000600000000061030000000000002000000000000a000000000000000000000000020000000040100000000000000900000000000130000000000013000000000000500000000000020000000000008000000000e10100000000061030000000002103000000000610400000000021020000000006102000000000a10100000000000050000000000007000000000610200000000061030000000000000
  | 7, 59 => 0x5000000000610100000000000020000000000013000000000000000000000000060000000084100000000000000800000000000050000000006100000000000000f0000000006102000000000e100000000008510000000000000010000000002102000000001210000000000000040000000000010000000008410000000000000060000000000001000000000001300000000000140000000000003000000480a201000000000000c00000000000000000000000005000000000610000000000000050000000000006
  | 7, 60 => 0x2000000000000400000001011010000000000008000000000000200000000000140000000000003000000000a100000000000000500000000000050000000000013000000000001300000001091000000000000013000000000000400000000000040000000000002000000000e103000000480e2010000000002103000000000000200000000000100000000000008000000000001200000000061010000000109100000000000000300000000061020000000000009000000000000500000000000020000000002101
  | 7, 61 => 0x600000000000130000000002102000000000000800000000000050000000000002000000000000400000000000120000000000014000000000000500000000000090000000006101000000000000800000534402000000000000005000000000a10100000000851020000000000003000000010d10000000000000040000000000005000000000000500000000000090000020480200000000000000e00000000021000000001802200000000000000a0000000000011000000000001000000000000030000000000013
  | 7, 62 => 0x210400000000000030000000000007000000000210300000000000050000000000008000000000001000000000c51010000000000000000000001210000000000000030000000002100000000000000200000000000030000000000014000000000a10100000000000020000000000009000000000610200000415042000000000006102000000000000200000000000020000000002102000000001210200000000000010000000000005000000000000300000000000050000000000008000000000a1020000000002100
  | 7, 63 => 0xa102000000000000200000000061000000000000003000000000610000000000000030000000000012000000004010000000000000050000000012103000000000210000000000c91010000000000009000000008510100000000841000000000000006000000000e1030000000012101000000000000300000001051010000000000010000000000a100000000000000500000000000060000000012102000000000000000000000401010000000000009000000010d100000000000001100000000061030000000000003
  | 7, 64 => 0x6101000000000000d0000000002100000000000000f000000000000200000000021000000000000008000000008010000000000000100000000006100000000480e200000000000210100000000061010000000000013000000000001300000001001000000000000002000000000000700000000c510100000000000020000000006100000000000000700000000000050000000000014000005408120000000001051010000000000009000000000000e0000000000008000000000e10000000000000080000000000005
  | 7, 65 => 0x2000000000000500000000000050000000000002000000000610300000000021000000000000007000000480620100000000000010000000000004000000000000300000000c910000000000000050000004802201000000000000900000000000020000000002104000000000a1000000000002104000000000000800000000021020000000000004000000000a100000000000000200000000000030000000000011000000000000a00000000000140000000000005000000000000f00000000021040000000080101
  | 7, 66 => 0x9000000010d1010000000000009000000000210000000000061000000000002102000000000001300000048022010000000002101000000000a101000000000a1000000000000002000000000000f000000480e200000000000210200000000000050000000000004000000000001300000000021020000000000008000000000000200000000000080000000000003000005250020000000000000130000000000004000000000001000000000000070000054440201000000000000400000534402000000000002102
  | 7, 67 => 0x14000000000e1020000000000002000000000001300000000021030000000000009000000000001000000000000030000000100101000000000000800000000000020000000000002000000000000300000000061010000000000000000000000000500000000000040000000000002000000000000500000000061020000000012100000000000001000000540812000000000012100000000000610100000000000030000000000009000000000000600000000000130000000006103000000000a1020000000000004
  | 7, 68 => 0x2000000000000800000000000030000000000004000000000610000000000061000000000000007000000000000100000000000060000000000003000000000000200000000000030000000000006000000000000700000000000030000000108100000000000000a000000001210100000000000020000000000008000000000000500000000000020000000080100000000000610300000000000080000000000007000000000000700000000000030000000006102000000000001000000028022010000000002101
  | 7, 69 => 0x6102000000000610000000000000050000000085101000000000000300000000061000000000002103000000000210100000000000080000000000008000000000610000000000000080000000006102000000000000600000000851010000000105103000000000000500000000000040000000006102000000000000800000000021010000000000000000000001210100000000021000000000000010000000000001200000000000040000000000007000000000000a000000000000900000000000050000000000003
  | 7, 70 => 0x61020000000002103000000001210000000000000070000000000002000001044020000000000000040000000000011000000000000500000000021020000000000005000000000000200000000000020000000002104000004050020100000000000120000000006101000000000000400000000000050000000000009000000000210400000000061040000000000003000000000000200000000021040000000000002000000000000500000000000020000040500200000000000001300000000000050000004806201
  | 7, 71 => 0x20000000000010000000000000d00000000000030000000000013000000000000400000000000050000000000008000000000000e0000000000003000000001210200000000121030000054440201000000000a10000000000000130000000006100000000000000400000000000050000000002100000000000001300000000000060000000000008000000000000800000000000070000000000004000000000000f000000000610100000000061000000000000007000000000610100000000000060000000000007
  | 7, 72 => 0x210400000000000050000000006104000000000000700000000000020000000002102000000000000c0000000000007000000000000300000000000070000000006100000000000000700000000000050000000000006000000280220100000000851000000000002102000000000000100000000000060000000000004000000010d10100000000000030000000000004000000000000400000000851010000000000004000000000000200000000121000000000000002000000000210300000000000040000000000000
  | 7, 73 => 0x2000000000001100000000000080000000105103000000010d101000005150020000000000000050000000000004000000000e101000000000610000000000000090000000104100000000000000f0000054440201000000008110000000000000060000000000005000000000000900000000000040000000000011000002148420000000000000030000000000000000000008410100000000000080000000002101000000480220100000000000050000000000006000000000000200000001051030000000000006
  | 7, 74 => 0x380220000000000000130000000012100000000000000200000000c41000000000040100000000000e103000000000000200000000000000000000000004000000008510200000000000080000000000010000000000e1010000000012100000000000e1010000000000006000000000210100000524402000000000084100000000000000500000000061030000000000008000002048020100000000000000000000000013000000000000400000000000050000000000008000000000000300000000000030000001802201
  | 7, 75 => 0x415042010000000104100000000000000f0000000040101000000000000600000000061030000000000004000000000000400000000000040000000000008000000000610400000000c0100000000000001300000000000130000000002100000000000000000000000000050000000000013000000000e1010000000000008000000000000500000000000060000000000002000005350020000000000000010000000000004000000000000700000425082000000000000003000000000000300000534402000000000000013
  | 7, 76 => 0x2000000000610000000000000110000000000010000000000000f000000000610300000000000020000000000013000000008510100000000000020000000000001000000000000300000000000090000000000005000000000210100000000411000000000105101000000000000600000000000070000000000004000000000000600000000000020000000000013000000000001000000000061040000000000013000000000000900000000000020000000000010000000000000700000000000120000000000013
  | 7, 77 => 0x200000000841000000000000004000000000000300000000811010000000000005000000000210000000000000030000000000004000000000000500000000061020000000000006000000000000f000000000000500000001041000000000012103000000380a200000000000000700000000411010000000000001000000000000f000000000000000000000c910000000000000140000000000003000000010d101000000004010100000000021030000000000005000000000000500000000061030000000000003
  | 7, 78 => 0xd00000000000070000000000002000000000000200000000000080000000000003000000000000f000000000000f000000000210000000000021020000000000005000000001210100000000061020000000000006000000008510000000000000040000000000002000000000000f000000000610200000000000030000000000004000000000000600000000121030000000000004000005250020100000000000050000000000006000000000000f00000000000090000004806201000000000e1000000000000006
  | 7, 79 => 0x21030000000000004000000000000200000000811000000000012100000000000000300000000000080000000000005000000000000500000000000070000000000003000000000000400000000000060000000000008000000000000400000000000080000040500200000000000000500000000000050000000000004000000000000700000000000010000000000009000000000610400000000000070000000000014000000000000c00000000000090000000000009000000000000900000001051030000000000004
  | 7, 80 => 0x6000000000001400000000000050000000085100000000000000f000000000000300000000000040000000000000000000000e1000000000000002000000000000f0000000000010000000000000700000000000040000000000007000000000e101000000000000900000000000020000000000000000000000000800000000000060000000012103000000000610100000000000020000000000005000000000000200000000000130000000000014000000010910000000000000070000000000002
  | 7, 81 => 0x5000000000e100000000000a1000000000000004000000000e1000000000000004000000000610200000000121030000000002100000000000000500000000000000000000000013000000000000f0000000000004000000000000300000000061040000000000013000000000a10200000001051030000000000002000000000000c00000000121010000000000004000000000000700000000000080000004806201000000000000400000000000020000000006103000000000000200000000000030000000000013
  | 7, 82 => 0x3000000010d106000000000000400000000021040000000006101000000000000400000000000050000000000008000000000001300000000000040000000000005000000000000f000000000a1010000041504201000000000000600000000000070000000000005000000000000600000000000020000000000005000000000000400000000000040000000000008000000000001400000000000040000000002102000000000210000000000000090000000000002000000010d10000000000000020000010440201
  | 7, 83 => 0x1000000004010100000000021020000000000004000000000e1000000000000007000000000000500000000000050000000000013000000000000f0000000000006000000280620000000000061030000000000009000000000000f00000000061020000000000006000000000000800000000000040000000000002000000000000200000000000040000000000000000000000a102000000000000600000000000090000000000009000000000000f0000000000010000000000000200000000000020000000000004
  | 7, 84 => 0x21030000000002103000005244020100000000000020000000006102000000000000300000000000050000000000003000000000001300000515002010000000000002000000000001300000000000100000000000008000000000000500000000000010000000100100000000000000200000000000050000021484201000000000a1020000000000006000005408120000000000000090000000100103000000000210100000000061020000000000002000000000a100000000000001000000000000030000000000013
  | 7, 85 => 0x6000000000000800000000c910100000000121010000000000003000000000210200000000021040000000006102000000000000f0000000108100000000000210100000000000080000000000002000000000001400000000c5100000000000000c000000000001300000000000140000042508201000000000000400000000000130000000041101000000000000000000000000030000000000008000000004110000000000c110100000000000050000000000013000000000000400000000061000000000000002
  | 7, 86 => 0x2102000000000001000000000061020000000000006000000000000200000000061010000000000002000000000000700000000000010000000000007000000000000800000000000060000000000014000000000000500000000021030000000000004000000000000f0000000000002000000000000f0000000000003000000000000400000000000040000000000009000000000000c00000000000050000000000004000000000610300000000000050000000002100000000000000200000000000100000000000002
  | 7, 87 => 0x80000000000006000000001210300000000021020000000000003000000000000300000000021010000000000002000000000000000000000000070000001802201000000000000f0000000000008000000010010300000000021020000000006102000000000000f000000000000300000000000100000000000008000000000001300000000000060000000000001000000010810000000000000070000000000013000000000a10200000000061030000000000002000000000210200000000000050000000000002
  | 7, 88 => 0x70000000000008000000000000400000000000010000000000002000000000210200000000000090000000000013000000000000200000000000070000000000003000000000610300000000000090000000002102000000000000f00000000000040000000000013000000000610300000000000050000000000013000000000000400000000000090000000000014000000000000100000000061020000000002103000000000000300000000000070000000000007000000000210300000000000080000000000013
  | 7, 89 => 0x2102000000001210000000000411000000000000005000000000610400000000000020000000000006000000000000f0000000085102000000000a10200000000000030000000006102000000000000400000000c910100000000000080000000000006000000000000400000000000130000000000007000000000210300000000000050000000000008000000000000200000000000020000000000007000000000e100000000000000800000000121000000000000003000000000001000000000000040000040500201
  | 7, 90 => 0x50000000000014000000000000700000000000050000000006102000000000210200000000000020000000000002000000000610200000000000100000000000009000000000a102000000000000f00000000021030000000000005000000000000600000000000030000000006102000000000000900000000000080000000002103000000000000700000000061040000000000000000000000000200000000000040000000000005000000000000f0000000006104000000000000400000000000020000000000007
  | 7, 91 => 0x2000000000000f00000000121030000000000004000000000210400000000000080000000000008000000000000600000000000040000000000004000000000000700000000000010000002806201000000000000600000000121030000000000000000000000000200000000c110000000000000060000000000006000000000000200000000021020000000000001000000000000900000000000050000000085102000000000000200000000000020000000000010000000000000400000000000080000000002102
  | 7, 92 => 0x200000000000090000000000013000000000210300000000000090000000000003000000000000400000000000130000000000002
  | 8, 0 => 0x1000000000000060000000006101000000000000f0000000041101000000000000000000000000070000000000002000000000000000000000000030000000012100000000000000300000000811000000000000000000000000000100000000c5101000000000000400000000000070000000100101000000000000200000000000010000000104100000000000000400000000411000000000012101000000000a101000000000000400000000000020000000000000000000000000000000000000040000000000000
  | 8, 1 => 0x100000000000020000000000001000000000000100000001051010000000081100000000000001000000000000010000000000000000000000000300000000000040000000000000000000004110000000000000100000000000003000000010d1000000000000000000000000000300000000000010000000000009000000008010100000000000010000000000013000000010d1000000000006101000000000000c000000010910000000000000030000000012100000000000000200000000841010000000000004
  | 8, 2 => 0x121010000000080101000000000000200000000000000000000000001000000000000100000000000030000000000010000000010d1000000000101100000000000610100000000401010000000000002000000008110000000000c91010000000000002000000000000f00000000000140000000000002000000000000300000000000010000000000003000000000000000000000000030000000000004000000000000700000000c110100000000000000000000000004000000000210100000000000020000000000002
  | 8, 3 => 0x2000000000000600000000000040000000000009000000000001300000000c51010000000104100000000000000300000000c110100000000021000000000000002000000000000100000000411010000000105100000000000000000000000000100000000000002000000000000000000000000020000000000000000000000000200000000000090000000000004000000000000000000001011010000000000003000000000000400000000000030000000000003000000000000300000000851010000000002100
  | 8, 4 => 0x20000000000000000000000000600000001041010000000000002000000000a1000000000000013000000000000f00000000000010000000000002000000010010000000000000030000000000003000000000a1000000000000004000000000001000000000000010000000000001000000000000200000001011000000000084101000000000000100000000c91010000000000001000000000000100000000000020000000000005000000010810000000000000030000000105101
  | 8, 5 => 0xa1000000000084100000000000000000000000801010000000101101000000000000200000000000030000000000005000000000000200000000000030000000000010000000000000f0000000000003000000000000200000001091010000000000000000000000001200000000000010000000000003000000000000100000000000030000000000002000000000e1010000000080101000000010d1010000000000004000000000a10100000000000010000000000002000000000000200000000061000000000105100
  | 8, 6 => 0x90000000000007000000000000f00000000000030000000000002000000000001300000000061000000000100101000000000000100000001051010000000000002000000000000100000000c1100000000000000000000000000000000000000010000000000000000000000c510100000000000020000000000009000000008510000000000000020000000000000000000010410100000000000130000000012100000000000000400000000000070000000000000000000000000200000000000090000000000007
  | 8, 7 => 0x40100000000000000800000000000040000000000004000000010d10100000000021010000000000001000000000a10100000000000040000000000003000000000a1000000000000003000000000000800000000000080000000012101000000000000900000001091000000000000006000000000e100000000000000800000000021000000000000000000000010910100000000000000000000006101000000000000200000000000000000000000000000000000000000000000c910100000000000040000000000009
  | 8, 8 => 0x41100000000000000900000000000050000000000004000000000000200000000000010000000085101000000000000300000000000000000000000002000000000000100000000000080000000000000000000004010100000000000130000000108101000000000000600000000000070000000000004000000000210100000000000070000000000001000000000001000000000000020000000085100000000000000300000000000060000000081100000000000000300000000c51000000000000003000000000e101
  | 8, 9 => 0x9000000000000c0000000000001000000010910100000000000000000000100100000000000000400000000000000000000000002000000008410100000001081010000000000003000000000a100000000000000100000000000000000000000003000000000610100000000000090000000000013000000000000300000000000020000000000002000000000000600000000c510000000000000060000000000005000000010410100000000000040000000002100000000000000200000000000050000000000004
  | 8, 10 => 0x300000000000020000000000007000000000000000000000851010000000000004000000000000700000000000010000000000002000000000000100000000000090000000040101000000000000f000000000000300000000000000000000000009000000000000c000000000000100000000000070000000000003000000001210100000000000090000000006100000000000000300000000000050000000002101000000000001000000000000010000000000004000000000000200000000000000000000000001
  | 8, 11 => 0x200000000000050000000000014000000004010000000000000000000000012100000000008110100000000841010000000000004000000000000100000000000000000000000002000000000000300000000c1100000000000000000000000000040000000000001000000000000600000000121010000000000002000000000001400000000000060000000000001000000010110000000000000000000000000004000000000000600000000c11000000000080101000000000001300000000000040000000000003
  | 8, 12 => 0x4000000000a10100000000000040000000000004000000010d1000000000000014000000000000400000000000130000000081101000000001210100000000c91000000000000003000000000000600000000021010000000000009000000000000000000000c110000000000000000000000000004000000000000700000000000030000000041100000000000001300000000000010000000000000000000000000600000000000060000000000003000000010810100000000c910100000000000060000000000002
  | 8, 13 => 0x300000000000090000000000011000000000a10100000000000070000000000004000000000000500000001011000000000000004000000000000200000000000020000000000004000000000a100000000000000300000000000010000000000002000000001210100000000021010000000104101000000000000400000000000020000000006101000000000000f0000000000003000000000000400000000000000000000000003000000000000200000000c9101000000000000400000001001010000000080101
  | 8, 14 => 0x60000000041101000000000a1000000000000003000000000000400000000811010000000012101000000000e100000000000000300000000000050000000000002000000000000100000000000040000000000012000000000000100000000000020000000000012000000000610100000000000030000000000004000000000000900000001051000000000000004000000000000000000000000020000000109101000000010010100000000000010000000000009000000000000200000000000040000000000003
  | 8, 15 => 0x100101000000000000300000000000070000000000004000000010d100000000000000000000000000020000000000001000000000a101000000000000800000001081010000000000002000000000000300000001091010000000000002000000000000100000000000040000000012101000000000e1000000000000009000000000000300000000000100000000000009000000000000700000000021010000000000002000000000000400000000c11000000000000013000000010410100000000000020000000000002
  | 8, 16 => 0x5000000000610100000000000000000000000004000000000000000000001051010000000000002000000000000300000000c510100000000000040000000000009000000000000400000000000000000000002100000000000001300000000c9100000000000000300000000000030000000000008000000000000300000001011010000000000002000000000000900000000000020000000000012000000000610000000000061010000000000002000000000000f000000000000200000000000030000000000001
  | 8, 17 => 0x200000000000020000000000003000000000000300000000000030000000000002000000000000400000000000080000000000004000000000000400000000841000000000000008000000000001000000000000050000000000003000000000a1010000000000004000000000000200000001081010000000000002000000000000200000000000020000000000002000000008510000000000000030000000000002000000000000200000000000000000000000004000000000000400000000401000000000000002
  | 8, 18 => 0x85101000000000000f00000000000020000000000003000000000001000000000401010000000000003000000000000200000000000020000000000001000000000000f000000000000400000000021010000000002101000000000000200000000000070000000000002000000008010000000000000040000000000003000000000610100000000121010000000108100000000000000400000000000130000000000002000000000000300000000000060000000000007000000000001300000000000020000000000004
  | 8, 19 => 0xc00000000000140000000084101000000000001400000000000030000000000004000000000000900000000000020000000000003000000000000500000000000000000000000003000000000000c0000000000004
  | 9, 0 => 0x100000000000000000000000001000000000000000000000000010000000000000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 13 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_47 roots_47 8 s ws hint
  | 1 => checkCutEntry dom_55 roots_55 8 s ws hint
  | 2 => checkCutEntry dom_31 roots_31 7 s ws hint
  | 3 => checkCutEntry dom_59 roots_59 7 s ws hint
  | 4 => checkCutEntry dom_27 roots_27 6 s ws hint
  | 5 => checkCutEntry dom_61 roots_61 6 s ws hint
  | 6 => checkCutEntry dom_31_32 roots_31_32 6 s ws hint
  | 7 => checkCutEntry dom_59_4 roots_59_4 6 s ws hint
  | 8 => checkCutEntry dom_62 roots_62 6 s ws hint
  | 9 => checkCutEntry dom_62_1 roots_62_1 6 s ws hint
  | 10 => checkCutEntry dom_15_32 roots_15_32 5 s ws hint
  | 11 => checkCutEntry dom_23_32 roots_23_32 5 s ws hint
  | 12 => checkCutEntry dom_39 roots_39 5 s ws hint
  | 13 => checkCutEntry dom_43_4 roots_43_4 5 s ws hint
  | 14 => checkCutEntry dom_51_4 roots_51_4 5 s ws hint
  | 15 => checkCutEntry dom_29 roots_29 5 s ws hint
  | 16 => checkCutEntry dom_30_1 roots_30_1 5 s ws hint
  | 17 => checkCutEntry dom_46 roots_46 5 s ws hint
  | 18 => checkCutEntry dom_54 roots_54 5 s ws hint
  | 19 => checkCutEntry dom_60_1 roots_60_1 5 s ws hint
  | 20 => checkCutEntry dom_30_32 roots_30_32 5 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_27 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_61 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31_32 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_59_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_62 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_62_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15_32 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23_32 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_39 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_43_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_51_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_29 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_30_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_46 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_54 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_60_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_30_32 _ hc
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
private theorem z5_0 : ∀ i, 0 ≤ i → i < 8 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 0 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 8 → Z 5 i = true := z5_0
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
private theorem z6_176 : ∀ i, 176 ≤ i → i < 178 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 2 176 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 178 → Z 6 i = true := (range_split (range_split (range_split (range_split z6_0 z6_16) (range_split z6_32 z6_48)) (range_split (range_split z6_64 z6_80) (range_split z6_96 z6_112))) (range_split (range_split z6_128 z6_144) (range_split z6_160 z6_176)))
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
private theorem z7_624 : ∀ i, 624 ≤ i → i < 628 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 4 624 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 628 → Z 7 i = true := (range_split (range_split (range_split (range_split (range_split (range_split z7_0 z7_16) (range_split z7_32 z7_48)) (range_split (range_split z7_64 z7_80) (range_split z7_96 z7_112))) (range_split (range_split (range_split z7_128 z7_144) (range_split z7_160 z7_176)) (range_split (range_split z7_192 z7_208) (range_split z7_224 z7_240)))) (range_split (range_split (range_split (range_split z7_256 z7_272) (range_split z7_288 z7_304)) (range_split (range_split z7_320 z7_336) (range_split z7_352 z7_368))) (range_split (range_split (range_split z7_384 z7_400) (range_split z7_416 z7_432)) (range_split (range_split z7_448 z7_464) (range_split z7_480 z7_496))))) (range_split (range_split (range_split z7_512 z7_528) (range_split z7_544 z7_560)) (range_split (range_split z7_576 z7_592) (range_split z7_608 z7_624))))
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
private theorem z8_304 : ∀ i, 304 ≤ i → i < 320 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 304 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_320 : ∀ i, 320 ≤ i → i < 324 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 4 320 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 324 → Z 8 i = true := (range_split (range_split (range_split (range_split (range_split z8_0 z8_16) (range_split z8_32 z8_48)) (range_split (range_split z8_64 z8_80) (range_split z8_96 z8_112))) (range_split (range_split (range_split z8_128 z8_144) (range_split z8_160 z8_176)) (range_split (range_split z8_192 z8_208) (range_split z8_224 z8_240)))) (range_split (range_split (range_split z8_256 z8_272) (range_split z8_288 z8_304)) z8_320))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_0 : ∀ i, 0 ≤ i → i < 16 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_16 : ∀ i, 16 ≤ i → i < 27 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 11 16 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 27 → Z 9 i = true := (range_split z9_0 z9_16)
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

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 15]⟩], 16⟩

theorem wit_mono : PEqualNP.MetaComplexity.Monotone2 wit := by
  simp [wit, PEqualNP.MetaComplexity.Monotone2]

theorem wit_sz : wit.size ≤ 11 := by decide

set_option maxRecDepth 40000 in
theorem wit_ev : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = Nat.testBit (4278124266 * 2 ^ 32 + 4277992584) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel

set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_63.testBit r.val = (fun x : Fin 6 → Bool => Nat.testBit (4278124266 * 2 ^ 32 + 4277992584) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) (pt6 r.val) := by decide +kernel

theorem lower : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124266 * 2 ^ 32 + 4277992584) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) t → 11 ≤ t :=
  lower_to_circuit6 (fun x : Fin 6 → Bool => Nat.testBit (4278124266 * 2 ^ 32 + 4277992584) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) goal_63 11 hT6 (by unfold IsConst; decide) low_63

end PEqualNP.Outside.L_meta_38135_aux

theorem PEqualNP.Outside.L_meta_38135 :
  ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124266 * 2 ^ 32 + 4277992584) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124266 * 2 ^ 32 + 4277992584) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  exact ⟨PEqualNP.Outside.L_meta_38135_aux.wit, PEqualNP.Outside.L_meta_38135_aux.wit_mono, le_trans PEqualNP.Outside.L_meta_38135_aux.wit_sz (PEqualNP.Outside.L_meta_38135_aux.lower s hs), PEqualNP.Outside.L_meta_38135_aux.wit_ev⟩
