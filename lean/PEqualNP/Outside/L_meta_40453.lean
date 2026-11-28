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

namespace PEqualNP.Outside.L_meta_40453_aux

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
def goal_61 : Nat := 0xfaaaaaa0faa00000faaaaaa0faa00000faaaaaa0faa00000faaaaaa0faa00000
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_31 : Nat := 0xffffffff
def goal_31 : Nat := 0xfee8ccc8fee8ccc8fee8ccc8fee8ccc8fee8ccc8fee8ccc8fee8ccc8fee8ccc8
def roots_31 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_31_32 : Nat := 0xffffffff00000000
def goal_31_32 : Nat := 0xfeeaeee8feeaeee8feeaeee8feeaeee8feeaeee8feeaeee8feeaeee8feeaeee8
def roots_31_32 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_47_16 : Nat := 0xffff0000ffff0000
def goal_47_16 : Nat := 0xfeeafeeafee8fee8feeafeeafee8fee8feeafeeafee8fee8feeafeeafee8fee8
def roots_47_16 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xeaeae8e8e8e8c8c8eaeae8e8e8e8c8c8eaeae8e8e8e8c8c8eaeae8e8e8e8c8c8
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_15_16 : Nat := 0xffff0000
def goal_15_16 : Nat := 0xfee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8
def roots_15_16 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0]

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xeee8eee8ccc8ccc8eee8eee8ccc8ccc8eee8eee8ccc8ccc8eee8eee8ccc8ccc8
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_62_1 : Nat := 0xaaaaaaaaaaaaaaaa
def goal_62_1 : Nat := 0xfffffffcfffcccccfffffffcfffcccccfffffffcfffcccccfffffffcfffccccc
def roots_62_1 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_39 : Nat := 0xff000000ff
def goal_39 : Nat := 0xe8e8e8e8c8c8c8c8e8e8e8e8c8c8c8c8e8e8e8e8c8c8c8c8e8e8e8e8c8c8c8c8
def roots_39 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xeeaaee88ee88cc88eeaaee88ee88cc88eeaaee88ee88cc88eeaaee88ee88cc88
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_43 : Nat := 0xf0f00000f0f
def goal_43 : Nat := 0xee88ee88cc88cc88ee88ee88cc88cc88ee88ee88cc88cc88ee88ee88cc88cc88
def roots_43 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_30 : Nat := 0x55555555
def goal_30 : Nat := 0xfcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0
def roots_30 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfeeaeee8fee8ccc8feeaeee8fee8ccc8feeaeee8fee8ccc8feeaeee8fee8ccc8
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

namespace S_61
def pairsG : List (Nat × Nat) := [(5, 21), (5, 37), (9, 25), (9, 41), (12, 28), (13, 29), (13, 45), (17, 21), (17, 25), (17, 49), (20, 21), (20, 28), (24, 25), (24, 28), (33, 37), (33, 41), (33, 49), (36, 37), (40, 41), (44, 45), (44, 60), (48, 49), (52, 53), (52, 60), (56, 57), (56, 60)]
def r1sG : List Nat := [5, 5, 9, 9, 12, 13, 13, 17, 17, 17, 20, 20, 24, 24, 33, 33, 33, 36, 40, 44, 44, 48, 52, 52, 56, 56]
def r2sG : List Nat := [21, 37, 25, 41, 28, 29, 45, 21, 25, 49, 21, 28, 25, 28, 37, 41, 49, 37, 41, 45, 60, 49, 53, 60, 57, 60]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [22063651494165, 18713729377557, 18730909247769, 26474465269020, 22012448021525, 36305646982437, 26427674401817, 36356984476977, 26474734757148, 36357051586865, 26461630895385, 48464967837980, 48452082935061, 26444854271001, 48482147706140, 61762186585372, 36305646983465, 39724557015333, 26462169144345, 36322826852649, 26427674663961, 61659106845980, 57278240204060, 22012264261909, 22012264260885, 36370523692081, 52919032683569, 36357051849009, 36370724428069, 44122536416553, 36387837187369, 39725093886245, 44123073287465]
def xsM : List Nat := roots_61.map (· &&& dom_61)
def goalM : Nat := goal_61 &&& dom_61
def NN : Nat → Nat
  | 3 => 5
  | 4 => 44
  | 5 => 292
  | 6 => 301
  | 7 => 24
  | 8 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x8b555a864fe8826e33817b7c29a1ac4719dbd9dc
  | 4, 0 => 0xfa7696bff03f1e3cee89ae8cc118d12ec0b2eae7b088d112aeb4f5a0a8ffc36ba81ee4889d7d8b4e99b6b9c3995298d190313def8e0202627855b511744e6a466eb1181a68fbc092652a3f145ce050c75c44d52f5b91bea255a93a5b4f396a3d48695b833f2ab7b03d3a6b7a3384bf723226a5563039e82b2b1c829c25851610222ff6812208cf902154fe791c668a3911b327b70deb9aae0ac3804b0998d386088f066c07c19d390772cacc015b1814
  | 5, 0 => 0x28a247c827e97e3b268603ed261c9e0624c22a38247d230d231df0ee22f163c02248b0ca21168df0200cefc0200a33aa1f37b2231f0498601e220b471d62e31f1cf373841c2aea931b9e18081b6cd0c71a043f5c19af2455191c1d9018ba579a1871215d17f67f1917f5008217823e151733b4dd170177a916c5f80f16bacd0e1685b4271576086b14304f6a131c0700125bff26116f84a0114a7be410531ac41034689f0fbee3f00f92b19f0e46cf900af8c4820ad52c000aa6b0d808c5626307ac7e7f0790dcd107463b13072e002f066a35da066441da05a46f3c048c4679041cbf2103e333a0038826d003736295035373af01f6dec301b9be50009fac28
  | 5, 1 => 0x526176265204438b51ee935b51bd0e77516e0975511d4c8c50989d2b50652fb04fb5fcda4ee182884d7e1b7f4cd3aa854c30ac4b4ba822cc4aa34d9c483cf29d46f06a5a465ecefc45612809446ff4cb43d1e7a042e305334296398c41b1069c419567fe417dd0ff4105f2c040c10b4d3f7aa0f03f2dfba63f25e4fc3ec3eb003eb1b4d03e7a55a73e65a3a33e3ca5393e16ae093c78a41e3b1bb2123a80c3183a4c48133830095536a1a86a368ac93136664f9c350fab4434c544493492bdf3343cd7ad31c9706c30d68f5a2f6b56df2effe60c2e3e52a52df677a12d8e446c2d5c596c2be8cfb12b2c63e72ac4f6e52a4995e429880446294f517428b4c817
  | 5, 2 => 0x83fef145830750d182a16b57828fa8117fd81dd07fd015f37f19eadc7d575aed7c7402f27c6fffd67bfe8af67a1c51d679b337d1795e351078a86aa9789ee5fc7887406e7753044f7694e789759e4e7974a4fcc674321128740ff6c97319e8657273f9d8720b235371d494997146686b6f89dccd6f7caeb26f2faaa96cc2b8356b690e5c6adfcf826a5752e1692586a0685f7b5667fe0a52679070d766a6b39866a4a3826593ebab6534bccb63db55fb62ab67e26213c9a46204460f6114a19e60ffdd5160087d7d5fa23a115f675c0c5f4194895f1fd1205d5e672e5ae2a671595a663958a2290658039cf9570585e25577e84454865bfe53121e7052c90180
  | 5, 3 => 0xc0b862e3bc320d46bbd19a69ba35c4b8b87c108bb4b560fcb2af3acab02b357aaff915b0afa3de14aefc3b2fad20c766abb8a62cab38cfdfa926c782a8f49c29a809893aa5ca66e4a47f6d72a3bc4901a1f03f81a0e35896a0c24652a064332c9e9b4db29e5950f39e4b1be19df8f8cb9dece1079db036219dac95f59c84198d9c1be6589ba085579b0e61fe9a11fff799ab3e96995298d19945d57698d737d098b8992797d69fee95f724b0924273c990c7dabf8f05e76a8e9a91ac8e8e475a8dc256e38d99cf4c8c287d868b980b8c8a9f2fe68a35798f892cb74a887d42298858671c8855a50887d5e25f87407e1986fec34985ea099b858f1995858c68b7
  | 5, 4 => 0xff73a77cfd046d17fb2753cbfab6755ef9798b14f81faa21f6a71adfeb31f7dae8faada9e6ea4658e4847c84e45cf41ce36212c6e1d78dc4e098c53fdbfa816bd76a2704d7603520d6f330acd532456ed2d63bf7d268f7e7d1ed96e6ce768a20ce2fdbfdcdb47afccc8e1026cabc3744ca4afdc7ca154b57c7d8adb0c7780177c71e4a3ec6e98f12c4784dc1c33bce80
  | 6, 0 => 0x268603ed26538a68257919e22505579624d4141c241a5d91239e3cb62313500e22acfdb32194f6fc210d7d9c20981f612097d6701feb46cf1fd50b541f4186351e9646da1dce88e91cd461b219cf9ce119a78d471925ff91190a67001876f8c1180aaad217823e15177baa8517670f4017202bfc15b8c4ce14ece3a714d14b1612ef774712ce089412c5492911d238ff1107245e10b2313c0f92b19f0eef36180e6dd5fa0e3fd20d0d991d150cee55a50ccad15b0c9ce5800b328f7b0b2986cb0b1ce3b00a6fc45f0a6443fd086941f407463b13071002620707b80d06ec1f7c0688002b0667813a066441da0522c74803d4fcb802b8d37b01c02c6100e0429d
  | 6, 1 => 0x5116c579501930ff4f7b23d44e3f75c04cbf0a3d4a5af10448f93e3d47ccba7347040e0d44f1157944c6a07b44c2db92443342c64396d34a431b1a0341e24d124105f2c040cd85c340c7b4733f6f10533e3ca5393d0f321e3d04f3643cc57f4a3befaf703bcf32913b6a3ffa3b1bb2123ada0f623ab91bed39e78ed939b2731639a4e8c3399fb3d539475be938efa7fa384bc2703810c1db37920be536e9258f36664f9c34372f0133e66d3731c9706c2fa36baf2f6159862ec72d222dd111802d8e446c2c7d061d2bcd7fcc2bc3f88e2b313a452ac4f6e52aadd4942a111cb5293e7380289af5592878011c27e97e3b274b07312747cf2e26ffd9f226c2d9c5
  | 6, 2 => 0x7d4be1cb79e3e4d979697c9a792749c578d33f877753044f7694e78975aac8ef74321128740be8e5735417d37319e865725b25bd71ec754a7181fe8f7132b184712720f16e1445ab6cee05076c1d17f66b96b44c6b690e5c6ad3e9306ac90d546a2e37fd68cd66c56843851c657a37956534bccb63db55fb629ed82f619df3c360f71128600e7d715fbb358b5fb86e365fa23a115f08d96d5de13d215cef20af5bea81c55b57c5875b30cd945a9408c85a565d0e5a24f14d583a89e657515f0056fff4e756ffc2ad56eb7f2d56e4e7ff5651b8cb5577e8445506cec854a4757c5480c232543a0d6253121e7053061dab52abcc1551db27f551bd0e77516d1ad4
  | 6, 3 => 0xc8a84e73c78542a9c5df00ecc4c1c2a4c4254cbfc3b6869cc267c173c05e9d30ba35c4b8b619cb05b4b89088b3507d7eb173a318af40e6fdad9e58feac8a94c3ab532136aad50b77aa4489e6aa028d27a82d55c1a70b327aa627110aa533770ca461d55ba1e3c5dba0fa5b229fceb7579e9096ab9e3d2f6f9e310d9b9df8f8cb9daaa9f19c1be6589bc1d3369a577ac199cef08f995298d198d737d09705a3089658476395714d0492a7ff7d9135a4eb8b780bac8b6186f38af1870b8a36f65688352f3387d5e25f8755d4d686fec34986b86b21862c0263858f19958542248384d0d05f8362b4dc819a727e8062335b7fd81dd07fadc6777f56ee497da5e651
  | 6, 4 => 0xfef56002fd8f760afabc4418fa3fc4d9eeefd547ede97adcec66dc94eac06c0dea79a652e82dc0aae7f71e86e7b058cbe7836fb3e646a1d4e34d8609e32d67a6e2bd5571e098c53fdff407eadfe7c175de7f782bdb852770d92ec0ffd8bbd9e9d76e91add7476cb1d6657378d532456ed4d8324cd268f7e7d2481c92d1af8ec7d0583179d01c021ececd1567ce2fdbfdce00f0dfcc2b7a01cc1596dfcbe2e634cbbe5e93cbace62dcb93e9a8c9831fefc948a61d
  | 7, 0 => 0xe7f71e86dff407ead8bbd9e9d268f7e7ce2fdbfdc5df00ecb3507d7e9e310d9b9c1be658995298d19705a30892a7ff7d6c1d17f668cd66c5657a379551db27f540cd85c33e3ca5393810c1db36e9258f2ac4f6e51dce88e912ef7747086941f4
  | 8, 0 => 0x995298d1
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x323232320000000000000000000000000000000000000000000000000000000030303030000000000000000000000000000000000000000000000000000000002222222200000000000000000000000000000000000000000000000000000000111111110000000000000000000000000000000000000000000000000000000003033333000000000000000000000000000000000000000000000000000000000303030300000000000000000000000000000000000000000000000000000000003300330000000000000000000000000000000000000000000000000000000000003333
  | 0, 1 => 0x2222000022220000000000000000000000000000000000000000000000000000111133333333000000000000000000000000000000000000000000000000000011110000111100000000000000000000000000000000000000000000000000000303000003030000000000000000000000000000000000000000000000000000003300000033000000000000000000000000000000000000000000000000000000003333333300000000000000000000000000000000000000000000000000000000333322220000000000000000000000000000000000000000000000000000000033330000
  | 0, 2 => 0x30003000300030000000000000000000000000000000000000000000000000000333333333333000000000000000000000000000000000000000000000000000033333333000000000000000000000000000000000000000000000000000000003333000033330000000000000000000000000000000000000000000000000000333300000000000000000000000000000000000000000000000000000000000033220000332200000000000000000000000000000000000000000000000000003300000033000000000000000000000000000000000000000000000000000000303000003030
  | 0, 3 => 0x330033003333330000000000000000000000000000000000000000000000000033003300330033000000000000000000000000000000000000000000000000003300330033000000000000000000000000000000000000000000000000000000330033000000000000000000000000000000000000000000000000000000000033002200330022000000000000000000000000000000000000000000000000003300000033000000000000000000000000000000000000000000000000000000300030003000300000000000000000000000000000000000000000000000000022002200220022
  | 0, 4 => 0x1030103010301030000000000000000000000000000000000000000000000000101333301013333000000000000000000000000000000000000000000000000010101013333333300000000000000000000000000000000000000000000000001010101010101010000000000000000000000000000000000000000000000000033333300000000000000000000000000000000000000000000000000000000003311330033113300000000000000000000000000000000000000000000000000330033333333330000000000000000000000000000000000000000000000000033003333003300
  | 0, 5 => 0x3033333030333330000000000000000000000000000000000000000000000000303303003033030000000000000000000000000000000000000000000000000030303033333333300000000000000000000000000000000000000000000000003030303030303030000000000000000000000000000000000000000000000000303030300000000000000000000000000000000000000000000000000000000030300000303000000000000000000000000000000000000000000000000000003020302030203020000000000000000000000000000000000000000000000000300030003000300
  | 0, 6 => 0x11111111111100000000000000000000000000000000000000000000000000001111111100000000000000000000000000000000000000000000000000000000111100001111000000000000000000000000000000000000000000000000000011001100110011000000000000000000000000000000000000000000000000001010101010101010000000000000000000000000000000000000000000000000033303330333033300000000000000000000000000000000000000000000000003300330033003300000000000000000000000000000000000000000000000000313031303130313
  | 0, 7 => 0x12121212121212120000000000000000000000000000000000000000000000001133113311331133000000000000000000000000000000000000000000000000111133331111333300000000000000000000000000000000000000000000000011112222111122220000000000000000000000000000000000000000000000001111111133333333000000000000000000000000000000000000000000000000111111112222222200000000000000000000000000000000000000000000000011111111111133330000000000000000000000000000000000000000000000001111111111111111
  | 0, 8 => 0x22002200220022000000000000000000000000000000000000000000000000002200220000000000000000000000000000000000000000000000000000000000212121212121212100000000000000000000000000000000000000000000000020202020202020200000000000000000000000000000000000000000000000002020000020200000000000000000000000000000000000000000000000000000200020002000200000000000000000000000000000000000000000000000000013131313131313130000000000000000000000000000000000000000000000001300130013001300
  | 0, 9 => 0x22222222000000000000000000000000000000000000000000000000000000002222222022222220000000000000000000000000000000000000000000000000222222002222220000000000000000000000000000000000000000000000000022222020222220200000000000000000000000000000000000000000000000002222111122221111000000000000000000000000000000000000000000000000222200002222000000000000000000000000000000000000000000000000000022220000000000000000000000000000000000000000000000000000000000002220222022202220
  | 0, 10 => 0x22222222222222220000000000000000000000000000000000000000000000002222222222222020000000000000000000000000000000000000000000000000222222222222000000000000000000000000000000000000000000000000000022222222222022200000000000000000000000000000000000000000000000002222222222200000000000000000000000000000000000000000000000000000222222222200220000000000000000000000000000000000000000000000000022222222202000000000000000000000000000000000000000000000000000002222222211111111
  | 0, 11 => 0x23232323000000000000000000000000000000000000000000000000000000002303230323032303000000000000000000000000000000000000000000000000223322332233223300000000000000000000000000000000000000000000000022332233000000000000000000000000000000000000000000000000000000002222333322223333000000000000000000000000000000000000000000000000222233330000000000000000000000000000000000000000000000000000000022222222333333330000000000000000000000000000000000000000000000002222222222223333
  | 0, 12 => 0x30300000333333330000000000000000000000000000000000000000000000003030000030300000000000000000000000000000000000000000000000000000302030203020302000000000000000000000000000000000000000000000000030033003300330030000000000000000000000000000000000000000000000003000300030003000000000000000000000000000000000000000000000000000300030000000000000000000000000000000000000000000000000000000000030000000300000000000000000000000000000000000000000000000000000002323232323232323
  | 0, 13 => 0x30303030303000000000000000000000000000000000000000000000000000003030303030003000000000000000000000000000000000000000000000000000303030300303030300000000000000000000000000000000000000000000000030303030000000000000000000000000000000000000000000000000000000003030302030303020000000000000000000000000000000000000000000000000303020203030202000000000000000000000000000000000000000000000000030302020303000000000000000000000000000000000000000000000000000003030003030300030
  | 0, 14 => 0x32003200320032000000000000000000000000000000000000000000000000003200220032002200000000000000000000000000000000000000000000000000313131313131313100000000000000000000000000000000000000000000000030333033303330330000000000000000000000000000000000000000000000003030333330303333000000000000000000000000000000000000000000000000303031313030313100000000000000000000000000000000000000000000000030303030333333330000000000000000000000000000000000000000000000003030303030303030
  | 0, 15 => 0x32303230303030300000000000000000000000000000000000000000000000003230303032303030000000000000000000000000000000000000000000000000323000003230000000000000000000000000000000000000000000000000000032223222322232220000000000000000000000000000000000000000000000003222322200000000000000000000000000000000000000000000000000000000322222223222222200000000000000000000000000000000000000000000000032220000322200000000000000000000000000000000000000000000000000003220322032203220
  | 1, 0 => 0x32323232303030300000000000000000000000000000000000000000000000003232323200000000000000000000000000000000000000000000000000000000323230303232303000000000000000000000000000000000000000000000000032323030303030300000000000000000000000000000000000000000000000003232222232322222000000000000000000000000000000000000000000000000323222223030000000000000000000000000000000000000000000000000000032320000323200000000000000000000000000000000000000000000000000003230323032303230
  | 1, 1 => 0x33003300000000000000000000000000000000000000000000000000000000003300300033003000000000000000000000000000000000000000000000000000330022003300220000000000000000000000000000000000000000000000000033000300330003000000000000000000000000000000000000000000000000003300003333000033000000000000000000000000000000000000000000000000330000003300000000000000000000000000000000000000000000000000000033000000000000000000000000000000000000000000000000000000000000003232323232323232
  | 1, 2 => 0x33003330330033300000000000000000000000000000000000000000000000003300330033003333000000000000000000000000000000000000000000000000330033003300330000000000000000000000000000000000000000000000000033003300330030000000000000000000000000000000000000000000000000003300330033002200000000000000000000000000000000000000000000000000330033003300000000000000000000000000000000000000000000000000000033003300320032000000000000000000000000000000000000000000000000003300330022002200
  | 1, 3 => 0x33222222330000000000000000000000000000000000000000000000000000003322222200000000000000000000000000000000000000000000000000000000332200003322000000000000000000000000000000000000000000000000000033203320332033200000000000000000000000000000000000000000000000003320332033003300000000000000000000000000000000000000000000000000331133113311331100000000000000000000000000000000000000000000000033033303330333030000000000000000000000000000000000000000000000003301330133013301
  | 1, 4 => 0x33300000333000000000000000000000000000000000000000000000000000003322332233223322000000000000000000000000000000000000000000000000332233223300330000000000000000000000000000000000000000000000000033223322222222220000000000000000000000000000000000000000000000003322332200000000000000000000000000000000000000000000000000000000332233003322330000000000000000000000000000000000000000000000000033223300330033000000000000000000000000000000000000000000000000003322222233222222
  | 1, 5 => 0x33330000000000000000000000000000000000000000000000000000000000003332333233323332000000000000000000000000000000000000000000000000333233320000000000000000000000000000000000000000000000000000000033320000333200000000000000000000000000000000000000000000000000003330333033303330000000000000000000000000000000000000000000000000333033303300330000000000000000000000000000000000000000000000000033303330000000000000000000000000000000000000000000000000000000003330330033303300
  | 1, 6 => 0x33330033333300330000000000000000000000000000000000000000000000003333000033333333000000000000000000000000000000000000000000000000333300003333000000000000000000000000000000000000000000000000000033330000333000000000000000000000000000000000000000000000000000003333000033000000000000000000000000000000000000000000000000000000333300003232000000000000000000000000000000000000000000000000000033330000222200000000000000000000000000000000000000000000000000003333000000003333
  | 1, 7 => 0x33332222333322220000000000000000000000000000000000000000000000003333222233330000000000000000000000000000000000000000000000000000333322222222222200000000000000000000000000000000000000000000000033332222000000000000000000000000000000000000000000000000000000003333202033332020000000000000000000000000000000000000000000000000333320203333000000000000000000000000000000000000000000000000000033331111333311110000000000000000000000000000000000000000000000003333010133330101
  | 1, 8 => 0x33333300333300000000000000000000000000000000000000000000000000003333323233333232000000000000000000000000000000000000000000000000333332320000000000000000000000000000000000000000000000000000000033333030333330300000000000000000000000000000000000000000000000003333303033330000000000000000000000000000000000000000000000000000333330303030303000000000000000000000000000000000000000000000000033333030000000000000000000000000000000000000000000000000000000003333300033333000
  | 1, 9 => 0x33333333010101010000000000000000000000000000000000000000000000003333333300330033000000000000000000000000000000000000000000000000333333330000333300000000000000000000000000000000000000000000000033333333000011110000000000000000000000000000000000000000000000003333333300000000000000000000000000000000000000000000000000000000333333303333333000000000000000000000000000000000000000000000000033333330000000000000000000000000000000000000000000000000000000003333330033333300
  | 1, 10 => 0x33333333222222220000000000000000000000000000000000000000000000003333333322220000000000000000000000000000000000000000000000000000333333332200220000000000000000000000000000000000000000000000000033333333202000000000000000000000000000000000000000000000000000003333333311111111000000000000000000000000000000000000000000000000333333331111000000000000000000000000000000000000000000000000000033333333110011000000000000000000000000000000000000000000000000003333333303030303
  | 1, 11 => 0x33333333333000000000000000000000000000000000000000000000000000003333333333003300000000000000000000000000000000000000000000000000333333333300000000000000000000000000000000000000000000000000000033333333323232320000000000000000000000000000000000000000000000003333333330303030000000000000000000000000000000000000000000000000333333333030000000000000000000000000000000000000000000000000000033333333300030000000000000000000000000000000000000000000000000003333333330000000
  | 1, 12 => 0x3333333333333300000000000000000000000000000000000000000000000000333333333333222200000000000000000000000000000000000000000000000033333333333300000000000000000000000000000000000000000000000000003333333333303330
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xcb79483b5784f39d804f39f704d3ab794f3
  | 4, 0, 0 => 0xcbb59c83400b5956d57400a39d7047400cbab79574009582704a400cb8d6a4a400b5957050400cbb5953f400b5705720400b0957057400cb8b7057400cb95572e400b595703a400bc956a4a400b5774f44400c89f70574
  | 4, 0, 1 => 0x95694f4a4009d704f47400b5a6804f400bea17057400ba9587574009579704f400b3957055400af926f5740095705715400cbb57857400b5a36547400b5ab7c4f400cbb55731400cb9d8057400cb9d7048400b5634f484
  | 4, 0, 2 => 0xaf956f55400cb95704b400b5957053400cb817744400cbb57c4840095664f4c400cbb56457400cbb5ab7a400cbb595454008d704f4a400cb95703c4cbb59570575
  | 5, 0, 0 => 0xcbb5777038500cbb56f571e500b595704f38500cbb57c7047500cbb59c6357500b595705705500d39570381450095574f2c14500b5a58f7057500cb95705712500bcb595704a500b57770574f500cbb5957e57500cbb5ab6557500be95705749500cba69d70475
  | 5, 0, 1 => 0xbeaf957057500b5956f574f500cbb5967057500cbb5775744500bf95704a0a500cbb570571b500cb95705514500e1af95572c500b5a395572c500cbb8957057500cbbf95704a500d7b595703b500cbb5957037500cbc466571e500dbb5956f57500cb95382c145
  | 5, 0, 2 => 0xcbc4956638500b59584574f500cbb5705d18500cbb59c7038500cbbe95704a500cbb5956f38500d3b595382c500c49566574f500d795704f14500cbb5955730500b595704f4d500bcb5957057500b59c70574f500cb95805714500b595715706500cb957357105
  | 5, 0, 3 => 0xcbb570571f500dab5957057500cbb5956557500b695705708500cbb595552c500cbb5956957500b5a495704f500cb9d70571e500b595705709500b59b70574f500cb97705714500cba095704a500b595705c57500958a704f4a500b5955f572c500e1b39570575
  | 5, 0, 4 => 0xcbc3956657500cbb58d70575009d9570574f500cba6704714500b59e957057500b5704f381e50095705b4f14500957057140a500b570571e05500d7b5954f2c500cbb5a66547500cb95705714500cbab635714500cbb5926f57500b59565570a500cb9566570c5
  | 5, 0, 5 => 0xb5ab95704f4a600bcb570571e500cbb5955727500cbb595572c500b59f957057500cbb58c7057500d3b5957057500cbb5705740500b595705751500d2b59570575b5aba570574f600cbbf704a1e500dbb5956c57500cb9d957038500dd95705714500b58d70570a5
  | 5, 0, 6 => 0xcbb5957257500cbb5a07047500c5b5957057500bf95704f4a500b5b195704f500cbb5a6472c500b595704f35500cbb5956b575009586817057500b595704a3b500b595572c0a500cbba957057500b595703805500cbb5635748500b5a5705746500cbb59570585
  | 5, 0, 7 => 0xd4b5957057500b595703b05500e1af957055500cb70571e145cbb595807d57600ddb58f7057500bcb5957038500b595705a57500cbb5917057500be95704f4a500cbb565571e500d1b5957057500cbb598705750095704f4a14500cbb5705722500ddb595572c5
  | 5, 0, 8 => 0xdab5957038500cb777057145009570574f14500b59570570e500cbb5a6703e500b5954f4a2c500dbb56c571e500cbb5ab7c57500b59569574f500cd95705713500ccb5957057500cbb5954424500b59570573b50070571e140a500b595867057500cbb59a70345
  | 5, 0, 9 => 0xe1af957057500cbb58d7038500cbb5957f57500b5957b7057500b5af957055500b5572c1e0a500cbb5958848500b58d70574f500957038140a500b595888644500cbb5572c1e500cb95703814500cbb5767057500d3b570571e500cfb5957057500cba28a70575
  | 5, 0, 10 => 0xcbc495572f500cbb595382c500cbc88a7057500ba9570574f500cb95797057500d3b5957038500cbb5955729500b595574f2c500dac4956657500cb956f5714500cb95705726500d2b5957038500cbb59c6557500dbb5956c38500dab5956f57500cbbb9566575
  | 5, 0, 11 => 0xcbb5a68057500cbb5957056500b59570550a500cbb5ab6157500cbb5957055500cb95704a0d500cbb595704e500cbb568571e500cbb5ab5732500b570573b1e500deb5957055500b595382c0a500cbb56a571e500c88a70570a500cbb4957057500b5956c57025
  | 5, 0, 12 => 0xbfbc95704a500e195705716500b595867038500b595705723500958170570a500cbb5a68047500cb9d9565575cbb595704f48600b59580570a500b586777057500cb95817057500cbb59c572c500d7b595704f500d1b5957038500cbb5958057500b595704f045
  | 5, 0, 13 => 0xb59570570a500b5ab63570a500b595705707500b5574f2c1e500cb9d705747500cbb5957057500cbb5947057500cbb5ab635750095704f38145009570571405500af95705700500b5a370571e5cbb5ab8a6657600dbb595572d500cbb5977057500b595703b385
  | 5, 0, 14 => 0xcbbf8d704a500b595704f3d500e1af957038500dfb5957057500cbb5937057500cb9d95572c500b5a670470a500ceb570571c500d6b595704f500b5957c704f500cbb5382c1e500cbb5a67047500cbb2957057500cbb5995728500cbb5955e57500b595705b4f5
  | 5, 0, 15 => 0xcbb570571d500cb9566574c500b595705725500b595704f4a500b595704f48500b59570554f500e1af956f575cbb595704a48600bcb58d7057500cbb5a17057500cbb5957054500cbb9957035500b595706757500b595705703500cb8d70574a500bc957057145
  | 5, 1, 0 => 0xb5a6704f47500cbb5957038500cbb5ab6338500cbb5957039500b59570574f500b5ab63574f500d395705714500b595704f05500ddb570571e500cbac957057500db956c5714500d8b5957057500cbb5956f55500cbb770571a500cb95705b0f500cb8d7057145
  | 5, 1, 1 => 0xbdb595704f500cbb5957a70500cb572c1e14500cbb58d6a57500c9b59570575009570573b145009586705714500cbb59c6657500b5956f570a50095705a5714500cbb5956f57500b5ad957057500cbab9d7057500b5957059055cbb5aba76357600b59570380a5
  | 5, 1, 2 => 0xd3b595704f500d3b5957036500cbbf95703d500cbb56357175
  | 6, 0, 0 => 0xd3cbb5957057600cbb595665744600decbb595572c600cbb59570574460000b595704f38500cbb595572c2b600cbb57057471e600cbb570571e14600cbb59560572c600dbcbb5956c5760000b595705705500cbbdb5957057600cbb5b3957057600cbb595757057600cbb5ab958857600cbc6b59570576
  | 6, 0, 1 => 0xcbb595705738600cbb595705752600b5a6a3957057600cbbfb5957038600cbb595572c0a600cbc7b595705760000cbbf95704a500cbb57063571e600cbc495706657600cbb595572c1e600bfb59570574f600cbb7b5957057600cbb595705711600cbb595706257600b5957057440a600cbb595706f576
  | 6, 0, 2 => 0xe1cbb5957055600cbb5ab957057600b5957063574f600cbb595705719600cdcb95705714600cbb595704738600cbb595703814600cbb595705718600beb59570574f60000bcb5957057500cbb595705741600cbb595897057600cbb58f70571e600b5957057380a600b59570574f47600b59570574f146
  | 6, 0, 3 => 0xcbb5956557500cbb5a5957057600cbb59570573b600b5958f70574f600dbcb95705714600d7cb95705714600cbb59570574d600cbb5958670576cbb5ab9570574f700cbc2b5957057600cbb595706338600e1b5af957057600b5ab9570570a600cbbbb5957057600cbb5ab956657600cbb5958570576
  | 6, 0, 4 => 0x957057140a500cbb595635744600cbc1b5957057600cbc8b58a7057600cbb59570574660000cb95705714500cb958a70574a600b5957170570a600cbb5958f7038600cbb595703833600cbc49570571460000dab5957057500cbb59570571c600cbb595717057600cbb9b5957038600cbb59570572a6
  | 6, 0, 5 => 0xcbb595747057600cb95705b5714600cb9588705714600cbb5956c6657600dbcbb595572c600e1cbb5957057600d7cbb595572c600cbb595706c5760000dbb5956c57500e1deb5957057600cbb7b570571e60000cbb58d7057500cb9570574f14600cbb57057441e600cbb5a4957057600cbb59570570b6
  | 6, 0, 6 => 0xb595572c0a500cbb5a6957057600cbb570571e19600cbb570571e1860000cbb595572c500cbb595705749600cbb595817057600cb957057140f600cbc4b595572c600cbb595757038600e1cbaf95705760000d3b5957057500e1b59570570a600cbb595737057600cbb57057381e600b595706c570a6
  | 6, 0, 7 => 0xcbb595706557600cbbf9570574a600cbb5b1957057600cbb595705735600cbb59588572c6cbb5ab9570574a700cbb59570570d600b59570574f38600cbb5a6957047600cbb595706e57600cbb5ab70571e600cb958a705714600d3cbb5957038600b5a69570570a600cbb595574f2c600cbb5ab9563576
  | 6, 0, 8 => 0xd7cbb595704f600e3cbb5957057600bfbcb5957057600cbb5ab957038600cbb59995572c60000b59570573b500cbb5a9957057600b5af9570570a600dab595706657600cbb59583705760000b595867057500cbb595705724600b5ab9570574f600cbb5af95705760000cb70571e14500cbb59c7057446
  | 6, 0, 9 => 0xdbb595706c57600b59570574f46600cbc8b595572c600b59570570a08600009570574f14500e1cbb570571e600cbb5706c571e600cbb5957057086cbb5aba7957057700cbb595705734600b5a59570574f600cbb59570572f600b59570574f3b600cbb595705721600cbb5958a572c600cb9570574a146
  | 6, 0, 10 => 0xe1cbb5957038600cbcab5957057600e1b59570574f600cbb59570570a600b59570572c0a60000e1af957057500cbb59566572c600cbb595574a2c600cbbf95705714600cbb59570572c600deb59570570a600decbb595705760000cbb5572c1e50000cb95703814500cbb595705700600cbb5957060576
  | 6, 0, 11 => 0xcbb595706a57600cbb5a6957038600cb9570635714600e2cbb5957057600cbb5af70571e60000cbb595382c50000cbc88a7057500b5a69570574f60000d3b5957038500cbb595705716600ddcbb595705760000b595574f2c500cbb5958e7057600b59570574f49600cb9570574714600cbbfb58d70576
  | 6, 0, 12 => 0xcdcbb595705760000cb95817057500cbb59570383560000d7b595704f500b5af9570574f600b59570570a0660000cbb5958057500d5cbb5957057600cbb595705742600cbb595705706600cb958f705714600cb957057141360000cbb5957055500cbb595705717600e1cbb5956f57600cbbfb595572c6
  | 6, 0, 13 => 0xb59570574f2c60000b59570570a500cbb595705736600deb59570574f600c4b59570570a60000cbb595705750000cbb5ab6357500cbc4b5957057600cb9588817057600d7b59570570a600d7cbb5957057600cbb595705704600cecbb5957057600cbb59c957057600cbb5af957038600cbb595704f4a6
  | 6, 0, 14 => 0xcbb59570570f600cbb595705957600d6cbb5957057600cbb5957c7057600cbb595705b57600cbb595705701600d9cbb5957057600cbb59570380a600cb9570573814600cbb59570382c600b59570574f0a600d0cbb595572c600decbb5957038600cb9570571411600cbb59570574f60000cbb5a670475
  | 6, 0, 15 => 0xb59570574a0a600d7b59570574f600cbb59570574a600cbbfb595704a600cbb595705748600cbb5a8957057600cbb595705743600cbb59570575560000b595704f4a500b5958a70570a600d3b595705738600cbb5958a7057600cbb59570573d600cbab95705714600b5957059570a600dccbb59570576
  | 6, 1, 0 => 0xcbb5957038500cbb5ae957057600cbb595706157600cbb595907057600cbc4b5957038600cbb58870571e60000b59570574f500cbb5a6956557600cb9573705714600cbb5aa957057600c4b59570574f600d7cbb5957038600cbb595572c2a600cbb595705732600e1cb95705714600e0cbb59570576
  | 6, 1, 1 => 0xcbc0b5957057600cbaf95705714600cbbeb5957057600b5957057140a60000cbb5956f57500cbb5957057146cbb5958a706657700cbb5a6705747600bfb59570570a600b59570570a05600cbbfb5957057600cbb5a7957057600cbb595704f38600cbb59570570560000b59570380a500cbb5957038366
  | 6, 1, 2 => 0xcbb595704a38600cb957057140a600b59570574f4a600cb9570572c14600cbb595705713600cbb9b5957057600cbb5958a7038600b5957063570a600b6b59570570a600b5958a70574f600cbb595706357600cbb6b5957057600cbbcb59570576
  | 7, 0, 0 => 0xb59570570a500cbb59570575cbc4b59570576d7cbb59570576cbb59570570a6cbb59570572c6decbb59570576cbb5af9570576cbb5a6957057600cbb595572c5e1cbb59570576cbb595706c57600cb957057145cbb5ab9570576cbb5957057386cbb5957057446
  | 7, 0, 1 => 0xcbb5957063576cbb5957057146cbbfb5957057600cbb5957038500b59570574f5cbb59570574a6cbb5958a70576cbb59570574f6
  | 8, 0, 0 => 0xcbb59570575
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 28
  | 4 => 44
  | 5 => 52
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
  | 0, 0 => 0xfff0000000000000000000000000000000000000000000000000000000000000c7300000000000000000000000000000000000000000000000000000000000003ef0000000000000000000000000000000000000000000000000000000000003c1000000000000000000000000000000000000000000000000000000000000033ff000000000000000000000000000000000000000000000000000000000000338c0000000000000000000000000000000000000000000000000000000000000f83000000000000000000000000000000000000000000000000000000000000007f
  | 0, 1 => 0x1c06f00000000000000000000000000000000000000000000000000000000001e3fff00000000000000000000000000000000000000000000000000000000001e0010000000000000000000000000000000000000000000000000000000000005c00c000000000000000000000000000000000000000000000000000000000003c0030000000000000000000000000000000000000000000000000000000000003fff0000000000000000000000000000000000000000000000000000000000003fef0000000000000000000000000000000000000000000000000000000000003f80
  | 0, 2 => 0x21c38000000000000000000000000000000000000000000000000000000000001fffff00000000000000000000000000000000000000000000000000000000001fff8000000000000000000000000000000000000000000000000000000000001fc07f00000000000000000000000000000000000000000000000000000000001fc00000000000000000000000000000000000000000000000000000000000001dc07f00000000000000000000000000000000000000000000000000000000001c007c00000000000000000000000000000000000000000000000000000000001a0073
  | 0, 3 => 0xe3cfff0000000000000000000000000000000000000000000000000000000000e3cf830000000000000000000000000000000000000000000000000000000000e3cf800000000000000000000000000000000000000000000000000000000000e3c0000000000000000000000000000000000000000000000000000000000000e1cf830000000000000000000000000000000000000000000000000000000000e00f800000000000000000000000000000000000000000000000000000000000c20c03000000000000000000000000000000000000000000000000000000000001c383
  | 0, 4 => 0x325f38000000000000000000000000000000000000000000000000000000000033ff07f0000000000000000000000000000000000000000000000000000000003243fff00000000000000000000000000000000000000000000000000000000032430000000000000000000000000000000000000000000000000000000000000ffc0000000000000000000000000000000000000000000000000000000000000ffcf930000000000000000000000000000000000000000000000000000000000e3ffff0000000000000000000000000000000000000000000000000000000000e3f07c
  | 0, 5 => 0x33ff3ff00000000000000000000000000000000000000000000000000000000033a33f3000000000000000000000000000000000000000000000000000000000325ffff000000000000000000000000000000000000000000000000000000000325f38c000000000000000000000000000000000000000000000000000000000325c0000000000000000000000000000000000000000000000000000000000003203380000000000000000000000000000000000000000000000000000000000305f38c000000000000000000000000000000000000000000000000000000000304300c
  | 0, 6 => 0x3fe3c000000000000000000000000000000000000000000000000000000000003fe00000000000000000000000000000000000000000000000000000000000003e03c0000000000000000000000000000000000000000000000000000000000031c30100000000000000000000000000000000000000000000000000000000000da0c100000000000000000000000000000000000000000000000000000000003e7ff8f0000000000000000000000000000000000000000000000000000000003c63c0f0000000000000000000000000000000000000000000000000000000003e7ff8c
  | 0, 7 => 0xdbcf9c0000000000000000000000000000000000000000000000000000000003ffff930000000000000000000000000000000000000000000000000000000003fffc7f0000000000000000000000000000000000000000000000000000000003e1fc6f0000000000000000000000000000000000000000000000000000000003fe3fff0000000000000000000000000000000000000000000000000000000003fe03ef0000000000000000000000000000000000000000000000000000000003fe3c7f0000000000000000000000000000000000000000000000000000000003fe3c10
  | 0, 8 => 0x6c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000032430630000000000000000000000000000000000000000000000000000000000000063000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000600000000000000000000000000000000000000000000000000000000003ffff9c00000000000000000000000000000000000000000000000000000000031c301c
  | 0, 9 => 0x1c00000000000000000000000000000000000000000000000000000000000000003ef00000000000000000000000000000000000000000000000000000000000003ec00000000000000000000000000000000000000000000000000000000000003e300000000000000000000000000000000000000000000000000000000001e039000000000000000000000000000000000000000000000000000000000000003800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006f
  | 0, 10 => 0x1c3ef000000000000000000000000000000000000000000000000000000000001c3e3000000000000000000000000000000000000000000000000000000000001c380000000000000000000000000000000000000000000000000000000000001c06f000000000000000000000000000000000000000000000000000000000001c000000000000000000000000000000000000000000000000000000000000001c06c000000000000000000000000000000000000000000000000000000000001c000000000000000000000000000000000000000000000000000000000000001fc10
  | 0, 11 => 0x325c000000000000000000000000000000000000000000000000000000000000325f3ec0000000000000000000000000000000000000000000000000000000000e3cfef0000000000000000000000000000000000000000000000000000000000e3c00000000000000000000000000000000000000000000000000000000000001fc3ff00000000000000000000000000000000000000000000000000000000001fc000000000000000000000000000000000000000000000000000000000000001ffff000000000000000000000000000000000000000000000000000000000001c3ff
  | 0, 12 => 0xc03fff0000000000000000000000000000000000000000000000000000000000c00c000000000000000000000000000000000000000000000000000000000000180073000000000000000000000000000000000000000000000000000000000039c3f0000000000000000000000000000000000000000000000000000000000018007000000000000000000000000000000000000000000000000000000000001800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000325f3ef
  | 0, 13 => 0xda0c000000000000000000000000000000000000000000000000000000000000da00700000000000000000000000000000000000000000000000000000000000da338c0000000000000000000000000000000000000000000000000000000000da00000000000000000000000000000000000000000000000000000000000000d80c730000000000000000000000000000000000000000000000000000000000c00c630000000000000000000000000000000000000000000000000000000000c00c000000000000000000000000000000000000000000000000000000000000c20c03
  | 0, 14 => 0x18007c000000000000000000000000000000000000000000000000000000000000006c0000000000000000000000000000000000000000000000000000000003fe3c730000000000000000000000000000000000000000000000000000000000fbcff30000000000000000000000000000000000000000000000000000000000dfcc7f0000000000000000000000000000000000000000000000000000000000de0c730000000000000000000000000000000000000000000000000000000000da3fff0000000000000000000000000000000000000000000000000000000000da0c73
  | 0, 15 => 0xda0c730000000000000000000000000000000000000000000000000000000000da0c730000000000000000000000000000000000000000000000000000000000c00c00000000000000000000000000000000000000000000000000000000000019c3ff000000000000000000000000000000000000000000000000000000000019c000000000000000000000000000000000000000000000000000000000000001c3ef0000000000000000000000000000000000000000000000000000000000000380000000000000000000000000000000000000000000000000000000000018007f
  | 1, 0 => 0xdbcc730000000000000000000000000000000000000000000000000000000000dbc0000000000000000000000000000000000000000000000000000000000000da0ff30000000000000000000000000000000000000000000000000000000000da0c730000000000000000000000000000000000000000000000000000000000c1cfef0000000000000000000000000000000000000000000000000000000000c1cc000000000000000000000000000000000000000000000000000000000000c00f800000000000000000000000000000000000000000000000000000000000da0c7f
  | 1, 1 => 0x31c00000000000000000000000000000000000000000000000000000000000003183070000000000000000000000000000000000000000000000000000000000300306c000000000000000000000000000000000000000000000000000000000304300c000000000000000000000000000000000000000000000000000000000303f003000000000000000000000000000000000000000000000000000000000300300000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000000dbcfff
  | 1, 2 => 0x31e307f00000000000000000000000000000000000000000000000000000000031c307f00000000000000000000000000000000000000000000000000000000031c307c00000000000000000000000000000000000000000000000000000000031c307000000000000000000000000000000000000000000000000000000000031c306c00000000000000000000000000000000000000000000000000000000031c300000000000000000000000000000000000000000000000000000000000031c007c00000000000000000000000000000000000000000000000000000000031c006c
  | 1, 3 => 0x301f000000000000000000000000000000000000000000000000000000000000301c000000000000000000000000000000000000000000000000000000000000300338000000000000000000000000000000000000000000000000000000000031c307f00000000000000000000000000000000000000000000000000000000031c307c0000000000000000000000000000000000000000000000000000000003fe3c7c00000000000000000000000000000000000000000000000000000000033df3fc00000000000000000000000000000000000000000000000000000000033c307c
  | 1, 4 => 0x3c03c0000000000000000000000000000000000000000000000000000000000031df3ff00000000000000000000000000000000000000000000000000000000031df07c00000000000000000000000000000000000000000000000000000000031dc3ef00000000000000000000000000000000000000000000000000000000031dc00000000000000000000000000000000000000000000000000000000000031c33fc00000000000000000000000000000000000000000000000000000000031c307c000000000000000000000000000000000000000000000000000000000301f3ef
  | 1, 5 => 0x3e000000000000000000000000000000000000000000000000000000000000003dfffff0000000000000000000000000000000000000000000000000000000003dfc0000000000000000000000000000000000000000000000000000000000003c03f800000000000000000000000000000000000000000000000000000000003de3c7f0000000000000000000000000000000000000000000000000000000003de307c0000000000000000000000000000000000000000000000000000000003de00000000000000000000000000000000000000000000000000000000000003dc3c7c
  | 1, 6 => 0x3e3ff830000000000000000000000000000000000000000000000000000000003e03fff0000000000000000000000000000000000000000000000000000000003e03f800000000000000000000000000000000000000000000000000000000003e03c000000000000000000000000000000000000000000000000000000000003e030000000000000000000000000000000000000000000000000000000000003e00f800000000000000000000000000000000000000000000000000000000003e003800000000000000000000000000000000000000000000000000000000003e0007f
  | 1, 7 => 0x3e1ffef0000000000000000000000000000000000000000000000000000000003e1ff800000000000000000000000000000000000000000000000000000000003e1c3ef0000000000000000000000000000000000000000000000000000000003e1c0000000000000000000000000000000000000000000000000000000000003e03fe30000000000000000000000000000000000000000000000000000000003e03f800000000000000000000000000000000000000000000000000000000003fe3f900000000000000000000000000000000000000000000000000000000003e43f80
  | 1, 8 => 0x3fc3f800000000000000000000000000000000000000000000000000000000003fbffff0000000000000000000000000000000000000000000000000000000003fbc0000000000000000000000000000000000000000000000000000000000003fa3ff30000000000000000000000000000000000000000000000000000000003fa3f800000000000000000000000000000000000000000000000000000000003fa0c730000000000000000000000000000000000000000000000000000000003fa00000000000000000000000000000000000000000000000000000000000003f83ff0
  | 1, 9 => 0x3fff0000000000000000000000000000000000000000000000000000000000003ffcf830000000000000000000000000000000000000000000000000000000003ffc07f0000000000000000000000000000000000000000000000000000000003ffc0100000000000000000000000000000000000000000000000000000000003ffc0000000000000000000000000000000000000000000000000000000000003fe3fff0000000000000000000000000000000000000000000000000000000003fe00000000000000000000000000000000000000000000000000000000000003fc3ffc
  | 1, 10 => 0x3ffc3ef0000000000000000000000000000000000000000000000000000000003ffc3800000000000000000000000000000000000000000000000000000000003ffc06c0000000000000000000000000000000000000000000000000000000003ffc0000000000000000000000000000000000000000000000000000000000003fffc100000000000000000000000000000000000000000000000000000000003fffc000000000000000000000000000000000000000000000000000000000003fff0100000000000000000000000000000000000000000000000000000000003fff38c
  | 1, 11 => 0x3fffc000000000000000000000000000000000000000000000000000000000003fff07c0000000000000000000000000000000000000000000000000000000003fff0000000000000000000000000000000000000000000000000000000000003ffcfff0000000000000000000000000000000000000000000000000000000003ffcc730000000000000000000000000000000000000000000000000000000003ffcc000000000000000000000000000000000000000000000000000000000003ffc0700000000000000000000000000000000000000000000000000000000003ffc000
  | 1, 12 => 0x3fffffc0000000000000000000000000000000000000000000000000000000003ffffef0000000000000000000000000000000000000000000000000000000003ffff800000000000000000000000000000000000000000000000000000000003fffc7f
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3db50000000000000000000000000000000000000000000000000000000000002cb100000000000000000000000000000000000000000000000000000000000015a500000000000000000000000000000000000000000000000000000000000028100000000000000000000000000000000000000000000000000000000000001104000000000000000000000000000000000000000000000000000000000000110400000000000000000000000000000000000000000000000000000000000004810000000000000000000000000000000000000000000000000000000000000000
  | 0, 1 => 0xec04a0000000000000000000000000000000000000000000000000000000000003db50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004800800000000000000000000000000000000000000000000000000000000000240020000000000000000000000000000000000000000000000000000000000003db50000000000000000000000000000000000000000000000000000000000003db50000000000000000000000000000000000000000000000000000000000003db5
  | 0, 2 => 0x21020000000000000000000000000000000000000000000000000000000000000efdff00000000000000000000000000000000000000000000000000000000000efdff00000000000000000000000000000000000000000000000000000000000ec04a00000000000000000000000000000000000000000000000000000000000ec04a00000000000000000000000000000000000000000000000000000000000ec04a00000000000000000000000000000000000000000000000000000000000c804800000000000000000000000000000000000000000000000000000000000a4042
  | 0, 3 => 0x6346830000000000000000000000000000000000000000000000000000000000634683000000000000000000000000000000000000000000000000000000000063468300000000000000000000000000000000000000000000000000000000006342020000000000000000000000000000000000000000000000000000000000634683000000000000000000000000000000000000000000000000000000000061068100000000000000000000000000000000000000000000000000000000004244830000000000000000000000000000000000000000000000000000000000634683
  | 0, 4 => 0x21020000000000000000000000000000000000000000000000000000000000000ec04a0000000000000000000000000000000000000000000000000000000000003db5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006fc24a00000000000000000000000000000000000000000000000000000000006346830000000000000000000000000000000000000000000000000000000000637fb70000000000000000000000000000000000000000000000000000000000637b36
  | 0, 5 => 0x12fd34e00000000000000000000000000000000000000000000000000000000012b5346000000000000000000000000000000000000000000000000000000000125bfbd000000000000000000000000000000000000000000000000000000000125930c00000000000000000000000000000000000000000000000000000000012582080000000000000000000000000000000000000000000000000000000001211304000000000000000000000000000000000000000000000000000000000125930c000000000000000000000000000000000000000000000000000000000104910c
  | 0, 6 => 0x29028100000000000000000000000000000000000000000000000000000000002900000000000000000000000000000000000000000000000000000000000000290281000000000000000000000000000000000000000000000000000000000029028100000000000000000000000000000000000000000000000000000000002902810000000000000000000000000000000000000000000000000000000000167d78f000000000000000000000000000000000000000000000000000000000146d58f000000000000000000000000000000000000000000000000000000000125930c
  | 0, 7 => 0x3b5bb1c0000000000000000000000000000000000000000000000000000000002f36e9300000000000000000000000000000000000000000000000000000000029ee85a00000000000000000000000000000000000000000000000000000000029ee85a0000000000000000000000000000000000000000000000000000000002903db500000000000000000000000000000000000000000000000000000000029015a500000000000000000000000000000000000000000000000000000000029028100000000000000000000000000000000000000000000000000000000002902810
  | 0, 8 => 0x10c916c00000000000000000000000000000000000000000000000000000000010c804800000000000000000000000000000000000000000000000000000000004a44e300000000000000000000000000000000000000000000000000000000004a44e300000000000000000000000000000000000000000000000000000000004004a100000000000000000000000000000000000000000000000000000000000800600000000000000000000000000000000000000000000000000000000003b5bb1c000000000000000000000000000000000000000000000000000000000394b91c
  | 0, 9 => 0x16fc24a00000000000000000000000000000000000000000000000000000000016fd7ef00000000000000000000000000000000000000000000000000000000016d97ed00000000000000000000000000000000000000000000000000000000016b57e700000000000000000000000000000000000000000000000000000000016117a500000000000000000000000000000000000000000000000000000000016117a5000000000000000000000000000000000000000000000000000000000161020000000000000000000000000000000000000000000000000000000000014ed5ef
  | 0, 10 => 0x16fd7ef00000000000000000000000000000000000000000000000000000000016fd7ef00000000000000000000000000000000000000000000000000000000016fd7ef00000000000000000000000000000000000000000000000000000000016fd7ef00000000000000000000000000000000000000000000000000000000016fd7ef00000000000000000000000000000000000000000000000000000000016fd36e00000000000000000000000000000000000000000000000000000000016fc6eb00000000000000000000000000000000000000000000000000000000016fea5a
  | 0, 11 => 0x16fc24a00000000000000000000000000000000000000000000000000000000012d936c00000000000000000000000000000000000000000000000000000000016fd7ef00000000000000000000000000000000000000000000000000000000016fc24a00000000000000000000000000000000000000000000000000000000016fd7ef00000000000000000000000000000000000000000000000000000000016fc24a00000000000000000000000000000000000000000000000000000000016fffff00000000000000000000000000000000000000000000000000000000016fd7ef
  | 0, 12 => 0x2d03db50000000000000000000000000000000000000000000000000000000002d02cb10000000000000000000000000000000000000000000000000000000002da6cf30000000000000000000000000000000000000000000000000000000002b92a7000000000000000000000000000000000000000000000000000000000029828700000000000000000000000000000000000000000000000000000000002980040000000000000000000000000000000000000000000000000000000000290283000000000000000000000000000000000000000000000000000000000016fd7ef
  | 0, 13 => 0x2da6cf30000000000000000000000000000000000000000000000000000000002da68720000000000000000000000000000000000000000000000000000000002da51460000000000000000000000000000000000000000000000000000000002da40420000000000000000000000000000000000000000000000000000000002da6cf30000000000000000000000000000000000000000000000000000000002da6cf30000000000000000000000000000000000000000000000000000000002da6cf30000000000000000000000000000000000000000000000000000000002d26cb3
  | 0, 14 => 0x39cb97c00000000000000000000000000000000000000000000000000000000039cb97c0000000000000000000000000000000000000000000000000000000002da6cf30000000000000000000000000000000000000000000000000000000002fb6ef30000000000000000000000000000000000000000000000000000000002deecfb0000000000000000000000000000000000000000000000000000000002da6cf30000000000000000000000000000000000000000000000000000000002da7df70000000000000000000000000000000000000000000000000000000002da6cf3
  | 0, 15 => 0x3deecfb0000000000000000000000000000000000000000000000000000000003da7df70000000000000000000000000000000000000000000000000000000003d03db50000000000000000000000000000000000000000000000000000000003ffffff0000000000000000000000000000000000000000000000000000000003ffc24a0000000000000000000000000000000000000000000000000000000003ffffff0000000000000000000000000000000000000000000000000000000003f13fb50000000000000000000000000000000000000000000000000000000003defdff
  | 1, 0 => 0x3ffeefb0000000000000000000000000000000000000000000000000000000003ffc24a0000000000000000000000000000000000000000000000000000000003fb7ff70000000000000000000000000000000000000000000000000000000003fb6ef30000000000000000000000000000000000000000000000000000000003ffffff0000000000000000000000000000000000000000000000000000000003ffeefb0000000000000000000000000000000000000000000000000000000003f13fb50000000000000000000000000000000000000000000000000000000003defdff
  | 1, 1 => 0x39c8048000000000000000000000000000000000000000000000000000000000398397400000000000000000000000000000000000000000000000000000000039cb97c000000000000000000000000000000000000000000000000000000000394b93c0000000000000000000000000000000000000000000000000000000003927936000000000000000000000000000000000000000000000000000000000390393400000000000000000000000000000000000000000000000000000000039000000000000000000000000000000000000000000000000000000000000003ffffff
  | 1, 2 => 0x39ef97e00000000000000000000000000000000000000000000000000000000039cb97c00000000000000000000000000000000000000000000000000000000039cb97c00000000000000000000000000000000000000000000000000000000039cb97c00000000000000000000000000000000000000000000000000000000039cb97c00000000000000000000000000000000000000000000000000000000039cb97c00000000000000000000000000000000000000000000000000000000039cb97c00000000000000000000000000000000000000000000000000000000039c916c
  | 1, 3 => 0x3fffb7e0000000000000000000000000000000000000000000000000000000003ffc24a0000000000000000000000000000000000000000000000000000000003f13fb50000000000000000000000000000000000000000000000000000000003defdff0000000000000000000000000000000000000000000000000000000003def97e00000000000000000000000000000000000000000000000000000000039cb97c0000000000000000000000000000000000000000000000000000000003bdbb7c00000000000000000000000000000000000000000000000000000000039cb97c
  | 1, 4 => 0x3d03db50000000000000000000000000000000000000000000000000000000003ffffff0000000000000000000000000000000000000000000000000000000003fffb7e0000000000000000000000000000000000000000000000000000000003ffd7ef0000000000000000000000000000000000000000000000000000000003ffc24a0000000000000000000000000000000000000000000000000000000003fdbffd0000000000000000000000000000000000000000000000000000000003fdbb7c0000000000000000000000000000000000000000000000000000000003ffffff
  | 1, 5 => 0x3f102000000000000000000000000000000000000000000000000000000000003ffffff0000000000000000000000000000000000000000000000000000000003ffc24a0000000000000000000000000000000000000000000000000000000003f13fb50000000000000000000000000000000000000000000000000000000003defdff0000000000000000000000000000000000000000000000000000000003def97e0000000000000000000000000000000000000000000000000000000003dec04a0000000000000000000000000000000000000000000000000000000003dcbdfd
  | 1, 6 => 0x3f37fb70000000000000000000000000000000000000000000000000000000003f13fb50000000000000000000000000000000000000000000000000000000003f13fb50000000000000000000000000000000000000000000000000000000003f13fb50000000000000000000000000000000000000000000000000000000003f13b340000000000000000000000000000000000000000000000000000000003f13fb50000000000000000000000000000000000000000000000000000000003f117a50000000000000000000000000000000000000000000000000000000003f10200
  | 1, 7 => 0x3ffffff0000000000000000000000000000000000000000000000000000000003ffffff0000000000000000000000000000000000000000000000000000000003ffd7ef0000000000000000000000000000000000000000000000000000000003ffc24a0000000000000000000000000000000000000000000000000000000003fb7ff70000000000000000000000000000000000000000000000000000000003fb7ff70000000000000000000000000000000000000000000000000000000003f13fb50000000000000000000000000000000000000000000000000000000003f13fb5
  | 1, 8 => 0x3fdbffd0000000000000000000000000000000000000000000000000000000003ffffff0000000000000000000000000000000000000000000000000000000003ffc24a0000000000000000000000000000000000000000000000000000000003fb7ff70000000000000000000000000000000000000000000000000000000003fb7ff70000000000000000000000000000000000000000000000000000000003fb6ef30000000000000000000000000000000000000000000000000000000003fb42420000000000000000000000000000000000000000000000000000000003f93ff5
  | 1, 9 => 0x3ffc24a0000000000000000000000000000000000000000000000000000000003ffc6cb0000000000000000000000000000000000000000000000000000000003ffc24a0000000000000000000000000000000000000000000000000000000003ffc24a0000000000000000000000000000000000000000000000000000000003ffc24a0000000000000000000000000000000000000000000000000000000003ffffff0000000000000000000000000000000000000000000000000000000003ffc24a0000000000000000000000000000000000000000000000000000000003fdbffd
  | 1, 10 => 0x3ffd7ef0000000000000000000000000000000000000000000000000000000003ffd7ef0000000000000000000000000000000000000000000000000000000003ffd36e0000000000000000000000000000000000000000000000000000000003ffc6eb0000000000000000000000000000000000000000000000000000000003ffea5a0000000000000000000000000000000000000000000000000000000003ffea5a0000000000000000000000000000000000000000000000000000000003ffea5a0000000000000000000000000000000000000000000000000000000003ffd34e
  | 1, 11 => 0x3ffffff0000000000000000000000000000000000000000000000000000000003fffb7e0000000000000000000000000000000000000000000000000000000003fffb7e0000000000000000000000000000000000000000000000000000000003ffffff0000000000000000000000000000000000000000000000000000000003ffeefb0000000000000000000000000000000000000000000000000000000003ffeefb0000000000000000000000000000000000000000000000000000000003ffea7a0000000000000000000000000000000000000000000000000000000003ffea7a
  | 1, 12 => 0x3ffffff0000000000000000000000000000000000000000000000000000000003ffffff0000000000000000000000000000000000000000000000000000000003ffffff0000000000000000000000000000000000000000000000000000000003ffffff
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 228 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 228 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 228 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 228 then wireAt i else 0
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
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 5 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 5 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 5 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 16 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_16 : ∀ i, 16 ≤ i → i < 32 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_32 : ∀ i, 32 ≤ i → i < 44 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 12 32 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 44 → Z 4 i = true := (range_split (range_split z4_0 z4_16) z4_32)
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
private theorem z5_112 : ∀ i, 112 ≤ i → i < 128 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_128 : ∀ i, 128 ≤ i → i < 144 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_144 : ∀ i, 144 ≤ i → i < 160 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_160 : ∀ i, 160 ≤ i → i < 176 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 160 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_176 : ∀ i, 176 ≤ i → i < 192 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 176 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_192 : ∀ i, 192 ≤ i → i < 208 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 192 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_208 : ∀ i, 208 ≤ i → i < 224 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 208 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_224 : ∀ i, 224 ≤ i → i < 240 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 224 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_240 : ∀ i, 240 ≤ i → i < 256 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 240 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_256 : ∀ i, 256 ≤ i → i < 272 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 256 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_272 : ∀ i, 272 ≤ i → i < 288 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 272 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_288 : ∀ i, 288 ≤ i → i < 292 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 4 288 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 292 → Z 5 i = true := (range_split (range_split (range_split (range_split (range_split z5_0 z5_16) (range_split z5_32 z5_48)) (range_split (range_split z5_64 z5_80) (range_split z5_96 z5_112))) (range_split (range_split (range_split z5_128 z5_144) (range_split z5_160 z5_176)) (range_split (range_split z5_192 z5_208) (range_split z5_224 z5_240)))) (range_split (range_split z5_256 z5_272) z5_288))
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
private theorem z6_288 : ∀ i, 288 ≤ i → i < 301 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 13 288 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 301 → Z 6 i = true := (range_split (range_split (range_split (range_split (range_split z6_0 z6_16) (range_split z6_32 z6_48)) (range_split (range_split z6_64 z6_80) (range_split z6_96 z6_112))) (range_split (range_split (range_split z6_128 z6_144) (range_split z6_160 z6_176)) (range_split (range_split z6_192 z6_208) (range_split z6_224 z6_240)))) (range_split (range_split z6_256 z6_272) z6_288))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : ∀ i, 0 ≤ i → i < 16 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_16 : ∀ i, 16 ≤ i → i < 24 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 16 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 24 → Z 7 i = true := (range_split z7_0 z7_16)
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
  scr dom_61 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 8) (h : RunD dom_61 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_61 roots_61 goal_61 9 := by
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

theorem low_61 : Lower dom_61 roots_61 goal_61 9 := S_61.noCircuit

namespace S_31
def pairsG : List (Nat × Nat) := [(1, 3), (2, 3), (2, 6), (2, 10), (4, 6), (5, 7), (5, 21), (8, 10), (9, 11), (9, 25), (12, 14), (12, 28), (13, 15), (13, 29), (17, 19), (17, 21), (17, 25), (18, 19), (18, 22), (18, 26), (20, 21), (20, 22), (20, 28), (24, 25), (24, 26), (24, 28)]
def r1sG : List Nat := [1, 2, 2, 2, 4, 5, 5, 8, 9, 9, 12, 12, 13, 13, 17, 17, 17, 18, 18, 18, 20, 20, 20, 24, 24, 24]
def r2sG : List Nat := [3, 3, 6, 10, 6, 7, 21, 10, 11, 25, 14, 28, 15, 29, 19, 21, 25, 19, 22, 26, 21, 22, 28, 25, 26, 28]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [18700624528899, 5506434663174, 4407040936454, 8804969808650, 5506484995587, 9904598878723, 2203655214339, 22063280947989, 13203133958662, 19864628238613, 18700691900931, 22063651494165, 26461327721241, 9904481436426, 13203066848778, 26397155853066, 26474212623900, 21999109079814]
def xsM : List Nat := roots_31.map (· &&& dom_31)
def goalM : Nat := goal_31 &&& dom_31
def NN : Nat → Nat
  | 4 => 4
  | 5 => 26
  | 6 => 16
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xc1904e78ac05225e419149242c1123fc
  | 5, 0 => 0xd75027cad68db2b9c56e12e7c5159104be3fb924ac05225ea289336e89c6729288a34107778bdbcc537bfbe7526e44fc4ca6240746836c3c4166ee5a3b937b233a6b8d412b6753152637312d1edc73cf1ac7d7cf192cbc4f158632870ceda7c808a43bb305f246af
  | 6, 0 => 0xd051f507ce00c9b9c5159104be3fb924ba7741d8ac05225e7ecfa183778bdbcc3a6b8d4130706e42276bea4325303d37206585ea1b8a7ef1126b25b70241d3e1
  | 7, 0 => 0xac05225e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xa0a0a0a000000000000000000000000000000000000000000000000000000000888888880000000000000000000000000000000000000000000000000000000055555555000000000000000000000000000000000000000000000000000000003333333300000000000000000000000000000000000000000000000000000000333300000000000000000000000000000000000000000000000000000000000000ff00ff000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000000000000000000000000000000000003333
  | 0, 1 => 0xf000f00000000000000000000000000000000000000000000000000000000000eeeeeeee00000000000000000000000000000000000000000000000000000000ccccffff00000000000000000000000000000000000000000000000000000000cccccccc00000000000000000000000000000000000000000000000000000000cccc000000000000000000000000000000000000000000000000000000000000cc00cc0000000000000000000000000000000000000000000000000000000000aaaaaaaa00000000000000000000000000000000000000000000000000000000aaaa8888
  | 0, 2 => 0xffaaffaa00000000000000000000000000000000000000000000000000000000ffaa000000000000000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000ff00cc0000000000000000000000000000000000000000000000000000000000fafafafa00000000000000000000000000000000000000000000000000000000faaafaaa00000000000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000f0f00000
  | 0, 3 => 0xfffff0f000000000000000000000000000000000000000000000000000000000ffffcccc00000000000000000000000000000000000000000000000000000000ffffc0c000000000000000000000000000000000000000000000000000000000ffffaaaa00000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000fff0fff000000000000000000000000000000000000000000000000000000000ffccffcc00000000000000000000000000000000000000000000000000000000ffc0ffc0
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0xdeaf362eeb162541bd49880a45884
  | 5, 0, 0 => 0x562c28541bac5c6506eb1291416ac589506e9162541dac589506eb16154158a483506eb361d4158b120506e2c2894158b123506f1162541ea4589506eb28b141eac5855
  | 5, 0, 1 => 0x562920541fac189507ab15a54158b121506eb149141bac58950562d62541eac5245ddeb38b181eac5895
  | 6, 0, 0 => 0xdd62c495bdbac58960562c48541bac5245dd62c5a581bac5895dd62c49181eac589506eb1615779ac5896e6eb1625b758bd896dd671625b758b1216dd62c525b758c1896
  | 7, 0, 0 => 0x1bac5895
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 29
  | 5 => 34
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
  | 0, 0 => 0x306000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003fe0c9e0000000000000000000000000000000000000000000000000000000003f1fff10000000000000000000000000000000000000000000000000000000003f1c00000000000000000000000000000000000000000000000000000000000007fc07f0000000000000000000000000000000000000000000000000000000000003fff0000000000000000000000000000000000000000000000000000000000003ff1
  | 0, 1 => 0x3c0000000000000000000000000000000000000000000000000000000000000ff36f00000000000000000000000000000000000000000000000000000000000e3fff00000000000000000000000000000000000000000000000000000000000e000e00000000000000000000000000000000000000000000000000000000000e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001f361000000000000000000000000000000000000000000000000000000000001c000
  | 0, 2 => 0x381ffe1000000000000000000000000000000000000000000000000000000000381c0000000000000000000000000000000000000000000000000000000000003803f800000000000000000000000000000000000000000000000000000000003800000000000000000000000000000000000000000000000000000000000000071ff71000000000000000000000000000000000000000000000000000000000001ff610000000000000000000000000000000000000000000000000000000000703c700000000000000000000000000000000000000000000000000000000000700000
  | 0, 3 => 0x3fffc700000000000000000000000000000000000000000000000000000000003ffc00e0000000000000000000000000000000000000000000000000000000003ffc0000000000000000000000000000000000000000000000000000000000003fff3610000000000000000000000000000000000000000000000000000000003ffc0000000000000000000000000000000000000000000000000000000000003f03ff000000000000000000000000000000000000000000000000000000000038e3f8e0000000000000000000000000000000000000000000000000000000003803f80
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x10b060000000000000000000000000000000000000000000000000000000000002512300000000000000000000000000000000000000000000000000000000036c0c9c0000000000000000000000000000000000000000000000000000000002d1aa400000000000000000000000000000000000000000000000000000000002d1aa40000000000000000000000000000000000000000000000000000000000036c07700000000000000000000000000000000000000000000000000000000000015bf0000000000000000000000000000000000000000000000000000000000000000
  | 0, 1 => 0x2403c000000000000000000000000000000000000000000000000000000000001bff7ff00000000000000000000000000000000000000000000000000000000012e55bf00000000000000000000000000000000000000000000000000000000012e55bf00000000000000000000000000000000000000000000000000000000012e40000000000000000000000000000000000000000000000000000000000001081588000000000000000000000000000000000000000000000000000000000093f363000000000000000000000000000000000000000000000000000000000093f363
  | 0, 2 => 0x3dbffeb0000000000000000000000000000000000000000000000000000000003dbea400000000000000000000000000000000000000000000000000000000003c93f880000000000000000000000000000000000000000000000000000000003c93f880000000000000000000000000000000000000000000000000000000002f7ff770000000000000000000000000000000000000000000000000000000002d3ff63000000000000000000000000000000000000000000000000000000000274bc74000000000000000000000000000000000000000000000000000000000274a840
  | 0, 3 => 0x3fffe740000000000000000000000000000000000000000000000000000000003ffffff0000000000000000000000000000000000000000000000000000000003fffe740000000000000000000000000000000000000000000000000000000003fffb630000000000000000000000000000000000000000000000000000000003ffea400000000000000000000000000000000000000000000000000000000003fdbffc0000000000000000000000000000000000000000000000000000000003ef7fbf0000000000000000000000000000000000000000000000000000000003ed3fbc
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 32 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 32 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 32 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 32 then wireAt i else 0
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_31 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_31 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]]
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

namespace S_31_32
def pairsG : List (Nat × Nat) := [(33, 35), (33, 37), (33, 41), (33, 49), (34, 35), (34, 38), (34, 42), (36, 37), (36, 38), (40, 41), (40, 42), (44, 45), (44, 46), (44, 60), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [33, 33, 33, 33, 34, 34, 34, 36, 36, 40, 40, 44, 44, 44, 48, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [35, 37, 41, 49, 35, 38, 42, 37, 38, 41, 42, 45, 46, 60, 49, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0xffffff
def pool6G : List Nat := [39724725445413, 61796545799484, 48521121899817, 37525803116835, 48521189009701, 48525416867370, 48525483977254, 61715127215409, 57321576999462, 44122772218665, 39729003569958, 57317080704305]
def xsM : List Nat := roots_31_32.map (· &&& dom_31_32)
def goalM : Nat := goal_31_32 &&& dom_31_32
def NN : Nat → Nat
  | 4 => 4
  | 5 => 39
  | 6 => 24
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x6151fc205f5ce3514c6cbb0146df9ed9
  | 5, 0 => 0xef068884dc1b0d52d93e3f7dcd07a878cce3300ecbe6991bcbba9a76bac05386b8694a06b740b46eb10a609b98c2c66d940d634889c9bc08891d1cfd77dc40c7764c6cf37523d75b7402c7fe643ce693636d008b608578e95fef68c05f5ce3515afe272753cc152d3c29922b3a877c602c8bb197239e6b931d05c19c1c4825ff1b8092ea0e094e0c0c9503e809f3bf120467640c034654af02a103ae
  | 6, 0 => 0xdb85cf97ccc7d25dcbba9a76c6e47c5fb740b46ea3321dd28f19090277186efb7523d75b7402c7fe6b1890e067e5bb3d608578e95f5ce351531e2a99527e04584fbea8484995ef473c415933358964b82f5e14ef273b926c1dcf2103059706fd
  | 7, 0 => 0x5f5ce351
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x88888888000000000000000000000000000000000000000000000000000000005555555500000000000000000000000000000000000000000000000000000000333333330000000000000000000000000000000000000000000000000000000033330000000000000000000000000000000000000000000000000000000000000f0f0f0f0000000000000000000000000000000000000000000000000000000000ff00ff000000000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000333300000000
  | 0, 1 => 0xccccffff00000000000000000000000000000000000000000000000000000000cccccccc00000000000000000000000000000000000000000000000000000000cccc000000000000000000000000000000000000000000000000000000000000c0c0c0c000000000000000000000000000000000000000000000000000000000aaaaaaaa00000000000000000000000000000000000000000000000000000000aaaa000000000000000000000000000000000000000000000000000000000000aa00aa0000000000000000000000000000000000000000000000000000000000a0a0a0a000000000
  | 0, 2 => 0xf0f0f0f000000000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000eeeeeeee00000000000000000000000000000000000000000000000000000000eeeecccc00000000000000000000000000000000000000000000000000000000eecceecc00000000000000000000000000000000000000000000000000000000eeaaeeaa00000000000000000000000000000000000000000000000000000000ecececec00000000
  | 0, 3 => 0xffaaff0000000000000000000000000000000000000000000000000000000000ffaa000000000000000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000fcfcfcfc00000000000000000000000000000000000000000000000000000000fcf0fcf000000000000000000000000000000000000000000000000000000000faf0faf000000000000000000000000000000000000000000000000000000000f8f8f8f800000000
  | 0, 4 => 0xffffc0c000000000000000000000000000000000000000000000000000000000ffffaaaa00000000000000000000000000000000000000000000000000000000ffffaa0000000000000000000000000000000000000000000000000000000000ffff888800000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000fff0fff000000000000000000000000000000000000000000000000000000000ffccffcc00000000000000000000000000000000000000000000000000000000ffaaffaa00000000
  | 0, 5 => 0xfffff0f000000000000000000000000000000000000000000000000000000000ffffcccc00000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x23758512375738b502385745008e05d24
  | 5, 0, 0 => 0x8dd5ce2d6338b0c258dd68e2d5d5ce2c458dd6cc2d637574cb58d72c5096475738b57573ce2d6375744e58dd64e2d637d738b58e05ce256374e1835a1d38b0d6775738b5
  | 5, 0, 1 => 0x8dd60e2d5d5cb14158dd5cb156975638b599d5ce295d5cb1445a1d5ce196575738b58e254e2d5d5ce18158dd5ce196875738b58dd5d02d6875734b575738b055e75738b5
  | 5, 0, 2 => 0x2875750b58dd5d41d5d5ce2c058dd5c6155738b0815a1d5cb15635ce2c25
  | 6, 0, 0 => 0x23757386502875738b58dd5d538b68dd5ce2c2601d5ce2c1502375738b58e075738b68dd5d438b6a2375738b68dd5ce2c668dd5ce2c168dd5ce2c768dd5ce2c56a6375738b68dd5ce30b68dd71738b6
  | 6, 0, 1 => 0x8dd5ce2ca69a375738b60235ce2c258dd5ce34b60237572c558e275738b68dd6d738b68dd5ce2c86
  | 7, 0, 0 => 0x2375738b5
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
  | 0, 0 => 0xfffff00000000000000000000000000000000000000000000000000000000000fc7f8f0000000000000000000000000000000000000000000000000000000000fc40000000000000000000000000000000000000000000000000000000000000e3c67f00000000000000000000000000000000000000000000000000000000001fc1ff0000000000000000000000000000000000000000000000000000000000003fff0000000000000000000000000000000000000000000000000000000000003f8f
  | 0, 1 => 0x3bfff000000000000000000000000000000000000000000000000000000000003807000000000000000000000000000000000000000000000000000000000000380000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 0, 2 => 0x1c398000000000000000000000000000000000000000000000000000000000001c00000000000000000000000000000000000000000000000000000000000000003800000000000000000000000000000000000000000000000000000000000003807f00000000000000000000000000000000000000000000000000000000000380700000000000000000000000000000000000000000000000000000000000038070000000000000000000000000000000000000000000000000000000000000000f0000000000000000000000000000000000000000000000000000000000038070
  | 0, 3 => 0xe03e000000000000000000000000000000000000000000000000000000000000e000000000000000000000000000000000000000000000000000000000000000e03e000000000000000000000000000000000000000000000000000000000000e0000000000000000000000000000000000000000000000000000000000000001fb9f000000000000000000000000000000000000000000000000000000000001c398000000000000000000000000000000000000000000000000000000000001c398000000000000000000000000000000000000000000000000000000000001c3980
  | 0, 4 => 0xffc0000000000000000000000000000000000000000000000000000000000000ffc00f0000000000000000000000000000000000000000000000000000000000ffc0000000000000000000000000000000000000000000000000000000000000ffc0000000000000000000000000000000000000000000000000000000000000ffc0000000000000000000000000000000000000000000000000000000000000fc3f800000000000000000000000000000000000000000000000000000000000e3be700000000000000000000000000000000000000000000000000000000000e03e0f
  | 0, 5 => 0xfff9800000000000000000000000000000000000000000000000000000000000ffc070
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x80110000000000000000000000000000000000000000000000000000000000db35600000000000000000000000000000000000000000000000000000000000b46a8e0000000000000000000000000000000000000000000000000000000000b46008000000000000000000000000000000000000000000000000000000000062c65d00000000000000000000000000000000000000000000000000000000000dc1bb0000000000000000000000000000000000000000000000000000000000001ff70000000000000000000000000000000000000000000000000000000000000a86
  | 0, 1 => 0x4b9ff700000000000000000000000000000000000000000000000000000000004b957100000000000000000000000000000000000000000000000000000000004b80000000000000000000000000000000000000000000000000000000000000091120000000000000000000000000000000000000000000000000000000000024ca9f000000000000000000000000000000000000000000000000000000000024c0080000000000000000000000000000000000000000000000000000000000200a040000000000000000000000000000000000000000000000000000000000040882
  | 0, 2 => 0x9d39a200000000000000000000000000000000000000000000000000000000009d2000000000000000000000000000000000000000000000000000000000000090380000000000000000000000000000000000000000000000000000000000006fdfff00000000000000000000000000000000000000000000000000000000006fd57900000000000000000000000000000000000000000000000000000000006b9f75000000000000000000000000000000000000000000000000000000000066dedf00000000000000000000000000000000000000000000000000000000004f9df3
  | 0, 3 => 0xf6fe4c0000000000000000000000000000000000000000000000000000000000f6e0080000000000000000000000000000000000000000000000000000000000f23e440000000000000000000000000000000000000000000000000000000000f220000000000000000000000000000000000000000000000000000000000000dfbdf30000000000000000000000000000000000000000000000000000000000df3de20000000000000000000000000000000000000000000000000000000000bd3ba600000000000000000000000000000000000000000000000000000000009db9b3
  | 0, 4 => 0xfff1280000000000000000000000000000000000000000000000000000000000ffea9f0000000000000000000000000000000000000000000000000000000000ffea0c0000000000000000000000000000000000000000000000000000000000ffe0190000000000000000000000000000000000000000000000000000000000ffe0080000000000000000000000000000000000000000000000000000000000ff3fe60000000000000000000000000000000000000000000000000000000000fbbf750000000000000000000000000000000000000000000000000000000000f6fedf
  | 0, 5 => 0xfff9aa0000000000000000000000000000000000000000000000000000000000fff579
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

namespace S_55
def pairsG : List (Nat × Nat) := [(1, 3), (2, 3), (2, 6), (4, 6), (5, 7), (5, 21), (5, 37), (17, 19), (17, 21), (17, 49), (18, 19), (18, 22), (20, 21), (20, 22), (33, 35), (33, 37), (33, 49), (34, 35), (34, 38), (36, 37), (36, 38), (48, 49), (50, 51), (50, 54), (52, 53), (52, 54)]
def r1sG : List Nat := [1, 2, 2, 4, 5, 5, 5, 17, 17, 17, 18, 18, 20, 20, 33, 33, 33, 34, 34, 36, 36, 48, 50, 50, 52, 52]
def r2sG : List Nat := [3, 3, 6, 6, 7, 21, 37, 19, 21, 49, 19, 22, 21, 22, 35, 37, 49, 35, 38, 37, 38, 49, 51, 54, 53, 54]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [2203924628995, 2203655144963, 18700624528899, 36293080057347, 5506434663174, 18713729377557, 2204193850883, 5506484995587, 36356984476977, 39724186469157, 4407192519430]
def xsM : List Nat := roots_55.map (· &&& dom_55)
def goalM : Nat := goal_55 &&& dom_55
def NN : Nat → Nat
  | 3 => 1
  | 4 => 3
  | 5 => 54
  | 6 => 25
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x8a75e717
  | 4, 0 => 0x47baa0702b0e32a10728bfe5
  | 5, 0 => 0xfd05eeb0f154aa00e81a7d20e7a1edd4c93c0113c8c371c7ba0ba89ab6f3eb28b50fb2d6b4c0e045af452846ae2f9285a570c60fa4f836c3a2399ad197b5c1248a64578186d4643b853384616f56f6da6e8fe3356b85db74628184da5dbf3d605abc144f5a43850356c06ab355a1e42b54c5e1114cd9999447baa070447a08c6402287963fafa5c13ee8921c3d0687ed3c32f590385234e72a462135286ec0bb28206f8327c978c2246a2e1a20d129b417493eed1638e054132e963711c6c4520fd3edf5066ead8103f5f65303eb5def02ae5c62017c9d5c
  | 6, 0 => 0xfd05eeb0e0d44139c9d5353ac2948086ba0ba89aa570c60fa4f836c392c817469034ec5b8a64578188ca29be6b85db7469ad9211514fa09150eeb30f47baa0704642573735e497682f17f7c4290a2e9c27ca5be020b49e3817bdcd4415dbc31515521a2e
  | 7, 0 => 0x47baa070
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x3300330033003300000000000000000000000000000000000000000000000000330033000000000000000000000000000000000000000000000000000000000033000000330000000000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000aa000000aa00000000000000000000000000000000000000000000000000000033000000330000000000000000000000000000000000000000000000000000000000ff00ff
  | 0, 1 => 0xaa00aa00aa00aa00000000000000000000000000000000000000000000000000aa00aa0088008800000000000000000000000000000000000000000000000000aa00aa0000000000000000000000000000000000000000000000000000000000aa000000aa000000000000000000000000000000000000000000000000000000a000a000a000a000000000000000000000000000000000000000000000000000880088008800880000000000000000000000000000000000000000000000000055005500ff00ff0000000000000000000000000000000000000000000000000055005500550055
  | 0, 2 => 0xee000000ee000000000000000000000000000000000000000000000000000000ea00ea00ea00ea00000000000000000000000000000000000000000000000000e000e000e000e000000000000000000000000000000000000000000000000000cc00cc00ff00ff00000000000000000000000000000000000000000000000000cc00cc00cc00cc00000000000000000000000000000000000000000000000000cc000000cc000000000000000000000000000000000000000000000000000000c800c800c800c800000000000000000000000000000000000000000000000000c000c000c000c0
  | 0, 3 => 0xfa000000fa000000000000000000000000000000000000000000000000000000f800f800f800f800000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000f0000000f0000000000000000000000000000000000000000000000000000000ee00ee00ee00ee00000000000000000000000000000000000000000000000000ee00ee00cc00cc00000000000000000000000000000000000000000000000000ee00cc00ee00cc
  | 0, 4 => 0xff008800ff008800000000000000000000000000000000000000000000000000ff005500ff005500000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000ff000000f0000000000000000000000000000000000000000000000000000000ff000000aa000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000fc00fc00fc00fc00000000000000000000000000000000000000000000000000fa00fa00fa00fa
  | 0, 5 => 0xff00ff00cc00cc00000000000000000000000000000000000000000000000000ff00ff00cc000000000000000000000000000000000000000000000000000000ff00ff00c000c000000000000000000000000000000000000000000000000000ff00ff0055005500000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000ff00f000ff000000000000000000000000000000000000000000000000000000ff00cc00ff00cc00000000000000000000000000000000000000000000000000ff00aa00ff00aa
  | 0, 6 => 0xff00ff00ff000000000000000000000000000000000000000000000000000000ff00ff00f000f0
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x1d60e3
  | 4, 0, 0 => 0x2b95d4cf501d4ce3100a5d64f4
  | 5, 0, 0 => 0xae47533d697533c05ae575a296f7533cc5b25753216b4cf1035be5753216e95d4cf57533cd316d95d4cf595d3c7197095c4cf5ae37533d6b95d593595d4cd216b7533c15
  | 5, 0, 1 => 0xae77533d6b99d4cf59533cd116b9532045aea7533d6b96140f5ae58132d6b95d44f5ae57533d657544cf595d4cf396b94f1c45ae974f1d6ba5d48f595d4cf256b7574cf5
  | 5, 0, 2 => 0xbe57533d6b7533c25ae55533d6ba1d4cc5adf7533d6b74f1c3595d4cf356b95d4c85add6133d5d4cf0c05ae574f1d7189d4cf5add4cf156f9533c45be97533d6b7533c35
  | 5, 0, 3 => 0xae54cf116b95e4cf595d3cd1d6b95d20757533cd0d6b7532035
  | 6, 0, 0 => 0x2b95d3c75c6b95d4cf602b7533c35ae575340f6ae57533c46ae575a4cf602b95d4cf5ae57533c36c2b95d4cf6ae57533ca6ae589d4cf6ae57533c86ae575b4cf6ae57533c76ae575348f6ae585d4cf6
  | 6, 0, 1 => 0x2b9533c45ae57533cb6ae895d4cf6beb95d4cf602f95d4cf50257533cd502b95d4c85ae581d4cf6ae57533cc6
  | 7, 0, 0 => 0x2b95d4cf5
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 22
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
  | 0, 0 => 0x339f3f9000000000000000000000000000000000000000000000000000000000339c00000000000000000000000000000000000000000000000000000000000032033800000000000000000000000000000000000000000000000000000000000e7cf8700000000000000000000000000000000000000000000000000000000001fc07f000000000000000000000000000000000000000000000000000000000001c071000000000000000000000000000000000000000000000000000000000019c0790000000000000000000000000000000000000000000000000000000000003fff
  | 0, 1 => 0x1c3f1000000000000000000000000000000000000000000000000000000000001c000000000000000000000000000000000000000000000000000000000000001c0000000000000000000000000000000000000000000000000000000000000000380000000000000000000000000000000000000000000000000000000000000007000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003fe3fff0000000000000000000000000000000000000000000000000000000003fe3c0e
  | 0, 2 => 0xc00f80000000000000000000000000000000000000000000000000000000000001c3f100000000000000000000000000000000000000000000000000000000000000700000000000000000000000000000000000000000000000000000000000c63fff0000000000000000000000000000000000000000000000000000000000c60c060000000000000000000000000000000000000000000000000000000000c00c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 0, 3 => 0x300338000000000000000000000000000000000000000000000000000000000031830780000000000000000000000000000000000000000000000000000000003183078000000000000000000000000000000000000000000000000000000000318000000000000000000000000000000000000000000000000000000000000030030000000000000000000000000000000000000000000000000000000000000c7cff70000000000000000000000000000000000000000000000000000000000c7cc060000000000000000000000000000000000000000000000000000000000c60f86
  | 0, 4 => 0x3e03f800000000000000000000000000000000000000000000000000000000003fe3f8e0000000000000000000000000000000000000000000000000000000003e03f800000000000000000000000000000000000000000000000000000000003e030000000000000000000000000000000000000000000000000000000000003e003800000000000000000000000000000000000000000000000000000000003e000000000000000000000000000000000000000000000000000000000000003de3c7e000000000000000000000000000000000000000000000000000000000319f3f9
  | 0, 5 => 0x3ffcc060000000000000000000000000000000000000000000000000000000003ffcc000000000000000000000000000000000000000000000000000000000003ffc0000000000000000000000000000000000000000000000000000000000003fffc0e0000000000000000000000000000000000000000000000000000000003ffc0000000000000000000000000000000000000000000000000000000000003f83f800000000000000000000000000000000000000000000000000000000003e63f860000000000000000000000000000000000000000000000000000000003e1fff1
  | 0, 6 => 0x3ffff800000000000000000000000000000000000000000000000000000000003fff078
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x129936000000000000000000000000000000000000000000000000000000000012982400000000000000000000000000000000000000000000000000000000001211320000000000000000000000000000000000000000000000000000000000063468300000000000000000000000000000000000000000000000000000000001ec05f00000000000000000000000000000000000000000000000000000000000ac05300000000000000000000000000000000000000000000000000000000000880400000000000000000000000000000000000000000000000000000000000003dbf
  | 0, 1 => 0x16bd7f300000000000000000000000000000000000000000000000000000000016bc6d300000000000000000000000000000000000000000000000000000000016bc24000000000000000000000000000000000000000000000000000000000016117a0000000000000000000000000000000000000000000000000000000000108917000000000000000000000000000000000000000000000000000000000004244930000000000000000000000000000000000000000000000000000000002943dbf000000000000000000000000000000000000000000000000000000000294280c
  | 0, 2 => 0x3e13fa00000000000000000000000000000000000000000000000000000000003ffffff00000000000000000000000000000000000000000000000000000000039cb97c0000000000000000000000000000000000000000000000000000000002d67dbf0000000000000000000000000000000000000000000000000000000002d66c9f0000000000000000000000000000000000000000000000000000000002c02c800000000000000000000000000000000000000000000000000000000002d66c9f000000000000000000000000000000000000000000000000000000000294281c
  | 0, 3 => 0x3e13fa00000000000000000000000000000000000000000000000000000000003defdff00000000000000000000000000000000000000000000000000000000039cb97c00000000000000000000000000000000000000000000000000000000039c804000000000000000000000000000000000000000000000000000000000038039200000000000000000000000000000000000000000000000000000000003ffffff0000000000000000000000000000000000000000000000000000000003ffeedf0000000000000000000000000000000000000000000000000000000003f77fbf
  | 0, 4 => 0x3e37fb30000000000000000000000000000000000000000000000000000000003f53fac0000000000000000000000000000000000000000000000000000000003e13fa00000000000000000000000000000000000000000000000000000000003e13b200000000000000000000000000000000000000000000000000000000003e117a00000000000000000000000000000000000000000000000000000000003e102000000000000000000000000000000000000000000000000000000000003defdff0000000000000000000000000000000000000000000000000000000003ffffff
  | 0, 5 => 0x3ffeedf0000000000000000000000000000000000000000000000000000000003ffeec00000000000000000000000000000000000000000000000000000000003ffea5c0000000000000000000000000000000000000000000000000000000003ffea4c0000000000000000000000000000000000000000000000000000000003ffc2400000000000000000000000000000000000000000000000000000000003fdbfe00000000000000000000000000000000000000000000000000000000003f77fbf0000000000000000000000000000000000000000000000000000000003ebfff3
  | 0, 6 => 0x3ffffe00000000000000000000000000000000000000000000000000000000003fffb7c
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 50 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 50 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 50 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 50 then wireAt i else 0
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
private theorem z5_0 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_16 : ∀ i, 16 ≤ i → i < 32 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_32 : ∀ i, 32 ≤ i → i < 48 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_48 : ∀ i, 48 ≤ i → i < 54 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 48 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 54 → Z 5 i = true := (range_split (range_split z5_0 z5_16) (range_split z5_32 z5_48))
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
  scr dom_55 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_55 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_55 roots_55 goal_55 8 := by
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

theorem low_55 : Lower dom_55 roots_55 goal_55 8 := S_55.noCircuit

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

namespace S_47
def pairsG : List (Nat × Nat) := [(1, 3), (2, 3), (2, 6), (2, 10), (4, 6), (5, 7), (5, 37), (8, 10), (9, 11), (9, 41), (12, 14), (13, 15), (13, 45), (33, 35), (33, 37), (33, 41), (34, 35), (34, 38), (34, 42), (36, 37), (36, 38), (40, 41), (40, 42), (44, 45), (44, 46)]
def r1sG : List Nat := [1, 2, 2, 2, 4, 5, 5, 8, 9, 9, 12, 13, 13, 33, 33, 33, 34, 34, 34, 36, 36, 40, 40, 44, 44]
def r2sG : List Nat := [3, 3, 6, 10, 6, 7, 37, 10, 11, 41, 14, 15, 45, 35, 37, 41, 35, 38, 42, 37, 38, 41, 42, 45, 46]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := [2203924628995, 4407192519430, 36293080057347]
def xsM : List Nat := roots_47.map (· &&& dom_47)
def goalM : Nat := goal_47 &&& dom_47
def NN : Nat → Nat
  | 4 => 2
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xf65ed8d10f1fce07
  | 5, 0 => 0xf1fce07
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffff000000000000000000000000000000000000000000000000000000000000fff00000fff00000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000f0f00000f0f00000000000000000000000000000000000000000000000000000cccc0000cccc0000000000000000000000000000000000000000000000000000aaaa0000aaaa
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
  | 0, 0 => 0x1ffe0000000000000000000000000000000000000000000000000000000000001f81ff00000000000000000000000000000000000000000000000000000000001e01f800000000000000000000000000000000000000000000000000000000001981c70000000000000000000000000000000000000000000000000000000000007000e000000000000000000000000000000000000000000000000000000000000fb61
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x1fff2400000000000000000000000000000000000000000000000000000000001fedffc0000000000000000000000000000000000000000000000000000000001e49f8800000000000000000000000000000000000000000000000000000000019a5c740000000000000000000000000000000000000000000000000000000001572dbf0000000000000000000000000000000000000000000000000000000000a9fb63
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

namespace S_62_1
def pairsG : List (Nat × Nat) := [(1, 3), (5, 7), (5, 21), (5, 37), (9, 11), (9, 25), (9, 41), (13, 15), (13, 29), (13, 45), (17, 19), (17, 21), (17, 25), (17, 49), (33, 35), (33, 37), (33, 41), (33, 49)]
def r1sG : List Nat := [1, 5, 5, 5, 9, 9, 9, 13, 13, 13, 17, 17, 17, 17, 33, 33, 33, 33]
def r2sG : List Nat := [3, 7, 21, 37, 11, 25, 41, 15, 29, 45, 19, 21, 25, 49, 35, 37, 41, 49]
def mpG : Nat := 0x3ffff
def pool6G : List Nat := [18713729377557, 18713729378585]
def xsM : List Nat := roots_62_1.map (· &&& dom_62_1)
def goalM : Nat := goal_62_1 &&& dom_62_1
def NN : Nat → Nat
  | 4 => 2
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x4ced50031873cbb6
  | 5, 0 => 0x4ced5003
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xaaaaaaaa00000000000000000000000000000000000000000000000000000000aaaa0000aaaa0000000000000000000000000000000000000000000000000000aaa0aaa0aaa0aaa0000000000000000000000000000000000000000000000000aa00aa00aa00aa00000000000000000000000000000000000000000000000000a0a0a0a0a0a0a0a00000000000000000000000000000000000000000000000008888888888888888
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x2c4428b184
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
  | 0, 0 => 0x3c0000000000000000000000000000000000000000000000000000000000000003c0000000000000000000000000000000000000000000000000000000000000003fe00000000000000000000000000000000000000000000000000000000000003f0000000000000000000000000000000000000000000000000000000000000038e0000000000000000000000000000000000000000000000000000000000000000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3e2480000000000000000000000000000000000000000000000000000000000023d240000000000000000000000000000000000000000000000000000000000019bfe00000000000000000000000000000000000000000000000000000000000113f00000000000000000000000000000000000000000000000000000000000008b8e0000000000000000000000000000000000000000000000000000000000004493
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

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]
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

namespace S_39
def pairsG : List (Nat × Nat) := [(1, 3), (2, 3), (2, 6), (4, 6), (5, 7), (5, 37), (33, 35), (33, 37), (34, 35), (34, 38), (36, 37), (36, 38)]
def r1sG : List Nat := [1, 2, 2, 4, 5, 5, 33, 33, 34, 34, 36, 36]
def r2sG : List Nat := [3, 3, 6, 6, 7, 37, 35, 37, 35, 38, 37, 38]
def mpG : Nat := 0xfff
def pool6G : List Nat := [4407192519430, 36293080057347]
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_39 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_39 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]]
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

def isoMv_59 : List (Nat × Nat) := [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem low_59 : Lower dom_59 roots_59 goal_59 8 :=
  lower_iso isoMv_59 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_55

def isoMv_43 : List (Nat × Nat) := [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem low_43 : Lower dom_43 roots_43 goal_43 5 :=
  lower_iso isoMv_43 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_39

def isoMv_30 : List (Nat × Nat) := [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]
theorem low_30 : Lower dom_30 roots_30 goal_30 5 :=
  lower_iso isoMv_30 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_39

namespace S_63
def pairsG : List (Nat × Nat) := [(1, 3), (2, 3), (2, 6), (2, 10), (4, 6), (5, 7), (5, 21), (5, 37), (8, 10), (9, 11), (9, 25), (9, 41), (12, 14), (12, 28), (13, 15), (13, 29), (13, 45), (17, 19), (17, 21), (17, 25), (17, 49), (18, 19), (18, 22), (18, 26), (20, 21), (20, 22), (20, 28), (24, 25), (24, 26), (24, 28), (33, 35), (33, 37), (33, 41), (33, 49), (34, 35), (34, 38), (34, 42), (36, 37), (36, 38), (40, 41), (40, 42), (44, 45), (44, 46), (44, 60), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [1, 2, 2, 2, 4, 5, 5, 5, 8, 9, 9, 9, 12, 12, 13, 13, 13, 17, 17, 17, 17, 18, 18, 18, 20, 20, 20, 24, 24, 24, 33, 33, 33, 33, 34, 34, 34, 36, 36, 40, 40, 44, 44, 44, 48, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [3, 3, 6, 10, 6, 7, 21, 37, 10, 11, 25, 41, 14, 28, 15, 29, 45, 19, 21, 25, 49, 19, 22, 26, 21, 22, 28, 25, 26, 28, 35, 37, 41, 49, 35, 38, 42, 37, 38, 41, 42, 45, 46, 60, 49, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0x3fffffffffffff
def pool6G : List Nat := [2203655144963, 4407040936454, 8804969808650, 14302527947530, 22012448021525, 18700624528899, 21999226980870, 2203655214339, 5506484995587, 9904598878723, 36293080057347, 18713729377557, 18713729378585, 22063651494165, 18730909247769, 26474465269020, 18700691900931, 2204260960771, 22046807759893, 36305646982437, 26427674401817, 19808675758854, 2203722713603, 36356984476977, 36387703561265, 26410494532633, 36305646983465, 61715125705777, 5506754479619, 9904868362755, 18701162448387, 8805020337674, 5506704147206, 26474734757148, 36357051586865, 36293349279235]
def xsM : List Nat := roots_63.map (· &&& dom_63)
def goalM : Nat := goal_63 &&& dom_63
def NN : Nat → Nat
  | 6 => 23
  | 7 => 76
  | 8 => 49
  | 9 => 9
  | 10 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 6, 0 => 0xd4e034e8c8af3bbb9c8ef6418c49e4aa70f028e0680c889867aab8ca603785a74fe64fd44eb1559f4e8b95e04bd49b7044257dc83292cbac2e1d0c0d282cb394261253a523e58d1a1ace62b610684a9e0f77894c0c06304907ecc2e6
  | 7, 0 => 0x9eb2336c9be41d5a9af8871598f4208d94d4832a8d94f5ad8b6aabe7888f7ea4841fb46482fee33982c4fa7080ab0b5c7ea020fc797004af785ee2587731b80f6e4e17c7694fc71e601d48af5f18482b595c1952592f0198581ef1aa4d84259f4b093b3e4a9428d247b76ea345a7f59843c469ce40e5429a3fca826d3abe076538c68766377efee635bfbca933496ad531ae08452e8a65942bbea46f2920d9a427ebdf6f27d25737279f070c2748e4d0250f254024f59d08232c6add20580ac3204fb0ae1ff6fee71d1165dd18e16a7f186c3881183355481813153413fa3b791247bf7811bd50f40f06017a0919997808a3620f014ecf6801189ba900a7cf8b
  | 7, 1 => 0xfc1a4b00f582e6acf1e2cc0decc12505e455e20ada1e6317d60caeb3cb5c33febf79164fb7dce78eb44008a2a5268c5f
  | 8, 0 => 0xfcf8d17ff05fc8f2ec164c1eea555bf2e7283c3dd87f9952bfa41077be4be64fbcc8e334ab681b8eaa87c3f1a6877d59a275c8f59d2006f693f42b8d9351acbb828511a47fe35f827bf0d33379e15a28791d9b4177d135d069f92139514aca6d4d1acf0f4c4c79c445f6b584433f660a4214fad12d90db782b81626d28a4a83e26beaf6f261c309d22c735132219ec0a1b61a0cd1922d7aa119811441187183a0f79f41c0efa46790e57c7a70cabde0a0c167f100ae892150acf09dd06291d83059e8b17
  | 9, 0 => 0xf2854adfdac0e1e9b6be763476f0de33764e5f615fbac6fd5cde0cce0e7e151305169eb0
  | 10, 0 => 0x42b779a3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x505ffff0505ffff000000000000000000000000000000000000000000000000050505050505050500000000000000000000000000000000000000000000000000ff00ff00ff00ff0000000000000000000000000000000000000000000000000055ffff0055ffff0000000000000000000000000000000000000000000000000055005500550055000000000000000000000000000000000000000000000000000f000f000f000f0000000000000000000000000000000000000000000000000000ffff0000ffff00000000000000000000000000000000000000000000000000000000ffffffff
  | 0, 1 => 0xaaaaaaaaaaaaaaaa000000000000000000000000000000000000000000000000aaaaaaaa00000000000000000000000000000000000000000000000000000000aaaa0000aaaa0000000000000000000000000000000000000000000000000000aaa0aaa0aaa0aaa00000000000000000000000000000000000000000000000005555ffff5555ffff000000000000000000000000000000000000000000000000555555555555555500000000000000000000000000000000000000000000000055550000555500000000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f
  | 0, 2 => 0xfafafafa00000000000000000000000000000000000000000000000000000000fafaf0f0fafaf0f0000000000000000000000000000000000000000000000000fafa0000fafa0000000000000000000000000000000000000000000000000000f5f5f5f5f5f5f5f5000000000000000000000000000000000000000000000000f5f5f0f0f5f5f0f0000000000000000000000000000000000000000000000000f5f50000f5f50000000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000000cccccccccccccccc
  | 0, 3 => 0xffaaffaaffaaffaa000000000000000000000000000000000000000000000000ffaaffaa00000000000000000000000000000000000000000000000000000000ffaaff00ffaaff00000000000000000000000000000000000000000000000000ffaa0000ffaa0000000000000000000000000000000000000000000000000000ff55ff55ff55ff55000000000000000000000000000000000000000000000000ff05ff05ff05ff05000000000000000000000000000000000000000000000000ff00ff00ff00ff00000000000000000000000000000000000000000000000000fafafafafafafafa
  | 0, 4 => 0xffffffff55555555000000000000000000000000000000000000000000000000ffffffff00000000000000000000000000000000000000000000000000000000ffff0000ffff0000000000000000000000000000000000000000000000000000fffafffafffafffa000000000000000000000000000000000000000000000000fffafff0fffafff0000000000000000000000000000000000000000000000000fffa0000fffa0000000000000000000000000000000000000000000000000000fff0fff0fff0fff0000000000000000000000000000000000000000000000000fff00000fff00000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 6, 0, 0 => 0x8595503ce695038a20569d140a141699c65028869e540a2056999450287671940f200699c4503c2665140f1c065d54503c569a171140a671940f388665140f387685e71140f69a5450303685c4503c06
  | 6, 0, 1 => 0x990288141665545028068994503c067994503c4699f71140c699f45030169502881406
  | 7, 0, 0 => 0x269503ca205700079c65140f60269617d140a700099955140a60007194503c060258596103ce702695945028270257d940f38870269614503c3702695140d285702695955140a70009903c8141602585f79140f702695940a248702585f4503c070007194503ce6
  | 7, 0, 1 => 0x2695140f185701f7194503c0700095140e28560257de6503c870009e545028560266544503c170257d940f20070256503ce288702765140f28170266d945028170259194503c0702695f4503c2702795940f288702695b65028870264503ca14170268a165140f7
  | 7, 0, 2 => 0x2685f4503c1702665140f08170269503cd2057026859450281702565140f180702695b6503c870009a171140f600095140a14060009a57d140c60267d9450281702695f650288700099940a201602695a65140f70256503ca200702665140f0c170266584503c77
  | 7, 0, 3 => 0x266154503c570009503c8140602696365140f70267d940f20170269194503c170269564503c5702695d65140a702696065140a70009503ce20560269594d140a700099c6503c8602565845028070269617d140c702696165640f70009994503c7602685f71140f7
  | 7, 0, 4 => 0x2565140f080702665140f301702585945028070009a265140f602565140f382702585945038a702796165140a79a58607d140f80009d945028160009a540a205602695949140a702696465140c7
  | 8, 0, 0 => 0x258594503c070269594503c370266584503c170269594503c970257de65140f70257d94503c0702695951140f702665855140f702565140f38a70258594503ce700095940f20069a58594503cc80279594503ca702695b65140a702695140f28579a565855140f8
  | 8, 0, 1 => 0x9a58594503c2802695f6503c8700099940f20169a56584503cd802696465140f700095140f38560269617d140f700099955140f60269594503c2702695140f345702695955140f702696165140a702695f65140a700099945028160009a5650288602565140f2807
  | 8, 0, 2 => 0x9a586065140f80009a540f20569a58594503cd802695945028970269594503cc702695d65140f7000959450280602696065140f79a592165140f89a58594503ca800095945038a60009e565140a60256584503ce702665140f28170268594503c1702695945034a7
  | 8, 0, 3 => 0x269594503cb7
  | 9, 0, 0 => 0x9594503c0602565140f39a69594503cd79a565140f29e696165140f702665140f05809a56503c8602695945029a695961140f7
  | 10, 0, 0 => 0x9a565140f6
  | _, _, _ => 0
def stateW : Nat → Nat
  | 6 => 40
  | 7 => 52
  | 8 => 52
  | 9 => 46
  | 10 => 40
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 6 0) :: stateWires n (ids >>> 6)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x38fffff8e1ffff0000000000000000000000000000000000000000000000000038f19c38e0010e0000000000000000000000000000000000000000000000000007f07fc7fe00ff0000000000000000000000000000000000000000000000000007ffffc7e1ffff0000000000000000000000000000000000000000000000000007f07c07e0001e0000000000000000000000000000000000000000000000000000f01fc0fe000f00000000000000000000000000000000000000000000000000000fffc001ffff000000000000000000000000000000000000000000000000000000003fffffff
  | 0, 1 => 0x3c01fcee100000000000000000000000000000000000000000000000000000003c000000000000000000000000000000000000000000000000000000000000000001e0000000000000000000000000000000000000000000000000000000000000001cee0000000000000000000000000000000000000000000000000003fffffffe1ffff000000000000000000000000000000000000000000000000003ffffc3fe0311e000000000000000000000000000000000000000000000000003ff0003fe000000000000000000000000000000000000000000000000000000038f19ff8fe0f0f
  | 0, 2 => 0x70e63c000000000000000000000000000000000000000000000000000000000070e60071ff0f000000000000000000000000000000000000000000000000000070000071e0000000000000000000000000000000000000000000000000000003ffffc3fe1f1fe000000000000000000000000000000000000000000000000003ffe603fe1f0f0000000000000000000000000000000000000000000000000003ff0003fe0000000000000000000000000000000000000000000000000000000070e600701f0f00000000000000000000000000000000000000000000000000000e01c00e0000e
  | 0, 3 => 0x380f83f81fffe100000000000000000000000000000000000000000000000000380f83c000000000000000000000000000000000000000000000000000000000380f80381fff0000000000000000000000000000000000000000000000000000380000381e0000000000000000000000000000000000000000000000000000003ffffc3fe1ff1e0000000000000000000000000000000000000000000000000038ff9c38e1ff0e00000000000000000000000000000000000000000000000000380f803801ff0000000000000000000000000000000000000000000000000000070e63c71ffef1
  | 0, 4 => 0x3fffffffe0311e000000000000000000000000000000000000000000000000003fffffc0000000000000000000000000000000000000000000000000000000003ff0003ffe0000000000000000000000000000000000000000000000000000003f0fe3ff1ffff1000000000000000000000000000000000000000000000000003f0fe03f1ffff0000000000000000000000000000000000000000000000000003f00003f1e0000000000000000000000000000000000000000000000000000003f0fe03f01fff0000000000000000000000000000000000000000000000000003f00003f000000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x1087fdd0815bbf00000000000000000000000000000000000000000000000000108110108001080000000000000000000000000000000000000000000000000003706ec37600f7000000000000000000000000000000000000000000000000000247fdc2415bbf00000000000000000000000000000000000000000000000000024048024000140000000000000000000000000000000000000000000000000000300640320003000000000000000000000000000000000000000000000000000007fdc0015bbf000000000000000000000000000000000000000000000000000000003feef77f
  | 0, 1 => 0x932a7c93fcee3000000000000000000000000000000000000000000000000000932a7c011088000000000000000000000000000000000000000000000000000093002093e8440000000000000000000000000000000000000000000000000000902a1890dcee00000000000000000000000000000000000000000000000000036cffdf6c17bbf0000000000000000000000000000000000000000000000000036cd5836c0311c0000000000000000000000000000000000000000000000000036c80036c020000000000000000000000000000000000000000000000000000018b19758ba0f0b
  | 0, 2 => 0x2f7eefc0110880000000000000000000000000000000000000000000000000002f7e6aaf7ff4f4000000000000000000000000000000000000000000000000002f78022f7ea4400000000000000000000000000000000000000000000000000037cf78b7c5f1fc0000000000000000000000000000000000000000000000000037ce68b7c5f0f40000000000000000000000000000000000000000000000000037c80037c4a04000000000000000000000000000000000000000000000000000274e68a745f0f40000000000000000000000000000000000000000000000000012e55c52e2533f
  | 0, 3 => 0x3dbfb7fdbfffeb000000000000000000000000000000000000000000000000003dbfb7c0110880000000000000000000000000000000000000000000000000003dbf933dbfff48000000000000000000000000000000000000000000000000003db8023dbea440000000000000000000000000000000000000000000000000003ecfd93ec9ff1c000000000000000000000000000000000000000000000000003c8f913c89ff08000000000000000000000000000000000000000000000000003c8f913c89ff08000000000000000000000000000000000000000000000000002f7eefef7ffef7
  | 0, 4 => 0x3ffffff6d1399c000000000000000000000000000000000000000000000000003fffffc0110880000000000000000000000000000000000000000000000000003ff8023ffea440000000000000000000000000000000000000000000000000003fffffffffffff000000000000000000000000000000000000000000000000003ffffbbffffffc000000000000000000000000000000000000000000000000003ff8023ffea440000000000000000000000000000000000000000000000000003fcff9bfcdfffc000000000000000000000000000000000000000000000000003fc8003fcca440
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 8 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 5 => 2
  | 6 => 186
  | 7 => 936
  | 8 => 337
  | 9 => 27
  | _ => 0
def CH : Nat → Nat → Nat
  | 5, 0 => 0x91911e7142b779a3
  | 6, 0 => 0x492b5ae447c6e16346854e7b4675c8f94594043e42e68c5242b779a33f8d72f83be85be036bd7d743681559c35bfbca93307fdaa31d2bb4a31ae08453139f1ca2e9a4d392b81626d2ab9f2702a8c84472a59da8229c61d0029b62f0f29ae14bf28a4a83e2884fdf8285eebd12123972e20c912ec1da43c041d600c9e1a888b681a65090118e16a7f1842f65e176bcc78170f33761594fa3812c81b5111fd39c011f9841911f1c6191160596f106d47050dd90e0a0cabde0a0bed84ba09f6f25b09e76cd909b7c85209209d23079721a807962ead0700037b06e7b83006165d760505ca7204ef228402c42272029531040261d2e00229104300a9e32300a7cf8b
  | 6, 1 => 0x85c2d5a684ff1a8d84ca8d4b84212c8282c4fa708229ac848222605e800e00007f78bc997d7f56c67cfa44f47ba3862e7a2af07b79e15a287997b68e78ad1f3a788aa53978704f69785ee258781928d475413da67540a7b3751e0f9874e9bb5c74d841fc74856ceb734bd994730c7bc77244de576c5cc38c6a8772f969f9213967b453a3671308da65e76cd56501783e64298c5863df1d386363a0a562a0afc562868ddd6266878561fbdec361fa7f4b60bfdce05f51ec415e2f68925d930b505d7cd4b05cd50f7c5a942b785a5437a059caebfc596b204c581ef1aa57665cb1555ffb3653fa289852c30a034d9ae2e34d3d0f484d1acf0f4af9e31e4aae3b9e
  | 6, 2 => 0xf6ce9c4af3b27adfed1cfa4becc12505ecae38b7ec1734bbec164c1eea6a2d26e795fa06e7606c99e5c02157e580cb8ae276b9c4e0068025dffd3fe0df0d00beddfec7e5dbb49a3ecf5a3a2dc9c5f187c9880156c471d76dc38acab3c33839b7c00fd164bf7ad2bbbf5c25cbbe4be64fba62b566b8e76ab4b887c075b3616ff9b1c39860b1b8bb56b0ead2c5b05bd67eaf2f3e37ad7847e4acd91e61a698872fa6877d59a63dc468a3b67c5ca275c8f5a194c2cba12301bea05b39a2a019f6b69b9d07039b7186cd99308b4d9623baaf90e2f0448fe00edb8abcf7348a77e85487be0786870b766e
  | 7, 0 => 0xa26407909cc529509c0e3280989c7c30905f9ab08e4c69e08c7c03908c00bc908b46af10865d84f080f596907ed8a3207d4d70907a99a0b078179cf073258370709752006fd04030651b5d5064cb80906291d8306237d4e06148c15060e01a405c171a505a47d010567dbbf05169eb004ccdfdc04c9880c048faf4c04824cd40472ece0046088880442bd86042b899703939ebd0384d1180355cd580341d11b033b05b5033a727c03254bac030a418d028de01e02895eae02867f1c023f5c5b020b934d01bc533301afbd410195ffdc0191869801660357015fcb3e01551783014268c700ea38dd00b6512f00ad42790082d9db007dbb7a002d875e002bdc3e
  | 7, 1 => 0x16e96cfa16d6f5a816d21d8816c91dcd16b01e54167cc58616573f00164f38e0164042a2162baad5161b95e2160c7aef15da66d015da08fc15d3b4e415ba6e6315af65f115423b4114e907ff14db292014cc203914c37a0914c0d43c14affb971499cfe51476241e14649f8f143a35731436a47013c146b612e127a112ddb43412a8595d12423e081228cbf912245a6811eac26e11a36f331187183a11804b361150faed1142fa41108d3a53106f8d040fda9e160fb1a7760f79f41c0f622c520efa46790ed019dd0e90cf7c0e7e15130e05ccb20de1cc4b0d49c4170c64c7b30b2912830afb5dd30af197a60ae892150acf09dd0ab8b2690a4613430a38ae29
  | 7, 2 => 0x20d56179206969b82064873a204b60b61fd3c25f1fc4f9a61fba95f01fb5cfd51fa939b01fa565611f129f391f05df5c1efda3231ee77a8a1ee50e861ed55caf1e808ee71e5d9f271e4008941da670221d98a19b1d85da9b1d68e5f71cfd2fc91ce5940a1cd038361ccc0bd21ca481c01c96ea491c5a42401ba64fad1b61a0cd1b6003b71ae9b4a21add53df1a9c7f661a8e79ea1a6eda831a6a04de1a4dc7a41a35fb731a13ea6d1a04d97919fc1ed919f37e0719c7c79119ba301a19a917ce198916cb1980bc2919224d721921f28d1891b64a1883498818595dba184be9d718261f7817c5c22e17b7e34f17a3f1f5175c2c75171f64aa17135e9f170e6fea
  | 7, 3 => 0x2a975fae2a8c3c9c2a7c1a122a4993872a430f592a06a6fe29f0b1cd29ed6e3b29af2b6429428e4b29259dd7291d2a9e291563e329046ad928d6af59287e5ad228768e5727e01bb22781b97327778c4a2710b40c26f168c926beaf6f26bb2fef267fe1b7267799182648e3a8260fca68260a164f25fc139f25dc2a2825d992dc25d51a46258822082566dfcd24fc57bc24dd90d224cc78e0242930a9241d331323fade1623e5cb332385b345233e519822b0699f228b59102289ec0b22747b08226e2d532265e4b4224c5c7c2202198b21eaa96f21e6cbde21dae13221ce372521c636b821bde80721a5f968218ce6fb214f0d11212a86b02123972e20f7486e
  | 7, 4 => 0x361d64da35f2a557358833f8357ada313579865d35239d6d350ff6a134ceb8d13466ebee345ddff534487e1233fffa6733cd017f33b85c43339be830330575cc32eb626b32def36c32a1bcd5326bf53f326a54bf3264f1943252e2e0324a6b873242e2d331ffed833159aba13130272030dba21430b1e59a30a02a49306c1f0a304a85c7302ca777301b2a853014f8752f636c812f29cd722f1a0c9e2ec68d272e9b5e9e2e3b996a2e3a69332df013cb2de6358a2d3e70562d19df392c7afb6d2c42325c2c2937292c18d8712c009a592bfd93d32bb2627d2badab652b811d732b6d71132b69948c2b5b15012b3360e82b2a76162afd8c522aa00b9d2a9cb57b
  | 7, 5 => 0x42ba7c5242b779a342ae7c51425bc8a4424d728e424083084197b05c417103f5412c1b3840f0f80a4042c3c8403af74d4025a2a04021fadd3ffe8f0c3fb404613f8ddd6d3f8398af3f4622693f3bf5403f2afc363f15457d3f09c54c3e69a4d83e444aad3e3c020e3dd8da4c3dc07c953d99833c3d2562093d1dd8183cbde0b03ca34bd03c9e2a753bfbaba33bcc8c933b3668933aab48ca3a93e9c13a8512d93a64e63a3a4fc2063a4487b239fa66b039d3956d3961b02b395f2ed039514ff1394f142038ec2da138bbb164389cbe36388c76113884a1d73864ee27385c30bb381fcf1437a858aa3745c9b53729e7e336b521a2364691d83644f7dd36262504
  | 7, 6 => 0x52534f9451688e28509f5416506b190f50490acd5036f0254fbdd0064fa260824ed50c3e4e9a87094e8bd3f94e5372144e4388a54e3b68614e18a5394e12cbcc4dace24a4d704cfa4d2ff4d14d1acf0f4c7c5aee4c46545e4c0122844b5e75fd4b50406a4ab8c3e84a77d2104a6c36964a39d0ac49f3d2f349e8ddff4987e82849148db0490584c948ae22b5488ad56b480eeebd47e9072d47703dcb476a5be94727debc471a541a471718c44700cb0e46de759446d0e8cf46c9322546c6bba6469949b5466764c545ff7132450e2e1744ecccfe445ca64c440fd5ef4408d56743eb0c0643c1fcc943992f1e4397d140433f660a432dfd82431f7df742e7b5af
  | 7, 7 => 0x62fa02de62d73fc862d4bd2362d3b1c9621d1ce661fe39a261cf8f7361a982436042b3645fbac6fd5f411ea25f26c7b65e9456d05e82f8175e394d3c5dfe16575d7408235d65f9355cde0cce5cbe4b0e5c5fae8d5c3b8dfc5c33c1815c1e7f7b5b4dbe2c5b47f7025b34bf745b26580e5aebfb475ac679ad5abcb8a95a7ee5485a4c2e7059efad2e59a0445d5996f4f559924d70597bfa895925466958b56100583d5a5957ad78bd578e67bf5742a7955727b7f456c5d00a56488c3a5551c8e55520126a54e2c70654d24b7a5476a8055467b4c65462936b544bdb3154324e155421696053ca920853c0149953c0043b537c0e455377c91a52ce9ec252a2b541
  | 7, 8 => 0x7051552970120e997005f1236fb8decd6f71e1b36f410f6b6f1deb2a6f13e0ff6ee8713b6edb0ec36e8379536e5a9f856e16b7eb6db3cd8b6d5b0d956d5129f76c96b4706c64553c6c41d5016bf899566be5d2566bba30316b5f3d456b3934176b302ff16aefcfd96ac5c8b56ababa2c6aa75b3f6a729fe46a08291469da0c1f68fc772168ee71a568e6a26668c81d0c6885fcc068201ef167fbcd3367b7d8a267891a306752b39f6741623a671066ce66e5ae6b66e4732066abe192668f2c5366730cef6617db0a660e2ed065ecad8165e76cd565d6d88f65b3f9f7650aa1d364d4ee0264b23f0e6433ac9f640e6da16407b8f163c9cc6363b272246320cbf7
  | 7, 9 => 0x8154339f80b2da9b80b1b4cd7f48d8727f31a4837efde3047eeeae697edbceae7e704a887e4dc0ce7dc60fd37cb3fec07c65e62a7c2948dc7b37240e7b1ff01f7abeb30b7a7f40357a38d5c279f05dc079c02f72796fc1e1796deb397931a7f078e9916b78e6cebf78849c9477e509f57776a25c76fdbb7a76fcecf676f0de3376e7e0e1764e5f61761a42bc75571bf07554e386751ff38c7512fdf774ae2b34746a0e0a73f993ba73e9209c73da4b1a73d425d573d3559173be3a8b73bcfd3f73a75c7d739a9980734eaa0d730c5ff872464c2172286c4f71b7c8f2719e7521719e52c1716cc1f97145678c7110615a7101499370e34a067089019870607efa
  | 7, 10 => 0x9e1370af9d9a91c89d2006f69b34b1219b0c849e9af310349a6914bc9a6324e39a4ad2999a07492d9a026443994406639848d5ba97d6532297a4f387970d416896f60d799608f40395fa9786950239c5942a4f209405ef3093f42b8d93c49ebe936e25d292cbdd1a92bb0e58923f113d91b6394091503a309102d10890f610e69049058a8fe77d2d8fa972eb8f74f0a98f63e3fa8f4e886f8eba28b68e27cd4e8d1b84e68aa701598a29179989a8e63589312aef890be79e88e50a9488d9be16887ddfc2884d6a8e88338d2887de9c8a874d6699869d478d865cbae8846b9cfe84594c5e844c644983fe99eb8323a63b82673617825ec43882348b3c821853fe
  | 7, 11 => 0xb0231954b017b28fafe8b470af9abc18af73942eaf5954afaf4aa714aee89f20ad6b0c80acc6a2bbac7b9e87ac54c35bac41cfbeac1e6e85ab79c6cbab2a5122ab214571ab1a9a18a994b72fa9908080a97aa236a9679bafa80cba21a7ac52a8a735b75fa6877d59a6563cc3a61bfe94a5f8bd8ca5f12d82a5a62689a598068da57ecc1ca57519cca56b5b41a4ae7b11a44634c2a40b50aca39ec2eea390017ea37a73fba32cb193a3098384a275c8f5a265fcc7a26534afa2602c83a2465e8da1fee453a1f16defa1a3dfbba1947225a0d050949ff394c19f885efe9f7298a79f620de99f281e6a9f1c706f9ed6de7b9e56566f9e519fea9e4b2ef19e418da4
  | 7, 12 => 0xc9f553bac97fa584c8bf6cefc8bcd3fdc7d22c68c667cc40c63e6ab8c5ff83fec5eadd1ec5736c6ac5382f90c52f7576c4e09fabc4d7a737c416706bc3e2d77bc38acab3c26131dec1980f89c154e976c121cba0c0f590b7c08f374dc088640abfda4f41bfa41077bf62c138bf0ef053befa2055bedf3b8dbec33186beb14ce4be430903be04cff8bd8be129bd6a8f7fbd2fc437bcc91ac8bc87e6edbc591900bb779f5ab9f31b94b9e4f0ccb9c33d03b9af61aeb6f964b2b6be7634b666254db59dad4ab432738eb42966f3b37c045eb36d3a2db36b0913b35c5b78b34ae530b31e2f22b2ce525eb2118fd6b1ff7463b1bb3c8eb1b8bb56b06379a0b028f5a0
  | 7, 13 => 0xec04ee7febefca4beaf7f023ead93aa9ea6cc730ea472a57e8ac2f7ae8796d32e7eb888ae7283c3de63575f3e5cbe3a1e5cb74e9e5c2ba49e5a002ace4e88dfde41e5447e2e5bc00e298b8f8e1ea8e0ce1283faae1151f08e0ba14e3dfdba1afdfda7178df7e61aeddd8d9a8dd6521e7dca8607fdc4d3caedba47023db4f33a9db48ce50dac0e1e9da1fccb5d9cc308ed96e9d0fd96359b3d84ccd00d7272a2ed6ea9846d6d35949d6af2d85d5c938eed53d3f77d44635d3d42b6155d2c39f73d29482abd2849381d173caa4d06e9653d019acf1cfcc1781cfaaeb5dcf93d245cf01a125cd13336dcc3d2a65cbedcfe9cb2f7209cb20c46eca92acacca5d1f3f
  | 7, 14 => 0xfff37a59ff3e3073fea58edcfe2b8d04fe1c6333fe1106f7fdd6902afd9b65b0fd7e81a8fcfeb677fc53b9bbfbe1c5f5fb19fc8afab495f5f9b835b8f9aef702f8eb2a3df8c7e701f8ba5c5ff87e7dd9f867a20ff808cdccf5ab4c3ff5855b21f44d45f4f44935f4f3bffcabf3b27adff33384e5f31ff462f2854adff1c6f18ff19e9751f0886534effcebf1ee02495bedfca193ed899b23ecbde3deecb47af8
  | 8, 0 => 0x29e942c42964176b2774c460275958f22705880d26d2458e26396ad425fb67b225d7fbe12429651522c1b3a32282fd3e21a5f9682081cc61203e530f20292edb1fd3d3851f3d31db1eb3facb1d81c57f1c93f14f1c1ffead1b52f3321a5d395419deb3e219d9673c19b1d448183e8305175a929b16b50ee91623f29c15f86a801561a43a14f37973141a4f1c1415063f1413d60814121a0c1317dd2b12b8884a124e263511eb7ccf11d748061134c9340f8898390f3badb20e7dd0190d9cbe430d61f2fb0d4d98860cea20e10c22507d0bb2ffb10a029d7e09ee1b6f089ab0f30864c5e506fd040306ecbabd05ad2f3405869eb10233af150086a50c00273479
  | 8, 1 => 0x48f889f848e9602748b0ac9d484e6acf475141bb471a8c3146e1bded45c07cca457c5ed144d9dfff42b779a341d9fb7841d622d341a4b5d64079af633f49363a3e5fa5093dc32c533d8620523d0124c93cedcf813c9f3cdf3c21f90f3a8b9b213a8b1a653a861c993a4766343a305add39fad6353950034038ad846e3899ed18387c221637dd7e8036c744ae36b6da923678c0eb363c57f4359f67e7357bcd573518dab134746a9f346540ce342cdee933ab0d08333e196732e7627a32ba82ac3264f1943255c7c3315024ba31381b073129ad3f3055c0a6302ca7772f790d942eedfa852edbd6b52de85b922d014b912cf3c0ef2cf085992cb7e2692a6cf071
  | 8, 2 => 0x6be1bd3a6b6909ce6b46b4d16b1be3666a7ff66869b2eaed683fb3fc67f1c0d3679d352a66fb4c91668c4770651506a464cf00c5645092fc63353df463275f156292bf226284e0436129ea295d93d62e5d7bf2db5d3a46645b2acd595af03eb05ab946475a437adf5916f56256e9ce2f567ee6cd5640306856240dff55df5df8558b875054ed1c7554b47b98531915d1530ec13f52acbe7d523dc211520a3fab51d2062b51bf3f2b51a4e00751099cc64fb2394c4f9b055d4f0fba7a4ec7de7a4e2ce2974e00c0ea4de27c5e4dc27b5b4cd8ba054bff26be4bf147df4b62f61f4b02825d4ac0774d4a0d197449e125c6499b08ca498bdef949148db048fa38cc
  | 8, 3 => 0xa141bf77a07b39919ffd08839d3508f49c3531c39b1dd7b099ed5e8793602c46927a567e925c0be491b98d12906d26118f7fd14d8f78512d8e7679718e6e30d28df2ab598dcbb2008d5eaaf98c76bee98b308e208a81f0ca8a18c288897643b68968a0cb895976fa88ede028886bb2a5881ad29987080352869b7594868cb424867726a185f48e9f85520fcd8549f6d2850f030e8492c7cd83f048fb83c5bc5283233d8082d3eb997fb9fc427f97da8d7f27d8097e8559377d33ff317a38d5c278493a7f77211a3f76f0de3376db0b2e745b5f6d727daf3d7260e48f721cd83371be65bd70ffce107005f1236ebe77696e0cf9fd6db8095f6d9b14bb6cd622c6
  | 8, 4 => 0xe862cb83e795c008e73f702ce4625a30e3d420a8e2f02cffe1283faae11915d9e07b344edfdba1afdfb32b5bdede789bdb6f1befd96359b3d8e7dfa1d7d8277ed6af2d85d69e993fd62ad27fd58853add3c1c38ed39b7279d355d4ffd229a3e5d1d3f658cf6e15b1cecb96dfce3bc8d3cc0fb7b2cb46a5f8c9e65a89c5c226a0c52f7576c4605fcec3935453bef5700abee065e9bd2744b8bab08b31ba2399e2b837fe7bb7610a65b59a84ddb3823d02b315333eb253eee6b1b17014b12375bdb108215ab0ed6350b080f6ebad85a160ad6b0c80a9cb11c2a98c5b5da9647ee6a8e78fc4a80d8a65a80d4bfda5d7b751a494c22fa3f2435da302d5f5a2f4f716
  | 8, 5 => 0xffcceadcff5a28fefab495f5faa130d0f9acd0faf8b72109f7c42f43f6e94291f646c3bff23e3488f22186e7f0f10dbeef0e3eb4ee6bbfe2ede8c63eeaf7dac4ea39f55d
  | 9, 0 => 0xdd9de376c2afde01bad4da24a6563cc3a1f16def9b34b1217e1a8a567cea112d705b5d9f5e22a7545a34cc4255df5df851bb2a0f5059633d4f8c57c24aee737942b779a33e277fff34064f6c2efbd9642eedfa851e7359ed1b78d4bc1729918f1561a43a15527a691142fa41
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 5, 0 => 0x851080000000000000
  | 6, 0 => 0x18c5244130000002530413000000e01802300000120280630000000048c020500000029002050018c1050030000000028c02040000054081201000000000000b00000540812010000000000005000000480a2020000004806200000000000a1030000a53041300000000000e1020000000012101000002048020400000000000090001a540413000000253081300000005308120500012018023000000003802204001505304130000145400803000001a53081300000000000000b0000002802204000000000000b0018c20500300
  | 6, 1 => 0xa54402300001802148130000002530413000000000002102000000380a20200000000021020000000000000000000280220200000000121020000e0280630000002514803000000a0090030000000008c020500000534802010000a54402300000000480a2010000a0090030000000038022000008553081300000125304130000000540c12020000054081204000000000000b0000053081205000000180220000000204802040001a530413000001601900300000000000e102001802148130000000038022030001251480300
  | 6, 2 => 0x290020400000028c02040000a54402300000120280230000000058c020400000029002050000a0090030000000000000080018021481300000000010010500000038022010000000085108000000380a2030000a54402300000000380a204000000000000200000009002040000002802201000000000000800000000000030000a5440230000000544022040008553081300000005308120400006530813000001201802300000000380220600150530813000000a0090030000000530412000001a530413000000002802205
  | 6, 3 => 0x8553081300000000480220200000000000080001253081300000065308130000189530403000000002802202000000380a202000000480a20400000000021030000a01900300000000480a205000000001210500000038062000000e544023000018021481300000000001210000012530413000001a53041300000005308120400000048022040000004802201000005308120400150530413000000e02802300000000000e1030000e01802300000000008010400000058c02050018c2050030000000038022060000002900200
  | 6, 4 => 0x18c5244130000000048022000000a53041300000000380a206000000000000800012028063000000a0190030000194038813000000000000008000000380a20100000400c020400000028c02050000000000008000005408120200000009002000008553041300000005308120400000544022000000000012103000000380a206000000000a10500002530813000000a01900300000000280220400000008c02040000000002105000000480220500000400c020400000000851080000a018023000000e514803000000003802204
  | 6, 5 => 0x48c02050000e544023000000e544023000018c52441300000000380a2040018c52441300000000280620000000530812040000e54402300000000000e105000000000e1000000a0180230000000038022040000000000001000000280220100000000000070018c105003000000e028063000000a0180230000000000000070001202806300000000000000a0000e009003000000e0280630000000000021020008553041300
  | 7, 0 => 0x2000000280220100000038022000000000002103000000280620000000540c12010000000002105000000000a104000005040e200000005140a200000000010010400000038022040000001802200000000190020000000530852000000000002101000000480220000000019002000000054402203000000000000a00000000021050000001802200000000380a204000000380220300000000021030000000002105000000000e10300000524412000000000080104000000010010100000028022040000000881200
  | 7, 1 => 0x90020300000000000020000000000004000000000210400000214412000000004881200000000000210000000000c0105000000000210300000048022010000002900203000000001210400000009002000000003881200000000380a2020000021500200000000008110400000059002000000000002105000000480220400000028022000000050085200000005440220300000048022000000000900203000002150020000000000c11060000000041100000000188120000000540c120100000000121040000004802200
  | 7, 2 => 0x210100000001001040000000002103000000000e105000000000a1060000052402200000005140220000000000c0104000002050020000000000c41000000053081200000005408120000000000000080000000002105000005304120000000000811040000000900200000000000e10100000000c11060000000002100000000000e104000000000000400000048062000000001900200000000000a10400000524c4200000005140220000000544022000000052402200000005240220000000000c910200000000c0105
  | 7, 3 => 0xc010400000000c110600000000021010000004802205000000000e104000000000000b00000000000050000000000004000000380a201000000010010000000000c1106000000480a201000005304120000000514c020000000028022000000004802201000000000a1000000053081200000000180220000000028022010000053002200000000000000900000000021010000000885200000000000000300000058c020000000000811030000054402204000000000a101000000000a10400000000021010000002802201
  | 7, 4 => 0x811030000000012104000000390020300000000000080000000002106000005440220000000000c0104000000480620000000540812000000005881200000000000000800000000021030000001802200000000000a102000000280620000000000021010000000002105000000480620000000000c1103000000000000b00000028c020000000000c010500000028412000000000900204000000280220000000038022000000004802201000000000e1010000003885200000000000000a000000001210100000000c9101
  | 7, 5 => 0x58412000000053081204000005000620000000000c9101000000480a20300000000c0105000000000000800000530412000000000000003000000000a105000005300220000000000000010000000000002000000588520000000000000020000003802202000000010010000000028c020500000000c0105000000280220000000000021030000004802203000000488520000000000811040000054402200000000380220000000524022000000000012102000000380a200000000000a10100000000c01050000053002200
  | 7, 6 => 0x2150020000000540c1202000000000210200000000c910300000008812000000000000009000000480620000000000000040000021441200000002148120000000000c1102000005148020000000000021010000001900200000000000e104000000010010400000544022040000054402200000005240220000000000000020000004802203000000000a10300000000000080000000000008000000000e10300000530412000000003802200000005408120100000530412000000010500200000000000a1010000000900200
  | 7, 7 => 0x10010300000000c91010000000100104000000000210000000000c910300000000121040000000000007000000480e202000000000a1060000001802200000000380a20000000000000010000004881200000005140220000000540812010000000100105000000010010500000000c910200000001001040000020500200000000380a2020000004802202000000480220000000500c520000000009002040000000900200000000280620000000000c1101000000480220000000105002000000053041200000000000a104
  | 7, 8 => 0x1900200000000280620000000000121020000000081104000000000a10100000000000080000001900200000000008110400000000c1106000000000a103000000000a10200000000121000000000002104000000000a1020000000081104000000000e10100000000000080000000000000000000000210400000514c0200000000000210600000530412000000000002105000000380a200000000000e102000000010010500000000c9106000000000e10100000530412000000000000008000000000e10500000058c0200
  | 7, 9 => 0x530852000000000000000000000000000a00000540812000000001802200000000000000500000028c0200000005000e200000000000a104000000000e100000000000a10500000038062000000002802200000000480220200000504062000000054402200000000000000a0000053002200000000480e2030000000080105000000584120000000038062000000000002106000000000000700000000021020000000002105000000000000100000000000010000002802202000000000000200000540812000000004841200
  | 7, 10 => 0x29002050000000900200000002150020000000028022030000000002101000000000000700000000c91010000003802200000000000a10300000048062000000005881200000000000a1030000004802200000000088520000000530412000000054081201000000000000100000038812000000004802200000000380220100000544022000000002900205000000000210300000000021020000002841200000000180220000000029002000000053081205000000380a2000000001802200000000001210000000000c1106
  | 7, 11 => 0x2900200000000000000000000000021010000000012103000000480a200000000001210400000000000080000000000001000000000a10400000105002000000000012105000000001210500000029002000000001802200000000000a101000000380a203000000088120000000000021050000000012104000000488120000000514022000000000002103000000000000800000530412000000004802204000000480220000000000c91010000004841200000000488520000000000c01050000053041200000000000e103
  | 7, 12 => 0x4806200000005300220000000000000080000054081202000000480620000000540c1202000000380a205000005140220000000038062000000003806200000000000a10100000000c01050000004806200000000010010400000000000010000054081200000000000e103000000000e1050000000002104000000088120000000540c1201000000000e1000000002802202000000000e10400000000000050000000002106000000588520000000000000080000053041200000000001210500000000c91060000000002103
  | 7, 13 => 0x21010000003881200000000000a1010000005881200000000480a205000000000a1040000003841200000000000a10300000058c020400000038022030000001881200000000480a201000000000000a0000000012102000000000e101000000380220000000000000050000003885200000000380a20400000530412000000003806200000000000000300000000c81040000000002101000000380a2030000054081205000000000e10300000524412000000000100104000000001210100000000021000000000002105
  | 7, 14 => 0x5308120000000530412000000000000002000000000e1010000000885200000000000a10300000038022000000004841200000000000210100000000c1106000000000e10500000000c91030000000006100000000480a2010000001802200000005408120200000008c0200000005308120000000000c91060000000002105000000480a2050000004802200000000000a104000000000210100000029002030000003806200000000488520000000000000080000000012101000000000000800000028022010000003806200
  | 7, 15 => 0xe103000000180220000000000c1103000000290020000000000c91030000000012104000000000210200000029002000000000081103000000000e100000000000000b0000000002105000000008110200000000000000000000002104000000000a10100000028c020000000000c01050000000006100000000000000800000540c1201000000000210500000000021050000053041200000000000000200000029002000000000881200000000008510800000008c0205000000000e1040000053041200000000480a200
  | 7, 16 => 0x100105000000000a106000000000000800000214812000000054081202000000480e202000000000210200000000801040000000000005000000008110500000000c0105000000380a2000000000081101000000380220000000029002040000003802200000000000a104000000480a20100000000021030000003885200000000000e102000000000e1010000003802200000000000000800000000000080000000000001000000280620000000540c1202000000180220000000058852000000001802200000000000a101
  | 7, 17 => 0x2802200000000480e2020000003806200000000088520000000000c1106000000380220000000524412000000003802203000000000a104000000180220000000000000070000000000007000000380220200000000c01040000054402205000000000210200000000c910600000018022000000002802205000000000a103000000480a20300000000021010000000100103000000000210100000038062000000000000008000000000e1050000051480200000000000e101000000000000000000000021040000000002103
  | 7, 18 => 0x210100000000851000000003881200000000000000b00000000021050000054402205000000090020500000008412000000004806200000000000210500000524c020000000000000000000000900200000005440220300000000c81040000000000005000000000210200000028c02000000000000003000000480a200000000000a10400000038022010000003802200000005408120000000008c02000000000900205000000000000b000000000a10100000544022050000053041200000000000000b0000002802205
  | 7, 19 => 0x8000000000a10600000000c010500000009002000000000002106000005308120000000214812000000004802200000000480a20400000000000040000000002104000000090020000000029002040000005841200000005440220000000000000080000053041200000000380620000000214c8200000000588520000000000811030000002806200000000480a2000000000900205000000000000a0000000000007000002150020000000009002030000021441200000005350020200000000000070000000002100
  | 7, 20 => 0x48852000000000000004000000480220300000000801040000053085200000005244120000000544022000000000002103000000000000b00000000021010000000000004000005304120000000048022050000000100104000000380620000000000c11030000053041200000000000000b000000480620000000028022030000053041200000000000210300000001001050000000000007000000000a10500000000021030000003802205000000001210300000514c020000000000c91060000000000008000000480a202
  | 7, 21 => 0x300000000021020000010500200000000004010000000000c01040000054402200000000280220400000514022000000053081204000000000210400000008c020000000000000070000000006100000000090020000000504c820000000048022000000000002106000000000000200000105002000000000002106000000480a20400000000000070000003802200000005440220000000018812000000000900200000000000000300000524c02000000000100104000000000210400000000c01040000004802205
  | 7, 22 => 0xb000005244120000000029002030000004802202000000000000b000000480a20100000038022000000000012101000000000e1000000002802202000000000000100000544022000000000081104000000000210100000540c92010000004802200000005408120000000000c1100000000488520000000544022050000000012104000000000000100000000021030000000000001000000090020000000000000070000000002103000000000000000000000c0105000000000000400000000021020000000002104
  | 7, 23 => 0x280220400000544022000000051402200000000480220000000000c01050000000000008000005440220000000058c020000000019002000000000002106000000000e1040000000081103000000088520000000001001030000003802204000000000e101000000000210100000500852000000001881200000000000000b00000000121040000000000001000005440220300000000811030000000002101000000090020000000000c5100000000000000800000000000010000003802200000000010010500000000c0105
  | 7, 24 => 0x2101000000090020000000000c01040000000012105000000480a20300000000021040000000000002000000000000200000214812000000054402200000000000000300000530022000000000900203000000000a10400000000c01000000000000000000005440220300000000000000000000900200000000000000b0000053081204000000000210600000009002000000053041200000000000000200000058852000000000000008000000000210400000029002000000000000003000000000e10500000008c0200
  | 7, 25 => 0x81101000000480a20000000000021030000000000000000000380a20100000048022010000052441200000000280620000000038412000000000002104000005304120000000048062000000000000003000000280620000000000021000000000012103000000000210600000000021030000003802200000000000000b00000000c010500000038852000000000002102000000380a201000000000000800000524c02000000000100100000000010010400000000021010000053081204000000000e1010000002806200
  | 7, 26 => 0x811060000000100100000000000000800000000c910300000214c02000000051002200000000380a2010000000012100000005440220000000000121040000054402200000000480220000000500852000000053085200000000090020000000000021010000000100105000000000000200000048022030000000002102000005440220000000000c9102000000000a10400000058c02000000000002103000005308120400000000c110300000048022000000000002106000000480220000000544022000000000000005
  | 7, 27 => 0x2103000000480220000000000c9103000005300220000000530852000000000900200000005440220000000000000070000000000003000005300220000000544022000000000100105000000000000800000000021030000003802200000000000000b000000000000b000000000000700000000021010000000900200000000180220000000000021050000000900200000005340220000000000021020000000000007000005440220000000028062000000054402200000005408120300000215002000000000002106
  | 7, 28 => 0x38852000000000002102000000008510000000048022020000002806200000000480220000000028062000000004802200000000280620000000038022000000003802200000000480220000000000000080000000000008000000000a1040000001900200000000380a202000000000000200000000021030000000012102000000000000100000000021000000000012100000000000000300000000021010000000000000000005008520000000000000000000053002200000005304120000000009002000000000000001
  | 7, 29 => 0x4802201000000380a203000005300220000000038022050000003802200000000000000800000524412000000000002103
  | 8, 0 => 0x6100000000010010000000000411000000000000003000000000000200000000851000000000000002000000004110000000000c11030000000041100000000000210100000000c9101000000000000600000000c0105000000000a1000000000000005000000000a1030000000081102000000000e102000000000a10000000000000040000000012100000000000210200000000c01040000000100100000000000000100000000c910300000000121030000000000004000000000000100000000811020000000012100
  | 8, 1 => 0x2102000000000000500000000021030000000000000000000000000400000000c910300000000000040000000002100000000000000100000000000080000000100104000000010010000000000021030000000081102000000000000300000000121000000000000003000000000000500000000c11020000000002100000000004110000000000021000000000002100000000000000300000000c0100000000000e100000000000a10000000000811030000000000000000000000210200000001001000000000000003
  | 8, 2 => 0xe1000000000100102000000000610000000000c0104000000000000100000000c11010000000006100000000000000300000000000040000000081105000000008110000000000121010000000000009000000010010500000001001010000000041100000000000e105000000000e100000000000a1010000000000002000000000e1030000000081105000000000a1040000000006100000000001210000000000c01000000000012100000000000e100000000000e10000000000000010000000012100000000000a105
  | 8, 3 => 0x5000000008510000000000021000000000002103000000000210200000000000010000000000001000000000000b000000000210500000000000050000000000000000000000000800000000021050000000041100000000004110000000000411000000000100103000000000000400000000c1101000000000000000000000000030000000012101000000000210000000000811000000000000005000000001210400000000121000000000000008000000010010300000000000080000000000005000000000a101
  | 8, 4 => 0xc1101000000008110300000000021000000000081100000000000e1020000000002101000000000210000000000c9101000000000000300000000121030000000100101000000000e1000000000002100000000000000800000000851000000000000006000000000610000000000c1101000000000000100000000000050000000041100000000000e10000000000121010000000002101000000001210500000000c9101000000000a100000000000210000000000021050000000002100000000000a1010000000000001
  | 8, 5 => 0x61000000000081104000000004110000000000000040000000006100000000000610000000000021000000000012102000000008510000000000021050000000000006000000000a10200000000c9102000000008110300000000021000000000002101000000008510000000000c910100000000021010000000000005000000000610000000000c1102000000001210200000000851000000000100104000000001210000000000811000000000000001000000000210400000000021000000000012103000000000e100
  | 8, 6 => 0x21000000000085100000000000000300000000811040000000002100000000008510000000000021000000000085100000000000e10300000000c01040000000000001000000000210200000000c910200000000411000000000000004000000000a102000000000000300000000021000000000081104000000000610000000000121040000000002102000000000210300000000c91020000000000007000000000a103000000000e100000000001210000000000021030000000085100000000000e101
  | 8, 7 => 0x81101000000000a105000000008110100000000811000000000000002000000000e100000000000e10000000000000050000000100101000000000210200000000c9102000000000000500000000c010000000000000040000000002104000000000210000000000411000000000085100000000000e100000000000000100000001001010000000006100000000000210300000000c910300000000c010500000000c0100000000000210000000000000010000000100102000000000a10100000000021000000000000001
  | 8, 8 => 0x1210500000000c010000000000c0100000000010010200000000000010000000002100000000000210000000000c9101000000000e105000000000000300000000811030000000100100000000001210000000000021000000000085100000000000210000000000c010000000001001000000000085100000000000000300000001001050000000000004000000008110000000000021010000000041100000000010010000000000c010000000000c01000000000002100000000008510000000000c01000000000100101
  | 8, 9 => 0x1001000000000100100000000000210000000000c0100000000001210000000000021010000000002105000000000210000000000851000000000002103000000000e1040000000002102000000000000100000000021050000000012102000000000e10000000000000020000000000001000000000210300000000c9103000000000000300000001001000000000000003000000010010200000000000020000000002105000000000000500000000c010000000001001000000000012100000000000000300000000c0100
  | 8, 10 => 0x210000000000121000000000002101000000001210100000000000040000000002101000000000000600000000021040000000000004000000010010000000000c010000000000c0100000000000210000000000851000000000100103000000000000b0000000002101
  | 9, 0 => 0x100000000000040000000000000000000000000300000000000030000000000005000000000000000000000000000000000000000000000000000200000000000000000000000003000000000000000000000000000000000000000000000000000200000000000000000000000002000000000000000000000000000000000000001000000000000100000000000000000000000001000000000000500000000000000000000000005
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 11 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_61 roots_61 9 s ws hint
  | 1 => checkCutEntry dom_31 roots_31 8 s ws hint
  | 2 => checkCutEntry dom_31_32 roots_31_32 8 s ws hint
  | 3 => checkCutEntry dom_47_16 roots_47_16 8 s ws hint
  | 4 => checkCutEntry dom_55 roots_55 8 s ws hint
  | 5 => checkCutEntry dom_59 roots_59 8 s ws hint
  | 6 => checkCutEntry dom_15_16 roots_15_16 7 s ws hint
  | 7 => checkCutEntry dom_47 roots_47 6 s ws hint
  | 8 => checkCutEntry dom_62_1 roots_62_1 6 s ws hint
  | 9 => checkCutEntry dom_39 roots_39 5 s ws hint
  | 10 => checkCutEntry dom_43 roots_43 5 s ws hint
  | 11 => checkCutEntry dom_30 roots_30 5 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31_32 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_55 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_59 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_62_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_39 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_43 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_30 _ hc
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
private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 16 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_16 : ∀ i, 16 ≤ i → i < 23 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 7 16 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 23 → Z 6 i = true := (range_split z6_0 z6_16)
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
private theorem z7_64 : ∀ i, 64 ≤ i → i < 76 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 64 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 76 → Z 7 i = true := (range_split (range_split (range_split z7_0 z7_16) (range_split z7_32 z7_48)) z7_64)
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
private theorem z8_48 : ∀ i, 48 ≤ i → i < 49 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 48 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 49 → Z 8 i = true := (range_split (range_split z8_0 z8_16) (range_split z8_32 z8_48))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_0 : ∀ i, 0 ≤ i → i < 9 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 9 0 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 9 → Z 9 i = true := z9_0
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

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 15]⟩], 16⟩

theorem wit_mono : PEqualNP.MetaComplexity.Monotone2 wit := by
  simp [wit, PEqualNP.MetaComplexity.Monotone2]

theorem wit_sz : wit.size ≤ 11 := by decide

set_option maxRecDepth 40000 in
theorem wit_ev : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = Nat.testBit (4276809448 * 2 ^ 32 + 4276669640) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel

set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_63.testBit r.val = (fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4276669640) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) (pt6 r.val) := by decide +kernel

theorem lower : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4276669640) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) t → 11 ≤ t :=
  lower_to_circuit6 (fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4276669640) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) goal_63 11 hT6 (by unfold IsConst; decide) low_63

end PEqualNP.Outside.L_meta_40453_aux

theorem PEqualNP.Outside.L_meta_40453 :
  ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4276669640) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809448 * 2 ^ 32 + 4276669640) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  exact ⟨PEqualNP.Outside.L_meta_40453_aux.wit, PEqualNP.Outside.L_meta_40453_aux.wit_mono, le_trans PEqualNP.Outside.L_meta_40453_aux.wit_sz (PEqualNP.Outside.L_meta_40453_aux.lower s hs), PEqualNP.Outside.L_meta_40453_aux.wit_ev⟩
