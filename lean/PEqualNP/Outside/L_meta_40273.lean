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

namespace PEqualNP.Outside.L_meta_40273_aux

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

section
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
end

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

def forceN {α : Type} (n : Nat) (k : Nat → α) : α := match n with | 0 => k 0 | m + 1 => k (m + 1)
theorem forceN_eq {α : Type} (n : Nat) (k : Nat → α) : forceN n k = k n := by cases n <;> rfl
def bsr (read : Nat → Nat) (h : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo + 1 < hi then
      forceN ((lo + hi) / 2) fun mid =>
      if read mid ≤ h then bsr read h f mid hi else bsr read h f lo mid
    else lo

def hw256 (seed w : Nat) : Nat :=
  forceN ((((w &&& 4294967295) ^^^ seed) * 2654435761 +
           (((w >>> 32) &&& 4294967295) ^^^ seed) * 2246822519) &&& 4294967295) fun x =>
  forceN (((x ^^^ (x >>> 16)) * 2246822519) &&& 4294967295) fun y =>
  ((y ^^^ (y >>> 13)) * 3266489917) &&& 4294967295

def hz (seed : Nat) : List Nat → Nat
  | [] => 0
  | w :: t => hw256 seed w + hz seed t

def hk (seed : Nat) (zs : List Nat) : Nat := hz seed zs &&& 4294967295

def found (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (s : Nat) (zs : List Nat) : Bool :=
  decide (idx s zs < N s) && zs.isPerm (S s (idx s zs))

def foundH (S : Nat → Nat → List Nat) (N : Nat → Nat) (htAt : Nat → Nat → Nat)
    (idxH : Nat → Nat → Nat) (s h : Nat) (zs : List Nat) : Bool :=
  forceN (idxH s h) fun i =>
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
         forceN (hk seed cz) fun h =>
         !(foundH S N htAt idxH s h cz) && !(cutHitH s h cz)))

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
         forceN (hk seed cz) fun h =>
         !(foundH S N htAt idxH s h cz) && !(cutHitH s h cz))
      have hF (zs) (hz : RunD dm (T &&& dm) s zs) : F zs = true := by
        have hcz := hr hz
        have hcutf : cutHitH s (hk seed (ori zs)) (ori zs) = false := by
          cases h : cutHitH s (hk seed (ori zs)) (ori zs) with
          | false => rfl
          | true => exact absurd hcz (hcut h)
        simp only [F, forceN_eq, coversP_ok hd pairs hpairs hz, scr_no pool hz, hcutf, Bool.not_false, Bool.true_and, Bool.and_true, foundH]
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
            forceN (hk seed cz) fun h =>
            !(foundH S N htAt idxH s h cz) && !(cutHitH s h cz)))) = F := by
        funext zs
        have hfst : (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))).map Prod.fst = zs := by
          simp [List.map_map, Function.comp_def]
        rw [coversD_eq, hfst]
        simp only [F, Bool.and_assoc]
      rw [hFeq, hN] at hb
      contradiction

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

theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with | nil => rfl | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
def goal_all : Nat := 0xfeeaece8eee0e0e0
def dom_63 : Nat := 0xffffffffffffffff
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]
def dom_x0_0_x3_1 : Nat := 0x5500550055005500
def roots_x0_0_x3_1 : List Nat := [0x4400440044004400, 0x5000500050005000, 0x5500000055000000, 0x5500550000000000]
def dom_x0_0_x4_1_x5_1 : Nat := 0x5555000000000000
def roots_x0_0_x4_1_x5_1 : List Nat := [0x4444000000000000, 0x5050000000000000, 0x5500000000000000]
def dom_x0_0_x4_1 : Nat := 0x5555000055550000
def roots_x0_0_x4_1 : List Nat := [0x4444000044440000, 0x5050000050500000, 0x5500000055000000, 0x5555000000000000]
def dom_x0_0_x5_1 : Nat := 0x5555555500000000
def roots_x0_0_x5_1 : List Nat := [0x4444444400000000, 0x5050505000000000, 0x5500550000000000, 0x5555000000000000]
def dom_x0_0 : Nat := 0x5555555555555555
def roots_x0_0 : List Nat := [0x4444444444444444, 0x5050505050505050, 0x5500550055005500, 0x5555000055550000, 0x5555555500000000]
def dom_x1_0_x3_1_x5_1 : Nat := 0x3300330000000000
def roots_x1_0_x3_1_x5_1 : List Nat := [0x2200220000000000, 0x3000300000000000, 0x3300000000000000]
def dom_x1_0_x5_1 : Nat := 0x3333333300000000
def roots_x1_0_x5_1 : List Nat := [0x2222222200000000, 0x3030303000000000, 0x3300330000000000, 0x3333000000000000]
def dom_x3_0_x4_0_x5_1 : Nat := 0xff00000000
def roots_x3_0_x4_0_x5_1 : List Nat := [0xaa00000000, 0xcc00000000, 0xf000000000]
def dom_x3_0_x5_1 : Nat := 0xff00ff00000000
def roots_x3_0_x5_1 : List Nat := [0xaa00aa00000000, 0xcc00cc00000000, 0xf000f000000000, 0xff000000000000]
def dom_x4_0_x5_1 : Nat := 0xffff00000000
def roots_x4_0_x5_1 : List Nat := [0xaaaa00000000, 0xcccc00000000, 0xf0f000000000, 0xff0000000000]
def dom_x3_1_x5_1 : Nat := 0xff00ff0000000000
def roots_x3_1_x5_1 : List Nat := [0xaa00aa0000000000, 0xcc00cc0000000000, 0xf000f00000000000, 0xff00000000000000]
def dom_x4_1_x5_1 : Nat := 0xffff000000000000
def roots_x4_1_x5_1 : List Nat := [0xaaaa000000000000, 0xcccc000000000000, 0xf0f0000000000000, 0xff00000000000000]
def dom_x5_1 : Nat := 0xffffffff00000000
def roots_x5_1 : List Nat := [0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000]
def dom_x1_0_x4_1 : Nat := 0x3333000033330000
def roots_x1_0_x4_1 : List Nat := [0x2222000022220000, 0x3030000030300000, 0x3300000033000000, 0x3333000000000000]
def dom_x1_0_x3_1 : Nat := 0x3300330033003300
def roots_x1_0_x3_1 : List Nat := [0x2200220022002200, 0x3000300030003000, 0x3300000033000000, 0x3300330000000000]
def dom_x1_0 : Nat := 0x3333333333333333
def roots_x1_0 : List Nat := [0x2222222222222222, 0x3030303030303030, 0x3300330033003300, 0x3333000033330000, 0x3333333300000000]
def dom_x3_1 : Nat := 0xff00ff00ff00ff00
def roots_x3_1 : List Nat := [0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000]
def dom_x4_1 : Nat := 0xffff0000ffff0000
def roots_x4_1 : List Nat := [0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000]
def dom_x2_0 : Nat := 0xf0f0f0f0f0f0f0f
def roots_x2_0 : List Nat := [0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000]
def dom_x3_0_x4_0 : Nat := 0xff000000ff
def roots_x3_0_x4_0 : List Nat := [0xaa000000aa, 0xcc000000cc, 0xf0000000f0, 0xff00000000]
def dom_x3_0 : Nat := 0xff00ff00ff00ff
def roots_x3_0 : List Nat := [0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000]
def dom_x4_0 : Nat := 0xffff0000ffff
def roots_x4_0 : List Nat := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]

namespace S_x0_0_x3_1
def pairsG : List (Nat × Nat) := [(10, 14), (10, 26), (10, 42), (12, 14), (24, 26), (28, 30), (28, 60), (40, 42), (44, 46), (44, 60), (56, 58), (56, 60)]
def r1sG : List Nat := [10, 10, 10, 12, 24, 28, 28, 40, 44, 44, 56, 56]
def r2sG : List Nat := [14, 26, 42, 14, 26, 30, 60, 42, 46, 60, 58, 60]
def mpG : Nat := 0xfff
def pool6G : List Nat := [30830017391130, 30830218713614, 48421934992938, 48422404758030]
def xsM : List Nat := roots_x0_0_x3_1.map (· &&& dom_x0_0_x3_1)
def goalM : Nat := goal_all &&& dom_x0_0_x3_1
def NN : Nat → Nat
  | 4 => 5
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0xb21e852da4d56d409e62cb8d7731f1d07693318f
  | 5, 0, 0 => 0x7693318f
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x550055000000550000005500050005000500050011001100110011005500550000000000550000005500000050005000500050004400440044004400
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x44746464685468c46884
  | 5, 0, 0 => 0x6884
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 16
  | 5 => 16
  | _ => 0
def stateM : Nat → Nat
  | 4 => 0xffff
  | 5 => 0xffff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0x7f000000000000038f0000000000000c970000000000000ff80000000000000f800000000000000c7000000000000003680000000000000007
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x3b000000000000018d00000000000004960000000000000a400000000000000fc40000000000000e720000000000000b6900000000000005bf
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 8 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 8 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 8 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 8 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 8 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => [] | n + 1, ids => wireDAt (ids &&& 0x7) :: stateWiresD n (ids >>> 3)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => [] | n + 1, ids => wireSAt (ids &&& 0x7) :: stateWiresS n (ids >>> 3)
def SD (s j : Nat) : List (Nat × Nat × Nat) := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) : stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with | zero => rfl | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) : SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := stateWiresD_eq _ _
def htAt (s i : Nat) : Nat := (HT s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def idxH (s h : Nat) : Nat := bsr (htAt s) h 4 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 2 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x0_0_x3_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x0_0_x3_1 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x0_0_x3_1 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x0_0_x3_1 goalM u ys) : RunD dom_x0_0_x3_1 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x0_0_x3_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 5) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool := scr dom_x0_0_x3_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 3 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_x0_0_x3_1 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x0_0_x3_1 roots_x0_0_x3_1 goal_all 6 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x0_0_x3_1 goal_all := by
    have h0 : isConstB dom_x0_0_x3_1 goal_all = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub; have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq; rw [hcov] at hbad; contradiction
end S_x0_0_x3_1
theorem low_x0_0_x3_1 : Lower dom_x0_0_x3_1 roots_x0_0_x3_1 goal_all 6 := S_x0_0_x3_1.noCircuit

namespace S_x0_0_x4_1_x5_1
def pairsG : List (Nat × Nat) := [(50, 54), (50, 58), (52, 54), (52, 60), (56, 58), (56, 60)]
def r1sG : List Nat := [50, 50, 52, 52, 56, 56]
def r2sG : List Nat := [54, 58, 54, 60, 58, 60]
def mpG : Nat := 0x3f
def pool6G : List Nat := [57390296480310]
def xsM : List Nat := roots_x0_0_x4_1_x5_1.map (· &&& dom_x0_0_x4_1_x5_1)
def goalM : Nat := goal_all &&& dom_x0_0_x4_1_x5_1
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x7228e998
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x550000000000000050500000000000004444000000000000
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x243
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 10
  | _ => 0
def stateM : Nat → Nat
  | 3 => 0x3ff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0x30000000000000000c0000000000000003
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x3a000000000000002d0000000000000017
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 3 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 3 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 3 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 3 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 3 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => [] | n + 1, ids => wireDAt (ids &&& 0x3) :: stateWiresD n (ids >>> 2)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => [] | n + 1, ids => wireSAt (ids &&& 0x3) :: stateWiresS n (ids >>> 2)
def SD (s j : Nat) : List (Nat × Nat × Nat) := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) : stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with | zero => rfl | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) : SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := stateWiresD_eq _ _
def htAt (s i : Nat) : Nat := (HT s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 2 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x0_0_x4_1_x5_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x0_0_x4_1_x5_1 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x0_0_x4_1_x5_1 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x0_0_x4_1_x5_1 goalM u ys) : RunD dom_x0_0_x4_1_x5_1 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x0_0_x4_1_x5_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool := scr dom_x0_0_x4_1_x5_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x0_0_x4_1_x5_1 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x0_0_x4_1_x5_1 roots_x0_0_x4_1_x5_1 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x0_0_x4_1_x5_1 goal_all := by
    have h0 : isConstB dom_x0_0_x4_1_x5_1 goal_all = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub; have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq; rw [hcov] at hbad; contradiction
end S_x0_0_x4_1_x5_1
theorem low_x0_0_x4_1_x5_1 : Lower dom_x0_0_x4_1_x5_1 roots_x0_0_x4_1_x5_1 goal_all 4 := S_x0_0_x4_1_x5_1.noCircuit

theorem low_x0_0_x4_1 : Lower dom_x0_0_x4_1 roots_x0_0_x4_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5555000000000000, 28, 60)] (by decide +kernel) (by decide +kernel) low_x0_0_x4_1_x5_1

theorem low_x0_0_x5_1 : Lower dom_x0_0_x5_1 roots_x0_0_x5_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5555000000000000, 44, 60)] (by decide +kernel) (by decide +kernel) low_x0_0_x4_1_x5_1

namespace S_x0_0
def pairsG : List (Nat × Nat) := [(2, 6), (4, 6), (10, 14), (10, 26), (10, 42), (12, 14), (18, 22), (18, 26), (20, 22), (24, 26), (28, 30), (28, 60), (34, 38), (34, 42), (36, 38), (40, 42), (44, 46), (44, 60), (50, 54), (50, 58), (52, 54), (52, 60), (56, 58), (56, 60)]
def r1sG : List Nat := [2, 4, 10, 10, 10, 12, 18, 18, 20, 24, 28, 28, 34, 34, 36, 40, 44, 44, 50, 50, 52, 52, 56, 56]
def r2sG : List Nat := [6, 6, 14, 26, 42, 14, 22, 26, 22, 26, 30, 60, 38, 42, 38, 42, 46, 60, 54, 58, 54, 60, 58, 60]
def mpG : Nat := 0xffffff
def pool6G : List Nat := [30830017391130, 55096716822042, 30830218717702, 61761799194172, 48421934996010, 55165436298794]
def xsM : List Nat := roots_x0_0.map (· &&& dom_x0_0)
def goalM : Nat := goal_all &&& dom_x0_0
def NN : Nat → Nat
  | 4 => 1
  | 5 => 9
  | 6 => 12
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x18ff61a4
  | 5, 0, 0 => 0xb916002ead54f17b9ec973065520dbb94a70dfc03b0dd7452495b66f226651e717b655ee
  | 6, 0, 0 => 0xfd6d7d12f9219bcdef945754e96adfeab9f5ec8eb88e7d9fa92b75249e7b792b85d3f3cd4a8681083ee011902957f7c7
  | 7, 0, 0 => 0xc99170a
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x4444444400000000444400004444000054545454000000005454000054540000444444444444444454545454545454540000000055555555505050505050505000005555000055555500550055005500111111111111111105050505050505055555555500000000555500005555000054005400540054004040404040404040
  | 1 => 0x50505050000000005050000050500000
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x188204
  | 5, 0, 0 => 0x31050b5119a85a8c465014465912a2320a95188c5228ccc42d466590ea3320a75
  | 6, 0, 0 => 0x188c85b98623222b6188c85bd8623220b6188c859180232169500c4659140311905500cc859d462321656188ca42d862321606
  | 7, 0, 0 => 0x31190b5
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 24
  | 5 => 29
  | 6 => 34
  | 7 => 29
  | _ => 0
def stateM : Nat → Nat
  | 4 => 0xffffff
  | 5 => 0x1fffffff
  | 6 => 0x3ffffffff
  | 7 => 0x1fffffff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0xc300000000000000c00c000000000003f700000000000003c0dc000000000000c30dd00000000003f7dff0000000000000fff0000000000334d22000000000003f03f0000000000c38e3c0000000000f3cf220000000000ccb2dd0000000000fff0000000000000fc0fc00000000000030c3c0000000000000000
  | 1 => 0x3340000000000000300d00
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x5df01000000000005c07c80000000000fff8100000000000fe0fc800000000005df7ff0000000000ffffff00000000000007ef0000000000b75d67000000000001f0370000000000ebaebc0000000000a20800000000000048a2980000000000fff8100000000000fe0fc80000000000ebaebc0000000000155567
  | 1 => 0xb758000000000000b60d40
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 18 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 18 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 18 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 18 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 18 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => [] | n + 1, ids => wireDAt (ids &&& 0x1f) :: stateWiresD n (ids >>> 5)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => [] | n + 1, ids => wireSAt (ids &&& 0x1f) :: stateWiresS n (ids >>> 5)
def SD (s j : Nat) : List (Nat × Nat × Nat) := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) : stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with | zero => rfl | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) : SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := stateWiresD_eq _ _
def htAt (s i : Nat) : Nat := (HT s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def idxH (s h : Nat) : Nat := bsr (htAt s) h 5 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 5 => 12
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xf6fd0ad0d0f31148c643154fc6330426b6cffbabad9b8ff1ac1fffb293787a54935ce4606fec06cc11100f4401ad06c9
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x8400000000610000000008400000000e10000000018400000000a10000000008400000000a10000000028400000000e100000000384000000006100
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 5 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_x0_0_x3_1 roots_x0_0_x3_1 6 s ws hint
  | 1 => checkCutEntry dom_x0_0_x4_1 roots_x0_0_x4_1 5 s ws hint
  | 2 => checkCutEntry dom_x0_0_x5_1 roots_x0_0_x5_1 5 s ws hint
  | 3 => checkCutEntry dom_x0_0_x4_1_x5_1 roots_x0_0_x4_1_x5_1 4 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x0_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x3_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_1_x5_1 _ hc
  · contradiction
def p0Subs : List Nat := [0, 1, 2, 3]
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)) ||
  p0Subs.any (fun k => checkCutByIdx s ws k)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x0_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq, Bool.or_eq_true] at h; rcases h with h1 | h0
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2
  · obtain ⟨k, _, hk⟩ := List.any_eq_true.1 h0; exact checkCutByIdx_sound hk
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x0_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x0_0 goalM u ys) : RunD dom_x0_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x0_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 9 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 12 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
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
def RootG (s : Nat) : Bool := scr dom_x0_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_x0_0 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x0_0 roots_x0_0 goal_all 8 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x0_0 goal_all := by
    have h0 : isConstB dom_x0_0 goal_all = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub; have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq; rw [hcov] at hbad; contradiction
end S_x0_0
theorem low_x0_0 : Lower dom_x0_0 roots_x0_0 goal_all 8 := S_x0_0.noCircuit

namespace S_x1_0_x3_1_x5_1
def pairsG : List (Nat × Nat) := [(41, 45), (41, 57), (44, 45), (44, 60), (56, 57), (56, 60)]
def r1sG : List Nat := [41, 41, 44, 44, 56, 56]
def r2sG : List Nat := [45, 57, 45, 60, 57, 60]
def mpG : Nat := 0x3f
def pool6G : List Nat := [48555548752173]
def xsM : List Nat := roots_x1_0_x3_1_x5_1.map (· &&& dom_x1_0_x3_1_x5_1)
def goalM : Nat := goal_all &&& dom_x1_0_x3_1_x5_1
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xe580895f
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x330000000000000030003000000000002200220000000000
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x243
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 10
  | _ => 0
def stateM : Nat → Nat
  | 3 => 0x3ff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0x30000000000000000c0000000000000003
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x3a000000000000002d0000000000000017
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 3 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 3 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 3 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 3 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 3 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => [] | n + 1, ids => wireDAt (ids &&& 0x3) :: stateWiresD n (ids >>> 2)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => [] | n + 1, ids => wireSAt (ids &&& 0x3) :: stateWiresS n (ids >>> 2)
def SD (s j : Nat) : List (Nat × Nat × Nat) := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) : stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with | zero => rfl | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) : SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := stateWiresD_eq _ _
def htAt (s i : Nat) : Nat := (HT s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 2 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x1_0_x3_1_x5_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x1_0_x3_1_x5_1 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x1_0_x3_1_x5_1 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x1_0_x3_1_x5_1 goalM u ys) : RunD dom_x1_0_x3_1_x5_1 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x1_0_x3_1_x5_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool := scr dom_x1_0_x3_1_x5_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x1_0_x3_1_x5_1 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x1_0_x3_1_x5_1 roots_x1_0_x3_1_x5_1 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x1_0_x3_1_x5_1 goal_all := by
    have h0 : isConstB dom_x1_0_x3_1_x5_1 goal_all = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub; have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq; rw [hcov] at hbad; contradiction
end S_x1_0_x3_1_x5_1
theorem low_x1_0_x3_1_x5_1 : Lower dom_x1_0_x3_1_x5_1 roots_x1_0_x3_1_x5_1 goal_all 4 := S_x1_0_x3_1_x5_1.noCircuit

theorem low_x1_0_x5_1 : Lower dom_x1_0_x5_1 roots_x1_0_x5_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x3300330000000000, 52, 60)] (by decide +kernel) (by decide +kernel) low_x1_0_x3_1_x5_1

namespace S_x3_0_x4_0_x5_1
def pairsG : List (Nat × Nat) := [(33, 35), (33, 37), (34, 35), (34, 38), (36, 37), (36, 38)]
def r1sG : List Nat := [33, 33, 34, 34, 36, 36]
def r2sG : List Nat := [35, 37, 35, 38, 37, 38]
def mpG : Nat := 0x3f
def pool6G : List Nat := [37525735744803]
def xsM : List Nat := roots_x3_0_x4_0_x5_1.map (· &&& dom_x3_0_x4_0_x5_1)
def goalM : Nat := goal_all &&& dom_x3_0_x4_0_x5_1
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xd942fcfb
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xf000000000000000cc00000000000000aa00000000
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x243
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 10
  | _ => 0
def stateM : Nat → Nat
  | 3 => 0x3ff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0x30000000000000000c0000000000000003
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x3a000000000000002d0000000000000017
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 3 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 3 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 3 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 3 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 3 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => [] | n + 1, ids => wireDAt (ids &&& 0x3) :: stateWiresD n (ids >>> 2)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => [] | n + 1, ids => wireSAt (ids &&& 0x3) :: stateWiresS n (ids >>> 2)
def SD (s j : Nat) : List (Nat × Nat × Nat) := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) : stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with | zero => rfl | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) : SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := stateWiresD_eq _ _
def htAt (s i : Nat) : Nat := (HT s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 2 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x3_0_x4_0_x5_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x3_0_x4_0_x5_1 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x3_0_x4_0_x5_1 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x3_0_x4_0_x5_1 goalM u ys) : RunD dom_x3_0_x4_0_x5_1 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x3_0_x4_0_x5_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool := scr dom_x3_0_x4_0_x5_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x3_0_x4_0_x5_1 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x3_0_x4_0_x5_1 roots_x3_0_x4_0_x5_1 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x3_0_x4_0_x5_1 goal_all := by
    have h0 : isConstB dom_x3_0_x4_0_x5_1 goal_all = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub; have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq; rw [hcov] at hbad; contradiction
end S_x3_0_x4_0_x5_1
theorem low_x3_0_x4_0_x5_1 : Lower dom_x3_0_x4_0_x5_1 roots_x3_0_x4_0_x5_1 goal_all 4 := S_x3_0_x4_0_x5_1.noCircuit

theorem low_x3_0_x5_1 : Lower dom_x3_0_x5_1 roots_x3_0_x5_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff000000000000, 33, 49)] (by decide +kernel) (by decide +kernel) low_x3_0_x4_0_x5_1

theorem low_x4_0_x5_1 : Lower dom_x4_0_x5_1 roots_x4_0_x5_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff0000000000, 34, 42)] (by decide +kernel) (by decide +kernel) low_x3_0_x4_0_x5_1

theorem low_x3_1_x5_1 : Lower dom_x3_1_x5_1 roots_x3_1_x5_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc00cc0000000000, 40, 42)] (by decide +kernel) (by decide +kernel) low_x1_0_x3_1_x5_1

theorem low_x4_1_x5_1 : Lower dom_x4_1_x5_1 roots_x4_1_x5_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa000000000000, 48, 49)] (by decide +kernel) (by decide +kernel) low_x0_0_x4_1_x5_1

namespace S_x5_1
def pairsG : List (Nat × Nat) := [(33, 35), (33, 37), (33, 49), (34, 35), (34, 38), (34, 42), (36, 37), (36, 38), (40, 42), (41, 43), (41, 45), (41, 57), (44, 45), (44, 46), (44, 60), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [33, 33, 33, 34, 34, 34, 36, 36, 40, 41, 41, 41, 44, 44, 44, 48, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [35, 37, 49, 35, 38, 42, 37, 38, 42, 43, 45, 57, 45, 46, 60, 49, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := [61749486953777, 61788275877418, 55165436306986, 61762320803132, 57390296476198, 57351440442673, 55152617794083]
def xsM : List Nat := roots_x5_1.map (· &&& dom_x5_1)
def goalM : Nat := goal_all &&& dom_x5_1
def NN : Nat → Nat
  | 5 => 10
  | 6 => 12
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xf69a2bdcdbed3bd2d129852fca328ef09679e0108c04abbb41067208169ce0f10854d8be009e3c06
  | 6, 0, 0 => 0xfea03031e9a78c85d4369f1ac5ee96e7c3c729e0be37fa2fb433ea0595a507ef8ec34358499e69e43bd8c2aa009e3c06
  | 7, 0, 0 => 0xbe37fa2f
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xfcfcfcfc00000000fafafafa00000000eeeeeeee00000000ffffcccc000000000000ffff00000000ffaaffaa0000000000ff00ff00000000f0f0f0f00000000055555555000000003333333300000000ffff000000000000ff00ff0000000000cccccccc00000000aaaaaaaa000000000f0f0f0f00000000
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x3210a54376554210853715a5472685492105b32105431505432605432105
  | 6, 0, 0 => 0xb3721543e721604371550437265437c216043721503721a543721060472185049721543d72160432105
  | 7, 0, 0 => 0x437215
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 24
  | 6 => 28
  | 7 => 24
  | _ => 0
def stateM : Nat → Nat
  | 5 => 0xffffff
  | 6 => 0xfffffff
  | 7 => 0xffffff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0x3f70f80000000000387ec70000000000070e3f0000000001ff80380000000000007fff0000000001c07f0700000000003f80ff00000000003870c00000000001fff1f80000000001f8ffc70000000001ff80000000000001c07f0000000000000700380000000000000e070000000001c78f3f
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x1bf77fb00000000017bfedf0000000000dfbfff0000000001ffebbd00000000000037fb0000000001edff6f00000000001b80df00000000013a74d20000000001b661b0000000000168dc460000000001ffc8040000000001e47f2000000000009723b90000000000499e4f0000000000c58b2d
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 15 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 15 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 15 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 15 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 15 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => [] | n + 1, ids => wireDAt (ids &&& 0xf) :: stateWiresD n (ids >>> 4)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => [] | n + 1, ids => wireSAt (ids &&& 0xf) :: stateWiresS n (ids >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) : stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with | zero => rfl | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) : SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := stateWiresD_eq _ _
def htAt (s i : Nat) : Nat := (HT s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def idxH (s h : Nat) : Nat := bsr (htAt s) h 5 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 2 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_x0_0_x5_1 roots_x0_0_x5_1 5 s ws hint
  | 1 => checkCutEntry dom_x1_0_x5_1 roots_x1_0_x5_1 5 s ws hint
  | 2 => checkCutEntry dom_x3_0_x5_1 roots_x3_0_x5_1 5 s ws hint
  | 3 => checkCutEntry dom_x4_0_x5_1 roots_x4_0_x5_1 5 s ws hint
  | 4 => checkCutEntry dom_x0_0_x4_1_x5_1 roots_x0_0_x4_1_x5_1 4 s ws hint
  | 5 => checkCutEntry dom_x1_0_x3_1_x5_1 roots_x1_0_x3_1_x5_1 4 s ws hint
  | 6 => checkCutEntry dom_x3_1_x5_1 roots_x3_1_x5_1 5 s ws hint
  | 7 => checkCutEntry dom_x4_1_x5_1 roots_x4_1_x5_1 5 s ws hint
  | 8 => checkCutEntry dom_x3_0_x4_0_x5_1 roots_x3_0_x4_0_x5_1 4 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x5_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x3_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x4_0_x5_1 _ hc
  · contradiction
def p0Subs : List Nat := [0, 1, 2, 6, 3, 4, 7, 5, 8]
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)) ||
  p0Subs.any (fun k => checkCutByIdx s ws k)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x5_1 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq, Bool.or_eq_true] at h; rcases h with h1 | h0
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2
  · obtain ⟨k, _, hk⟩ := List.any_eq_true.1 h0; exact checkCutByIdx_sound hk
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x5_1 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x5_1 goalM u ys) : RunD dom_x5_1 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x5_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 12 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
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
def RootG (s : Nat) : Bool := scr dom_x5_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_x5_1 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x5_1 roots_x5_1 goal_all 8 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x5_1 goal_all := by
    have h0 : isConstB dom_x5_1 goal_all = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub; have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq; rw [hcov] at hbad; contradiction
end S_x5_1
theorem low_x5_1 : Lower dom_x5_1 roots_x5_1 goal_all 8 := S_x5_1.noCircuit

namespace S_x1_0_x4_1
def pairsG : List (Nat × Nat) := [(17, 21), (17, 25), (17, 49), (20, 21), (24, 25), (28, 29), (28, 60), (48, 49), (52, 53), (52, 60), (56, 57), (56, 60)]
def r1sG : List Nat := [17, 17, 17, 20, 24, 28, 28, 48, 52, 52, 56, 56]
def r2sG : List Nat := [21, 25, 49, 21, 25, 29, 60, 49, 53, 60, 57, 60]
def mpG : Nat := 0xfff
def pool6G : List Nat := [30860216381721, 30860283484437, 57248092788017, 57248562551061]
def xsM : List Nat := roots_x1_0_x4_1.map (· &&& dom_x1_0_x4_1)
def goalM : Nat := goal_all &&& dom_x1_0_x4_1
def NN : Nat → Nat
  | 4 => 5
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0xaf0580ed7fcd688c226ca2290b55417b0aa44f0a
  | 5, 0, 0 => 0x7fcd688c
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x333300000033000000330000030300000303000011110000111100003333000000000000330000003300000030300000303000002222000022220000
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x447468846464685468c4
  | 5, 0, 0 => 0x6884
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 16
  | 5 => 16
  | _ => 0
def stateM : Nat → Nat
  | 4 => 0xffff
  | 5 => 0xffff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0x7f000000000000038f0000000000000c970000000000000ff80000000000000f800000000000000c7000000000000003680000000000000007
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x3b000000000000018d00000000000004960000000000000a400000000000000fc40000000000000e720000000000000b6900000000000005bf
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 8 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 8 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 8 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 8 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 8 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => [] | n + 1, ids => wireDAt (ids &&& 0x7) :: stateWiresD n (ids >>> 3)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => [] | n + 1, ids => wireSAt (ids &&& 0x7) :: stateWiresS n (ids >>> 3)
def SD (s j : Nat) : List (Nat × Nat × Nat) := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) : stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with | zero => rfl | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) : SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := stateWiresD_eq _ _
def htAt (s i : Nat) : Nat := (HT s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def idxH (s h : Nat) : Nat := bsr (htAt s) h 4 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 2 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x1_0_x4_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x1_0_x4_1 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x1_0_x4_1 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x1_0_x4_1 goalM u ys) : RunD dom_x1_0_x4_1 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x1_0_x4_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 5) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool := scr dom_x1_0_x4_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 3 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_x1_0_x4_1 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x1_0_x4_1 roots_x1_0_x4_1 goal_all 6 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x1_0_x4_1 goal_all := by
    have h0 : isConstB dom_x1_0_x4_1 goal_all = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub; have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq; rw [hcov] at hbad; contradiction
end S_x1_0_x4_1
theorem low_x1_0_x4_1 : Lower dom_x1_0_x4_1 roots_x1_0_x4_1 goal_all 6 := S_x1_0_x4_1.noCircuit

theorem low_x1_0_x3_1 : Lower dom_x1_0_x3_1 roots_x1_0_x3_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x3300330000000000, 28, 60)] (by decide +kernel) (by decide +kernel) low_x1_0_x3_1_x5_1

namespace S_x1_0
def pairsG : List (Nat × Nat) := [(1, 5), (4, 5), (9, 13), (9, 25), (12, 13), (17, 21), (17, 25), (17, 49), (20, 21), (24, 25), (28, 29), (28, 60), (33, 37), (33, 49), (36, 37), (41, 45), (41, 57), (44, 45), (44, 60), (48, 49), (52, 53), (52, 60), (56, 57), (56, 60)]
def r1sG : List Nat := [1, 4, 9, 9, 12, 17, 17, 17, 20, 24, 28, 28, 33, 33, 36, 41, 41, 44, 44, 48, 52, 52, 56, 56]
def r2sG : List Nat := [5, 5, 13, 25, 13, 21, 25, 49, 21, 25, 29, 60, 37, 49, 37, 45, 57, 45, 60, 49, 53, 60, 57, 60]
def mpG : Nat := 0xffffff
def pool6G : List Nat := [30860216381721, 45200977954073, 30860283490565, 61796276307260, 57248092789041, 57351440434481]
def xsM : List Nat := roots_x1_0.map (· &&& dom_x1_0)
def goalM : Nat := goal_all &&& dom_x1_0
def NN : Nat → Nat
  | 4 => 1
  | 5 => 9
  | 6 => 12
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x804cbb24
  | 5, 0, 0 => 0xf6b9c127f62dadc8af7648c1aeea356261c1332d449fb97141b0659928938e011ef1044d
  | 6, 0, 0 => 0xe3c1d732e335c3d3e054aec2d3b21256c2a4578ba323d1d6938a2981782e51cd36487f0130ead96726460bbe1acbddc7
  | 7, 0, 0 => 0x653667d8
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x2222222200000000220022002200220032323232000000003200320032003200222222222222222232323232323232320000000033333333303030303030303000330033003300333333000033330000111111111111111103030303030303033333333300000000330033003300330032320000323200002020202020202020
  | 1 => 0x30303030000000003000300030003000
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x188204
  | 5, 0, 0 => 0x6120a95309644a8cc829d466590ea3308a45309a85a8cc25014666216a31050b5
  | 6, 0, 0 => 0xcc24154033096451984a42d8661216e6198485bd86612165619848591806121695198485818033216751984882d8661222b6
  | 7, 0, 0 => 0x33090b5
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 24
  | 5 => 29
  | 6 => 34
  | 7 => 29
  | _ => 0
def stateM : Nat → Nat
  | 4 => 0xffffff
  | 5 => 0x1fffffff
  | 6 => 0x3ffffffff
  | 7 => 0x1fffffff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0x1b000000000000001800c000000000037f0000000000000078c1c000000000001b0ed000000000037fdff0000000000000fff0000000000364d1200000000003871e30000000000f80fe00000000000fe4f120000000000c9b2ed0000000000fff0000000000000c78e1c0000000000300de00000000000000000
  | 1 => 0x3640000000000000060c10
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x5bf080000000000043865c0000000000fff8800000000000e78e5c00000000005bf7ff0000000000ffffff000000000000077f0000000000b6dd3700000000001871a30000000000fd2fe80000000000a4080000000000004922c80000000000fff8800000000000e78e5c0000000000fd2fe8000000000012d537
  | 1 => 0xb6d8000000000000a68c14
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 18 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 18 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 18 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 18 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 18 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => [] | n + 1, ids => wireDAt (ids &&& 0x1f) :: stateWiresD n (ids >>> 5)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => [] | n + 1, ids => wireSAt (ids &&& 0x1f) :: stateWiresS n (ids >>> 5)
def SD (s j : Nat) : List (Nat × Nat × Nat) := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) : stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with | zero => rfl | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) : SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := stateWiresD_eq _ _
def htAt (s i : Nat) : Nat := (HT s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def idxH (s h : Nat) : Nat := bsr (htAt s) h 5 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 5 => 12
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xf71871dff68c5e80e85c0296c1a356698b84ec7a7803523e747a543473ee40d553ef87fb5363749c444174142526fd3b
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x8400000000610000000038400000000a10000000038400000000a10000000008400000000610000000008400000000610000000028400000000e100
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 5 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_x1_0_x4_1 roots_x1_0_x4_1 6 s ws hint
  | 1 => checkCutEntry dom_x1_0_x3_1 roots_x1_0_x3_1 5 s ws hint
  | 2 => checkCutEntry dom_x1_0_x5_1 roots_x1_0_x5_1 5 s ws hint
  | 3 => checkCutEntry dom_x1_0_x3_1_x5_1 roots_x1_0_x3_1_x5_1 4 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x1_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x3_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x3_1_x5_1 _ hc
  · contradiction
def p0Subs : List Nat := [0, 1, 2, 3]
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)) ||
  p0Subs.any (fun k => checkCutByIdx s ws k)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x1_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq, Bool.or_eq_true] at h; rcases h with h1 | h0
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2
  · obtain ⟨k, _, hk⟩ := List.any_eq_true.1 h0; exact checkCutByIdx_sound hk
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x1_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x1_0 goalM u ys) : RunD dom_x1_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x1_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 9 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 12 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
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
def RootG (s : Nat) : Bool := scr dom_x1_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_x1_0 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x1_0 roots_x1_0 goal_all 8 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x1_0 goal_all := by
    have h0 : isConstB dom_x1_0 goal_all = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub; have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq; rw [hcov] at hbad; contradiction
end S_x1_0
theorem low_x1_0 : Lower dom_x1_0 roots_x1_0 goal_all 8 := S_x1_0.noCircuit

theorem low_x3_1 : Lower dom_x3_1 roots_x3_1 goal_all 7 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaa00aa00aa00aa00, 12, 13)] (by decide +kernel) (by decide +kernel) low_x0_0_x3_1

theorem low_x4_1 : Lower dom_x4_1 roots_x4_1 goal_all 7 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcccc0000cccc0000, 20, 22)] (by decide +kernel) (by decide +kernel) low_x1_0_x4_1

namespace S_x2_0
def pairsG : List (Nat × Nat) := [(3, 35), (9, 25), (10, 26), (10, 42), (11, 27), (11, 43), (17, 25), (17, 49), (18, 26), (19, 27), (19, 51), (24, 25), (24, 26), (33, 35), (33, 49), (34, 35), (34, 42), (40, 42), (41, 43), (41, 57), (48, 49), (50, 51), (50, 58), (56, 57), (56, 58)]
def r1sG : List Nat := [3, 9, 10, 10, 11, 11, 17, 17, 18, 19, 19, 24, 24, 33, 33, 34, 34, 40, 41, 41, 48, 50, 50, 56, 56]
def r2sG : List Nat := [35, 25, 26, 42, 27, 43, 25, 49, 26, 27, 51, 25, 26, 35, 49, 35, 42, 42, 43, 57, 49, 51, 58, 57, 58]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := [61655096695321, 55023147096362, 61620585961754, 45161767967025, 55152616282403]
def xsM : List Nat := roots_x2_0.map (· &&& dom_x2_0)
def goalM : Nat := goal_all &&& dom_x2_0
def NN : Nat → Nat
  | 5 => 6
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xe4fac21bcf7e460e9113e5436ecbae435bafac8c0f0260ba
  | 6, 0, 0 => 0xf0260ba
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xf0f0f0f00000f0f00000f0f000f000f000f000f030303030303030305050505050505050f0f0f0f000000000f0f00000f0f00000f000f000f000f000c0c0c0c0c0c0c0c0a0a0a0a0a0a0a0a
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x421085432155431075321095432065432105
  | 6, 0, 0 => 0x432105
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 24
  | 6 => 24
  | _ => 0
def stateM : Nat → Nat
  | 5 => 0xffffff
  | 6 => 0xffffff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0x1fff00000000000fe03f000000000071e7c100000000019e78c20000000001f3990c0000000001ffe0000000000001f01fc000000000018e183e000000000061873d00000000000c66f3
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x1b56000000000007a029000000000030e48100000000009848c2000000000143110c0000000001ffe4a90000000001f85fd60000000001cf1b7e000000000167b73d0000000000bceef3
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 10 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 10 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 10 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 10 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 10 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => [] | n + 1, ids => wireDAt (ids &&& 0xf) :: stateWiresD n (ids >>> 4)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => [] | n + 1, ids => wireSAt (ids &&& 0xf) :: stateWiresS n (ids >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) : stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with | zero => rfl | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) : SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := stateWiresD_eq _ _
def htAt (s i : Nat) : Nat := (HT s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def idxH (s h : Nat) : Nat := bsr (htAt s) h 4 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 2 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x2_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x2_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x2_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x2_0 goalM u ys) : RunD dom_x2_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x2_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 6 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool := scr dom_x2_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_x2_0 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x2_0 roots_x2_0 goal_all 7 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x2_0 goal_all := by
    have h0 : isConstB dom_x2_0 goal_all = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub; have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq; rw [hcov] at hbad; contradiction
end S_x2_0
theorem low_x2_0 : Lower dom_x2_0 roots_x2_0 goal_all 7 := S_x2_0.noCircuit

theorem low_x3_0_x4_0 : Lower dom_x3_0_x4_0 roots_x3_0_x4_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff00000000, 3, 35)] (by decide +kernel) (by decide +kernel) low_x3_0_x4_0_x5_1

theorem low_x3_0 : Lower dom_x3_0 roots_x3_0 goal_all 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff000000ff0000, 33, 49)] (by decide +kernel) (by decide +kernel) low_x3_0_x4_0

theorem low_x4_0 : Lower dom_x4_0 roots_x4_0 goal_all 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff000000ff00, 34, 42)] (by decide +kernel) (by decide +kernel) low_x3_0_x4_0

namespace S_63
def pairsG : List (Nat × Nat) := [(1, 5), (2, 6), (3, 7), (3, 35), (4, 5), (4, 6), (9, 13), (9, 25), (10, 14), (10, 26), (10, 42), (11, 15), (11, 27), (11, 43), (12, 13), (12, 14), (17, 21), (17, 25), (17, 49), (18, 22), (18, 26), (19, 23), (19, 27), (19, 51), (20, 21), (20, 22), (24, 25), (24, 26), (28, 29), (28, 30), (28, 60), (33, 35), (33, 37), (33, 49), (34, 35), (34, 38), (34, 42), (36, 37), (36, 38), (40, 42), (41, 43), (41, 45), (41, 57), (44, 45), (44, 46), (44, 60), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [1, 2, 3, 3, 4, 4, 9, 9, 10, 10, 10, 11, 11, 11, 12, 12, 17, 17, 17, 18, 18, 19, 19, 19, 20, 20, 24, 24, 28, 28, 28, 33, 33, 33, 34, 34, 34, 36, 36, 40, 41, 41, 41, 44, 44, 44, 48, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [5, 6, 7, 35, 5, 6, 13, 25, 14, 26, 42, 15, 27, 43, 13, 14, 21, 25, 49, 22, 26, 23, 27, 51, 21, 22, 25, 26, 29, 30, 60, 35, 37, 49, 35, 38, 42, 37, 38, 42, 43, 45, 57, 45, 46, 60, 49, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0xffffffffffffff
def pool6G : List Nat := [57257050179077, 45161767967025, 61620369491498, 45201179285765, 30868806305306, 48426446423302, 61693231301948, 30868806316313, 55096783936006, 30834312358426, 55152146520355, 61796309861692, 61654729229617, 61788275869226, 45200977954073, 57295185713468, 61762319222076, 57256682718513, 48426229958186, 48498958014780, 61693097084220, 48461059463429, 57257152485894, 30834260384026, 30868806305049, 55023147096362, 30834312349210, 45201076979205, 55023299729699, 45127695079971, 48426699725318, 55152617794083]
def xsM : List Nat := roots_63.map (· &&& dom_63)
def goalM : Nat := goal_all &&& dom_63
def NN : Nat → Nat
  | 4 => 1
  | 5 => 6
  | 6 => 118
  | 7 => 597
  | 8 => 257
  | 9 => 26
  | 10 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x95802aeb
  | 5, 0, 0 => 0xcb3ecbed82475dd929dc436f25dac08712a909af08f1f700
  | 6, 0, 0 => 0x82efd65981e111c08185a02e7c2cfebf7be1e93c7b3832d678c7d28f77837e8674f8694c74297a2b6e49534f694fe0066880eff467d660b0666677fc665c9dfe62405679621ab0cb5f9ae4715f3c4d2a5f26e13f5c7ef4b15b9961895738c8965724beb6551cf90e540db023538795055305fb8e481e863947741cc445ef58054586fa03451a7cea43ef151f406493373eb098023e4248733d6089e83a340d2137d1bf1f35fda06a3325547632fc7e7c32d72e892bedc5d128ae58f32689afed25f28c30244bec26241394c32374b284201efaa41fde28751d8af27a1ac8344b19fd5c29177e0b3e153dc90f128d7e0f11f6914210fb6b470efd143c0139f406
  | 6, 0, 1 => 0xffffad9bf828deddf5b929eef524d58ef2f99d3af1ecc207f13521d2eeedead5ee21ca8aed2150faeaff66b7e8a02a3de426eff2e3e7068add0ee232dccf0a37d9f314f8d8d8118dd54f3e20d40cb338d232cbf3c5ce23eac2ab5a26c24088c9c0454128bf3470aabe797823ba04a7adb8a251f7b805fedbb5f3aab8b3737adeb20c714eae62d9dcacd3d368aafdb8a3a7fed1d9a7988c73a76b4f4d9f3f73b09d4e0f849d13f6189bc2629399ffbf5f994c8c9c96b0156196053d6d955575c59474301b93874b008e0d070e8a65e23c897c50e5833bb76a
  | 7, 0, 0 => 0x1adb9ef91ad3b1b61a0397ba19b45c241929eff618917f94185e09bd184e84e31769b9701747ce401736d9ea1702826616ab874c16a7a1ad1673e57615dc7c8415bf0bfb1585bdc9149a4ea11357233a13495b61128628ed1227f09d1182c6e910b47c75108dfb0010873aff107eac711073336b103915950f4449ac0f342ea80ed4b88e0daeef0b0c3025590c2225300b45d6cd0adb1bc30acc9fe20a91fbbe0a3a77c00a364335097f4255093090f10889983b0835910107942f9006d1977a06d133fa0674bcee062c153d05ab6a770429783903f5a318036355ec035871b402c4fbd302a7bb830188bf7200a8eff100a57767009978f50075184c003aa60a
  | 7, 0, 1 => 0x3532e67c34ea9d8534d0c5503403b3df33ae28583326906d331102a8326f284231eb022d304e4479302f8f992fc216982f76da822f2f3f132e79a6882e2cb24b2e1f778a2ddbe4da2d81375d2d7eac952c1be7cb2c05dd8b2c002f4b2b77caf02b0c54332ad101ba29c9f845296883742920d6ee28f983f8285b2ead2807443f27b0b5e326f3c2d426099ed525b758692543e48c2484e125246a0b8a23efb9852331768c2308cf9f2284b33321ea34962185dc37217de21421701c682164fee02112506520e3556c2016bee32011cf641fcef5c61fbbaa661f3e23d61ed593121ed2190f1ecaaa601d8e1e2d1c9476741c6686f61beeb5211b5aa7ce1ae55435
  | 7, 0, 2 => 0x520551e45200f47051db4f1a510e4d9950b5442c5040d64c4ffb3acc4f8a3cb44f5a6fd74ef588884e1ca4aa4e10be834deb64974d6207e44bd65d2f4b07216949a68b8148c9430848c10a35483a13a947ef23c547848d8c47623978462698db45bd00e645af514245a49808454119044512459e4477af8f43d3fa3d42f9159c42a5c7fd423b0fde41c3487d40e06b1a405380cd3f5076ed3e294fff3df9cadc3d5edcee3d3c97f43cf4fcd73cc117773c4b2c0a3bd23dc43bc2caa43a5ac9523a5868a13a1fbb53393fefff38f267cf3899b8e1382d8f7737e355da375cfd243705812c3622fc1e35e94e9c35907712358231293579dda7353f367835389f97
  | 7, 0, 3 => 0x69bc6b266991695b6985d5026977216c69627b62689eda7667fcab5667ee2c5966f87fdc66c18c7966484c30664278a8661f5eb765c95a1364a6aa8e6452eb0d62bc2e5c62adb27b623567bb61c7627361c37cf2616bcee460c081b760b6159e60acc2c7600403e25fdec53c5f83829a5ed0c0195e7132cc5df32cf65d97f1e35cd1412f5c4850ef5bf745775b850fbb5b791fcb5b6d297d5b60eb4b5b04eb6c5af228825aef23a75aca5d735ab8a9c85a757c2359a1e0795979ab67597460c85916f36a58c2ef5958c2518c5874c9ef57378c3857106ce856fb2fd856f73cc156cd3b8555eaa365559b0952555672e1544daeb9535d66b75271f78f52083abf
  | 7, 0, 4 => 0x86bb989c8647c9818618a37a8574e5528515b8cd84b77d6d84ac2d0783114e2f82771924824ebd7681db201581704eb880fd971480ceed00806943d17f6c93bd7f1dbf9e7ec9c7b37eb814087e5eb0787cbd2ffa7c34289a7c2fad4a7b28e4477a9eb29b79e6d0c7789be7d6785ddb1277f9409377c666a777a34c83762971fb7520f49f74e4177e7455c33e73e7ee5673d1733373b7125c7371dd9672a340cd7280092671a437ce70e8ab9670d14bca6fd5c76f6fc727d96f48dd226eac48236e9fdaee6e25ed676e0d8dc26dd70a656cd332bc6ca5bfe46c6767be6c5fcf1e6c2cc8e16ba2e3c56b9ca6a46a6c21046a5e2e496a38ec4f69cae70769c19091
  | 7, 0, 5 => 0xa03392daa02300249f67cab99f56ae149f0c24059e8fb9389e7a94da9e58602e9e4ff7719ddf60659d9501b29d12b9ba9c69df519c5909559c0945a09c029e899b6f9ad19b5bb1f19a8d7d6a9a2a447c99205edf991a12f198c6cc9598a2066197fd83ad97e36841977147d6967c8c2e964c72dd9631868095ff77d895c3b1989583352e947f040f937ec4bf934ff48a92fb6e8991b18ab19132cadd9061903f8facd3798f5565b78eb6e2ca8eaf7f208e9c58c18e68f6f78d7ea7078d7869e68c8d4e388c86d0e28c7b7f7b8c39f18b8bd99a928bc6b8af8bbc70aa8a7a9db889ae061d8952d7948946360787a82a1f87888bea877e346f8759260287428a31
  | 7, 0, 6 => 0xb85802fcb8572b6cb7fafb32b760e134b758a4ccb6f40975b5ff4747b5e54624b5e1844eb5ca4c10b574c2ceb533f09fb4bbb986b420beb5b2f89d8db28f99edb274a0a9b1ea3e9eb1def199b18896bbb177d426b14872c1b0c4a235b0598918af6a54ceaf552038af470c66aee9412baee1256bae7a07f8acbf819aab65e7feab5fb83faa939139aa82d705aa2f2ca6a9faaec3a9744f92a96f6c7fa9622045a8583e27a76b4f4da70d7892a70c7473a6d0c780a697208ba67b0d35a6768364a6513371a49090eca4232d48a41650f4a406231da39c9fa5a3731f65a2066a62a18fd52ca177ed5aa138fd27a0ca5129a0a58af5a093d74aa0855b69a03a73ba
  | 7, 0, 7 => 0xd74112a8d6951e9fd5ba5b61d547dd01d470aa0dd430d163d34f9306d30cb086d2b65212d2a6e32cd1c7e360d1bac628d1aafba8d1816841d16ca0bed1566dadd130e37ad0ff6571d008a737d00843b7cf2e0516cf0b2d9ece8dcdf0cd8357a1cd20b155cc5e9a47cc5b0663cbd1d700cb5012d4caac0d7dc946bfc4c91fa0d1c8f98b0cc85246a6c72a8082c677c7a3c66f499fc65854a2c61fa59ec5b84604c58eebc9c46975e9c45b15b3c44c184fc38bd864c2742114c1438dfbc005c2cebff60ab6be652655be390894be29aebcbdbed188bd197d31bd1857eabbfcd59abba3605bbb806acdbb7be6e9bb067030bae981f9b9a1b450b9695cedb8873eb6
  | 7, 0, 8 => 0xf3031826f2810ca6f261a728f25261f5f1e406f9f16d981ff1411580f05e0487efa703a7ef3f8a25ef201bafeecf7391ee60f2f9ee28865dedf00c4cecf958ccec7a86e0ec41d777ec000843ebe30bfdea72c138e9e08265e9a376e3e9942c9ce9840b59e96a477ce93d90ece9060583e85bc3b8e85a7ff3e7f3217ae673c6dde645392be54e6e14e542f83be53126b1e4de2dade47fbc49e4052d0ee3b83e5ce38d55f2e32c873fe27552aee1f74cd8e05ce993df4022ffded551a2de8ede08dcc9e4eedcbab869dbaaaeb5db6fd9b3db482cc5d9e0ee8ed9c9b650d9bc7fd4d9ae803cd959f241d8d69c0bd8c3bfbfd801ed6ad7fb9027d7f9dca0d7d25a00
  | 7, 0, 9 => 0xffaa18f5ff945926fe6faf54fcc3aa8ffcaa14ddfc30d494fc24ab7bfc1ea315fbec75b6fbc60337fba57992f9611aa0f8806e93f7ef4ae1f760f6a9f6b5bc52f670f085f4081177f3eb797df396896af31b8797
  | 8, 0, 0 => 0x382614fb375c328c35db239335895b043578c84e34bd92e331b30d7c315f0dca30b17a1b2e7627092cc710002c33b3742ad2a9b428a5bcb427928aca2781934225029ba324f1d90e24ba3ed6249d63ef23bebf2121f40ce01f28e87e1da0f8bb1c7f660e1c1160c61c02e4e51ae554351a01f53117c0281517a485a0178028051742223f16ed244d14c25be7147be17a147387c8144456111439cce4141f8fdd140ddc3213b478a2126ac74e11c9fc59111d5c611106cdc7108cbea20f1c517e0ecd7e060db3a33c0d359d660d2c2e290b5d6d2909ab8b68093db68007f908f707f0d02407695452052b8f990402104d02fbbdeb0193adbd00f8abef00f26ece
  | 8, 0, 1 => 0x7e67abc27db0481d7a98c065795af538779b444e6f36b6b86f1f7e7a6c96dad26a9da52b6a0e5a806986998d685bd80f67108e52655e0be164ede01564d6e24c64bb1a686430b85d63d8096f620d6f8d61b0ce8d61279f2a60c081b76001d5a75e4f53365bcd8fcd59bf3e1358bcfd2356a65876555e780a538ed0be537f76e65310cae8526f455b51529dc450d632f74f4e6d214d2e4be94d2885244cd3f7294cae6cf64c50a0f34b550f714b0d465447e5621746cd9c50465f78f84541e84844aae86243cfd0224307780a42a809fe40fd5c8940f62fdf3fd89f2f3f521ef63eca17bc3d9f9c853ce83b323cc117773c79d3023bcc4b8e3a1aa6c2392a1219
  | 8, 0, 2 => 0xb93140c9b1447d4bb0b62913b0b06ff8b03b1c5fb0316723af0a244eacab5189ac584a90aba7945fab858806a99d0106a8fc3611a8f48ae1a8aceb64a77db8c7a7420870a64e8b36a5dd0329a57263d1a42a80b8a3bd12ada304b735a022680c9e86591b9ce2885c9c6b500d9c26fc249bed4a379bca85189b4c7f429b0132a19a80d3c49a7af97c97e4107297b7adba95feb81b94ffe11f94ea2150923c767591ffdd0791869cbe911bcb618ed4acb68dbf9f568c0b847c8b1d15ca8ac1d328895dd9a187abe57286c3604986bb277685b3ccb184fccbd184d0ab2d84013fe783b31a7d824f20f6824ebd7681a2fbbd8128f3f38124f5e7805efbd87fbb0c1d
  | 8, 0, 3 => 0xff123350fee73185fdf4a2a0fc4e4806fa359d84f9a8b337f8350b36f8037aa5f7a272fef61649e1f05ab396eeca28f2ee18b783ed03ec8beccf062fec663512eb6b0ca8eb406b8feb1c83beeaac3b0be9f6ba3be9a376e3e892c0b4e7311744e62388c3e4e004dee44b50b2e3412cc1e2760958e0b0bd65ddb2f137dd44ebefdb7c6105d7fdd228d6a4388cd6363344d5053b33d43a869fd3f99519d358ca24d24ac501d11892ced0ab1f49cedaf033ce63f497cdef810bcb78c448cb41d630cad7f953ca94fea2c98e47ffc58557c3c5164b1ec4cca2acc3827a75c3753fb4c2d474bfc18ac36bc026c9e4bfd6d0e9be769f18be2c3e52bb5f66ffb9daa94f
  | 8, 0, 4 => 0xffb3f673
  | 9, 0, 0 => 0xfe971ab2f92dd199f61649e1ee12c54deab44034d43a869fc708d5a6c68acfd0c02871deba47a138b749d50ab158ad0fb03b1c5fa42346308ff96af68f8b65ae77cbd18269904ec93ef2c9303e51fe3b3d084ce73ba45360242a74e01957081117a485a0167ebc1d
  | 10, 0, 0 => 0x69904ec9
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xf0f0f0f0f0f0f0f00ffff0000ffff00ccccccccccccccccaaaaaaaaaaaaaaaaffff0000ffff0000ff00ff00ff00ff00ffffcccc00000000ffaaffaaffaaffaaffffccccffffccccffaaffaa00000000ffffffff00000000ffaacc88ffaacc88ffaacc8800000000ff000000ff000000f0f0f0f0f0f0f0f0eeeeeeeeeeeeeeee
  | 1 => 0xeeee0000eeee0000ee00ee00ee00ee001111111111111111fcfcfcfcfcfcfcfcfca8fca8fca8fca8fafafafafafafafafafac8c8fafac8c8fffff0f0fffff0f0f0f00000f0f0000000ff33ff00ff33ffff00cc00ff00cc0000000000ffffffff5555555555555555333333333333333300ff00ff00ff00ff0000ffff0000ffff
  | 2 => 0x55ffff0055ffffffaa0000ffaa0000fefecccc00000000ffeeeeee00000000fefeeeee00000000feeefeee00000000fcfcfcfcccccccccfafafafaaaaaaaaaeeeeeeee00000000fefefefef0f0f0f0f0f0f0f000000000e0e0e0e0e0e0e0e001010101fffffffffefefefe00000000fefe0000fefe0000fe00fe00fe00fe00
  | 3 => 0xff00cc0000000000ff00ff0000000000fff00000fff0000000003333ffffffff0f0f00000f0f0000feaafeaa00000000fff0fff0fff0fff0f000f000f000f000ffeecccc00000000ffff000000000000ffaa00000000000000ffffff00fffffffff0f0f0fff0f0f0ff00f000ff00f00000550055ffffffff0f000f000f000f00
  | 4 => 0xff00fffffffffffff0fff0f0f0f0f0ffccffccccccccccff00000000000000ffccccccffccccccfcfcccccfcfcccccfcccfcccfcccfccc0f0f0f0f00000000fcfcfcfc00000000fcfc0000fcfc0000fc00fc00fc00fc000303030303030303ffffff0000000000ffffff00ffffff000f0f0f000f0f0f00ffaaeeaa00000000
  | 5 => 0xfefefefeeeeeeeeefefeeeeefefeeeeefafaaaaafafaaaaafeeefeeefeeefeeefaaafaaafaaafaaa0e0e0e0e0e0e0e0e11111111fffffffffefef0f0fefef0f0fef0fef0fef0fef00101010101010101fefefefefefefefe1111111100000000f1f1f1f1f1f1f1f1fafafafa000000000505050505050505f0f0fffff0f0ffff
  | 6 => 0xfffaf0f0fffaf0f0ffeeccccffeeccccffaaf0a0ffaaf0a00f0a0f0a0f0a0f0afffafafafffafafa05050505fffffffffefefefeccccccccfefeccccfefeccccfffffafafffffafafeccfeccfeccfecc0505050500000000cdcdcdcdcdcdcdcdfafa0000fafa0000fa00fa00fa00fa00ffeeeeeeffeeeeeeffaaaaaaffaaaaaa
  | 7 => 0xfefefefeaaaaaaaafefeaaaafefeaaaafeaafeaafeaafeaafffcfffcfffcfffc0303030300000000abababababababab0000fffffffffffffffff0f0f0f0f0f0ffffaaaaaaaaaaaaf0fff0fff0fff0fffff0faf0fff0faf0ffffaaaa00000000ff00aa00ff00aa000f0f0a0a0f0f0a0affffaaaaffffaaaaf0a0f0a000000000
  | 8 => 0xf000f00000000000f0000000f000000cfcccfcccfcccfccafaaafaaafaaafaaf0f0c0c000000000fff0fcf0fff0fcf0ffaaeeaaffaaeeaafff0ccc0fff0ccc00f0f0c0c0f0f0c0cfffcf0f0fffcf0f0ffccffcc00000000ffcc0000ffcc00000f0c0f0c0f0c0f0cffccffccffccffccfffcfcfcfffcfcfc03030303ffffffff
  | 9 => 0xfaaafaaa000000000555055505550555fffcccccfffcccccfffff0f000000000fff0fff000000000ffffccccccccccccff00ffffff00ffffaaaaffffaaaaffffffaaffaaaaaaaaaaffff00ffffff00ffccffccffccffccffcfcfcfcfccccccccafafafafaaaaaaaa0f0f000000000000cfcfcccccfcfccccafafaaaaafafaaaa
  | 10 => 0xfff0f0f000000000000f0f0f000f0f0fffcccccc000000000033333300333333ffaaaaaa000000000055555500555555fff0f0f0ff00000003030303333333330505050555555555fcfccccc000000000303333303033333fafaaaaa000000000505555505055555ffaafaaaffaafaaafcccfccc000000000333033303330333
  | 11 => 0xfff0f0f0f0f0f0f0ffccccccccccccccffaaaaaaaaaaaaaa
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x30201004
  | 5, 0, 0 => 0x302010d0c5050402010050908020100507060201005050d0c0f0e50b030a01005
  | 6, 0, 0 => 0xb2c0a010d0c60539380c12106093f02010d0c6090b0a0d130f60b030a010d0c60b0a3a010d0c6050a13120f1060b0602010c126050a21240d0c6360602010d0c60602010d0c1060b0c120f11146090b01000c1160d0c0f11101460a2221010d0c6050b0a1b010060b0601001e0d6050b150d130f60b0a0d0c0f3c60a22010d0c106050a210d0c0f642020d0c0f146090a02010d13609330a010d0c60b370a010d0c60b060d0c0f30605420d0c0f3460b02010d0c3160b0a2901270c6090b0a000c0f6010c1211101460a02010d0c3c6
  | 6, 0, 1 => 0xb0a2b010d0c6050b081e0d0f6372e0a010d0c6050d130f111060b0a2d010d0c60b0a13120f1460518170d13116050a010c122f60b0615010d0c60a0d130f101460b4015010d0c60b22010d0c116092e0a010d0c605070802010060a010d0c311060b06010d0c346090b010d131160b060201000d6090802010d0c605011312111060b0a22240d0c60b060a010d1d6070602010d0c60a011312101460b06020d0c0f6050b0d0c0f1660b0a010d0c2360b060a1c010060543020d0c0f6090b39380d0c60b0a220d0c0f60b010d0c113c6
  | 6, 0, 2 => 0x90a010d0c346093d0a010d0c62e0a0d0c0f146050b010d131660b3306010d0c60b0d130f11146050b0a1901006050402010d0c6060a01000d106090a020d0c0f60b060a0c120f6050b20240d0c60b06010d0c306060a0d0c0f1060005010d0c0e518060a170d0c6050d0c0f111060b2220010d0c6090b080a010060b01131211146093902010d0c6090a01001f0c6070b060a01006050b200d0c0f6010d131110146090a010d0c3b6050a0d0c0f2f6090b0a010c1d6060a010c121060b0a0d0c0f316052e0a0c120f6050b13120f116
  | 6, 0, 3 => 0x90a0d0c0f3b6090b0d0c0f116050b040a01006050c120f111060b400a010d0c605070a1f0c0f6090b0a1a01006052e0d0c0f306090a0201000c60a0c120f10146093e02010d0c60b0a2a010d0c60b0a26250d0c605150d0c0f3b60b0a2801270d6180602010d0c60b060a000d0f60b0632010d0c60902010d0c1160b150d0c0f146063502010d0c605020d0c0f416
  | 7, 0, 0 => 0x50b020d0c0f11700050b0d0c0f111070005390a010c1210700050b0a0d8c0c0f700070a02010d0c14700050b151a010d0c700050b0a150d0c0f7050b3e0201000d0c800050b0a46010d137000b1c010d0c1114700000a010d131014600050b0a1c000c0f700050b820d0c0f307000a010d0c0f1014700050b3e02010c12700080a010d0c10147000b0a020d0c0f14700050b0a3e0d130f700050a2101000d0c7000b0a0d0c0f1014700054202010d0c0f700050b0a010d0c87700050b0a018d0d0c7000b36850a010d0c7000b0a221a010d0c7000b360a0d0c0f48700050b4d0a010d1370005770b0a0d0c0f70005070a010d0c34700050b0a010d0c56700050b3308010d0c70005073d0a010d0c7
  | 7, 0, 1 => 0x50a0d980c0f10700050b0832010d0c700050a01250d1310700050b0a620d0c0f700050b0a010d7a0c70000050b0113121160005360a0d0c0f3b700050b0a4c010c12700050b0a0d130f30700050b010c120f1170000050b08011e0d600050b850a0d0c0f700050a020d0c0f3b700050b0aa6010d0c700050b0a010d0cae700050b330a250d0c700050b0a010d1348700050a0d0c0f3b10700050a1c010d1310700710b0a0d0c0f14700050702010d0c11700050b0a76010c12700050b0a0d0c1d0f7000005010d131110600050b0a26010d0c700000b0a01131214600050b360d0c0f11700050b0a010d0c83700050b330a1c0d0c70005010d0c0f11107000b0a010c120f14700090b390a010d0c7
  | 7, 0, 2 => 0x5182e0a010d0c700090b0a1a010d0c700050b0a950d0c0f700050b0a010c1230700050b394b010d0c700050b3e020d0c0f700050b010d0c4411700050a1a010c121070005710a0d0c0f3b7000b0a1c01000c1470005770b010d0c11700050b0a4a010d13700050b47010d0c11700050b0a9f010d0c70005180b010d13117000b0a49010d0c14700050b0a01251312700050b0a1c00240c700050b0a50010d137000b060a01170d0c7000b0a01380d1314700000b0a010d0c31600050b860a010d0c700050b0a5f010d0c70000052e0a010c1260005180802010d0c700050b394c010d0c700050b0a0c120f3b7000b0a010d0c4414700050b080a000d0f70005710b0d0c0f1170000050a0d0c0f106
  | 7, 0, 3 => 0x710b010d0c1114700050b0a52010c12700050b6e0a010d0c700050b010d0c1d11700050b0a010d900c7000536330a010d0c700050a02010d1310700050b9d0a010d0c700050b0a0d0c0f8f70005330a010d0c10700050b390a0c120f700050b750a010d0c700050b0a760d0c0f70005070b0a1a0100700050b0a5c010d0c700050b0a1f0d0c0f700070b0a0d0c0f14700050a52010d0c107000b0a2201000d0c700000b0a0d130f1460005070a0201000c70000050b20010d0c6000b0a010d0c1d14700050b040a010d0c700050b1c01000c117000b080a0d0c0f1470000050a010d0c2f600050b49010d0c1170005390a0d0c0f1070005073e02010d0c700050b9702010d0c700050b0a010d0ca77
  | 7, 0, 4 => 0x50b0a0d0c0f72700050b0a4901000c700050b3945010d0c700050a1a0d0c0f1070000060a010d0c10600050b0a01910d0c700050b0a0d0c0f9270005070a0d0c0f3b700050b0a66010d0c700050b0a01000c44700050b4b0a0d0c0f7000005010d0c1110600050b0a0d0c0f8e700050b360a01131270000052e0a0d0c0f6050b330a01000d0c800050b0a4701000c700050b0a02011312700050b0a0d0c0f41700050b0a010d133b700050b0a1c0d130f700050b0d0c0f4811700050bb10a010d0c700050b330a010c12700059b0a010d0c1070005070b0d0c0f1170005360a02010d13700050b0a22010d0c70000050b0d130f11600050b020d0c0f30700050b0a4c0d0c0f700000b39380d0c146
  | 7, 0, 5 => 0x5180a63010d0c700050b201a010d0c700050b0a520d0c0f70005780a02010d0c700050b0a5b010c12700180b060a010d0c700070b010d0c111470000050b150d0c0f600000b010d13111460005070b0a000c0f700050b4e0a010d137000b010d0c0f111470005740b0a0d0c0f700050bad0a010d0c700050a1a01000d10700050b0a940d0c0f700050a5b010d0c1070000090a02010d0c600090b0a010d0c11700050b0a58010d0c700050b0a1a0c120f700059a0a02010d0c700000b060a010c12600050b0a1e0d0c0f700050a010c1211107000b0a3e010d0c487000b06350a010d0c700050b0602010d0c700050a211c010d0c700050b0a010d0c6a7000518600a010d0c700390a010d0c10147
  | 7, 0, 6 => 0x50b0a5201000d700050b0a1b010d0c700050bab0a010d0c70005070a02010d13700050b0a53010d0c700050a3e010c1210700050b0d0c0f3b11700050b9b0a0d0c0f70005183902010d0c700050a01380c1210700050a55010d0c107000a1a010d0c1014700050b1c010d1311700050b0a010d0c6c700050b080d0c0f30700050b0a450d0c0f700050b0a28010c12700050b360a0d130f7000507330a010d0c700050a010d130f10700050a29010d0c10700050b0a020d130f700050b3932010d0c70005780b0a010c127000b4b0a010d0c14700050b0a0d130f10700002e0a010d0c14600050b840a0d0c0f700050b330a0d0c0f7000b0a0d0c0f3b147000b0a1c010d1314700050a28010d0c107
  | 7, 0, 7 => 0x50b0a0c120f11700050b0a730d0c0f700090b0a018b0d0c700050b6f0a010d0c700000b15010d0c1460000050a0c120f10600050b0a010d0c5a700050b0801001e0d7000b390a0d0c0f14700050a50010d1310700050b0a010d1334700050baf0a010d0c700052e0a01250d0c700050bb00a010d0c700050b0a010c1251700000b060a0d0c0f600051a010d0c1110700050a0d0c0f11107000b0a01170c12147000b0a1a010c1214700050b8915010d0c7050b0a2601000d0c80000050b0d0c0f11600052e0a1c010d0c70005393e010d0c10700050a5521010d0c700050b01250d1311700050b0a0113120f700050b4b010d0c11700090b0a3e010d0c700090b0a01380d0c700050a010d0c51107
  | 7, 0, 8 => 0x50802010d0c10700050b0a15010d137000518360a0d0c0f70005780b0a0d0c0f7000b0a3e01270d0c700050b52010d0c11700054d0a010d0c1070005180a020d0c0f700050b7c45010d0c700050b0a49010d137000b0a02010d131470005070b01000c11700050b0a1a000d0f70005740b010d0c11700000b060a01000d600050b0a320d0c0f700050b0a0d0c0f877000b330a010d0c14700050b0a8d0d0c0f700050b0a68010d0c700059c0a02010d0c700050b0a010d13447000b0a221c010d0c700050bb20a010d0c700050b4e02010d0c70000090b0a0d0c0f600050a000d0c0f10700050b0a69010d0c700059a0b0a0d0c0f700050b01170c1211700050b1a010c1211700050b0a47010d137
  | 7, 0, 9 => 0x50b1a0d0c0f117050b0a2201000d0c80005070b39380d0c7000a01000d0c1014700050b2e0a010c12700050b0a010d0c80700050b393e0d0c0f700050b0aa4010d0c700000a010c121014600050b0a020d0c0f70005180a010d0c3470005183d0a010d0c700050b0a2801000d700050b8a0a010d0c700050b0a0d130f48700050b0a3e0c120f70005990a0d0c0f10700050b0a550d0c0f7000b0a1a0d0c0f1470005070b0a0d130f700050b2001000d0c70005970a010d0c10700050b0802010c12700050b0a0d0c0f83700050b36010d1311700050b1501250d0c700050b0a5b01000d700050a3e0d0c0f1070005360802010d0c700050b010d131110700050b4b0a01000c700050b33010d0c117
  | 7, 0, 10 => 0x50b080a1c0100700051802010d0c11700050a5d010d0c10700420b0a0d0c0f14700050a01250c1210700050b1a01000d11700050b0a010d0cac700050b0a0c120f30700059c0b0a0d0c0f700050b0a010d0ca8700050b0a010c12487000b060a01250d0c700050b3e02010d13700050b0a0d0c0f4f70000090b010d0c116000501000d0c1110700050b0a01000d51700050b810a010d0c700180a02010d0c14700059a0b010d0c11700050b333e010d0c700050b0a010d930c700050b0a1c010c1d7000005010c1211106000b0a1a01000d14700050a0d0c0f30107000b060a1c010d0c700050a010d0c4810700050b0a1a00240d7000b0a5b010d0c147000b0a5522010d0c7000005070a011f0c6
  | 7, 0, 11 => 0x50b970a0d0c0f700050b0a460d0c0f700000a0d0c0f1014600050b0a4c010d13700050b76010c1211700050b0a010c1279700050b080a010d1d700050b0a0d900c0f700050b010d130f11700050b82010d0c3070005070802010d0c700050b29010d0c11700050b0a7e010d0c700056e2e0a010d0c70005820a0d0c0f1070000180a170d0c146000b0a010d0c5114700000542020d0c0f600050b0a5d010c1270005600a010d0c10700050b08020d0c0f70005060a010d0c107000b0a01380c12147000b0a55010d0c147000b360a010d0c48700050b28010d0c11700050b4d0a0d0c0f700050b0a55240d0c7000b0a010d130f14700051836010d0c11700090b0a01250d0c70005780b010d0c117
  | 7, 0, 12 => 0xb0a0125270d0c700000542010d0c34600050a1c0d0c0f1070005183e02010d0c700050b0a910d0c0f7000b0a000d0c0f147000b36060a010d0c700050b0aa1010d0c700050b08010d0c3470000050d0c0f1110600050b0a7d010d0c700050b4b0a010d13700050b330a1a0d0c7000b060a010d0c1070005072e0a010d0c700000b0a0c120f1460000090b0a01000c600052e0a010d0c0f700050b6b0a010d0c700050b080201000d700000518170d0c11600050b0a0d130f3b700050b010d0c5111700050b2e0a0d0c0f70005090a02010d0c700050b0a010d8c0c700050b600a010c12700050b01380c1211700050b55010d0c117000b1a010d0c11147000b0a0d0c0f111470005070b010d13117
  | 7, 0, 13 => 0x50b15010d0c0f700050b3902010c12700050b0a010d0c7b700090b0a3f010d0c70005180b0d0c0f11700050b0815010d0c700050b0a500d0c0f700050b0a2901000c700820a010d0c1014700050a01270d0c1070000050a21010d0c600004202010d0c14600050b0a010d0ca570005363902010d0c7000b0802010d0c14700050b950d0c0f11700050b0a01171312700050b0a010c123b705360a0201000d0c800059c0b010d0c11700050b000d0c0f11700053902010d0c1070005423302010d0c7000b0a3e0d0c0f48700050b0a63010c12700180b0a0d0c0f14700050b0a01640d0c70005670a63010d0c70005360a02010c1270000050b0c120f11600050b0a010d1330700050a01170d13107
  | 7, 0, 14 => 0x50a020d0c0f10700000b010c1211146000b0a0d0c0f301470005430b0a0d0c0f700050b0a57010d0c700050b0a7f010d0c7000b360a01270d0c70005420201250d0c700050b880a010d0c70005090b0a0d0c0f7000a1c010d0c1014700050b0a0d0c0f6c700050b0a45010d13700050b0a5d01000d70000010d0c111014600054e0a010d0c10700050ba20a010d0c700050b330a010d13700050b3e0d0c0f11700050b600a0d0c0f700050b0a010d0c59700050b060a0d0c0f700050b0a010d0ca0700050b760d0c0f11700050b201c010d0c700050b0a0d0c0f79700050b6d0a010d0c700050b0a010d0c5470005180a4c010d0c70000050b15010d13600000b0a010d0c3c60005710a010d0c3b7
  | 7, 0, 15 => 0x5960b0d0c0f11700050b5520010d0c70000090b0a010d13600050b39020d0c0f700090b0a010d0c0f700050b0a0d980c0f70005070a010d0c3b700090b080a010d0c70000050a01131210600050b0a0d0c0f5a7000501250d0c1110700050b360a0c120f7000b0a4a010d0c1470005070b0a010c1d700050a010c120f107000b0a5d010d0c14700180b010d0c1114700056f2e0a010d0c70005080a010c1210700050b0a020c120f700050b0d0c0f3011700070b060a010d0c700050b0a010d0c9e700050b010d0c48117000b060a010d0c0f700051c010d0c1110700050b0a630d0c0f70005360a020d0c0f7000b01000d0c111470005360a0d0c0f10700050ba90a010d0c700050b600a01000d7
  | 7, 1, 0 => 0x5090b010d0c11700050b0a29010d13700000b0d0c0f1114600050a1c01000c10700050b3e0d0c0f30700050b39010d0c34700050b4e0a0d0c0f70005770b0a010c12700050a49010d0c10700050b9b02010d0c700050a3e010d1310700050a01380d1310700050b0a01940d0c700050b0a010c1234700050b3d0a010c12700050a010d0c4410700000b0a22010d0c60005180a02010d13700050a47010d0c10700050a211a010d0c70005070b080a01007000b820a0d0c0f14700050b0a270d0c0f70005073902010d0c700050b4a010d0c11700050b5d010d0c11700050b01250c1211700050b0a32010d137000b600a010d0c14700050b0a010d0c7270005070a01001f0c7000b060a01700d0c7
  | 7, 1, 1 => 0x5850a010d0c10700050b0a4a01000c700050b0a1a010d1d700050a0d0c0f4810700050b02010c121170005070a020d0c0f700050b01170d1311700050b1c0d0c0f1170000050a0d130f10600050b610a010d0c7000b3902010d0c14700050b08010d0c30700050b0a19010d0c700050a010d0c1d10700050b0a010d0c6570005080a0d0c0f10700000b0602010d0c6000005180a170d136000b360a47010d0c7000b0a3e52010d0c70000050b010d0c166000b0a02010c1214700050b330a010d0c7000518080a170d0c700050b0a3e011312700050b0a1c1a01007000b0a01170d1314700050b0a0138131270000054302010d0c6000b0a1c0d0c0f14700740b0a3e010d0c700050b890a010d0c7
  | 7, 1, 2 => 0x50b0a470d0c0f70005180b0a0d130f70000050b39380c12600050b0a62010c12700050a500d0c0f10700050b0a0d0c0f34700050b0a010d0caa700050b8a15010d0c700050b0a010d0ca3700050b3d0a0d0c0f700050b01270d0c11700050b0a0c120f48700050b0a010d134f70005080a01000d10700000539380d0c1060000050b0a13120f600050b0a0d930c0f700050b080a0c120f700050b0a5e010d0c700050b36010c1211700050b3915010d0c7
  | 8, 0, 0 => 0x50b0a0138000d0c800050b0a010d0c51700050b0a3e010c127000b0a01170d0c1470005990a010d0c10700050b0a01380c127050b0a01001f0d0c800050b0a55010d0c7000b0a1a010d0c1470005070b0a010d13705070b0a010d0c0f800050b0a010d130f7050b820a01170d0c805070b080a010d0c800050b0a29010d0c7050b080a010d0c0f80005420b0a0d0c0f700050a3e010d0c10700050a01380d0c107050b0a1a52010d0c800050b0a28010d0c7000518360a010d0c70005780b0a010d0c70005180a02010d0c705180b0a010d0c118050b390a1c010d0c800050b0a1a01000d700050b0a32010d0c700050b0a5b010d0c7050b600a02010d0c80000090b0a010d0c600050a01000d0c107
  | 8, 0, 1 => 0x50b7c0a1c010d0c800050b2e0a010d0c7000b0a010d0c1114700050b970a010d0c700050b0a46010d0c700000a010d0c1014600050b0a3e0d0c0f70005820a010d0c1070000054202010d0c600050b0802010d0c700050b4d0a010d0c7050b0a01001e0d0c80005180b0a0d0c0f700420b0a010d0c147050b36390a010d0c8050b0a1c010d0c44800059c0b0a010d0c700050b0a000d0c0f7050b390a010d0c108050b0a1c47010d0c800050b0a010d0c4f70000050b0a0c120f6050b0a1c1a010d0c805180b0a3e010d0c800050b01170d0c11700050b1a010d0c11700050b0a0d0c0f1170000050a0d0c0f10600050b393e010d0c7050b0a3e01000d0c800050b0a02010d0c7000005180a170d0c6
  | 8, 0, 2 => 0x50b01380d0c11700050b060a010d0c700050b76010d0c11700050b0a010d0c797050b0a0125000d0c805070b390a010d0c800050b0a4a010d0c700050b0a5d010d0c70005180b010d0c11700050b0a01250c12700050b0a50010d0c7000b0a01380d0c14700050b01950d0c11700050b01000d0c117050b0a01250d0c11800050a01250d0c10700180b0a010d0c1470000050b010c1211605670b0a1a010d0c800050b0a0d0c0f30700050b0a010d0c487050b0a1c010d0c11800050a1c010d0c107050b360a1a010d0c8000b0a01000d0c147050b0a021a010d0c8050b0a1a010d0c518000005010d0c11106050b0a1a010d0c10800000b0a010c12146050b0a551a010d0c805420b0a01250d0c8
  | 8, 0, 3 => 0x50b0a1c45010d0c8000b0a1c010d0c14700000b010d0c1114600050b4e0a010d0c705420b0a010d0c0f8000b820a010d0c14700050b0a01270d0c70005960b010d0c11700050b3902010d0c7050b360a01000d0c800050b0a010d980c7050b0a0201000d0c800050b360a010c12700050b0a02010c12705070b0a1a010d0c8050b0a5501000d0c800050b0a01170d13700050b0a010d0c3b700050b0a1c0d0c0f7050b080a01170d0c800050b0a63010d0c70005360a02010d0c70000050b0d0c0f1160005360a010d0c10700050a02010d0c1070005430b0a010d0c70005090b0a010d0c700000b0a0d0c0f146050b0a3e1c010d0c800050b820a0d0c0f700050b3e010d0c11700050b600a010d0c7
  | 8, 0, 4 => 0x50b0a3e010d0c0f8050b36820a010d0c800050b0a010d0c447050b330a02010d0c80005770b0a010d0c700050b0a47010d0c70005180b0a010d13705180b080a010d0c800050a50010d0c10700050b0a010d0c34700050b3d0a010d0c70005710b0a0d0c0f7050b0a01000d0c0f80000050b0a011312600050b01250d0c11700050b0a010c120f700050b080a010c127050b0a1a63010d0c80005070a02010d0c705070b0a010d0c11800050b1c010d0c1170000050a010d13106050b0a010d0c0f11800050b360a0d0c0f700050a010d0c0f1070005080a010d0c10700050b0a020d0c0f705710b0a3e010d0c800050b0a0d0c0f10705710b0a01380d0c8050b4b0a02010d0c8050b820a01250d0c8
  | 8, 0, 5 => 0x5710b0a01250d0c800050b080a01000d70000050b39380d0c60005710b010d0c1170000050a010d0c10600050a010d980c10700050b0a62010d0c7050b0a0201250d0c800050b850a010d0c700050b0a0d0c0f487050b0a01250d0c1080005070b0a0d0c0f70000050b0a0d130f6050b360a1c010d0c800710b0a010d0c14700050b0a010d0c1d7050b0a021c010d0c800050b080a0d0c0f700050b36010d0c117050b0a0100240d0c800050b02010d0c117050b0a551c010d0c800050b010d0c1110700050b0a15010d0c700050b0a1c01000c700050b0a49010d0c705070b0a3e010d0c8000b0a02010d0c14705070b0a01380d0c800050b0a3e010d13700050b0a01380d137000b0a010d0c10147
  | 8, 0, 6 => 0x50b0a011e0d0c700050b0a010d0c30700050a01170d0c10700050a1a010d0c107050b0a1a62010d0c80000050b0a0d0c0f605070b0a01250d0c800050b0a01250d13700050b4b0a010d0c70000052e0a010d0c6050b080a01250d0c800050b0a0d0c0f3b705180b390a010d0c800050b0a1c010d1370005070b010d0c117050b080a1c010d0c80000050b010d1311600050b0a4c010d0c700050b010d0c0f11700050b390a010c127050b0a1c46010d0c800050b0a76010d0c700050b0a011f0d0c700070b0a010d0c14700000b0a010d13146000b0a010d0c0f147000b080a010d0c147050b0a0100270d0c80005390a010d0c107050b820a010d0c0f800050b0a01950d0c700050b3e02010d0c7
  | 8, 0, 7 => 0x50b0a010c1211700050b0a73010d0c70000050a010c12106000b390a010d0c14700050b0a1a0d0c0f700000b060a010d0c6050b0a01000d0c1d800050a010d0c1110705710b0a010d0c0f80000050b010d0c11600050b9b0a010d0c700050b0a45010d0c700050b360a010d137050b0a3e1a010d0c8050b360a010d0c0f800050b0a02010d137050b36080a010d0c800050b0a010d13107050b0a02010d0c0f800050b840a010d0c7050b0a010d0c0f10800050b330a010d0c7050b080a010d0c10800050b0a52010d0c705180b0a1a010d0c80000050b15010d0c60005070b0a01000c70005740b0a010d0c700050b390a0d0c0f7050b0a0117000d0c800050b0a01170c12700050b0a1a010c127
  | 8, 0, 8 => 0x59a0b0a010d0c7
  | 9, 0, 0 => 0x50b0a01250d0c7050b0a1c010d0c700050b010d0c116000b0a010d0c146050b820a010d0c700050b0a0d0c0f6050b0a3e010d0c7050b0a01380d0c705180b0a010d0c7050b0a01000d0c700050b0a010c126050b0a010d0c11700050a010d0c10605420b0a010d0c7050b0a01170d0c7050b0a1a010d0c7050b390a010d0c700050b0a010d0c605070b0a010d0c700050b0a010d136050b0a010d0c0f7050b080a010d0c705710b0a010d0c7050b360a010d0c7050b0a02010d0c7050b0a010d0c107
  | 10, 0, 0 => 0x50b0a010d0c6
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 36
  | 5 => 44
  | 6 => 52
  | 7 => 68
  | 8 => 68
  | 9 => 60
  | 10 => 52
  | _ => 0
def stateM : Nat → Nat
  | 4 => 0xfffffffff
  | 5 => 0xfffffffffff
  | 6 => 0xfffffffffffff
  | 7 => 0xfffffffffffffffff
  | 8 => 0xfffffffffffffffff
  | 9 => 0xfffffffffffffff
  | 10 => 0xfffffffffffff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0xe3c79f8cff3fcf001fff8003ffffc00003801c00f83f0e0000070380e738cd00ffc0007fff000000e03f807c00ffc000ffc01c0000000000e03f83fce7ffcd00ffc01c7fff3f0e00e03f838000000000ffffff8000000000e000007ce73f0c00e000000000000000e000007c000000001c38607300c0300003871f80ff3fcf
  | 1 => 0x3800000ff00000000070000003fc000fc78e07f00c030001fb87c73f8ff3e0000380070e0ff0c001c3f63f3e7f8fd001c000073e7380c00fff8607fffc030001c000073000000001fffff83ffc0ff00e000007c003f00000000007fffffff00fff8fc7f18c73200fc7fe3ff07c0f1001fc07f83ff003f00003fff8000ffff
  | 2 => 0x1fffff8318ffff00e000007ce70000001f801c0000000000e3871f80000000001f871f800000000003bf1f80000000001fb87c00f83f0e001c3f6380e738cd0003871f80000000001fbf7ff300c030001c386000000000000000000000000000e040807fffffff001fbf7f80000000001f800073ff000000003f007000ffc0
  | 3 => 0xe000000000000000e03f800000000000fc00007f00000000003fe3ffffffff00e3c0000cff000000003f038000000000fc3fe07f00fff0000038007000c00000e3801c0000000000ffc0000000000000e0000000000000001fffff83ffffff00fc38607f00c03000e038007c00c000001fc07c7fffffff00e007800c003fc0
  | 4 => 0x1fc07fffffffff00fc3fe07300c03000e3bf9c00f83f0e00e000000000000000e3801c7cf83f0e001f801c73f83f0e0003b81c70f8ff0e00e3c79f80000000001fb87c00000000001f800073f80000000038007000ff0000e047838c0700c100ffff800000000000ffff807fffffc000e3c7800cff3fc000e0070380000000
  | 5 => 0x1fbf7f80ff3fcf001f871ff3ff3fcf001c0703f3e738cd0003bf1ff0ffffcf00003f03f0e7f8cd0003871f80ff3fcf00fc78e07fffffff001fb86073ffc030001c3f607300fff000e040800c000000001fbf7ff3ffffff00fc78e00000000000fc78e07f00c030001c3f638000000000e3c09c0c180702001c3ffff300ffff
  | 6 => 0xfc38607fe7c03000e3801c7cff3f0e00e038007ce7c00000e007838ce73fcd00fc3f63ffe7f8fd00e3c09c7fffffff001fbf7f80f83f0e001f801c73ff3f0e00ffff63fffff8fd0003bf1c70f8ffce00e3c09c0000000000e3c09c0cf83f0e001c000073e7000000003f007000f8c000e3871ffcff3fcf00e00703fce738cd
  | 7 => 0x1fbf7f80e738cd001f8703f3ff38cd00003f03f0e7ffcd00ffbffc7ff8fffe00e047838000000000e047838ce738cd00003fffffffffff00fff8607300c03000ffc70380e738cd001ff87ff3ffc03f00fc3f607f00f8f000ffc7038000000000e007007c0038c000e3c7038cff38cd00ffc703ffff38cd0000380000000000
  | 8 => 0xe007800000000000e000000c00000000e3879c0cf83fce00e007838ce73fcd001c00000000000000fc38607f00ff3000e00703fce73fcd00fc00007f003f0000e3c01c0cff3f0e00ffb8607ff8c03000e3bf9c0000000000e380007cf8000000e3879c0cf83fce00e3bf9c7cf8ffce00ffb87c7ff8ff3e00e04783ffffffff
  | 9 => 0x3f038000000000ffc0fc0f18073200ff801c7ff83f0e00fff8600000000000fc3fe00000000000ffc01c00f83f0e00e03ffffc00ffff00003fff80e7ffff00e03f8380e738cd00ffc07fffff003f001fc07f83ff3f3f00e3c79f80f83f0e00e3c79f80e738cd00e3c0000000000000e3c01c0cff3f0e00e3c7038cff38cd
  | 10 => 0xfc3860000000000003c79f80ff3fcf00e3801c00000000001c7fe38307c0f100e0070380000000001ff8fc0318c73200fc38607c00000000e04783ff07c0f100e3c09c7f18c732001f801c0000000000e07fe38c07c0f1001c07038000000000e3f8fc0c18c73200e03f03fce7f8cd0003b81c0000000000fc47e38f0700f1
  | 11 => 0xfc38607300c03000e3801c00f83f0e00e0070380e738cd
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x62c5968cd63688000ddb9203aded40004b91dcaaf8bf2e0024cf2795e778dd00ffe4027fff128000f23f907c52ffc000fff5dec084240800f6ffb7fdf7ffdd00fff5deffffbfae00f6ffb7c084240800ffffffc084240800f6f596fdf7bf8c00f6f596c084240800f224007c521280009d3a697329c977006fdfffbfffffff
  | 1 => 0x6fc4023fff128000621f903c52ffc0009020004000000000dfbbfdfbf9ff7f00d6bbb5f9f1ff5d00bdff6ff7eff9ff00bdf54ef7efb9ae00fffe6b7fffdbf7009d200073290000000dca6f83ad407f00f235907c52bf80000000003f7bdbf700db30d86a18872200b46e23550740d1000dc06f83ad003f00001bfd8000ed7f
  | 2 => 0x91bfd8208ed7f00f6e4027df7128000fff5dec084240800ffffffc084240800ffffffc084240800ffffffc084240800dfbbfdeaf8bf2e00bdff6fd5e778dd006fdfff8084240800fffffff3aded7f009d3a6940000000000d1a693329c977000000003f7bdbf700ffffffc084240800ffe4027fff128000f23f907c52ffc0
  | 3 => 0xf235904000240000f23f904000240000ff24007f7b128000000a213f7bdbf70062c4020cd6128000f6ffb7c084240800ff3ff97f7bfff700903a007000c94000fff5dec084240800ffe4024084000000f6e40240840000000ddbff83aded7f00ff3e697f7bdbf700f23e007c52dbc0000900483f7bdbf7006205900c523680
  | 4 => 0xdc06fbfffdbff00ff3ff97329ed7700fbbfdceaf8bf2e00f224004000000000fbb5dcfefabfae00dfb1dcfbf9bf2e00dbbbdcfaf8ff6e0062c5968084240800dfbbfdc080240800dfa0007bf9120000d23b907850ff40002044020406008000ffff924084240000ffff927fffffc00062c5920cd6368000f6ffb7c0842408
  | 5 => 0xffffffffffffff00ffffffffffffff00bdef27f7ef78dd00ffffffffffffff00b4ff27f5e7f9dd0062c5968cd63688009020007f7bdbf700fffe6b7fffdbf700ff3ff97f7bfff7000000000000000000ffffffffffffff0090200040000000009d3a697329c97700bdff6fc08420080042009008100600009d3bfdf329ed7f
  | 6 => 0xfffe6b7fffdbf700fff5deffffbfae00f6fe237df7dbd50062c5968cd6368800ffff6ffffffbff004200903f7bdff700ffffffeafcbf2e00fff5deffffbfae00ffff6ffffffbff00fbbfdcfefaffee0042009000000400004b91dcaaf8bf2e00bde40277ef108000b03f007442f9c000ffffffffffffff00f6ef27fdf77add
  | 7 => 0xffffffd5e77cdd00ffef27ffff7add00f6ffb7fdf7ffdd00ffbffdfffbffff00204402000400000024cf2795e778dd00001bfdbf7bffff00fffe6b73adc97700ffef27d5e778dd009dfa6ff3adc97f00ff3f697f7bfbf700ffef27c084200800f22f007c527ac00062c5068cd6328800ffef27ffff7add00943a2140000000
  | 8 => 0x62059000002400006204000c521280006b95dcaefabfae0066cfb79df77edd009d30484000000000ff3ff97f7bfff700f6ffb7fdf7ffdd00ff35d87f7bbfa60062c5968cd6368800ffbe697ffbdbf700fbbfdcc080240800fba4007efa1280006285948cd2368800fbbfdcfefaffee00ffbffdfffbffff002044023f7fdbf7
  | 9 => 0xb4ff27c0842008004b00d80a18062200ffb5dcfffbbfae00fffe6b4084000000ff3ff94000240000fff5deeafcbf2e00f23ffdfc52ffff0024dfff95e7fdff00f6ffb7d5e77cdd00ffe46fffff12bf004fd1ffabfdbf3f006bd5deaafcbf2e0066cfb795e77cdd0062c40200840000006bd5deaefebfae0066cf279df77add
  | 10 => 0xff3e69400000000000c1968084240800fbb5dcc080240800044a230105405100f6ef27c0842008000910d80208852200ff3e697c52128000204402150740d1004200902a18872200dfb1dcc080240800204e23040640d100bdef27c0842008004210d80810872200f6ff27fdf7fbdd00dbbbdcc08024080024442305070091
  | 11 => 0xff3e697329c97700fbb5dceaf8bf2e00f6ef27d5e778dd
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 179 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem wd_0 : ∀ i, 0 ≤ i → i < 128 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem wd_128 : ∀ i, 128 ≤ i → i < 179 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 51 128 = true)
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 179 → wireDOK i = true := (range_split wd_0 wd_128)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 179 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 179 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => [] | n + 1, ids => wireDAt (ids &&& 0xff) :: stateWiresD n (ids >>> 8)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => [] | n + 1, ids => wireSAt (ids &&& 0xff) :: stateWiresS n (ids >>> 8)
def SD (s j : Nat) : List (Nat × Nat × Nat) := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) : stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with | zero => rfl | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) : SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := stateWiresD_eq _ _
def htAt (s i : Nat) : Nat := (HT s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def idxH (s h : Nat) : Nat := bsr (htAt s) h 11 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 5 => 12
  | 6 => 447
  | 7 => 1944
  | 8 => 397
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xf9ac80e5f5b8581ac240f4f7aef9854995e1ac6e94eab1058f35e17984ad39b57cc0814b3bfb029d1688927f13c6ec39
  | 6, 0, 0 => 0x2137771720ed7a8a20e90f5020bb1aa21ff2102c1fe9baa51fd528dc1ed2190f1eaae7571e5d01b71e06cafd1d7550671cc1e90f1c6528f71c23e8ea1be341e41b5deaba1ae554351ae4d3311aace10f1a81704b19a4c687194947e118e35781182be3b617802805177c24c616d6d09316034669157554d51515303f14b3ba6d1461d13713f2ead712cf542212986a661182c6e910847a160e2146200db59adb0da501c20cf9cfce0c4514960bf7a5d30ab1918c09fa4f0908eff97f07788fc9075b3a910722e32e05fcea2e05c54fb8043c9520043b3177032e490f031672fa02ed76e0029240460200fdc201766d8100f8abef00c78cfd004c81e600142a83
  | 6, 0, 1 => 0x4459c9ea443e78e943cfd022439cf8a642c4d29242ad9c6542410deb417a81cf405380cd3ffd5c943fdec00b3ce2c1c13cda6c3a3cc117773cc096733bcc4b8e3bc2caa439fb5db839b2d81e39149a7f38c2cc77387b0742382c47793628b0ea35b2c10c358231293541799934bd92e334bd11df34b4ec9a34ab512833d88edc339a36b6332ee49d32adedcd32124cbd311d8ece30b17a1b305bb5122fd2dc832eee73662ed593102e9f17e82dd6a17c2d6cc1652cf723472ca7cc942c6ef2492c05dd8b2bad0b982a836b2f2a5eafb72a5cb8c42a2651ed29c4b9f829a845422945e4fd27e8e496256ecaf1237b1fe72373e1a2226b515e21f40ce021a84b1b
  | 6, 0, 2 => 0x6f8372c46ee241d66cde3a3c6cad05f76c76c0d66ba2e3c5698ca03869627b62689eda76677fee3066ad06a566427f576640782b653d59ad64f0602b6452eb0d61d91fd6616ac2cf610d536c60c081b75e177c725cb1fe155c5a99ed5c0439a35bf7671c5ab12b4559b6feb958f8451358bcfd2357ec096e571d3cdb56c687de562589e1559b095254ae798154703f9a532cafce53218092529e822851c1097a50f68d87508cbf0e507904ff4f8a3cb44f02fe524ecd1a174e838fd64e5e19f74dc98a5c4da7af824d4c66a74d2dbb9b4c862c7b4ba07d3a4b7caab04b6882954b4d3194497e0663496e353148d83c5c48c9430848893a7a4745001344b84c76
  | 6, 0, 3 => 0x933cb47192411eb091db2e5090ddb02b8ffd1cea8f85af878ebbea2f8e33b0768d7ea7078d59a8068d5071458c95ff338c810a2e8c0b847c8b8de4ab8b392fdd8a7a9db88a3672408a34f76c8a19a66b89f5a01189f3ce3889ea70d589926d628888c9e78755af5187191cef864aef5b8513ced184fccbd18498e7e782d62f53823172d882064d6581aa8f6b808661d7808545537f5540ab7ebf1def7dd32a5e7d93c1b37d7c07117ce6cbbe7cd063437cc317d07b12e2e37ab069477a98c06579c7ccb079bf63cc78b9448078a8ae86789cc4ca772d50a87720ead2771b4f4f747a456a7435e6e972b4c9f171cb389a701d6163701232276ff442ca6fefc945
  | 6, 0, 4 => 0xb574c2ceb53b688ab4458a1bb3995386b2f3534db24db15bb1ba629fb18b9460b14fdb85b0b62913b03b1c5fb018c14cb00d48f8af31d045aecbdfe5ae7a07f8ade9db15ac420587ac41a57eab581427a9f637a7a9bde044a8fc3611a8ef1b4da8cc5a0fa89428dda7ed6f8ea7c43dcca74f3e58a6f1e3d6a65948dca5c1ad00a409ce849f67cab99f58f1359ed629319dd91c739dbb983a9d97fcbf9d8a0a049d70b2ea9d43c2f59cc565699b5bb1f19a5b59039a02193299f4951699c114d89963c3e799085ded9891466397843901971fe3a896a5b6c89682c94996350a4a95ab19329599601b958d765f951e1a47945f29f093a4b7de9391693f934ca058
  | 6, 0, 5 => 0xd685b5cad6669851d522cb00d4d1b38dd43a869fd429749dd3e83490d3315ec6d2555ac5d169122dd1424602d11892ced0e9f9b0d0338f3bcf8817c4cf54d149ce1dc8c9cd2f9a87ccd97be5cc22a61bcbb7367dcb7a0fdfcad7f953ca58b31cc9c932d0c90a0ef3c89d7b8fc848c5bcc6e66a60c6bb6582c6a8d9dec60edeb8c4d6fbcac4229849c3b3b1e9c3573493c31e08c5c2d474bfc241fcadc231b1bac1438dfbc13c3652c021bcacbfb4dfb5bf65cd46be69af8dbe32f81abd026363bc90b0a3bc45cd9abb53afffba89a681b9a1b450b95c6a06b88d22c6b763de43b74c0a98b71c01a3b64ff35db649ae3eb5f91ac5b5da9890b5cb4dddb5ba88ab
  | 6, 0, 6 => 0xffb0d7b7ffa4edfbfe8ba7b7fdf9659afdf4a2a0fd90beb6fd380cd7fc813e75fbced83af9a8b337f9963cc4f84d177af6e568f1f61649e1f5dea28df47d59d8f393c881f3878204f28b7112f1bfa95ef19cf3caf15296c4f0d8e625efa703a7eddb106decfc0107ecf3a28aec7a86e0ec4582deebf99862eb9cda82eb1b634eeb01a236ea202f11e9bc24cae986d3dae9498908e9153832e901d5cde707d935e542f83be4e004dee4db98e8e49fd283e39955eee291c940e221046ae1fd7feee0e258bee0b33483e0addab3dcc9e4eedc6779cfdbe06c38dbcd1d99db7868cbdb382d48dac7448fd9f9fb5ad9a47bd8d91e295ad77a5816d708d53c
  | 7, 0, 0 => 0x8028ac807c6446507a1618d07983db607540f08073f35800735b008073325e0071ebcc6070b6e2706dd0edc0694c235068d4b130682030e0672c3e80620bd3c05f6b71805eac08505b329cf05b2eac50583d1110567fa510564049705406a460533fba6050cdc2204ddb57304d064d1047e8d15043d9cd60408fbf903afd081038d424b035dc2d90342ee7a0337d67b0331cac602fbbdeb02e42d5302d33fd402d338cd028e484802463e470244bc38023e56a50229321f0213165e01e806dd01dfe0b301be086c01b60d15019f51af019520ef015f4010012d94cb012ae19901189fc600f8abef00f26ece00d64fc300252651001c45a1001528ba0010041b
  | 7, 0, 1 => 0xeeac9300ed51c0e0ed4fd100ecd7e060e86711a0e68f5ce0e61175a0e5684bd0e4468b30e41de8b0dfa82c30dd6cf3b0db6ae630db3a33c0d52fdb80d37803a0d359d660cfdf2310cd6fa8f0cd3e9650c76b2fc0c7515ce0c4456cc0c1de1fe0c1b94cd0c10da480c0ce0890c0c577e0bb355150bac83940b8bbf6b0b7a8be00b619aaf0b5d6d290b0d46330af1588d0accf95f0a9cd3050a7bfb9f0a75aa570a5db90d0a4b0a760a49c2db0a200d4a0a1c88f40a0eeb570a01adfb09ca1cde095537f9093db6800918ed40090b2c30090422d808f88e9108c04d1d08a584ed0895d5190883b66b087d4564086df8bb0869cb9a085b798b0828fed70812e9d2
  | 7, 0, 2 => 0x18927098182077a417ec8ed517d900ce17c2485d17bd685317bc20f017a485a01783d36c176707ad16c4ecbb167ebc1d1656f99b161b607615e3d4b915b8d2ee15930133156f272215554fd015522f7014e6f9fa14d1b9a314c1c479147387c81460b592145be6f1141f8fdd13fda56313f695b113b639f4138bc72e1383ce79138177d51345c7c51332ca01131fe96f131b184412d4145e12a5b21f1288b0461267856412598b66122391de11c9fc5911b4999e1194d57e1183b7ed1158bc8d113c00b6112ec5f5112b6c9010f31c5810d730f7109959ad10987933108cbea21056c74b101cf3100fcf05c80fb89c5c0f9f8c4e0f88b3880f86cbb10f52f7e7
  | 7, 0, 3 => 0x20bd10b420b6d82820b14afe204cfb9c202d9691202b40b220044b421ff874121fded0131fc1b3651fa9b9161fa3ca1c1ee037e11ec8cee61ec8714f1eb180c41e56cbc31e254cf11dd9276e1dbf2e791d64beba1d1a31a91d0c61251cfe81b51cbc6c011ca1fc5c1c7f660e1c54452b1c313daa1c1160c61c0377111c02e4e51bf4b44a1bb5a1481ba9074c1b9b06e31b96e8611b8f8cf31b8f4bc21b77905d1b3609e11b23c71b1af0de741ae457171a939d131a8dde0a1a812e9f1a76b50e1a6b10fc1a39cc121a28899f1a0fd8341a0a201f19ed6768198257a319763e0f197293191957081119324a89191c880718f7b2bb18f4e10a18ccc15018b26e22
  | 7, 0, 4 => 0x296764912935e746293392ce290c466228e13c0c28c3a7c3289b697328708577285eafc82841347c2841265828318577281e7a9427c003a927bf8f0327af0de9273c4f3c2730f4cd2726dd4726d06c1026c74c062613f6fd25c5d193255eaa5025271dcb25029ba324f1d90e24ecb71b24d5ba0324bff0952461748c244f7a0a2422aaa3241a19e723fa7d6423aa133923a558352380f5722379a87f2371f15e2363757d235dd3e7234fd88e2343ced9233bab09232fdfb72305e8be22ddf8e722a39c5a2299efc4223fc74c222383cc21f40ce021d6d25821d2836121cfe53d2195a69b21677a512161cccc2118d8ca210940e420fb4f1320dc7ec920da0450
  | 7, 0, 5 => 0x30dac11430d3ff15308ead5a306461c73062345c304cf6a43044b910303247ff302c87ea302a0ae32ff39f242faa7f832f60d99f2f56ff032f2d333f2f244e602ef94f442ef590472ee5f83b2ea15e5e2e7b65df2e7627092e65c3952dfd8d012dd5e4112dca65fb2d6782ad2d5d2c392d476d832d0b08af2cfda1512cd48a3e2cc710002cbfb75d2ca409f32c9d909e2c60eef42c35d6762c0d41422bc4046a2bb7e6892b9f72c22b5379482b4529312b411ce62b3e9fc02b351a482b3290202aff1c0f2af61e482ae6ef722ae3339f2ada82fe2abf74ef2a88612a2a71ab6e2a71985b2a5f79ad2a3e98622a20277c29e09a2c29c9cb4929c95011297400f8
  | 7, 0, 6 => 0x38f9f1d038c12eb9387cf5323872f2083865c14c385e3e023849e4bb38326dc137fd8b9f37f723b837e869b3376cca45376a4f69375c328c371be02136f914db36bba0ba36727dff3666efa43620a03035db239335d968a53597574d35895b043583222d3578c84e3576bc2135747c403535d36d3509393735017f8434c730bd34bd92e334aeaf24348ee9a33487b4ef346473883457b9423428a0bd341c5d503402387733b8069c33addc96338b1457337098c0337026a63344a17a32dfd22e32d4864e32c69f3432a1551e32998b1f32681bf431b30d7c318eb2df316e3c87315f0dca314f85573146060b311656bb3107d3ae30f9ec0330f28d1230dae181
  | 7, 0, 7 => 0x424b72b2423d3c4e4222f01b41be98b94197cdb1415ce1b94156fa74414e7062410ec54a41055e2c40fd5c8940ba3bb340a1669c408d53e240811af0407b21bb407914423fd89f2f3fd81e2b3fc6f07c3fb245d23f8b767a3f5b35893f12e7d53ef2c9303ec4f5c93eadf8b13e8c7c4f3e5d1fd33e4848ff3e2a98cc3e2424c43e098a5f3e0301fa3dccbcab3dca78633d9dd74c3d71fd593d36eb2a3d35d18c3d1f58a03d1bf2473d084ce73cfa499c3c83af333c7bdb083c771e663c6977bf3c5fea2a3c2cf4da3c1fe1e43bf8f7873bed95723bbb8b303b6671ed3b22fa393b1437703aa0418d3a99cd023a8927f03a6372fa3a58367539ad638a395f96ae
  | 7, 0, 8 => 0x4b3060ba4afc9a304aee95694ae58e0c4ae0b3c94abb17904aac3dc34a9c663a4a6005a64a4cbebc49f19482499b524548a30f48489e7dbe489cb018486b9cc54860daab485d290d47e748c447e5621747cd22e3475aa13c473a9da3473a6d924702e8f446f3f1d646da15bd46cd9c5046b17d4546a5a3af465232c3463a0f17460863bc45eb319d45e12de845de9edc45d63c9845d5b36a45b4cc80459ded53459a7aba458c1b084566e491456621344561370c4541e84844e3171544b0b53e446609b64430796e442d00d14421a80f441fad5c43ff470e43f8662a43e12dec43cfd02243c11da543a70ae5433fa33f42fc4e1d42e4851042b870d04266f78e
  | 7, 0, 9 => 0x52afc25752996d67528b5c3a528577355270ec6c526f455b52652dd5524b30b652368d0152267abf521c2316520b52db52084b2c51fb152a51d54e5151affe5e513f899f50f4e59f50cb4eac50c1bb7d50c1a5e050a37433509287a75062f21b505729215047ce894fb750c94f2308104f1775264ee29ddf4ee201a54edbdb8e4ed160d14ebdb7684eb232304eabf50f4e5aaf8b4e2ff7f04e2e2ce84df9f4364da171e74d9a7b164d7df7ce4d7b070d4d6d7cb44d2885244d1a63024d10dd8a4d0e53624cfa2ad14ce69ba94cdb51174cd3f7294cba213e4cae6cf64cacc4fc4c9ad3b34c74d9df4c35789e4c1de4d44bf1bf454bafb81c4b6fa6144b448057
  | 7, 0, 10 => 0x5ba41d8b5b96d7675b5840ee5b3983f85b212d615b1b4a615aed0b785a9cf1fb5a79a54a5a69bac65a5f46385a2cc3f459d8d2e559cb15b459c5ddbf59bf3e1359253d1f58d6963f58c7437a58bcfd235813abce58119e9858039e4a57db40a8578a7e975735f67a572f6f4b57213a145710d06856f51c3656ae68fc569e151f5679d043565a3d7756590b9556337c8455fdc57d55f820925593c9de5593c31055784b9c557784d6556da6c7555e780a554eef97553eb09b5539a68b550f9dbf55073dee54920a80548e179a5478803b54617bf9545424d35431b23f540efd8e53c3f8a453857156537f76e65359b3fb532862f0530dd69552f219fd52e515da
  | 7, 0, 11 => 0x6603f64965d5f467659ce0e7655e0be1655c4e5a649434126493563e6438425e63ff7f47639d7a81639a5bfb63965c2862fec6b962e1216e628be68f6245d4796241b5f761f7222a61d9161e61b0ce8d616dfee36151516d6142791d61279f2a610788a560feacb060dd91ac60dd8b7660d6c19560d35735609ba710608f0109605c2bfe602ebcf1601d50b96013f4555fe54eea5fae7b465faa2c4f5fa624535f9b06c75f66e6445f6459b65f16df6a5f13a1b05f0577095ef7b5895e88f3ec5e6d15f35e4e7aea5e4644e35e1f89135e053f7f5e02f9755dee6b6b5deb6f4c5d42352f5d37c7f85d017f515cf0c0825ceb5e295c90af7e5c8704475c7c04cf
  | 7, 0, 12 => 0x6e6656486e21547c6df9a8166df1abd96df0fec26da8abc16da035b16d72199c6cdf4af96cd020406c6b07056c5e9d666c453e1d6bc738476bb6c94b6bb38dc86bab9a0f6ba0ff156b6f4ef26b024b4d6afd64966aefe1a56ad9b6196ad97ffd6ac5e7666ac4e77d6ac0678d6a7bb2e16a0993c569de091c69b46fdc698f8f776986998d69658b746954d60169548d2469506ea2690b0d3968ff83c268e1164068ddca6368bee2ec68badc8d6821124f6802b2e767f8c41b67e20fe067c3a34567adb0e367796d5c676ca7536767de4a6742a7d3673d759c6722ad00670425a966e46e666684c085667cc29c6673126166704cbc6658320f6653a3d96608c413
  | 7, 0, 13 => 0x772ab2d976e3013076b68f5476883f0f7669dadc765f42f5760b27767590c5d1754e913974f44fdf74dd2a1a74a4fd867480d247747d87ae747215127440f1177419a07b74125043740286f473ff5c9c73e4978d73b11193739f2b3973722950735fe3877348088d7322a3cc72ba3b1172ab5f4f729b2e07727f3775727e079d7278be20722f623071fe46de71ebea7c71d3a02871afb552717d774a7162bd4571541dde7101265370d6c06670d1106770cd5ae470be61217098f8c1707653cd7050cc06704a65907032d0ab702759d96fec830e6fd9346f6f508a4a6f43ea976efc04706edf7c9c6e991aae6e83e6036e7696f56e74d7686e73d1506e6dbd79
  | 7, 0, 14 => 0x80446b3b8032d812803070bd80231ba07f6971e87f2cc9a57f29300d7f2619507f18940b7eee8de77eeda02d7e7ba7e07e62c7897e151cff7e04ecbd7dfebfe97dc7732a7d87996f7d6e9ad67d6b8e997d5b202e7d4a419d7d291a647d0c8cbb7cf70da37cb55eb97ca259337ca027e27c9f7e7c7c7f02d67c3f68397c3a52057c34d6c77c2e85b57bb3add87bac4d1a7b8055d47b7c8fb07b103aa87a98c0657a8096417a6bf5b27a5716df7a32e6c479fd2fbd79ef6f1079c53e607976ef16795af53878ebe05e78ba6f2e789e7b0c788c2ff5786dfc597862d6897860e639785978f078510b2077dfd53c77cbd18277b2125f7791cd22776cef3577496a09
  | 7, 0, 15 => 0x894e9e1a89469bc488ef6b0288dd4a2e88d4431e8869664f883cc48d8833f5518826a0348820d24187b698fb8778745f8738119c87299de48726336286c3604986b049208682ca86865fd91e86453eb986412037861a5c81860c2be685ee6e9c85db428985b3ccb185a4cbd185a3bc0f85839d3f85721f6a84fccbd184f3169584d2c17584c381458467a9d1845b963e84582d5584366cf7841cbaf984135e9584013fe783cbd3c083b647ca83b31a7d839db7c2838cae8a836650848363c3f6833dca22833c7e9483324e8f83079e27824f20f6823fe56f821c9d5a81c8c2f481a29664819b4b0881975c238128f3f380f16ac480b8c97c806c43f7805199b4
  | 7, 1, 0 => 0x90962ebf908ece02908d554b9033b5248ff96af68ff3586c8fdfe3ad8fccc2048f6eb9328f69047f8f4ddcde8f2f8aec8f295bc48f042eb78ed4acb68ed0cc8d8ec7b0ec8ec451bd8e46ca478e3d634f8e2e01ec8e26e5f78e032ec18dff31bb8dc02d048da850658d9ebf6c8d9225708d8425078d7aed198d145d498ce4dcad8cbb13f68cb5433f8c839dfd8c7cbb378c6c2dc88c491a168c3afb688c03c8b18bd6858c8bb9cc5e8bb2b8e58bb1328c8ba664528b9a7c8c8b90331e8b793b1c8b67488a8b55b5f88b3625d88b3227778b1d15ca8af2be0a8ae474e18addff2e8ac1d3288aac706d8aa94f158aa2abe88a38315c8a224c288a1656d2896dabdf
  | 7, 1, 1 => 0x995d02aa9944d26b9937be1a990ffb6b99016ebb98925296984429e79811ba83980f33cf979e957997941ecf9781008d976c8913974a5a399747c87497356364971c539996d01321967edfc89677bd2a965c958996305e1095feb81b95fe6b0e95e626af95c7433b959ee8589556de689556175c9553881e95522fc3954a07bc95225003950f352694ffe11f94e8795694dbd1b494b8dcd49492ddb294872291941fa722940b257293da0a2093a98caf938b73e293593a8c934f2dc493384e8a92f43bb59274a52892646ea3923924e7923619c092352ad9922628d291ecb7d991e1923691dab36f91d7069f911fadd9911dfd7890f2ef9690bda49790b665a8
  | 7, 1, 2 => 0xa0ba2447a09c7f18a06bbb55a05bb1f0a039bc45a022680ca01eb416a00525279fd89fc89fa3366c9f8844ec9f7bf9f09f6c35d39f31eb719f1dec7a9f06ad0e9eb1c3c19eab00239e846bb59e7b41be9e60f45a9e56811f9e42fc499e33d4ec9e08b2919e0665df9dfb72369df4f9a79deb9d439dd249f19d66305e9d3f16bb9d3e8f329d3a363b9d1c0c8f9d17c8749d14bd429ce83a339ce2885c9cd5fbe69c7f2c819c6d66999c6395789c44bee19c26fc249c14133a9bd8f2ff9bd4a9df9b65def89b53791e9b52b2589b0132a19af3a5179aeb76b19ae20b659abdc1009ab8455a9a759f419a67f3379a4707359a43ff8699f1845d998dc66d996dd3cc
  | 7, 1, 3 => 0xa8fc3611a8d0e661a894d850a888922ba86f31f2a8579795a84a90f6a84135a5a8255610a82101fba80fe5eca7db6d6fa7c8dcf2a79d2202a778c454a76199bca7352dc1a73369e3a7070867a6ea9da8a6ae84b7a697cd48a64e8b36a640a41ca6375980a5ef21d7a5dd0329a5dc1862a5da4240a596fabaa593fad9a54714f0a54213c6a53f8738a51841d6a4d35194a4b7b929a497a2f7a42ac53aa427599ba4234630a3f6f2dea3d38329a3cf9872a3b74bbea3ac4ce7a32c9765a317fe4ba304b735a28a69a4a26ac316a241a4fda23614c8a214873fa1c22db6a18ed7a9a1607947a15def42a14a8c27a13bd84ba10bf6fba104f34fa0f982e0a0e18795
  | 7, 1, 4 => 0xb1838f47b176d427b158ad0fb14a7c74b1498684b11cca9ab1074598b0e446edb0df3a84b0d183e5b0bf6537b0b06ff8b04a1743b044ba39b03e1077b03b1c5fb0316723afec201eafe9653dafdef203afd5efccafb5dacfaf98e252af7e5c2daf359018af2022c0af0a244eaedd696eaeb8f7e5aea402e0ae8e3c58ae619b76ae49084eae427b2dadcd7a96adb1d04aadb0dd5dada685f3ad13ee5aacf4fbe3acb391a9aca5b365ac77f2fbac584a90ac203c81ac139c47abd61055aba7945fab377bdcab1cd5c8ab04c9ddaaf7e2b6aab59f25aaaa4cddaa452991a9ce7a41a99d0106a9925c3da9907e58a9851227a9818b2da9536d8da944cd73a927f774
  | 7, 1, 5 => 0xb95bf854b954389eb9238bb6b90d0024b8db78a7b8db3bf4b8b97ddfb89bc33ab839de42b8110090b802dc33b7d97460b7d3b0e4b7c1e9f1b7bed18eb7a8f6efb7901f62b749d50ab737b8cab72f4b60b6fad8c9b6c4937ab6b0f2bcb6af85aab66db2f5b63e8ff7b6358400b6355c70b60754e6b5e0fc76b5c7e6b8b5c668b8b5b94823b5b77e2ab5b461f1b59cf503b5902909b57154edb52bb7ccb4abb72fb442d94eb436000bb426fbacb3ef1ffcb3c9c30bb3c24a54b37b151bb3686ebfb35a2bf3b34d471eb341a868b33dffa7b3156a73b3129c5ab2f35618b2b438ddb2a359d7b26a3914b2466a4cb23ccd8fb2069b61b19e29acb1918fb0b1908a5b
  | 7, 1, 6 => 0xc1cbd369c18fbe0fc18ac36bc1637e35c157bd32c124aa0ac11b76cfc10c93d2c0e7a473c0b58cbbc0aa5d7fc0a94172c0a7fd53c03f650bc0324461c02871debfdb0e57bfd73578bf8fc338bf851e63bf666733bf52f044becd8a39beab9042be937088be769f18be4929dbbde508e2bdbb02bebd8d30adbd5c6ceabd569d44bd481cb7bd16353ebcf80b4bbcf03cf9bce0ee17bcd904bbbc8f7c91bc885194bc7ca571bc4e049dbbf2c6b6bbecc5edbbe6e79bbbcd479fbbc7133abb6bf353bb5f66ffbb49c479bb151e4fbb07baebbae435a9ba506113ba427f45ba2fc850ba0bd188b9daa94fb9cec865b9c6ad7bb9b21282b99a9a36b985498cb97a58bb
  | 7, 1, 7 => 0xcad7f953cabe2c2bca9741c3ca94fea2ca546425ca30e3fcca17292dca04774eca011952c9f8ee7ac9f3d846c9e8e892c9c45eccc9ad816cc98e47ffc980ba33c978e544c93615f1c8e2cba9c88322c2c8821c3bc81b12f1c7e4a5b2c7db80e1c7b9162ac7b58e37c7abb727c758fffbc72fa268c71fc81ac708d5a6c6af14d6c69e7be3c69c512dc68acfd0c654fc98c5f87b2fc5dbc5b7c5d82793c5ca4838c5c197f6c5bbbdecc5a7e8ddc5a1bf72c57fd30dc53b428bc532c1fdc4bdf1fbc4b98e87c489c356c4828b8bc406c3f6c3f04a81c3d28b09c35a0575c33155b1c2c2898fc29ee904c22fd643c22b236ac2290d86c2157f87c1fd94bec1de7afe
  | 7, 1, 8 => 0xd2c00a2fd28da698d28c47b6d281ea23d2793d18d257e8b9d24ac501d248728ed23c8d64d23889ebd1cce4d6d1b1b30ed18f4277d175aa0ed11892ced111535ad10ff778d10ba971d0f46623d0eed897d0d31777d0b92cb0d0b78a0bd0b2fbe9d094765bd06fa9abd062548ecff42cabcfb93b24cf73c5f6cf65523ecef74cf6cee27a34ce9c234ace9bbdfbce846d20ce6a62a9ce07748ecdfbffc3cdc18071cdaa44eccd52d7cdcd4803e3cd43454dcd359d45ccf7e195cce560cacce31d9cccc52a17cca35e2bcc86101fcc7a28d9cc684041cc2a050dcbbcb7cecb7d8f0bcb7d4e04cb78c448cb76685acb69ce5ecb50d9e6cb349801caea07e8cadcbb49
  | 7, 1, 9 => 0xdae1e332dab6ff36da868036da7ab10fda61dd2cd98f9349d984ba31d95b6233d93d87e6d92ea3f0d8f77560d8ed43cdd8c624d8d89dfb22d88137bcd8513566d825c4b2d8114742d808765ed7bd6d5dd7bcbfb8d7899138d73f0427d734ab98d719f753d6f1bbdfd698d3ddd6827ea1d65b2656d6363344d5fede1cd5e6dcbdd5e404bfd5b41e40d5a576d8d57f7a4cd558a97bd5484081d5443201d5220327d5081364d4f0f799d4a3bcb0d49fd409d47ce68ad43a869fd41890d1d40806fed3ff0dd7d3f580b8d3d3e2c2d3cbe778d3c5c492d3b5450fd3a8e0f7d39eec29d379eceed36d52f2d35f5289d338bdb8d31e59f0d313bffed2d954e0d2d4b27b
  | 7, 1, 10 => 0xe3412cc1e3106e12e30df211e2f73a11e2b96760e2a3a791e29557f5e283c095e2785dd5e25821fce244b55ee20b1b97e1edd638e1e47322e1a3dc52e1560784e1410c7ae0f74a87e08a5211e07f22d5e0500651e04d6edde01f1c9be00dbdb6df99d6a4df68f3efdf382235df140ce9df138139df130c3cdeeb28eddeb1fadbde9849e3de91cd35de53bb01de4dbcd2de49688cde49630fde41b497de3eec65de3e9d1bddf8560cddea6151dd768b6add22f5f6dd193586dd09945fdd076004dc8e32f7dc7a461adc580c1cdc56f92cdc15be7adc0b8b92dc06615adbff3966dbf3b568dbb5b57bdba7faeddba270bddb94eee6db61cf48db3dab48daf3b57d
  | 7, 1, 11 => 0xebdaeb21ebd032e7ebaed3bfeba52384eb9304d6eb7e1f2aeb72283ceb5bbcf8eb406b8feb222eefeacca4d1eab44034eaac3b0beaa78c21ea9c0e9dea8b3a97ea8af7dbea8706dae9d791d3e9877a69e9435bdae935373ae8e13f4fe8cf8ba4e8bab8e2e881f5cbe8363210e80761dfe7deeac6e7a7b2fee78ddb80e78c552be73ba6c9e7311744e72b167be71705cde6ed781be6e489dbe65bb776e64c55b1e626c786e6194c97e5f2c308e5b7338ee5aa15aee59d96b3e5996144e54da510e52648e8e5159907e4e004dee4aea01ae4a9c7bfe4a63fcce4966ad9e4844c2be46f7636e45de151e458c67ce41a242ee414a759e398d376e38f2d78e37f5dab
  | 7, 1, 12 => 0xf42435d0f3f82decf3ee0630f3a8a818f3a1f4fef3733036f36d449cf367d1f7f34f0363f2c10465f280ddebf27b317ef24e026ef21bf636f1fe0360f198f40df195bf85f1350785f11de759f0e61da6f0d31038f0c49457f0be3d76f0857a5ff07b02c5f05ab396f05897d3f04f03a7f047ce9cf041e202f0296f4defaf0f89ef57b8faef335fc1ef2e9b0feeca28f2eeb4623aee459ecdee30e0bdee12c54dedf34286eddbee4dedd4dd83edacebaced8d83bded8629efed6973f8ed41d198ed19e3bfed105b43ecff8014ecf6989eeceb1d3becc5cb2aecb91f5fec99ef6dec72facaec6e369fec663512ec65e546ec20b13cec1a7a9bec01c0ebebfd1c1c
  | 7, 1, 13 => 0xfdaefc54fd9d02e8fd99ff10fd93ab53fd90ee05fd676c26fd3ce5b2fcfe2ea5fcecae0dfcb0afc1fc8bca0cfc20dd5afc02cecffbc1bc8dfbbf59a1fbbcb1d0fb88fb78fb6b568bfb3e6e67fb2e4632facfb439fab21684fa9321d7fa25e2b1fa11d0d1fa10fd1dfa0187f4f9f779d9f9b38880f9a8b337f9554771f9552142f947aac1f92dd199f8fbfd03f8dbc959f848f742f8456696f8454e67f82e5cddf82ca004f821a1bdf81aa65df8037aa5f7f54a0af7813a1af75b3d8ef7568747f713a9b3f6f4ac3ff68e4a3df66671a5f644b462f6189a95f61649e1f5e05daef5c74da0f5373f08f4fa1d32f4c930adf4b303e2f4a423e9f469dc77f46969da
  | 7, 1, 14 => 0xffff0634fffea3a6fffd9e4bffb3f673ff86098aff640b3dff58e3f3ff4da10aff3d1588ff123350ff0402b5fefe038cfee73185fea4321afe971ab2fe82066dfe7e7e7afe69f639fe554becfe5269ebfe24198cfdf4a2a0fdf0164bfddd6bbc
  | 8, 0, 0 => 0x21a9023c2136416c20bd10b42085ba6f1fbe639e1f505e561eb180c41eaec2be1e21c84f1da3c2791d42c60e1cc1ea541c3bd1d81c1a73291b9b06e31ad3e37a1a51558f19edd2a919b15e681917953718ed5c0818b98c201867ad1418097fbf18035660179ba568174164871703b38d155b070712b5374512a036a6126f593f11f546a61101c9f510bcd6ce0f970d4b0f88aeee0db6ae630d2e3d660cf6d6570cd4669f0c5bdf350c0c577e0c041eab0bedd9ed0b8bbf6b0b15b6280af1fed60ae68dfb0a9f6c0309efeca509d69a710907828d08719fb80790ca2a07852a5a076d9aca07540f0804be9b5d0426a54103e5727602c7e1c601c0cf2f01737d88
  | 8, 0, 1 => 0x52652dd551f0701b50c1bb7d50a840dd509cfade4fed6a864ef5be6c4dcff4e94d2f3c8a4bba970048be36e948a30f484716cec6455fb1d0452bb7f644ea4890449d41de43fdcee443cb072843a4cbbe42ed440f424b4c73412582f0411da5b740b9cff8408d4406400015073fd242ec3eb72f933d88f5423d41059b3c8ae61d39559c2f376a4f6936aa1577368f6cac36209e1535e8537e352b3a5934bca48e33e83ed833ac494932c96d1e31c32ec33116eaad30797d6f30452eee2ff1212a2f1583e82ee5f83b2dbb214e2d6782ad2c9d909e2b5379482b3beed929e93d17293de18527a4a97826c74c062595651923d4986c23937e852209c14921b44742
  | 8, 0, 2 => 0x76e1ad9c76b73a4776abcfae7663a7c675a337077596bf2d759045d8752fd481749a204b745985b3740279ad739f2b3972f58c2c7278be20724ff73c712a2db970e422b0706ffaba705b213270519bba70227bd6700149d46f653f376ebd78496ea16f056d97aec66d42739e6cd46e566c8cdfa26b58cb236b3d020a6af4746f6aeac5db6a314b0769999003690b818467af13ba6722ad006716b47363ff7f47621b7fc56131850560f5b64260bf4dc96013f4555c6c86d75bf8a09c5b7badac59428c4e58652e3d572b3dcc56cdce4e567ab1f4564fc87855da718055b00d5b5514da2a53fc1e2653ebb6ee53d94335532b31af52e2f8d752d41b9452c6dafb
  | 8, 0, 3 => 0xa2729855a26835d3a203df1fa1ea2ffda185d949a08ce91fa039bc459deb9d439d717a869d3b975e9bea8a5f9b87d20b9b237b579a8d182a999e3acc97b3be83979476b89790a9e095f96264956af0e494dbd1b49492ddb294213f909406f9df92e1305c92bd4609928a0576917f8e97913e368f90dec3a2909436918f95124e8f87e3d58ea1b5b78e5c135a8e3118c78d8425078cb80d3c8c53b6888c27a7848b9a7c8c8b3625d88969c3558911bc2488c8f86088c3fb8588a3b6dc877f470c861b4d8585db428984135e95836a9b7e83490ab082fc9636816c4ed8811ec7de801c3ae37f82a65d7f1e4fa97dd7bdf57d57e2b57c3a52057b7c8fb07b436789
  | 8, 0, 4 => 0xcccd458fcb694c08cad8ea57cacb121cca5896e9c9ad816cc972257ac92fe007c90dcec6c8f91191c7fd48dcc7abb727c77d5d96c74aa3c2c6dc9e7ac6579413c5af49adc52d073fc242cba7c2157f87c11b76cfc02126d4bfa320febd95ab3dbb553d6fbb32f41dbab4727abaa031c9b9fc0058b96ac126b940c30cb8db3bf4b806c79fb6b375dab5e0fc76b3ef6d88b399a266b37b151bb1838f47b14a7c74b141b29aafabcd08af99e6ccaf359018af1d0a4eae6ff2a8ad70b361ad48081daba98afbab2b8525aa70fe3da96bd003a9536d8da91c00b9a906a98fa7697e48a6ea9da8a643b4c5a5ef21d7a4c9dd97a4c92733a3d3d878a3ac4ce7a38fee89
  | 8, 0, 5 => 0xf779aaaaf6b00b97f4ed8e48f4b6683ef46969daf452118af42e45c1f3c7c4c5f303e5cdf29f8f19f1de1c4af1af9c79f179c596f13196a3ef2e9b0feecba126ee9a4055edacebacece124ddeb8687baeacf38b1eaa4dc92e9877a69e8a9e5dbe78c552be76e1fb8e72b167be7125d9fe6a45857e3a3bb46e337d007e286305de27df1c3e2182b15e1f09bdde1c02f6ee07b3ab3dffd34ddddce86eedbff73e2db747efcdae1e332dabcacbbdab6ff36da70651bda025fd3d9f67adfd9e2caf7d99ad6ebd992242bd749a837d676da41d428db12d35f5289d277431ed175aa0ed111535ad0bc3a17cf54f589cee4c42bceca0d03ce16f6e3ce0e84ffcd52d7cd
  | 8, 0, 6 => 0xff89d50dfee14d72feceb7ccfe5a0e72fdf7bd66fddc089cfc453af5fbcfa734fb3c38d9fb1f7172fab21684f7e1aeb9f7af6be0
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x43094434c00000000a1050010832080000430c82020011430480400351052010010832080108351093000000002841108351093020010c3208090c2510d302
  | 6, 0, 0 => 0x842400000021090000002840c00001051010000a03880000320062000000203880400450c1200000000384240000006100000d4104808004350c20100002038800000000e10400094434800004350c201000c8008808000590c20200006028800000000e102000003204000021484202000d4104808004350c2010000003841400000411070001641480400450c92020011430480000250412000000000841c0000012107
  | 6, 0, 1 => 0x1840000450c120100000028404004350c2010000201880400000061010000a04880000320022000000010441c000080a2020000003841c00250c12000000002840c000000210700108008800000000a10100000028404000180e20000000018400000080e2010000002840400008122020000000840c00008122010000002840c00314c42000000004840c000000e1090000004841c00058c8200001080388000000006109
  | 6, 0, 2 => 0x11410480800355002000000002840c00018122010000003841c00324c820000094434808002504120200002038804000000a100000000384000025041202000c8018808004200e20000006048800000000a10900094104800004200220000114104808000000e102000c8048800002504120000000018408000000e1020000032040000350812020000004840400150812020010c008808000010c10200002018800000080a202
  | 6, 0, 3 => 0x6038800000281220100002028800000001210200000038404000080e20000000048404000381220000108038800000000a1010000002841c000080a20100000028404000280e200000000284000000812200000c801880000000021050008521080800420062000009410480000000c810200016320808000000a10300000420400000180a2000010c0188080003812200000000484000035105201000060288000000806202
  | 6, 0, 4 => 0x114304800003201220000000048424000000610900000008410000080e20000000018400002510d20200108018800000080a2000011420480800320062020000a04880400150812000000a04880000000061020000604880400000061020000002840400450812020000004840c000000a10200000048424000080620000006028804000280e2000000002840400058c12010010c3208080000812200000c804880800000c8102
  | 6, 0, 5 => 0x2840800000061090010d43080400314c420000000048400004300620200094304800003201220200006038808000001210200002018800000000210700000028404000180a2010008120080800420062000000003840400000061030000002841c000180a2000000e018800000000a1090000043040800304c02000000002841c00350412000000004841c000000a10100006048800004140a2010010c0288080035041200
  | 6, 0, 6 => 0x6048800004504120000016320808004350c20100002048800000000a1040000010440c000000e10700094304800000000e1090000000840c00000061070000003840c00450c12000010c320808000281220000105038804002504120200114324800000000610700000018404001510120000002018800004504120000000028400c8450c93000000004840c000000610300000018410000180e20000114214800000010c102
  | 6, 0, 7 => 0x2842400000061030000604880400450c12000011410480800000021000000002840c00000021070010c02880800000061090010803880000038122010000603880800000021000000e04880800000121090000a038808003504120000006028800000280e2010000003841000001051010000e048800000010810000002028800000281220000006038804000000e10900000320400000000e100000d44248000025041202
  | 6, 0, 8 => 0xa03880400028122010010c00880800450c520200000018408000000e1070011410480800430062020000000840000320062020000000840c000000a1030000001840c00001051010000010440c000000a1070000030440400000c11010000003840800320022020000032040800000411070010c320808000000a107000c5310800000000a10700000028404004508120200108008800000180e2010000a038808000000e103
  | 6, 0, 9 => 0xd410480000250c5202000060288080000012107000d4204808000000a1070000032040000450412000010801880000214842000000003840000350812020000004841c000000a1030000a048804000180a2020000604880000018122020000004840c00000061030000000841c000001210700000018400000010810000054304800000001210300000018400000000a1070000010440c00000021010000e048808000180e202
  | 6, 0, 10 => 0xa038804000001210900000048424000000a1090000002840400000121000000010440c00350412000000e04880400420c820000006038800000000a1020010c028808000000e10300000008424004508120200000018408000010810000000048424003200220000094304800004300620200000414404002510d2000000002840c00320122020000003840c00000c110100000430408000180a2010000010441c0035041200
  | 6, 0, 11 => 0x32040800450c120000054304800000081220100000018400000000e1070000001840c00000021040000202880400028122020009410480000000c8100000000084080000002102000c104880400008062010000a048808000000a1030000003840c000000a104000000284240035085200000000284000001812202000000284000000012103000d4204800000000a10332114324c08000000a101000d44248000000002107
  | 6, 0, 12 => 0x114104800001044020000000320400000000e10500114104800000000e1030000001841400000c11010000004840c000280e2010009430480000450c12000010c32080800018122020000003840c00000121030000a03880000420c82000000001840c000000a10700114104800000000e10300002018804000080e20200000008424004300a2020000003841c00038122000000003840c00420c8200000c80188000002806202
  | 6, 0, 13 => 0x21070000000840400058c820000006048800000080e200000d4424808000000e10000002018808000004110300000420400004508120000000028414000000e100000000284000000006103000164208000032002200000c102880400351092020000002841400250c1200000c8048800000000a10300006038800000000e1090000010441c00000c810200108320800000080a201000d4104808000180a202
  | 7, 0, 0 => 0x114314808000010c101000c932080400000c81000000202880000000841000000001840800000c81020000002840000000061020000004841c000000a1020000002840c000080a20200000320408000010810000000038408004350c20100000008408000000a10700000310408000081220100000038404000000e10300000018408000010c10200000038400000000e1000000a038808000000e107000020188080000012101
  | 7, 0, 1 => 0xa038800000180e20000000018400000000a10100000038408000000e10200000038400000001210100000018404000000e10200000404404000080620000000420408000000e10700000018404000000a10400000008424000004110000000048408000000610300000008404000000e10000000018424000000a10900000048400000000e1030000002840800000121090000001840000000411030000000841c0000012100
  | 7, 0, 2 => 0x85210800000010410000000048408004250820100000204404000000e1040000003840000000061020000a04880800001081000000003841c000001210700000104404000000610200000048400000010010200000048424000010910100000028408000000a1070000001840000000411020000e04880400314c420000006048800000000a101000003044040000806201000d420480800000c8100000000284080000002107
  | 7, 0, 3 => 0x841c000000e10300002018800000000a1030000001840000000061000000041440400028122010000000840000000061010010d430804000000a10300000028408000001210100000104404000000a10000000038424000000e10100000424404000000a10900000008400000000e1090000032040800000c81000000001840c00324c82020000041440400000c81000000002840000324c820000000018408000000e109
  | 7, 0, 4 => 0x32440400000c91010000002840c00000121030000042040000000411070000030440000000061020000003840c00250c12000000003841c0000006100000000084040002812201000c1048804000000a1090000030040800000121020000003840800000061000000003841c000180a200000c5310808000010410200000008424000381220200006038804000381220000000038404000000a101000943048000000012101
  | 7, 0, 5 => 0xc1018804000280e2020000010440800000c010000000210408000000a1020000a03880000000c810000000028404000080e20000000048408000000e1000000003840400000061020000001840c00000c810000000430400000000e1010000031440000324c820000000410400000008510200002038808000000e10300000304400000010010000000104400000180e20200000324404000000a100000000484000000006109
  | 7, 0, 6 => 0xa03880400000021090000000840800000121000000043440400450c12010000002840000000121070000002841c00000c41000000004840800000c810000000008424000010810200000404404000000e10000114304800000000e1030000001840000000841020000e048804000081220200000214404000000610300000048404000010c1000000002840800000121010000003840800000021010000010440c000000a101
  | 7, 0, 7 => 0x2840000000c510100000038400000000210100000028410000000610100000320408000000210200000320400000000e10000000028400000010810000000028404000010910100000028408000000a10100000048400003200620200000420408000000e10200002038804000281220000000314400000000a10900000048408000000e10300000028424000000210100000320408000000a10000000048404000000a103
  | 7, 0, 8 => 0x10d430804000000e10100000204408000000610000114304804002148420200000038424000008110100000028404000010c10200000414404000000e10900000038400000000e1090000003840800000c81000000002840c00000c810200000038424000000a10100000018408000000e1020000003842400000c81000000031040000038122020000a038800000180e20100000038408000000e103000001044000045041200
  | 7, 0, 9 => 0x18400000008010200000320408000000a10300000018424000000610200002038800000080a20000000048400000001210000000320400003508120200000048404000000210000000018408000001210300000008410000010810000002028804000000210000000028404000010c10000000038400000080a20100000038424000010910100000018400000000a10700000018400000000a102000003204000000108100
  | 7, 0, 10 => 0x420408000280e2010000003840000000121010000004840800000061090000001841c00000c81000000003840c00450c120000000018408000000e10300000048424000000610200000018400000000a1010000000840400000411070000003841c000000e10200000410400000000210700000018424000000e1010000a048800000000e101000000184240000006104000d410480000324c820200000314400000000e101
  | 7, 0, 11 => 0x314404000000610200000038400000000e10100000028400000000210300000028400000381220100000028404000000a1010000004840800001041020001643080800351052010000001840400000811010000020440400000121000000001840000314c42000000001840000000c81000000004840400000c51010000e04880800000061070000002840800058c8202000004244040000012103000002004000000002100
  | 7, 0, 12 => 0x48404000000210900000048400000010910100000028408000180e2000000021440400018122020000010440c000181220000000008424000000e1030000e048804000000210200000028424000010c1020000002840c00000061030000030040800000c810200000104408000000a1010000031040800000121010000003840800000121010000003840c000000a107000000384000045081202000c5310800000010c102
  | 7, 0, 13 => 0x8414000080620200000018404000000a103000003204080000006101000004304080045081200000c8048808000000a1020000041040000351052010000000840000000c810000000048404000000a1000000001840000000c41000000002840c000001210900000038404000280e202000003204080000108100000c102880400000c410200000424404000000610100000310400000008510100000008404000000e101
  | 7, 0, 14 => 0xa03880400000021090000000840c000004110300000324404000000a10100000204408000000210200000048404000000a10100000018400000000210000000210408000001210300000214404000000a1000000000840800000121090000602880800000c810200000038424000180a2000000201880000000061070000a038800000000a1070000002840800000c51010000604880800450c92020000001840c000000e101
  | 7, 0, 15 => 0x38408000000210700002028800000000610500000048408000004110300000210400000000e10900000420400000000a1070000002840400000021030000002840c0000104102000000084080021484202000c1104804000000e1020000010440000000121010010c32080800250c120000000018408000010810000000304400000001210700000048400004300e20200000430404000000e10000000018404000000a109
  | 7, 1, 0 => 0x414404000000e10100085210800000000e10200000018408000000210100108320800000181220000000210408000180e20000006048808000000e10000006028800000001210100000048408000000610000000210400000000a10900000018410000001210100000304404000000e10100000038410000010010000000028408000000610000000008408000001210000000018424000001210300000018400000180a202
  | 7, 1, 1 => 0x18404000000e1030000004841c00000c510000094104808000000a10700000048408000001210100000420400000001210900000038408000000a10200000038404000010910100000210408000181220100002038808000000610900000320400000000a10200000038424000000e10100000430404000080e20100000420408000000610200000038408000000a100000000284000000108100000000284040000100100
  | 7, 1, 2 => 0xc5310808000000210700000430408000000e1020000010440000038122000000010440400450812010000602880000000c81020000043440400450c12010000043040800000c410200000028408000000a10000000038404002504120000000028408000000e1010000031040000000021000000003841c000001210300002018800000000210000000304404000000a1010000031440000000c110000000414404000000e102
  | 7, 1, 3 => 0x28408000081220200000210400000000210700000420400000010810000000028404000001210300006038808000000610700000410408000000610300000038404000000a10700006048808000010c1020000002840c000001210100000320400000000a1000011420480800000061000000041440400000c51010000002840000000061020000002840c0000100100000004304040000006102000000184000000006109
  | 7, 1, 4 => 0x430400000000a10100000018400000280e2000000004840400028122020000a048800000010d1010000002841c000000e10000000028404000000610200000028404000081220000000008404000000210900000018400000000a1010000001840000000121070000a03880800001081000000a03880400001091010000041040000001051010000032040000000061010000003840c00000021000000003841c0000041102
  | 7, 1, 5 => 0x114304800000000e105000c9320800000000610200000048400000000a10100000410400000080a2020000004840c00001041000000000841c000000e1010000602880800000c8102000c8008800000010c10200000304404000001210100000028424000000a10100000038424000010c1020000001840400000021010000002840c000000a10200000430408000010810000000038400000000a10300000028408000000a103
  | 7, 1, 6 => 0x2038808000000e10900000038408000000e1000000001840400000121020000004842400000021030000010441c000000e1020000e04880000000061020000602880000214c820000000038404000001210000000038424000010c10200000410408000000210000000038410003508120200000038400000010c10100002028800000000a10900000404400000000a1090000003841c000001210000000018414000000e107
  | 7, 1, 7 => 0x320408000000e1030000002840000000c81020000a048804000000a1000000004841c000000e10200000018408000001210000000028414000000610000000048424000000e1070010c01880800008122010000003840c00425082010000010440800000c4100000000084080000012109000d4414804000010c10100000048424003540a20000000048408003508120200000018404000000e109000000184080021484200
  | 7, 1, 8 => 0x3840000000061000000002842400008062010000001840c000000a10900000038424000000a1020000004840400000c010000000048408000000a101000c9320808000010110100000018424000010110100000028424000010c1010000003840c000280e2000000a048808000000610900000008400000000210200000028408000000a10900000018400000081220000000048424000000610200000048404000000a100
  | 7, 1, 9 => 0x4840000000c810200000038404000000e1010000001840800000021000000001840000028122010000041040800000c810000006028804000000a1020000042040000000841000000000841c000008110100000038400000000a10000000048404000000a109000c932080000000411020000003841c00000061020000001841c000000e1030000043040000000121000000002840000000061020000002841c0000012103
  | 7, 1, 10 => 0x3840400018122000000603880800000121070000001840c00000021010000002841c000001210300000038400000000a1000000032040800000061020000004840c000000a1020000010440000000121030000002841c000000a10100000410408000010c10200000018404000000e1020000004841c00000061020000002840c0000012100000c5310808000010c1000000202880000000c81020000002842400000c4100
  | 7, 1, 11 => 0x38404000000a100000c8018800000010d10100000028400000000e10500000304404000180e2000000010441c000000a1010000032440400000c81020000602880400000c810200000048404000000e101000c5310808000280e2020000032040800001011010000042040000028122020000003840800425082010011430480400000411000000000841c000000e107000000184080000002101000000284000000006101
  | 7, 1, 12 => 0x114214800000010c1000000010441c000081220100000008424000000e10000000018400000000e10100000420408000000e10900006048804000180a2000000002841c000000e10700000048424000000610000000324404000281220000000310400000001210100000018414000081220100000008400000180a2020000021040800000c810000000038424000008510000000304400000004110000000048404000000e101
  | 7, 1, 13 => 0x43040400000021020000004840800000121020000043440400000c81000000002841c00000121090000003840800000061090000030440400000061010000001840c000080e20200000320408003508520100000028404002148420200000048400000000a10300000414404000000210300000310408000000e1020000003840400324c820100000320400000000210200002018800000000a10900000008400000000e100
  | 7, 1, 14 => 0x18400000010c1010010c02880800008062020000003840c000010510100000018408000000610000000028404000008410000000048408000000e10900000048404000001210700000018408000181220000000048400000000610000000310408000000e10000000038400000000e10900000430408000000a10900000204408000000210100000018400000000a10700000320400000008010000000018408000000a101
  | 7, 1, 15 => 0x1842400000c81000000004841c00000c11010000004840c0000006105000c8008808000000a10200000028408000000e1000000002841c00000121000000e048804000000a1090000041040000000c81020000021440400000c810200000008424000080a2010000002840c000000a1000000203880400058c820000000028408000000a10200000028404000010c100000d4214800000000a10000000038400000000e100
  | 7, 2, 0 => 0x840c000000a10200000048408000000e1090000000842400000c410200000008404000010c1010000e048808000000a10200000320400002148420000000430408000000e1020000003841c00000c110100006028800000001210700000038400003504120200000038404000010c102000003244040000012101000000184080000006101000000484080000806202000001044040000085101000000084000045081202
  | 7, 2, 1 => 0x430408003201220000000018408000000a10300000310400000000a10100000204404000000a1020000002840400038122000000e048804000000210000000204408000000210700000018400000010810100000414404000000a1030000603880400000121010000042440400000021010000001840800324c820100000424404000000a10900000038424000000e10200000048404000000210100000214404000000e102
  | 7, 2, 2 => 0x840800000851010000041040800000121000000003840000250c120000000048408000000a1020000030440000028122000000a038808000001210100000018424000000e10700000048400000000a1040000032040800000811020000003841400028122020000004840400000061000000003840400000061010000003840800000c810000000008408000000a10200000104408000000e10700000430408000010c101
  | 7, 2, 3 => 0x3840c00000061010000004840400028122010000004841c003200a20000000300400000180a2020000003840000000061020000003840400000121010000a038800000000e1030000a04880400000c010000000430408000000e10100000008400000081220000006038804000000e1000000043040000000c810000105028804000000e100000000284080021484200000000084080000006100000004304080000002101
  | 7, 2, 4 => 0x48408000010c1020000003840000000c810000000048400000001210100000210408000000210000000410408000080a2010000031040000000121090000043040400000121020000003841c000000e10300000038424000000a1030000002840000000121010000042040000000021020000031040800250c120200000018404000008410000000028414000000210400000008404000000a107001080388000000012101
  | 7, 2, 5 => 0x3840c00420022000000001840c000000e1000000001840000000c810200006028804000000e10700094314808000000e10100000430400000000610000000420400000000e10300000008400000000a10000000038404000001210900000324404000080a20000000434404000180a2010000032040800008122020000031440400000121090000002841c00000121020000004840000000121070000003841c0000002100
  | 7, 2, 6 => 0x28408000281220000000028400000000a1070000000841c00000c41020000000840000324c82010000032440000000061010000041040000314c82020000001841c000000e1020000032040000000061020000003841c000000210300000018400000000e1050000003840c00008062020000003840c000001210700000038400000008010200000038424000000e10000000018408000000e1070000003840c0000100100
  | 7, 2, 7 => 0x1840000000061030010d430804000008510200000008400000000a10300000008400000000e10100000018400000080e2010000010440000000121020000001840c000000a10100000430408000000210000000048404000000210100000018400000001210100000028424000000e10900000018400000000610300002028808000000a10000000038404002150820000000320400000000e10900000324404000000a101
  | 7, 2, 8 => 0x3840800420c820000002038800000000a1020000004840800000061090010d430804000000e100000000284100000006109000d420480800001081020000001840000000c810000000008414000000a1010000a038804000000210700000038424000000e10000000414404000180e20200000028414002148420200000018408000000e107000c5310808000010910100000420400000000e1020000001840c000000e103
  | 7, 2, 9 => 0x28404000001210200000028400000000e101000003144040000002102000000084000000006102000d441480400450c120000000430408000000a10000095038808000000e10100000200400000000e10000000038400000000e10900000008424000000a10200006048808000000e10300016420800000081220200000018400000000210200000210400000000a1010000003840400000061020000003840000450c1201
  | 7, 2, 10 => 0x32040000000121090000002840800000021000000003840800000411000000004840c000008410200000420400000000a1010000002840800000c81010000004841c000000210400000320408000181220000000430404000280e2010000003841c00000021090000000841c00000c81000000003840400000c81000000003840c000000e10200000038424000000a101000000084000000006102000000184080000002109
  | 7, 2, 11 => 0x10440000000121000000e04880400000c1100000003104080000006100000004204080000085101000c9320804000010110100000430400000180a2020000004841c004140e20100000048404000000a10100000038408000000210000000018410000000a10000000018424000000610300000320408000000210900000048404000000e1020000002840400000021010000031040000000061020000020440800000c0100
  | 7, 2, 12 => 0x38404000004110100000038400000001210200000320400000010010200000320408000008110100000008404000080e20200000410400000081220200000038400000000e10700000210400000180a20000000028408000000a1030000032440400000c810000000048408000000a10500000320408000000610000000304404000010c1010000000840c00000061000000001840c000010110100000424404000000a102
  | 7, 2, 13 => 0x11430480800000021000000002840400001081000000002840000000121020000001840000000021030000002840400000021030000003840000000801000000002841c00000c81020000603880400000c510000094304800000000e1070000000841c000000210100000008404000000610000000018404000001210700000430400000000e10300002038804000000e1030000002842400420062000000002840c000080e200
  | 7, 2, 14 => 0x841000450c12000000021040000324c82020000004840000000841000000003840000000841000000002840c00450412020000042040000001081000000002840400000061000000000840400000c11010000002840c00450c12010000e048808000000210000002028808000008010200000028400000000a1030000032040800000411010000004840c0000002107000d4414804000000a100000000484000000085102
  | 7, 2, 15 => 0x28400000180e20000000430408000010c101000000484240035081202000c9320800000000210900000028400000000210000006048804000000610900000048404000000e1000000002842400250c120000000038404000080e20000000028400000010810000000320400000000a10900000018408000000e1020000000840000000061070000001840800314c420000000038400000000a10200000420400000000e107
  | 7, 3, 0 => 0x18414000008510200000104400000000e1000000042040000000061090000002840000000c1100000003044040000006102000c9320808000000a1020000003840800001051010000031440000000841020000002841000430022020000a038808000000e10000000310400000000e10000000420400000000e1090000001841c000000a10200000048424000001210200000214408000000a101000000284040045081202
  | 7, 3, 1 => 0x2840800000061000000001842400001041000000010440c000000a1090000032040800000061020000002842400000021010000201880000028122020000003840c000000a10200000320400000000a10000000038410000000a10100000018400000000a10100000018404000000e1010000010440c00000061040010510480400000021020000000840800000c5101000000484080000812201000000084240000006100
  | 7, 3, 2 => 0x8424000000e10000000028404000000a10700000048404000000e1030000a048800000001210300114204808000000210200000420400000004110700000320408000000610000000038404000001210000000028424000000210200000008410000000e10000000420400000000a10900000320400000001210000000028424000000a1020000003840400000021000000001840800000c8100000004144040000081101
  | 7, 3, 3 => 0x38400000000a10000000048424000000e10000000008404000000610200000038404000000210200000048424000000210700000430404000000e1020000001840000000061030000042040800000c81020000002841c000000e1010000000840800000841000000002840800008122010000e04880000000121030000000840000000c110100000028404000080620100000430408000000e100000000284040000012100
  | 7, 3, 4 => 0x2018804000001210300000424404000081220000000420400000180e20200000414404000000e1030000043040800000c810200000028400000010c1010000a038804000000e1020000004840c00001011010000001841400324c820100000430408000000610300002038808000000a10000000420408000001210100114304800000000e10700000028404000000a1000000000841c000000e102000060488040000012100
  | 7, 3, 5 => 0x430400000004110200000018404000000a10000000410408000000210500002038800000000e1070000202880800001001000000001840000000c910100000310408000000a103000003044040000806200000000284240000081101000c9320800000000e1000000043440400008062020000041040000000121030000004840c004200a2000000004840000350812000000004840000000c81020000a0388040042508201
  | 7, 3, 6 => 0x28400000010410000000048408000000a10000000008404000281220100000104408000010810000006038800003510520100000414400000010410200000430404000000610200114304800000000610300000310400000004110200000320408000000610700000018400000000a1070000e048800000001210100000048424000010410200000048404000010c1020000000841c0000012101000000184100042508201
  | 7, 3, 7 => 0x18408000010410200000018400000081220000000018404000000a10700000028424000000610000000038400000000a10100000048400000008110000000320408000000610100000210408000000e10400000320400000000e10000000018400000000a10200000304404000000a104000001044000000012100000000384140001812202000c543080800214842020000000840400450c920000000008400000000e102
  | 7, 3, 8 => 0x4841c000000e1030000002840800000841020000001840800000021090000043040400000121000000602880400000c81020000030440000000061000000004840c000004110700000038424000010510100000304404000000e10100000324404000001210200000104404000000e1010000002840c000280e200000000284240000002109000003204000000012100000000484080000006107000004204000000105101
  | 7, 3, 9 => 0x28408000010d10100000410400000080a20000000104404000080a2010000003840000000121020000032040000450812020000000841400314c420000000200400000000e1020000004841c002148420000000008400000000610200000038400000000610300000028400000000610400000028414000180a2020000004840c00000c91010000000840c000000a1010000002841c00000121020000001840000000c8102
  | 7, 3, 10 => 0x2840c00000411000000004840c000000210300000038424000000a10200000304404000281220100000008400000381220200000008408000000e1030000e048804000000e1010000003841c000000610200000320400000000210100000038400000000e1050000603880800000c810200000028400000180e20000000028424000000210000000028408004250820100000048404000181220100000430408000000a100
  | 7, 3, 11 => 0x18400000000210000000038404000000a10100000104404000000e1040000004842400430c820200000018408004350c2010000603880800314c420000000008400000000610100000320400000001210300002028804000000a10200006048800000081220000000048400000001210100000018404003200e20200000420408000010c1020000003841c0000040100000000184000000108100000003004000000002102
  | 7, 3, 12 => 0xe048800000000a10100105008804000010c10200006038800000001210100000214408000000e10700006028804000000a10200006038804000008110200000320400000000e1030000041040000000121000000004841c000000a1050000003842400250c120000000048404000000e1020000000840800000c9101
  | 8, 0, 0 => 0x840000000c810100000320408000000e10200000028400000000a10200000048404000008510000000104404000010810100000320400000000a10000000204404000000610200000430404000010510100000038400000010910100000048404000000610100000028404000000a10200000214408000001210000000210400000000e102000001044040000081100000000384040000012101000000184040000101101
  | 8, 0, 1 => 0x18400000008410000000028400000010d1010000031040800000411020000002840400000061020000042040800000841020000030440800000c51020000041440400001091010000000840400000c51000000002840400000c11000000000840800000c810100000304404000001210000000018408000010410000000018400000010110100000314408000008110200000204400000010910100000104400000010c102
  | 8, 0, 2 => 0x210408000000210200000104404000010810000000018408000010410200000314404000008110200000324408000000610100000430400000000210100000320400000000a10100000204404000000e10000000304404000000610000000038404000000a1020000004840400000061020000041440400000061000000041040000000851000000002840400001011010000010440000000c1100000003104080000108100
  | 8, 0, 3 => 0x2840400000c810000000028400000010c1020000002840400000c510200000320408000000e10200000028408000008510100000048400000000e10100000214404000008110000000048408000010410000000214408000010c1000000032440400000851010000032040400000c810000000038400000000a10200000324408000000e1010000003840800000c41000000010440800000c9100000003144040000109101
  | 8, 0, 4 => 0x104408000010c10100000304400000001210100000018400000000210000000314404000000610200000430404000000a1000000004840400001081020000003840000000851000000042040400000c11020000041040000000c11000000042040400001081020000001840000000841020000041440400001041020000032440400000c9100000003144040000041100000002144080000108100000003044080000085100
  | 8, 0, 5 => 0x420400000010110100000008400000008410000000008408000004110000000214404000010d10100000310400000000610200000430400000000e10200000204408000000e10100000320400000000e10000000214408000010c10200000430408000010c1000000043440400000c51000000041040800000c810200000404404000000e1020000042040400000811010000003840400000c41020000032440400000c4100
  | 8, 0, 6 => 0x430404000000e1010000041040800000c110100000048404000000a10200000028400000010910100000038408000000e1000000041440400000c41020000000840400000c910000000104408000000a10100000304404000000a1020000001840000001081010000001840400000811010000043440400000c41000000030440400000c91020000032440000000121020000003840400000121010000003840000000c1102
  | 8, 0, 7 => 0x21440000001081020000042040000000841020000021040000001011010000002840400000121000000042440400000c91020000000840000000c510200000314400000008110000000304400000000610000000434404000004110100000028400000000210200000038400000000610100000018408000010c10100000048404000008110200000320404000010510100000214400000000210100000048400000000a101
  | 8, 0, 8 => 0x30440400000c51010000001840800000c11020000042440400000c810200000028404000000e10100000104404000000a1000000001840800000061000000021440800001041000000030440000000c81020000042040000000841000000002840800000c410000000038408000010c1020000010440000000c810200000048404000000e10200000028400000000e1010000031440000000c81010000004840400000c9101
  | 8, 0, 9 => 0x18408000008110200000304404000000a10000000324404000000e10000000048408000010c10000000048400000000a10200000314404000000a1010000032040000000c410200000104408000000e10000000204400000008510100000324404000000e1010000001840000001081020000021040800000c910000000414404000000a1010000000840400000c410000000320404000000a101000003144080000006100
  | 8, 0, 10 => 0x48404000008110100000008400000000e10000000420400000008410000000104400000000a10000000324408000000e10000000048408000000a10000000420404000008110100000410408000000e10200000314400000010410000000314400000008510100000104400000000e10100000214400000000a102000000284000000002100000002044000000085102000003244000000002102000003204040000006102
  | 8, 0, 11 => 0x314408000010d10100000430404000010c10200000028400000010c1000000032440400000121010000032040800000c81000000003840800001081000000003840000000841000000002840800000c11000000043440400000061000000001840000000811020000031440000000c410000000038404000000a1020000003840800000811000000004840800000c410200000104408000010c101000004104000000108101
  | 8, 0, 12 => 0xc11020000001840000000c910000000420408000010c1000000021040800000c81000000003840400000c9102000000384000000012101000004304080000104102
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 12 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_x0_0 roots_x0_0 8 s ws hint
  | 1 => checkCutEntry dom_x5_1 roots_x5_1 8 s ws hint
  | 2 => checkCutEntry dom_x1_0 roots_x1_0 8 s ws hint
  | 3 => checkCutEntry dom_x3_1 roots_x3_1 7 s ws hint
  | 4 => checkCutEntry dom_x0_0_x3_1 roots_x0_0_x3_1 6 s ws hint
  | 5 => checkCutEntry dom_x1_0_x4_1 roots_x1_0_x4_1 6 s ws hint
  | 6 => checkCutEntry dom_x3_0_x5_1 roots_x3_0_x5_1 5 s ws hint
  | 7 => checkCutEntry dom_x4_1 roots_x4_1 7 s ws hint
  | 8 => checkCutEntry dom_x0_0_x4_1_x5_1 roots_x0_0_x4_1_x5_1 4 s ws hint
  | 9 => checkCutEntry dom_x2_0 roots_x2_0 7 s ws hint
  | 10 => checkCutEntry dom_x3_0 roots_x3_0 6 s ws hint
  | 11 => checkCutEntry dom_x3_0_x4_0 roots_x3_0_x4_0 5 s ws hint
  | 12 => checkCutEntry dom_x1_0_x3_1_x5_1 roots_x1_0_x3_1_x5_1 4 s ws hint
  | 13 => checkCutEntry dom_x4_0 roots_x4_0 6 s ws hint
  | 14 => checkCutEntry dom_x4_0_x5_1 roots_x4_0_x5_1 5 s ws hint
  | 15 => checkCutEntry dom_x3_1_x5_1 roots_x3_1_x5_1 5 s ws hint
  | 16 => checkCutEntry dom_x4_1_x5_1 roots_x4_1_x5_1 5 s ws hint
  | 17 => checkCutEntry dom_x3_0_x4_0_x5_1 roots_x3_0_x4_0_x5_1 4 s ws hint
  | 18 => checkCutEntry dom_x1_0_x3_1 roots_x1_0_x3_1 5 s ws hint
  | 19 => checkCutEntry dom_x0_0_x4_1 roots_x0_0_x4_1 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_63 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x3_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x3_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x4_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x3_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_1 _ hc
  · contradiction
def p0Subs : List Nat := [3, 9, 7, 0, 2, 1, 10, 13, 4, 5, 11, 15, 16, 6, 14, 8, 12, 17, 18, 19]
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)) ||
  p0Subs.any (fun k => checkCutByIdx s ws k)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_63 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq, Bool.or_eq_true] at h; rcases h with h1 | h0
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2
  · obtain ⟨k, _, hk⟩ := List.any_eq_true.1 h0; exact checkCutByIdx_sound hk
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_63 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_63 goalM u ys) : RunD dom_63 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_63 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 6 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 64 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 64 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6_64 : ∀ i, 64 ≤ i → i < 118 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 54 64 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 118 → Z 6 i = true := (range_split z6_0 z6_64)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_0 : ∀ i, 0 ≤ i → i < 64 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_64 : ∀ i, 64 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 64 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_128 : ∀ i, 128 ≤ i → i < 192 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_192 : ∀ i, 192 ≤ i → i < 256 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 192 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_256 : ∀ i, 256 ≤ i → i < 320 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 256 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_320 : ∀ i, 320 ≤ i → i < 384 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 320 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_384 : ∀ i, 384 ≤ i → i < 448 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 384 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_448 : ∀ i, 448 ≤ i → i < 512 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 448 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_512 : ∀ i, 512 ≤ i → i < 576 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 512 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_576 : ∀ i, 576 ≤ i → i < 597 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 21 576 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 597 → Z 7 i = true := (range_split (range_split (range_split z7_0 z7_64) (range_split z7_128 (range_split z7_192 z7_256))) (range_split (range_split z7_320 z7_384) (range_split z7_448 (range_split z7_512 z7_576))))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_0 : ∀ i, 0 ≤ i → i < 64 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_64 : ∀ i, 64 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 64 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_128 : ∀ i, 128 ≤ i → i < 192 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_192 : ∀ i, 192 ≤ i → i < 256 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 192 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_256 : ∀ i, 256 ≤ i → i < 257 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 256 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 257 → Z 8 i = true := (range_split (range_split z8_0 z8_64) (range_split z8_128 (range_split z8_192 z8_256)))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z9 : ∀ i, 0 ≤ i → i < 26 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 26 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
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
def RootG (s : Nat) : Bool := scr dom_63 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 6 5 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 10) (h : RunD dom_63 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_63 roots_63 goal_all 11 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_63 goal_all := by
    have h0 : isConstB dom_63 goal_all = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub; have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq; rw [hcov] at hbad; contradiction
end S_63
theorem low_63 : Lower dom_63 roots_63 goal_all 11 := S_63.noCircuit

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

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 12]⟩], 16⟩
theorem wit_mono : PEqualNP.MetaComplexity.Monotone2 wit := by simp [wit, PEqualNP.MetaComplexity.Monotone2]
theorem wit_size : wit.size ≤ 11 := by decide
theorem wit_eval : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = ((fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4007715040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0))) x := by decide +kernel
theorem hT6 : ∀ r : Fin 64, goal_all.testBit r.val = ((fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4007715040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0))) (pt6 r.val) := by decide +kernel
theorem lower : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4007715040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) t → 11 ≤ t :=
  lower_to_circuit6 (fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4007715040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) goal_all 11 hT6 (by unfold IsConst; decide) low_63

end PEqualNP.Outside.L_meta_40273_aux

theorem PEqualNP.Outside.L_meta_40273 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4007715040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808936 * 2 ^ 32 + 4007715040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro s hs
  have hlb : 11 ≤ s := PEqualNP.Outside.L_meta_40273_aux.lower s hs
  exact ⟨PEqualNP.Outside.L_meta_40273_aux.wit, PEqualNP.Outside.L_meta_40273_aux.wit_mono, le_trans PEqualNP.Outside.L_meta_40273_aux.wit_size hlb, PEqualNP.Outside.L_meta_40273_aux.wit_eval⟩
