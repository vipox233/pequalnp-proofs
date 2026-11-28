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

namespace PEqualNP.Outside.L_meta_40403_aux

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
def goal_all : Nat := 0xfeeaeee8fae8e8e8
def dom_63 : Nat := 0xffffffffffffffff
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]
def dom_x2_0_x4_1 : Nat := 0xf0f00000f0f0000
def roots_x2_0_x4_1 : List Nat := [0xa0a00000a0a0000, 0xc0c00000c0c0000, 0xf0000000f000000, 0xf0f000000000000]
def dom_x0_0_x4_1_x5_1 : Nat := 0x5555000000000000
def roots_x0_0_x4_1_x5_1 : List Nat := [0x4444000000000000, 0x5050000000000000, 0x5500000000000000]
def dom_x0_0_x4_1 : Nat := 0x5555000055550000
def roots_x0_0_x4_1 : List Nat := [0x4444000044440000, 0x5050000050500000, 0x5500000055000000, 0x5555000000000000]
def dom_x1_0_x4_1_x5_0 : Nat := 0x33330000
def roots_x1_0_x4_1_x5_0 : List Nat := [0x22220000, 0x30300000, 0x33000000]
def dom_x4_1_x5_0 : Nat := 0xffff0000
def roots_x4_1_x5_0 : List Nat := [0xaaaa0000, 0xcccc0000, 0xf0f00000, 0xff000000]
def dom_x1_0_x4_1 : Nat := 0x3333000033330000
def roots_x1_0_x4_1 : List Nat := [0x2222000022220000, 0x3030000030300000, 0x3300000033000000, 0x3333000000000000]
def dom_x3_0_x4_1_x5_0 : Nat := 0xff0000
def roots_x3_0_x4_1_x5_0 : List Nat := [0xaa0000, 0xcc0000, 0xf00000]
def dom_x4_1_x5_1 : Nat := 0xffff000000000000
def roots_x4_1_x5_1 : List Nat := [0xaaaa000000000000, 0xcccc000000000000, 0xf0f0000000000000, 0xff00000000000000]
def dom_x3_0_x4_1 : Nat := 0xff000000ff0000
def roots_x3_0_x4_1 : List Nat := [0xaa000000aa0000, 0xcc000000cc0000, 0xf0000000f00000, 0xff000000000000]
def dom_x4_1 : Nat := 0xffff0000ffff0000
def roots_x4_1 : List Nat := [0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000]
def dom_x1_0_x5_1 : Nat := 0x3333333300000000
def roots_x1_0_x5_1 : List Nat := [0x2222222200000000, 0x3030303000000000, 0x3300330000000000, 0x3333000000000000]
def dom_x0_0_x5_1 : Nat := 0x5555555500000000
def roots_x0_0_x5_1 : List Nat := [0x4444444400000000, 0x5050505000000000, 0x5500550000000000, 0x5555000000000000]
def dom_x2_0_x4_0_x5_1 : Nat := 0xf0f00000000
def roots_x2_0_x4_0_x5_1 : List Nat := [0xa0a00000000, 0xc0c00000000, 0xf0000000000]
def dom_x4_0_x5_1 : Nat := 0xffff00000000
def roots_x4_0_x5_1 : List Nat := [0xaaaa00000000, 0xcccc00000000, 0xf0f000000000, 0xff0000000000]
def dom_x2_0_x5_1 : Nat := 0xf0f0f0f00000000
def roots_x2_0_x5_1 : List Nat := [0xa0a0a0a00000000, 0xc0c0c0c00000000, 0xf000f0000000000, 0xf0f000000000000]
def dom_x3_0_x4_0_x5_1 : Nat := 0xff00000000
def roots_x3_0_x4_0_x5_1 : List Nat := [0xaa00000000, 0xcc00000000, 0xf000000000]
def dom_x3_0_x5_1 : Nat := 0xff00ff00000000
def roots_x3_0_x5_1 : List Nat := [0xaa00aa00000000, 0xcc00cc00000000, 0xf000f000000000, 0xff000000000000]
def dom_x5_1 : Nat := 0xffffffff00000000
def roots_x5_1 : List Nat := [0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000]
def dom_x0_1_x1_0_x2_0 : Nat := 0x202020202020202
def roots_x0_1_x1_0_x2_0 : List Nat := [0x200020002000200, 0x202000002020000, 0x202020200000000]
def dom_x0_1_x1_0 : Nat := 0x2222222222222222
def roots_x0_1_x1_0 : List Nat := [0x2020202020202020, 0x2200220022002200, 0x2222000022220000, 0x2222222200000000]
def dom_x1_0_x3_1_x5_0 : Nat := 0x33003300
def roots_x1_0_x3_1_x5_0 : List Nat := [0x22002200, 0x30003000, 0x33000000]
def dom_x1_0_x5_0 : Nat := 0x33333333
def roots_x1_0_x5_0 : List Nat := [0x22222222, 0x30303030, 0x33003300, 0x33330000]
def dom_x1_0_x2_0 : Nat := 0x303030303030303
def roots_x1_0_x2_0 : List Nat := [0x202020202020202, 0x300030003000300, 0x303000003030000, 0x303030300000000]
def dom_x1_0_x3_1 : Nat := 0x3300330033003300
def roots_x1_0_x3_1 : List Nat := [0x2200220022002200, 0x3000300030003000, 0x3300000033000000, 0x3300330000000000]
def dom_x1_0 : Nat := 0x3333333333333333
def roots_x1_0 : List Nat := [0x2222222222222222, 0x3030303030303030, 0x3300330033003300, 0x3333000033330000, 0x3333333300000000]
def dom_x0_1_x2_0 : Nat := 0xa0a0a0a0a0a0a0a
def roots_x0_1_x2_0 : List Nat := [0x808080808080808, 0xa000a000a000a00, 0xa0a00000a0a0000, 0xa0a0a0a00000000]
def dom_x2_0_x3_1_x4_0 : Nat := 0xf0000000f00
def roots_x2_0_x3_1_x4_0 : List Nat := [0xa0000000a00, 0xc0000000c00, 0xf0000000000]
def dom_x2_0_x4_0 : Nat := 0xf0f00000f0f
def roots_x2_0_x4_0 : List Nat := [0xa0a00000a0a, 0xc0c00000c0c, 0xf0000000f00, 0xf0f00000000]
def dom_x2_0_x3_1 : Nat := 0xf000f000f000f00
def roots_x2_0_x3_1 : List Nat := [0xa000a000a000a00, 0xc000c000c000c00, 0xf0000000f000000, 0xf000f0000000000]
def dom_x2_0 : Nat := 0xf0f0f0f0f0f0f0f
def roots_x2_0 : List Nat := [0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000]
def dom_x3_1_x4_0 : Nat := 0xff000000ff00
def roots_x3_1_x4_0 : List Nat := [0xaa000000aa00, 0xcc000000cc00, 0xf0000000f000, 0xff0000000000]
def dom_x3_1_x5_0 : Nat := 0xff00ff00
def roots_x3_1_x5_0 : List Nat := [0xaa00aa00, 0xcc00cc00, 0xf000f000, 0xff000000]
def dom_x3_1 : Nat := 0xff00ff00ff00ff00
def roots_x3_1 : List Nat := [0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000]
def dom_x0_1 : Nat := 0xaaaaaaaaaaaaaaaa
def roots_x0_1 : List Nat := [0x8888888888888888, 0xa0a0a0a0a0a0a0a0, 0xaa00aa00aa00aa00, 0xaaaa0000aaaa0000, 0xaaaaaaaa00000000]
def dom_x0_0 : Nat := 0x5555555555555555
def roots_x0_0 : List Nat := [0x4444444444444444, 0x5050505050505050, 0x5500550055005500, 0x5555000055550000, 0x5555555500000000]
def dom_x3_0 : Nat := 0xff00ff00ff00ff
def roots_x3_0 : List Nat := [0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000]
def dom_x4_0 : Nat := 0xffff0000ffff
def roots_x4_0 : List Nat := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]
def dom_x5_0 : Nat := 0xffffffff
def roots_x5_0 : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]
def dom_x3_0_x4_0_x5_0 : Nat := 0xff
def roots_x3_0_x4_0_x5_0 : List Nat := [0xaa, 0xcc, 0xf0]
def dom_x3_1_x4_0_x5_0 : Nat := 0xff00
def roots_x3_1_x4_0_x5_0 : List Nat := [0xaa00, 0xcc00, 0xf000]

namespace S_x2_0_x4_1
def pairsG : List (Nat × Nat) := [(17, 19), (17, 25), (17, 49), (18, 19), (24, 25), (26, 27), (26, 58), (48, 49), (50, 51), (50, 58), (56, 57), (56, 58)]
def r1sG : List Nat := [17, 17, 17, 18, 24, 26, 26, 48, 50, 50, 56, 56]
def r2sG : List Nat := [19, 25, 49, 19, 25, 27, 58, 49, 51, 58, 57, 58]
def mpG : Nat := 0xfff
def pool6G : List Nat := [28661159440665, 28661260097811, 55049035846449, 55049539164435]
def xsM : List Nat := roots_x2_0_x4_1.map (· &&& dom_x2_0_x4_1)
def goalM : Nat := goal_all &&& dom_x2_0_x4_1
def NN : Nat → Nat
  | 4 => 5
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0xe7dbc970bce3f3408893c3164c61689a2d4927ce
  | 5, 0, 0 => 0x4c61689a
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xf0f0000000f0000000f0000030300000303000005050000050500000f0f0000000000000f0000000f0000000c0c00000c0c00000a0a00000a0a0000
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x646468c4447468846854
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x2_0_x4_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x2_0_x4_1 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x2_0_x4_1 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x2_0_x4_1 goalM u ys) : RunD dom_x2_0_x4_1 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x2_0_x4_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x2_0_x4_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 3 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_x2_0_x4_1 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x2_0_x4_1 roots_x2_0_x4_1 goal_all 6 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x2_0_x4_1 goal_all := by
    have h0 : isConstB dom_x2_0_x4_1 goal_all = false := by decide +kernel
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
end S_x2_0_x4_1
theorem low_x2_0_x4_1 : Lower dom_x2_0_x4_1 roots_x2_0_x4_1 goal_all 6 := S_x2_0_x4_1.noCircuit

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
    [(0x5555000000000000, 26, 58)] (by decide +kernel) (by decide +kernel) low_x0_0_x4_1_x5_1

namespace S_x1_0_x4_1_x5_0
def pairsG : List (Nat × Nat) := [(17, 21), (17, 25), (20, 21), (20, 28), (24, 25), (24, 28)]
def r1sG : List Nat := [17, 17, 20, 20, 24, 24]
def r2sG : List Nat := [21, 25, 21, 28, 25, 28]
def mpG : Nat := 0x3f
def pool6G : List Nat := [22063651494165]
def xsM : List Nat := roots_x1_0_x4_1_x5_0.map (· &&& dom_x1_0_x4_1_x5_0)
def goalM : Nat := goal_all &&& dom_x1_0_x4_1_x5_0
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xfb501748
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x3300000000000000303000000000000022220000
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x1_0_x4_1_x5_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x1_0_x4_1_x5_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x1_0_x4_1_x5_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x1_0_x4_1_x5_0 goalM u ys) : RunD dom_x1_0_x4_1_x5_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x1_0_x4_1_x5_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x1_0_x4_1_x5_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x1_0_x4_1_x5_0 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x1_0_x4_1_x5_0 roots_x1_0_x4_1_x5_0 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x1_0_x4_1_x5_0 goal_all := by
    have h0 : isConstB dom_x1_0_x4_1_x5_0 goal_all = false := by decide +kernel
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
end S_x1_0_x4_1_x5_0
theorem low_x1_0_x4_1_x5_0 : Lower dom_x1_0_x4_1_x5_0 roots_x1_0_x4_1_x5_0 goal_all 4 := S_x1_0_x4_1_x5_0.noCircuit

theorem low_x4_1_x5_0 : Lower dom_x4_1_x5_0 roots_x4_1_x5_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcccc0000, 17, 19)] (by decide +kernel) (by decide +kernel) low_x1_0_x4_1_x5_0

theorem low_x1_0_x4_1 : Lower dom_x1_0_x4_1 roots_x1_0_x4_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x3333000000000000, 17, 49)] (by decide +kernel) (by decide +kernel) low_x1_0_x4_1_x5_0

namespace S_x3_0_x4_1_x5_0
def pairsG : List (Nat × Nat) := [(17, 19), (17, 21), (18, 19), (18, 22), (20, 21), (20, 22)]
def r1sG : List Nat := [17, 17, 18, 18, 20, 20]
def r2sG : List Nat := [19, 21, 19, 22, 21, 22]
def mpG : Nat := 0x3f
def pool6G : List Nat := [19864560735507]
def xsM : List Nat := roots_x3_0_x4_1_x5_0.map (· &&& dom_x3_0_x4_1_x5_0)
def goalM : Nat := goal_all &&& dom_x3_0_x4_1_x5_0
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x1a967a91
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xf000000000000000cc00000000000000aa0000
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x3_0_x4_1_x5_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x3_0_x4_1_x5_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x3_0_x4_1_x5_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x3_0_x4_1_x5_0 goalM u ys) : RunD dom_x3_0_x4_1_x5_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x3_0_x4_1_x5_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x3_0_x4_1_x5_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x3_0_x4_1_x5_0 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x3_0_x4_1_x5_0 roots_x3_0_x4_1_x5_0 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x3_0_x4_1_x5_0 goal_all := by
    have h0 : isConstB dom_x3_0_x4_1_x5_0 goal_all = false := by decide +kernel
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
end S_x3_0_x4_1_x5_0
theorem low_x3_0_x4_1_x5_0 : Lower dom_x3_0_x4_1_x5_0 roots_x3_0_x4_1_x5_0 goal_all 4 := S_x3_0_x4_1_x5_0.noCircuit

theorem low_x4_1_x5_1 : Lower dom_x4_1_x5_1 roots_x4_1_x5_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa000000000000, 48, 49)] (by decide +kernel) (by decide +kernel) low_x0_0_x4_1_x5_1

theorem low_x3_0_x4_1 : Lower dom_x3_0_x4_1 roots_x3_0_x4_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff000000000000, 17, 49)] (by decide +kernel) (by decide +kernel) low_x3_0_x4_1_x5_0

namespace S_x4_1
def pairsG : List (Nat × Nat) := [(17, 19), (17, 21), (17, 25), (17, 49), (18, 19), (18, 22), (20, 21), (20, 22), (20, 28), (24, 25), (24, 28), (26, 27), (26, 30), (26, 58), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [17, 17, 17, 17, 18, 18, 20, 20, 20, 24, 24, 26, 26, 26, 48, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [19, 21, 25, 49, 19, 22, 21, 22, 28, 25, 28, 27, 30, 58, 49, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0xffffff
def pool6G : List Nat := [61646105613105, 28661159432985, 57248461166101, 55049035846449, 28661260097811, 57248562420758]
def xsM : List Nat := roots_x4_1.map (· &&& dom_x4_1)
def goalM : Nat := goal_all &&& dom_x4_1
def NN : Nat → Nat
  | 5 => 3
  | 6 => 7
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x9117bc2c712aa9a91066b989
  | 6, 0, 0 => 0xefd062d2cf84214ec8a6a23caf970ecb6dc8fddb3c805a533048116e
  | 7, 0, 0 => 0x6eb47690
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xffff0000ffcc0000ffcc0000ffaa0000ffaa0000eeee0000eeee0000aaaa0000aaaa0000cccc0000cccc000000ff000000ff0000ffff000000000000ff000000ff000000f0f00000f0f0000055550000555500003333000033330000
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x432105426155427055
  | 6, 0, 0 => 0x4a3267604327054328676042675503267b549326760432615
  | 7, 0, 0 => 0x432675
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
  | 0 => 0x3fff0000000000e3be300000000000e03e0f000000000003b83f000000000000000f000000000003b83000000000001fc1ff0000000000ffc0000000000000e03e0000000000001c01c00000000000fffff00000000000fc47cf
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x1ff70000000000fbbfb50000000000f6ff5f00000000006ffaff000000000024ca5f00000000004bb8b100000000000dc0fb0000000000ffe0080000000000f23f0400000000009d15e20000000000db35a00000000000b4474e
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 12 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 12 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 12 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 12 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 12 then wireAt i else 0
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
  | 5 => 8
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xef9bbf8ea3bb6eb583ce5c327327a10b704cc23142004b420f88d211047f5ed5
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x28400000000610000000028400000000e10000000008400000000e100000000184000000002100
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 4 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_x2_0_x4_1 roots_x2_0_x4_1 6 s ws hint
  | 1 => checkCutEntry dom_x0_0_x4_1_x5_1 roots_x0_0_x4_1_x5_1 4 s ws hint
  | 2 => checkCutEntry dom_x0_0_x4_1 roots_x0_0_x4_1 5 s ws hint
  | 3 => checkCutEntry dom_x4_1_x5_0 roots_x4_1_x5_0 5 s ws hint
  | 4 => checkCutEntry dom_x1_0_x4_1_x5_0 roots_x1_0_x4_1_x5_0 4 s ws hint
  | 5 => checkCutEntry dom_x1_0_x4_1 roots_x1_0_x4_1 5 s ws hint
  | 6 => checkCutEntry dom_x3_0_x4_1_x5_0 roots_x3_0_x4_1_x5_0 4 s ws hint
  | 7 => checkCutEntry dom_x4_1_x5_1 roots_x4_1_x5_1 5 s ws hint
  | 8 => checkCutEntry dom_x3_0_x4_1 roots_x3_0_x4_1 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x4_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x4_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x4_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x4_1 _ hc
  · contradiction
def p0Subs : List Nat := [0, 2, 5, 3, 7, 8, 1, 4, 6]
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)) ||
  p0Subs.any (fun k => checkCutByIdx s ws k)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x4_1 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq, Bool.or_eq_true] at h; rcases h with h1 | h0
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2
  · obtain ⟨k, _, hk⟩ := List.any_eq_true.1 h0; exact checkCutByIdx_sound hk
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x4_1 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x4_1 goalM u ys) : RunD dom_x4_1 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x4_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 7 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 7 0 = true)
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
def RootG (s : Nat) : Bool := scr dom_x4_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_x4_1 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x4_1 roots_x4_1 goal_all 8 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x4_1 goal_all := by
    have h0 : isConstB dom_x4_1 goal_all = false := by decide +kernel
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
end S_x4_1
theorem low_x4_1 : Lower dom_x4_1 roots_x4_1 goal_all 8 := S_x4_1.noCircuit

namespace S_x1_0_x5_1
def pairsG : List (Nat × Nat) := [(33, 37), (33, 41), (33, 49), (36, 37), (40, 41), (44, 45), (44, 60), (48, 49), (52, 53), (52, 60), (56, 57), (56, 60)]
def r1sG : List Nat := [33, 33, 33, 36, 40, 44, 44, 48, 52, 52, 56, 56]
def r2sG : List Nat := [37, 41, 49, 37, 41, 45, 60, 49, 53, 60, 57, 60]
def mpG : Nat := 0xfff
def pool6G : List Nat := [48521121902889, 48521189009701, 57317080704305, 57317282031909]
def xsM : List Nat := roots_x1_0_x5_1.map (· &&& dom_x1_0_x5_1)
def goalM : Nat := goal_all &&& dom_x1_0_x5_1
def NN : Nat → Nat
  | 4 => 5
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0xdaa29e0ed9246cde51b2e97e404f366434576818
  | 5, 0, 0 => 0x404f3664
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x3333000000000033003300000000030303030000000011111111000000003333000000000000330033000000000030303030000000002222222200000000
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x646468544474688468c4
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x1_0_x5_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x1_0_x5_1 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x1_0_x5_1 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x1_0_x5_1 goalM u ys) : RunD dom_x1_0_x5_1 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x1_0_x5_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x1_0_x5_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 3 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_x1_0_x5_1 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x1_0_x5_1 roots_x1_0_x5_1 goal_all 6 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x1_0_x5_1 goal_all := by
    have h0 : isConstB dom_x1_0_x5_1 goal_all = false := by decide +kernel
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
end S_x1_0_x5_1
theorem low_x1_0_x5_1 : Lower dom_x1_0_x5_1 roots_x1_0_x5_1 goal_all 6 := S_x1_0_x5_1.noCircuit

theorem low_x0_0_x5_1 : Lower dom_x0_0_x5_1 roots_x0_0_x5_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5555000000000000, 44, 60)] (by decide +kernel) (by decide +kernel) low_x0_0_x4_1_x5_1

namespace S_x2_0_x4_0_x5_1
def pairsG : List (Nat × Nat) := [(33, 35), (33, 41), (34, 35), (34, 42), (40, 41), (40, 42)]
def r1sG : List Nat := [33, 33, 34, 34, 40, 40]
def r2sG : List Nat := [35, 41, 35, 42, 41, 42]
def mpG : Nat := 0x3f
def pool6G : List Nat := [37525803116835]
def xsM : List Nat := roots_x2_0_x4_0_x5_1.map (· &&& dom_x2_0_x4_0_x5_1)
def goalM : Nat := goal_all &&& dom_x2_0_x4_0_x5_1
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x2977382d
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xf000000000000000c0c0000000000000a0a00000000
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x2_0_x4_0_x5_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x2_0_x4_0_x5_1 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x2_0_x4_0_x5_1 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x2_0_x4_0_x5_1 goalM u ys) : RunD dom_x2_0_x4_0_x5_1 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x2_0_x4_0_x5_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x2_0_x4_0_x5_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x2_0_x4_0_x5_1 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x2_0_x4_0_x5_1 roots_x2_0_x4_0_x5_1 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x2_0_x4_0_x5_1 goal_all := by
    have h0 : isConstB dom_x2_0_x4_0_x5_1 goal_all = false := by decide +kernel
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
end S_x2_0_x4_0_x5_1
theorem low_x2_0_x4_0_x5_1 : Lower dom_x2_0_x4_0_x5_1 roots_x2_0_x4_0_x5_1 goal_all 4 := S_x2_0_x4_0_x5_1.noCircuit

theorem low_x4_0_x5_1 : Lower dom_x4_0_x5_1 roots_x4_0_x5_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f000000000, 33, 37)] (by decide +kernel) (by decide +kernel) low_x2_0_x4_0_x5_1

theorem low_x2_0_x5_1 : Lower dom_x2_0_x5_1 roots_x2_0_x5_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f000000000000, 33, 49)] (by decide +kernel) (by decide +kernel) low_x2_0_x4_0_x5_1

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

namespace S_x5_1
def pairsG : List (Nat × Nat) := [(33, 35), (33, 37), (33, 41), (33, 49), (34, 35), (34, 38), (34, 42), (36, 37), (36, 38), (40, 41), (40, 42), (44, 45), (44, 46), (44, 60), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [33, 33, 33, 33, 34, 34, 34, 36, 36, 40, 40, 44, 44, 44, 48, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [35, 37, 41, 49, 35, 38, 42, 37, 38, 41, 42, 45, 46, 60, 49, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0xffffff
def pool6G : List Nat := [61715127215409, 48521121899817, 55118056006947, 57317080704305, 55118258776614, 48521189009701, 55118190945827]
def xsM : List Nat := roots_x5_1.map (· &&& dom_x5_1)
def goalM : Nat := goal_all &&& dom_x5_1
def NN : Nat → Nat
  | 5 => 3
  | 6 => 7
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xd129852f9679e0100854d8be
  | 6, 0, 0 => 0xc5ee96e7b433ea05a716f0c18ec3435845025efc3bd8c2aa009e3c06
  | 7, 0, 0 => 0xbe37fa2f
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xffff00000000fff0fff000000000ffaaffaa00000000fafafafa00000000aaaaaaaa00000000f0f0f0f00000000000ff00ff00000000ffff000000000000ff00ff0000000000cccccccc0000000055555555000000000f0f0f0f00000000
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x427055462155432105
  | 6, 0, 0 => 0x43621503627b5493627604627554a3627643862760432705
  | 7, 0, 0 => 0x436275
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
  | 0 => 0x3fff0000000000fc3f800000000000e03e0f00000000001c398f000000000000000f00000000001c398000000000001fc1ff0000000000ffc0000000000000e03e0000000000000380700000000000fffff00000000000e3c67f
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x1ff70000000000ff3fe60000000000f6fedf0000000000bdfbbf000000000024ca9f00000000009d39a200000000000dc1bb0000000000ffe0080000000000f23e4400000000004b95710000000000db3560000000000062c65d
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 12 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 12 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 12 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 12 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 12 then wireAt i else 0
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
  | 5 => 8
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xdbed3bd2cf2b795aca328ef0a4c1e84379885aa941067208169ce0f10656cce9
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x8400000000a10000000038400000000a100000000384000000006100000000184000000002100
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 4 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_x1_0_x5_1 roots_x1_0_x5_1 6 s ws hint
  | 1 => checkCutEntry dom_x0_0_x4_1_x5_1 roots_x0_0_x4_1_x5_1 4 s ws hint
  | 2 => checkCutEntry dom_x0_0_x5_1 roots_x0_0_x5_1 5 s ws hint
  | 3 => checkCutEntry dom_x4_0_x5_1 roots_x4_0_x5_1 5 s ws hint
  | 4 => checkCutEntry dom_x2_0_x4_0_x5_1 roots_x2_0_x4_0_x5_1 4 s ws hint
  | 5 => checkCutEntry dom_x2_0_x5_1 roots_x2_0_x5_1 5 s ws hint
  | 6 => checkCutEntry dom_x3_0_x4_0_x5_1 roots_x3_0_x4_0_x5_1 4 s ws hint
  | 7 => checkCutEntry dom_x4_1_x5_1 roots_x4_1_x5_1 5 s ws hint
  | 8 => checkCutEntry dom_x3_0_x5_1 roots_x3_0_x5_1 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x5_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x4_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x4_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x5_1 _ hc
  · contradiction
def p0Subs : List Nat := [0, 2, 5, 3, 7, 8, 1, 4, 6]
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
private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 7 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 7 0 = true)
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

namespace S_x0_1_x1_0_x2_0
def pairsG : List (Nat × Nat) := [(9, 25), (9, 41), (17, 25), (17, 49), (33, 41), (33, 49)]
def r1sG : List Nat := [9, 9, 17, 17, 33, 33]
def r2sG : List Nat := [25, 41, 25, 49, 41, 49]
def mpG : Nat := 0x3f
def pool6G : List Nat := [18730909247769]
def xsM : List Nat := roots_x0_1_x1_0_x2_0.map (· &&& dom_x0_1_x1_0_x2_0)
def goalM : Nat := goal_all &&& dom_x0_1_x1_0_x2_0
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xe9d5d613
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x20202020000000002020000020200000200020002000200
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x0_1_x1_0_x2_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x0_1_x1_0_x2_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x0_1_x1_0_x2_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x0_1_x1_0_x2_0 goalM u ys) : RunD dom_x0_1_x1_0_x2_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x0_1_x1_0_x2_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x0_1_x1_0_x2_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x0_1_x1_0_x2_0 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x0_1_x1_0_x2_0 roots_x0_1_x1_0_x2_0 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x0_1_x1_0_x2_0 goal_all := by
    have h0 : isConstB dom_x0_1_x1_0_x2_0 goal_all = false := by decide +kernel
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
end S_x0_1_x1_0_x2_0
theorem low_x0_1_x1_0_x2_0 : Lower dom_x0_1_x1_0_x2_0 roots_x0_1_x1_0_x2_0 goal_all 4 := S_x0_1_x1_0_x2_0.noCircuit

theorem low_x0_1_x1_0 : Lower dom_x0_1_x1_0 roots_x0_1_x1_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x2020202020202020, 1, 5)] (by decide +kernel) (by decide +kernel) low_x0_1_x1_0_x2_0

namespace S_x1_0_x3_1_x5_0
def pairsG : List (Nat × Nat) := [(9, 13), (9, 25), (12, 13), (12, 28), (24, 25), (24, 28)]
def r1sG : List Nat := [9, 9, 12, 12, 24, 24]
def r2sG : List Nat := [13, 25, 13, 28, 25, 28]
def mpG : Nat := 0x3f
def pool6G : List Nat := [13233198733581]
def xsM : List Nat := roots_x1_0_x3_1_x5_0.map (· &&& dom_x1_0_x3_1_x5_0)
def goalM : Nat := goal_all &&& dom_x1_0_x3_1_x5_0
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xa3e95fe9
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x3300000000000000300030000000000022002200
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x1_0_x3_1_x5_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x1_0_x3_1_x5_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x1_0_x3_1_x5_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x1_0_x3_1_x5_0 goalM u ys) : RunD dom_x1_0_x3_1_x5_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x1_0_x3_1_x5_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x1_0_x3_1_x5_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x1_0_x3_1_x5_0 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x1_0_x3_1_x5_0 roots_x1_0_x3_1_x5_0 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x1_0_x3_1_x5_0 goal_all := by
    have h0 : isConstB dom_x1_0_x3_1_x5_0 goal_all = false := by decide +kernel
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
end S_x1_0_x3_1_x5_0
theorem low_x1_0_x3_1_x5_0 : Lower dom_x1_0_x3_1_x5_0 roots_x1_0_x3_1_x5_0 goal_all 4 := S_x1_0_x3_1_x5_0.noCircuit

theorem low_x1_0_x5_0 : Lower dom_x1_0_x5_0 roots_x1_0_x5_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x33003300, 17, 25)] (by decide +kernel) (by decide +kernel) low_x1_0_x3_1_x5_0

theorem low_x1_0_x2_0 : Lower dom_x1_0_x2_0 roots_x1_0_x2_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x202020202020202, 24, 25)] (by decide +kernel) (by decide +kernel) low_x0_1_x1_0_x2_0

theorem low_x1_0_x3_1 : Lower dom_x1_0_x3_1 roots_x1_0_x3_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x3300330000000000, 9, 41)] (by decide +kernel) (by decide +kernel) low_x1_0_x3_1_x5_0

namespace S_x1_0
def pairsG : List (Nat × Nat) := [(1, 5), (4, 5), (9, 13), (9, 25), (9, 41), (12, 13), (12, 28), (17, 21), (17, 25), (17, 49), (20, 21), (20, 28), (24, 25), (24, 28), (33, 37), (33, 41), (33, 49), (36, 37), (40, 41), (44, 45), (44, 60), (48, 49), (52, 53), (52, 60), (56, 57), (56, 60)]
def r1sG : List Nat := [1, 4, 9, 9, 9, 12, 12, 17, 17, 17, 20, 20, 24, 24, 33, 33, 33, 36, 40, 44, 44, 48, 52, 52, 56, 56]
def r2sG : List Nat := [5, 5, 13, 25, 41, 13, 28, 21, 25, 49, 21, 28, 25, 28, 37, 41, 49, 37, 41, 45, 60, 49, 53, 60, 57, 60]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [48418107693317, 18730909247769, 48521119794473, 61796276307228, 57317078598961, 48418109070341, 61761782351132, 57214201568261, 48452467431685, 48521186908421]
def xsM : List Nat := roots_x1_0.map (· &&& dom_x1_0)
def goalM : Nat := goal_all &&& dom_x1_0
def NN : Nat → Nat
  | 5 => 5
  | 6 => 8
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xf71871dff68c5e80af7648c1aeea356244417414
  | 6, 0, 0 => 0xe3c1d732e335c3d3dda09adcd3b212568cff9f0a788d0285755479d430ead967
  | 7, 0, 0 => 0x653667d8
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x3300000033000000222222220000000022220000222200002200220022002200222222222222222203030303030303033300330033003300000033330000333333333333000000003333000033330000303030303030303011111111111111110033003300330033
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x462155468755432105438705428055
  | 6, 0, 0 => 0x436215043687543628a64362896436c286046285503628b50432805
  | 7, 0, 0 => 0x436285
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
  | 0 => 0x3003000000000000001c0000000000000000380000000000000001c000000000001c39d000000000325f39d00000000031c307c00000000001fc07f0000000003ffc0000000000003e03f800000000000da0c620000000003fe3c620000000000e3cf83
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x390394800000000016fc210000000000161178800000000010c913c00000000016fd7bf000000000125931800000000039cb97c00000000000ec0370000000003ffc2100000000003f13fc80000000002da6ce700000000029028400000000000634683
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 13 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 13 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 13 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 13 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 13 then wireAt i else 0
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
  | 5 => 8
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xfdda1512f6b9c127f62dadc892a540658b84ec7a4b03174743e2c35c1be96057
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x8400000000210000000018400000000e10000000038400000000a100000000284000000002100
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 4 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_x1_0_x5_1 roots_x1_0_x5_1 6 s ws hint
  | 1 => checkCutEntry dom_x0_1_x1_0_x2_0 roots_x0_1_x1_0_x2_0 4 s ws hint
  | 2 => checkCutEntry dom_x0_1_x1_0 roots_x0_1_x1_0 5 s ws hint
  | 3 => checkCutEntry dom_x1_0_x5_0 roots_x1_0_x5_0 5 s ws hint
  | 4 => checkCutEntry dom_x1_0_x3_1_x5_0 roots_x1_0_x3_1_x5_0 4 s ws hint
  | 5 => checkCutEntry dom_x1_0_x4_1_x5_0 roots_x1_0_x4_1_x5_0 4 s ws hint
  | 6 => checkCutEntry dom_x1_0_x2_0 roots_x1_0_x2_0 5 s ws hint
  | 7 => checkCutEntry dom_x1_0_x3_1 roots_x1_0_x3_1 5 s ws hint
  | 8 => checkCutEntry dom_x1_0_x4_1 roots_x1_0_x4_1 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x1_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_1_x1_0_x2_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_1_x1_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x3_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x4_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x2_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x3_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x4_1 _ hc
  · contradiction
def p0Subs : List Nat := [0, 2, 6, 7, 1, 8, 3, 4, 5]
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
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 5 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 0 = true)
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

theorem low_x0_1_x2_0 : Lower dom_x0_1_x2_0 roots_x0_1_x2_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x808080808080808, 1, 3)] (by decide +kernel) (by decide +kernel) low_x0_1_x1_0_x2_0

namespace S_x2_0_x3_1_x4_0
def pairsG : List (Nat × Nat) := [(9, 11), (9, 41), (10, 11), (10, 42), (40, 41), (40, 42)]
def r1sG : List Nat := [9, 9, 10, 10, 40, 40]
def r2sG : List Nat := [11, 41, 11, 42, 41, 42]
def mpG : Nat := 0x3f
def pool6G : List Nat := [11034444835083]
def xsM : List Nat := roots_x2_0_x3_1_x4_0.map (· &&& dom_x2_0_x3_1_x4_0)
def goalM : Nat := goal_all &&& dom_x2_0_x3_1_x4_0
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xe377bddf
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xf000000000000000c0000000c0000000a0000000a00
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x2_0_x3_1_x4_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x2_0_x3_1_x4_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x2_0_x3_1_x4_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x2_0_x3_1_x4_0 goalM u ys) : RunD dom_x2_0_x3_1_x4_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x2_0_x3_1_x4_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x2_0_x3_1_x4_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x2_0_x3_1_x4_0 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x2_0_x3_1_x4_0 roots_x2_0_x3_1_x4_0 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x2_0_x3_1_x4_0 goal_all := by
    have h0 : isConstB dom_x2_0_x3_1_x4_0 goal_all = false := by decide +kernel
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
end S_x2_0_x3_1_x4_0
theorem low_x2_0_x3_1_x4_0 : Lower dom_x2_0_x3_1_x4_0 roots_x2_0_x3_1_x4_0 goal_all 4 := S_x2_0_x3_1_x4_0.noCircuit

theorem low_x2_0_x4_0 : Lower dom_x2_0_x4_0 roots_x2_0_x4_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0000000f00, 33, 41)] (by decide +kernel) (by decide +kernel) low_x2_0_x3_1_x4_0

theorem low_x2_0_x3_1 : Lower dom_x2_0_x3_1 roots_x2_0_x3_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0000000f000000, 9, 25)] (by decide +kernel) (by decide +kernel) low_x2_0_x3_1_x4_0

namespace S_x2_0
def pairsG : List (Nat × Nat) := [(1, 3), (2, 3), (9, 11), (9, 25), (9, 41), (10, 11), (10, 42), (17, 19), (17, 25), (17, 49), (18, 19), (24, 25), (26, 27), (26, 58), (33, 35), (33, 41), (33, 49), (34, 35), (34, 42), (40, 41), (40, 42), (48, 49), (50, 51), (50, 58), (56, 57), (56, 58)]
def r1sG : List Nat := [1, 2, 9, 9, 9, 10, 10, 17, 17, 17, 18, 24, 26, 26, 33, 33, 33, 34, 34, 40, 40, 48, 50, 50, 56, 56]
def r2sG : List Nat := [3, 3, 11, 25, 41, 11, 42, 19, 25, 49, 19, 25, 27, 58, 35, 41, 49, 35, 42, 41, 42, 49, 51, 58, 57, 58]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [28626899314947, 18730909247769, 28661259049219, 55049034793777, 28626899773955, 61684473987882, 61611744822057, 36396495149315]
def xsM : List Nat := roots_x2_0.map (· &&& dom_x2_0)
def goalM : Nat := goal_all &&& dom_x2_0
def NN : Nat → Nat
  | 5 => 5
  | 6 => 8
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xf0dd32ccddc13115bb78fa15518fca972f479397
  | 6, 0, 0 => 0xe292339dcf7e460e9113e54389a9dbc06ecbae436cb2dc485bafac8c43cbfcf3
  | 7, 0, 0 => 0xf0260ba
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xf000f00000000000a0a0a0a000000000a0a00000a0a00000a000a000a000a000a0a0a0a0a0a0a0a03030303030303030f000f000f000f00000000000f0f0f0f0f0f0f0f000000000f0f00000f0f00000c0c0c0c0c0c0c0c0505050505050505000f000f000f000f
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x328055438705368755432105362155
  | 6, 0, 0 => 0x4628a50436215043280543628b60362855436c28604368754362896
  | 7, 0, 0 => 0x436285
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
  | 0 => 0x3180000000000000001c0000000000000000380000000000000001c000000000001c39d000000000339cb9d000000000318387c0000000000003fff0000000003ffc0000000000003e03f800000000000c634620000000003fe3c620000000000e7c783
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x39ca05000000000016bc2100000000001611f88000000000108993c00000000016bdfbf0000000001298b1800000000039cb97c0000000000001daf0000000003ffe2500000000003e13f880000000002d674e700000000029420400000000000634683
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 13 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 13 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 13 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 13 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 13 then wireAt i else 0
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
  | 5 => 8
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xd83b7632a576a76f6f4330c9670c46a444c40fa431a80ded30d8cffe0e9098fe
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x8400000000210000000008400000000a10000000038400000000610000000028400000000e100
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 4 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_x2_0_x4_1 roots_x2_0_x4_1 6 s ws hint
  | 1 => checkCutEntry dom_x0_1_x1_0_x2_0 roots_x0_1_x1_0_x2_0 4 s ws hint
  | 2 => checkCutEntry dom_x0_1_x2_0 roots_x0_1_x2_0 5 s ws hint
  | 3 => checkCutEntry dom_x2_0_x4_0 roots_x2_0_x4_0 5 s ws hint
  | 4 => checkCutEntry dom_x2_0_x3_1_x4_0 roots_x2_0_x3_1_x4_0 4 s ws hint
  | 5 => checkCutEntry dom_x2_0_x4_0_x5_1 roots_x2_0_x4_0_x5_1 4 s ws hint
  | 6 => checkCutEntry dom_x1_0_x2_0 roots_x1_0_x2_0 5 s ws hint
  | 7 => checkCutEntry dom_x2_0_x3_1 roots_x2_0_x3_1 5 s ws hint
  | 8 => checkCutEntry dom_x2_0_x5_1 roots_x2_0_x5_1 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x2_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_1_x1_0_x2_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_1_x2_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x3_1_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x4_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x2_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x3_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x5_1 _ hc
  · contradiction
def p0Subs : List Nat := [0, 2, 6, 7, 1, 8, 3, 4, 5]
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)) ||
  p0Subs.any (fun k => checkCutByIdx s ws k)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x2_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq, Bool.or_eq_true] at h; rcases h with h1 | h0
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2
  · obtain ⟨k, _, hk⟩ := List.any_eq_true.1 h0; exact checkCutByIdx_sound hk
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
private theorem z5 : ∀ i, 0 ≤ i → i < 5 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 0 = true)
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
def RootG (s : Nat) : Bool := scr dom_x2_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_x2_0 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x2_0 roots_x2_0 goal_all 8 := by
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
theorem low_x2_0 : Lower dom_x2_0 roots_x2_0 goal_all 8 := S_x2_0.noCircuit

theorem low_x3_1_x4_0 : Lower dom_x3_1_x4_0 roots_x3_1_x4_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0000000f000, 9, 13)] (by decide +kernel) (by decide +kernel) low_x2_0_x3_1_x4_0

theorem low_x3_1_x5_0 : Lower dom_x3_1_x5_0 roots_x3_1_x5_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc00cc00, 9, 11)] (by decide +kernel) (by decide +kernel) low_x1_0_x3_1_x5_0

namespace S_x3_1
def pairsG : List (Nat × Nat) := [(9, 11), (9, 13), (9, 25), (9, 41), (10, 11), (10, 14), (10, 42), (12, 13), (12, 14), (12, 28), (24, 25), (24, 28), (26, 27), (26, 30), (26, 58), (40, 41), (40, 42), (44, 45), (44, 46), (44, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [9, 9, 9, 9, 10, 10, 10, 12, 12, 12, 24, 24, 26, 26, 26, 40, 40, 44, 44, 44, 56, 56, 56]
def r2sG : List Nat := [11, 13, 25, 41, 11, 14, 42, 13, 14, 28, 25, 28, 27, 30, 58, 41, 42, 45, 46, 60, 57, 58, 60]
def mpG : Nat := 0x7fffff
def pool6G : List Nat := [28626696146187, 48490333408540, 48490334456618, 28626697063705, 48417603455757]
def xsM : List Nat := roots_x3_1.map (· &&& dom_x3_1)
def goalM : Nat := goal_all &&& dom_x3_1
def NN : Nat → Nat
  | 5 => 1
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x6cd6aa0
  | 6, 0, 0 => 0xd9129671
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xaa00aa00aa00aa00ff00ff0000000000ff000000ff000000f000f000f000f000cc00cc00cc00cc005500550055005500
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x46885
  | 6, 0, 0 => 0x468d5
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 19
  | 6 => 19
  | _ => 0
def stateM : Nat → Nat
  | 5 => 0x7ffff
  | 6 => 0x7ffff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0xf00000000007f80000000000000707c0000000000000e0380000000000000707000000000007ffff0
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x12949f00000000007fc0480000000000787e0400000000004e2ba2000000000025717100000000006d6b60
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 6 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 6 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 6 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 6 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 6 then wireAt i else 0
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
  | 0 => checkCutEntry dom_x1_0_x3_1 roots_x1_0_x3_1 5 s ws hint
  | 1 => checkCutEntry dom_x2_0_x3_1 roots_x2_0_x3_1 5 s ws hint
  | 2 => checkCutEntry dom_x3_1_x4_0 roots_x3_1_x4_0 5 s ws hint
  | 3 => checkCutEntry dom_x3_1_x5_0 roots_x3_1_x5_0 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x3_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x3_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x3_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_1_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_1_x5_0 _ hc
  · contradiction
def p0Subs : List Nat := [0, 1, 2, 3]
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)) ||
  p0Subs.any (fun k => checkCutByIdx s ws k)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x3_1 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq, Bool.or_eq_true] at h; rcases h with h1 | h0
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2
  · obtain ⟨k, _, hk⟩ := List.any_eq_true.1 h0; exact checkCutByIdx_sound hk
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x3_1 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x3_1 goalM u ys) : RunD dom_x3_1 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x3_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
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
def RootG (s : Nat) : Bool := scr dom_x3_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_x3_1 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x3_1 roots_x3_1 goal_all 7 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x3_1 goal_all := by
    have h0 : isConstB dom_x3_1 goal_all = false := by decide +kernel
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
end S_x3_1
theorem low_x3_1 : Lower dom_x3_1 roots_x3_1 goal_all 7 := S_x3_1.noCircuit

theorem low_x0_1 : Lower dom_x0_1 roots_x0_1 goal_all 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x8888888888888888, 1, 3)] (by decide +kernel) (by decide +kernel) low_x0_1_x1_0

theorem low_x0_0 : Lower dom_x0_0 roots_x0_0 goal_all 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5555000055550000, 12, 28)] (by decide +kernel) (by decide +kernel) low_x0_0_x4_1

theorem low_x3_0 : Lower dom_x3_0 roots_x3_0 goal_all 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff000000ff0000, 33, 49)] (by decide +kernel) (by decide +kernel) low_x3_0_x4_1

theorem low_x4_0 : Lower dom_x4_0 roots_x4_0 goal_all 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f00000f0f0, 1, 5)] (by decide +kernel) (by decide +kernel) low_x2_0_x4_0

theorem low_x5_0 : Lower dom_x5_0 roots_x5_0 goal_all 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcccccccc, 1, 3)] (by decide +kernel) (by decide +kernel) low_x1_0_x5_0

namespace S_x3_0_x4_0_x5_0
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (2, 3), (2, 6), (4, 5), (4, 6)]
def r1sG : List Nat := [1, 1, 2, 2, 4, 4]
def r2sG : List Nat := [3, 5, 3, 6, 5, 6]
def mpG : Nat := 0x3f
def pool6G : List Nat := [2203385726211]
def xsM : List Nat := roots_x3_0_x4_0_x5_0.map (· &&& dom_x3_0_x4_0_x5_0)
def goalM : Nat := goal_all &&& dom_x3_0_x4_0_x5_0
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xd4bda944
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xf000000000000000cc00000000000000aa
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x3_0_x4_0_x5_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x3_0_x4_0_x5_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x3_0_x4_0_x5_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x3_0_x4_0_x5_0 goalM u ys) : RunD dom_x3_0_x4_0_x5_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x3_0_x4_0_x5_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x3_0_x4_0_x5_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x3_0_x4_0_x5_0 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x3_0_x4_0_x5_0 roots_x3_0_x4_0_x5_0 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x3_0_x4_0_x5_0 goal_all := by
    have h0 : isConstB dom_x3_0_x4_0_x5_0 goal_all = false := by decide +kernel
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
end S_x3_0_x4_0_x5_0
theorem low_x3_0_x4_0_x5_0 : Lower dom_x3_0_x4_0_x5_0 roots_x3_0_x4_0_x5_0 goal_all 4 := S_x3_0_x4_0_x5_0.noCircuit

namespace S_x3_1_x4_0_x5_0
def pairsG : List (Nat × Nat) := [(9, 11), (9, 13), (10, 11), (10, 14), (12, 13), (12, 14)]
def r1sG : List Nat := [9, 9, 10, 10, 12, 12]
def r2sG : List Nat := [11, 13, 11, 14, 13, 14]
def mpG : Nat := 0x3f
def pool6G : List Nat := [11033973230859]
def xsM : List Nat := roots_x3_1_x4_0_x5_0.map (· &&& dom_x3_1_x4_0_x5_0)
def goalM : Nat := goal_all &&& dom_x3_1_x4_0_x5_0
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xd8484119
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xf000000000000000cc00000000000000aa00
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x3_1_x4_0_x5_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x3_1_x4_0_x5_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x3_1_x4_0_x5_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x3_1_x4_0_x5_0 goalM u ys) : RunD dom_x3_1_x4_0_x5_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x3_1_x4_0_x5_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x3_1_x4_0_x5_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x3_1_x4_0_x5_0 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x3_1_x4_0_x5_0 roots_x3_1_x4_0_x5_0 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x3_1_x4_0_x5_0 goal_all := by
    have h0 : isConstB dom_x3_1_x4_0_x5_0 goal_all = false := by decide +kernel
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
end S_x3_1_x4_0_x5_0
theorem low_x3_1_x4_0_x5_0 : Lower dom_x3_1_x4_0_x5_0 roots_x3_1_x4_0_x5_0 goal_all 4 := S_x3_1_x4_0_x5_0.noCircuit

namespace S_63
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (2, 3), (2, 6), (4, 5), (4, 6), (9, 11), (9, 13), (9, 25), (9, 41), (10, 11), (10, 14), (10, 42), (12, 13), (12, 14), (12, 28), (17, 19), (17, 21), (17, 25), (17, 49), (18, 19), (18, 22), (20, 21), (20, 22), (20, 28), (24, 25), (24, 28), (26, 27), (26, 30), (26, 58), (33, 35), (33, 37), (33, 41), (33, 49), (34, 35), (34, 38), (34, 42), (36, 37), (36, 38), (40, 41), (40, 42), (44, 45), (44, 46), (44, 60), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [1, 1, 2, 2, 4, 4, 9, 9, 9, 9, 10, 10, 10, 12, 12, 12, 17, 17, 17, 17, 18, 18, 20, 20, 20, 24, 24, 26, 26, 26, 33, 33, 33, 33, 34, 34, 34, 36, 36, 40, 40, 44, 44, 44, 48, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [3, 5, 3, 6, 5, 6, 11, 13, 25, 41, 11, 14, 42, 13, 14, 28, 19, 21, 25, 49, 19, 22, 21, 22, 28, 25, 28, 27, 30, 58, 35, 37, 41, 49, 35, 38, 42, 37, 38, 41, 42, 45, 46, 60, 49, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0x3fffffffffffff
def pool6G : List Nat := [55049468642563, 18730909247769, 55049034793777, 57317078598961, 61611744822057, 48491123055622, 48521119794473, 48490333406492, 61684608729898, 48521186908421, 57287115408924, 28661191017753, 36322826852649, 48490334454570, 61762186577180, 28661259053315, 55165116285738, 57286560646428, 28661158380313, 48521087625769, 61612045894937, 48490332095260, 61761782350620, 48490332095274, 61684473988394, 28661192394243, 48417604376837, 28626697988355, 57248458343173, 28661192399897]
def xsM : List Nat := roots_63.map (· &&& dom_63)
def goalM : Nat := goal_all &&& dom_63
def NN : Nat → Nat
  | 5 => 2
  | 6 => 89
  | 7 => 416
  | 8 => 238
  | 9 => 23
  | 10 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x205263b20361b21d
  | 6, 0, 0 => 0xb5a82bdcb03ca86dae167fd3ade9db15a67fe469a4a10bd29d13f6189c9d873e96ca698896053d6d941e120c941965bf8fab7dc78c15e12b8a65e23c833bb76a7f58e0277c2cfebf7b3832d67a2fddfc77a096e077837e86746fb46d74297a2b6ff0f0146e6536ae692e52b262d410305f3c4d2a5d92b6175cb4d9595738c896570893fe54b154c554955f8e5461d2e4532180924e42e48a4aa0de1a4473e5693fba0e323d6089e83cc096733c2d61af39b9eed635a33f96351ea90432fc7e7c31c5695e30dfae1d2e9486eb2bedc5d12a5cb8c41f2276f01515303f14a34e5310687c870efd143c0d891f440d227c4c0c9fc9bf08770ba6051ef7b803f21250
  | 6, 0, 1 => 0xfe98b7e7fe8ba7b7f90122dcf6f91945f652342df524d58ef47d59d8f47366c0ed2150faeb865a11ea6832e7e57e025cdabc9fa1da5c6f41d5acb028d2186bafcfa2773acda92b94cb11054eca14e71bc7adf1c2c7474ecabe794a80ba04a7adb6ed774a
  | 7, 0, 0 => 0x27a4a8492730f4cd26c80b1626144d3626099ed525836aef2543e48c248e50e9246a0b8a23efb9852308cf9f22ae156b2284b333223769d3219084bb20a9991b1fbbaa661ed2190f1d714dfe1ca711891c6686f61b8f4bc218917f94181b10ba176707ad17028266150dfc80149a4ea1138bc72e128628ed1205328f1182c6e910b47c75109959ad108dfb001002172d0fa701a80c76b2fc0c3de4c00c3025590c1de1fe0bb355150b50bf8d0ae95fc10a9cd3050a3643350a01adfb097f42550895d519079816f407936aa70750f5920749dc200694c2350674bcee0620bd3c05e0f0500567fa510535186904e437fd03c61cd003a7a7ad0188bf7200242408
  | 7, 0, 1 => 0x4c74d9df4bd65d2f4926b510483280b847623978462698db45f4fb8345bd00e6459270974561370c44b0b53e441369d343f8662a43e12dec43c11da543a4a4f9433fa33f42e11d4e405380cd3f5f549d3f3c83753d6a91643d5edcee3d21d1683cf4fcd73bd5ac933bd23dc43bc2caa43b6671ed3add98ba3aca73853a1fbb5339f6d3fc375cfd2436f1a5a3368845d536727dff35e94e9c359128c13582312934d0c5503457b9423403b3df33df7b7b3384e6b3326f284231f34f68307299be2ddc07642d7eac952c2031b22c05dd8b2c002f4b2b0c54332ad101ba2aafe6892a71985b2a20277c29c9f8452967649128b7dffc2850803027fa169d27c003a9
  | 7, 0, 2 => 0x7a32e6c478ec302a78de0fbc785ddb1277a34c837527fdbd727f3775722f623071686d2e70f3945670e8ab9670ac39d16dd70a656d2479296d1f9e616cd020406bc7b2ce6b9ca6a46a697e6b6a5e2e4969cae70769bc6b2668c78de0689eda76676bb23d66484c3065dd7ad365a37f6d64f83f64646f590d64545b1d6452eb0d63df5c5262bc2e5c61c7627361ac135560e190246066cd78605cf9925ed0c0195d97f1e35d45a2725d42352f5d03b9ec5ccbc6555cc3a9ed5aca5d735ab8a9c85a757c2359d2d77959c5ddbf58c2ef595710d06857106ce856f73cc156cd3b85559b0952553eb09b534c3a7b5271f78f5011dd494f5a6fd74e1ca4aa4c9ed9d9
  | 7, 0, 3 => 0xa3731f65a320cff4a2dee76ea0e3d99da0d1e825a0a58af5a093d74aa0855b69a02ab1c09fae04fb9f67cab99f56ae149f0c24059e7b41be9dccd3d09c5909559b6f9ad19b1d4b609a78a26b9a470735998e521e98a20661984429e797c47c1b977147d696cbd80a9677bd2a94e87956946ca34093384e8a91b18ab19132cadd902116718e9c58c18e68f6f78d9ceb668d7869e68c86d0e28bfc04118b303b6f8b21bf8e8a7a9db889ae061d88f9edfc88d106a5881d533b87f329e785b9af858574e5528515b8cd83cbd3c0832cb6db827719248246e48c8119fa028103242c80e5759f809c81347fefa5537f8e9d3a7f6c93bd7c9f7e7c7c34289a7a9eb29b
  | 7, 0, 4 => 0xc66f499fc5342b32c51c6308c45b15b3c35a0575c301a16cc300e1d9c26e9b1ec20f561cc1438dfbc0ddf788c005c2cebf6dea7dbe652655be390894bd8d30adbd8cffe8bd7d1a02bd63b217bd197d31bbf2c6b6bbac5b9db8572b6cb7edea51b788427ab72f4b60b71d2d87b6897ce4b6187b80b5af91d3b574c2ceb3c24a54b3971adbb28f99edb1b80fbab177d426b04302eab03e1077b03a9b5bafcbe12cafa76697af78aea8af6a54ceaf0aef8cae7a07f8adee40ccadcd7a96adbb0c5babea86aeaaf7e2b6aa9730b5a9b63e9ca9744f92a898adeca7778458a76b4f4da70c7473a6d0c780a6b9e07fa6768364a5ef21d7a5eabc38a5da4240a57de989
  | 7, 0, 5 => 0xeb1a9bc8e9eb6b25e9e08265e9b79b0ee9840b59e8cf8ba4e879cfe1e7e9b955e71705cde6b6f618e64c55b1e542f83be53126b1e44a5e60e311d1c1e2dcb27ae27552aee2590ed6e0ce06f0e00571fedf4022ffded551a2de8ede08dcc9e4eedc0b8b92db7af8fbd9e0ee8ed9c9b650d801ed6ad5b41e40d5340983d3d3e2c2d30a59ccd2b65212d21f9782d1bac628d168f0afd10ff778d10cbaffd0f46623d0b2fbe9d02ede41d008a737d00843b7cfdf5c60ce8d2592ce6a62a9cce0ba88ccc52a17ccbc92c1cc5e9a47cc2a050dcb5012d4cad7f953cabe2c2bcab7206bca1247a7c98b03f2c85246a6c816b9b0c80f6476c7dbd7ccc7147b79c6b296df
  | 7, 0, 6 => 0xffb3ea6bff86098afd56bc3dfd05efccfcc3aa8ffbfedff8f8806e93f845dbe6f7949bb9f6e37eaff6b5bc52f5e6a71cf55337a9f539372af4e61d0ef4b474e9f4581c32f3a8a818f39639ddf2caac3cf1e406f9f195bf85f0d31038f0c49457efa703a7ee73db6eee33f0d4ee28865dece2987aec99ef6deba52384eb5c844e
  | 8, 0, 0 => 0x43596148434d744140f62fdf3fd89f2f3f521ef63eca17bc3e51fe3b3d9f9c853d0508da3cc117773bcc4b8e3b4067bb382614fb375c328c3627b04f35db239335895b043578c84e34bd92e331b30d7c315f0dca300d39e92ee5f83b2cc710002c33b3742aa9504827a4a97824f1d90e23bebf2122f2b39021f40ce0216845b4207787b81e08fcca1c1160c61c02e4e51ae5543519b22bfc196926bf17c0281516ed244d169ad4dc1658ec5614f312d414c25be71439cce4141f8fdd140ddc32132809e312a036a611f546a610af5719106602d20f88aeee0e50224f0db3a33c0d2c2e290c0c577e093db68007852a5a052b8f99020fff7e0193adbd00f26ece
  | 8, 0, 1 => 0x861a5c8185cf5b4385b3ccb1857f377784fccbd184135e9584013fe78302b3d6824f20f6824ebd7681d2870380d29a39805efbd87f2d59fd7db0481d7ac3e1087a98c065795af53876e1ad9c742c1b0370d0c1256f36b6b86f1f7e7a6a9da52b6a0e5a80686021f6685bd80f6722ad0067108e5267103ec5664a2e4d6608c413655e0be16535248a644d152062125aeb61ede05661b0ce8d6131850561279f2a60c081b76013f4555f40357b5d319ff65a910ab558bcfd2357c4634856a6587655e7a0d6555e780a53d94335538ed0be537f76e652e2f8d7526f455b51529dc450d632f750c1bb7d4f85907a4c8d80f448be36e947e5621746cd9c5043cfd022
  | 8, 0, 2 => 0xd0bc3a17cdef810bcad7f953ca94fea2c9ad816cc88323f1c77d5d96c58557c3c4cca2acc3827a75c2d474bfc08ae272c026c9e4bfd6d0e9bf75efa6bebd2cbbbe769f18bd4fdec7bb5f66ffb9daa94fb8db3bf4b65b2236b0bd8805af0a244ead70d8e4ac584a90aac32e09aa6baa8ba8fdcabba8fc3611a8f48ae1a77db8c7a7420870a69e95f1a64e8b36a5ef21d7a5dd0329a42a80b8a3dc3944a07a6a939ee8568d9e86591b9deb9d439ca6bdbc9c31e4e49c26fc249bea8a5f9bca85189a8d182a99d4553f98fd6fd797e4107295feb81b94ffe11f94dbd1b49301e1e191869cbe911bcb618f0950aa8cea63e38c0b847c895dd9a18888016887abe572
  | 8, 0, 3 => 0xffb3f673ff123350febb539efeaa4057fdf4a2a0fc4e4806fc4b0b8dfb6d2ecff9a8b337f8037aa5f61649e1f2218e7ff05ab396eeca28f2ee18b783edacebaced03ec8bec663512eaac3b0bea36d74ae9a376e3e8a202a5e7d7a280e7311744e6eaac2be5f93c5ddde38353ddce86eedd44ebefdcf66048db7c6105db4ac3addae5b725dab6ff36da067d68d982c8fbd916e5cfd753c3f4d6d37c15d6363344d5053b33d4f48f2ad3d6fe7ad3ba0645d24ac501d11892ce
  | 9, 0, 0 => 0xf92dd199f61649e1ee12c54deab44034d8af2972d43a869fc708d5a6c43bc065ba47a138b749d50ab158ad0fb03b1c5f8f8b65ae8d2c30e48302b3d677cbd18269904ec94e31041e3e51fe3b3ba45360196926bf1957081117a485a0
  | 10, 0, 0 => 0x69904ec9
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xccccffffccccffffffffccccffffccccf0f0f0f0fffffffffffffffff0f0f0f000000000ffffffffff00ff00ff00ff000000ffff0000ffff555555555555555500ff00ff00ff00ffcccccccccccccccc0f0f0f0f0f0f0f0fffffffff00000000ffff0000ffff0000f0f0f0f0f0f0f0f055aa55aa55aa55aa3333333333333333
  | 1 => 0xaaaaaaaaaaaaaaaaa8a8a8a8a8a8a8a8fcfcfcfcfcfcfcfcfafafafafafafafaeeeeeeeeeeeeeeeeffaaffaa0000000000550055ffffffffffaa0000ffaa00000055ffff0055fffffafa0000fafa00000505ffff0505ffffeeeeeeee0000000011111111ffffffffffff000000000000ff00ff0000000000ff000000ff000000
  | 2 => 0x1133113311331133000500050f0f0f0f0011333300113333005500550f5f0f5f0055337700553377aa00aa00aa00aa00ffaaffaaffaaffaa55ff55ff55ff55fffefeccccfefecccc0101333301013333fafac8c8fafac8c80505373705053737eeeeeeeee0e0e0e0111111111f1f1f1ffefefefef0f0f0f0010101010f0f0f0f
  | 3 => 0x5500550055005500f5f5f5f5f5f5f5f5ddddddddddddddddfff0fff0f0f0f0f0fafafafaf0f0f0f0eeeeeeeeccccccccfafaf0f0fafaf0f0ffccccccffcccccceeeecccceeeecccc050f050f0f0f0f0feecceeccccccccccfaf0f0f0faf0f0f01133333311333333050f050f050f050ffaf0faf0faf0faf0eecceecceecceecc
  | 4 => 0xff00ffffffffffffccffccccccccccff0000000000000000ffffff00fffffffff0f0f0fff0f0f0f0fff0fff0fff0ffccffccffccffccfffff0fff000000000fff00000fff00000ffccffcc00000000ffcc0000ffcc0000ffccffccffccffccfff0fff0fff0fff055555555000000005555000055550000ff55ff55ff55ff55
  | 5 => 0x505050505050505fac8fac8fac8fac8eee0eee0eee0eee0fef0fef0fef0fef0fefefefefefefefefefefefe00000000fefe0000fefe0000fe00fe00fe00fe001111111111111111aaffaaffaaffaaffaaaaaaaa00000000aaaa0000aaaa0000fafafafa00000000fa00fa00fa00fa00eeee0000eeee0000ee00ee00ee00ee00
  | 6 => 0xffaaaaaaffaaaaaafafaf0f0f0f0f0f0eeeeccccccccccccfefefcfcfefefcfc11113333111133335555ffff5555ffffaa00aa0000000000faf0faf0f0f0f0f0aa000000aa000000eecccccceeccccccfefcfefcfefcfefcfffafffaf0f0f0f0ffeeccccffeeccccffaaffaaf0a0f0a0ffaacc88ffaacc88feccfeccfeccfecc
  | 7 => 0xffffaaaaaaaaaaaafffcccccfffccccceeeceeeceeeceeecffffccccccccccccfffcfffcf0f0f0f0aa88aa88aa88aa88faf8faf8faf8faf8fffcfffcfcfcfcfcfffcfcfcfffcfcfc0303030303030303fffff0f0f0f0f0f0aaa0aaa0aaa0aaa0ffaaffaaaaaaaaaa050505050f0f0f0ffefefefefcfcfcfc55555555ffffffff
  | 8 => 0xfffffffffffffcfcfcfc00000000fcfc0000fcfc0000fc00fc00fc00fc00fffcfffcfffcfffcaaaa000000000000000f000f0f0f0f0f0033333300333333
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x403060105504030201005
  | 6, 0, 0 => 0xe0a0d02060860a160206080b604031c061e0760e061f05070b60429022a000960a0223061f096030a02061f2e6032102061f07604380a02371f6040a0800050960403021b1e0760c03020800076030a020608136030a0d02080060c02060807096031f0005070b60a02140608096040e0a021f2f60a0d020608096061f0507090b6180a0206080b60c030a311f0061a0a020608096042502061f076040a02061f266021f0007090b60314061f0507604031d1c1b0760a2502061f0b60403290628056030a1d1c1b0b6030a02061f226
  | 6, 0, 1 => 0x4030206015040a0f06080560c021f00070960329062a050b604030a351f056040e06080507603020800070b60e0a0608050b6040e0a301f05602060807090b6030223061f076042702061f076030a02061f2060a2702061f0b6030a061f05196040308000507612111002060860406080507096030a0800050b604030a061f3660302140608076040a021f00176030d0206080760a060805090b6040a021f001560c030a061f3260c0a020f06086040a02061f2d604020800070960c0e02060807604160206080760a020800090b6
  | 6, 0, 2 => 0xa2102061f096040a020608176040a02061f246040a0206081560c0a020800096041f000507096030a02060819604030a341f0060a1f0005090b60403290228006033c0a3b061f60c030a391f006030a02061f2c604030a021f3360416021f0007604020f0608076030a061f130560a16021f000b6040e0a3a1f0560a020f06080b60a14061f05096040a1d1c1b0960e020608070b603060805070b6040a02061f2b6
  | 7, 0, 0 => 0x4030a2102061f7000403061f08050770000030a0208000b6000c030a1002060870003641a0a02061f70000040329022a006000c030a0237061f70004430a021f00097000403180a0206087000403023d060807700040e0a3b02061f700040e0a11020608700030a020608070b700031d02061f070b700030a0206083f0b700000a020608090b600030a061f08050b70000030a0223061f60000040a2702061f60004030a3a061f0570004033e02061f0770004030a1f55000570004030a1106080570004440a0206080970004033c02061f0770000042902062a09600033c0a02061f557000004030a02661f60004030a1d39061f70004030a0654080570004034e0a0206087000403780a02061f7
  | 7, 0, 1 => 0x30a110206550870004031a0a0206087000003640a02061f60004034a0206080770004030a49061f05700040302065408077000403433802061f7000c0a021b061f09700040302061f7607700040a1c021f0009700030a1d021b1f0b7000c030a021f0007700047f0302061f0770000040a02061f15600000c0a021f0009600040a020f061f0870000030a02061f196000004180a021f0060004030a02061f8170004030249060807700030a02061f760b7000403021b0608077000004030208000760000040e0a060805600040a021f2a00097000403460a061f05700040e02061f0807700040a1d02060809700030a021b06080b70004030a4a021f0070004030206083f07700000402060807096
  | 7, 0, 2 => 0x40e0206080760004034b0a021f007000403023d061f0770004033c0a1c061f70004030a1602060870004120a100206087000c030a021f5400700000403060805076000403630a02061f700040a061f2a0509700040302061f570770004030a02061f7270004030a6802061f70004037e0a02061f700000e0a0206080b600040a100237061f70000040e2902062a60000030a0608050b60000040e0a02301f6000004035802061f600030a02061f570b70004031d021b1f0770003290a061f050b70004030a39021f007000302061f08070b7000403440a06080570000040a02061f1760000040329062a0560004033b02061f0770004031102060807700040e0a061f55057000403400a0208007
  | 7, 0, 3 => 0x4030a021f7400700040a1c021b060970000040a16021f00600040a1c02061f1570000031a0a021f0060004030a50061f0570004030a061f7005700040a021f00070970000040a020f06086000403061f5505077000403400a0608057000c0e0a02061f0770003440a0206080b70004030a0214060870004030a061f690570004030a7102061f70000032902062a0b60004031d1c061f07700001a0a02061f096000403431002060870004033c4402061f70004030a1d31061f70004030a6002061f70004030a023006087000403380a061f057000004030a02351f6000403120a0208007000004180a061f0560004030a1f2a0005700030a1d1c061f0b7000403020656080770004030a100208007
  | 7, 0, 4 => 0x30a0d021b061f700041c02061f0709700030a1c021f000b7000403441102060870000030a0d021f0060000040e0a023a1f600000c02061f070960004033802061f07700040a02061f5f09700040a3102061f097000403021f2a0007700000a0214061f09600040e0a061f2a057040a10021b061f54800040a5b02061f097000a1c02061f090b70004031d02060807700000a0d02061f09600040a10021f54007000403120a06080570004290a0206080970004030a100608057000475030a021f0070003380a02061f0b70000180a02061f0b600030a021f2a000b70004030a37061f05700030a1d0206080b70004030a6c02061f7000003020608070b60004033c0a02060870004030a1d02301f7
  | 7, 0, 5 => 0x403061f2a0507700040310020608077030a111c02061f55800040a11061f05097000403380a021b1f70004030237061f07700040302061f1e07700030a061f2a050b70004030a023a060870004030a3b020608700030a100206080b70004030a0255080070004030a2702061f700030a0237061f0b70004030a02061f2f70000046f0a0206546000403293102062a700040a1b061f05097000c03021b061f07700047c030a061f0570004031c021f000770004030a1f000507700000e1a0a02061f60000040a1f000509600000c03021f000760004030a0206084c7000403470a02060870004037b0a02061f70000030a02061f13604030a101d1c061f80004030a31021f0070000031a0a061f056
  | 7, 0, 6 => 0x4030a024906087000403111002060870004030a061f054f70004030a0655080570004021b061f07097000403770a02061f7000c030a0230061f700040e1c02061f07700040e0a061f05077000004021f000709600030a1c021b060b7000c030a10021f00700000c0e02061f0760000040a2502061f60000041602061f07600040e0a3102061f7000a021b061f090b7000403180a021f0070004030a520206087000e0a1c02061f0b700000a021f00090b600000e0a0d02061f6000403460a02060870000030a14061f0560004030a1d023a1f7000004030a1d1c1b600000a1602061f0b6000403640a02061f70004030a111f000570004030a1f54000570004730a02061f09700040312020608077
  | 7, 0, 7 => 0x40302061f5f0770004033102061f0770000030214061f07600030a113b02061f700040e0a11061f0570004035b02061f07700031c02061f070b700030a061f05070b70004033c0a1d061f70000030d02061f07600000a061f05090b60004030a4d02060870004034a021f00077000403021f540007700000403290206286000463180a02061f700030a02061f5f0b700030a3102061f0b70004030a5e02061f7000403430a02080070004030a4a020608700030a5b02061f0b70004030a02510608700000c030a39061f60004034e0a061f05700040a1c020f061f700030a021f54000b70003290a0206080b700000c0a020f061f60004430a0206080970004031c021b060770004030a02061f807
  | 7, 0, 8 => 0x4030a02061f32700040349061f050770004030a3902060870004031b061f050770004030a0266061f70004030a025006087000004030a021b1e60004030a021f2800700000c030a0208006000403020655080770004030a16021f00700040a0230061f097000004031f000507600041c1602061f07700040a021f0800097000a021b14061f0970004030a025d061f700040a1c020608097000012111002061f6000c030a02060807700030a1b061f050b700000c0a0206080960004030a6502061f7000004061f0507096000403380a02060870004034b0a1c061f7000004030a34061f60000030a1f00050b600040302061f08077000a1c1602061f0b7000004180a02060860004030a022a08007
  | 7, 0, 9 => 0x4030a5c02061f7000004610a02061f6000403480a0206087000a1d02061f090b7000403020628080770004030a1d3b061f700030a0d02061f0870004030a062a080570004037302061f077000002061f07090b60004030a027d061f700043c0a02061f097000403450a02060870004034b0a020608700040311061f0507700030a11061f55057000403290230062a700030a210214061f70004030a0237060870004031a0a061f0570004030a53020608700040e430a02060870004034310021f0070000030a2102061f6000004030a6e061f600040302060842077000003620a02061f6000403380a1d021f7000004034002063f600030a021b061f1370000040a5902061f600040302561f00077
  | 7, 0, 10 => 0x4030a30061f0570000040a0208000960004034e0a021b1f7000403120a1f0005700000c030a31061f60003430a0206080b700000c0e0a02060860004030a061f7a05700040306561f050770000040a1602060860004290a021f000970004030a101f000570000040e061f05076000004630a02061f60000031a0a02060860004030a1d02371f700040a020608070970004030a061f2805700041d02061f0709700040a0206083f0970003021b061f070b70000040302060807600040a061f0805097000004030a68061f604033c0a021b061f8000c0302061f08077000003021f00070b6000004030a026d1f6000004030a1c061e600000e0a061f050b60004033c0a021f0070004380a02061f547
  | 7, 0, 11 => 0x30a0214060860004030a3b021f00700030a10021f000b700000e02061f070b60004030a11020800700030a1c0206080b700040e3c0a02061f70000030a0d0206086000403020608410770004030a025408007000003730a0206556000003061f05070b600040a1d021b1f09700040302062a08077000c03440a020608700040a3b02061f09700040a1102060809700000c032902062a600040a100206540870004036f02061f0770004030a021f004c7000403470a021f00700040a02061f760970000030a5a02061f60004033e0206080770000040a0f061f0560003440a061f050b70004030a14061f05700036f0a02061f0b700040a021b06080970004030a02061f6b70004030a020800077
  | 7, 0, 12 => 0x40a271602061f700040a061f5505097000004020f061f07600040a1d1c061f0970004030a52021f00704030a111d021b1f80004030a0206084f70403380a1c02061f80004034411061f0570004030a7902061f7000004030a0800056000c03380a02061f700000a020f061f0b600040e0a0206080770004030230061f07700000c180a02061f6000c030a021f2a007000403021f08000770003021b14061f0770003120a11020608700040310021f000770004030a021f670070004031c0206080770004030a0608050770000040a06080509600000c030206080760004030a021f6a00700040a02061f5709700030a0230061f0b7000402061f080709700030a021f08000b70004030a310206087
  | 8, 0, 0 => 0x40e0a02061f0770003120a1102061f70004031c02061f0770004030a061f050770000040a061f0509600000c0302061f0760004030a02061f08704030a11021b061f80004030a02061f5f70004030a3102061f70000030a0214061f604030a021b061f5480004030a11021f00704030a021b51061f80004030a5b02061f700030a1c02061f0b70000030a0d02061f604030a1d02061f2a80004030a021f540070403440a1c02061f8000403290a020608700040302061f2a077000c03440a02061f700040a1102061f09704030a1c5302061f800040a1002061f547000475030a02061f700030a02061f2a0b70004030a1c021b06704030a021b061f07804036f0a1002061f800040a021b061f097
  | 8, 0, 1 => 0x40e0a061f05604030a0237061f54804030a1d02061f07800040a1d02061f0970403120a1c02061f800030a021b061f0b7000004030a020608604030a101c02061f8000c030a02061f08700000402061f070960000030a021f000b6000c030a1002061f70403830a1d02061f8000403180a02061f700040e0a1102061f700030a02061f070b7000403730a02061f70004030a8502061f700000a02061f090b60004030a11061f0570004440a02061f09704030a3102061f2a80004030a061f540570004034e0a02061f704030a021b50061f80004030a0206084270403430a02061f0880004030a1b061f0570004030a02061f4f70004030a020655087000004030a1f0005600040a1c1602061f7
  | 8, 0, 2 => 0x4030a10021f0070000040e02061f0760004030a1c02060870004030a02061f28700000c030a02060860004030a1602061f704030a02061f080780004120a1002061f700000403061f0507600040a02061f08097000c03290a02061f700000e0a02061f0b60004030a0206084170000030a061f050b60004030a02062a08704030a111d02061f80004030a02061f427000403440a061f05704030a1d02061f5480004031102061f0770004036f0a02061f700030a1102061f5570004031a0a02061f70004034a02061f0770004030a02061f87700040302061f540770004030a3e0206087000403430a020608700030a02061f540b70004030249061f077000403021b061f07700000403021f00076
  | 8, 0, 3 => 0x4030a0206080770004030a02061f4170004031d02061f0770004030a0206083f70000040a0206080960004030a061f08057000403120a061f0570004030a02061f2a70004290a02061f0970004030a10061f05704030a0230061f2a804030a3b02061f5580403380a1002061f80004030a023d0608700030a1d02061f0b70004030a3e02061f700000302061f070b60004033c0a02061f704030a1102061f08804030a1c02061f5580000040a020f061f60003440a02061f0b70004030a0214061f7000403431002061f70403120a021b061f80004030a0230061f704030a10021b061f80004030a021f08007000403120a021f00700030a021b14061f70004030a02061f7a70004030206561f077
  | 8, 0, 4 => 0x4030a101d02061f8000c030a02061f2a7000403290a061f05700040302061f080770004031202061f0770004031002061f0770004030a02061f6770004030a02061f6a704030a021b061f5580004030a1d021b1f700030a02061f080b70004030a023a061f70004030a3b02061f700030a1002061f0b70004030a021f550070004030a1102060870403440a02061f0880004032902061f2a70004030a0206540870004030a02061f76700047f030a02061f70004030a8602061f700040a02061f550970403730a1102061f80004030a02061f4c7000403470a02061f70004030a021b06087000403441102061f7000004030a0208006000403290a021f00700040e0a02061f08704030a1c1602061f8
  | 8, 0, 5 => 0x4030a021f2a0070004030a1d0206087000004030206080760004030a4d02061f700040a02061f2a0970403430a021b061f804030a1002061f088000403430a021f0070004030a4a02061f70004030a0251061f70000030a0206080b60004030a02061f8270003290a02061f0b704030a021b14061f8000403440a0206087000004032902062a60004430a02061f09700040e0a02061f5570004030a0249061f7000403111002061f70004030a061f550570004030a1d1c061f70004030a02061f3f70004030a5202061f70000040e0a0206086000403460a02061f700040e290a02061f70004030a023d061f704030a1c02061f2a8000004030a06080560403120a1d02061f80004030a02061f577
  | 8, 0, 6 => 0x403120a02060870004030a061f2a05704030a111c02061f80004030a100206087000403450a02061f704030a1c02061f5480004034b0a02061f70004030a0237061f7000c030a02061f5470004030a5302061f700040e430a02061f70004030a02061f1e7000c030a021b061f704030a1d02061f5580004030a1c021f0070004030a3902061f70004030a0250061f70004030a02061f70700000c030a021f00600040302061f55077000403400a02060870004030a0206561f70004030a02061f69704030a1c02061f07804033c0a1102061f800040a1c02061f09704030a1c5202061f8000c030a02061f07700000c0a02061f09604030a021b061f2a8000403380a02061f7000004180a02061f6
  | 8, 0, 7 => 0x47c030a02061f70004030a021f000770004030a02061f74700040e0a1c02061f70000040a021f000960003430a02061f0b700000c0e0a02061f60000040a1602061f60000031a0a02061f600040a02061f070970000040302061f07600040e0a02061f2a7000403480a02061f70004030a8402061f7
  | 9, 0, 0 => 0x4030a1d02061f700040302061f07600030a02061f0b60403440a02061f700040e0a02061f60004030a061f05604030a1102061f704030a02061f54704030a021b061f70004030a021f00604030a02061f07700040a02061f09604030a1c02061f7000c030a02061f604030a02061f2a70403430a02061f70004030a02061f604030a02061f5570004030a02060860403290a02061f704030a02061f0870403120a02061f704030a1002061f7
  | 10, 0, 0 => 0x4030a02061f6
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 44
  | 6 => 52
  | 7 => 68
  | 8 => 68
  | 9 => 60
  | 10 => 52
  | _ => 0
def stateM : Nat → Nat
  | 5 => 0xfffffffffff
  | 6 => 0xfffffffffffff
  | 7 => 0xfffffffffffffffff
  | 8 => 0xfffffffffffffffff
  | 9 => 0xfffffffffffffff
  | 10 => 0xfffffffffffff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0xeffff830ffff003ff01c3fff1c0c00070e603fffffff003fffffc1c0e030000000003fffffff00380f803e00ffc000000fffc000ffff003ffffc3ff0fc3c0007f07fc1ff003f0000e01c38301c0c0038f19ffe3f1fcf003fffffc0000000003ff0003fff000000070e6001c0e03000380f83fe0ffc03003f1fe3c7cfe3f3
  | 1 => 0x3c00f03c300000000000000000007ee7c39f0fc3c00070e63c1cfe3f30000e01ff83f1fcf00380f83c00000000007f07c3fffffff003800003e0f00000007ffffc1f0ffff0007000001cf00000038fffffe30ffff0000e01fc0000000003f1fe03fffffff003ff0000000000000380f8000000000003800003e000000
  | 2 => 0x3f1fe3c7cfe0330000f01c3e3f1fcf00071fe3c1c0e3f30007f07c3fff1fff0007ffffc1f0e3ff00000000000003c000380f83fe0fffc3003ffffffffffc3f0007e01c39ff1c0c00381fe3c600e3f30007000001cf00000038fffffe30ffff0000e01fc0000000003f1fe03fffffff0007ee7fc1c0e030003811803e3f1fcf
  | 3 => 0x380f803e00fc00003ffffc3ff0fc3c003ffffc3ff0fc3c003f0fe001c0e03000070e63c1c0e0300000e01ff8301c0c00070e6001cfe0300038e01c3e301c0c0000e01c383f1c0c0038f19ffe3f1fcf0000e01c38301c0c00070e6001c0e030003f1fe3c7cfe3f30038f19ffe3f1c0f00070e6001c0e3f00000e01c38301fcc
  | 4 => 0x7f07fffffffff0038ef9c38301c0c00380000000000000007ffffc1ffffff003f0e603fc0e0300007fe7fc1ffe03f0007f07ff9ff1c3f003f0fe000000000003f00003fc000000038ef9c000000000038e0003e3000000038ef9c3e30ffcc003f0fe03fc0fff0003ffffc00000000003ff0003ff00000003ffffc3ff0fffc
  | 5 => 0x38f19c3e301c0c00000e000000e3c00000000038001fc000070e6039c0fff00007ee7ff9ffffff0007ee7fc00000000007e00039ff000000000e003800ffc0003f1fe007c0e0300007f07fc1ff03ff00000003c000000000000000000f000000070e63c000000000000e000000e3c00000e000383f00000000000038001fc0
  | 6 => 0x380003fe0f03c300070e6001c0e0300000e01c38301c0c0007ee7c39fffc3c003f1fe3c7c0e3f3003ffffffff0ffff000000000000000000070e6001c0e03000000000000000000000e01c38301c0c0007ee7c39f0fffc003f0fe3c1c0e0300038e01c3e3f1c0c00380f83c000e000003800003e0f1c000000ee1c3830ffcc
  | 7 => 0x3ff003c00f03c3003fe01c3ff01c0c0000e01c38301fcc003ff01c38301c0c003feffc01c0e03000000000000003c000070e6001c0e3f0003feffc39f0fc3c003fee7c3ff0fc3c00381183c60f03c3003ffe6001c0e03000000000000003c000380f83c00f03c30038f19c3e3f1fcf0007ee7ff9f0fc3c003ffffc3fffffff
  | 8 => 0xfffffffffff0007ee7c000000000007e00039f0000000000e003800fc00003feffc3ff0fffc00000000000000000000f01ffe3f1fcf00071fe3c1cfe3f3
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x12e7fdf8b17eff003ffd5e7fffdd6d00274e689ff7edff003ffffff5eafaba000000001ff7edff003c8f913f04ffc0000007fdc0007eff0036cd5835a0d8280003706ec0fb003f0012e55c78b15c6d0018b1976a1d1745003fffffe0081200003ff8023fff810000274e6895e2e8ba0035bd36f55bd817002d1aa3874ea392
  | 1 => 0x932a7ca5f27d700012224c85324d70037ef7cfdf3fcff002f7eefdfffefff001bf7fffaff7fff003dbfb7e0081200000240481ff7edff003db8023f5f8100000247fdc0a07eff002f78021fff8100001087fde0007eff001bf7ffe0081200002408001ff7edff003ff80220080000003c8f9120001200003c88003f048100
  | 2 => 0x251822854a8012000000000a150545000002a180002292000240480ab5056d000242e980a022ba000802810a0427c0003dbfb7ff5fffd70037fd7ef5fbd83f003ffd5e7fffdd6d000002a180002292002f7c4e5fffcd6d001083b1a0003292001bf7fff0ea7aba002408000f158545003ffffff5eafaba000000000a150545
  | 3 => 0x348d103500d8000037cf78b5e2f8ba0036ed5c7db1dc6d003fcff9b5e2faba002f7eefd5eaeaba001bf7fff8b95e6d002f7e6a9fffe9ba003eed5c7fb5dd6d001bf55e7aff5d6d0010b1166a1d1545001ae7dd78b15e6d002f4e689fe6e9ba00251aa3854aa2920010b11660191005002f4ee99fe6effa001ae7dd7ab57fed
  | 4 => 0x3706edfffedff003eefdd78b15e6d003c880020000000000377ffc0fb7eff003fce68bfe6e9ba00277e6ed5fbe8bf0013f57ef8fb5c7f003fcff9a0001200003fc8003fe68100003eefdd60001200003ee8003fb58100003eefdd7fb5ffed003fcff9bfe6fffa0036cd58200010000036c80035a08000003ecfd93fa4ffe8
  | 5 => 0x10811020001000002e6ecd5fb5efed001bc7f9bae67ffa003fcff9bfe6fffa003fffffffffffff003fffffe0081200003ff8023fff8100003c8f913f04ffc00024080005008000000b72efcaff27ff000932a7c0080200000930020a5f0100002f7eefc0080200002c0e811f04efc0001bf0023aff0100001887913a047fc0
  | 6 => 0x3dbaa7ff5fa7d7002f7e6a95eae8ba001bf55e78b95c6d003fff7efffffdff00240aa18500a2920036cffdf5a0feff0008028100000200002f4ee995e2eaba000800000a040100001ae55c7ab55d6d003feffdfff7ffff003ffffff5eafaba003ffd5e7fffdd6d003dbfb7f54afa92003dbd167f5fdd45003eefdd7fb5ffed
  | 7 => 0x3ffaa7ea5f27d7003fed5c7ff7dd6d001be7fdfaf77fff003ffd5e78b95c6d003feffdf5e2faba000822854a1527c5002f6eeddff7efff003feffdfdf3feff003fef7cfff7fdff00081083020c0300003ffe6ab5eae8ba000902a18a4627d2003dbfb7ea5f37d7001081102a151545003ffffffdfbfeff0036cd583ff7fdff
  | 8 => 0x7fddff7ffff0037ef7ce00010000037e8003df3800000348f103d00fcc0003feffdfff7ffff0009300200080000000030064a1d0545000112a3804a2292
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 136 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem wd_0 : ∀ i, 0 ≤ i → i < 128 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem wd_128 : ∀ i, 128 ≤ i → i < 136 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 8 128 = true)
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 136 → wireDOK i = true := (range_split wd_0 wd_128)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 136 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 136 then wireAt i else 0
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 10 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 5 => 12
  | 6 => 509
  | 7 => 2332
  | 8 => 410
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xef90fb32ce087972c7116ed5bf0dea41a82065a9813641536456e10656906d834e8ce8ef356c28b42d68a42010b54001
  | 6, 0, 0 => 0x1ed2190f1ec641401d995eb21d98e2a11c46abd31b30e09c1ae554351ae4d3311ac1c4da1a97ec0a1a6109241a519e6d19b22bfc19a4c687194947e118e3578118b71c4c18af80cd18917f9418405eba182d4abd17ba9f93177d348c16d6d0931658ec5615d8bb2815c8eab715955e0d1541688b1342e5c2132809e312edb1731279613a11fdc2171182c6e90fb71aff0f6b3e1a0ec187460e2146200d2f6b050caedf080c4a0b790ab1918c0a583cd10a34a7db0a164d1209fa4f090979a5d3090fc5e107fe3fd307936aa7074d1a3006e356c406350f0a05fcea2e05c54fb805a77092055517d504e437fd03d88c74032e490f02ed76e0024022630063d605
  | 6, 0, 1 => 0x3bb6f2d53ad916173a7cd14d39f86a3f39f6d3fc39c8295e38d4220938cb0ba03771214f3735945937345580372e3f1f35f050a63582312934ed624534bd92e334702ab832603d5830d73d1430c7870c30777df32ef458bf2eee73662ee197fb2ea91c1d2e9f17e82de5383e2dd6a17c2d651ec12d2083942c05dd8b2b2f4cc22a836b2f2a6a52732a34794a29cb842329b322d129a8454229a15c2129347f3c290f0ba8270cc4fa26c80b1626a71d232611cae925e96bd0254f9c34254f1b30247947d323620fd722982227223f9947223769d321f40ce021c92a6d21c7655d21a84b1b2186451d214c466820b30561208a8efc201efaa41ff2102c1fd528dc
  | 6, 0, 2 => 0x591e134458bcfd235755a50e563c4d63559b095255519d35554cf0e854ae7981532cafce530110b752a34a4e529863255293f12b527c055552378dbf51cb0b1651ba264a50c31e47508cbf0e4fa1bfa64f5a6fd74f408a4a4f3996ef4e85d7fc4d0346ac4c9930344be8bf974ba07d3a4b8f05934b10427e4a92ee0449f653c649e152db497e06634926b51048893a7a481b4fe547ad947447741cc446a3d46646735fff45d34bee45b84e38451a7cea4459c9ea43cfd02243bb5cb343a4edaf43a3289f439cf8a643596148430cbdea42ad9c65417a81cf4157649441204cd8405380cd3f304adc3e51fe3b3ce2c1c13cc117773c0ab8fe3bd5ac933bcc4b8e
  | 6, 0, 3 => 0x7a98c06579bf63cc791366f1788d557a7863c8f576b6f19d75693d58755c37ee74bcc57d747a456a740312a673fef70172424eca723da27d71f2137671cb389a70d0c125701d61636ff442ca6f8372c46e4d7f436dd298c36d91538c6cc2972b6c76c0d66b2ac9b66a7b4da169ee8ee269b7b878687f97a867d59b01677fee3067734ea96640782b65d496fb653d7016653d59ad6535248a6516ca0264f83f646452eb0d63df2b32636c94f66327452261ede056616ac2cf60c081b760868aa2607c1314602bb2d35f718eae5f5eacbf5e8b8a475d319ff65ce950475cb1fe155c86ba0f5c64cb105b1320aa5af05dc15aa8f55e5a3b12535a3976715a217497
  | 6, 0, 4 => 0x9a7ddf2497a784889750518c96c7b6a496c18c5696b0156195805ebf94b018d3944bf0e69391693f934bf6d892411eb0917242ec912f1e3990f41f1790efa8969000e36c8f35e3838f346e288f1a8e3c8eef91248d2c30e48ce1a1a98cac943f8c3cd7b98c3abc918c0b847c8be0a2098b937bba8b8de4ab8b15b96f8af066f98a34f76c89f5a0118888c9e7882f52c48825b57d87bc307387b05a3d876bff368755af5186e18ee484fccbd18498e7e78443baf48402af93823172d882079cb0813a70018106bffa8103242c8085455380674d897facd5a97f5540ab7ee125037d8db0117d7c07117cfebbc47ce6cbbe7cd063437cc317d07c644d9a7b958da5
  | 6, 0, 5 => 0xc0582317c021bcacc01b919bbf9bab35beee9473bebd2cbbbdf46bd2bcf879d7bb53afffba694640b97fc8ffb864725ab7edea51b763de43b759ca51b6811421b64ff35db5da9890b574c2ceb428acc5b3d0ece6b34e062eb2f3534db2b1c5a5b0cfa838b099c290b018c14caf885bf3aeed0fc3aed08696aecbdfe5ade53914adb0c883ad70d8e4ac9ab39cac41a57eac269518ac251fbdabb93556ab8f0c02ab581427aac7e744aabd402da96b029da947c278a8fc3611a89428dda80de02da76fe7c7a75b00d7a6f1e3d6a6b9e07fa5da4240a5c1ad00a504e9e9a49448e9a2e2833ca206e2779eb63d339d2cf5e09c8f176a9c23eb979b24b8349adefea8
  | 6, 0, 6 => 0xe23acc48e2262981e221046ae2165b9be1fd7feee1776e77dfe68bfede6f49b1de167681dd82b20adcc9e4eedc646bc5dc530cc6dbcd1d99db242495dae5b725dad7d7dfd9f9fb5ad973e9e3d910a4e9d7c8ad1bd73fecf8d708d53cd68a8ce6d5d6d97cd42f64bed41e9489d4171a0dd3e83490d3d6fe7ad3d67d76d3cf3014d39f70fad389964fd3315ec6d215ea13d1b33d20d169122dd11892ced057efc7d02ede41d0006acdcf54d149cee14481cebcaa6dce8d2592ce6a62a9ccd97be5cc22a61bcb8bc7facb073168cad7f953cab7206bca58b31cc8a301e3c89d7b8fc848c5bcc5fd5e6bc4d6fbcac47d0f4fc38ac4d3c3573493c2d474bfc13d5ef2
  | 6, 0, 7 => 0xffb0d7b7ffa4edfbff957eabff59a130ff16db16ff0d80a2fe68200cfe331010fdf9659afdf4a2a0fdbd7d26fc4b0b8dfb6d2ecffb557527f9a8b337f9551d5af8d361cbf850b6f6f84d177af7cf2a9ef69881caf6649b78f61649e1f5dedc51f54d88f8f496b32ef3cac05cf37b3e7bf2c78b11f29d61bdf1bcb5e5f0f90680f0d8e625f0986daff021fed5eeedead5ee73db6eee530286ed64ae15ed0db871ecf11c62ecb1adebeca99953ec4582deec1b0274ebf99862ebd6ced7ebb29bcbeb9cda82eb3293cceb1a9bc8ea99dd29e9153832e872ec00e7455612e59d38a3e4e943fce4d4de3fe4ae2957e426eff2e39955ee
  | 7, 0, 0 => 0x702eb1b06e0c14b06dc1cba06b2f97806a9d42c068d4b130682030e0672c3e80628affa0612865805e90d4b05d78d0e05b329cf05b2eac505ab6a77058f39b4058c7df80573298d056af0ba051d92c4050cdc22049fe5830489cb8d04734679046531a9041ebbc80414a8770402104d03acc1d5035dc2d90335143e0331cac60303e9c302d338cd02b9da3102a7bb8302a7a996028e48480244bc38023e56a50229321f020343d901dfe0b3019f51af0183aeef017d5a38016d7b82015f4010014ed352012ae19901271ba701189fc600f5391200e0ce0a00d64fc300a5776700924263008576e5006e43f5003aa60a003649a000252651001c45a1001528ba
  | 7, 0, 1 => 0xd7fc1df0d52fdb80d4180e80d3f58fe0d2f75e70d0b05da0cdeecc20c9f1b370c7515ce0c4d96010c405b110c1b94cd0bc598650bab8a350b45d6cd0b236e970b0d59c30b0d46330b0965080accf95f0ac78f9b0a868e460a75aa570a6b59eb0a5db90d0a5133e10a4ca9000a2d480b0a0eeb5709ca1cde09a8b18809951e78097d9607095537f9094ba77a093090f1092d9a5f0918ed40090b2c30090422d808f88e9108e3b35808c04d1d08a8fb0e0889983b0883b66b087d4564086df8bb0869cb9a084aa39808359101082a1dbb0828fed7081c4a800814753608028ac807d4482407c6446507a1618d07983db607852a5a0735b008073325e0070b6e27
  | 7, 0, 2 => 0x13d693d213b478a213b13c8e13aedd491383ce791357233a135185f913495b611345c7c5134279a9131fe96f12fb13ed12ca7d2a1288b046126f0f311267856412660b0d121c126e11c9fc5911b4999e1194d57e116cda671158bc8d1149f2221148cdc7113fcc38113c00b6111b7f221113be0a110fc7821105561310e737ec10dad07310d730f7108cbea2107c28dc106602d21056c74b10391595101cf3100fe6c67b0fdf613e0fcf05c80fb89c5c0fb19ba80f99453c0f8fbf640f713d840f6a88660f5896ee0f4449ac0f232de10edc4daa0ed51c0e0ed4fd100eb3ce750e68f5ce0e5684bd0e41de8b0df8e8330de9ba4d0dd6cf3b0db6ae630daeef0b
  | 7, 0, 3 => 0x1a812e9f1a76b50e1a39cc121a141c851a0a201f1a0397ba19ed676819b9c86819b45c2419b22bfc19b15e681991f46c198a8534198257a319763e0f19729319196c97d4196926bf195e483819570811194d07b4191c880718f5929718f4e10a18f4153718b26e22186b8f5c183e4131182077a418054bf517d900ce17bd685317bc20f017a76cd417a485a01783d36c1769b9701747ce4016c4ecbb16ab874c169c9370169ad4dc1682538b165c88241658ec561656f99b1637db9c161b607615e3d4b9159301331578ae8c15736fd7156f272215554fd0154ef37814fbddd214d1b9a314b7c4bd145be6f1141a49b21405939c13fda56313f695b113ec0a33
  | 7, 0, 4 => 0x21701c68216845b421677a5121638c9c214d3e85212934402118d8ca2112506520fb4f1320e3556c20bd10b420bd045520b6d82820b45b6820aa522b20a269f0207787b8206d00e32069571d204cfb9c202b40b22014b8842011cf6420044b421fd503bc1fcef5c61fa9b9161f49dc541f0910ea1f0257501ec8714f1e85d81f1e546ac11e0c97d61dd9276e1d64beba1d2710f51d1a31a91d0839f91cc1c7601c9476741c88066d1c7f660e1c54452b1c1160c61c0377111c02e4e51bf4b44a1beec3151ba9074c1b9b06e31b8f8cf31b77905d1b7725391b5aa7ce1b23c71b1b0c122d1af7262a1af0de741adb9ef91ad576b71ac66f081aa0a2381a939d13
  | 7, 0, 5 => 0x2a2f82d329d34d23297cc0d4297400f82935e7462920d6ee290c466228f983f828e0b01128c771b4289b697328992b9b2841347c283f1c4d28318577280f289427edaeb527d8185027d27a5a27b0b5e327af0de927a2b1ad2795024727872db92773e4862726dd4726f1d260263b8e072613f6fd2613f5a22601ac8525f197ff25ce605325cd4ba525c5d19325c57f882579fcdf25613c152521c3b825029ba324ffd71f24f506d224d5ba0324cb8b552461748c244f7a0a242a74e0241a19e723a5583523a12dde2371f15e2363757d234fd88e232fdfb722f2b39022cfb361225735b92246227221f0ebfc21d6d25821d64afc21c06e8b21bffba721bb080f
  | 7, 0, 6 => 0x30d17f8130b4684030b123c530a99e14308ead5a30888249304e44793044b910303a5178303247ff302f8f99302b6e7b2ff39f242fd90f922fb4080e2faa7f832fa9bd1b2fa732f32f775b232f76da822f4cd03b2f2d333f2f2664432f244e602ef590472ed106232e94ca4f2e8270162e7ade792e1f778a2e1313d52dd5e4112dca65fb2d80e9352d6782ad2d48cd4d2d3304032d0b08af2cfd4cb22cd9989b2cd48a3e2cc710002cbfb75d2c60eef42c35d6762c13df762bfb4c212b9d09942b94eb122b3e9fc02b32ee6b2b3290202aff1c0f2aeff1232ae6ef722ae3339f2ada82fe2ad3cf392abf74ef2aa950482a7e41a82a71ab6e2a5f79ad2a3e9862
  | 7, 0, 7 => 0x36817d763675237c3666efa436607174365b88e63622fc1e3620a0303600263635db239335d968a535ac22d8358f846f35895b043579dda73576bc213565de74355a85df354c0f9d35389f973532e67c3509393734e922e134c730bd34c3851934b3dda734aeaf2434adc67234a4326c348ee9a334647388344e166f343baa9e340c055d33b8069c33b2c29e33addc96338b145733885092338166d6337fa1c6337098c0335a9b0e331102a832dd24d032d4864e32c69f3432be679b32a1551e3268995b32681bf431eb022d31c32ec3317dda3a316e3c87315708a13152907e314f8557314ce6a131345a30311656bb3107d3ae30f9ec0330dd2abe30dac114
  | 7, 0, 8 => 0x3cf888fe3ce8e9cf3ce05b1a3ccff6cb3cc208833cc117773cb7623b3ca51e343c83af333c7bdb083c771e663c71b2763c6977bf3c5fea2a3c5cd0913c4b2c0a3c2e28d93bbb8b303ba453603b22fa393b1fa0fa3b1437703adb92773a99cd023a8906683a6372fa3a39bf7f3a36b6f73a1a9e3839f2dbb639b3d94b39ad638a39912610395f96ae393738c1392320c838f9f1d038c12eb938ad22a838ab9cc13899b8e138910023387cf5323865c14c385e3e02382d8f77382ca96f380f69e337f723b837e0382c37bb71f83781b790376a4f69375c328c37505abd37492921371be0213709d18b36fc90e836f914db36f64b1d36d7b87036ca91d036bba0ba
  | 7, 0, 9 => 0x458feefb457649034566e491450d58f6450427cf44e3171544e281d0446609b64458f2cf4448bf434421a80f441fad5c43ff470e43d3fa3d43cfd02243a70ae54326ac1e42e48510427e2d324277a4cd4266f78e424dd2bc4222f01b41d2554b41c3487d4190951a417604ab41699faa415b109441588a44410ec54a40ffb32940e06b1a40ba3bb3409484b740811af040302e03401b4829401ab5ae3fdb14c03fad42e13f9ec7003f12e7d53eadf8b13e8136503e5d1fd33e51fe3b3e4848ff3e2a98cc3e294fff3e2424c43e098a5f3dced0b63dccbcab3d71fd593d5db2783d4d40833d249fa53d2434913d1f58a03d1bf2473d0e653e3d0e5bb43d0508da
  | 7, 0, 10 => 0x4d7b070d4d6d7cb44d2885244d1a63024d0e53624d025dfc4ce69ba94cdb51174cae6cf64cacc4fc4c8d80f44c63c6984c35789e4c3021524c1de4d44c153af14bfbeabe4bef9b8c4bcbca9e4ba3ecca4b6d7f204b4480574b3060ba4afc9a304aee95694ae58e0c4ae0b3c94abb17904a9c663a4a9b3bae4a4cbebc4a3408ba4a0491ce49f1948249db8764499f41ff496f5b4948a30f48488dbb29486b9cc54860daab4830af3347ef23c547e5621747a969a647a0981e47989971475aa13c47449f5b473a9da3473a6d924702e8f446f3f1d646da15bd46cfadf846cd9c5046b17d4546a5aa93469151e1468e95ab465ec40945e428f445d63c98459ded53
  | 7, 0, 11 => 0x53c3f8a4537f76e65363fe36535d66b75359b3fb532862f0530dd69552fe543752f219fd52e515da52c31b2852996d67528621785281da56526f455b52368d01520b52db520551e451db4f1a51d54e5151b94a615194e40151529dc4513f899f50fcb6f250fc017750f4e59f50ebe3bd50eb246750e8874550c1bb7d50c1a5e050a7d0d150a374335062f21b5047ce895040d64c503e3f224ffb3acc4fe884164fd65b6b4fc4d3114fb750c94f85907a4f1c75a54f1775264f004b644ee29ddf4ee201a54ebdb7684eabf50f4e83672f4e8225634e4532634e39dea64e31041e4e2e2ce84e19c9cd4e10be834df9f4364defa2b84dbb014a4daa25224da171e7
  | 7, 0, 12 => 0x5a910ab55a69bac65a5fdbb45a4109985a2cc3f459e2499a59d8d2e559cb15b459c3926a59bf3e13599470e7597be0c15979ab67597460c8595bb8d459458c945926dba959253d1f5922ec465914aa69590f36fe58c2518c58a6551258a0143c58871ddb5874c9ef5867afd6580aba2258039e4a57c0dd4e578a7e97577c15f45735f67a56f67d2956f51c3656ac910056a3343e569e151f5695158656590b955649f1245618a06b55f8209255f262bd55eaa36555e7a0d655b28f385593c9de557784d6557159c5556413d45518170655073dee54f1735f54b83bed548e179a548547b35478803b54617bf9544daeb9544d5c36544523635431b23f53ed427d
  | 7, 0, 13 => 0x614941da611cde0961170055610788a560feacb060dd8b7660d6c19560cfe67b60c081b7609fe702609ba710608f0109607f8486605c2bfe602ebcf1602bde88601d50b96013f4555ff7d54a5fdec53c5fcd3a315fae7b465f8fed345f83829a5f66e6445f6459b65f3975ba5f16df6a5f13a1b05ef7b5895e6d15f35e4e7aea5e4d75b85e3d32e05e0ae56f5e02f9755deb6f4c5de9039b5d995c535d7fcda25d4631575d37922c5cf0c0825c8704475c7c04cf5c46243c5c09a8905be538835bb3a9b85b9966485b850fbb5b799ad45b60eb4b5b4c7f215b3983f85b212d615b0dbc325b0d3dbf5b0631845b04eb6c5af228825aef23a75aedf30a5a9cf1fb
  | 7, 0, 14 => 0x6795ef97676ca7536767de4a6742a7d3673d759c6722ad00671b739667103ec5670425a966f87fdc66f5436366f41fba66c18c79668c78806684c085667cc29c6678e449667312616658320f664bccff664a2e4d661f5eb7661766a565d993e365d5f467656b230a655c4e5a6555e603655258d66536bacd6535248a6511e6c664bb1a6864b7656c64b3ca6064b073fb6493563e6483cd40645d37e6644d15206441f1ad6438425e6412729763fe5a4f639d7a8163965c28638844836376351f6374814a635f225d633cbe4b62fec6b962e9c1c962b0c67b6245d479623a6240623567bb622d0e0961ede05661d9161e61b0ce8d61a2505e61727cfb6165648b
  | 7, 0, 15 => 0x6f1f7e7a6edf7c9c6ed3404e6ed2d11c6e9f61156e7696f56e74d7686e6dbd796e6656486e62b4746e310df96e2a2c416df9a8166df1abd96df0fec26dc5812b6d87aff76d71deff6d7144946cf10f6b6c96dad26c95b5226c6b07056c5e9d666c55ce416c5367486c453e1d6c3019736bb6c94b6bb38dc86bab9a0f6ba0ff156b6f4ef26b3017626b0b5d396b024b4d6ad97ffd6ac8f5be6ac5e7666ac4e77d6a40fc8c6a38ec4f6a161b4269e9125369de091c69c02cf8698f8f77697828dc69658b7469548d246954782d69506ea26920629d690b0d3968ff83c268f8c50e68e5b1bd68bee2ec68badc8d68b10909686021f66821124f681eaba8679b2929
  | 7, 1, 0 => 0x760b277675f001ec75ec322d75a42d4775a337077590c5d1753c1a0574fb6bb774ee7fdf74dd2a1a74a892fc7490c7ba7480d247747215127463a89f744a6a427440dbf1743b6ebe74381a627412504373e7ee5673b111937370a743736c3eab7366785c735fe38773536d5d7334bc727322a3cc7321729572e3d16772d87a3472ba3b1172b857c072ab5f4f729b2e07727e079d7278be2071fe46de71ebea7c71e224f471d3a02871cfa26f71cce63971afb5527162bd45715f6ccd715adeae70f7e40370cd5ae470cb1ea570be612170a4bc46707653cd704a6590704a4f117029630f702759d970228aea6fef05cc6fd9346f6fd5c76f6fc2e2136f43ea97
  | 7, 1, 1 => 0x7dd241b97dc7732a7d7ff2037d6efcf87d6e9ad67d4a419d7d347ede7d0c8cbb7cf70da37cd5890c7ca027e27c7f02d67c3f68397c3b9ef67c2395e47c22fff67c1cccda7bac4d1a7b9f80657b5f89e47b5ee8917b3164647b28e4477acb8d727ac3e1087abc8b8c7aaa9a147a98c0657a8096417a5716df7a10de7579ef6f1079eb7a8b79b74c7a798382f17976ef1679700e8a7968f2b2795af538795752d278fa5a2578ebe05e78e4f5a278db4aa8789e7b0c786dfc597860e639785c912977ee46d777cfa30e77cbd18277c666a7777857d877496a09772ab2d9771e700576f1fb2d76e3013076b692d376acad037669dadc765f42f5764e172f7623de9a
  | 7, 1, 2 => 0x8577d8858577c6ff85721f6a854e5260854cb0a884fccbd184f3169584c3814584a52c19845c63d284582d5584366cf7841cbaf984135e9583fa8b3383f73f8a83e1369083b647ca83b31a7d83a7f6e4833e6a86833c7e9483324e8f83079e278302b3d682c9e5be82ba668281eb355181db201581a29664819b4b0881975c2381704eb88168cc8a81450cb28128f3f380e8d70280b8c97c80b18522806943d180458e7c80446b3b8032d812803070bd7ffd68267fda735e7fd996ed7f34c9357f2d59fd7f21f4997f1dbf9e7f18940b7f05a1247eeaeee67ec9c7b37eb814087eb3423b7ea0a7df7e6b005c7e62c7897e5eb0787e151cff7e0700227e04ecbd
  | 7, 1, 3 => 0x8be88e5d8bd6858c8bba63a28bb9cc5e8bb2b8e58ba664528b7f50dd8b3a1cd38b34a47b8b3227778b1d15ca8b0ab19f8b0551fa8b04dcb88ac1d3288abc62618ab9e18c8aac706d8aa2abe88a165d718a1656d289fc41b189c7447a896dabdf896336f88952d794894e9e1a89469bc48931321e88d4431e88d0391188c8f86088a9727788a2ca0488880168886be25d8869664f8867af228856fc838833f55187e8f73b87d866c987d4247987888bea873c288b8738119c86c3604986bb989c8669e687865fd91e86453eb986448212864120378626c9b8861a5c81860c2be6860858218602dca985db428985cf5b4385c3ded685b6fcdc85b3ccb185a3bc0f
  | 7, 1, 4 => 0x9323bdfe92fb6e8992bb609592813d8e92646ea39263d170923924e7923619c092352ad9922628d291ecb7d991b813ea911fadd9911bcb619112e78990dec3a290a4b5609073fab89061903f905037549032bced8ff96af68ff3586c8fdbeb5d8fccc2048fc876348fbfa2c28f8f80a98f8b65ae8f6eb9328f69047f8f2f8aec8f20ea1d8f175eb78f0950aa8ec451bd8eaf7f208eaae5848e46ca478e3d634f8e3987468e3270a98dd05b6d8dc02d048db1fd5d8d9225708d8425078d7aed198d76345a8d2c30e48d27d7738d145d498cd297818cbb13f68cb5433f8ca6ef548c94a7298c839dfd8c7b7f7b8c3afb688c127d8a8c0b847c8c096b588c03c8b1
  | 7, 1, 5 => 0x9a7253f19a67f3379a47b1c99a2a447c9a1dcd2a9a1c8ce899bb987e99b83634998bcfd1996dd3cc996bf0539944d26b99243b9f990ffb6b98fd6fd798f5fe4c98c6cc9598b76a5d9836ef269811ba83980f33cf97fc608297941ecf9781008d977cddc1976c89139765e29c974a5a3997482fc9973b0d5496d72ef996d0132196ac7d51965c9589964c72dd95dd264195c7433b95b99e2f959ee858957fdd3c956af0e49556175c95522fc3954d6df6954a07bc9522500394ea215094b0dbf19492ddb294872291947f040f9437159c941fa7229410b3b793e35c0593da0a2093c3b93993bde83693a98caf938b73e29353153f934ff48a934f2dc49338f490
  | 7, 1, 6 => 0xa00525279fec64eb9fa3366c9f8844ec9f1dec7a9f1871cb9f135f8f9ecf60d39e5fc3239e52ceb09e4ff7719e33d4ec9e08b2919e0665df9e04d2e49df4f9a79deb9d439de0fd1e9dd249f19dcf7e389d9fc82e9d9b72049d97ea119d5b48799d3e8f329d3df8079d1bdcb79d17c8749d14bd429d04d4cd9cf6d7539cebfdea9ce83a339ce2885c9cd5fbe69ca6bdbc9c865d569c80d7bd9c6d66999c464a4e9c44bee19c31e4e49c26f80f9c14133a9c0635639be5eaa99bda856f9bd4a9df9bca85189bc73dcd9b7787f89b65def89b5bb1f19b53791e9b52b2589b4c7f429b2dce579b0132a19ad61d679ab8455a9aa960819a96a5999a91b62d9a8bf7aa
  | 7, 1, 7 => 0xa7352dc1a73369e3a71f544ba7070867a69e95f1a69a1caaa697cd48a697208ba6892a12a67b0d35a640a41ca6375980a61de4fea5f66f26a5ea9f91a5dd0329a5d302cca59a240ca596fabaa593fad9a54213c6a53f8738a51841d6a50155e6a4cc9566a4b7b929a497a2f7a49090eca43fb11da3f6f2dea3dc3944a3b74bbea39c9fa5a39854aaa32d150fa317fe4ba304b735a2f38e3ea2ed028ba2c58cb3a2b50c6da2ab898aa26ac316a241a4fda22151bea214873fa1c22db6a1b636a0a18ed7a9a15def42a13bd84ba101dc92a0f982e0a0e2096ca0ca5129a0ba2447a09a887ca07e6740a06bbb55a03a73baa0353164a0230024a022680ca01eb416
  | 7, 1, 8 => 0xae49084eae45eeb5ae37ebe9ade8f265addc392fadbb5be8adb1d04aadb0dd5dada685f3ad8c73d7ad70d8e4ad4fb26facf6a118accc3a68aca5b365ac77f2fbac584a90ac451088ac272790ac203c81ac139c47ac08d977ab9c9261ab7bab3aab5fb83fab377bdcaaeb2637aa98f8b4aa939139aa82d705aa6baa8baa5f4264aa4f8b80aa452991aa2f2ca6aa26b1caa9c34916a9925c3da97724a4a9536d8da94faecca927f774a917ebcda8fc3611a8d0e661a8c77f14a86f31f2a85e41a0a85b9c23a84135a5a8255610a821f9f1a82101fba7fd1eefa7df1306a7c8dcf2a7ba6418a7af40b0a78974f5a77d7de0a7752a14a76199bca74efc98a73eccc8
  | 7, 1, 9 => 0xb5df9bc7b5de5852b5b461f1b59cf503b59bbf22b5902909b579183ab554a760b533f09fb52bb7ccb4d28f2cb4c9c506b4b7ad7cb4abb72fb44a929fb442d94eb426fbacb403b48eb35a2bf3b34d471eb33dffa7b2f35618b2eeaacbb2aa4fc4b2a359d7b274a0a9b26a3914b23ccd8fb2395506b22e5d43b1d74b79b1c6e4a7b1838f47b1776664b15c16f7b158ad0fb14a7c74b1498684b14872c1b146c193b0b06ff8b08645feb0772feeb0728791b0598918b044ba39b03b1c5fb00c731fafedb434afd6dd83afd5efccafb5dacfafac1eafafa392a4af7e5c2daf365ea7af2bc6ccaf0a244eaee9412baedd696eaed207f3ae8e3c58ae619b76ae5db543
  | 7, 1, 10 => 0xbc8cd216bc885194bc4e1733bc4e049dbc1d99c2bbfcd59abbecc5edbbe6e79bbbc7133abb9554cdbb7ff28dbb5f66ffbb49c479bb47bb4abae435a9bab4727abaaa26d3ba90fbf4ba6ddb7aba6bf53cba506113ba2fc850ba2c20fdba28212eba1aaad3ba0d7012ba0bd188ba0a4a0bb9f8020cb9d56a55b9cec865b9b21282b99a9a36b941a5deb9238bb6b906d2ffb8fa157bb8b97ddfb89bc33ab886036bb87a7005b877b3cfb7dd1192b7d97460b7d57de9b7a8f6efb737b8cab71ef297b710c514b7043cc0b6e2d1dcb6c4937ab6b24b4fb6b17062b6b0f2bcb6a9ab77b63e8ff7b6358400b6355c70b619f45cb619a837b60754e6b5f8321ab5ec76f9
  | 7, 1, 11 => 0xc33155b1c2d474bfc29f4858c29e518fc22fd643c22fa591c22b236ac2223b36c2157f87c210f4a6c1ffdce4c1fd94bec1de7afec1a1f633c18fbe0fc18ac36bc1881394c184087ec124aa0ac10c93d2c10593c9c0e7a473c0b58cbbc0aa5d7fc0a7fd53c08340e2c04efcebc0429fd7c0324461c02871dec0167737bff50da0bfe09626bfcdc6ffbfbe674cbf8928b0bf866c7abf851e63bf75efa6bf666733bf1361a9befb92b4bee8615dbe937088be8a4766be695d85be4929dbbe3b504ebe159bfbbe04ba19bdfad6fbbde508e2bddfe1a1bd5c6ceabd569d44bd53855abd16353ebcf80b4bbcf03cf9bce0ee17bcd904bbbcd3a035bccbccecbc8f7c91
  | 7, 1, 12 => 0xca30e3fcca011952c9f8ee7ac9f3d846c9ea6d51c9e8e892c9afe55ec9ad816cc98e47ffc978e544c96fe6b4c93615f1c92e315ac92b194cc9240959c8f98b0cc8e2cba9c86aea85c81b12f1c8144c74c7edc099c7e9b3cec7e4a5b2c7db80e1c7b9162ac7b58e37c77e063ac775e74ec76c6475c75da8f3c75aa013c72a8082c71fc81ac708d5a6c6d90c65c6c87980c6aa6d36c6a09950c69e7be3c68acfd0c64ee270c61d4f36c613f6dfc5f87b2fc5bbbdecc5a7e8ddc55c4746c553eeacc532c1fdc4cf5180c4cca2acc4c83208c4b98e87c489c356c47d52b3c4775350c4588134c44c184fc43bc065c406c3f6c3f04a81c3975ae4c3827a75c34759aa
  | 7, 1, 13 => 0xd130e37ad111535ad106b24ad0f8af51d0f3126dd0d24eb3d0cfa936d0bc3a17d0b92cb0d06fa9abd033f968d000bef7cff42cabcfed907acfd29977cfc309abcf73c5f6cf2e0516cf0d0abbcf0bda5bcf0b2d9ecef74cf6cee52cedcee27a34ce9bbdfbce20d3cace16f6e3ce0b07cdcdfbffc3cdef810bcdcb422ccdc22ffacdaa44eccd900d75cd52d7cdcd43454dcd359d45cd20b155cd18a10acd083060ccef4fa8cce6e03ecc98182ccc7a28d9cc5dabe0cc5b0663cc42fc48cc32d0cfcc247446cc224b71cbaf8a27cb9f0c58cb9adf78cb7d8f0bcb7a5a8bcb78c448cb69ce5ecb349801cadcbb49cab12130caac0d7dca546425ca537f57ca363ac9
  | 7, 1, 14 => 0xd808765ed7d25a00d7c698f7d7aa6bbad793416cd77efc9fd75e8d0fd7461506d74112a8d73f0427d734ab98d719f753d702496bd6f1bbdfd6e2b88bd6cc8efcd6b9fbc8d6827ea1d6683848d647910fd64187a9d62f196ed61a4d78d5e6dcbdd58f2765d56908f6d558a97bd5484081d547dd01d5220327d5081364d4f48f2ad4f0f799d4a3bcb0d4861306d44c5213d43a869fd41890d1d404f3a6d3ff0dd7d3f580b8d3cd493ed3c5c492d3b30ebbd39eec29d36d52f2d35f5289d358ca24d313bffed2e42213d2d4b27bd2a6e32cd2a60669d28da698d28c47b6d257e8b9d24ac501d24558f5d23889ebd21ac315d1c7e360d1b1b30ed175aa0ed16ca0be
  | 7, 1, 15 => 0xdeeb28eddeb0d72fde9a8e22de9849e3de91cd35de559161de4dbcd2de49630fde3eec65de3e5923ddea6151ddd031a2ddc76448ddbeb597dd92abf9dd768b6add193586dd09945fdcf66048dced4dafdcc2d6ebdcbab869dca985b1dc8e32f7dc79da45dc56f92cdc15be7adc06615adbff3966dbf99c90dbea5838dba270bddb7c6105db3dab48db1766eadb00be62dab6ff36daa3ea24da6a175ada61dd2cda067d68d9df23c3d9d3059ed9bc7fd4d98f9349d984ba31d95b6233d94bf1b5d93d87e6d916e5cfd9137c0cd8f77560d8ed43cdd8d69c0bd8c624d8d8b63777d88137bcd873d567d8316a54d829e7e2d823951fd8179fb7d8114742d80e38fa
  | 7, 2, 0 => 0xe85a7ff3e7efba21e7deeac6e73ba6c9e7311744e72b167be7253829e6e489dbe6a00801e65915f5e652343de626c786e5f2c308e5aa15aee59d96b3e56e18dee56c185ee54da510e52648e8e5159907e50d18f3e4c211b0e4aea01ae4a9c7bfe4a63fcce46f7636e458c67ce426c48de41a242ee4052d0ee402f227e38f2d78e341463fe30df211e2d32023e2d1c9bae2b96760e2af43c4e2a3a791e283c095e2785dd5e25821fce2128133e20b1b97e1fdf0a7e1f74cd8e1e47322e1d915bae19798c9e1560784e1410c7ae0ee7d18e0ebc0e2e08a5211e04d6edddfec358ddfb96348dfa83d6ddf99d6a4df739b43df66fd53df382235df130c3cdf0bc77b
  | 7, 2, 1 => 0xee396f22ee343295ee30e0bdee23135cee18b783ee12c54dedf34286edacebaced8d83bded7dc820ed7b3b92ed333564ed2a2a1aed19e3bfed105b43eccf22c6ec96029dec87d0bfec83f7cfec72facaec6e369fec663512ec65e546ec20b13cec1a7a9bebfd1c1cebdaeb21ebd8a273ebc63093ebbb66bdebaed3bfeb9304d6eb7e1f2aeb72283ceb406b8fead54e4eeaac3b0beaa78c21eaa4b7c1ea9517a3ea8706daea6c0015ea6043fdea5d0618ea080100e9f1eafae9d0ea74e9a376e3e9877a69e979a0dce96a477ce963f38ee9430aa7e93d90ece935373ae92139dee91e6a92e9060583e8bab8e2e8a202a5e89fb0f7e88a844ae881f5cbe86884c7
  | 7, 2, 2 => 0xf5118c29f4ee35ecf4d2a75af4d0f0ecf4b303e2f4ad3575f4a423e9f4857ffdf42435d0f4211c37f3f19c1ef3ee0630f3a1f4fef3733036f36d6c95f367d1f7f3201a90f2c10465f280ddebf264f3cef25261f5f2218e7ff21bf636f1f4b290f1ce1097f1b84c83f1b2d8fef18b6326f1784439f173b0a8f16d981ff16191faf153f5cff153a027f1411580f136cbbdf1350785f11de759f1195156f0e61da6f0d81ed1f0be3d76f0923f3af08b0e3ff0857a5ff07b02c5f05e0487f05ab396f05897d3f04f03a7f041e202efb9323aefaf0f89efae69a2ef3e65bdef335fc1ef2e9b0fef14a663eede5f57eeafd98eeea09446ee876a10ee4c34a6ee459ecd
  | 7, 2, 3 => 0xfdb3f8dffdaefc54fd9d02e8fd90ee05fd676c26fcd4c3e5fcb2c7eafc8bca0cfc093e8cfc02cecffbeba59dfbc60337fbc1bc8dfbbf59a1fbbcb1d0fb88fb78fb6d2ecffb6b568bfb3e6e67fb2e4632fb2a5f25faf9a1abfacfb439fa9321d7fa3bf073fa11d0d1f9d2155ff98630cef9611aa0f9552142f93a5051f8fbfd03f8ec2452f8dbc959f87cb44af848f742f8456696f82e5cddf82ca004f82530ccf821a1bdf8037aa5f7f54a0af7e7d309f7d8efe4f782419cf781aefbf7717167f7712f20f760f6a9f75ba0adf750e12cf721c153f68e4a3df66671a5f61649e1f6144ec5f60e6587f5e05daef57ec026f574dc78f5635cbbf5373f08f5325572
  | 7, 2, 4 => 0xffff0634ffb3113affaa18f5ff9ff7b5ff9b1b81ff640b3dff58e3f3ff4da10aff3d1588ff123350ff0402b5fee6a5c8fedd3cb7fec7e6ddfebb539efe971ab2fe82066dfe7e7e7afe7dc54dfe6faf54fe69f639fe52e151fe282b53fe24198cfdf0164bfdeaed64fddd6bbcfdbc4d94
  | 8, 0, 0 => 0x240356ad23937e852326239721a9023c2136416c20bd10b41f505e561eb180c41e21c84f1da0f8bb1cf1298c1c8d2d2f1c7f660e1b9b06e31b54b30e19b15e6819959b0d194d07b418ed5c0818b98c2018097fbf1773f9151742223f172371541703b38d169f5cd9155b0707147be17a1444561113b478a212c7ac7e128177ed126f593f11c9fc59111d5c611106cdc710dfc44d10bcd6ce0f1c517e0ecd7e060eb2ba8a0e532e160de1f81f0db6ae630d359d660cda57470cd4669f0b8bbf6b0b15b6280a5133e109d69a71092808eb08cb2a3508719fb807f0d02407a389060790ca2a07540f0804be9b5d03e572760355f04501c0cf2f019bcd0d0132a60a
  | 8, 0, 1 => 0x4c50a0f34bba97004b0d46544a258bc548a30f4847c656fb47aec13b4749554c4716cec6465f78f84541e848452bb7f644aae862449d41de44333198440fed9243fdcee443cb072843a4cbbe4307780a424b4c73417604ab414c6349411da5b7409e34a4408d44063fd242ec3fc0243e3eb72f933e0da1cd3d9cd9ed3d41059b3c79d3023c5cd0913a1a9e38376a4f6936aa157735a9aa79352b3a5934bca48e33c0c90033ac49493265f79931c32ec330cd8a4230a9414830452eee2ff1212a2f1583e82dbb214e2d6782ad2cbbaac62c9d909e2b5379482a339e292990644b292c0d9728a5bcb427d93e0026c74c062547379b24c639ab24ba3ed6244d7067
  | 8, 0, 2 => 0x71e3fb2170e422b070821968706ffaba705b2132700149d46ebd78496db5f55b6d6ed5cb6cd46e566c96dad26c8cdfa26bf5ec266bf2d3266b3d020a6aeac5db6a866f27690b0d3968f8c50e688b911168273a5d67360e8c6716b473664b1a3364ede01564bb1a686438425e63ff7f4763e020e4628eab4b621b7fc5620d6f8d60bf4dc9604bbc7e5f938c875e6214035e471a635dfdbd4f5c0fa18f5b8a9b5459428c4e58652e3d56cdce4e567ab1f45514da2a55119db15400b90d53fc1e2653ebb6ee532b31af5310cae852c6dafb51bbbb75510cb0e150ba5f8b50a840dd4f4e6d214f1c75a54f01e97c4ef5be6c4d476b1d4d2f3c8a4d2e4be94cae6cf6
  | 8, 0, 3 => 0x97de4ccf97b3be8397a2ad889790a9e095cb9afe959b5dd2956af0e494ea21509492ddb2948431fc9406f9df92bd4609923c767590dec3a2903af60b8f87e3d58ed4acb68ea1b5b78e3118c78dbf9f568d8425078cb80d3c8c90870c8c53b6888b9a7c8c8b3625d88b1d15ca8ac1d32888c8f86088c3fb8588a3b6dc86bb27768646d6de86448212861b4d8585db428985823cea84d0ab2d84613cd483b31a7d83490ab082fc963681a2fbbd8128f3f3801c3ae37fbb0c1d7dd7bdf57d57e2b57c3a52057c1b050478e4f5a278d7caf17673e45e7663a7c67651891876374ac775a3370774e1c74f749f06a7749a204b73f742fa739f2b3972f58c2c7278be20
  | 8, 0, 4 => 0xc3753fb4c242cba7c2157f87c18ac36bc02126d4be2c3e52bd95ab3dbd541193bc64b401bb67486ebab4727aba53eca2b806c79fb7acf0edb6b375dab5f8321ab5e0fc76b5611d4db3c7f7b0b25ec8e9b1838f47b14a7c74b141b29ab0b06ff8af359018af1d0a4eae6ff2a8ae5dd3faada97aa9ad48081dacab5189ac272790ab2b8525aa70fe3da99d0106a96bd003a9536d8da92e1f67a91c00b9a8aceb64a7697e48a61c3eeda57263d1a54e664ba549f6c7a4c9dd97a4c92733a4ae5f18a3ac4ce7a38fee89a304b735a26835d3a203df1fa184c90da0bdc985a039bc459f9b20929f36c9de9c6b500d9b4c7f429b0132a19a80d3c498e639c8989ed467
  | 8, 0, 5 => 0xece124ddeccf062febeba476eb8687baeb5bd121eb406b8feb1c83beeac36ef1eaa4dc92ea5d0618e9877a69e91e322fe8a9e5dbe892c0b4e78c552be72b167be6a45857e5685c65e4ee680be445238de3a3bb46e337d007e2182b15e1f09bdde0b0bd65dffd34ddddf5fcc6ddb2f137dbff73e2dae1e332dabcacbbda1ba67fda025fd3d99ad6ebd7c1c93cd676da41d58f793dd4034cd6d35f5289d358ca24d175aa0ed111535ad0ab1f49cee4c42bce16f6e3cd79adfbcd52d7cdcb78c448cb694c08ca5896e9ca1e5d15c98e47ffc972257ac90dcec6c8f91191c7fd48dcc7bf284bc7abb727c6dc9e7ac6579413c634e73dc5742e9cc52d073fc3e57ed0
  | 8, 0, 6 => 0xff652815fe5a0e72fbd97b37fbcfa734fb8cf931fb1f7172fab21684f9d0f0ddf8ec2452f6b22f67f63e7977f4ed8e48f4da989ff4c886ecf4b6683ef4643038f452118af303e5cdf29f8f19f1dccc71f1af9c79ef2e9b0feee28738eecba126ed71f1d3ed6973f8
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x38408000000210100000028408000001210200000008400000000e10200000008400000000a1030000004840c000000a10200000048408000000e103
  | 6, 0, 0 => 0x104424004000a2020000203880000018122000000003840000155002000000203880000001001020000002841000001091040000603880c000480a2030001640080800450812030000204880c0025440202000c000880c0000041109000d4104808000010c10c00109204800000000e10400006028808000000e102000554008080000002104000553008000000002100000d41048080001812200001000388080001812203
  | 6, 0, 1 => 0xd4204808004140220200100038808000180a202000d420480800038122010000603880800104402030000010440c000080620200000314410000080620300105028808000081220200000008400000081220100000008410000001210200002028808000381220000000314410000180e20000000414408000000e1030000040040800254c020000041100808000181220200000320474000080e203000550488080035081202
  | 6, 0, 2 => 0x114104808002048020300000028410004508120300002038808000000e1020000030040c00038062020010900880000155002020011420480c00255002000000a03880c000000a10400000038408000004010200000430430000000e1010011410480c000180e2010001630080c0000006102000c504880c00450812030000202880800000c510400095400804000000a102000000084100035041203000020188040002812202
  | 6, 0, 3 => 0xc500880c003000220300100018808004140220200002028808000000210400100008808000180a2020000a048808001550020000014414808001044020200114018808000080a2030000000840000038122020000204880800000021040000043040000018122020000031441000058c020300002038804000000e10300114204808000000e10300000008410002504120200000104424000180a2030009410480800154c0203
  | 6, 0, 4 => 0x424410000280e203000d410480800018122030010002880800350812030011410480c000080a2000000010040c00058c020300000048404000180e2030000203880c000000a10200114204808004140e20100000424410000001210200000018408000381220200002038808000381220300105008804000280220200114304800000281220300000008408000080a2010000a0388080025500201000553008040000012102
  | 6, 0, 5 => 0x202880c0001812202001140188080035041202001143048040005105202000d410480800000121030000201880000450812030000a04880800255002010001200880c004504120300000048400000010c10f0000031441000304c02010000602880c002504120300002038804001541220100095300804003140a2030008120080c001550020100114104808000000a10200055300800000380a2020000000841000050c5203
  | 6, 0, 6 => 0x2018800000000a1010000201880800000c811b00006028800000000a1020000042441000059002020011420480c000000210000002048804000001210200105008808000280620300006028808000004110200002048800000500e20300055300804003508120300000018408000001210200000320474000000a1030000202880800304c020000000314410000000210400055300800000000e10000100008808001540e203
  | 6, 0, 7 => 0xa048808002504120200105038808004140e2020000004840800051052020004110080800008062030000002840c000000a1030005530080000000061040011410480c00154c0203000c502880c000000610400000038408000080a2000011420480c000000a1020000203880c00000411090000042441000300062030000004840c000000a10200002018804003141220300000028404000080e200000000484040000012102
  | 6, 0, 8 => 0x202880c00008122000000202880800000061040000003841000000021040000202880800008122030000a04880c000000a101000020388080000002101000c130080000414412010000204880c00300062030000042441000008062020010001880800008122020000002840800008122020000203880000204802020005503880c000000e10300000424410000000210400000018400000000e104000000184040020480202
  | 6, 0, 9 => 0x3204740002812201001143048000020480202000c500880c002504120300000038410003000a20300000008410000280e2020000e00880800000061000011420480c00450412030000032046c000000a10400000008410000000610400000018410000000a1000005540080000001051020001630080c003001220300095300804000180e203000000084080041402201000000384040003812202000d42048080025041202
  | 6, 0, 10 => 0x38404000000210200002038804000001210400000028410000000a1040001431480c003000a2030000001841000000121040010003880800254c020100002038804000080620200000048410002048020300055300800000010c1010000000840400254c020000000008410000180e202000c004880c00400022020000202880800424062000000602880400304c0201000000184100045081203000941048080000812202
  | 6, 0, 11 => 0x55300804000180e20200105028804000180e2020010502880800204802020000031441000000021030000004840c003508120300000028410001541220200055400808000000210000109038800004508120200000038410000180a201000d4104808000080a203000c001880c0000109104000d420480800059002020009504880000000c5104000d420480800450c1201000d410480800424062000000a0488040000006100
  | 6, 0, 12 => 0x10510480400414022020000201880c000180a203001142048080002812202000d42048080000002101000c000880c001541220200002018800000004110200100018808003508120200000008410000000e1040000203880c00048062030000a03880c000080a2020009530080400018122020000000840800350812020000002841000000121040000a038804000480e20300000018410000000a103000020488080025440202
  | 6, 0, 13 => 0xd4204808004140e20200000048410000010c10f0000a038808000280e2020011410480c004248120000002028804000280e20100114104808000181220100000018408000080e2020009540080400001051020000003840800038122020000e048808003504120300000008400004140a2010000a018808004140a202000d4104808000080a20300002038800000590020200000018410004140e2020004110080c0000002101
  | 6, 0, 14 => 0xc002880c004140a20200000008404000000a104001000288080040006202000d420480c000080a2030009530080400254c0200000004304000031412203000000384000000109104000020288000042481200000d4104808004504120300055400804000180a202000550488080040002202000c004880c000180a2000000a00880c000180e2030000004841000414412010009410480c00000121000011410480c0001812202
  | 6, 0, 15 => 0x21000000000840400424022000009410480c001540e20300014048808000280e200000954008000001812202000000384080035041202000004144080035041202000d410480800450812020000e04880c00000021040000032046c000180e20000055400800000080e2020000a048800000000a1020000602880000000c5104000c500880c0030002203000c502880c00050c5203
  | 7, 0, 0 => 0x424400000000a1030000000840c000010c10300000008404000000610200000028408000000a10400002028808000008010300000038408000000a1000011410480c00400022020000010440c00008122010000001840c00000c11000000010440800000061020000032040c000000610300000038408000000e1000000030040c000010c1000000003840800000c910000000424400000280e202000000384000000806202
  | 7, 0, 1 => 0x18408000000a1030000040040c00000c51040000001840400001081020000003840000000061010000030040000001091000000042040c001540e2030000004840800000061000000a04880000414022020000001840c00000021000000203880000001011000000003841000000411020000000840800001051010009530080000001041020000010440800000c810300000424400000010c101000c1300804000000a102
  | 7, 0, 2 => 0x38404000001210300000420408000004110300000028408000000a1020000002840000000801030000010440800300122030000e04880400001091040000021440c000000a101000003044040000806201000d4204808000000e1010000e04880c00000c010300000028408000000210000000048404000000e10000000414408000000e1030000000840c000000a10100000300404000010010000000048404000000e102
  | 7, 0, 3 => 0x41440800000411010000032440400000c810300000008408000000210000000424410000000a1010000003840c00000811010005504880800000061040000040040800000c11000000004840000000021020000004840400000121020000040040800001001030000020040c00000c51030000001840800314022030000a04880800000021010000000840000000411000000001840800001001020000030040c0000040103
  | 7, 0, 4 => 0x430400000000e1000000041040800001091040000000841000000021030000a03880c000381220200000424400000004110100006038804000381220200000008404000000210000000424400000010010200000204404004140a2010000604880c000000610100109008800000000e1040000001840c000000210100000028400000281220100000018404004140220200055048804000000a10400000028408000280e200
  | 7, 0, 5 => 0x840000000021020000002840c00000811020000001840c000281220000000414408000000e10000000324404000010c1010000004841000000c010000105028808000000610200000008410000000e1040000021040c00000061010000000840c00000021010000002840000000c51010000002840c00304c02000000020040c000010c1000000030040800001081020000041440400001001010000003840c003000a203
  | 7, 0, 6 => 0xa038808000008510200000320408000000a1000000000840c000180a2030000004840800000c810300000008408000008010300000048400000000210200000400408000000e1010000041440800000061020000001841000001011000010901880000000c91000000003840400304c020000002038804000000e10000000214408000010010200000400408000008010200000324404000180e2020000042040c0000100102
  | 7, 0, 7 => 0x40440400000021000000003841000000c11010000e048804000080e2030000204880800000021000000020040c000000a1030000000840800000c510300000008408000008510100000018410000001210100002048800000000210200000048404000010c10200000008408000001210100000314400000081220000000204404000000a1010000004840000000c01020000a038808000010910400000104400000000a102
  | 7, 0, 8 => 0x18408000000e10000000420408000080e20000000414404000000e1010000021440800000021010000001840c00424022000000002840c00000021010000002840c00000121000000002840c000280e2010000000840000000021020000000840400450c12010000004840000001081020000a038800000000210300000300408002048020300000048408000000a1000011410480000000c5103000003044000000002103
  | 7, 0, 9 => 0x203880000000c01030000e04880800000121030000000840800000411010000603880400008062030000030440000000411030000002840c000000610200000314404000008110100000300400004140a2010000002840800000061010010503880400000021010000001840400000021010011420480c00000c81020000031440c00008122030000000841000001051020000030040c00000c510300000028408000000e100
  | 7, 0, 10 => 0xc500880c00000c41030000003840c000008010200000104408000000210400000424410000010c1030000001840800000811030000001840800000411020000032040c004508120300000304408000000e10100000304400000008110000000204404000000a10100000414404000000e1030000000840400001051020000020040c00000c510300002028808000000e1020000030040c0000002101000000484040000012100
  | 7, 0, 11 => 0x9530080400414022010000000840c000000e10100000200408000000e10300000028410000010c1000000042441000000411030000603880c0000100102000000484000000080102000d420480800001051010000002840c00001051010000202880c00000c11000000004841000000021030000042040800038122000000000840000000021030000031440c00001001020000043040c00000c0103000000084000000002102
  | 7, 0, 12 => 0x1840000000c510400000028408000000210400000204400000001210400000048404000010c1030000001840c00001081020000a03880400000121020000001840c000000a1010000010440800001051020000032040c00000061020000000840c000000a10100000008404004140e20200000038400000000e1020000000840c000010910000000008400000000210100000028408000000e101000000384040000006103
  | 7, 0, 13 => 0x3840c001550020100000008408003141220300000038408000010510100000324400000000e1000000031440c00038122010000001840c00000021000000004840800000021040000030040800001041020000040040000001051010000000840c000000a1030000010440000000061010000000840800000811010000004840c0000002104000000084080000109100000000384040002812200000d420480c0003812202
  | 7, 0, 14 => 0x18404000181220200000100408000000210300000038410000000a1000000041440400000c11010000003840000000c0102000000084000000109100000000284100000006104000d410480800000c01020000041440800000411020000042040c00000021020000001840c000381220300000314400004140a20200000048404000008110000105038804000000a1000000203880800450812020000010040c00000c5101
  | 7, 0, 15 => 0x8404000000210100000028410000000e10200000300408000280e2000000004840c000008110000000038404000280e2020000021440000001011020000030440400000c81030000043040c00000021030000000840000000021010000004840c00038122000000021440400000c510300000038404000000210000000048400000000210300000324400000008510200000008404000000a1020000030040c00450c1200
  | 7, 1, 0 => 0x4840c000000e100000004144080000012103000020188000000806202000c502880c00000411030000000840c00000121020000604880c00000c810200000018404000000a1030000004840800001091000000002840800000061030000010440c00001001030000000840800000c11000010900880000000c510400000048404000004110100000018410000000a1030000042040c0042406200000000184080000041103
  | 7, 1, 1 => 0x10440000414022020000000840000154122010011410480c000000e1000000003840000000021040000021040800000121000000021440000000061020000002840c00000021020000000840400000c810300000424400000180a20200000204408000180e203000c1300804000000e10400000314410000000a1020000000840c00018122020000030040c00000801030000003840c000000e101000004304000000006100
  | 7, 1, 2 => 0x3840c000000210300000028408000000210200000028408000000a1030000043040000000801020000002840c000000a1030000030440400000121020000003840c000010c10100000008408000000210000000018404000010c1030000002840c000280e2010000004840c000080a20300000028404000000a10100105008808000000e101001143048000000012100000000284040000105102000000084080000002103
  | 7, 1, 3 => 0x1840c000000e1010000604880800001001010000030040c00000121020008120080800000021030000002840c001540e2030000004840400000c11010000003840400000c11000000002840800000021020000020040800000121040010503880400314022030000602880800001051020000001841000001051010000021040c00001051010000000840000000c810200000424400000080e200000000084040045041203
  | 7, 1, 4 => 0x414408000000e10200000048408000008010300000400408000000e1000000010440c000181220100002038808000000e1040000001840c000000a1020000000840c00000c010300000008400000000e10100000028400000010c10100002038804000010810200000018408000000e10200000008404000000a102000000284080000806200000000084100000002101000004144000045081201000000184080000012103
  | 7, 1, 5 => 0x114304804000010c10200000310408000000a10200000038404000010510200000028408000000e1010000002840c00000121040000000840c000004110200114304800000000e10200000028404000008110000000008410000000e1040000003840800000c510300000008408000000e10200000018404000000e10400000048400000000210000094104808000000a1000000004840000000801020000004840c0000105102
  | 7, 1, 6 => 0x2840c00000401030000031440400000061020011430480000000021000000e04880000001091000000021440800000411010000002841000000021030000000840c000010c1010000003840000000061020000040040c00000021000000003840800000021010008120080800000021010000031440c00001001020000010440400154122010000a04880c000008110000000038404002541220000000400408000000a103
  | 7, 1, 7 => 0x8120080c00000c11000000041440800000121030000001840000000c9100000000084080000006104000000384000000041102000003244000000812202000d410480800000c010300000304404000180e2020000001841000000c01030000040040c00018122020000000840400000c51030000002840c000000a1030000002840400008122010000004840400450412000000020040c000000e101000000384000045081202
  | 7, 1, 8 => 0x2840800001091000000002840000000811000011420480c000000a1000000002840800000021030000004840800000c01030000a048808000000210200002028800000000210100000018400000281220200000038408000010510100000038400000004010200002018808000000e1020000040040000000061020000043040400000121000000a03880800000c810300000424400004240e2000000a038804000000a104
  | 7, 1, 9 => 0x8400000008110100000018408000000a1000000003840400314122030000602880800000c810200000414404000010c1020000000840c00000021020000020440c00000841030000043040c00000c51030000042440000000c1101000c000880c00000c41030000000841000000c910000000028408000000610000000038400000080e2030000030040c00008062010000001840400000c0102000000284100000002101
  | 7, 1, 10 => 0x2840800000c81020000040040c00350812020000043040400000841020000030040400000811000000001840800000021000000002840c000180a20000000038400000000e10200000414408000010910000000104424000004010200000008400000000a1030000002840c00000021020000001840800000021010000010040800000801020010500880800001081030000032040c000180e2030000040040c000080a202
  | 7, 1, 11 => 0x21440c00000121000000042440000000121030000003840000350812020000001840000000411010000002840c00058c020300000018408000000210300000430400000080e2020000003840c000000210000000038408000000210000002038808000080a20300000008404000001210200000414404000080620300000038408000381220300000038404000000610200000028410000000e1010000003840c000010c102
  | 7, 1, 12 => 0x840c000000e10000000430400000010c10000000048400000000a1030000010040c000000210300000038408000000e1020000040040800000c01010000004840c000080a2000000031441000000811000000003840c00000021040000003840800000121030000001840000000c51030000204880400000c91000000604880c00000061000000000840c00000411020000030040c000001210100000300404000000e102
  | 7, 1, 13 => 0x10440800000c91000000a03880c00028122020000001840c00000021020000004840400001001020000000840800000121030000031440c00001001020000000840000000021040000002840c00000021030000010440000018122030000001840800000061000000020040800350812030000030040c000010c10c0000003840000000c91000000a0488040000002101000000084000000105102000000284080042402200
  | 7, 1, 14 => 0x48404000000210200000324404000000a10300000018408000010910000000018400000000e10400055048808000180a20300000008404000000e1020000001840800000121030000004841000000c01020000020040c00008062010000031440c000000610400000038400000000a1030000003840c00000021030011410480000000c010200000048408000000610100000200408000000a10100000008400000000e101
  | 7, 1, 15 => 0x40040800008122020000030040c000010c10200081200808000180a2030000032040800000c010300000048408000008010200000028408000000610100000038404000000e1010000001840800000121040000042040c000010010200000300400004504120000000038400000010510100006028804000000a10200000008410000008010300000420408000000a104000000084000000081101000c1300800000000a103
  | 7, 2, 0 => 0x38400000000210300000018408000000210100000018404000000a1030000603880800038122030000002840000000061040000030440400001001030000000840400000121040000040040400000021040000030040c000001210000105028808000000a10200000204408000001210000000028400000000a1030000000840c000010c1020000004840c000000a104000000384080000041103000020488000000006102
  | 7, 2, 1 => 0x30440400000851010000000840c004240e20000000008408000000a10000000008400000080a2010000002840c00000c91010000031440c000001210100006028800000001210100000314410000004110200000008410000010910400000048408000280e2020000043040c00028122020000031441000000021010010003880800450c12010011410480c004504120000000008400000000210300000414408000000e101
  | 7, 2, 2 => 0x2840000001001030000000840400000061020010500880400001051010000042040c00304c02000000021440c00000121040000000840000000021010000004840000008122010000602880800001091000000000841000000c010300000214408000080e20000105038808000281220300000038404000001210200000038404000080a20200000008404000000a103000000284080001812200000004244000000002100
  | 7, 2, 3 => 0x4840c000000a1000000004840000001051020000204880000000021040009410480c000000e10200000038404000000a10200000008408000000a10300000008408000000a1020000021440000001091040000003840000000021000000001840400000021020000000840000001001020000021440c001540e2030000000840c001550020200000018408000000e10100000420408000181220100000424400000280e203
  | 7, 2, 4 => 0x32040c00000411000000020040c000000e103000c500880c00000801020000030040c000000210300000018408000010c10100000008408000001210200000008400000000a10000000008408000000210300000008408000000a10200000028400000000e10200000424400000000e1000000010440c00000121030000020440c00000c010100000018400000180e20000002028800000080e2020000030440000000c8102
  | 7, 2, 5 => 0x840c00001001020000203880000000021040000030040c000000210000000008400000010c1010000000840c000000a1030000003841000001051010000001840800000021030000010440400008062020000042040800000121020000003840c003504120300000104408000000a100000003104080000812201000002004080000002101000000084040000109100000000384000000081102000000084000000002103
  | 7, 2, 6 => 0x1840400000c510300000008408000000210200000028400000010c1000000000840c000000a1020000000840c003141220300109018800000004110300000018408000381220100000320408000000a10300000314404000000210300002028804000010510200000028410000008110000000008410000080e201000000484100000006100000000284080000002100000000484040000081102000000284080000101100
  | 7, 2, 7 => 0x414408000381220200000048400000000a10200000304400000010c1020000042441000001051020000001840000350412020000002840c00000c01030000032440400000021020000001840800304c020100105008804000000610100002018808000010510100002018804002550020000000048410004508120200000028408000000e1030000001840c0000002100000004244100000012104000000084080000002101
  | 7, 2, 8 => 0x400408000010c10000000008408000000a1040011420480c00000121010000603880400000121010000032040c000004110000105028804000010910100000008404000000e102000000484000000002101000c1300800000010510200000430400000008510100000018404000000210000000028408000000a1030000000840c00000121020000004840000000021010000030040c0000002102000004004080000012100
  | 7, 2, 9 => 0x8410000180e2030000010440400001051020000604880000154c02000000a04880800000121010008120080c000000e1000000604880000038122030000002840800000c81030000001840800000021000000000840000000c01030000001840c00001091000010903880000000c41020000004840c003140a20300000028408000000e1010000020040c000010510100000104408000000a101000000484000000806200
  | 7, 2, 10 => 0x400408000180e2000000204880c00000021030000203880c00000061010000002840800424062000000000840800000021020000043040800000021000000000840400000021020000000840c000010010100000048408000000a102000000384000000040102000c1300800000000610200000414404000280e20200000048400000000e1000000004840400000061030000010040800028122000000004840800000c5104
  | 7, 2, 11 => 0x18408000180e2000000041440800000c11000000004840800204802020000a03880c00204802020000003840c000001210100000314400000000610100000008404000000e1030000000840000000121000000604880c000004110100002048800000180a2020000003840c000008010200000038404000001210000000400408000000e10000100018808000000e10400000314410004140e20200002038804000000e101
  | 7, 2, 12 => 0x4840400000841020000201880c00001001020000002840800424022000000202880400000c01020000004840c0000100103001142048040000012102000c130080400001081020000040040800000c510000000008404000000e1000005503880c000000e10300000028400000280e2000000002840800000021030000000840000000121000000042441000000061010000002840c00000c11000000030040c0000002103
  | 7, 2, 13 => 0x3840000001051020000003840000001011010000001840c00001091000000042040800000c01030000000840c00001001000000202880c00008122020000031440400000121030000002840000000121020000000840400001091000000004840000008122020000000840000001091040000042440000000c51010000004840800000021010000030040c00450c12010000004840000001051010000042040c0000002104
  | 7, 2, 14 => 0x840c000004110300000008410000000610200000038400000000a1000005504880800000121030000000840400001001010000030040c000001210000000028408000080620200000038410000000e1000000004840000000801020000000840000028122030000003840000000021020000602880c000000e1040000001840c000000210400000018400000080e2000000002840000000c4103000003204080000006103
  | 7, 2, 15 => 0x4840400000021010011410480c000080a2010000020040c00000c51000000003840c00450c12000000000840800000c110000000018410000080a2020000040040800001001020000032040c000000e10000002028808000000a1010000003840c0000108103000000284080002812203000000384000000100102000004144080000002100000003104080035081203000004304000000006101000003004000000006100
  | 7, 3, 0 => 0x8408000000e10000000430400000010510200000028404000000e10000105028808000000e1020000002840c000000e1000000002840800000021030000001841000154c02030000001840c000001210100000204400000000e10100000028400000000e1020000203880400000c0103000c1300800000000610400000008410000000210300000008404000000e1010000000840400000021020000003840c00000c8103
  | 7, 3, 1 => 0x3840800000121010000041440400000121020000000840000000061000000002840800000121020000001840c00000c01030000000840800000021010000003840400000851020000001840c003508120200000420408000000610200000018408000080a200000d420480800000061000000043040000414022010011410480c000280e20100000048408003504120200000038400000000e103000000084080000109100
  | 7, 3, 2 => 0x4840c000010c10000000008400000000a1020000003840400000c51010000032440000000021030000003840000000c51010000000840c00154c02010000042040c000000e10100000038408000000210100000008408000000210100006048808000280e20300105038804000080e20300002048808004140e20200000008404000008010300000204400000281220000105038808000000e104001143048040000006103
  | 7, 3, 3 => 0x3840400001051020000002840800000061040000003840c000000e1020005504880800000061010000004840000038122000000000840000001001020000032040c00000841020000004840800450c120000000028408000008010200000430404000280e2000000000840c000000e1010000002840800000121030000003840c000080620300000038408000000a1010000020440c00304c02010000002840000000c5103
  | 7, 3, 4 => 0x404404004000a2020000e04880400414022020000000840800001081020000041040c000000210300000038410000001210100000048400000180a20200081200808000000a1010000000840c000010510100000008400000000a10200000008400000180a2030000201880c000001210200000320408000010c10000000038408000000a10100000008404000000e10000000200408000008110000000048408000000a102
  | 7, 3, 5 => 0x104400000008110100000028408000080e20200000414404000000a1030000204880800000021000000020040c00001001020000001840c000000a10200000028410001541220100000048408000000210300000414404000010910000000018400000000e101000060388000000002103000c504880c0000041102000001044000000012100000003044040000105102000004004000005900202000000084100000006103
  | 7, 3, 6 => 0x3840000001001030000020440800000061040000001840400008122030000000840800000021010000000840400000c51000000000840c000010c10200000038408000000e1010000203880400314022030000002840c000000210400000300400000000e10400109008800000000a10000000038408004140a20200000104404000000e1030000004840800000c81020000040040800001091000000004840000000c8102
  | 7, 3, 7 => 0x2841000000021010000031440000000c110000000048410003140a2030000203880c000004110300000038404000000e1000000031440c00000121000000021440800000021040000010440800000121030000003840800000c51030000004840800000021000000003840c000000a10100000008400000000e1040000002840000000c51030000021440000000411010000603880400000c5102000950488000000012100
  | 7, 3, 8 => 0x2840800001081020000043040c000010910400055400800004240e2000000201880000000841020000030040800000121020000002840000008122000011410480800000c110100000414404000000210100000008404000000e1000000002840c000010c1010000002840c00450c1201000000184080000002102000000084000000081103000003004080000006103000020288080000012100000003004080045041200
  | 7, 3, 9 => 0xd4204808000000e1000000000840800018122010000020440c00000061030000000840000000c01000000002840c000000e10100000304404000000610000000314410000000210400000314404000000a1000000203880400001001030000002840c000000610300000300404000000e10200000018408000000e10200000018410000000610000114204804000000e101001142048040000002102000004244000000012103
  | 7, 3, 10 => 0x304404000010c10000000018408000000a1020000003840800450812030000021440000000c01020010503880800000021020000000840c00000021000000002840400000c01030000040040800000021010000021440c000010c10100000048400000000e10100000038400000000e10300000414408000000a10200000048408000000a1010011420480800000061010000002840000000121030000000840c00000c5104
  | 7, 3, 11 => 0xe048800000000a102000d420480c00000c01030011410480000001081020000020440000000801020000e04880000000021020000030440400000021020000031440400000021010000040040800000c510300002048804000000a1030000041440800000c51030011430480000000021030000030040c000180a20000000008408000000a1020000000840800000c51030000203880000000021020005503880c0025412200
  | 7, 3, 12 => 0x8408004508120200000038404004240e20000000018408000000e1010000021440c000000a1030000000840800001091000000042040c000000e1000000204880c000000a1020000003840400000021030000030440000000c01030000020440000000411030000020040c000000a1040000001840c000000a10300000320408000000a1010000000840400300062030000a03880c000281220200000028408000180e203
  | 7, 3, 13 => 0x840800450812030000032440000001051020000a04880c00000801020000002840000001051020000a03880000000121010000004840000000021020000031441000000c1101000000084040035041202000004144040000806201000d41048080000002104000000084080000100102000002044000000012103000c504880c000008010200000048400000000e1040000032040c000001210400114204808000000a103
  | 7, 3, 14 => 0x20040800018122010000031440c00000c51000000003840400001081020000000840400000021000000000841000000c51030000020040800000c910000000018408000000e1010000000840800000c11000000004840c00000c010100000008410000010c10100000038408000180a2030000000840c004508120100000420408000008010300000038400003140a2030000000840400314022030000003840400000c0102
  | 7, 3, 15 => 0x2840c00000c010300095048800000080620000000048410000001210200000018404000180e2020000003841000001001020000002840c00000c81030000041440800000c5103000c502880c000010c1010000003840800000121040000030040c000000210300000008408000000210000000404400000180a20000000028410000000610400002038808000010810200000048404000000210000000200408000080a203
  | 7, 4, 0 => 0x30040c000000610100000008408000001210000000410408000000210100002018800000000e1000000202880800000411010000003840c00000c910100000424410000080e20300000028410000000e1000010503880400000061020000002840c00000c51040000041440400000021000000201880800000121000000001840000000021000000004841000000021040000002840c0000012103000003204080000002101
  | 7, 4, 1 => 0x4840c000000e10000000008400000000a1030000040040c00000121020000000840000028122010000004840c000000a10200000314404000000a10000000414408000010c1010000001840800000021030000031440c00000061040008120080c000004110200000038400000000210200000018400000000a10400000028400000001210300000048400000010010100000430408000010810300000008400000080a200
  | 7, 4, 2 => 0x3840c000000a10300000008400000000e1000000032040800000061010000042040c000001210300000300400000000e1010000040040800000021020000042440000000021000011410480c00000c81030000002840800000c51030000010440c00204802030000030440000008122030000000840000000061030000031441000008062030000604880000000c010200000048404002541220000006048808000000a103
  | 7, 4, 3 => 0x3840400000021020000043040400154122020000000840000000121020000602880400000801030000a04880c00000021020000204880c00154122010000002840c00000c110100000038404000001210200000430400000000e1000000000840c000000a1030000000840c00000021000000004841000000121020000001840000001051000000001840800001001000000042441000001001020000000840c0000006101
  | 7, 4, 4 => 0x40040800000021020000202880c000001210000000018408000000e1030000e048800000000610400000008410000180e2000000000840400255002010000602880800000121030000002840c00001081030000000841000000121030000004840800000021010000032040800000061010000000840c000000e10400000028408004240e200001142048040000080103000000084100015412202000000084080000002103
  | 7, 4, 5 => 0x105028808000000210000000028408000000210000000048404004140a20200000018400003504120200000028408000000e1010000031440c000010010300000104404000080a20100000400408000001210200000028400004508120200000008400000000e1000000003840c000008010200000038408000000e10200000008400000010010200105008808000000210300000018400000000210200000028400000010c102
  | 7, 4, 6 => 0x8400000000210400000204408000000e1030000002840800028122010000001840c00000021020000e048808000000e1000000e0488040041402201000000084040000002103000d420480c00000021000000021440c000000e1030000040040c00000c5101000c1300804000000e10300006048800000000a10200000430404002048020200006038808000080a203000d41048080000105102000000084080000002101
  | 7, 4, 7 => 0x840800000021030000001840c000004110000002048800000010810300000300404000180e2020000042040800000021020000040040800000c810300000018404003508120300000048410000080a2000000030040c000000a1020000002840400000121020000000840800001001020000004840c0000006100000c502880c00001081020000003840c00000021010000001840c0000002102000000384000000012104
  | 7, 4, 8 => 0x4840000001051010000041040c002048020300000048404000001210100000214408000000e10000006028804000000a1020000603880400000021010000004840c00001051020000020040c00001041020000004841000000121000000003840c000000610300006038800000000e1010000000840800000121010000000840800000061000000032440400000c5104
  | 8, 0, 0 => 0x43040800000021030000021440c00000c11000000010440000000c81020000020440c000000a10000000400404000000a10300000018400000000a1020000003840c000000210100000104400000000610200000430404000000210100000018400000008010200000400400000000a1020000003840000000c110100000214408000000e10200000104404000000e1000000031440c0000006101000004304000000100102
  | 8, 0, 1 => 0x42040c00001001000000041440400001001030000030040c000000a10300000104408000000a10100000420408000010c1000000041440800000021000000002840c00000021010000030040800000021020000043040000000021020000030440400000121030000020040c00000021010000010440c00000411000000020440800000811020000021440c00000121030000001840c0000002100000002004080000002102
  | 8, 0, 2 => 0x20440000000021010000042440000000021020000010440400000c510300000314404000008110200000214400000000610100000324400000000210100000414408000000e1000000020440400000c010000000304404000000e1010000002840800001001020000004840400000061020000000840c000010010200000400408000001210000000038400000000a1000000031440000000c110000000324400000000a103
  | 8, 0, 3 => 0x1840c00000851000000004840c00000811000000003840000001091000000021440c000010010200000214404000000a1030000003840c00000121020000004840000000851020000004840000000021030000043040c00000c91010000021440400000811000000032040c000000210000000314400000000a10200000400404000000e1010000000840c000010c1030000010440800000c81030000030040000000c5100
  | 8, 0, 4 => 0x42040800000c01010000021440000000801020000003840000000801020000042040c00000811010000030040c00000c01000000042040800000801030000032440400001051010000030040800000021000000031440400000851020000002840c00000851020000030040000000c510300000008408000010c1020000010440c00000021030000030040400000c810200000300408000000a10200000324400000000e100
  | 8, 0, 5 => 0x18400000008510200000008408000010c1020000043040800000021000000032040800000c510300000314400000008110100000038400000000e10100000008400000000e10000000324404000004110200000104408000000a1030000000840c0000105102000004144080000041100000003144040000081103000002044000000002103000000184000000006102000000084040000109100000004304040000081103
  | 8, 0, 6 => 0x104404000010510200000304404000000a10200000400408000000a1030000030040c000000e10300000018404000008110100000430400000000a10000000304404000008510300000048408000000e1010000004840400000801020000000840000001001030000030040400000021030000043040c00000c11000000000840800000411000000032040c000010010300000430400000000e10200000204408000000e101
  | 8, 0, 7 => 0x20440c00000c010300000314400000004110100000008404000010010100000008408000000210000000018404000010010300000430404000008110200000304400000000210000000400404000010c10100000028400000000e10100000304400000004110300000048404000000a1020000032040c000000a10200000038408000000e1020000002840c000000610300000008404000010010000000104408000000e100
  | 8, 0, 8 => 0x40040c000000a1020000002840000000801030000003840800000021020000043040800000121000000032040800000851000000010440c00000c510000000400408000000e1010000040040000001051010000004840400000c910100000038400000010810200000420408000010010100000400400000000a1010000030040800000c01020000043040000000021030000004840000001081030000021440c0000081103
  | 8, 0, 9 => 0x4840000000c91010000003840400000121030000042040800000851030000030040000000c01020000042040c00000c01010000000840400000801020000030440400001001010000031440400001051010000001840800000c01030000021440000000c910000000028404000000e10100000104404000000e1000000001840800000851020000000840c000010c1030000020040c00000c81020000032040c00000c5103
  | 8, 0, 10 => 0x20440400000c01000000002840c000008510100000300400000000210000000038404000000210300000028408000000a1020000020440c00000851020000000840800000c010100000018408000000e1000000020440800000c910000000204400000000a1030000004840800000121020000002840800000c510100000424400000000a101000001044080000002100000003244000000002102000002144040000080103
  | 8, 0, 11 => 0x840c000010c1030000003840000000811020000043040c00000021000000032040c00000121030000030040c00000021020000003840400001091000000002840800000c11000000003840800000121020000010440800000021010000010440c00001051020000043040400001001030000020440000000061030000010440c00000801030000040040800000061030000002840c000000e103000000484080000080102
  | 8, 0, 12 => 0x300404000010810200000430400000000e10100000300408000010010000000048404000010010000000008400000000210100000304400000010c1010000010440000000021020000043040800000021020000043040800000c81020000032040800000061000000042040c000000a1020000030040c00000021000000042040c000000e103
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 13 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_x4_1 roots_x4_1 8 s ws hint
  | 1 => checkCutEntry dom_x5_1 roots_x5_1 8 s ws hint
  | 2 => checkCutEntry dom_x1_0 roots_x1_0 8 s ws hint
  | 3 => checkCutEntry dom_x2_0 roots_x2_0 8 s ws hint
  | 4 => checkCutEntry dom_x3_1 roots_x3_1 7 s ws hint
  | 5 => checkCutEntry dom_x0_0_x4_1 roots_x0_0_x4_1 5 s ws hint
  | 6 => checkCutEntry dom_x0_0_x5_1 roots_x0_0_x5_1 5 s ws hint
  | 7 => checkCutEntry dom_x0_1_x1_0 roots_x0_1_x1_0 5 s ws hint
  | 8 => checkCutEntry dom_x0_1_x2_0 roots_x0_1_x2_0 5 s ws hint
  | 9 => checkCutEntry dom_x0_1 roots_x0_1 6 s ws hint
  | 10 => checkCutEntry dom_x0_1_x1_0_x2_0 roots_x0_1_x1_0_x2_0 4 s ws hint
  | 11 => checkCutEntry dom_x0_0 roots_x0_0 6 s ws hint
  | 12 => checkCutEntry dom_x3_0 roots_x3_0 6 s ws hint
  | 13 => checkCutEntry dom_x3_0_x4_1 roots_x3_0_x4_1 5 s ws hint
  | 14 => checkCutEntry dom_x3_0_x5_1 roots_x3_0_x5_1 5 s ws hint
  | 15 => checkCutEntry dom_x4_0 roots_x4_0 6 s ws hint
  | 16 => checkCutEntry dom_x3_1_x4_0 roots_x3_1_x4_0 5 s ws hint
  | 17 => checkCutEntry dom_x4_0_x5_1 roots_x4_0_x5_1 5 s ws hint
  | 18 => checkCutEntry dom_x5_0 roots_x5_0 6 s ws hint
  | 19 => checkCutEntry dom_x3_1_x5_0 roots_x3_1_x5_0 5 s ws hint
  | 20 => checkCutEntry dom_x4_1_x5_0 roots_x4_1_x5_0 5 s ws hint
  | 21 => checkCutEntry dom_x3_0_x4_0_x5_0 roots_x3_0_x4_0_x5_0 4 s ws hint
  | 22 => checkCutEntry dom_x2_0_x5_1 roots_x2_0_x5_1 5 s ws hint
  | 23 => checkCutEntry dom_x1_0_x4_1 roots_x1_0_x4_1 5 s ws hint
  | 24 => checkCutEntry dom_x1_0_x3_1_x5_0 roots_x1_0_x3_1_x5_0 4 s ws hint
  | 25 => checkCutEntry dom_x0_0_x4_1_x5_1 roots_x0_0_x4_1_x5_1 4 s ws hint
  | 26 => checkCutEntry dom_x2_0_x3_1_x4_0 roots_x2_0_x3_1_x4_0 4 s ws hint
  | 27 => checkCutEntry dom_x1_0_x5_0 roots_x1_0_x5_0 5 s ws hint
  | 28 => checkCutEntry dom_x1_0_x4_1_x5_0 roots_x1_0_x4_1_x5_0 4 s ws hint
  | 29 => checkCutEntry dom_x2_0_x4_0 roots_x2_0_x4_0 5 s ws hint
  | 30 => checkCutEntry dom_x2_0_x4_0_x5_1 roots_x2_0_x4_0_x5_1 4 s ws hint
  | 31 => checkCutEntry dom_x1_0_x2_0 roots_x1_0_x2_0 5 s ws hint
  | 32 => checkCutEntry dom_x3_1_x4_0_x5_0 roots_x3_1_x4_0_x5_0 4 s ws hint
  | 33 => checkCutEntry dom_x4_1_x5_1 roots_x4_1_x5_1 5 s ws hint
  | 34 => checkCutEntry dom_x1_0_x3_1 roots_x1_0_x3_1 5 s ws hint
  | 35 => checkCutEntry dom_x2_0_x3_1 roots_x2_0_x3_1 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_63 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_1_x1_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_1_x2_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_1_x1_0_x2_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_1_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x4_0_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x3_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x3_1_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x4_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x4_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x2_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_1_x4_0_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x3_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x3_1 _ hc
  · contradiction
def p0Subs : List Nat := [4, 2, 0, 3, 1, 11, 9, 12, 15, 18, 7, 8, 5, 6, 27, 29, 10, 16, 19, 25, 13, 14, 21, 24, 26, 17, 20, 28, 30, 31, 22, 23, 32, 34, 35, 33]
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
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 2 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 64 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 64 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6_64 : ∀ i, 64 ≤ i → i < 89 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 25 64 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 89 → Z 6 i = true := (range_split z6_0 z6_64)
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
private theorem z7_384 : ∀ i, 384 ≤ i → i < 416 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 32 384 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 416 → Z 7 i = true := (range_split (range_split z7_0 (range_split z7_64 z7_128)) (range_split (range_split z7_192 z7_256) (range_split z7_320 z7_384)))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_0 : ∀ i, 0 ≤ i → i < 64 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_64 : ∀ i, 64 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 64 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_128 : ∀ i, 128 ≤ i → i < 192 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_192 : ∀ i, 192 ≤ i → i < 238 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 46 192 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 238 → Z 8 i = true := (range_split (range_split z8_0 z8_64) (range_split z8_128 z8_192))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z9 : ∀ i, 0 ≤ i → i < 23 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 23 0 = true)
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

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 11]⟩], 16⟩
theorem wit_mono : PEqualNP.MetaComplexity.Monotone2 wit := by simp [wit, PEqualNP.MetaComplexity.Monotone2]
theorem wit_size : wit.size ≤ 11 := by decide
theorem wit_eval : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = ((fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4209567976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0))) x := by decide +kernel
theorem hT6 : ∀ r : Fin 64, goal_all.testBit r.val = ((fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4209567976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0))) (pt6 r.val) := by decide +kernel
theorem lower : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4209567976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) t → 11 ≤ t :=
  lower_to_circuit6 (fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4209567976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) goal_all 11 hT6 (by unfold IsConst; decide) low_63

end PEqualNP.Outside.L_meta_40403_aux

theorem PEqualNP.Outside.L_meta_40403 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4209567976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809448 * 2 ^ 32 + 4209567976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro s hs
  have hlb : 11 ≤ s := PEqualNP.Outside.L_meta_40403_aux.lower s hs
  exact ⟨PEqualNP.Outside.L_meta_40403_aux.wit, PEqualNP.Outside.L_meta_40403_aux.wit_mono, le_trans PEqualNP.Outside.L_meta_40403_aux.wit_size hlb, PEqualNP.Outside.L_meta_40403_aux.wit_eval⟩
