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

namespace PEqualNP.Outside.L_meta_40183_aux

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
def goal_all : Nat := 0xfeeaeaeaeee0ea00
def dom_63 : Nat := 0xffffffffffffffff
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]
def dom_x0_0_x2_1 : Nat := 0x5050505050505050
def roots_x0_0_x2_1 : List Nat := [0x4040404040404040, 0x5000500050005000, 0x5050000050500000, 0x5050505000000000]
def dom_x0_0_x1_1_x5_0 : Nat := 0x44444444
def roots_x0_0_x1_1_x5_0 : List Nat := [0x40404040, 0x44004400, 0x44440000]
def dom_x0_0_x3_1_x5_1 : Nat := 0x5500550000000000
def roots_x0_0_x3_1_x5_1 : List Nat := [0x4400440000000000, 0x5000500000000000, 0x5500000000000000]
def dom_x0_0_x5_1 : Nat := 0x5555555500000000
def roots_x0_0_x5_1 : List Nat := [0x4444444400000000, 0x5050505000000000, 0x5500550000000000, 0x5555000000000000]
def dom_x0_0_x1_1 : Nat := 0x4444444444444444
def roots_x0_0_x1_1 : List Nat := [0x4040404040404040, 0x4400440044004400, 0x4444000044440000, 0x4444444400000000]
def dom_x0_0_x3_1 : Nat := 0x5500550055005500
def roots_x0_0_x3_1 : List Nat := [0x4400440044004400, 0x5000500050005000, 0x5500000055000000, 0x5500550000000000]
def dom_x0_0_x4_1_x5_1 : Nat := 0x5555000000000000
def roots_x0_0_x4_1_x5_1 : List Nat := [0x4444000000000000, 0x5050000000000000, 0x5500000000000000]
def dom_x0_0_x5_0 : Nat := 0x55555555
def roots_x0_0_x5_0 : List Nat := [0x44444444, 0x50505050, 0x55005500, 0x55550000]
def dom_x0_0_x4_1 : Nat := 0x5555000055550000
def roots_x0_0_x4_1 : List Nat := [0x4444000044440000, 0x5050000050500000, 0x5500000055000000, 0x5555000000000000]
def dom_x0_0 : Nat := 0x5555555555555555
def roots_x0_0 : List Nat := [0x4444444444444444, 0x5050505050505050, 0x5500550055005500, 0x5555000055550000, 0x5555555500000000]
def dom_x1_0_x2_1 : Nat := 0x3030303030303030
def roots_x1_0_x2_1 : List Nat := [0x2020202020202020, 0x3000300030003000, 0x3030000030300000, 0x3030303000000000]
def dom_x1_0 : Nat := 0x3333333333333333
def roots_x1_0 : List Nat := [0x2222222222222222, 0x3030303030303030, 0x3300330033003300, 0x3333000033330000, 0x3333333300000000]
def dom_x2_1 : Nat := 0xf0f0f0f0f0f0f0f0
def roots_x2_1 : List Nat := [0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000]
def dom_x1_0_x4_1 : Nat := 0x3333000033330000
def roots_x1_0_x4_1 : List Nat := [0x2222000022220000, 0x3030000030300000, 0x3300000033000000, 0x3333000000000000]
def dom_x1_1_x5_0 : Nat := 0xcccccccc
def roots_x1_1_x5_0 : List Nat := [0x88888888, 0xc0c0c0c0, 0xcc00cc00, 0xcccc0000]
def dom_x3_1_x5_1 : Nat := 0xff00ff0000000000
def roots_x3_1_x5_1 : List Nat := [0xaa00aa0000000000, 0xcc00cc0000000000, 0xf000f00000000000, 0xff00000000000000]
def dom_x4_1_x5_1 : Nat := 0xffff000000000000
def roots_x4_1_x5_1 : List Nat := [0xaaaa000000000000, 0xcccc000000000000, 0xf0f0000000000000, 0xff00000000000000]
def dom_x4_1 : Nat := 0xffff0000ffff0000
def roots_x4_1 : List Nat := [0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000]
def dom_x3_1 : Nat := 0xff00ff00ff00ff00
def roots_x3_1 : List Nat := [0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000]
def dom_x5_0 : Nat := 0xffffffff
def roots_x5_0 : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]
def dom_x1_1 : Nat := 0xcccccccccccccccc
def roots_x1_1 : List Nat := [0x8888888888888888, 0xc0c0c0c0c0c0c0c0, 0xcc00cc00cc00cc00, 0xcccc0000cccc0000, 0xcccccccc00000000]
def dom_x5_1 : Nat := 0xffffffff00000000
def roots_x5_1 : List Nat := [0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000]

namespace S_x0_0_x2_1
def pairsG : List (Nat × Nat) := [(6, 14), (6, 22), (6, 38), (12, 14), (20, 22), (28, 30), (28, 60), (36, 38), (44, 46), (44, 60), (52, 54), (52, 60)]
def r1sG : List Nat := [6, 6, 6, 12, 20, 28, 28, 36, 44, 44, 52, 52]
def r2sG : List Nat := [14, 22, 38, 14, 22, 30, 60, 38, 46, 60, 54, 60]
def mpG : Nat := 0xfff
def pool6G : List Nat := [30812837520918, 30812971734542, 48404755123750, 48405157778958]
def xsM : List Nat := roots_x0_0_x2_1.map (· &&& dom_x0_0_x2_1)
def goalM : Nat := goal_all &&& dom_x0_0_x2_1
def NN : Nat → Nat
  | 4 => 5
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0xf0264e89ec2d39dbd27173f0050bf61c00edca17
  | 5, 0, 0 => 0xec2d39db
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x505050500000505000005050005000500050005010101010101010105050505000000000505000005050000050005000500050004040404040404040
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x68546884646468c44474
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x0_0_x2_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x0_0_x2_1 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x0_0_x2_1 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x0_0_x2_1 goalM u ys) : RunD dom_x0_0_x2_1 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x0_0_x2_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x0_0_x2_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 3 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_x0_0_x2_1 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x0_0_x2_1 roots_x0_0_x2_1 goal_all 6 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x0_0_x2_1 goal_all := by
    have h0 : isConstB dom_x0_0_x2_1 goal_all = false := by decide +kernel
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
end S_x0_0_x2_1
theorem low_x0_0_x2_1 : Lower dom_x0_0_x2_1 roots_x0_0_x2_1 goal_all 6 := S_x0_0_x2_1.noCircuit

namespace S_x0_0_x1_1_x5_0
def pairsG : List (Nat × Nat) := [(6, 14), (6, 22), (10, 14), (10, 26), (18, 22), (18, 26)]
def r1sG : List Nat := [6, 6, 10, 10, 18, 18]
def r2sG : List Nat := [14, 22, 14, 26, 22, 26]
def mpG : Nat := 0x3f
def pool6G : List Nat := [11021189781006]
def xsM : List Nat := roots_x0_0_x1_1_x5_0.map (· &&& dom_x0_0_x1_1_x5_0)
def goalM : Nat := goal_all &&& dom_x0_0_x1_1_x5_0
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x38233cb0
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x4444000000000000440044000000000040404040
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x0_0_x1_1_x5_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x0_0_x1_1_x5_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x0_0_x1_1_x5_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x0_0_x1_1_x5_0 goalM u ys) : RunD dom_x0_0_x1_1_x5_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x0_0_x1_1_x5_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x0_0_x1_1_x5_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x0_0_x1_1_x5_0 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x0_0_x1_1_x5_0 roots_x0_0_x1_1_x5_0 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x0_0_x1_1_x5_0 goal_all := by
    have h0 : isConstB dom_x0_0_x1_1_x5_0 goal_all = false := by decide +kernel
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
end S_x0_0_x1_1_x5_0
theorem low_x0_0_x1_1_x5_0 : Lower dom_x0_0_x1_1_x5_0 roots_x0_0_x1_1_x5_0 goal_all 4 := S_x0_0_x1_1_x5_0.noCircuit

namespace S_x0_0_x3_1_x5_1
def pairsG : List (Nat × Nat) := [(42, 46), (42, 58), (44, 46), (44, 60), (56, 58), (56, 60)]
def r1sG : List Nat := [42, 42, 44, 44, 56, 56]
def r2sG : List Nat := [46, 58, 46, 60, 58, 60]
def mpG : Nat := 0x3f
def pool6G : List Nat := [48559843719726]
def xsM : List Nat := roots_x0_0_x3_1_x5_1.map (· &&& dom_x0_0_x3_1_x5_1)
def goalM : Nat := goal_all &&& dom_x0_0_x3_1_x5_1
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x4e4c4181
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x550000000000000050005000000000004400440000000000
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x0_0_x3_1_x5_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x0_0_x3_1_x5_1 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x0_0_x3_1_x5_1 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x0_0_x3_1_x5_1 goalM u ys) : RunD dom_x0_0_x3_1_x5_1 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x0_0_x3_1_x5_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x0_0_x3_1_x5_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x0_0_x3_1_x5_1 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x0_0_x3_1_x5_1 roots_x0_0_x3_1_x5_1 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x0_0_x3_1_x5_1 goal_all := by
    have h0 : isConstB dom_x0_0_x3_1_x5_1 goal_all = false := by decide +kernel
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
end S_x0_0_x3_1_x5_1
theorem low_x0_0_x3_1_x5_1 : Lower dom_x0_0_x3_1_x5_1 roots_x0_0_x3_1_x5_1 goal_all 4 := S_x0_0_x3_1_x5_1.noCircuit

theorem low_x0_0_x5_1 : Lower dom_x0_0_x5_1 roots_x0_0_x5_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5500550000000000, 50, 58)] (by decide +kernel) (by decide +kernel) low_x0_0_x3_1_x5_1

theorem low_x0_0_x1_1 : Lower dom_x0_0_x1_1 roots_x0_0_x1_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x4444444400000000, 6, 38)] (by decide +kernel) (by decide +kernel) low_x0_0_x1_1_x5_0

theorem low_x0_0_x3_1 : Lower dom_x0_0_x3_1 roots_x0_0_x3_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5500550000000000, 28, 60)] (by decide +kernel) (by decide +kernel) low_x0_0_x3_1_x5_1

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

theorem low_x0_0_x5_0 : Lower dom_x0_0_x5_0 roots_x0_0_x5_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x44444444, 12, 14)] (by decide +kernel) (by decide +kernel) low_x0_0_x1_1_x5_0

theorem low_x0_0_x4_1 : Lower dom_x0_0_x4_1 roots_x0_0_x4_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5555000000000000, 28, 60)] (by decide +kernel) (by decide +kernel) low_x0_0_x4_1_x5_1

namespace S_x0_0
def pairsG : List (Nat × Nat) := [(6, 14), (6, 22), (6, 38), (10, 14), (10, 26), (12, 14), (18, 22), (18, 26), (20, 22), (24, 26), (28, 30), (28, 60), (34, 38), (36, 38), (42, 46), (42, 58), (44, 46), (44, 60), (50, 54), (50, 58), (52, 54), (52, 60), (56, 58), (56, 60)]
def r1sG : List Nat := [6, 6, 6, 10, 10, 12, 18, 18, 20, 24, 28, 28, 34, 36, 42, 42, 44, 44, 50, 50, 52, 52, 56, 56]
def r2sG : List Nat := [14, 22, 38, 14, 26, 14, 22, 26, 22, 26, 30, 60, 38, 38, 46, 58, 46, 60, 54, 58, 54, 60, 58, 60]
def mpG : Nat := 0xffffff
def pool6G : List Nat := [48404755125798, 46206098740750, 48404755123750, 46300690913806, 55002058332694]
def xsM : List Nat := roots_x0_0.map (· &&& dom_x0_0)
def goalM : Nat := goal_all &&& dom_x0_0
def NN : Nat → Nat
  | 5 => 3
  | 6 => 7
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xac1fffb293787a5417b655ee
  | 6, 0, 0 => 0xfd6d7d12f438b0ceb88e7d9f9e7b792b85d3f3cd8159b5291a3d9d91
  | 7, 0, 0 => 0xc99170a
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x5555555555000000550000004444000044440000440044004400440044444444444444445500550055005500000055550000555555555555000000005555000055550000505050505050505011111111111111110055005500550055
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x432105427055462155
  | 6, 0, 0 => 0x4362796436278603627b504362150462755436a2760432705
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
  | 0 => 0xfff0000000000c00e0000000000000c00c0000000000000c01800000000000cd0df0000000000c3ce38000000000003f03f0000000000fff0000000000000fc0fc00000000000332d270000000000f32f2000000000003c31c7
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x7fb0000000000ea8e9000000000005c87d2000000000049c6b900000000005df7ff0000000000ebceb9000000000001702d0000000000fff8040000000000fe8fd20000000000b77d6f0000000000a208000000000000143146
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
  | 5, 0, 0 => 0xb6cffbab9eacabe1860526835520dbb93b0dd745226651e7218ad9fc1a6ed047
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x18400000000210000000028400000000e10000000008400000000a100000000384000000006100
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 4 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_x0_0_x2_1 roots_x0_0_x2_1 6 s ws hint
  | 1 => checkCutEntry dom_x0_0_x1_1_x5_0 roots_x0_0_x1_1_x5_0 4 s ws hint
  | 2 => checkCutEntry dom_x0_0_x5_1 roots_x0_0_x5_1 5 s ws hint
  | 3 => checkCutEntry dom_x0_0_x1_1 roots_x0_0_x1_1 5 s ws hint
  | 4 => checkCutEntry dom_x0_0_x3_1_x5_1 roots_x0_0_x3_1_x5_1 4 s ws hint
  | 5 => checkCutEntry dom_x0_0_x3_1 roots_x0_0_x3_1 5 s ws hint
  | 6 => checkCutEntry dom_x0_0_x4_1_x5_1 roots_x0_0_x4_1_x5_1 4 s ws hint
  | 7 => checkCutEntry dom_x0_0_x5_0 roots_x0_0_x5_0 5 s ws hint
  | 8 => checkCutEntry dom_x0_0_x4_1 roots_x0_0_x4_1 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x0_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x2_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x1_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x1_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x3_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x3_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_1 _ hc
  · contradiction
def p0Subs : List Nat := [0, 3, 5, 7, 2, 8, 1, 4, 6]
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

namespace S_x1_0_x2_1
def pairsG : List (Nat × Nat) := [(5, 13), (5, 21), (5, 37), (12, 13), (20, 21), (28, 29), (28, 60), (36, 37), (44, 45), (44, 60), (52, 53), (52, 60)]
def r1sG : List Nat := [5, 5, 5, 12, 20, 28, 28, 36, 44, 44, 52, 52]
def r2sG : List Nat := [13, 21, 37, 13, 21, 29, 60, 37, 45, 60, 53, 60]
def mpG : Nat := 0xfff
def pool6G : List Nat := [30808542553365, 30808676766989, 48400460156197, 48400862811405]
def xsM : List Nat := roots_x1_0_x2_1.map (· &&& dom_x1_0_x2_1)
def goalM : Nat := goal_all &&& dom_x1_0_x2_1
def NN : Nat → Nat
  | 4 => 5
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0xe7b11702e3ccf53bcc3977cbadd45a704948d49b
  | 5, 0, 0 => 0x4948d49b
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x303030300000303000003030003000300030003010101010101010103030303000000000303000003030000030003000300030002020202020202020
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x64646854447468c46884
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x1_0_x2_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x1_0_x2_1 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x1_0_x2_1 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x1_0_x2_1 goalM u ys) : RunD dom_x1_0_x2_1 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x1_0_x2_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x1_0_x2_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 3 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_x1_0_x2_1 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x1_0_x2_1 roots_x1_0_x2_1 goal_all 6 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x1_0_x2_1 goal_all := by
    have h0 : isConstB dom_x1_0_x2_1 goal_all = false := by decide +kernel
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
end S_x1_0_x2_1
theorem low_x1_0_x2_1 : Lower dom_x1_0_x2_1 roots_x1_0_x2_1 goal_all 6 := S_x1_0_x2_1.noCircuit

theorem low_x1_0 : Lower dom_x1_0 roots_x1_0 goal_all 7 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x3030303030303030, 17, 21)] (by decide +kernel) (by decide +kernel) low_x1_0_x2_1

theorem low_x2_1 : Lower dom_x2_1 roots_x2_1 goal_all 7 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa0a0a0a0a0a0a0a0, 12, 13)] (by decide +kernel) (by decide +kernel) low_x0_0_x2_1

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

theorem low_x1_1_x5_0 : Lower dom_x1_1_x5_0 roots_x1_1_x5_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x88888888, 10, 11)] (by decide +kernel) (by decide +kernel) low_x0_0_x1_1_x5_0

theorem low_x3_1_x5_1 : Lower dom_x3_1_x5_1 roots_x3_1_x5_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaa00aa0000000000, 40, 41)] (by decide +kernel) (by decide +kernel) low_x0_0_x3_1_x5_1

theorem low_x4_1_x5_1 : Lower dom_x4_1_x5_1 roots_x4_1_x5_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa000000000000, 48, 49)] (by decide +kernel) (by decide +kernel) low_x0_0_x4_1_x5_1

theorem low_x4_1 : Lower dom_x4_1 roots_x4_1 goal_all 7 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcccc0000cccc0000, 20, 22)] (by decide +kernel) (by decide +kernel) low_x1_0_x4_1

theorem low_x3_1 : Lower dom_x3_1 roots_x3_1 goal_all 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaa00aa00aa00aa00, 8, 9)] (by decide +kernel) (by decide +kernel) low_x0_0_x3_1

theorem low_x5_0 : Lower dom_x5_0 roots_x5_0 goal_all 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaaaaaa, 8, 9)] (by decide +kernel) (by decide +kernel) low_x0_0_x5_0

theorem low_x1_1 : Lower dom_x1_1 roots_x1_1 goal_all 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x8888888888888888, 10, 11)] (by decide +kernel) (by decide +kernel) low_x0_0_x1_1

theorem low_x5_1 : Lower dom_x5_1 roots_x5_1 goal_all 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaaaaaa00000000, 32, 33)] (by decide +kernel) (by decide +kernel) low_x0_0_x5_1

namespace S_63
def pairsG : List (Nat × Nat) := [(1, 9), (1, 33), (3, 11), (3, 35), (5, 13), (5, 21), (5, 37), (6, 14), (6, 22), (6, 38), (7, 15), (7, 23), (7, 39), (8, 9), (10, 11), (10, 14), (10, 26), (12, 13), (12, 14), (17, 21), (17, 25), (17, 49), (18, 22), (18, 26), (19, 23), (19, 27), (19, 51), (20, 21), (20, 22), (24, 25), (24, 26), (28, 29), (28, 30), (28, 60), (32, 33), (34, 35), (34, 38), (36, 37), (36, 38), (40, 41), (42, 43), (42, 46), (42, 58), (44, 45), (44, 46), (44, 60), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [1, 1, 3, 3, 5, 5, 5, 6, 6, 6, 7, 7, 7, 8, 10, 10, 10, 12, 12, 17, 17, 17, 18, 18, 19, 19, 19, 20, 20, 24, 24, 28, 28, 28, 32, 34, 34, 36, 36, 40, 42, 42, 42, 44, 44, 44, 48, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [9, 33, 11, 35, 13, 21, 37, 14, 22, 38, 15, 23, 39, 9, 11, 14, 26, 13, 14, 21, 25, 49, 22, 26, 23, 27, 51, 21, 22, 25, 26, 29, 30, 60, 33, 35, 38, 37, 38, 41, 43, 46, 58, 45, 46, 60, 49, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0xffffffffffffff
def pool6G : List Nat := [46261933775369, 48409050093094, 20921492049429, 61788275873306, 55005967095078, 46300690913806, 30817132486933, 57294983334204, 46261566441761, 46261211631130, 46209873348878, 46300489584154, 30817266705934, 30868873414933, 48498890315068, 57205375764757, 61762336067132, 61796830025276, 61693231174972, 46210394495502, 48409050089761, 30868637098261, 30817333807381, 57363702024508, 46300690913801, 61603189623073, 30868636765717, 30817132488214, 61693029848380, 55006119856417, 46300623801882, 30817266701577, 48409050094118, 61796309931324]
def xsM : List Nat := roots_63.map (· &&& dom_63)
def goalM : Nat := goal_all &&& dom_63
def NN : Nat → Nat
  | 5 => 51
  | 6 => 343
  | 7 => 1204
  | 8 => 512
  | 9 => 38
  | 10 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xf75e2cf3e84318ead6c82f18c97b9abfc3fa525ec178162bbf64bc4bbcb8e893b6ba208fb6540b6ab58c75d9b3ad8e52a7706924a4fbec99a172a0f3a0c2cbcea06e262a9eb528769dcb1f8e9d88f90998ea59a09420ac089254a12a8f694fcd832b24157da216287cc0814b6bfd3e9c680256c9652230305ffed235588a48775679741c4e75ef884df5cc094d57595b498e224b3c698bf73c0009713575e61135519bf12c81485d2659c0f125e624ea24de99661e563c5d12a909af084b0f8907ede7d105a551d201d1fb4c
  | 6, 0, 0 => 0x3029ab0b2fd4b6942f1607bd2f11fd702ecd41412dcfddb22d780fbf2d254c882cfd8d5a2bedc5d12bdedf942bd36dee2a3d9739288899a124fa08c6230d2c7e22edf2a022d48e932237b4b52215f9ef20edeffe20929a791fde28751f1de22e1e5d01b71c5b95511c4999bd1aea6e0c1a2c019b1a12755b182be3b617af6c8a16ba1b82153dc90f13e7ea7f13c885491389bf84121079c111dc8fac116f61d20f9560200efd143c0ecea6820ddc47860db1c64a0da501c20d7999d10d275f760d0e52bb0c18961f0b16a67f0af6ed730ac3e21509b104fc0998fc1c0929baf608f6dbb006b7cecb049e3220044b6db603ee125d02e354b5029b3eb60081dde4
  | 6, 0, 1 => 0x60ac378160a95c2b607e1616602dec6e5f3c4d2a5f38b1aa5f3250f95e12e8275dc023bd5aa628485a5c0a245a17fe3859e9e15859c31801599fce475738c89656b1a87c561308b0558bb0725432b04253010dd252f160c752c3b2f352a98aba51bf936d51a921334fec18bb4f9a193a4f02fe524dbb31b34cc3d6cf4ba9d3944b7caab048766c38465fdb9144c0523b44277b894251007342378439422ec18640b4397340410a5a3f192df13f0afc333f098ffa3d6089e83cf59fa73ce2c1c13ca9f1eb3b8044543ae886593ad06f2f389792923891e7f6379c2fd2377c4b0135d3015e355e8e133347b36532fc7e7c32f7fd0132dec133325beb0131b05021
  | 6, 0, 2 => 0x925ebe0a91db2e5090e9c4cf8dada9d18d19fd948cd7a4ca8c95ff338c78e2518b0fcf348a9b7fbd8a28818c886b0dba8686581285a7c971856a29a684a1e078842a3f0783e6cbf783c89905833bb76a82eeeb6b813fd1ea81162b8f7fe032217f7287787f5540ab7d4f84c87d1e9e037c94a35e7c2cfebf7be36d2d7bc514717b3832d679c55aac796617bc78371883778492527706196e74297a2b71bbe90f70dec194701d61636f3cb6bb6cd3b62f6c16da506c123f576bb08dbf6bad3b4b6ad5364868afbc156821124f6769c68b669c157d658acf6b656b5a93646ba37a6440749a641daae2635ebbd4634135076224c73f61fb923b61bc76f8619b4dce
  | 6, 0, 3 => 0xc3b3b1e9c340192cc2e5c480c22af6b1c16fd0f1c1438dfbc03ce206bcdc5aeeba733478ba346190ba04a7adb9eb10bfb8d9f172b62a214db5da9890b4c87f1ab4ac218fb45f7f4eb286b549b092519eaeea03c9aecbdfe5ae824278ad73f346acd8212caafe928aaa46d0fcaa4191b8a96993e6a8d99a93a7fed1d9a76b4f4da764d536a6ce5f25a6c30677a6c08f03a4574d70a409ce84a3ee15a9a39b513fa2953e5aa2434c68a1b17899a0d7918aa0cf87d19f67cab99ebf81e39d1611799d13f6189cbba27f9c74f9fc9bea91159b97ccab9b41dafe9a62429e99d3c5d9997252789908cff298cf2cee98cc033d9627bcd296053d6d9577e7ad927eac92
  | 6, 0, 4 => 0xeb4b9c34eaf48ef3ea158b76e9d2b2a7e9c9ce4fe8f58028e8afba31e7874908e70eb3e5e59991dce5649a3ae542f83be4e20136e22d262ae0f1cc48e0def1ade03d9a2cde8e4475de3055cedde65253dd72b94ddb7c5bb1daaadca9daa43da4da80df53da7c516dda67ba7ada4a05cfd8a03ae7d856e61fd6a197add629b6f3d5180ecbd46a84f2d425c8c3d388d753d169122dd053618bd022f3becff51fcecf9b3956cf4fb688ce1dc8c9cd830333ccb78401cc9e6aa1cc044d5fcbb7367dcb8552bfcb780b12c9f37904c95fd88cc956a284c934fa39c91589c7c85246a6c7c0ff93c74f3428c74c31f4c6b9d7f6c694a89ac6660a79c62dd4b4c4d6fbca
  | 6, 0, 5 => 0xfea8ad91fd76ecabfd5e80cafd40af6ffc288677f6dbbefaf6a528fdf524d58ef4de5840f419caf6f3878204f34f20c8f210ca83f1ecc207f1d0efa4f1297289f11c1b10f0f904bcf08e10e8edb3505ced2150faec4582deebdfe0dd
  | 7, 0, 0 => 0xdaeef0b0da9502f0d5ae39f0d359d660c7515ce0c5be1980c1b94cd0c0104af0bd16bcb0b7cf6450b53118e0ad79ab60acc9fe20a5db90d0a36433509d41c9d09baeccb09937df409917c47097f4255097b206e094a91aa08c04d1d088ec9d50883b66b083591010828fed707e0fb8307b7fb5607983db6073325e00719241c06e2e06806d1977a06d133fa06bb320006b474760674bcee0672c3e80620bd3c0619093905ab6a7705a60b080573298d056404970560aa7205575f0b05406a46050cdc2204ddb5730429783903a7dab8034e7221026f7d87023e56a5023d26a30229321f020a349501c0cf2f01bda424016807810103037500a8eff10010041b
  | 7, 0, 1 => 0x1af080381ae554351adb9ef91aa0a2381a3d0b5f1a39cc121a0a201f1a0397ba19f7a8a219ed676819ac22b518b26e221892709818917f941788ef501783d36c17681a91171556271702826616fd86d61682538b162a36491609134215e3d4b9159e41e51534e57014da5bda14c596e1147be17a14498cb913b13c8e13ac2e7a13a4f3551383ce791357233a13315a4f1315562c1274662d125667471229b7271227f09d1205153611ef62541194d57e1183546d1182c6e9113fcc38108dfb0010873aff103915950fcf05c80f9f8c4e0f856abc0f7d0cdf0f0003390ed51c0e0ed4b88e0ebbdfe60e82974a0e6bfd880e5684bd0de050250db3a33c0db338d3
  | 7, 0, 2 => 0x2881547e27d27a5a27a744f827872db9273c4f3c2737a5c426ec44b126b7a5be26817b7526099ed525a22a7f2583885025271dcb24bc32c924a4de9024a1a6b223f4b53323dff6a62379a87f2371f15e2363757d23304577232fdfb722b12ef0228d066022880a072284b333226fc5be2254b62c2240fc3422272e9b21f0ebfc219e81df2185dc372118d8ca20fb4f1320bb33b5208cb324202d9691202b40b21ff147e71fcef5c61f9438771eb4212a1eb180c41e85d81f1e7897721e73f7591e0c97d61de8e6291dc0d5e41db3e6c31da1c6791cfe81b51cb356241ca711891c9308ff1c85d82a1c7f660e1c02e4e51bf4b44a1bdc203c1b5aa7ce1b4858b1
  | 7, 0, 3 => 0x35389f973532e67c34bf309d34bd92e334824e4b3403b3df338c9ad2338b1457337098c03326806b331102a832e8732132d4864e32c69f3432ac8e8131b30d7c3122624030759d4c303247ff2ff0c8502f953ec82f2d333f2ee11b4d2e2cb24b2e1f778a2ddbe4da2dba570b2d9010422d7eac952d457fda2ceec5e32ce4fe312cbfb75d2cbc57412ca863242c9c92ba2c35d6762bc312f32bb7e6892b77caf02b33ca0b2b3290202b2a190d2b18b8892b08aee72ad101ba2ac5b9242aa75ad22a88612a2a5f79ad2a3e98622a379df02a20277c29d523c129bfe79b29ac15fc296883742961a8832959c7692935e746290c466229007e6628acf73c289037b8
  | 7, 0, 4 => 0x437f917b436627984353c81b42f9159c42c9bb70427439e5426dd934426118cd424c63d041c887f74197cdb1417f83a64173da3e4162c42241588a44414e706240dc028640be667a3f313b653ebf5c103e098a5f3e0108f43d7e72543d71fd593d6e98473d1bf2473cf4fcd73cc117773cbb43653cb7623b3ca2e1bb3c7ebbf73c2cf4da3c08061b3bed95723bcc4b8e3bc01a9d3b901f663b58f2743a48df3c3a1fbb53395f96ae3928b26a38ceb1e838c4dd7b387cf5323872f208385be21d37655348374100aa371be0213715cd543705812c36f2504936df244036b1e5413622fc1e360f1ba735970f003583222d358231293574f688354288ec353f3678
  | 7, 0, 5 => 0x4f1874eb4ef588884ecd1a174eabb3414e7421054e5d1adb4e24e1914e10be834df656554deb64974de1bf624ce69ba94cb8f4624c2e2dab4c1de4d44bd0eb074bce73ae4ba07d3a4b92cec84b358aab4b3414874b3060ba4b0d46544afc9a304aa826bc4a4cbebc4a1e47444a01e9b94a00efde49a68b81499b52454983083a494860864926880b48e7cc21486b9cc5485d3eb74815a6f34804f0f947e5621747cd22e3477912bf472f49f74702dc3b46f506fc46b099304695e7ff462698db45eb319d45bd00e6457aef8e4541e848452dec8244e3171544af6d2d448a930944462f214430796e442d00d14421a80f441595d643e74c2043cfd022439cf8a6
  | 7, 0, 6 => 0x5d0305d85cf367e15cf0c0825cd503df5c4c78935c4617e25bea70c45bd1ec345bbb23a85b6d297d5b26af105b22d3925af1ba895aef23a75ab8a9c85aacd4df5a9cf1fb5a75721d5a715b805a2e99a55a2cc3f459a5928559196ee158c2ef5958c0f65358bcfd2358a7c81057f655b7578a7e975789f01b57378c38571af9ba57106ce856dc16c956ac910056abf8c1569e151f5611198655f8209255eaa36555a97397556da6c7555672e1548fcd225431b23f53b79f145337e0835310cae852996d67525043505232231852083abf51ac192d50d022c950c6d60e50b5442c509c95255008758d4ffb3acc4fb750c94fad60444f9dcc3d4f961a4d4f5a6fd7
  | 7, 0, 7 => 0x6b024b4d6ac4e77d6a698cb76a5e2e496a38ec4f69bc6b2669a77bb76991695b697e6e45697b90ed6954d60169506ea268ff83c268e057d568d267d3689eda76689777d86821124f68025c1d6793ee46677b653867796d5c67712c076722c01366fe990666c925b066704cbc66484c306625159d65d5f467659a5792655c4e5a64ef0a7e64b7656c647309a4644ffd2764499c7663d45e74632a33a462fec6b962d8cb5d62bc2e5c62adb27b62935a98623567bb61f432cb6151516d60dd8b7660c081b760a24bfb607ce25b605a53ac5ffed7895fdec53c5fae7b465f5bf45d5f4dc8b15f48864b5ed0c0195eca5fea5e6d15f35e6b51f15da496675da3ca9a
  | 7, 0, 8 => 0x78d69b63789be7d678740b52785ddb127843832f77e5f75777dfd53c77c666a777a60ff377323623772d50a876ce319075e8794b75b1a7e874f972b174f8aee274e4177e74d9cfda74d7cef374415c4d73fbe2cc73b7125c73b1119373a6bc307371dd967370e283734c9f767347fe8773286417727e079d7222b27971d3a02871cee00e70e8ab9670e3dc6970d5ec6770d14bca70cbec1270a7275b708d1f83704a65906fc727d96fa28b5f6f6d0f5f6f2eb18f6ecaacfc6e9f0d0f6e97e31f6e73d1506e0b00166df603116de2735a6da3d86c6d043ea96d025b646cd730016cd0cdf86c873f416c6b07056c5e9d666bf75fd76bcc8d236b9ca6a46b9b9cb6
  | 7, 0, 9 => 0x869993fc86519f6a86453eb9864345b3864120378574e55285539e728515b8cd841e33b9841371a884013fe783d4d7b783a7f6e48394a9d48379d2b58369a8098315c73282b0af5c82771924824ebd76823fe56f823d0f53823c975a8227626b819b4b08812d3dbb80c5100980a1645e8080ab1d805199b47f6c93bd7f491f307f2619507f223dd27f1dbf9e7e960f687e7ba7e07e5eb0787e103b177e0700227dfebfe97dcfc2677db6488a7d908acf7d495f677d347ede7d22d1117d2289917d1c28e07cf70da37cdd11327ccd7dcb7c85f1297c34289a7bfcc00e7b50240a7b1a410b7b1a20cb7a9eb29b7a98c0657a8d2c777a403fb5796200be78ec302a
  | 7, 0, 10 => 0x951f691794f752ac94f0f1fb94872291947cc7b2945fbc1393d611bd93d1892993810ddf937ec4bf934ff48a92fb6e8992721828923619c091ea244691d7069f91b813ea91b629f491869cbe912e86b9911fadd990880b65900d98039004c28d8f81b9038f6eb9328f577a9f8f295bc48ee6b5b58ec451bd8eb3ee738e902fad8e68f6f78e46ca478e3d634f8dabfb228da850658da284ba8d7869e68d3bd3218c6c2dc88c6c29718c39f18b8bf16b828be3e6828bd8ba188b76bbc28b6d2c9d8b1d15ca8b19b7c88a7a9db88a34206a89b668d388dd4a2e88a4e8f2888486d1887b09918790bb57877e346f87465dba87428a318738119c87299de486b04920
  | 7, 0, 11 => 0xa19522f2a14856ffa141a9c7a138fd27a12c4feda101dc92a0fe0114a0f982e0a0ca5129a09f4f5ea093d74aa0855b69a0779242a068cacba03a73baa03392da9f67cab99f4d72d69f320b879f31eb719efbd4e59eeec4469e33d4ec9dfb40999dd4a0cb9d5c02279d12b9ba9c6d66999c6b6d939c638aca9c44bee19c26fc249c0a3ca09c0945a09c029e899ba8ca2e9b6c59759b65def89b5bb1f19b53791e9af1f8a09ac04df89a8d7d6a9a399e549a2a447c99c5d28899bb987e99ba47d099ad2ed5991a12f1990ffb6b98f5fe4c98c6cc9597fd6b5a97e3684197ba2eaa978d6b2a9771c12e977147d6974a5a399667f78895a00a35959ee858958ffed7
  | 7, 0, 12 => 0xae7a07f8ae732135ae0bcf42adb1d04aad81abe0ad543dbdad433354ad1082d8acc344cbacb391a9ac8bb181ac8550d0ac598a13ab94a992ab8b1150ab65e7feab49c28aab377bdcaad1b77aaa939139aa3324b1aa00588ba9cecb1fa98165a6a9744f92a944cd73a90d5b2ea8909481a8866956a85b9c23a843d86da827cfbba76b4f4da750f76aa70aed3fa6b0199ca697cd48a6768364a640a41ca63f4fafa6375980a612076ea5dd0329a5b52466a59d7b87a596fabaa4484375a443bed1a43fb11da42a80b8a406231da3c937b5a35b4c3ba333f748a30f43b0a2cf61fba2b12677a2a0d34ba2925731a24ca910a23614c8a2066a62a1f93736a1dbf7f7
  | 7, 0, 13 => 0xbb49c479b9fb3ed2b9d468fcb9cc0f4ab9839c69b95c1f28b9238bb6b91f90c3b8ad8c6db8997bc3b8261bbdb7aeeec9b7aa7e56b7a8f6efb79ae05fb780781fb75e26bbb7454b89b6f2a7d9b6c4937ab6af85aab6a894c8b6358400b5e1844eb5ca4c10b5b77e2ab533f09fb4d59461b4c08736b4b27f72b49eb14fb4868a20b4260588b3fa7eaeb3c24a54b3bef058b34d471eb33dffa7b30c2abeb2a359d7b28f99edb28e24e8b274a0a9b2466a4cb23ccd8fb1e9f931b1908a5bb18896bbb1838f47b18017d5b177d426b0c4a235b0ab9910b0458977afedb434afec201eafb5dacfaf85cf8daf81c9c5af5aa227af3a1f85af173a4caedd696eae7c8ff5
  | 7, 0, 14 => 0xcaac0d7dca996e56ca546425c9f3d846c9c45eccc99664fac946bfc4c91fa0d1c8fd7c87c8f98b0cc8f8b2c0c89d7b8fc85246a6c83d4d94c825829cc81b12f1c77fb61dc71fc81ac6fa342cc677c7a3c6357f08c6315ab4c5b84604c5aeb032c57f7335c5093225c4f3c18dc46975e9c45b15b3c42e7276c423096bc40a0846c4085248c3f04a81c3e22da4c33155b1c2cdd7e9c2bf3383c2742114c1fec366c1d7ed90c15b6c67c1438dfbc134a7bec0e86e36c0e7a473c0ae4188c08a7c9fc03ddbb7bf6dea7dbf0cadf4becd8a39be390894be29aebcbde508e2bdbb02bebd78731bbd1acfdfbd197d31bcaa6aafbc4566a3bbf07120bbdea910bb806acd
  | 7, 0, 15 => 0xd74112a8d70b94fed6e7a459d6b7954cd6a04de8d6827ea1d66ede3dd64054a2d632e366d61a90f7d60e4952d60a019dd5d51448d59ecc27d55d9e42d51552b6d4e7b833d4e60e6fd439a2cfd430d163d41890d1d40a27d4d3ff0dd7d3d3e2c2d3b5450fd38539cdd2d4b27bd2c00a2fd2b65212d257e8b9d23889ebd2098388d1c7e360d1bac628d1b1b30ed1a93217d18f4277d1566dadd130e37ad0eed897d0eb3043d0b92cb0d0b2fbe9d06ac56ad008a737d00843b7cf249d9ace8dcdf0ce4e34aecdd100f8cdae86e1cd4ee83fcd3d1ce9ccc52a17cc67d89bcc5e9a47cc1fd388cbf05c1dcbd50cbbcbb8d6e8cb5012d4cb3b3297cb349801caea07e8
  | 7, 1, 0 => 0xe5c458a1e542f83be4a8a4cbe493496fe46f7636e458c67ce399e8fbe38f2d78e38d55f2e319565ce31177c2e2d1c9bae2b50a36e28a04cae27552aee2199ef9e1f74cd8e1e4d452e1e47322e1410c7ae0f74a87e032063ee00571fedffb16f0df4022ffdf2259d4deeb28edde97d81dde7c5035de4f3b30de3eec65dd5c2e0fdd580b4fdccedae9dc29c0fddbbe3bcedbaaaeb5dba90328db67a329db3dab48da9ee4ebda868036da7ea9a1da211020da161a65d9e0ee8ed9c9b650d9ae803cd9acb6abd95c3b61d959f241d93d87e6d8ec627ad8e17f45d8d69c0bd8d63aa6d89dfb22d8316a54d801ed6ad7ca020fd7c698f7d793416cd78489b0d77e4e07
  | 7, 1, 1 => 0xf4081177f396896af3733036f303696bf3031826f2d2bd4ef287c40cf1e406f9f16ad3a3f1411580f1195156f0c49457f065cdd6f04f03a7f04df3e5f04782b3f0029d09efd46819efa703a7ef35bc87ef0f63e1ee4053a3ee36c9a5ee28865dedf34286edc3c90ced5d787bed3de999ecf958ccec9ca3e1ec87d0bfec83f7cfec72facaec61014eebb11d6beb7f205deb72283ceb5ffc3fead54e4eead47602eaa78c21ea9a6fcaea843f78ea4e9f6fe9e08265e9c3c2e1e9b1cab3e984f115e97be937e93d90ece935373ae9060583e8197b1de749b073e6f5d7f9e6eae76be6e489dbe6cc61c0e67c845ee673c6dde652bfc4e645392be6334511e5e1b3ec
  | 7, 1, 2 => 0xff7f6c7fff7b156fff6b706aff640b3dff3d1588ff123350ff0402b5fe8b7e2afe554becfe1584a5fde47742fda28674fd76da79fd43650bfd3ce5b2fd2ce99afd0dd52afd03f230fc7878f8fc30d494fc24ab7bfbec75b6fbe1b6edfbc1bc8dfbb3721efba57992fb88fb78fb6b568bfb5c9134fab6ff8cfa6aefcff9963cc4f869526af84aa17ff82e5cddf8037aa5f7f54a0af781aefbf760f6a9f7429dedf6da13f8f6b5bc52f64a1ac2f60c94a5f5ff2455f5c74da0f5c1b207f5b4f1e4f58eacb7f560fd0ff492a2d8f425a199
  | 8, 0, 0 => 0x1c02e4e51b9b06e31b96e8611ae554351acafc521a51558f19b15e68196939d21957081119179537186b8f5c17c2485d17a485a0178028051742223f1703b38d168319a4161ad83314c25be7147be17a147805fc147387c8144456111439cce4140ddc3213b478a2122bc8a9111d5c611106cdc71101c9f510eee49c108cbea20ecd7e060e532e160db6ae630db3a33c0d359d660c9500f20b5d6d290b203b970b15b6280b0770120970372308719fb80801277907f0d02405e2e7ad05a02dba04e56c6204be9b5d0499b2c10451cc9a0402104d03edab490327c54502fbbdeb025a06d3020fff7e01dd076b01c0cf2f0193adbd0122554d011dc73700f26ece
  | 8, 0, 1 => 0x3fd89f2f3fc0243e3f9ad3953f521ef63eca17bc3e0da1cd3d9f9c853cc117773c79d3023c05e1c63bcc4b8e3b9517d93b76d13c39c95bf0392a12193889bf72386dc675376a4f69375c328c35db239335895b043578c84e3551f27834bd92e334bca48e31c32ec331b30d7c315f0dca313507a630c2219f30b17a1b30a941482d6782ad2cfda1512cc710002c9d909e2c33b3742ad82ba328a5bcb427d93e0027928aca273fec7026c74c0626b6092925e00859257200952563fe1925029ba3250036df24f1d90e24c4815c24ba3ed6241a19e7240356ad23bebf212238b79e21f40ce0212bd5321feb40ca1eb180c41e21c84f1da0f8bb1c7f660e1c1160c6
  | 8, 0, 2 => 0x5bf8a09c5bcd8fcd5b919bb95b8b473259ccc4ac59bf3e13595fd070595bb8d458bcfd2358871ddb572b3dcc56cdce4e56b13491563d6c9d560409b25593a3e1555e780a54bb1162538ed0be537f76e65310cae8526f455b52652dd551529dc45123e01950d632f7509f8ca34f2308104eb1e7524def43ed4d2f3c8a4d2885244d26bb934cfebf194cd640494cd3f7294cae6cf64c50a0f34c1021324b8b4c2a4b0d465449d837ae497bcdb2490e14d748a30f4847e5621747aec13b479295b946d9577146cd9c50465f78f8463a0f1745d1eda14541e848452bb7f644aae8624433319843cfd02243cc419643a4cbbe411da5b740f62fdf409f8ab4408d4406
  | 8, 0, 3 => 0x7c3a52057a98c06579930e2179200ff078e4f5a278ba6f2e78a93579779b444e773a3b4c7651891875a33707751d0c7d749f06a773f742fa7391a15173793d24735a86ea733d135672f58c2c7278be20711403f86f36b6b86f1f7e7a6ee55b736d42739e6cd46e566c96dad26c615d286bf88c416bf2d3266be357526bd02c766bc4a6676a75398c6986998d69415288690b0d3968db01f7685bd80f67108e526640f86d6608c4136601c8f4655e0be164bb1a68621b7fc5620d6f8d61fe340661b0ce8d61759bb261677585611f665760c081b7608a602b603fd0126001d5a75ff63ef25fecffb25f6ce3e65eec2d245e4f53365e4e7aea5e471a635d017f51
  | 8, 0, 4 => 0x9a80d3c49a31aaa698e639c898c8770b989ed46797de4ccf97b7adba97941ecf966e67f095feb81b956af0e494ffe11f9492ddb29406f9df936b4ccf92bd4609928a057691ffdd0791869cbe911bcb6190dec3a2902d5b0c900cc7b68ff96af68f95124e8f87e3d58f66a91b8ed4acb68e6a85208d8425078cb80d3c8ca877188c90870c8c0b847c8b1d15ca8b02f4388ae474e1895dd9a188c8f8608899f1fd877f470c8726336286bb2776861a5c8185db428985b3ccb185a3bc0f84fccbd184d0ab2d84013fe783b31a7d836a9b7e83490ab083199136824f20f6824ebd7681f4635f81a2fbbd8128f3f38124f5e780d4e887805efbd87dd7bdf57db0481d
  | 8, 0, 5 => 0xbe769f18be620e8cbd15572dbcfd0d22bbe6ae2bbbd7439fbb5f66ffba11faf3b9fc0058b9653685b93140c9b8b93da7b7aa7e56b749d50ab6e02c80b5c668b8b40748eeb1838f47b158ad0fb14a7c74b0b62913b0b06ff8b03b1c5fb0316723af0a244eae08364cad1f9a1cacd99b96acab5189ac584a90ab858806aabb0592aa70fe3da99d0106a8fc3611a8aceb64a77db8c7a7420870a6ea9da8a6d91c97a64e8b36a5dd0329a57263d1a42a80b8a3efa234a3d3d878a3ac4ce7a304b735a26835d3a039bc45a022680c9eadcef39df24a1a9de491ff9dd97e959cee05e09ce2885c9c26fc249c0a3ca09bed4a379bca85189b6ed1639b4c7f429b0132a1
  | 8, 0, 6 => 0xe173acfee0b0bd65de7c5035de139a83ddb2f137dccedae9dc851221dc06615adb7c6105db2c04c2dabcacbbda70651bda025fd3d982c8fbd7cf11d9d7ca020fd7c3a15ed7c1c93cd753c3f4d6a4388cd69e5019d6363344d43a869fd35f5289d358ca24d2c7c583d271ba71d24ac501d175aa0ed0ab1f49cf352890ce16f6e3ce0e84ffcdef7705cdc8ba32cb78c448cb694c08cad8ea57cad7f953ca94fea2ca1e5d15c9d81675c98e47ffc972257ac87c4895c82a4e78c7abb727c76b3ee8c708d5a6c68acfd0c5ca4838c5547d17c3827a75c3753fb4c3101f35c2d474bfc2157f87c18ac36bc088584ac060a091c026c9e4bf75efa6bf1a8222beaf8f93
  | 8, 0, 7 => 0xffb3f673ff123350fee73185fe971ab2fdf4a2a0fd76da79fcd4c3e5fc4e4806fc1eeddafab21684faa3a2ccfa1398e4f9dd0963f8037aa5f61649e1f5f81425f542c7dcf4ed8e48f071128bf05ab396f04782b3ef2e9b0feeca28f2ee18b783ee12c54ded71f1d3ed03ec8becf3ebfdece046c1eccf062fec663512ec31def3ec01c0ebebf3dd49eb8687baeb6b0ca8eb5881baeb406b8feb2014dbeb1c83beeac36ef1eab44034eaac3b0bea483678e9f6ba3be9b88a37e9877a69e8f3ed30e8a9e5dbe892c0b4e7baf5ffe7311744e72b167be68136c5e604fcffe50d18f3e45de151e44ff14fe44b50b2e3a3bb46e3412cc1e2182b15e1edd638e183f5d5
  | 9, 0, 0 => 0xfe971ab2f9554771f92dd199f61649e1ee12c54deab44034e5f2c308d43a869fc708d5a6c68acfd0c0a94172c02871debc1d1430ba47a138b749d50ab40748eeb158ad0fb03b1c5fa4234630a0e187958ff96af68f8b65ae77cbd18269904ec962a89ff75d017f5146d9577144efaef63ef2c9303e51fe3b3d084ce73ba45360358f846f242a74e01957081117a485a0167ebc1d0ee8d64b
  | 10, 0, 0 => 0x69904ec9
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xeeeeeeeeeeeeeeeefaeafaeafaeafaeaffff0000ffff0000fafafafafafafafaf0e0f0e0f0e0f0e0ee00ee00ee00ee00f0f0f0f0f0f0f0f0cccccccccccccccc00ffff0000ffff00f0f0c0c0f0f0c0c000ff00ff00ff00ffffffffff00000000ff00ff00ff00ff00cccc0000cccc000055555555555555550f0f3f3f0f0f3f3f
  | 1 => 0x33333333333333330f0f1f1f0f0f1f1f1111ffff1111ffff1111eeee1111eeee0000ffff0000ffff0f1f0f1f0f1f0f1f11ff11ff11ff11ffaaaaaaaaaaaaaaaa11ee11ee11ee11eefafaaaaafafaaaaafaaafaaafaaafaaae0e0e0e0e0e0e0e0fafaeaeafafaeaeaf0f0e0e0f0f0e0e0eeee0000eeee0000fafafafaea00ea00
  | 2 => 0xf0000000f0000000ccccc0c0ccccc0c00f0fffff0f0fffff0ff00ff00ff00ff00000ffffffff000000ff00ffff00ff000f0f0f0f0f0f0f0ffff0ffc0fff0ffc0f000c000f000c000fcfc0000fcfc0000fffcff00fffcff00fc000000fc00000000000000ffffffffc0c0c0c0c0c0c0c00303ffff0303ffffff00ff0000ff00ff
  | 3 => 0x1f1f1f1f1f1f1f1feaeaeaeaeaeaeaea111111111111111100ffffff00ffffffffff00ff00000000ffffffffffff0000ffff000000000000ffffff00ffffff00ff000000ff000000ffffccccffffccccffffffffff00ff00ff00ff00000000000f0f0f0ff0f0f0f00f0ff0f00f0ff0f0f0f00000f0f00000fff0ff00fff0ff00
  | 4 => 0xf0f0f000f0f0f000ffff0000eeee0000ff00ff00ee00ee00fafafafaeaeaeaeaf0f0f0f0e0e0e0e0ffffffffeeeeeeeeeeeeeeee00000000ffffeeee00000000ff00ee00ff00ee00ffffeeeeffffeeeeffffffffee00ee00ffeeffee00000000ffee0000ffee0000ffeeffeeffeeffee1515151515151515e0e00000e0e00000
  | 5 => 0xfafafaaafafafaaaeeeeee00eeeeee00fafafafaaaaaaaaa0505555505055555faaaaaaafaaaaaaa05550555055505550f0f0f0f1f1f1f1f00ff11ff00ff11ff0011ffff0011ffffffe0e0e0ffe0e0e0f000f000f000f000ffaaaaaaffaaaaaabbbbbbbbbbbbbbbbf0f0f0f0f0f00000fafafafafa00fa00eeeeeeeeee00ee00
  | 6 => 0xffaa0000ffaa0000eeeeaaaaeeeeaaaaee00aa00ee00aa00f0a0f0a0f0a0f0a0ffaaffaaffaaffaaea00ea00ea00ea00fafafa00fafafa00fafafafa0000000005050505ffffffffffffffffccccccccffffffffcc00cc00f0c0f0c0f0c0f0c0ffccffccffccffccfafafafafafaaaaafafafafafaaafaaa0055555500555555
  | 7 => 0xffeaffeaff00ff00ffffffffeaeaeaeaeaeaeaea00000000ffffffffea00ea00ffeaffea00000000ffea0000ffea0000ffeaffeaffeaffeafcfcfcfcfcfcfcfcfffffffffcfc0000ff00ff00cc00cc000000000000ff00ffffffffff00ff00ff00ff00ff00000000ff00ff00aa00aa00ffaaffff00000000ffaaffaa00000000
  | 8 => 0xff00ff00ffffffff00000000ff00ff000000ffffffffffff00ff00ffffffffffffaaffaaaaaaaaaaff00000000000000ffff00ffffff0000ffff00ffffff00ff00ff000000ff0000ff00ff000f000f00ff000000cc000000f0f0f0f0c0c0c0c0cccccccc33333333cc00cc00ffffffffcc33cc33cc33cc33ccffccffccffccff
  | 9 => 0xfc00fc00cc00cc00f0f0f0f000000000fffffffff0f0f0f00f0f0f0ffffffffff0ff00ff00000000fffffffff0f00000fffff0f0fffff0f0f0f0000000000000000fffff000ffffffffff000fffff000fff0fff0fff0fff00fff0fff0fff0fffff000000ff00ff00ffff0000ffffffff00000000ffff0000ff000000ffff0000
  | 10 => 0xff00ffffff00ffffcccccccc00000000ff00cc00ff00cc00ffcc0000ffcc0000cc00cc00cc00cc00f0f0f0f0f000f00000ffffff00ff00fffff0f0f0fff0f0f0ffff00ff00ff00ff00ffffff0000ffff0000ff00fffffffff0fff0ff000000000f000f00fffffffff0fff0fff0fff0ff00f000f000f000f0f0fff0ff00ff00ff
  | 11 => 0xfafafafafafafafafafa0000fffffafaffff0000fffafffaff00ff00fafa0000fafa00000505ffff0505fffffa00fa00fa00fa00fa000000fa00000005ff05ff05ff05ffeeeeeeeeeeee0000eeeeffffeeeeffffeeffeeffeeffeeffee000000ee000000e000e000e000e000ffff1111ffff1111ff11ff11ff11ff11
  | 12 => 0xffffffffaaaaaaaa00ff55ff00ff55fff0f0a0a0f0f0a0a00f0f5f5f0f0f5f5ff000a000f000a000ffffaaaa00000000ff00aa00ff00aa00ffffaaaaffffaaaaffaaffffffaafffff0f0f0f0f0a0f0a00055ffff0055fffff0a00000f0a000000f5f0f5f0f5f0f5fffaacc88ffaacc88ffffffffffaaffaa0055005500550055
  | 13 => 0xfc00fc00fc00fc0003ff03ff03ff03ff00000000f0f0f0f0ffffff00ff00ff00ffff0000ff000000ffffffffff000000aaffaaffaaffaaff0033003300330033fff0fff0ff00ff00fffffffff000f0003333333300000000ff33ff33ff00ff003300330033003300f0f0f0f0a0a0a0a00000000055555555ffff0000aaaa0000
  | 14 => 0xff33ff00ff33ffffaaeeaaffaaeeaaffffcccc000000000000000033ff33ffeeaaeeaaeeaaeeaa1155115511551155f0f0f0f0f0c0f0c00033ffff0033ffffffeeaaaaffeeaaaaf0c00000f0c000000f3f0f3f0f3f0f3fffccffcc00000000ffffffffffccffccc0ffc0ffc0ffc0fffcfcfcfcfc00fc00fcfcfcfc00000000
  | 15 => 0xffff0f0f00000000ff000f00ff000f00ffff0f0fffff0f0fff0fff0f00000000ffffffffff0fff0fff0f0000ff0f0000ff0fff0fff0fff0fccffccff00ff00ffeeeeeeeeaaaaaaaa0f0f0f0f3f3f3f3ff0f00000c0c00000f000f000c000c000ffff0000cccc00000000000033333333ccff00ffccff00ff1111555511115555
  | 16 => 0xf000f00000000000ccccccccffffffffaaaaaaaaffffffffffffccccccccccccffffaaaaaaaaaaaaffff0f0f0f0f0f0fff00ff00ff000000ffffffff0000ffffaaaaffffaaaaffffffccffccccccccccff0fff0f0f0f0f0fffccccccffccccccff0f0f0fff0f0f0fffffff0000000000ffff00000f0f0000ffffffff0f0f0f0f
  | 17 => 0xfa00aa00fa00aa0000ff0fff00ff0fffff00f000ff00f000fffff0f000000000f000f000f0000000f000fffff000ffff0fffffff0fffffff0fff00000fff0000afffafffafffaffffcccfcccfcccfcccfccc0000fccc0000faaa0000faaa0000fff0fff000000000fff0000000000000fff00000fff00000ccc0ccc0ccc0ccc0
  | 18 => 0xf0f0ffff0000fffffff0f0f0ff000000fff00000ff0000000f0f0000ffff00000f000f00ff00ff00fcfcfcfcccccccccfcfc0000cccc0000ff00ff00f000f000ff000000f0000000ffff0000f0f00000f0f00000f0000000f0ff00fff0ff00ff0f00ff000f00ff00afafffffafaffffffcfcccccfcfcccccfc00cc00fc00cc00
  | 19 => 0xf0c0c0c0f0c0c0c0f0a0a0a0f0a0a0a00f0f0fff0f0f0ffff0f0f0f0fffffffff0f0fffff0f0ffffccffccffccccccccffff000000ff0000f0f0f0f000f000f0ccffccccccffccccf0f000f0f0f000f0ccfcccfcccfcccfcf0ff0000f0ff0000ccffccff00000000ccff0000ccff0000c0f0c0f0c0f0c0f000cc00cc00cc00cc
  | 20 => 0xf0f0c0c0c0c0c0c00f0f0f0f0f0fffffff00ff000000ff00f0f0f0f00000f0f0ff00ffff00000000f000f0f0f000f0f0f0f0ffff00000000f000ff00f000ff00ff00ffff0000ffffffcc0000cccc0000f0c0f0c0c0c0c0c00f0f0f0f0fff0fffcccccccccc00cc00f0f0f0f0f000000000f0f0f000f0f0f0aaffffffaaffffff
  | 21 => 0xffccffccff00ff00ffffffffcccc0000ffccff00ffccff00ffffffffc0c0c0c0ffc0ffc0ffc0ffc0cc88cc88cc88cc88f0f00000f0f0f0f0f000f000f0f0f0f0f0f00000ffff0000f000f000ff00ff00cccc0000ffff0000cc00cc00ff00ff00c0c0c0c0f0f0f0f000000000ccccccccf0f0f000f000f000ff00cc00cc00cc00
  | 22 => 0xfffff0f0ffff0000
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x1820302915a8101a0e05829408030886000a0904060541b506820303302a8c45c180288d40812088600aa0404820020750203412180ba810441810815408030984822a03110604223502018040102a810041800015406020c00046a040304430055020241e1803a80c10181986d408030b04428a0401830241150200c260608a81006120c075412080c01c46a04170605a0550200c260908a83440080c0a54062e0c0b446a04040605207503008300511a83440090c07d40803030603aa0d0406058235
  | 5, 0, 1 => 0x10602f170614080d0586032a04128904418502020303202a81010181606d406080c0c846a09040600a2b50680c200907a81050270106141a080c0a454a040685414145020341c0905289844180288d4080d0602c14a0406828301a50202c14180da81006110c079408030100400a0401824301c5
  | 6, 0, 0 => 0x1201a09078600ac00020e01018148f18000401854120f0db00008360484430056000101a03288241ec000680cd04f04061800450680c12180fb0000854018241e116000104a240482030c00048603e050d88d800041c2a05e080c300008030482030a66000101a47060241ec000225410184a06d80035068d01e1814b0001a090c0f40a236000d41a860406052c00020349a0c0483d8000401830620f08b000080d2a00c123d60001006160483c22c00020dcd209040618000d2200c1e1814b000080d0182030596000353609040600ac0002034060c078fd800040680c18311eb000080d01858123d6001dc08031308830c000003406080c0cd4009d01820309c0db0001a090420830056
  | 6, 0, 1 => 0x1006900406052c0002034064c2583d8003804820303c11b000080d2a02414086001141a030406052c00020dc120f2f061800040691c1e1814b000080d35824d40860001018090781436c000406052050d88d80004069341e1814b0001a09170600a2360001006090304430c004c8c410180288d80003060241e1b11b000080d0499014186000000826110600aa000200c180f0a06d800040680c980907b000080d0482082056000107037060241ec0002034060800801800381b820302911b00008030483c30576000106c09010040ac005383412080c1cd8000401974120f0db000000313088302350024806080c0a522c000680c12082088d8000444020302943b0100685048c410187
  | 6, 0, 2 => 0x352a080c25046c004e83410184e015800040184c0c020c3000060f0c0a4362360001006314c0b830c000200c0c020c001800043780c126e043000084e01820302960001070370786052c002200c12080c06d800040680c180f16b00008030300830056000101a030602c1ec000200c021f1486d800000200c10181928006a0d1a0200229600010c6090506036c0002034060f0c069800040680c120f20b00008030583c301b6000101a281382030c000203406080c0b180004069ac126d04300000040682502185000106037048603ec003e03406091f021800042180c101814b0001a180f8a40a236000101a030702c1ec000000c12080c0ad400030482030670db0101a03060241e507
  | 6, 0, 3 => 0x34060c0785046c0002034c60a0c0a5800650680c12181eb0006a0d3b024301f60001012010f81436c000200c6e0c1883d800040680c185207b0000803060c41e1b60001006160483c36c000200c62110a061800045102030a10db00000040682c141850001006090904430c00020342a0907815800042300c180908b00006090087c36236001141a03048607ac00020dc12080c01d800381b9a012080c3000080d2a82828186000d41a34048f810c000211806090c07580004180dc101814b000082501898441860003406150483c46c000203406091f0f5800041c0241e181e3000080d018541e146000e806080c0a51ac0002034060e0483d800040786052050db000000d04820302a5
  | 6, 0, 4 => 0x3406010f8a446c000200c12080c15d800042300c221814b0001a0904060ce056000101a03310241ec0006a3c101814a398000304004521b11b0001a09040600aa56000e812080c0151ac00020e06e08008a586a374502462080c3800080d0196c120f600010a8030484410c001d83410181481586a341b82462080c38006a0d45020302960003418090781446c0002034180f0a01580035068d0101814b000080d01830960f6000241e180286c46c000203406091f201800040185812110430000854018241e1b60003488030406052c00020c006311706180004018c4101819300008030482030076000101a5d0483c0ac00020c012080c0f180004018184e020c3000d009040600a1b6
  | 6, 0, 5 => 0xc12080c29846c001a8d012180f86d8000d3d80c123e0430000803060247a1b6000d41a720406052c0002034fe091f0218009d4f02030050db000e80d048603e7360001006080c0b464c000683c30290288d8000d03020300511b000080d2a00c1e296000101a4d0406052c00020340609050f9800740482030730db00008890406052056000101a630486032c00020342a09078298000002018041802a800080d0087c52056000101a03098241ec040680c12500a061c6a0d5422812080c38000828018180418600010f403048f810c00020e01208008f1800000203410181628006a0d3b0203029602034ac030483c30e000202002290286d800952a820301b11b00000030300830235
  | 6, 0, 6 => 0x1006261106042c0002034840c04829800040482030054bb000760d0483c30056000101a03058f810c001d0e41018148158000406830620f02b000080d0b0241e0560001084090506036c000695006090788d800040189848220c30006a0904061181b60001012080c0840ac000182030290d88d8000304820309711b000743901830120f60003412010f81446c0002264602f040618000d0482030a911b0001a03060c41e2360003406160483c46c000211812110c015800040482030a602b0000004018b8302d5000101a030b03c28c0002034060c0903d800040680c120f2d300006090406042236000101a030406034c000482002050d88d800040182c10180db000080d0184c0c0f6
  | 6, 0, 7 => 0x26406080c0b446c00020e06e090c0f58000406824160a0c3000080d0184c240f60000008030304430a000482030050d88d80004018c45c1816b00074390183c30296000101a030a8247ac00000344009040614000d04004520511b0000803188b830056000108603060241ec003880c12080c06d80035068d0301f14b0001a9304060522360000d20080c0a446c0022834060c0483d800040680cd83e0430001a34048603e7561a8101a030483c7ce001a8d010181486d800040680c1e182cb00008030c0f4521b6001281a030602492c00020340c0f0c0158000406950120f02b000080d0185428086001d01a080c0a4e6c00068241018518158000002024101803a80008080c0a40a1b6
  | 6, 0, 8 => 0x1201a03060241ec0002034a80907829800450680c1e1814b000080d060247a05600034f0220c01446c000680c10180008d8000d048f8100511b00008090406078076000100634188b830c0002024303d0286d8003604808300511b0001a340406052756000101a03258f810c002503406490c0a5800000200c0c0200a8000899040605a05600034060c048f446c00020d806090c075800000200c0418002800080d01830283d600010d6030300830c0006a8012080c1cd800660680c921814b0001a090c07c0a236000109c03060241ec001a834065d0483d80003048607a1b11b000080d01984120f6000101a420506052c0002034060907981800040680c120f2e30006a0d04060528c6
  | 6, 0, 9 => 0x3406181e8a446c001a8353e0904061800040690812180cb0001a4401830120f60200c6e841882030e000680c120f1f08d80004069e4126a043000084e0183c30296000100631178b830c002200c120f0c06d800040680c18110a30001a080c0a40a2360001070541b8241ec00000340609418614007e0680c127d0430006a0401898441860009812080c01446c00020342a09050218000401898441802b000085401824620f6000101a030613c1ec000001006220c08540004068481e1802b000080d0483c305860029012080c01436c000203412531e8158000406818100102b000080d2a820302c60001086030786052c00020341018000158003506a2c101814b000760d0482002056
  | 6, 0, 10 => 0x10622e0c015400040680c1e180f3000080d0183014146000112c951782030c0006824a6180288d800040680c180f2030000003188b83023500010301f1481436c0024034060f0c0a5800040680c2c140430006a0d3802030296000101a181e8a40ac0002034123e40015800041b00c221814b268063704a6010187000101a030786000c000001006120886140004068241e3e02b000080d04061282c6000d41a34060241ec00018603e290d88d8003a1c80c100114b000080d0197c120f6
  | 7, 0, 0 => 0x101a03048f810057001ac060904060362370003406370406052237000101a03060241e1b7000101a035502030297000101a031a02002297000d41a031a024301f700010c60304820021b700000080d07860520560003406080c0a43623700000080d03020300560000008381b82410016000101a03048603e2d700034069304820302370003406090782830237000101a09668203005700010060904061801b7000106c03048083005700010703704820302970001006370483c301b7000101a030484428187020340676048c410188000101a030406052737000d41a039502410187000101a09042b80205700010060940020301b7000d4080d01824301f7000101a28018181018700000760d0482030056000006a0d450241018600012160d0182030297000013a034f020301b6
  | 7, 0, 1 => 0x101a080c0a40a1b7003581a0304c3c10187000101a0907828300570001006092a820301b700010060936020301b7000001a8f04820308e6000101a03048603ec0700011900304820302d70001006095a83c301b7000101a0304828441870001006370484410187000d4080d019e044187000101a035682030297000341208010600a23700034f009040600a237000e87203049541018700010060987020301b7000101a3901830120f7000d4080d018247c0870000006090400436236000113230018c410187000101a0370824101870033c0809040600a1b7000101a03848203029700034720304060522370000c12080c0a436237000101a033c08830057000101a031b830120f7000101a0304820301d70003406080c0a4469170023c06090406036237000d41a6b04a7810187
  | 7, 0, 2 => 0x10a803048c410187000101a03049b0301f7003201a030406052237000101a030613c10187000112c03048bc10187000006a0d3b02410186000101a031885010187000101ad00482030057000101a03040607a29700011fe0d018203029700011100d0483c3005700420080304060521b7000d4080d1b82030297000000809040040a1b600010068a04820301b7000001a03048043e236000101a3904060520570001012080c0a40a1b70033c080d048603e05700034129e040600a237000001a0304c4030236000101a095a02030057000101a030483c3019700010d609040600a1b7000101a3704060520570000008460182422186000106037048c410187000101a0304ce01018700198080304060521b700034d603048603e23700010063404820301b7000101b240482030057
  | 7, 0, 3 => 0x1a68048203005600000080304060521b600010060883860521b70001070541b82410187000000803048203097600010060904060788770001012080c014362370001006094f020021b70000008890482030056000340609042ac02237000d40803130241018700304080d0182030297000d4080d35824301f700000080d048043e05600000080d04c4030056000007439018203029600000080d01830620f600000080d01858120f6000101ae4018203029700010062604820300570000e76090406036237000101a0304c68101870003406090406078237000101a6b048603e0570003622030482030237000101a30048bc10187001141a030483c10187000101a030483c801870003406091882030237000000803048203021600000080d5102030a16000101a096902030057
  | 7, 0, 4 => 0x101a032f82410187000101ae00482030057000101a090c07c0a237000118e0304820301b7000d4080d04820303c7000340609550203023700010060904364301b70003406090c07c468e7000001a09078600a2360003406092a8200223700010063704948101870003406091f02030237000d4080d0182030297000127609040600a1b700000080d018181e18600011e603048c410187000101a090406078057000001a030482030bf600000080d2a00c120f6003681a0304a7810187000101b110482030057000101a099b0203005700000cc0d04ab830056000101a094002002057000101a031a0247c08700000080d0192c1e186000101a091882030057000101a030406052057001d0080d040605205700000080d268241018600011900d0406052057000101a030482828187
  | 7, 0, 5 => 0x200c6e091883c10188000101a092a82002057000101a031b83c302970003412080c01436237000101a0304b64301f7000101a0304d30101871a8101aa81b82410188000101a091f02030057000101a0307860521b7000101a034002030297000101a952a8bc10187000100637048c4301f700010060917820301b70033c1a0304060522370003406ad0482030237000101a030483c303f7000101a952a82030947000d41a34048c41018700010060904061281b7000d41a340602410187000d41a031a02030297000340609078083023700010060904061421b700010067604820301b7000101a092a83c14187000101a03048c4303d700012160d0482030057000006a0d3902410186000101a03040605a2971a8100637048c41018800010060905020301b7000101a09042ac02057
  | 7, 0, 6 => 0x33c080d04060520570001110091882030057000101aad0482030057000101ad70495410187000101a03048bc301f7000101a0348024101870001012080c0150e1b7000101ac20182410187000101a090780830057000351e030406052237000101a0304c9410187000340609ac8203023700010060942020301b700034d6030406052237000101a030493c10017000101a030482030e87000101a03048603e947000347209040600a237000101a03048603ea17000101a030a824aa0f7000101a630182002297000101a099a82030057000101a033b024301f7000100609188220e187000101b160482030057000101b010182030297000101a390183c30297000101a0304828301f7000101a030406052c070001006091883c22187000346e09040600a237000101a095502030057
  | 7, 0, 7 => 0x1a952a82030236003201a09040600a2371a8101a030483c441880000006090406036236000101a030406052f27000101a09040607a0570003406b9048203023700010060904061b01b7004200809040600a1b7000101a03044343029700010063704820021b7000101a030494c30057000101a6b0406052057000101a090c07c0a87700010067204820301b7000101a031a02030297000101a099982030057000101a094f03c30057001980809040600a1b7000d41a3404aa810187000101a09990203005700368080d01824301f7000101a430182410187000101a030882030297000d81a03040605223700010066804820301b7000101a03870203029702034600304a6010188000001a030400452236000d41a0304a6010187000101a0904388300570001223120182410187
  | 7, 0, 8 => 0x340609040605a237000101a0304822a818700011f20304820301b7000001a03048603e236000101aa00482030057000101ab9048203005700034066804820301b70003406093702030237000101a031b824021f70000074390482030056000101a038f824101870200c6e8a048c410188000101a0304820312370003406090c07c46dd7000101aaf0182030297000101a033602044187000101a030482030cc700198080d048603e0570000e78090406036237000101a03060241e23700012260304820301b7000d406094f020301b7000101a030483c303c700010700d01824303d7000106c0d0406052057001141a030482810187000d4080d01824a6187000d4080d358203029700000080d04004520560001006df04820301b70200c6837048c410188000101a034502030297
  | 7, 0, 9 => 0x10072804820301b7000101a0904061aa057000101a030483d641870025406090406036237000000803048607a1b60001006371882030297000101a032902030297000101afc0182030297000101a0937020300570001222030482030977000006c0304808302360003406370483c30237000101a030494010187000101a0304aa81e18700011100d048200205700010063104060521b7000101a4201830120f700010060907850301b700000089901820302d600000e80d0482030736000101a080c0a40a237000d41a0304a78301f7000101a030b024620f70038c080d0182030297000101b3404820300570003406080c0a4468e7000101b040182030297000000809040600a1b6001dc08031302410187000101208838600a1b70001084030483c301b70003406373402410187
  | 7, 0, 10 => 0x101a032882410187000101a031782030297000101a032a85010187000d40803048603e1b7000101a09078600a1b7000101a0304822801870003406090882030237000101a09400203005700010060904061381b7000101a030406128297000101a030406052a1700000080d01830123d6000101a03048f8d4087000101a033b02030297000d4080d01824303d7000101a030502030297000013a0d4f020300560001006090c07c0a1b7000101a03568241e1870001006094f020301b7000101a039782410187000001a033c08830236000101a0304820313d71a8101a030483c28188000101b390482030057000101a09040605a057000101a030436430297000006a3404820301b6000d6000d0182030297000101a03048607a05700000080d048603e056000001a03048f810236
  | 7, 0, 11 => 0x3406a40482030057000106c0d0183c3029700000080d0182c10186000e8080d01824303d7000001a030482030ec6000101a301b8241018700000080d018481e1860003412080c0a40a23700000080d01824a63d600011940d018203029700000080d018181001600000080d3c08830056000101a79018247c087001981a03040605223700368080d018203029700000080d0182030006000101a099b8203005700000080d048f810056000112c0d4a95410187000101a390483c30057000101a6b0181810187000006a0d1a024301f60003406092a82030237000112a09040600a1b702035500345024101880003406093602030237000001a9304820302360000006900482030236000101a0304820312b700010061504820301b70000008360480830056000101a370483c30057
  | 7, 0, 12 => 0x101a031b82002297000101a0307860522370001070370602410187000101a0339020302970001070031b82030297000101a0304844303d7000341208110600a237000101a0304004521b70003406094f020307570003406080c0a446dd7000101aac0182030297000d41a34048215618700198080d04060520570000006260482030236000101a0304aac303d7000101a092a820300570003406090400802237000101a093602030057000007439018241e18600010065d04820301b700010060918820303c7000101a03a80241018700128080d01830120f7000101a030a824301f7000d41a0304c3c10187000101a090882030057000d81a09040600a237000101a080c0a40a8776d0100637048c410188000101a030483c7c147000101a098702030057000001a09040040a236
  | 7, 0, 13 => 0x101a030483c302d7000101a030482c1e187000101a09044c4300570001006098d020301b70000c6e091882030237000340609290203023700000080d2102414186000101a030482030c370000008260482030056000100634048603e1b70000c1231040603623700010060907924301b7000d41a034f020302970001006092a8603e1b70000c18090406036237000101afa0182030297000101a09040080205700000ca0d0482030056000d41a34049541018700010760d0482030057000006a0d04820308c6000101a03550c410187000101a0304954303d7000101a390182002297000d41a3901824301f7000001a03040605223600010703704820303c7000101a032602410187000101a030406052d87000101a03428241018700010072a04820301b7000101a8a0482030057
  | 7, 0, 14 => 0xcc0d018255c0160001012080c0f00a1b700000080d018241e3e6000106e091882030057000101a092902030057000101adb01824301f7000101231040600a1b70003406091782030237000001a340482030756000101809040600a1b70001006080c0a40a1b7000101a03048b830057000340609188603e23700000940d0182492186000340609040612823700010de03048200418700000080d0406052056000101a420183c30297000101a394a9541018700034129e040600a7370003406090502030237000101a094f02002057000001a6304aac30236000101a03060241e49700011620d01824303d70001132031882030057000101b040482030057000101a951b9541018700010060932020301b700000cc0d0182492186000101a952a820301b7000101a0304820312c7
  | 7, 0, 15 => 0x101a0917820300570001012080c014e61b700010060904061181b700012180d0182030297000101a09188603e057000101a030c07c52057000101a030482030197000101a036482030297000101a0304b1010187000008a0d018241e186000101a09040612805700011b80d01824301f70001006080c0b4521b7000340609420203023700320060918820302370000008030c07c521b6000101a035c02410187000006a0d1a02030296000101a0905020300570003406090454c30237000115e03048220e187002741a031ba7810187000101a0304d1410187000101a03048603e757000d40837048c41018700000080d018607a2960003406090302030237000101a0304820023c7000101a03048603e91700010700304820303c700011320318820302d7000d4080304060521b7
  | 7, 1, 0 => 0x101a035f024101870003406370482002237000101a0942020300570001190091882030057000106c0d0483c30057000101a0304aa810017000101a03048203041700128080d0183c30297000e80839018203029700011940d0482030057000001a030494c30236000101a03049001018700035580304820302370003406090788830237000101a099d02030057000e808031b82030297000101a090302030057000101a0304828303d7000000843018241e186000100609a6020301b7000101a0304d3c1018700198080d0183c30297002681a0304a7810187000101a0304820311e70200c6e094f0c410188000101a030406052d17000d4080d018603e29700000080d04a0031306000006a0d4582410186000101a03040613829700010060f04060521b7000101a0304d2810187
  | 7, 1, 1 => 0xd41a0304b4810187000101a030a8241e087000101a030482030de700010063404060521b7000101a031a0245c187000101a09400883005700010065504060521b7000101a09040040a1b700000080d0494c30056000101aac048203005700000080d0192c10186000101a090788830057000101a0304822aa187000d41a390182030297000d59e0d01824301f70001132031a0c410187000101a035682410017000101a031202410187000101a0306020302d7000101a03048222e187000001a030482104186000101a6804820300570003412080c07c0a237000101a370483c14187000120c0304820301b7000101a097c020300570003406df048203023700000ca0d018241e186000101a0304ba410187001d0080d01824301f7000000004018c45c185000101a090c07c0a737
  | 7, 1, 2 => 0x3406310406052237000101a030792430297000115e0304060521b7000340609078503023700268080d01824301f7000106c0d0182002297000101a03238241e18700010de0304820301b7000d4080d6f82410187000e8080304820303c7000101ad71b82410187000101a030482030f070001006371302410187000101a092a82810187000101a033482410187000100637048c41e187000101a03049481e187000367809040600a23700000084e018241e186000d41a094f020300570000c12080c0143623700011160304820301b70001006091883c301b7000101adf0482030057000347209040600a737000101b030182410187000101a390482002057000001a09040600a236000101a030482030217000101a030483d66187000101a0304d6010187000101a370482002057
  | 7, 1, 3 => 0x101a090785030057000101a037f02030297000101a030400452237000d41a03048603e23700011b80d01820302970000c120f0406036237000101a030492c1e187000101a6f01824301f7000101a0304c6c10187000101a030406052757000101a390182030297000101a03048bc1e18700010060918844101870003406090c07c0a237000101a0307024101870003406c90482030237000101a030406052917000111e0304820301b70000006090c07c36236000101a031b820302970001006094c020301b7000101a034f13c10187000101a950182030947000101a030483c309470000074390182410016000101a039202410187000101adb0182030297000001a03048607a236000101a030482030977000e872030482030297000101a031a0603e297000101a0304820303f7
  | 7, 1, 4 => 0x101a0304060528c7000d4080d048603e0570000c130e04060362370001070370495410187000101a09040613805700011fa031b8203029700010120f040600a1b7000d41a340482004187000101a0304820022d7000113203188bc1018700012180d0482030057000101a097882030057000101a0304808303d700010072f04820301b7000104a031302410187000101ac90482030057000101a094f020300570033c080d018247c0870000008090c07c0a1b600000900d018241e186000101a0304a101e187000006a0d380241018600000080d048607a05600034071d0482030237000101a030482030ba7020e40637048c4101880003406150482030237000101a03048181e1870000008360182422186000d40809040600a1b7000101a310406052057000d41a037002410187
  | 7, 1, 5 => 0x101a0304b2c10187000100637060c410187000101a030614810187000101a09078603e057000101a0304b181018700010700d01830120f7000001aa4048203005600010060c18820301b7000100609078607a1b700010061604820301b7000e01a0304060522370001006094f0603e1b702034063704a10101880000c68090406036237000d59e0d018203029700000083601824040160000c125504060362370001070374502410187000101a0304820303c7000101a6b018247c087000101a090c07daa057000101b1d0482030057000101a030482030c57000101aac018241e187000101a150482030057001d0080d018203029700010074904820301b7000106c6b0182404187000114e0d0482030057000101a080c0a40a737001f8080d018247c087000101280040600a1b7
  | 7, 1, 6 => 0x101a0304aa81018700010c60304060521b70000132031882030236000101a03048603e8e700268080d01820302970001006090a020301b70000008381b8203029600010700d0406052057000101a099c02030057000101a03048f8fa087000101a030b024301f7000106809040600a1b700010a80304820301b7000101a0304b9810187000101255040600a1b700010074d04820301b7000101a03048224418700010e00304820301b700400080304060521b7002bc060904060362370003406092a8603e237000114409040600a1b7000101a5d0482030057000101a03060241e3d7000d41a390482030057000101a030483d6c187000101b06018203029700010840304820301b70000000040189844185000d41a0304a781e187000101a09400603e05700000080d0182410416
  | 7, 1, 7 => 0x101a03060241e057000101a34048603e057000101a030483cbc187000101a5401824301f7000124c031b82410187000341231040600a237000101a090792430057000115e09040600a1b7000101a092a8603e057000101ac90495410187000341809040600a2370003406080c0a40a237000000803060241e1b6000101a0304821c4187000106c0d0482002057000101a8b01820302970000006080c0a436236000001a03048b8302361a8101a030485010188000100609040610e1b74d0100637048c410188000001a44018241e1860003406090408802237000101a0304ac8101870001006370493c10187000100609078600a1b7000101b2a048203005700198080d0182002297000d4cc0d01824301f7000101a03048f81023700034060932020302370003406370482030237
  | 7, 1, 8 => 0x8080c0a40a1b600000080d048b830056000001a039e02030dd6000101a8f018203029700011f20304060521b7000001a030c07c52236000101a03048603e877000101a034c02030297000101a090408802057000101a952ac3c10187000101a390482030057000101a030482030ef7000107037048bc1018700010060987820301b7000101a093202030057000d4080d01830120f7000128e0304820301b7000101a3704820300570000008991882030056678100637048c410188000101a0304d0810187000d41a030406052237000101a0304cc810187000006a0d1a0241e18600000ca0d0182410016000101adb0482030057000101a032d82410187000340609ab8203023700010600304820301b7000101a6f0182030297000101a03420c410187000101a375c82410187
  | 7, 1, 9 => 0x80d0c07c52056000101b2d01824101870003578033402410187000101a0904061a60570000008880482030876003581a0304a7810187000101a033102410187000101a030483c301d7000101a6b01824dc0870001012086c8600a1b7000100637048c410017000101a030494810017000e8080d01830120f7000001a0304c3831526000d41a341b8241018700010060918820021b7000e81a030406052237000d4080d0406052057000115803048c41018700000083804820303c6000101a031b824303d7002681a0304a60101870200c6e0918a60101880001006375d8241018700034060f0406052237000101a3001824301f7000101a03048607a1b7000d41a030482030d57000101a0393824101870001006bb04820301b7000101b0501820302970203406370483c28188
  | 7, 1, 10 => 0x10700d0183c30297000101a03048603edd7000101a096c8603e057000101a03060241e117000e8080d0406052057000101a03048bc100170001006340483c301b7000112a032a820301b7000101a8004060520570001006092a83c301b7000101a03048c4021f7000100609a5020301b700034070e0406052237000341208570600a237000101a03048200294700012380d0482030057000101a0304060522370003406097582030237000101a0f04060520570001070a81b824101870001006370483c22187000340690048203023700000080d318255601600010069e04060521b70001012080c015421b700010060907844301b700001240304820309160000222030482030236000101a035002410187000d41a374502410187002481a030406052237000340609ab02030237
  | 7, 1, 11 => 0x101a42018203029700034062604820302370003406091883c30237000115e030483c301b7000101a097582030057000d4cc0d0182030297002740809040600a1b7000101a0304a1010017000101a030982410187000101a0304060528e7000101a030482031417000101a031883c28187000101a0304820302d70003406088686052237000101a030482c10187000101a03078607a2970000009110482030056000101a031a030120f7000101a03048481e187000101a090c07c0aa17000101a030481810017000108c0d01830120f700034063404060522370018c0609040603623700010060924820301b700034065504060522370000070370482030236000101a095a03c30057000d41a0304c3810187000100609a4020301b7000101a030482030007000101a034f82410187
  | 7, 1, 12 => 0x101a0304cf810187000101a09040043e057000101a6f0482030057000101a03040605287700000080d238241e186000101a0304d4410187000101a030b0241e087000101a260482030057000101a091883c30057000101a0307860520570000012080c0143623600000080d268241e186000101a030302030057000d4080d1a02030297000101a032782030297000340609045503023700000080307860521b6000101aac01824100170001006c9048c41018700358080d01824301f7000101a340406052057000101a54018203029700010c609040600a1b7000101a550406052057000101a030482030f67000101a03049901e187000101a700182030297000ec1a030482030057000d41a034502410187000013a0d01820309c600034de030482030237000101a0304060528d7
  | 7, 1, 13 => 0x10720304060521b7000101ab001824303d7003f41a0304060522370033c0803048603e1b70000c129e0406036237000101a038782030297000101b2e0182410187000101a54018241e087000e01a03340241018700010063704060521b7000101af301820302970000008430182410186000001a090c07c0a236000101a030981810187000101a0304bd010187000101a094c0203005700010060907828301b7000101a090c07c0ad8700000080d4a8203094600012040d0182030297000101a300182030297000101a03048f81041700010703704a7810187000101a0304cfc101870000008034802410186000d41a0304a7810017000101a63048603e05700011da0d01820302970000cf0090406036237000101a030302030007000008a0d0182410186000d4080d0183c30297
  | 7, 1, 14 => 0x10129e040600a1b7000101a39018603e297000341208558600a23700034060c188203023700011ae0304820301b70003406160482030237002641a09040600a237000d41a340482030297000101a030406052dd7002481a09040600a237000101a086c86052057000101a03048226218700010d603048603e1b7000101a031b8603e297000101a030482030ce7000101a0304820305a7000101a37048281018700010060969020301b7000101a030482030b77000101ae7018241018700000080d01854120f6000100609040040a1b7000341280040600a23700010f009040600a1b7000e8080d0183c30297000101a032915410187000101a54018dc120f7000101a03060241e0a700034120f040600a237330100637048c41018800128080d018203029700420080d0182030297
  | 7, 1, 15 => 0x11100d0406052057000101a031a03c30297004001a03040605223700010c6030483c301b7000101a034302030297000d4080d01824021f7000108c0d0183c3029700011b603048c4101870003406680482030057000101a030315410187000d41a0304a10101870000008381b8241e186000354409040600a23700000080d01974120f6000101a03189901018700000066804820301b6000101a0304acc10187000101a0304bd410187000101a43018241e187000101a030441c3029700034130e040600a237000101a030489c10187000101a080c25052057000101a03048043e057000101a080c0a40aa17000101a030784430297000e872030602410187000101a0907ab830057000000803048043e1b600011fa0d0406052057000006a0d1a02410016000d41a340482286187
  | 7, 2, 0 => 0x80d04aac30d86000101a03048203094700000080d018301e14600358080d01820302970001006e004820301b7000101a097b82030057001141a030483c141870001006090c07c36237000107311018241018700034060927820302370001006261202410187000101a0304820314e7000000609078603623600034c6030406052237000101a032482030297000101b210482030057000101a0c1882030057000101a09078607a057000101a1604820300570003406090a020302370001222031b82410187000d41a033402410187000101a094f0603e057000d41a340482044187000101ad701824301f700010060904060781b700034a8030482030237000100637048c41018700012220304820301b7000341255040600a23700000084e0182410186000101a0304888303d7
  | 7, 2, 1 => 0x101b030182030297000001a080c0a40a2361a8101a03048f810188000101a030482030e5700035f203040605223700000740304820308d6000101a030309c1018700010700d018200229700010071604820301b7000d41a3704a7810187000101a0304822a61870000c6e09040603623700010060955020301b7000101a09278203005700010063404820021b7000000809078600a1b60001006092a820021b7003ec080d0182030297000101a630406052057000101a090a02030057000e81a0334024101870001006260482030217000101a540482030057000101a030492c10187000101a03048603e3c71a8340634048c41018800400080d0406052057000101a038a82410187000101a03048bc10187000001a03060241e23600010060904060e61b7000101a09040600a8d7
  | 7, 2, 2 => 0x101af90406052057000101a030482030ea7000001a030482030676000101a030782830297000101a098782030057000101a0304a0044187000106e09040600a1b7000101af304820300570003406090c07c469170001006094f03c301b700034060907aac3023700012960304820301b7000340637048603e237000101a0304aa8301f7003681a03450241018700011320318a6010187000101a0304820311970003406091882002237000115e0304820021b7000101a0304954021f70000008301b82410186000101a0304850303d7000101a030406128a17000101a0304be0101870033c080304060521b7000101a030483ca0187000101b460182410187000101aee018241018700000080d060241e05600011da0d04820300570003406bb0482030237000101b260482030057
  | 7, 2, 3 => 0x101a6b018603e297000101a39048603e057000d4080d0182002297000101a03048203118700011c80304820301b7000d41a0304820309c7000101a0907aac30057000101a37048603e057000101a03049a810187000101a091882002057002201a09040600a237000101a0304004520570003406092a83c302370003406080c27052237000101ad00182030297000d41a0304a7810187000101afa0182410187000101a038a0241018700000080304004521b6000101a0394824101870001150031b8c410187000101a032a83c28187000101abb0482030057000100609040607a1b70033c080d018603e29700034069e04060522370003406090784430237000101a0907a003005700010d60304060521b7000101aa40482030057000107209040600a1b7000101a030499010017
  | 7, 2, 4 => 0x101a030482030607000101a0304820305c7000101a03049b41018700304080d01824301f7000101a039002410187000101a092482030057000e8080d0182002297000101a090c07da6057000101a030493c1e187000101a630183c302970003406090455430237000001a440182410186000101a092a83c30057000108c0d0483c300570001006080c0a436237000100609040600a1b7001d00809040600a1b700010de03048c4101870000008952a820301b60000000040181804185000101ad401824301f700000080d018043e296000d41a03048603ed57000101a090441c3005700000080d3182414186000101a9e0406052057000101aa8018bc101870001006b904820301b7000101ad70182030297000101a090784430057000d4080d1b824301f700000080d0182c1e186
  | 7, 2, 5 => 0x12140d018203029700010063704820302d7000101a0304bc410187000d4063404820301b7000101a030c07c52237000101a03048603e057001d0080d048603e057000101a030482031447000100609040605a1b7000001a030786052236000340609ac02030237000001a030302030236000006a0d1a02410186000101a3004954101870003406096682030237002f41a033402410187000d41a032e82410187000001a0304ab830f26000101a033082410187000101a0304060523c7
  | 8, 0, 0 => 0x10700d01820302970203406092a82030058000101a09040600b30700010063404820301b70001006092a820301b70203406a20482030058000101a032e824101871a8101a030482156188330101a031b82410188000d41a39018241018702034d66f0182410188020340609042ac30058000101a030483c301f7022641a03048203005800128080d018241e187000e808390182410187020340609188bc101881a8101a030483c10188000101a03048603ed57000101a950482030057000101a038e82410187000e808031b824101870203406094002030058000101a030a8241018700198080d018241e1870203406090782030058000101a030482030d17000d4080d01824301f702034a8031b82410188000101a0304820309c7020e01a03049541018800010060907820301b7
  | 8, 0, 1 => 0x101a030406052057000101a03048200223700011b80d018241018700000080304060521b600000080d018245c1860203406090406052238000101a030482044017000101a030482030757000101a3901824101871d0101a030495410188000101a030482030917000101a030499010187000101a031b82410187000000899018c4101860203406092a83c1018802034d603048204418800578080d0182410187000101adb0182410187000101a031a024301f70003406091882030237000101a030483c92187000115e0304820301b7000101a0304954301f7020340609078441018800034060c0482030237000106c0d018241001700274080d01a781018702034c603048c410188020d81a6b01824101881a8101a030495410188678101a030482044188000101a039502410187
  | 8, 0, 2 => 0x101a09042b830057000101a0304bac10187000101b06018241018700274080304820301b702034060907828101880000009110182410186000e01a030482030237022201a0304820300580203472950182410188000d59e0d0182410187000e8080d018203029700194080d0182410187020352a031b82410188000101b5d0182410187000340609042b83023700012380d01824101870203406094f0c410188000101a030782030297001d0080d0182410187020352a0304820301b8000101a09040600a7370203406340495410188000101a0304820308c7020340609040883023800000080d018603e296000101a030482030d3702035ae0304a7810188000d4080d01820302970203406340482156188022641a031a02410188000101a091882030057000101a0c0482030057
  | 8, 0, 3 => 0x10067804820301b7020347203048c41018802034063704820303c802034720306024101880003406090782030237020340637048c4101880203406370602410188000000809040600a1b602034060c04820301b8000101a8f0182410187000001a03048603e236000101a0304a60101870203406092a8bc101880203406092a82030948020e01a0304a7810188000d41a030482030237000101a6301824301f7000101a0304820021f7000101a6f0182410187000340609040600a237000101a8b0182410187000101a031302410187000101a03048c41e187000000609040603623602034d60304820301f800198080d0182410017000101a031a0203029700010c60304820301b7000101a032a8203029700268080d01824101870000008381b8241018600010700d0482030057
  | 8, 0, 4 => 0x101a03060c4101870003406090443430237000101a030483c303d7000101a030b0241018700011320d0482030057000101a0304a78301f700570080d018241018700034063404820302370003406092a82030237000101b5f018241018700010700d018241e1871a8101a0304a7810188000e8080d0482030057000101a09400203005702034c60304954101880003406098702030237000101a030482030237000101a0907820300570203406094f02030058000101a030483d5c18700011fa0d01820302970001006094f020301b7000340609042ac30237002641a030482030237002481a03048203023700000080d048603e0561a8101a0304820041881a8101a033c0241018802034060904008300580203406780482030058000e81a030482030237000d4080d0482030057
  | 8, 0, 5 => 0x678101a03048c41018800012040d01824101870203406094f15410188000101a30018241018700000080d01830120f600011da0d0182410187000d4080d018241e187000101b260182410187000001a030406052236000101a0304820308774d0101a03048c4101880203406340482004188000101a030483c30057000d4080d1a02410187000101a030493c101870000008030483c301b6000101a630182030297000101a030485010187000101a340482030057000101a540182410187000101a092a82030057000101a70018241018700400080d0182030297000101aa204820300571d0101a0304a7810188000101a0304820308d7000101a420182410187000101a0304bdc10187000d4cc0d0182410187000101a0304820308e7000101a09042ac30057000101a039082410187
  | 8, 0, 6 => 0x108c0d018241e187002741a030482030237000101a03048220e187000101a034f02030297000101a09040600aa17000101a030483c221870203406370483c10188000101a3901824301f7000101a030482030dd7000101a090436430057000101a030483d56187000101a031b824301f7000101a03048c4100171a8101a031b8241018802034d603048c41018802034060918a6010188000101a035d82410187000e8080d018241e187022581a030495410188020347203048203005800000080d040605205600128080d018241018700420080d018241018700010720304820301b70203406150495410188000101af901820302970203406370482030058000101a0304c3c1018700010063704820301b7000101af30182410187020340609040600a1b800198080d0182410187
  | 8, 0, 7 => 0x33c080304820301b7000001a09040600a23600000080d0183c3029600000080d018181018600010700d0182410017000101a0304b34101870203406374502410188020e01a030482030298000101a6304820300570203472030495410188000101a03048215c0170203406341b82410188020340637049541018802034063404820301b8020340721048c4101880203406092a820301b8025801a0304a7810188020340616048c41018802034d603048215c18800274080d048203005700358080d018241018700034c6030482030237000101a030492410187000101a03048603ed37020340609188203023802034060c048203023800011100d0482030057000101a031a0241e187000101a950195410187023201a030482030058000101a03049541e18702034c6ac0182410188
  | 8, 0, 8 => 0x20340637048bc1018800000080d01824021f6000101a094f0203005700000080d0182620186000101ad70182410187000101a6b01824301f7000d4080d01824100171a8101a0304822861881a8101a030482030298000101a0304b4810187020d81a030482030058000101a030482002057000101a090400830057000101a780482030057000101ad0018241018700000080304820021b60203406090406052058000101a39018203029700010060904060521b7330101a03048c4101880033c080d01824301f70003406094f0203023700010d60304820301b7000101a031b82030297020346003048c410188023201a031a02410188000101a0304060521b7023201a030495410188000101a030483c141870203608031b8241018800034060904008302370003406780482030237
  | 8, 0, 9 => 0x203406340482030298000101a03048f81018702034c603049901018802034c6031b8241018802034d603049541018802034d603049b0101880203550031b82410188000101a030482030737000101a63018255618700012160d0182410187000101a030482156017000101a037002410187000101a03048603e2374e8101a031b82410188000001a030483c3023602034d6030482156188678101a03049541018800010073b04820301b7000101a0304820303c7000101b110182410187000e8080d018241001700000cc0d018255c186000101a63018241e187000101a03048c4101871d0101a0304820302986d0101a031b824101881a8101a03048204418800011900d0182030297000001a03340241018600010060904060362370203406090408830058678101a030482156188
  | 8, 0, 10 => 0x20340609040603e058000106c0d018203029700000080d0182002296003201a030482030237000101a0304820303d70203406373c0241018800420080304820301b7000d4080d1b82410187000101a6b0182030297000101a3904820300570203406090785010188000101a370482030057000101a0304a781e1870203406092a8203023800198080304820301b7000101a09040600a1b702034063404820441880033c080d0182030297000101a035682410187000101a030483c04187020340609042ac30238000101a03848241018700034720304820302370003406090406046917000101a038b024101870003406370482030237000101a0304aa810187020d81a030495410188000101a031a0241001700000080d0483c30056000101a0304954100170003406090406036237
  | 8, 0, 11 => 0x112a0304820301b7000101a030482030c070000008360182404186000101a031b8241e1870203406092ac3c10188000101a030483c301b7000101a0304a00101870033c1a030482030237330101a030495410188000013a0d01a7810186023201a0304a7810188000d41a031a02410187000101a0304820302d700000080d01824301f6000101a030482030d57000101a03049b810187000d4080d0182410187000101a030406052237000101a030482030057001d0080d048203005700000080d4a9541018600011900d048203005700000080304820301b60001006090441c301b7000101a035c8241018700304080d01824101871a8101a0304820301f8000007439018241018602034063704a7810188000101ae401824101870203406094f020301b800198080d01824301f7
  | 8, 0, 12 => 0x6b0101a03049541018800000ca0d0182410186000101aaf0182410187000106c0d048203005702034d6030482004188000d4080d358241018700000080d0482002056000101a034502410187020e01a030602410188000101a030482030f27000101a0904060520570003406090408830237000101a03048221a187000101a6b048203005700198080d01820302970203472031b82410188000101a031a02410187000101a030495410187000101a03049b010187678101a030482004188000101a030484410187000d81a030482030237000101a0304c3810187000001a0304820022360033c080d04820300570003406090406052237000351e03048203023700000080d019e04418600034d6030482030237000101a63018241001700000080d018247c086000101a39018241e187
  | 8, 0, 13 => 0x368080d01824101870203406091883c10188000101a03048bc1018702034060918820302d8000101a03048c4301f7000101a030482030947000101a030482030a17000101a033b02410187000101a03048281018700000080d318255618600034060904060475271a8101a03048c4101881a8101a030602410188000101a0304821b2187330101a0304a1010188000100637048c410187000101a030494810187020340609188203005802034060c048203005800010060918820301b7020340609040083023800010060c04820301b700000080d0182030296000101a09040600a237000101a0304a78100170038c080d018241018700034060904060468e7000101b040182410187000101a09040883005702034d60304a78101880000008031302410186000101a030482004017
  | 8, 0, 14 => 0x101a0339024101870001070031b8241018702034d60304822b418802034726b01824101881a8101a03048215c188000101a0304820021b700000080d01824a618602034063704820302980003406090406046dd7000101a630182410187000101aac0182410187000101a030483c4418702034060904060521b802034d6031b8241018800198080d048203005700198080d018255c187020340609042b83005802034d60304820301b800400080d0182410187000101a033402410187000340609040603e2371a8101a0304aa810188000101b5b0182410187000101a09040600a877000101a0304a1010187000119003048c410187000106c0d018241e187678101a031b8241018800011940d01824101871d0101a030602410188000101a030481810187001981a030482030237
  | 8, 0, 15 => 0x12180d0182410187000101a03048603e057000101a036482410187000101a0304a7810187000000803048603e1b6000006a0d1a02410186000101a039402410187000352a03048203023700000080d01824303d6000d4080304820301b7000101a031882030297000101a030483c281870203407160495410188000100609040600a1b700000080d0482030056000101a42018241e187000101af90182410187020340637048203023800034073c0482030237000101b130182410187000d41a0304a7810187000101a09040603e057000101a036f82410187000101a390182410017000001a030482030236020340634048c41018802034063406024101880203406091895410188000101a030482030d870203472030482030298000101a031b82410017000101a030483c30237
  | 9, 0, 0 => 0x4e8101a030482030e000203406080c0a58080d018d012080c38101a030495410187020340609042ac30e044c834060904061c74040680c12080c38101a030483c10187000101a03048603ec3502034060904061c080d01824101802b800080304820301b6020e01a030482030e040680c120857061c080d0182462080c38101a030602410187020352a030482030e00020340609040618080d0182410180fb998080d01824101870203406090406046e040680c120811061c08360680c12080c3800080d01824100160203406090406052e04069ac060904061d9e040680c12080c3811900d01824101870203472030482030e040680c6e0904061c080d0182410180db800080d018241e186
  | 9, 0, 1 => 0x80d018253c080c38101a0304820041870203406780482030e000203412080c0158000d01824101811b0101a630182410187
  | 10, 0, 0 => 0x80d0182410186
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 49
  | 6 => 67
  | 7 => 76
  | 8 => 76
  | 9 => 67
  | 10 => 58
  | _ => 0
def stateM : Nat → Nat
  | 5 => 0x1ffffffffffff
  | 6 => 0x7ffffffffffffffff
  | 7 => 0xfffffffffffffffffff
  | 8 => 0xfffffffffffffffffff
  | 9 => 0x7ffffffffffffffff
  | 10 => 0x3ffffffffffffff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0x3871807f9dfff00003803873e1fff00ffc003fff80000001c38639f3e1fff0000380380061ff0000007000001c000001c386398061ff00003871807c1df8c001fff801fffe000001c000398001f80001fc07c1ff81fff00fffffc0000000000e03f83e007e0000003800007c0000000fffffff8c7e38000e3fffc67ffe07f
  | 1 => 0xfc78e7f83e207300e3fffc67ffe00f00fc7ffff807ffff00fc471bf801dfff00003ffc0007ffff00ffc7fc7ff9e00f00fff8fffffe3fff0000000007381c7f00e3b89be7fe3fff001c00039f381c7f00003803873e1c7f0000000000001ff0001c00039f381fff001c000398001ff00003800007f80000001c386000000000
  | 2 => 0x3800000000003800007c01f8000e3fffc67ffffff00fc07e07801fff000003ffffff80000001fc07fe007e00000e3c79c67f9e00f00fc3f83f807ff800000000380000000001f80039fc0000000ffbf83ffc7e000000000038000000000000003ffffffff0000000000001f8000e07ffc603fffff00e03f801ff81fff
  | 3 => 0xffffffffffe00f0000000007381fff00fc78e7f8062000001ffffc1fffffff00ffc07c0000000000fffffffff8000000ffc0000000000000ffff83ffffe00000e00003e000000000ffc71bfff9df8c00ffffffe007e00000e03f800000000000e3c79f98061ff000e3f86067fe1ff0001c00039800000000fc3f83f807e000
  | 4 => 0x1c38039806000000ffc00007f8000000e03f800001c000001c386007381fff001c386000001ff000fffffc07f9dfff000387180000000000ffc7180000000000e00703e001c00000ffc71bfff9dfff00fffffc0001c00000e3bf980000000000e38003e7f8000000e3bf9be7ffffff00fffffff8c7e0000000000000000000
  | 5 => 0x1c38039f3e1c7f0003870007f9c000001c386007381c7f00e3fffc60c7e3800000000387381c7f00ffc7fc78c1e38000e3c79fffffe00f001ff8fc1ffe3fff001c7ffc1807ffff00e00003e0001ff0000038038006000000e00003e7381c7f00fc78e7ff3e3c7f001c386398000000001c386380060000000387180001c000
  | 6 => 0xe00003e73800000003800007f81c7f00000000000000000000380380061c7000e03f83e73ffc7f0000000000000000001c38039f3e0000001c38600000000000e3c79fffffffff00fffffc07c1df8c00fffffc0001c0000000380380061f8000e3bf9be7c7ff8c001c38639f381c7f001c3863873e1c7f001ffffc18c7e380
  | 7 => 0xe03f83e007e00000fffffc07381fff000000000000000000fffffc0000000000e03f800000000000e00003e738000000e03f83e73fffff001fbf7b9fc7dffc00ffffff9fc0000000e03f800001c000000000001ff81fff00fffffc1ff81fff001fc07c0000000000e03f800000000000e03ffc0000000000e03f8000000000
  | 8 => 0xe03f83ffffffff00000003e007e00000003fffffffffff001fc07fffffffff00e03f8007381c7f00e000000000000000ffc07ffff8000000ffc07ffff81fff001fc0001ff8000000e03f806001e00000e0000000000000001c386000001f800003871bf83e207300000703ffffffff001c47641839c073001fc77c1ff9dfff
  | 9 => 0x3f000001c000001c38600000000000ffffff98061ff000e3c79fffffffff001fc07c0000000000ffffff9800000000fff863fffe1ff0001c0000000000000003fffc07ffffff00fff803fffe000000fc3fe3f807fff000ffc7fc7ff9ffff00e00003e007e00000ffc003ffffffff00000003fff8000000e00003fff80000
  | 10 => 0xe03fffe007ffff000387180000000000e00703e001c00000e38003e7c00000000007000001c000001c386380060000001ffffc1ff81fff00fc3863f8061ff000ffc07c1ff81fff001ffffc0007ffff00003f83ffffffff001ff87c0000000000e00783ffffffff001ff87f9ffe1fff001c006018001ff0001ff87c1ff81fff
  | 11 => 0x39f3e1fff001c38639f38000000fff863fff8000000fc3fe3e007e000001c00039f38000000e3fffc60c7ffff0000380380060000000000038000000000ffc7fc7ff9ffff0003871807f800000003bffc07ffffff001fc77c1ff9dfff0000000000000000000000000000000000fff8e7fffe200000fc7fe7f807e000
  | 12 => 0xfffffc07381c7f001ffffc1fffffff001c000398001c7000e3fffc67ffe38f000000038000000000ffc0000000000000e00003e000000000ffc003fff81c7f00e03fffe73fffff001c386380061c70001ffffc18c7ffff000000038000000000ffc7fc7ff9e38f00e00703e739dc0c00ffffffe73ffc7f001fc07c18c00380
  | 13 => 0x3f038007c00000ffc0fc7ff83fff0000000398061ff000ffff83e007e00000ffc003e000000000ffffffe0000000001fc07c1ff81fff001c40641838007300fc3fe3e007e00000ffffff8006000000fc78e40000000000fc7fe7e007e00000e03883e0062000001c386000001c7000000003f8c7e38000ffc00007380000
  | 14 => 0x1ff8fc1ffe3fff00e00703e739dc7f00ffc7180000000000000003fffe3fff000007000739dc7f00fff8fff8c62380001c386380061f80001c7ffc183fffff00e38003e7f81c7f000000038000000000ffc7fc7ff9e07f00e3bf980000000000ffffffe7c7ff8c001fc07c1ff81fff001fbf7b8007c000001fbf7800000000
  | 15 => 0xffc79c0000000000e00783e001e00000ffc79ffff9e00f00e3ff9c0000000000ffffffe7ffe00f00e3c003e7f8000000e3ff9fe7ffe00f001fc77c1ff81fff0003871807381c7f00e3c79fffffe07f001c000000000000000038000000000000ffc00007c0000000000003f83e2073001fc07c1ff81fff00fc7ffff807e380
  | 16 => 0x3800000000000003871bffffffff00000003ffffffff00ffc71807c1df8c00ffc00007381c7f00ffc79c67f9e00f00e03f83e000000000fffffc0007ffff00003ffc073fffff00e3bf9807c1df8c00e3ff9c67f9e00f00e3871be7c1df8c00e3c79fe7f9e00f00ffff800000000000ffc00067f8000000fffffc67f9e00f
  | 17 => 0x380000000001fc7fc1ff9ffff00e03803e006000000fff86000000000000038038000000000003fff8007ffff00fffffc7fffffff00ffc0007ff8000000ffc7fc7ff9ffff0003bf1b87c7df8c0003800387c00000000000038738000000fc3fe00000000000fc00000000000000fc0003f8000000000007000001df80
  | 18 => 0x1c3ffc0007ffff00fc3863e000000000fc0003e000000000e3c003fff8000000e00783e007e000001fbf7807c1df8c001f800007c0000000e03f838006000000e000038000000000ffc00398000000001c000380000000001fc07f9ff81fff00e03f806007e00000e3fffc67ffffff001f871b9fc1df8c000007038001c000
  | 19 => 0x380001f800000000380001c7000e3c7fc67f9ffff001c3863ffffffff001c3fff9807ffff001fc77c07c1df8c00ffc0001ff80000001c386018001ff0001fc7181ff9df8c001c006398001ff0001f87781fc1dffc001fc0039ff80000001fc77c00000000001fc0001ff80000001c006018001ff00003801807c01f8c
  | 20 => 0x1c000000001f8000e3c79c67ffffff00e03f800007e000001c386000061ff000e03ffc000000000000386380061ff0001c3ffc0000000000003f838007e00000e03ffc0007ffff00e3800007c000000000380000001f8000e3c79c7ff9ffff000387180001c000001c386380000000001c386018061ff0001ffffc1fffffff
  | 21 => 0xe3bf9be007e00000fffffc07c0000000e3bf83e7c7e00000fffffc00001f8000e03f83e007ff80000007000701dc0c001c000398061ff00000380398061ff0001c0003fff8000000003803e007e00000038003fff8000000000703e007e0000000000398061ff00000000007c1df8c001c38038006000000e007000001c000
  | 22 => 0xfff863fff80000
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x6fdffdffffffff00bdfbffbf7effff00ffe403fff9092000bdfbffbf7effff009d3a73994e9ff000621f81e297e495009d3a73994e9ff0004b975957c5df8c000ddb801d6eedb5009d3253994c9fa0000dc07c1d681b6a00fffffe0420124a00f23f83e297e495004b840157c1090000db365350c583800062cdac66b3605f
  | 1 => 0xb468a6a83a20730062c58c66b1600f00903bfe0006f6df00903bfe0006f6df00001bfc0006f6df0062c58c66b1600f009de07e1d681b6a0024c9acaf3a7c7f009de07e1d681b6a00bde9afbf7a7d7f00b4fbafaf3efcff000d1a71994e9ff000bdfbffbf7effff009d3a73994e9ff0006fc401fff9092000bdfbffa636f6df
  | 2 => 0x90200380000000004b965157c59f800062dffc66b7f6df006f05f07bd97b6500001bfdfbd91b6a000dc07de6b7f6df0062c58c66b1600f00ff3fd3fbdfffb5009032038004848000dfa403dfc9092000ffbf83ffdfedb500d22403c281000000000001fbdfedb50009125111449f8000205bfc2036f6df00f23f8219480920
  | 3 => 0xf2e58e66b1600f002ddbfdbf7effff0090200200000000000ddbfc1d6effff00ffe47e0420124a00fffffffff91b6a00ffe4020420000000ffff83ffffedb500f22403e291000000fff75bfffddfac00ffffffe6b7f6df00f23f82000000000062c58d9d6e8dba0062de7066b796d0009d20039948092000ff3f83fbdfedb5
  | 4 => 0x9d3a03994e8db000ffe403fff9092000f23f83e297e49500bdfbffbf7effff009d3a73994e9ff000ffffffffffffff006fdffc0420124a00fffffe0420124a00f23f83e297e49500ffffffffffffff00ffffffe6b7f6df00fffffe0420124a00ffe403fff9092000ffffffffffffff00d2240240810000000d000199480920
  | 5 => 0xbdfbafbf7efdff006fdf81ffffedb500bdfbfeaf3a7e7f004216504085828000b4e9afaf3a7c7f004b045050c103000062c58c66b1600f000dc07c1d681b6a00001bfc0006f6df00ff3e73fbdf9ff000903a038006849000f6edafefbb7c7f00b4e9aeaf3a7c7f009d3a7399481b6000bdfbffa636f6df006fdffde6b7f6df
  | 6 => 0xf6e403efb90820006fcdadfffb7d7f00620d81e293641500943a23890e9cf000f6ffafefbffcff00201b81a216e49500bdfb83bf7eedb500bdfbfe0420124a00420401fbdfedb500ffffff57e5dfce00ffffff46a5d6ce00993a5391469f9000fbbfdbf7d7ff9d00bdfbffbf7a7f7f00bdfbffaf3efeff0009125010448380
  | 7 => 0xffffffe6b7f6df00ffffffbf7effff002ddbfc0420124a00ffffffa636f6df00fffffe0420124a00ffe403fff9092000ffffffffffffff00dfbf7bdfcfdffc00ffffffdfe91b6a00f23f834285c484000000001948092000fffffe1d681b6a000dc07c0420124a00f23f82a212641500f6fffe0420124a00f6ffae0420104a
  | 8 => 0xf23f83fbdfedb500000001e297e49500001bfdfbdfffff000dc07dffffffff00f6ffaeaf3a7c7f00f224020000000000ffe47ffff91b6a00ffe47ffff91b6a000dc0001d68092000f23f826291600500f2240342810000009d3a7311449fc0004b9758ac1a323900421701fbdfedb5004657254aadc4e6004fd77d5feddfee
  | 9 => 0xd23f034285c484009d3a720000124000ffffff9d6e9ffa0062c58dffffedbf009de07e0420124a00ffffff9d681b6a00fffe73ffff9ff0009d2002000000000000dbfc0426f6df00fffe03ffff8db000ff3ff3fbdffff5006fc5fc7ff97b6f00f22403e297e49500ffe403ffffedb500000001fbd9092000f22403fbd90920
  | 10 => 0xf23fffe297f6df004b97580400120800f23703e295c48400fba403f7d10900004217014285c484009d3a73800696d0000ddbfc1d681b6a00ff3e73fbdf9ff000ffe47e1d681b6a000ddbfc0426f6df00001b81fbdfedb5009dfa7e0420124a00620581fbdfedb5009dfa7f9d6e9ffa000d007019481b60009dfa7e1d681b6a
  | 11 => 0x1bb5eedb500bdfbffbf781b6a00fffffffff91b6a00ffffffe6b7f6df00bde003bf78092000421ffc4087f6df00b03b83a216e49500b02003a2100000004fc47c5de91b6a006fdffdfff91b6a006fdffdffffffff006fdffdffffffff00620401e291000000001a018006849000ffe403fff9092000f23f83e297e495
  | 12 => 0xfffffeaf3a7e7f000dd27c1d6c9bea009d2823994a1d700062d7dc66b5e28f009028038002041000ffedae0420104a00f22d83e293641500ffedaffffb7d7f00f6ffffefbffeff009d3a73890e9ef000091bfc1046f7df0094200389080820006bc5dc76f1630f00f6f70befbddcac00ffffffefbffeff0009005010400300
  | 13 => 0xd23f03c287c494002dc0fc3d783b6b00000001994e8db000ffff83e6b7e49500ffe403e6b1000000ffffffe6b1124a002dc9fcbf7a7f7f000440240828006200ff3ff3e297f6d500ffffff842696da00b468a60020004200f67fa7e2b7e4d700b02882a0122011009d3a72890a1e700000000150c5818000ffe402af380820
  | 14 => 0xdc8fc1d6a3b7b00f6ffafefbffcff00fff75a0420120800000000b95a29310066dfadefbffcff0099205210400300009d3a7391469fd000045bfc082ef6ff00ffedaffffb7d7f00992003914009000066c5ac6eb9606f00fbbfda0400120800fffffff7f7ffdf000dd27d1d6c9fea00dfbf7bc687d6dc00dfbf7a04001248
  | 15 => 0xffe58e0420000a00f22583e291600500ffe58ffff9692f00f2ff8e0420000a00ffffffe6b7f6df00f2e403e6b1000000f2ff8fe6b7e49f004fd77c1d681b6a006fdffcaf3a7e7f0062c58ceebb603f009d20031140090000903a030004848000ffe40357e1090000000000a81a2031004fc47d5fe91b6a0090325200048280
  | 16 => 0x903a0200000000004b9759ffdfffbd0024c9adfffffdff00fff75b57e5df8c00ffedaeaf3a7c7f00ffe58e66b1600f00f23f83e291000000fffffe0426f6df0024dbfcaf3efeff00fbbfdb57c5df8c00f2ff8e66b1600f00fbb75bf7d5df8c00f2e58fe6b1600f00ffff820420000000ffe40266b1000000fffffe66b1724f
  | 17 => 0xb02983a2126415000dc1fc1d687b6f00f23e03e297849000fffe720420124000903a038000000000903bff8006f6df006fdffc7fffffff006fc4007ff90920006fcdfcfffb7f7f00dbbf5bd7c7df9c00dba403d7c1090000b4e003af38082000ff3ff20000124000ff24020000000000ff2403fbd90920004b175153c5df84
  | 18 => 0x9d3bfe0006f6df00ff3e73e291124000ff2403e29100000062c401fff9092000620581e297e49500dfbf7b57c5dfcc00dfa40357c1090000f23f838006849000f224038000000000ffe4039d680920009d200380000000009de07f9d681b6a00621f806297e4950066dffcefbffeff00dfb75bdfcddfac00d23703c285c484
  | 19 => 0x99325391449f8000942823890a1c700062c5fc66b1724f009d3a73fbdffff5009d3bff994effff004fd77d57e5dfce00ffe4021d680920009d3a7219481b60004fd7595feddfac009d207399481b60004f97795fcddfec009de0039d680920004fd77c0420124a004fc4015fe90920000d1271194c9fe00009805815401b08
  | 20 => 0x9d325311449f800062c58c66b7e49f00f23f820006e495009d3a72000696d000f23ffe0000124a00903a73800696d0009d3bfe0000124a00903b838006e49500f23ffe0006f6df00fba40357c1090000993a5311449f800062c58c7ff9692f004b97594685d68c009d3a7380001240000d1a70194e9ff0002ddbfcbf7effff
  | 21 => 0xfbbfdbe697f69d00ffffff57e11b4a00fbbf83f7d7ed9500ffffff15649fca00fb3fd3f3d7ff95004297094785dc8c009d2003994e8db000903a03994e8db0009d2003fbd9092000903a03e297e495004b8401ffd9092000421701e297e49500091251994e9fb00000000153c5cd84009d3a038006849000f237034285c484
  | 22 => 0xfffe73fff91b60
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 353 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem wd_0 : ∀ i, 0 ≤ i → i < 128 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem wd_128 : ∀ i, 128 ≤ i → i < 256 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem wd_256 : ∀ i, 256 ≤ i → i < 353 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 97 256 = true)
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 353 → wireDOK i = true := (range_split wd_0 (range_split wd_128 wd_256))
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 353 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 353 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => [] | n + 1, ids => wireDAt (ids &&& 0x1ff) :: stateWiresD n (ids >>> 9)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => [] | n + 1, ids => wireSAt (ids &&& 0x1ff) :: stateWiresS n (ids >>> 9)
def SD (s j : Nat) : List (Nat × Nat × Nat) := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) : stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with | zero => rfl | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) : SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := stateWiresD_eq _ _
def htAt (s i : Nat) : Nat := (HT s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def idxH (s h : Nat) : Nat := bsr (htAt s) h 12 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 5 => 57
  | 6 => 797
  | 7 => 2001
  | 8 => 211
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xf7afa212f7429dedf5b8581af489420ef2786db3f213ac51f11c1b10f02dda6cefac1d7ee82a55d8e2a1e3dae24e2729d9e6cfead7a50427d36a5d03cb66d86fcb090b09c5ddca82c5bc426db246db3eb03e0b23ac4d8db4a83bdc37a44a0920a22682d79667f788963180638c72f4328b58f2b48aaf25e886362ca3809847747e32a80f7e271897787825f97222b2797074a1656e95754b5a17fe3856e8940956952a155211343a509cdaf64ee50f754cd75e004c6f7bdf41ae0c663ec495b43976135231068f0a2ed9adaa28d7f3c022a80c4a18adaa7f11b74f1907ccebc303040eef
  | 6, 0, 0 => 0x12dca5be12d7e57c128b8a621242351f122f03d911fb2f401182c6e9114fe7591125c5fe110c69a71105b1e810b502fa108dfb000fdf4c510fb28dd10ebbdfe60e67e9730e255c0c0d5b5e4d0cf9cfce0b8d4bbc0b2cf61b0b21ca180a33c9650a2b7f4509fa4f0909f7aaac09a9f761097f42550978a57f093bd31f0932c3e70922416a08fdd93c08d7f62e07ddea3307d0354107361c0d0656511b061f667d0619093905fcea2e05c54fb805a60b080517acfc0446c582043308cc03ac249f035741ed0349bb5e02ed76e002cb356c023f8c570168078101384e8b0113ab2a0103f75400ea126400c9a4d300c2068600bf18a7008bbbc1003a36ad0010041b
  | 6, 0, 1 => 0x2723df5e26fc116726f3d28a26e26c0a25496642248274aa2402d8e5238ec98922e6910322ced8f722085e9121fb8a6f21f40ce021a84b1b213777171ff147e71fe205301fd528dc1fd230b01fc7929c1faa53541f38450d1e06cafd1db7f4151d7550671d4a39ee1cc31b6b1c85d82a1b5c2a5f1b30ad5a1af080381ae554351acafc521aace10f1a97ec0a1a04d9fd19f7a8a219a4c6871996d3a0197e5ef6196e8ca21930499a1909367c18d39c1818917f9417e2d0e517ceac1c179411ab178b6ae21783d36c17802805177c24c617681a9116d6d093163ee1681603466915bcdc7c15abcf0f14e4974614b3ba6d149a449b144cdc7013f2ead71309282e
  | 6, 0, 2 => 0x3f2057543eb82dbe3e3d405f3df477883dd11a073d6e69073cc117773cafee803c4250e83c04bede3bcc4b8e3b8ad5223b7296e23a5309ac3a1fe20939fb5db8396aa3ac395f96ae392e993f3899aedb37f2c0653747122336b5e23d362e6e193601afa23582312935389f9734d213a734bd92e334ab5128332d016332c13f4c32ad2e82324f85183247ed1d32124cbd31d548db31cae27131c88ed730b17a1b30ac2036307cd31a303718c23006aaf52fdf351d2f2763f22ed593102e9f17e82e852e2f2e35d1b02e2ae9852d7eac952ca7cc942c05dd8b2ad82ba32ab3b97028794e8628784ddb2803266127dbb08927d950e127b370af27add7e827ab8edf
  | 6, 0, 3 => 0x4f5a6fd74f218dc24ecd1a174e8dfc524e838fd64e46b70e4e24e1914df7eb2c4dddf93a4dc98a5c4d3d4c124c67bf654c6374c14c50d89e4bef001a4ba07d3a4b5c0cb54b0b17e04ac5524f49875221497e0663495eaa9f48f9730648e58c7a48d7a10748a662ee4812d5174809adf94802432546d2262846b74d584640cf7e45f7fc1c45eb319d45e54eb3453290c6451a7cea44ea515244643ad1444d540a444a21f9443e78e943cfd02243aebfc6439cf8a6438645da4378b7dc4344c82442b7b28342ad9c6541bffb6f41b7338b4183cd8d41826078417a81cf4173263f415b260b414a2693410d282340b90f4940a7f49a408064523fbf8a8c3f313b65
  | 6, 0, 4 => 0x6897c12f67f691a067b12ee367ae2a06677673d966ad06a565b0f9cf653d59ad6523650864ec4d4f64a08d2f638b7f9c635e23ba63480f61620312fa61f432cb616ac2cf615f47496148f8a260c081b760c03ec65f72ef455ef5cfdc5e8bb1c25e33bce65e177c725d9ef9a05d6698645ce8c8bb5cb6ae3d5cb1fe155c0439a35bf22aa55bea70c45bc441ed5bbb23a85acd4a505a978a32592b136c58bcfd2357d10e39575fbace56c367ce56ab450656882d2e565b55415630385255ca4cb15593a3e1556313d05540d0a654b329a954ae79815426324d535f9149532cafce532b54bc5321809252a828325285ec11519ec0a451278ed850fcf79a5006acc7
  | 6, 0, 5 => 0x7c12a6dc7bcc9cb17b08acdd7ab6d2f37a98c0657a6dda387a2fa2927a0eec3279f62c9279ceb6ba79930e2179200ff078e7c9f178c7d28f7892ed5c7891b1e4782415f177a60ff377a3bc597791116d776cad687763184c77365ae1772d50a87720ead276c4582a755243f1748b7758747a456a740f224873fbe2cc73b073b8732255e172ef6dca722046f47112267e70f7cfc670c44dfb7020915d701232276fe98c426fa28b5f6fa037c56e648c466df603116db47e636c87f2c46c8398876c76c0d66c5e9d666c52bbae6bf75fd76bdd12926ba26c6a6b086e886aba7bd46a3baabc6a1cc260698ca038697b90ed695f71e268ac406a68aa0679689eda76
  | 6, 0, 6 => 0x8e953daa8e6a85208ceac1a68ce6206a8c810a2e8c29bc6e8c1fd62d8c0b847c8bc07c358bbbb8e88b9517868b8de4ab8b8b07818b529a6b8b392fdd8b02f4388a7a9db88a47c63c8a19a66b8a072a0589ea70d58952f4408931925e88ee51f588def13f88931dff8888c9e78842110688272ad888263da48825b57d875d8dfa8755af5187191cef86fd53ab86db269e864aef5b859ab80e856b869a84fccbd184e7433584c69f75842637da841c519983bcf7a183b8345482f225d8829e5dd682771924824787f882332726812e0dca80e976c3804e48a5804d32567ff33fb47f45c8f47ef9cf177ef3c48f7dcdede77d7c07117cdd11327cb5d8077c19adc1
  | 6, 0, 7 => 0x9eeec4469ee922899ec9d9309eb63d339e47ab8a9dda28589d6d7b039d5f2b019cb97e2b9c769c849c751a479c2da7469c152aac9c029e899becc0779bbbe39e9b9b45a39b6ed1639b5bb1f19b35c5219a92b55f9a6d4a6e998a7148995a037b98e4b8dd98d6244598232c109819032597d7cd8597a78488978f875b96e7d77e96d24b5895f65730951eee9b94ff8b2994cfaf2794a123eb948c8cf893fd1ed893d611bd93a4b7de9391693f938dc2bc9387d4e7936b4ccf933cb471930798e9927bb89d924b4ad09208fdc891567ee79109a4ed90f9298090d29fb190c914da90b2209290ac661b902d5b0c900b576e8fd91ed38f35e3838f346e288eb4b34b
  | 6, 0, 8 => 0xb64d58f5b64ab510b5cb4dddb574c2ceb533f09fb4458a1bb40c4039b3d88913b3244fb9b3096afcb2f6302eb28b7570b1ad1411b1a27f24b171046ab0b62913b03b1c5fb02ed5acafda5c95af8c8b44af5aa227aed7c9d7ae7a07f8ae47307cade9db15acd99b96ac463922ac420587ac269518ac251fbdab99d814aacbb10faa939139aa87f0dcaa0ec716aa07787ea9d70228a974a9e9a93db95ba8fc3611a8cc5a0fa82ef85ea82b5118a7ed6f8ea76b0c5ca71b75e3a6768364a65948dca573a3a5a5688b9da4b228b2a43568c8a406231da35d6367a2cf61fba270cf02a203f3eaa1ca3707a1900e47a1712555a166c7c6a1203fb3a0e14f349f6f6474
  | 6, 0, 9 => 0xcad7f953cac0d3c7ca6298f1ca58b31cc9c932d0c9b77f35c8e7510bc89d7b8fc7d897a9c7c84d40c7095365c6fa342cc6655b7ec64938f9c57da38ec551c899c51fa9f3c423096bc4229849c3a85e1ec3573493c3416dabc2d474bfc2cdd7e9c2a0e184c25e5e0ec1c5ae3cc1b5690dc155f458c134a7bec0920075c072ccddc060a091c05fca4bc04907bac04157cac03ddbb7c021bcacbfea19b4bfe28f24bfd51315bf9592e1bf1a8222be61d6eabe50dd89be4af849bd15572dbb53afffbae3eb25baa6b062ba5bfb4eb9a2143bb9968a82b98347cab9653685b931e345b91e58dbb909c410b8d36980b8a08e2bb7d9e024b75e26bbb749d50ab6db4e6b
  | 6, 0, 10 => 0xe24836b6e2199ef9e208b42fe1fd7feee18f97fee16df81ce0bf0984e0addab3dfe04b27dea61aa2de3e4239ddf798f2dd82b20adc6779cfdc3acc6ddc29c0fddbe35342db2c04c2daf4aad4dadab8abda912719da4cc335da161a65d9f9fb5ad9a47bd8d76a5bfcd708d53cd5ace93ed51552b6d50f91b8d4d1b38dd43a869fd37e4266d3315ec6d2e4c6dbd2d73417d2c3bf0cd23889ebd207a363d195b865d15e650dd0deee00d030b325d01de6f5cffa0c58cf994254cf717ba0cf54d149cf352890cf1d417ace649adace57ec36ce4cede2ce4cbd8dcdef7705cd812822cd2f9a87cd12cd33cc385f10cc22a61bcbc5a530cbc12d58cb7a0fdfcb6a769c
  | 6, 0, 11 => 0xf7317530f6c286d1f69881caf6807c71f61649e1f5a60103f4c47380f4b2f759f477dc2af425a199f33a46e4f2cd7906f2aa959bf23f7728f1e3e927f1bfa95ef147879cf09dcfaef06be8eef06aacb8f0534097efb22faaefa703a7ef572062eefebad1eebf023dee12c54dedfbc500ede1a710edb12d2aed4639deec965f4dec7098acec4a9ec2ebf22ae1eb9cda82eb43b91feb2014dbea0c38c3e9f445a4e9bc24cae95bf40de9153832e90b3c2be8aa00ade872ec00e86cd99be8319215e8057c40e707d935e69f9199e653b48ce5f8406ce59798c5e4c4500be492dab9e489c2e7e4471a2ee39955eee37d8f58e3498518e2e7cf66e291c940e25047c9
  | 6, 0, 12 => 0xff99db15ff90dde2ff240698fedf4f46fe804993fe1584a5fdf9659afdf4a2a0fdaf6c9dfd76da79fd3b5006fd380cd7fd142868fc813e75fc1eeddafb3b3221faba10cbfa861961fa79027ef9e76dbbf9b0318bf9366032f9102696f8e68dd0f84d177af81be560f78d594ef760f6a9f75aa4f6
  | 7, 0, 0 => 0x8d21a8508a584ed0895d519086df8bb081475360812e9d208028ac807c6446507a1618d07852a5a07540f08073f35800735b00807299a300709560f0694c2350686615c0682030e05e2e7ad05e0f05005d3351c05d2cb9505b8ad5a05b329cf056c7bd70567fa510533fba60532d23704fa6d9d04d064d1049279e8049176ec047e8d15045c05c00451cc9a0405c08203d42f3f03afd08103ad58cf0331cac6031b206b02fbbdeb02e65fec02e42d5302db817802d3625402d338cd028b04db025a06d302463e470244bc3801dfe0b301bf50c301b60d15019f51af015f40100104396600f26ece00d64fc300d1a74d002526510022e4f5001c45a1001528ba
  | 7, 0, 1 => 0x11c9fc591168de381158bc8d11472389112ec5f5112b6c90111b2bc010d730f7109959ad1053c684104dd56b102dc9f8101cf3100fd8b3870fcdc10e0fb89c5c0f88aeee0f78e0f80f5e8c8c0f4449ac0f32cd070f232de10edf210f0ed4fd100ecd7e060e86711a0e68f5ce0e61175a0e4468b30de1f81f0db6ae630d6a41550d4c96070d48d7080d37803a0cfdf2310cd3e9650cbb9b490cb7cb8a0c76b2fc0c3025590c1de1fe0c0600430bb355150bac83940b8bbf6b0b7770420b6f2f220b66943c0b619aaf0b614b950b5d6d290b0d46330a5a70930a4b0a760a49c2db0a200d4a0a13a1ea0a01adfb09d69a71095537f9092d9a5f090b2c3008e50898
  | 7, 0, 2 => 0x19570811194a9f6819324a89192f3fd618f7b2bb18bc18ae18b98c20182077a4181b6ec817d900ce17d145a217bd685317bc20f017a485a01769b970176707ad1747ce40172babbb16f738fb16e93f8616c7550716c4ecbb167ebc1d1656f99b161b607615d61f6415c6dbae15c5698315b8d2ee15b2a53715930133159152e71585bdc915522f70151d519914e6f9fa14c1c47914b7c4bd14b3ce6e149a4ea1147805fc146907d91460b5921425a5261410a821140ddc32140984d713fda56313c54b9e13b639f4138bc72e136560ac1345c7c51300569312e4a74a12d4145e12a5b21f128628ed123727b51231c29f122391de1205328f11f546a611e861ff
  | 7, 0, 3 => 0x21701c6821677a512161cccc214d3e85214525f5213fe88e2132c46a210940e420da045020d5173220bd10b420b14afe206d00e32016bee31fe54a321fc1b3651fb2e6a61fa9b9161fa9a8051f90ec081f548f781f2f304f1efc58d31ecad99b1ec8714f1eb37cba1ea89fbe1e82e74f1e56cbc31e3d7d241e12f6b01e0058df1df4fadf1dc0ed751d817d661d1a31a91cbc6c011c9476741c9385c61c92106b1c6686f61c59b8491c4743d31c1160c61bd07d241bb7adc21ba9074c1b9b06e31b8f4bc21b77905d1b23c71b1b0c122d1b01564c1afbbe891af7262a1ab687241a8db47d1a76b50e1a5d9b5819d6e25419c5f3be19728323196c97d4195e4838
  | 7, 0, 4 => 0x2920d6ee290d7ed9290ba1ff28f8e7e628a5bcb4289d79c2289b6973289ae8a1287632fc28708577285eafc82841347c28412658281da14c27c003a927a7a87827a28a292794709c273fec702730f4cd26ffdd6726d06c1026c74c0626c5b4ad26c045b6264e1b3926144d362613f6fd25f87f7325f197ff25d07e9b25c5d19325c57f8825c5372925c4720925a675cf2563fe1925613c152549209624f1d90e24d5ba0324bff09524be3768246a0b8a2461748c23efb98523e4b78223715109234439c9233bab09231c4f452308cf9f2305e8be2304dae022e9b86822e36ade223fc74c221a04bf21e86b0521da66e821c06e8b2197efbb2195a69b2192d987
  | 7, 0, 5 => 0x308ead5a307c5741306461c73062345c304e44793044b9103037a380302a0ae32ff39f242fc9c5652fc7fa742fa60ebd2f7e31ac2f7e29e22f2664432ef590472ef501342eed69452ee6a1a12ee5f83b2ee0625e2ea15e5e2e217fe22dd5e4112dca65fb2d6782ad2d4ca52a2d44c2ca2d0b08af2cfda1512cfd4cb22ce182462cdc11412cba5f7d2ca409f32c9d909e2c7ebae42c60eef42c13df762c0d41422b93415e2b72e4032b5379482b411ce62b3e9fc02b351a482b0c54332afc43912afbe5a92af61e482ae6ef722ae3339f2ada82fe2abf74ef2a71985b2a5af2ea2a5553532a3c183b2a2b48f729ebd86a29e09a2c297cc0d4296be61729676491
  | 7, 0, 6 => 0x3a8916763a7a6f103a6372fa3a3663393a3459363a0550d43a046aa139f7320a38f9f1d038f9c94538c12eb938326dc1382d8f7738168c5937f723b837b2cada37ac804e376a4f69375cfd24375c328c37586489371fff3136f914db36f8386a36bba0ba36727dff36374b243620a03035ecbe1335e7bfcb35d968a535d7765e35ac22d835895b04355ab1d03551f278354c0f9d3535d36d352c24d9350e8d433509393734bde411348ee9a33465f32b346473883457b942343d615f342d3438341c5d50340c055d33c30ca233b8069c33b3dc6c33ac49493344a17a327951d13276ea7c326f6bb331f3ad7631c32ec3311656bb3107d3ae30f28d1230a94148
  | 7, 0, 7 => 0x41c6c27541be98b941b837f04183d824417c5d42417ae7e74156fa7441230c9a40eb971d40e6327b40e06b1a40b04b7940a506c440a1669c409f8ab4408655d940811af0400633023fd89f2f3f8a32283f36e8fe3f12e7d53efbbcfe3ef2c9303ecb0bdd3eca17bc3eadf8b13e9bf4f73e4848ff3e435d163e2a98cc3e2548743e2424c43e19f81b3e118dd93e066e433dfd3a643dfa8de33d9cb1693d6b71c53d5db2783d4d45463d43831d3d35d18c3d084ce73cfa499c3cc98e253c7bdb083c6977bf3c5fea2a3c4da15b3c1fe1e43bfbc27a3bd7674a3bbb8b303b7cf6613b6671ed3b573f9d3b22fa393b1437703adbcc2e3aca73853ac378663aacf352
  | 7, 0, 8 => 0x4aac3dc34a9c663a4a23df284a07ce474a04c69849f19482494f19304904ab3748fdf2d748be36e948a30f48489636af4860daab4851f9d2473a6d9247308869470552fe46da305e46da15bd46d9577146cd9c5046b17d45462101e54600bef845fe127745e12de845de9edc45cb8677459ded53459243c7458c1b084571c3254566e491456621344561370c452bb7f64516de6e450d58f64508ab2444f7874544efaef644b0b53e44aae862447f5f9c446609b6445383ff444a90b04433319843ff470e43e3fd0e43e12dec43c11da543bdd24743b97bdc434d0023434424c5433fa33f432efcf84328f2a342b870d04266f78e424b72b2423d3c4e4222f01b
  | 7, 0, 9 => 0x52bc8da352b710ef52b64cc852afc257528b5c3a528577355271f78f5270ec6c526f455b52368d0152267abf520b52db52084b2c51ed447051d54e5151750ba651529dc4513f899f51001be150fcb6f250fc017750f4e59f50c1bb7d509f8ca35047ce894fe884164fddcc1c4f2d2da44f2308104f06e9054ee29ddf4ebdb7684e8225634e68e09d4e54bd934e42b01a4e40162e4e2ff7f04e1ca4aa4e0572e64defa2b84de119ad4da171e74d7c1ea04d2f3c8a4d26bb934d1a63024d121f5c4d10dd8a4cfebf194cfa2ad14cd640494cd3f7294cae6cf64c36b62c4c172de44c07482c4bd65d2f4ba712b84b53d6034b47a9594aee95694ae809a44abb1790
  | 7, 0, 10 => 0x5a757c235a69bac65a656b815a5f46385a2b544f59d8d2e559cb464e595fd0705943b16558e0007b58ac94e15896b7bc5874c9ef585f71ec583e54f358224c155813abce580aba2258039e4a5735f67a5710d06856f73cc156f51c3656f3747f56ca5f7656b1349156ae68fc569515865679d04356590b9556337c845608f77a55f262bd559697f95593c9de5593a3e15589eea5557ef27655784b9c557784d6553eb09b5539a68b550f9dbf55073dee54e35c9054bb1162548e179a547f701d5478803b5462abd054617bf954566bc6541b196953eb878953dc75bd53c3f8a45396465d537f76e65360bdce535d66b7532862f0530dd69552f219fd52c9be74
  | 7, 0, 11 => 0x627d29de6232122c61d9161e61c7627361b0ce8d61a59074616dfee3615159d760dd91ac60d6c19560d35735609ba710608f0109608a602b607e89b7605c2bfe602ebcf1601d50b9601bb43c6013f4555faa2c4f5f83829a5f6a82755f66e6445f6459b65f3975ba5f13a1b05f084a655efa21385ee0e9d25ed1d7c75e88f3ec5e33c3765e1f89135dee6b6b5dc0c5455d995c535d97f1e35d51ec065d42352f5d017f515cd1d3785cb2738c5c90af7e5c8704475c8048ac5c7c04cf5c4539315be7e2d45b96d7675b7034a45b60eb4b5b5840ee5b4c7f215b3983f85b212d615b1ef03a5b1b4a615b10def85af33ad65aed0b785aca5d735a96d7c95a79a54a
  | 7, 0, 12 => 0x6a252a2e6a161b4269de091c69cae70769b46fdc6986998d696e78c469658e99693e0e7b6930df5d68e1164068ddca6368db01f768c7606168bee2ec68badc8d682cfc416808476567f8c41b67bd3c8767adb0e36782891a676e0709676ae4a96767de4a675c9966673d759c6722ad00670425a966f87fdc66e46e6666e34aed66c18c7966af1a9a668c78806673fe51667312616658320f664adcf26608c4136601c8f4659ce0e7657f5166656757586509429664ce772864bb1a68649434126493563e6483cd406438425e63ff7f4763cf269a63ba960e63b72ebb63ae5c09639d7a81639a5bfb63965c28632c34926324045f62e22b8d62d6318562a89ff7
  | 7, 0, 13 => 0x71e3fb21717d774a71541dde712138b27101265370db175f70d1106770cd5ae470be6121708a573770397887703171d9703080d5700eb7ac6fec830e6fd9346f6fa3a98d6fa224ac6f508a4a6f1f7e7a6f172c546f0608ee6efc04706ef35a186ee6cf816edf7c9c6e9f61156e83e6036e7696f56e6656486e3433cd6e25ed676df0fec26dd4d0176da035b16d82d5fa6d72199c6d6172a36cfd717f6cee2f236cd163926cca26066c96dad26c615d286c322b636c0ecbaf6be357526bc7d1216bc738476bc4a6676bb6c94b6bab9a0f6ba0ff156b58ddda6b22cfba6afd64966af2f3f26adad7966ad9b6196ad97ffd6ac0678d6ac0491a6a7bb2e16a75398c
  | 7, 0, 14 => 0x79ef6f1079930e21799132927976ef1678ebe05e78de9bf378d0df7878ba6f2e78b151a6789e7b0c789d0a56788162197862d6897860e639784d1d88780c022477ff6aae77e8987277cbd18277b2125f77863a7877540ede771e700576e3013076bbf7e376abcfae76a9de0e768d3e1e76883f0f7669dadc765f42f5764f73f7762971fb761777c47590c5d175766dee754e9139752c4d3674ff7fa474fb6bb774ce10617480d24774730a6574381a62743377b5743129e87412504373e4978d739f2b3973951930736f7e65736b23c97322a3cc731d845a730b3a7572d87a3472ba3b11727f37757278be207238611e722f62307217b12271fe46de71ebea7c
  | 7, 0, 15 => 0x83079e2782f798d582c9e5be82b6236a824f20f68236f38f8232e66481957b358128f3f380d4e88780d3e75480b8c97c806943d18050a21c803b4860803a6ab48035e0d98032d812803070bd80231ba0800f86b87fc8d0e97f89bf0c7f21f4997f0e00867edb507d7eb814087ea6fb037e9642097e7062897e62c7897e151cff7dd7bdf57dc84efb7dc7732a7db0481d7da6eaa77d6e9ad67d4a419d7d2fd1ca7d0c8cbb7cfc430d7cf9986b7ca027e27c9f7e7c7c7f02d67c3f68397c3b9ef67c3a52057c34d6c77c2e85b57bde17317ba3efb57b8ebac67b8055d47b7c8fb07b6ea85d7b4fb6487b2108ee7b1dd25f7b103aa87a5716df7a32e6c479fd2fbd
  | 7, 1, 0 => 0x8ac1d3288aa94f158aa2abe88a88182a8a713de38a6e20898a1656d289dcda8889ae061d89a878d18998ffc989753550895dd9a18952d7948944bb8888ef6b0288c8f86088b6d63c8899b4438869664f8856635b8833f5518826a0348820d24187d4a50f87c93d7087b0a97e87a82a1f8778745f874a584a8737715887263362870d7b5f86c6997186bb989c865f7def861a5c8185db428985c3ded685b3ccb185a908c185a3bc0f85839d3f85721f6a8569673c85437c8084ffc7a184fccbd184f3169584d2c17584cdc56e84b1beab841cbaf984135e9583e19bc583cbd3c083b647ca83b31a7d83ac4283838cae8a8363c3f683490ab0833dca22833c7e94
  | 7, 1, 1 => 0x91bebc9491b41eab91b18ab191a36be2918b0092917a50eb915a486d90f2ef969098f311909436919063d3a49061903f90269b48900e35ef900cc7b68ff9fb1a8ff96af68ff3586c8fccc2048f7bf8f38f69047f8f4ddcde8f2f8aec8f10fff38f088a868efbfe658ed4acb68ed3aa658ecc8e8d8e6a85208e5910f58e4b49138e3c73528e032ec18dc02d048db72a9c8d9ebf6c8d9225708cfc787e8cd297818cbb13f68cb5433f8c899ec68c89107e8c7cbb378c3afb688c2c48f78c0b847c8c0b0fa78bd6858c8bbc70aa8bb9cc5e8bb2b8e58bb1328c8ba351498b9a7c8c8b90331e8b67488a8b5cd5cd8b55b5f88b414eb68b3625d88b04dcb88addff2e
  | 7, 1, 2 => 0x9897bb25986e80b7984429e79839f57d9811ba83980f33cf97a689f0979e9579976c89139747c8749737905a97356364972b1cb896d72ef996d01321967edfc89677bd2a965c9589964ecda7964c72dd96305e1096172dd495feb81b95c99a0d95c7433b95c3b1989556de689556175c9553881e94f6110d94ee460f94e8795694dbd1b49493f2d894726a869466b5f394603ffe941fa722940b257293da0a2093d56e6b93a54b62939314a693713f05936b4ccf93593a8c934f2dc493384e8a9323bdfe932242409305732e92e53e3792ddd80692dc81ee92db4d9f92c1fb7a92acd3a992928040929274fd92646ea391ffdd0791ecb7d991e1923691dab36f
  | 7, 1, 3 => 0xa039bc45a00525279fa3366c9f9effc39f9a99c99f8844ec9f7bf9f09f6c35d39f469a319f0c24059f06ad0e9ed42a8b9eadcef39eab00239e7b41be9e672afb9e4ff7719e0665df9e05ebda9dfb72369df4f9a79deb9d439dd2540b9dd249f19d3f16bb9d3e8f329d3df8079d1c0c8f9d14bd429cf995a19cebfdea9ce503cd9cd5fbe69c76c2089c6395789bf8bc329bea8a5f9bd8f2ff9bca85189b8e2a269b6f9ad19b6ed1639b52b2589b4c7f429b0132a19af8ecd19af3a5179ae8c2cb9a8bf7aa9a759f419a67f3379a4707359a43ff869a31aaa69a2873fa9a1c8ce89a158b9b9a05b94e99c1f15c99b7a33f998e521e9937be1a99232e8698a20661
  | 7, 1, 4 => 0xa86f31f2a862bd1da854456da84a90f6a8255610a8206948a80a6233a7ff01ada7dcea2da7db6d6fa76199bca7358eeda721479da7070867a6d49e51a6ae84b7a6ae2eeea66aaf8fa65cb2a4a64e8b36a636e1dca6365dcfa5f87e3ba5ef21d7a5ba3af2a574db23a54714f0a54213c6a53f8738a51841d6a50155e6a4b7b929a4755945a43fb907a4234630a3efa234a3c6d6c3a3bb3777a3b74bbea39c9fa5a3731f65a3593a05a304b735a2a168daa25d3cd5a241a4fda214873fa1c22db6a1b60c82a1a6cf88a19ac5dda18ed7a9a17d41eca1607947a13bd84ba1146739a0e18795a0ba2447a0a97e27a0a58af5a072054ba06bbb55a05bb1f0a03eb38f
  | 7, 1, 5 => 0xb0b5f4abb0b06ff8b08e6291b07148bcb064e7c1b03f157db03e1077b03b1c5fb0316723affbd78dafdef203afd5efccafc6cea7afae9a9daf552038af359018af2bc6ccaf2022c0af0a244eaedbeef0aed822e5aeba08ffaeb8f7e5ae963e02ae8e3c58ae603738ae49084eae44786dae08364cadd85335adcd7a96adb0dd5dad74bff1ad4fb26facf4fbe3acddb1dcac2bc6f6ac203c81abf7c5d0abd61055ab00b1adaaf7e2b6aadb85f3aab8de38aaaa4cddaa9488bdaa82d705aa452991aa303209a9c57c00a9c34916a9aa541ca9a87301a99fc019a99d0106a9925c3da9536d8da927f774a917ebcda8fc3611a8ea807ea8d0e661a8cd2faea8aceb64
  | 7, 1, 6 => 0xb985498cb97b98a3b97ac3e0b97a58bbb970d61fb96663b4b954389eb911a0c1b9114bf3b90d0024b8db3bf4b8b4c543b875c2d6b82ebfcdb802dc33b7d97460b7d57de9b7d3b0e4b7901f62b758a4ccb749d50ab740e981b72f4b60b71f4a81b6c745b3b6b913f1b63e8ff7b60d03f7b60754e6b5e0fc76b5dbd7c9b5cc220bb5c668b8b5b461f1b5aa49adb5a9bb0bb59cf503b5784485b4e13670b4d28f2cb4ab7f69b46b6fb3b4659c05b40748eeb403b48eb3d5dde5b3686ebfb341a868b3156a73b3129c5ab2b438ddb2a00218b299699db2902c5ab26f73fdb26a3914b1af7eb6b18e64c6b176d427b158ad0fb11cca9ab104e717b0e0351cb0dcbed4
  | 7, 1, 7 => 0xc17f1d37c169e848c157bd32c124aa0ac11b76cfc10c93d2c10c1b3bc0f38e65c0e46e0dc0df4715c0c437dac0c3705dc0aa5d7fc0a94172c0a7fd53c0324461c02871dec026c9e4c0222c96c005c2cebfe1c44dbfd73578bfccba17bfba1f09bf8fc338bf75efa6bf594db5bf4ff589bf1f539ebf09e5eabedc76ddbeaf8f93beab9042be9812f9be769f18be652655be54e56bbe159bfbbe1213a2bd9624e0bd5c6ceabd569d44bd341972bd318850bcfd0d22bcf80b4bbce0ee17bc885194bc4e049dbc2067d6bc1d1430bbfcd59abbf2c6b6bbe6e79bbbd7439fbbd376a8bbce6b82bb6bf353bae435a9bad421dfba506113ba11faf3b9f6f76eb9a82248
  | 7, 1, 8 => 0xca08f644ca011952c9f8ee7ac9ad816cc98e47ffc972257ac93615f1c90dcec6c90b667ac8e2cba9c8da031cc88c5676c87c4895c84d79bec82a4e78c81e2380c8122111c7db80e1c7c57366c7b9162ac7b58e37c7aaaf4fc78b844fc758fffbc72fa268c72a8082c722d832c7147b79c708d5a6c6af14d6c69e7be3c68acfd0c64c00a3c6159836c5f87b2fc5dbc5b7c5d82793c5ca4838c5a7e8ddc599a974c58557c3c57fd30dc56b8624c55fe387c53b428bc532c1fdc4828b8bc476fc82c3e5b604c3aa5cb7c3827a75c380b1afc3753fb4c35cbd48c35a0575c2e7ba3dc2d474bfc2a56e5cc232b877c22b236ac2157f87c1fd94bec1b1df49c18ac36b
  | 7, 1, 9 => 0xd28da698d28c47b6d281ea23d25628d3d1f61820d1cce4d6d19e99b9d175aa0ed16ca0bed11c0b79d111535ad10ff778d10eeb0ed0f46623d0e09d4cd0bc3a17d06fa9abd062548ed0390299cfd785f5cfc0ca30cfb93b24cf96ebf8cf2e0516cee27a34ced54856cec333d3ce846d20ce43ae61ce32f271ce317d5ace07748ecdfbffc3cdc18071cd8357a1cd5604dbcd52d7cdcd43454dcd359d45cd19e6bdcce6e03ecc9873f2cc86101fcc7a28d9cc684041cc2a050dcb9fc35fcb9f0c58cb914436cb843643cb7d8f0bcb7d4e04cb78c448cb76685acb69ce5ecb14d575cad8ea57cad7f953cabe2c2bcab9c397caa8f2f0caa3d448ca288e20ca17292d
  | 7, 1, 10 => 0xd9fa4268d9d3059ed99b48e8d982c8fbd95bb36bd92ea3f0d9137c0cd8ed43cdd8a9c1e2d88ce72fd871e3f2d82ac424d825c4b2d808765ed7e5e446d7db0a89d7d7b214d7bd6d5dd7bcbfb8d7899138d7806269d76d8d27d74eaf49d74cb44dd73f0427d734ab98d71bb645d719f753d69eb6ddd687bc3ad6576e93d64732f5d6363344d62f38ebd61a4d78d5e6dcbdd5b41e40d5a576d8d57f7a4cd5443201d51f7162d4f0f799d456f126d43e7fbdd43a869fd40806fed4050714d3f580b8d3cbe778d3cb818cd3c5c492d3a8e0f7d39eec29d394c8cad379eceed36d52f2d358ca24d338bdb8d31f0cebd31e59f0d313bffed30500dbd2d79b92d2b37aa2
  | 7, 1, 11 => 0xe2f73a11e2c0314fe2a3a791e29557f5e283c095e27b5cc0e260d469e25821fce23a18e3e2178fcee1f09bdde1b9431ae1560784e12e834be12bd740e0bfa32fe08a5211e07f22d5e04d6edde01f1c9bdff5649cdfe94487dfca1832dfb96348df99d6a4df38302cdf382235df21d78fdf140ce9df138139dea768b3de9849e3de91cd35de8ede08de4dbcd2de49630fde3f5106ddff65f2ddea6151dd44ebefdd22f5f6dcc2d6ebdcb4ba0edc8e32f7dc15be7adc0b8b92dbff3966dba270bddb94eee6db7c6105db61cf48db08856fdb032183daf3b57ddae88803dae1e332dae1e286dabcacbbdab6ff36dab10399daa4971fda803c01da7ab10fda6a175a
  | 7, 1, 12 => 0xebeca87febdaeb21eba52384eb7e1f2aeb58a678eb406b8feb222eefeb2014dbead8cca8eacca4d1eab44034ea8706daea483678ea3d9d77ea036fe4e9d791d3e9cae13be9c148f5e939b56ee915f6bce8cf8ba4e8c7fbc5e8bab8e2e8b32ee1e8a78d9de881f5cbe85a7ff3e854581de8009180e7deeac6e7bc1e00e79d5b38e78ddb80e78c552be77177a8e761dc12e73ba6c9e7311744e72b167be71705cde70ff086e6aaed47e69551c9e626c786e5f2c308e5ae65d4e5996144e5728106e53126b1e52648e8e5159907e4b92357e4aea01ae4ad08b7e4a9c7bfe4a63fcce4966ad9e44ff14fe4386609e414a759e35521e4e3412cc1e3247725e30df211
  | 7, 1, 13 => 0xf46969daf42435d0f3db11d9f3a8a818f36d449cf346e419f2d02965f280ddebf27f4315f27b317ef261a728f257469bf25261f5f24e026ef22c7eabf21bf636f21b1b9ef206f478f1fe0360f1dccc71f198f40df195bf85f1350785f11de759f0d31038f0be3d76f0b6b375f0ad96f3f0a4ef4bf0857a5ff071128bf05e0487f047ce9cf041e202f0296f4def7db586ef57b8faef335fc1ef2e9b0fef2c4c96ef1265a0eed39095eec4f473eea663e9ee5cbc09ee459ecdee18b783ee16be6bee12c54dee07bedcedacebaced929b2bed8629efed26731fed19da12ed127202ecf6989eec99ef6dec663512ec65e546ec31def3ec20b13cec1a7a9bec01c0eb
  | 7, 1, 14 => 0xfddd6bbcfd9d02e8fd1304b1fcbd4b15fcaa14ddfc8bca0cfc4e4806fc20dd5afc02cecffc019be2fb564cfffb50720bfb3e6e67fb2e4632fb10699bfacfb439fa868decfa2bdd19fa1398e4fa0187f4f9f779d9f9dbef63f9ca1920f9b38880f983276ef9611aa0f95b9794f9554771f9552142f92dd199f8d7fe68f8963dd8f874971ff848f742f8456696f82ca004f821a1bdf81aa65df80abc96f7c7ccddf7813a1af75b3d8ef713d73ff6f4ac3ff6d72280f6c05a35f6ab2546f69beb92f68e4a3df66671a5f660409df644b462f642186cf61a42fff61649e1f60e6587f5f81425f5e595ebf5e05daef5373f08f51b75b9f4fa1d32f49e69cff47b8f92
  | 7, 1, 15 => 0xffff0634ffb86463ff86098aff6bb1a7ff4da10aff3a811dfee73185fea4321afe971ab2fe82066dfe7e7e7afe69f639fe5269ebfe24198cfe178c23fdf0164bfde91a7f
  | 8, 0, 0 => 0x53fc1e2653e3298153d9433552c6dafb51f0701b50c1bb7d50ba5f8b48be36e94749554c46ce9687455fb1d044ea489043fdcee4424b4c7341a234a6412582f0409e34a43fd242ec3da3a9703d88f54237fc88ca368f6cac32c96d1e3116eaad2ff1212a2ee5f83b2b7a0cc629e93d172990644b293de18527a4a97823fc0e4423d4986c23937e85220a9a9b21d460ea21b4474221a9023c2136416c20bd10b41feab86f1b54b30e1ad3e37a19edd2a918b98c2018097fbf1803566016c885cc155b070712c7ac7e12a036a6128177ed11f546a6109989db0f88aeee0eb2ba8a0cf6d6570cda57470c041eab0ae68dfb07852a5a076d9aca075d3abb0426a541
  | 8, 0, 1 => 0xa184c90da0bdc9859f9b20929deb9d439bea8a5f9ba44aeb9b237b579a8d182a999e3acc98a7fe4397b3be8397181da995f9626495cb9afe94dbd1b49244de83913e368f909436918f0252678d4f66ca8c53b6888b3625d88a713de388c3fb8587a8462485823cea84135e958260f229811ec7de7f1e4fa97c1b05047bdc910e7b7c8fb076e1ad9c76abcfae7673e45e7663a7c67596bf2d749a204b740279ad73be14ec724ff73c71801e44712a2db97082196870519bba700149d46f9675c96bf5ec266af4746f6999900367af13ba6722ad0063e020e461318505604bbc7e6013f4555e6214035c6c86d75c5597f659428c4e58652e3d567ab1f45400b90d
  | 8, 0, 2 => 0xeacf38b1eaa4dc92e95ac8b5e76e1fb8e6c3db03e5856fa9e337d007e1f09bdde1c02f6ee07b3ab3dffd34dddeae0fc1ddf5fcc6ddce86eedbff73e2dae1e332dab6ff36da1ba67fd99ad6ebd992242bd749a837d58f793dd45050ead428db12d2b37aa2d277431ed111535ad0bc3a17cf54f589ceca0d03cd79adfbcb884e68cacb121cca93785dc9ad816cc92fe007c90dcec6c7b80108c77d5d96c6579413c5af49adc11b76cfc0edcc81bd95ab3dbd541193baa031c9ba53eca2b8db3bf4b7acf0edafabcd08af359018ae6ff2a8ad70b361aba98afbab2b8525a96bd003a92e1f67a906a98fa5ef21d7a549f6c7a4c92733a2729855a203df1fa185d949
  | 8, 0, 3 => 0xff652815fee14d72feceb7ccfdf7bd66fc453af5fb8cf931fb1f7172f6b22f67f4c886ecf46969daf452118af29f8f19f1af9c79f179c596f13196a3eecba126edacebacece124ddeb500845
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x100d4104c00c0150c1300100d4104c00000000a10a00000028430003100a20100000038418003101220100000028418003100a20131014314c000031012201000000284288015081300000c402880400000c410100000018428000000e10c000c4048804000000e10c30054304c00000010410000016310804840508530000016310804801508130000000038418000000610a31014314c00000000a10a000001044144025041300
  | 5, 0, 1 => 0x610a30054304c00000000a106000c400880400058c420100016310804c0150c130000000018428000000e10a00000038428000508520000000028428c0150c130000000038428000000610a00000038428000000610c30054304c000000041105000d4214800000000a10a000c4028804000000e10a000c4048804000000610c
  | 6, 0, 0 => 0x4843c00001041000000002843c000004110f0000004840400000c41010000043045000324c820000006028800000180a20000000038404000000e10f00000018430000000210000000310404000000e10000000100400000000e10f00000038418004100e20000000104414000000e10f00000038418000000610a00000104414000000a10500000104414000000e10f00000028414000508520000000008430000000e105
  | 6, 0, 1 => 0x310404000000a1000000010040000304c02000000a038800000000a1050000a03880000425082000000003843c000000e10000000048404c0150c13000000204880000018122000000002840400304c02000000031040400104122050000000843000000061000000004843c001040a2050004103881400425082000000e048800000000e10a00000048414000000e10c0000e048800000004110f0000002841800000c4101
  | 6, 0, 2 => 0x14314800000000610a0000000843000000121050000003843c000000e10a00000018400000001210100041038814403504130000000028404000000e10500002028800000180a2000000004843c004548020000002038800000000a10f000c5310800000001210500000310400000000a10a00000038430000001210500000008414000000210a0000001843c000000610c000000384040000002101000000284280000104100
  | 6, 0, 3 => 0xc404880400000c41010010d430800000000a1050000003843c000000210000000028418001508120000054304800000000a10c00000028414c4050c530000002018800000000610a0000001840000028122000009431480000028122000000003843c00000c41010000004841400000411050000002841400000121050009430480000018122000000010441400151012000000010443c00000c410100104028800000180e200
  | 6, 0, 4 => 0x31040400000121000000000843c000000e1060000002843c000080e2000000002842800324c820000081200800000000610a0000002843c000000a10100041028814003100a20100000028400000000e100000000284140042508200000060488000001812200000060488000025041200000d4214800000000e10f0000003842800000c410100000048404001041220500041038814000004110f000000284140000006100
  | 6, 0, 5 => 0x38400001510120000115200800000001210f0000010443c00324c82000000a038800000000610000000104414c4050c530000002048800000080620000000028400000000a10000000104414000000210a00000038430000000e10f00000018428000000610100000038400000000210f00101400800000180a20000000104414000180a20000000048414000000210c0000e048800000180a20000101400800000000a10c
  | 6, 0, 6 => 0x3843c000000a1050004103881400058c420100000028430000004110500002048800000001210f00000038414000000e10500002028800000000e10600000048404000004110f00000310404000000210a000d4204800000080e20000000018418000000a10100000048400000000a10c0000e04880000000061000000003842800000021010000003843c004250820000000104414000004110500000038414000000e105
  | 6, 0, 7 => 0xa048800000000a1060005420480000150c12000000a04880000000c410100054304800000004110f00000104414000000a10c00000048414000080a20000000038428000000e10f00054404800000000a1010000003841800000121010000000843c000000a1000000a038800000000610a00041048814000000a10100000018400004100a2000000003843c0045480200000000184300000040100000003104044035041300
  | 6, 0, 8 => 0x18400002048020000054304800000000a105000d410480000058412050000003843c000181220000000018430000004110f31014314c00000001210500000048400000001210500000038418000080620000000038400000081220000000028414000000e10a00000038428000004110f00000028418000000210600000008418000080e2000000010443c0000002100000d4404800000001210f000410288140002812200
  | 6, 0, 9 => 0x18428000000a10c00000028418000000e10c0000002841400008062000004104881400000061060000010443c000000e10f00000104414000004110500000028418c4050c530000000028430004050020000000018430000000210c00000038428000180a20000000008400000001210500114304800000000a10000000028418000380620000109420800000080a2000000004843c000000610a0000001842800304c0200
  | 6, 0, 10 => 0x8404000000210f0000002840400000411050000003843c000000e10a0000004843c000180e200000000084140000812200000000384280000041105000d4204800001040a20500000048414000004110f00000048400000000a10100000018428004250820000016104814000000e10c00014214800000000a10100054204800000001210100094304800004548020000115200800000000e10500000018430000000a10c
  | 6, 0, 11 => 0x18428000000e10a100d4104c00000080e2000000a048800004100e20000000048414000000e1000000000840400058412050000001840000150c120000000310404000000610a0000201880000000061050000003843c000080a20000000018428004250820000000410400003100220100000038400001510120000002018800000001210500016310804000000a10500000028400000000e10a000000484040045081200
  | 6, 0, 12 => 0xa048800000000a1060000001842800058c420100000038414000000a1050000004843c000000e10000000038414000010410000000048400000000e10a00041048814000001210500000038430000000a10f00000038418004350c20000000028414000000e10600000008400c0150c130000115200800000380a20000000048414000000e10a00000038414000000a100000000284300035101200000003104040000012105
  | 6, 0, 13 => 0x2840400001041000000002843000000c410100000028430000000a10000000018428000000210000041028814000000a10531014314c00000000e10600000028414000004110f00000048414000508520000000028418000000e10600000028414000004110f0000e04880000000c410100000028418000004010000109420800000001210500002028800000000a1050000a038800000000a1010000a038800000000610c
  | 6, 0, 14 => 0x10443c002510120000000038418000180e2000000010443c00000021060000000843c000004110500000028414000000610c00000028418000000e1050000031040400000121000000002841400000c41010000002843c000000a10600000048404000001210100016410800000081220000000038428000001210f0000003842800000411050010140080000000c4101000000384000002802200000020288000000006105
  | 6, 0, 15 => 0x114204800004100e2000000010441400008062000000010443c000000610000000104414003508120000000028428000001210f0000002843000000121010000003841400000121050000000843c000000610a00000008418000000a1000000002843c000000610000000310404000001210100000018418000000a10100115200800000000610a00000104414000000610100000038418000180e200000943048000000002100
  | 6, 1, 0 => 0x3843c000001210500000008428003100a20100104038800000000610c00000028414000000610000054304800000000a10100000048404000000610000000038404c0150c130000000038430000000e10600000104414000000a10a0000010441400000c410100000028414004548020000109420800000000a101000c4048804000480620000000410400000000e10c0000000843c000000a1060000002841800150c1200
  | 6, 1, 1 => 0x38418000000610c0000010443c00350412000000004843c000000610c00041038814000000610000000310404000000a10600000008404000000a10500016104814000000a10f00000028414002148420000000038400000000a101100d4104c0000000c410100000048414000381220000000018430000000e10c00006048800004350c200000d4404800000000e10c0000a018800000180a2000000000841800324c8200
  | 6, 1, 2 => 0x41100800000000210f0010402880000000c410100006038800000180e2000000002840000454802000000004843c000000a10a000001004000000012105000000284180000041105000c1300800000000e10c00000038414000000e10600000008404000000a10a0010d430800000280e20000105410800000000e10500000038430000000610a0000003843c000000210c00000028414000000a10500000008400000280e200
  | 6, 1, 3 => 0x28400002048020000000310404000000e10c00000028400000004110f0005420480000350812000000003843c004250820000000310404000000a10500000028414003101220100000048414001040e2050000001843000454802000000004841400454062000000001843000150122000000004840000250c12000000010443c0042508200000000484000000012101000143148000025101200000020288000005904200
  | 6, 1, 4 => 0x3843c000000210a0010942080000018122000000010441400425082000000603880000000c410100094104800000004110f000d4214800000584120500000018400000000210c000d42148000000002106000d4104800000004110500016104814004508120000054304800003100a20100115200800000000a1050000002843c000000210000000008404000000a10a0000003841400324c8200000d42148000000006101
  | 6, 1, 5 => 0x8404000280e2000000004843c000280e20000000018430000000a10f00000028414000000a10f00000038414000000e10c30054304c00000000a10000006028800000000e10f00000008418000004010030054304c00002048020000115200800000180a20000000038428000000e10c0000e048800000381220000000038414000000e10500000018430000001210f0010403880000000c4101000000284280000006100
  | 6, 1, 6 => 0x16104814000000610a00000310404000000a1050000001842800000021000000003843c004548020000000038430000000210600000018418000000a10a00000038414000000610a00000028414000000e10f000d4214800000001210f000d420480000000411050000004843c000001210100104028800000000e10c00000028428000000e10a0000004841400304c02000000000840400000411050000003843c000000610c
  | 6, 1, 7 => 0x109420800000000a1000000000841800000121050000002840000000c410100000038430000281220000000038400001508120000054304800000010410000054048800000000e10600041048814000000610c00054404800002510120000000038414000000210100006038800004100a20000006038800000001210100000028428000001210000000048400000000e10f00109420800000000e10f00000028404000000610c
  | 6, 1, 8 => 0x3508520000000028404000001210f100d4104c00000000a10500006048800000181220000002038800000004110f00109420800000000e10600000038400000000e10c00000008430000000210000000028418000000210a0000004843c00001041000004102881400000c410100109420800000000e10a00000048414000000a1060000002843c000001210100000038414000000a101
  | 7, 0, 0 => 0x1840000000411050000002841400000121050010d430800000001210000000048400000080a200000d421480000000841000000003840400000061010000032440000001081000000002840000000c410100000404400000001210f00000028404000000610f0000020040000000021010000002843c000000a10a00000424400000000e1000000003840000000411050000003843c000000a10a00000028414000000210c
  | 7, 0, 1 => 0x31040400314c420000006048800000000210a00000038400000000210f0000a038800000180e20000000018400000001210000000038404000000e10100000038400000004110500000310400000080620000000310404000000e10f00000404400000000a105000d4214800002048020000000018400000001210100000038400000000e1000000004840000000061050000004843c000001210500000008400000000a10c
  | 7, 0, 2 => 0x28414000004110500000028400000000e10f0000002841400000c41000000031040000000021000000002843000000c81000000004843c000000a100000c932080000000061010000003841400000c410100000048400002148420000000028400000010410000000048404000000210a00000420400000000e10f0000004843c00000c410000000048400000000610f00000038428000000a1010000002843c00000c4101
  | 7, 0, 3 => 0x18400000000a10f00000018428000004110500000038418000000e10100000008400000000e10f00006028800000010d10000000008404000000e1000000003841800000121050000003842800038122000000002840000350852000000000843c000000e10c0000010441400000021000000003840000008062000000002843c000000610000000018400000001210f00000008400000000610500000028404000000610f
  | 7, 0, 4 => 0x3841400324c820000000018400000010410000000008418000000210000000424400000000a10a00000400400000001210000000304400000000610f0010541080000000121000000003843c000000a10c0000003843c000000a10000000048400000004110f00000048414000010410000000008404000004110f00000304400000000610500000048400000001210f0000003843c000000a100000000084000000040100
  | 7, 0, 5 => 0x43040000000021010000002841800000121050000010443c000004010000000048400000000a1060000002843c00000c010000000018428000000a1010000a03880000000c810000000008414000080e20000000018430000001210100104028800004250820000002048800000001210100000038400000000a10500000018404000008010000000008400000001210f000003204000000041105000004304000000002100
  | 7, 0, 6 => 0x4843c000001210500000310404000281220000000048404000000610500000028400000000a10000000048414000010910000000048400000000a10000000008404000008410000000008428000001210000000028400000001210f0000031040000104402000000004840400001001000000021040000000c410000000018400000000e100000001004000000012105000001004000000080100000000384280003812200
  | 7, 0, 7 => 0x18428000000e1060000a03880000001001000000004843c000010910000000028414000000e10100114104800000000e10000000028400000000e10000002048800000000210500000028404000000e10000115200800000000a1000000010443c00000121000000010443c000000a10100000048404000080a2000000002840400000411050000003841400000021010000004840000000c910000000310400000000a10f
  | 7, 0, 8 => 0x8400000000a10100000028414000004110500000048404000008110000000048414000000610000000018400000000a10100000048414000000a10500000320400000000a10c0000040040000001041000000000843c000000e1000000010443c000000e10a00000038404000000a10100000038414000001210f00000038414000000210000000310400000000a10500000048400000000210000000310400000000e100
  | 7, 0, 9 => 0x3841400000021000000002842800150c12000000004843c000010c10000002038800004548020000000048404000080a20000000048400000001210000000320400004250820000000008400000000e10000000048414000000a1000000042440000001081000000002840400000021000000002843c00000021000000010443c00000c410100000018428000010c1000000003843c00000801000000010443c000000e100
  | 7, 0, 10 => 0x10443c000001210100000038400000000e10500000410400000000e10600000018400000000610f000c1300800000000a10000000018404000001210f00000018404000000610000000018428000010c10000000008404000004110f0000003843c000000e10100000410400000000210f0000a048800000000a10f000000384000000006106000000184000000012100000d41048000000040100000000184000000006100
  | 7, 0, 11 => 0x38400000001210f0000003843c000000a10000000038414000000a10000000410400000001210500000048404000010410000000028414000000a1050000002841400050852000000030040000000121000010942080000000801000000000841800000061000000032440000314c420000000424400000000e1060000001843c000000a101000000284140000041105000000484140000080100000000384000000080100
  | 7, 0, 12 => 0x3841400001081000000030040000000c41000000040440000000c410000000104414000000a10500000048414000000a10100000048400000001210000000028418000180e2000001431480000000061000000003843000000021000000041040000018122000000040440000000061050000003843c00000021010000004840400001011000000004843c00001011000000002843c000000e100000c5310800000000e10f
  | 7, 0, 13 => 0x101400800000000a1010000004841400251012000000003840000000411050000001843c000000e10f00000008418000004110500000008430004508120000000028414000000210000000028404000000a100000d410480000000021000000001841400000c81000000002842800000121000000002840000000121010000001840000000c410000000434400000000e10c0000004840000000c4100000000284180020480200
  | 7, 0, 14 => 0x18430000000a10000000424400000000e10000000038430000000e10a00000300400000008010000006048800000000a10500000028400000000210100000018400000000210000041100800000001210500000028400000000210c0000010443c000000610c00000048414000000210000006028800000004110500002018800000010c1000000001843c000280e20000014214800000000a100000002004000000041105
  | 7, 0, 15 => 0x310404000000610600000008428000000a10100000028400000000a10000000210400000010810000000028414000000e10f00000038414000000210500000210400000000a10f0000004843c00000c11000000000840400405002000000003841400000401000000003842800001081000000002840400000c11000000010443c0000012100000000484000000002105000000384000000104100000000384300000081100
  | 7, 1, 0 => 0x38430000000e10000006028800000001210100000048404000001210000000018404000004110500000100400000000610000000048414000000a105000002104000000104100000d4214800000001210f00000028414000001210500000400400000000610000000038404000004110f00000210400000001210000000048400004050020000041100800000000610000000028414000000e1010000000843c000080a200
  | 7, 1, 1 => 0x48404000001210f000c9320800000000e10c00000048414000000e1010000004841400001041000000002843c00000121000000003843c000001210f0000000843c000010410000000018428004150420000000018404000010d10000000038404000001210000000028400000000a100000c1300800000000610c0000001842800214842000000003840400000021000000604880000000061000000603880000050c5200
  | 7, 1, 2 => 0x30040000000061050000001840000000121050000001843c00038122000000000841400000121000000002840000000411050000602880000000c41000000002840400000c410000000028404004350c20000000028400000001210000094104800000000210000000310400000000a1050000003843c000004110f00000038414000000a10c00000018400000004110500000028400000001210f00000028400000000a10f
  | 7, 1, 3 => 0x38400000000210a000d4404800000000a10100000210400000000210f00000038428000010810000000420400000000a10c0000001843c000000610c00000028414000004110500000038430000001210500000028414000000a10500000104414000000610000000038400000000e10500000028400000008110000000018414000000e10500000310404000000e10500000400400000010010000000018404000000210f
  | 7, 1, 4 => 0x840400000801000000a048800000000e1000000003840000350852000000002843c000000e10000002048800000000210f0000000841400000061000000010443c00000401000000001840000000c41010000004841400000841000000002841800000121000005430480000000411050000003840400001041000000004840000000c81000000042440000000121050000003841400000021000000003843c000004110f
  | 7, 1, 5 => 0x18428000010410000000430400000000210f00000028414000000610c00000008400000010910000000424400000000e10f0000040040000000121000000002842800000c41010000041040000425082000000002843c000000210000000018414000000a1010000003840000000061050000002843c000001210100000008400000000a10000000028404000000a1000000043040000000061000000a038800000000a100
  | 7, 1, 6 => 0x1840000000021000000003840000150c120000000048400000000e10500000104414000080a2000000040440000000411050010d430800000001210000000018418000001210500000028414000000210f00000410400000000e10600000028404000000a105000c9320800000000210100000104414000001210000000300400000001210500000100400000000610500000410400000000e10500000038400000001210f
  | 7, 1, 7 => 0x3843c00250c520000000018414000000e10c00000310400000000210000000008418002048020000000048404000000610f00000028428000000610100085210800000010110000000410400000000210600000038414000000e10100054304800000000e1000000004843c000000210a00000048400000000e1010000e048800000281220000006028800000000a100000003104040000012101000000484000000012100
  | 7, 1, 8 => 0x28428000001210100000028400000000610000002048800000000610100000018404000000a10000000200400000000a1000000004840000000c41000000010443c000008110000000310400000000a1000000004843c000000a1050000001843c000000610100000028428000000a10000000038414000000610100000048400000000a1060000001840000001041000000002843c00000c41000000004843c0000002100
  | 7, 1, 9 => 0x104414000000210500000018404000000610c0000002843c000000e10000000008414000010410000105410800000000e10000000028404000000e1050000030040000000841000000030040000000121010000004840000000411050000004843c00000061010000003843c000000210a0000002840000000021010000a03880000000c810000000018414000000210000000008404000001210500000028404000000e10a
  | 7, 1, 10 => 0x18404000001210000000018400000000a1000000002843c00000411050010942080000304c02000000032040000000121010000003843c000010810000000104414000000e1060000021040000000411050000021040000000c11000000000843c000000e1000000002840000000801000000021040000324c82000000001840000000411050000003843c000000610100000430400000000a10f000000484000000012105
  | 7, 1, 11 => 0x8400000000e10500000038400000004110f00000028400000001210000000018404000001210f00000028404000000a10f00041100800000010910000000028400000001210500000018414000000e10500014214800000000e10f0000004843c00001001000000002843c000000e10000000028414000004010000000018428000001210000000200400000010c1000000202880000000121000000000843c0000012105
  | 7, 1, 12 => 0x2841400000c01000000603880000050c52000000010441400000121010000010443c00000061000010140080000000061060000001840000000121000000010441400000121010000002841800001081000000003840400454062000000030040000000121010000000843c000001210100000410400000000a1000000003843c000000a1000000002841400000c410100006048800000004110f00000028430000001210f
  | 7, 1, 13 => 0x3843c00000061000000032440000000061000000a048800000000a1000000003843c00000c410000000410400000001210f00000410400000000210a00000008400000000610c00000048414000001210000000104414000000e10f0000021440000000c110000000048404000000e10f00000048400000000a10000000018400000000210000000310404000000a1010000004843c000000a100000000384180000100100
  | 7, 1, 14 => 0x4840400454802000000002843c000001210500000424400000001210000000008414000000a10100000038404000001210f00000008404000000210600002018800000000a10500000008400000000a10000000038400004508520000000430400000001210000000038414000000e1000000000843c000000e10000000028404000004110f00000028404000000a10f00000018400000000a10c00006028800000000a10f
  | 7, 1, 15 => 0x38400000008410000000424400000000210100000038400000000e1010000000843c00000121010000002843c000008010000000038414000008010000000008414000000a1050000003843c000000e10000000104414000000210100000048404000001210100000028400000001210500000028404000000a100000d4104800000000a100000000484140000041105000000184000000041105000000284180000002106
  | 7, 2, 0 => 0x38418000000a10000000028414000001210000000028400000000a10100000038400000000a10500000038400000010c100000d4214800000000a1000000010443c000000a1000000003843c000000e10000000038400000000610000000038404000001210100000018404000000610000000028400000008410000000048404000000e1050000010443c000001210f000060488000000002100000000484000000006100
  | 7, 2, 1 => 0x1841400000121010000000841400000c01000000041040000000411050000000840000000121050000003843000000c410000000028404000010910000000008400000000e10500000028400000001210f00000424400000000a1010000043040000000061060000001843c000000a10100000028404000000e1000010d430800000001210100000400400000000e10500000048400000001210f000000084040000104100
  | 7, 2, 2 => 0x8430000000a10f00000048414000001210000000028430000000a10c00016410800000000210000000008414000000a1010000041040000000c81000000002843c00000021050000010441400000021000000002843c000000e10600000008428000000a10100000320400002148420000000018400000000e1010000003843c000180a20000000018400000001210f00000028400000000e10000081200800000001210f
  | 7, 2, 3 => 0x320400000001210100000018430000004110f00000434400004350c20000000420400000000e10f0000003840000000121000000004840400000061050000010443c000000e10c00000204400000000a10500000310400000001210500000028404000000a1000000e048800000000e10f00000008400000000a106000000284000000041105000000184000000012100000000484140000104100000000384180000012100
  | 7, 2, 4 => 0x38400000000a1010000000843c00000c81000010541080000000c11000000a048800000000a1060000004843c000010910000000018404000010c10000000048400000000e10f00000048400000000a10a00000028400000010c11400000018400000001210100000048404000001210000000038414000004110f00000028404000004110500054304800000000e10c00000038414000000e1060000003840400000c8100
  | 7, 2, 5 => 0x2840000000121000000030040000000c010000000018430000000e1000000020040000000061010000a038800000000e1050000041040000000c010000000008400000000a10000000028414000000210000002048800000000a10600000028400000000e10a00000038400000008010000000430400000000e10a00000038400000000a10500085210800000000210100000018400000001210f0000010443c0000012100
  | 7, 2, 6 => 0x8400000010810000000310400000008410000000008400000000e10f00000420400000004110f00000048414000000a1000000002840000000841000000004843c000000210000000420400000000a10100000210400000008410000000018430000000210a0000000841400000401000000002843c000004010000000100400000001210100000028400000000a10100000008414000000e105000001044140000012105
  | 7, 2, 7 => 0x18400000000e10f0000003843c000004110500000424400000010c10000000018400000010810000000104414000000610c00000028400000000a10000000300400000000e10a00002028800000000e10c00000018428000001210500105410800000000a10f00000048404000001210000000324400000001210f00000008400000001210100000048400000000e10000000048400000000e10f00000028400000000e101
  | 7, 2, 8 => 0x1421480000000c81000000032440000001041000005430480000000401000000001843c00000021050000002841400000411050000003843c00000c410100115300800000000e10600000008430000000e105000c1300800000000e10a00000048404000001210500000310400000000e10000000038400000001210000000400400000000e1050000010443c000000a10500000028400000000610f00000038400000001210f
  | 7, 2, 9 => 0x8400000001210100000210400000000210000000018400000004110f00000310404000000e10500000410400000001210f0000000840000000121000000004840000000061000000004843c000000610a00000008428000000610c00000048404000000610000054404800000000610100000028404000000a10000000008400000000a10f0000002843c000000a1010000a048800000000a100000411008000000002105
  | 7, 2, 10 => 0x4840000425082000000003840000000121000000010443c00000061000000000840000000021060000010443c000000e10000000038414000000210f0000002843000000c410100000038414000000a106000d4104800000004110f00000018400000000610a0000001840000405002000000002843c000000a10500000038404000000e10f000000284000000006100001152008000000006105000000184040000012100
  | 7, 2, 11 => 0x410400000000a1000000002843c00000c410100000104414000000e10000000200400000000e1000000003840000150122000000003843c000000e10c00000424400000000e10f00000048414000000610000000048400000000210100000210400000010d1000000003843c000000a10500000028414000004110500000038400000000a10100000028430000000a100000004244000000012101000020388000000012105
  | 7, 2, 12 => 0x300400000000a10500000300400000508520000000008400000000a10000000028400000000210f0000010443c000000610100000410400000010910000000008400003504120000006048800000000e10f0000000843c00000c81000000032040000000121000000003841400454802000000010443c000000e10100000204400000000a10100000048404000000a1000000000840400001041000000032440000450c5200
  | 7, 2, 13 => 0x48414000001210500000310404000000a1010000002840400000121000000004840000000c41000000041040000000c110000000018400000000610f0000010443c000000e10c00000430400000000610c00000008400000001210f00000038404000000a10500000008400000004010000000028400000000210000000104414000000210000000038404000004110500000310400000000610100000028404000010d100
  | 7, 2, 14 => 0x48414000000210a00000038414000000210500000028400000000a1000000004840000000121050000002843c000080e2000000000840000000c010000000320400000000e10000000320400000001210500000008418000010410000000434400000000a10500000410400000000e1000000003840000000c41010000004843c000180a200000000484040040500200000000284180000012100000000484040000006105
  | 7, 2, 15 => 0x28414000000a10000000028400000001210100000018400000000210f0000041040000000121000000001840400000121000000042440000001081000000003840000000801000000002843c000000610c00000314400000001210000000204400000000e10500000008400000000e10f0008120080000000c41010000000843c00000811000000031040400000c01000000004843c000004010000000104414000010c100
  | 7, 3, 0 => 0x10d430800000000a10000000048400000008410000000038400000008410000000420400000000a10500000018414000001210500000008404000000610000000018400000000e10a0000003841800000411050000004840000000021010000030040000000121000000004843c000000210100000028400000000a1010000004840000000121010000001843c000000210f000000284000000012100000001004000000012105
  | 7, 3, 1 => 0x28400000000a10000000008400000000e10000000028414000001210100002038800000001210000000048404000000a1000000043440000000021050000004840000000c410100000028400000000210000000028404000000e1010000000840400000021000000001843c000004110f0000010441400314c42000000003840000000121050000003843c000000610500000420400000000a105000000084180000084100
  | 7, 3, 2 => 0x2840000000c110000000028414000004110500000018404000000a10100000038404000000610000000008400000010910000000028418000000e10000000310400000000e10000000420400000000a10000000048404000000a10000000028428000000610f0000003843c000000e10c00000038430000001210100000424400000000a1000000603880000000811000000002840400050c52000008521080000324c8200
  | 7, 3, 3 => 0x18400000000210a00000410400000008010000000028428000080620000000404400000000a10100000028430004100e20000000028400000000e10a00000028404000000610000000008400000000210000000008404000000210100000310404000001210500000008400000001210100000008428000000a10500000018418000004010000000300400000000e1000000004840400000021000000001843c0000006105
  | 7, 3, 4 => 0x38400000004110500000038414000001210000000038400000000a10f0000002843c00028122000000004841400000021010000001840400000061000000001840000000121000000041040000000021010000003840000150c12000000042040000000c810000000048400000000a10100000018430000000610c00000410400000000210000000100400000000610100000320400000001210f001054108000000012100
  | 7, 3, 5 => 0x430400001044020000054204800000000a1000000002843c000000210f00000018428000000e1010000010443c00000401000010942080000410022000000002843c000000210100081200800000000a1050000003843c000008410000000028404000000210f0010d43080000000411050000041040000000021060000e048800000001210f0000040440000000021000000004840000304c020000000310404000000a101
  | 7, 3, 6 => 0x48414000000e10500002048800000000a10f00115018800000000210500000028400000000210000000028414000000210000000320400000000610600000008418000000a10000000038414000000a1000000000843c000008010000000038404000000e10f00000100400000001210000000008404000000e10000000420400000001210100000028400003508520000000404400000001210f000000384000000012100
  | 7, 3, 7 => 0x28400000000a10100000008428000080e2000000003843c000010910000000018400000010010000000048404004250820000000008400000000e100000020188000000041105000000284300000002100000c9320800000000e1000000000843000001041000000010443c000000e1050000010443c000000a10c00000048414000000e10f000000484000000104100000d42048000000012100000000384180000002106
  | 7, 3, 8 => 0x8400000000e10100000038414004548020000000028400000010410000000048404000000a1000000010443c000000a10600000028414000180e20000000414400000508520000114304800000000a1050000002842800000c41000000010441400001011000000001843c00050c520000000018400000000a10f0000e04880000000c410000000008400000000210f00000048414000010c100000000084040000006105
  | 7, 3, 9 => 0x38400000000610100002048800000000e10500000028414000000e1000000002843c000000210000101400800000001210000000204400000000e10000000100400000000a101000000384280000006100000000384140000040100000004004000000104100000000484000000002100000000384180000012105000d4104800000000e10c00000048414000001210100000104414000000210f000c1300800000000a105
  | 7, 3, 10 => 0x2843c000001210100000018400000001210f0000004843c000000e10500000028404000001210000000028414000004110500000430400000000210c00000048414000000210500000430400000001210000000048400000000210a0000001840000000411050000010443c00000121010000031040400000c810000000048404000280e20000000320400000001210000000048400000000e10c0000001843c0000108100
  | 7, 3, 11 => 0x28400000000610c0000010443c000080a2000000003840000000841000000002840000000021060000031040000314c420000000008430000001210000000038414000008010000000310400000000e10100054048800000000610a0000004843c000000610f00085210800000000210000000018404000000e10000000028400000000a10600000028414000004110500000048400000000610c00000048414000000a105
  | 7, 3, 12 => 0x28414000000a10c0000002840400000021000000004843c000000210f0000032440000001081000000003843c000000e10f0000000843c000000210500000400400000000a10500000018428000000210100000038400000000e10600000028414000000a10c00000018414000000a10000000028400000010010000000204400000001210500006038800000000210000104018800000000a101000812008000000100100
  | 7, 3, 13 => 0x48414000000210000000400400000000a10000000038414000000e1050000004841400314c42000000000840000001091000000010443c000004110f00006048800000081220000000038414000001210000000104414000008110000000100400000000e10f0000010040000350412000000000840400000061000000010441400000061050000000842800000c0100000000084040000041100000003204000045480200
  | 7, 3, 14 => 0x381220000105410800000180e20000014314800000000e10f0000010441400000c810000000038414000010410000000048400000001210f0000002841800250c120000000038414000000210100000008414000000a105
  | 8, 0, 0 => 0x10440000000c110000000008400000001210000000420400000000610000000210400000000a1000000010040000000801000000031440000000c110000000048400000010410000000018400000010d1000000020440000000c010000000104400000000210000000008400000010510000000028400000010910000000214400000010110000000028400000000e100000000484000000084100000004044000000081100
  | 8, 0, 1 => 0x324400000010010000000104400000008510000000320400000000a1000000040040000000121000000000840000000801000000020440000001041000000043040000000c810000000404400000000e1000000041440000000c41000000000840000000c91000000040440000001081000000043040000000c81000000003840000000061000000004840000000061000000010040000001041000000021440000000c0100
  | 8, 0, 2 => 0x38400000010810000000008400000010110000000210400000004110000000310400000010c1000000041440000000c810000000048400000000e10000000200400000010c1000000031440000000401000000043440000000c410000000304400000000610000000008400000010910000000028400000001210000000038400000004010000000214400000010d1000000041040000000c11000000001840000000c0100
  | 8, 0, 3 => 0x48400000010d10000000100400000001210000000008400000008010000000314400000008110000000304400000010910000000018400000010d10000000028400000010510000000038400000000210000000214400000001210000000424400000000210000000028400000000e1000000041040000000c91000000040440000001001000000001840000000c01000000031040000000c9100000000084000000100100
  | 8, 0, 4 => 0x28400000010510000000038400000010c10000000048400000004010000000320400000000e1000000020440000000061000000041440000000c91000000000840000000c410000000400400000000610000000404400000000a1000000001840000001041000000030440000001081000000021040000000c4100000003004000000041100000000284000000080100000003144000000085100000004204000000084100
  | 8, 0, 5 => 0x31440000000c410000000048400000008110000000434400000010910000000410400000000210000000038400000010810000000210400000010910000000300400000004110000000028400000000e10000000028400000008010000000314400000010410000000314400000010d1000000030040000000411000000004840000000851000000002840000000021000000020440000000c9100000004244000000100100
  | 8, 0, 6 => 0x1051000000001840000000c91000000043040000000c810000000400400000000e10000000048400000004010000000028400000010c100000003204000000108100000000384000000084100000003044000000006100000000184000000080100
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 12 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_x0_0 roots_x0_0 8 s ws hint
  | 1 => checkCutEntry dom_x1_0 roots_x1_0 7 s ws hint
  | 2 => checkCutEntry dom_x0_0_x1_1_x5_0 roots_x0_0_x1_1_x5_0 4 s ws hint
  | 3 => checkCutEntry dom_x0_0_x3_1 roots_x0_0_x3_1 5 s ws hint
  | 4 => checkCutEntry dom_x0_0_x5_1 roots_x0_0_x5_1 5 s ws hint
  | 5 => checkCutEntry dom_x2_1 roots_x2_1 7 s ws hint
  | 6 => checkCutEntry dom_x1_0_x4_1 roots_x1_0_x4_1 6 s ws hint
  | 7 => checkCutEntry dom_x0_0_x3_1_x5_1 roots_x0_0_x3_1_x5_1 4 s ws hint
  | 8 => checkCutEntry dom_x1_1_x5_0 roots_x1_1_x5_0 5 s ws hint
  | 9 => checkCutEntry dom_x0_0_x4_1_x5_1 roots_x0_0_x4_1_x5_1 4 s ws hint
  | 10 => checkCutEntry dom_x0_0_x2_1 roots_x0_0_x2_1 6 s ws hint
  | 11 => checkCutEntry dom_x0_0_x1_1 roots_x0_0_x1_1 5 s ws hint
  | 12 => checkCutEntry dom_x1_0_x2_1 roots_x1_0_x2_1 6 s ws hint
  | 13 => checkCutEntry dom_x3_1_x5_1 roots_x3_1_x5_1 5 s ws hint
  | 14 => checkCutEntry dom_x4_1_x5_1 roots_x4_1_x5_1 5 s ws hint
  | 15 => checkCutEntry dom_x4_1 roots_x4_1 7 s ws hint
  | 16 => checkCutEntry dom_x3_1 roots_x3_1 6 s ws hint
  | 17 => checkCutEntry dom_x0_0_x5_0 roots_x0_0_x5_0 5 s ws hint
  | 18 => checkCutEntry dom_x5_0 roots_x5_0 6 s ws hint
  | 19 => checkCutEntry dom_x1_1 roots_x1_1 6 s ws hint
  | 20 => checkCutEntry dom_x5_1 roots_x5_1 6 s ws hint
  | 21 => checkCutEntry dom_x0_0_x4_1 roots_x0_0_x4_1 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_63 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x1_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x3_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x3_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x2_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x1_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x2_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_1 _ hc
  · contradiction
def p0Subs : List Nat := [5, 1, 15, 0, 12, 6, 16, 18, 19, 13, 20, 10, 8, 14, 17, 3, 4, 7, 9, 2, 11, 21]
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
private theorem z5 : ∀ i, 0 ≤ i → i < 51 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 51 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 64 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 64 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6_64 : ∀ i, 64 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 64 64 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6_128 : ∀ i, 128 ≤ i → i < 192 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 64 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6_192 : ∀ i, 192 ≤ i → i < 256 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 64 192 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6_256 : ∀ i, 256 ≤ i → i < 320 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 64 256 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6_320 : ∀ i, 320 ≤ i → i < 343 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 23 320 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 343 → Z 6 i = true := (range_split (range_split z6_0 (range_split z6_64 z6_128)) (range_split z6_192 (range_split z6_256 z6_320)))
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
private theorem z7_576 : ∀ i, 576 ≤ i → i < 640 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 576 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_640 : ∀ i, 640 ≤ i → i < 704 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 640 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_704 : ∀ i, 704 ≤ i → i < 768 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 704 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_768 : ∀ i, 768 ≤ i → i < 832 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 768 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_832 : ∀ i, 832 ≤ i → i < 896 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 832 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_896 : ∀ i, 896 ≤ i → i < 960 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 896 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_960 : ∀ i, 960 ≤ i → i < 1024 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 960 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_1024 : ∀ i, 1024 ≤ i → i < 1088 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 1024 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_1088 : ∀ i, 1088 ≤ i → i < 1152 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 1088 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_1152 : ∀ i, 1152 ≤ i → i < 1204 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 52 1152 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 1204 → Z 7 i = true := (range_split (range_split (range_split (range_split z7_0 z7_64) (range_split z7_128 z7_192)) (range_split (range_split z7_256 z7_320) (range_split z7_384 (range_split z7_448 z7_512)))) (range_split (range_split (range_split z7_576 z7_640) (range_split z7_704 (range_split z7_768 z7_832))) (range_split (range_split z7_896 z7_960) (range_split z7_1024 (range_split z7_1088 z7_1152)))))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_0 : ∀ i, 0 ≤ i → i < 64 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_64 : ∀ i, 64 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 64 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_128 : ∀ i, 128 ≤ i → i < 192 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_192 : ∀ i, 192 ≤ i → i < 256 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 192 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_256 : ∀ i, 256 ≤ i → i < 320 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 256 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_320 : ∀ i, 320 ≤ i → i < 384 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 320 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_384 : ∀ i, 384 ≤ i → i < 448 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 384 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_448 : ∀ i, 448 ≤ i → i < 512 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 448 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 512 → Z 8 i = true := (range_split (range_split (range_split z8_0 z8_64) (range_split z8_128 z8_192)) (range_split (range_split z8_256 z8_320) (range_split z8_384 z8_448)))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z9 : ∀ i, 0 ≤ i → i < 38 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 38 0 = true)
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

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 13]⟩], 16⟩
theorem wit_mono : PEqualNP.MetaComplexity.Monotone2 wit := by simp [wit, PEqualNP.MetaComplexity.Monotone2]
theorem wit_size : wit.size ≤ 11 := by decide
theorem wit_eval : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = ((fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4007717376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0))) x := by decide +kernel
theorem hT6 : ∀ r : Fin 64, goal_all.testBit r.val = ((fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4007717376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0))) (pt6 r.val) := by decide +kernel
theorem lower : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4007717376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) t → 11 ≤ t :=
  lower_to_circuit6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4007717376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) goal_all 11 hT6 (by unfold IsConst; decide) low_63

end PEqualNP.Outside.L_meta_40183_aux

theorem PEqualNP.Outside.L_meta_40183 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4007717376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4007717376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro s hs
  have hlb : 11 ≤ s := PEqualNP.Outside.L_meta_40183_aux.lower s hs
  exact ⟨PEqualNP.Outside.L_meta_40183_aux.wit, PEqualNP.Outside.L_meta_40183_aux.wit_mono, le_trans PEqualNP.Outside.L_meta_40183_aux.wit_size hlb, PEqualNP.Outside.L_meta_40183_aux.wit_eval⟩
