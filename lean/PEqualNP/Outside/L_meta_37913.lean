import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_37913_aux

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def mask256 : Nat := 2 ^ 256 - 1

def negD (d w : Nat) : Nat := (w ^^^ mask256) &&& d
def andD (d a b : Nat) : Nat := (a &&& b) &&& d
def orD (d a b : Nat) : Nat := (a ||| b) &&& d
def opD (d : Nat) (op : Nat) (a b : Nat) : Nat :=
  if op == 0 then andD d a b
  else if op == 1 then orD d a b
  else if op == 2 then andD d a (negD d b)
  else andD d (negD d a) b

def allowedB (u : Bool) (op : Nat) : Bool :=
  decide (op < 2) || (u && decide (op < 4))

def flipOp (op : Nat) : Nat :=
  if op == 2 then 3 else if op == 3 then 2 else op

def nrmD (u : Bool) (d w : Nat) : Nat :=
  if u && w.testBit 0 then negD d w else w &&& d

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

def RunD (u : Bool) (d y : Nat) (t : ℕ) (ws : List Nat) : Prop :=
  ∀ P : ℕ → List Nat → Prop, P 0 [y] →
    (∀ {s xs zs}, List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a b r} (op : Nat) (ka kb : Bool),
      allowedB u op = true →
      opD d op a b ≠ 0 →
      opD d op a b ≠ d →
      opD d op a b ∉ (a :: b :: r) →
      P s (opD d op a b :: kept ka a (kept kb b r)) →
      P (s + 1) (a :: b :: r)) → P t ws

section
variable {u : Bool} {d y : Nat}

theorem Run.done : RunD u d y 0 [y] := fun _ dn _ _ => dn
theorem Run.perm {s xs zs} (p : List.Perm xs zs) (h : RunD u d y s xs) :
    RunD u d y s zs := fun P dn q b => q p (h P dn q b)
theorem Run.two {s a b r} (op : Nat) (ka kb : Bool)
    (hop : allowedB u op = true)
    (h0 : opD d op a b ≠ 0) (hd : opD d op a b ≠ d) (hm : opD d op a b ∉ (a :: b :: r))
    (h : RunD u d y s (opD d op a b :: kept ka a (kept kb b r))) :
    RunD u d y (s + 1) (a :: b :: r) := fun P dn q v => v op ka kb hop h0 hd hm (h P dn q v)

theorem Run.fold {P : ∀ t ws, RunD u d y t ws → Prop}
    (done : P 0 [y] Run.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : RunD u d y s xs),
      P s xs h → P s zs (Run.perm hp h))
    (two : ∀ {s a b r} (op : Nat) (ka kb : Bool)
      (hop : allowedB u op = true)
      (h0 : opD d op a b ≠ 0) (hd : opD d op a b ≠ d) (hm : opD d op a b ∉ (a :: b :: r))
      (h : RunD u d y s (opD d op a b :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (Run.two op ka kb hop h0 hd hm h))
    {t ws} (h : RunD u d y t ws) : P t ws h := by
  have hex := h (fun s xs => ∃ h' : RunD u d y s xs, P s xs h')
    ⟨Run.done, done⟩
    (fun hp ⟨h', ih⟩ => ⟨Run.perm hp h', perm hp h' ih⟩)
    (fun op ka kb hop h0 hd hm ⟨h', ih⟩ => ⟨Run.two op ka kb hop h0 hd hm h', two op ka kb hop h0 hd hm h' ih⟩)
  exact hex.elim fun _ hp => hp
end

theorem allowed_cases {u : Bool} {op : Nat} (h : allowedB u op = true) :
    op = 0 ∨ op = 1 ∨ (u = true ∧ op = 2) ∨ (u = true ∧ op = 3) := by
  simp only [allowedB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h | ⟨hu, h⟩
  · omega
  · have : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl ⟨hu, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hu, rfl⟩))

theorem opD_comm {u : Bool} (d : Nat) {op : Nat} (hop : allowedB u op = true) (a b : Nat) :
    opD d op a b = opD d (flipOp op) b a := by
  rcases allowed_cases hop with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp [opD, flipOp, andD, orD, Nat.and_comm, Nat.or_comm]

theorem flipOp_allowed {u : Bool} {op : Nat} (hop : allowedB u op = true) :
    allowedB u (flipOp op) = true := by
  rcases allowed_cases hop with rfl | rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [allowedB, flipOp]

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

theorem run_len {u d y s xs} (h : RunD u d y s xs) :
    xs.length ≤ s + 1 := by
  induction h using Run.fold with
  | done => simp
  | perm hp _ ih => rwa [← hp.length_eq]
  | two _ ka kb _ _ _ _ _ ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

theorem zero_done {u d y t ws} (h : RunD u d y t ws) :
    t = 0 → ws = [y] := by
  induction h using Run.fold with
  | done => simp
  | perm p _ ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | two => simp

def IsConst (d w : Nat) : Prop := (w &&& d) = 0 ∨ (w &&& d) = d
def isConstB (d w : Nat) : Bool := (w &&& d == 0) || (w &&& d == d)

theorem isConstB_iff (d w : Nat) : isConstB d w = true ↔ IsConst d w := by
  simp [isConstB, IsConst]

def Avail (u : Bool) (d : Nat) (bank : List Nat) (w : Nat) : Prop :=
  IsConst d w ∨ (∃ v ∈ bank, (v &&& d) = (w &&& d)) ∨ (u = true ∧ ∃ v ∈ bank, (v &&& d) = negD d w)

def availB (u : Bool) (d : Nat) (bank : List Nat) (w : Nat) : Bool :=
  let m := w &&& d
  m == 0 || m == d || bank.any (fun v => (v &&& d) == m) ||
    (u && bank.any (fun v => (v &&& d) == negD d w))

theorem availB_iff (u : Bool) (d : Nat) (bank : List Nat) (w : Nat) :
    availB u d bank w = true ↔ Avail u d bank w := by
  simp [availB, Avail, IsConst, or_assoc]

def NatReach (u : Bool) (d : Nat) (roots : List Nat) : Nat → List Nat → Prop
  | 0, bank => bank = roots
  | p + 1, bank =>
    ∃ b a c op, allowedB u op = true ∧ bank = opD d op a c :: b ∧
      NatReach u d roots p b ∧ Avail u d b a ∧ Avail u d b c

def Lower (u : Bool) (d : Nat) (roots : List Nat) (T : Nat) (L : Nat) : Prop :=
  ∀ p bank, NatReach u d roots p bank → Avail u d bank T → L ≤ p

theorem avail_mono {d : Nat} {bank : List Nat} {w : Nat} (h : Avail false d bank w) :
    Avail true d bank w := by
  rcases h with h | h | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · contradiction

theorem reach_up {d : Nat} {roots : List Nat} {p bank} (h : NatReach false d roots p bank) :
    NatReach true d roots p bank := by
  induction p generalizing bank with
  | zero => exact h
  | succ p ih =>
    obtain ⟨b, a, c, op, hop, rfl, hrb, ha, hc⟩ := h
    have hop' : allowedB true op = true := by
      rcases allowed_cases hop with rfl | rfl | ⟨hc, _⟩ | ⟨hc, _⟩ <;> first | decide | contradiction
    exact ⟨b, a, c, op, hop', rfl, ih hrb, avail_mono ha, avail_mono hc⟩

theorem lower_down {d : Nat} {roots : List Nat} {T L : Nat} (h : Lower true d roots T L) :
    Lower false d roots T L := fun p bank hr ha => h p bank (reach_up hr) (avail_mono ha)

theorem mask256_bit (i : Nat) : mask256.testBit i = decide (i < 256) := by
  rw [mask256, Nat.testBit_two_pow_sub_one]

theorem opD_and_sub {d d1 : Nat} (hd : d &&& mask256 = d) (hsub : d &&& d1 = d) (op a b : Nat) :
    opD d1 op a b &&& d = opD d op a b := by
  apply Nat.eq_of_testBit_eq; intro i
  have h1 := congrArg (fun v => v.testBit i) hd
  have h2 := congrArg (fun v => v.testBit i) hsub
  unfold opD
  split_ifs <;> simp only [andD, orD, negD, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] at * <;>
    cases hi : d.testBit i <;> simp_all

theorem negD_invol {d : Nat} (hd : d &&& mask256 = d) (a : Nat) :
    negD d (negD d a) = a &&& d := by
  apply Nat.eq_of_testBit_eq; intro i
  have h1 := congrArg (fun v => v.testBit i) hd
  simp only [negD, Nat.testBit_and, Nat.testBit_xor] at *
  cases hi : d.testBit i <;> cases ha : a.testBit i <;> simp_all

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

theorem opD_mask_self (d op a b : Nat) : opD d op a b &&& d = opD d op a b := by
  apply Nat.eq_of_testBit_eq; intro i
  unfold opD; split_ifs <;> simp only [andD, orD, negD, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] <;>
    cases d.testBit i <;> simp

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

theorem avail_cons {u : Bool} {d : Nat} {bank : List Nat} (z w : Nat) (h : Avail u d bank w) :
    Avail u d (z :: bank) w := by
  rcases h with hc | ⟨v, hv, he⟩ | ⟨hu, v, hv, he⟩
  · exact Or.inl hc
  · exact Or.inr (Or.inl ⟨v, List.mem_cons_of_mem _ hv, he⟩)
  · exact Or.inr (Or.inr ⟨hu, v, List.mem_cons_of_mem _ hv, he⟩)

theorem avail_of_eq {u : Bool} {d : Nat} {bank : List Nat} {v w : Nat}
    (he : v &&& d = w &&& d) (h : Avail u d bank v) : Avail u d bank w := by
  rcases h with (h0 | h1) | ⟨x, hx, hxe⟩ | ⟨hu, x, hx, hxe⟩
  · exact Or.inl (Or.inl (he.symm.trans h0))
  · exact Or.inl (Or.inr (he.symm.trans h1))
  · exact Or.inr (Or.inl ⟨x, hx, hxe.trans he⟩)
  · exact Or.inr (Or.inr ⟨hu, x, hx, hxe.trans (by rw [← negD_mask, he, negD_mask])⟩)

theorem avail_neg {d : Nat} (hd : d &&& mask256 = d) {bank : List Nat} {w : Nat}
    (h : Avail true d bank w) : Avail true d bank (negD d w) := by
  rcases h with hc | ⟨v, hv, he⟩ | ⟨_, v, hv, he⟩
  · exact Or.inl (negD_const hd hc)
  · refine Or.inr (Or.inr ⟨rfl, v, hv, ?_⟩)
    rw [negD_invol hd, he]
  · refine Or.inr (Or.inl ⟨v, hv, ?_⟩)
    rw [he]; simp [negD, Nat.and_assoc, Nat.and_self]

theorem opD_const_left {u : Bool} {d : Nat} (hd : d &&& mask256 = d) {op : Nat}
    (hop : allowedB u op = true) {a b : Nat} (hc : IsConst d a) :
    (opD d op a b &&& d = 0) ∨ (opD d op a b &&& d = d) ∨
      (opD d op a b &&& d = b &&& d) ∨ (u = true ∧ opD d op a b &&& d = negD d b) := by
  rcases allowed_cases hop with rfl | rfl | ⟨hu, rfl⟩ | ⟨hu, rfl⟩
  · rcases hc with h0 | h1
    · left; apply Nat.eq_of_testBit_eq; intro i
      have h0i := congrArg (fun v => v.testBit i) h0
      simp only [opD, andD, Nat.testBit_and, Nat.zero_testBit, beq_self_eq_true, ite_true] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
    · right; right; left; apply Nat.eq_of_testBit_eq; intro i
      have h1i := congrArg (fun v => v.testBit i) h1
      simp only [opD, andD, Nat.testBit_and, beq_self_eq_true, ite_true] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · rcases hc with h0 | h1
    · right; right; left; apply Nat.eq_of_testBit_eq; intro i
      have h0i := congrArg (fun v => v.testBit i) h0
      simp only [opD, orD, Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit, beq_self_eq_true, ite_true, ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
    · right; left; apply Nat.eq_of_testBit_eq; intro i
      have h1i := congrArg (fun v => v.testBit i) h1
      simp only [opD, orD, Nat.testBit_and, Nat.testBit_or, beq_self_eq_true, ite_true, ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · rcases hc with h0 | h1
    · left; apply Nat.eq_of_testBit_eq; intro i
      have h0i := congrArg (fun v => v.testBit i) h0
      simp only [opD, andD, negD, Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit, beq_self_eq_true, ite_true, ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
    · right; right; right; refine ⟨hu, ?_⟩
      apply Nat.eq_of_testBit_eq; intro i
      have h1i := congrArg (fun v => v.testBit i) h1
      have hdi := congrArg (fun v => v.testBit i) hd
      simp only [opD, andD, negD, Nat.testBit_and, Nat.testBit_xor, beq_self_eq_true, ite_true, ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · rcases hc with h0 | h1
    · right; right; left; apply Nat.eq_of_testBit_eq; intro i
      have h0i := congrArg (fun v => v.testBit i) h0
      have hdi := congrArg (fun v => v.testBit i) hd
      simp only [opD, andD, negD, Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit, beq_self_eq_true, ite_true, ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
    · left; apply Nat.eq_of_testBit_eq; intro i
      have h1i := congrArg (fun v => v.testBit i) h1
      have hdi := congrArg (fun v => v.testBit i) hd
      simp only [opD, andD, negD, Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit, beq_self_eq_true, ite_true, ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all

theorem countP_kept_ge {α : Type} (p : α → Bool) (b : Bool) (a : α) (xs : List α) :
    xs.countP p ≤ (kept b a xs).countP p := by
  cases b <;> simp [kept, List.countP_cons] <;> split <;> omega

theorem contraction {u : Bool} {d d1 T : Nat} (hd : d &&& mask256 = d) (hsub : d &&& d1 = d)
    (hnc : ¬ IsConst d T) {s ws} (h : RunD u d1 T s ws) {roots p bank}
    (hp : NatReach u d roots p bank) (hs : ∀ w ∈ ws, Avail u d bank w) :
    ∃ q next, NatReach u d roots q next ∧ Avail u d next T ∧
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
  | @two s a b r op ka kb hop _ _ _ _ ih =>
    have ha := hs a List.mem_cons_self
    have hb := hs b (List.mem_cons_of_mem _ List.mem_cons_self)
    set z1 := opD d1 op a b
    set z0 := opD d op a b
    have hz_eq : z1 &&& d = z0 &&& d := by
      rw [opD_and_sub hd hsub, opD_mask_self]
    by_cases hcab : IsConst d a ∨ IsConst d b
    · have hz_av : Avail u d bank z1 := by
        apply avail_of_eq hz_eq.symm
        rcases hcab with hca | hcb
        · rcases opD_const_left hd hop hca with h0 | h1 | he | ⟨rfl, hn⟩
          · exact Or.inl (Or.inl h0)
          · exact Or.inl (Or.inr h1)
          · exact avail_of_eq he.symm hb
          · exact avail_of_eq (by rw [hn]; simp [negD, Nat.and_assoc, Nat.and_self]) (avail_neg hd hb)
        · dsimp only [z0]; rw [opD_comm d hop a b]
          rcases opD_const_left hd (flipOp_allowed hop) hcb with h0 | h1 | he | ⟨rfl, hn⟩
          · exact Or.inl (Or.inl h0)
          · exact Or.inl (Or.inr h1)
          · exact avail_of_eq he.symm ha
          · exact avail_of_eq (by rw [hn]; simp [negD, Nat.and_assoc, Nat.and_self]) (avail_neg hd ha)
      have hs' : ∀ w ∈ z1 :: kept ka a (kept kb b r), Avail u d bank w := by
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
          rcases opD_const_left hd hop hca with h0 | h1 | he | ⟨_, hn⟩
          · have hz1 : isConstB d z1 = true := (isConstB_iff _ _).2 (Or.inl (hz_eq.trans h0))
            simp [ha1, hz1]; split <;> omega
          · have hz1 : isConstB d z1 = true := (isConstB_iff _ _).2 (Or.inr (hz_eq.trans h1))
            simp [ha1, hz1]; split <;> omega
          · have hzb : isConstB d z1 = isConstB d b := by simp only [isConstB, hz_eq.trans he]
            simp [ha1, hzb]
          · have hzb : isConstB d z1 = isConstB d b := by
              apply Bool.eq_iff_iff.2; rw [isConstB_iff, isConstB_iff]
              have hnm : negD d b &&& d = negD d b := by simp [negD, Nat.and_assoc, Nat.and_self]
              constructor
              · intro hz; have hnb : IsConst d (negD d b) := by
                  rcases hz with h0 | h1
                  · exact Or.inl (hnm.trans (hn.symm.trans (hz_eq.symm.trans h0)))
                  · exact Or.inr (hnm.trans (hn.symm.trans (hz_eq.symm.trans h1)))
                have h2 := negD_const hd hnb
                rw [negD_invol hd] at h2
                rcases h2 with e | e <;> [exact Or.inl (by simpa [Nat.and_assoc, Nat.and_self] using e); exact Or.inr (by simpa [Nat.and_assoc, Nat.and_self] using e)]
              · intro hb'; have hnb := negD_const hd hb'
                rcases hnb with h0 | h1
                · exact Or.inl (hz_eq.trans (hn.trans (hnm.symm.trans h0)))
                · exact Or.inr (hz_eq.trans (hn.trans (hnm.symm.trans h1)))
            simp [ha1, hzb]
        · have hb1 : isConstB d b = true := (isConstB_iff _ _).2 hcb
          have hz_eq' : z1 &&& d = opD d (flipOp op) b a &&& d := by rw [hz_eq]; dsimp only [z0]; rw [opD_comm d hop a b]
          rcases opD_const_left hd (flipOp_allowed hop) hcb with h0 | h1 | he | ⟨_, hn⟩
          · have hz1 : isConstB d z1 = true := (isConstB_iff _ _).2 (Or.inl (hz_eq'.trans h0))
            simp [hb1, hz1]; split <;> omega
          · have hz1 : isConstB d z1 = true := (isConstB_iff _ _).2 (Or.inr (hz_eq'.trans h1))
            simp [hb1, hz1]; split <;> omega
          · have hza : isConstB d z1 = isConstB d a := by simp only [isConstB, hz_eq'.trans he]
            simp [hb1, hza]
          · have hza : isConstB d z1 = isConstB d a := by
              apply Bool.eq_iff_iff.2; rw [isConstB_iff, isConstB_iff]
              have hnm : negD d a &&& d = negD d a := by simp [negD, Nat.and_assoc, Nat.and_self]
              constructor
              · intro hz; have hna : IsConst d (negD d a) := by
                  rcases hz with h0 | h1
                  · exact Or.inl (hnm.trans (hn.symm.trans (hz_eq'.symm.trans h0)))
                  · exact Or.inr (hnm.trans (hn.symm.trans (hz_eq'.symm.trans h1)))
                have h2 := negD_const hd hna
                rw [negD_invol hd] at h2
                rcases h2 with e | e <;> [exact Or.inl (by simpa [Nat.and_assoc, Nat.and_self] using e); exact Or.inr (by simpa [Nat.and_assoc, Nat.and_self] using e)]
              · intro ha'; have hna := negD_const hd ha'
                rcases hna with h0 | h1
                · exact Or.inl (hz_eq'.trans (hn.trans (hnm.symm.trans h0)))
                · exact Or.inr (hz_eq'.trans (hn.trans (hnm.symm.trans h1)))
            simp [hb1, hza]
      simp only [List.countP_cons] at hle ⊢
      exact ⟨q, next, hq, ht, by omega⟩
    · have hna : isConstB d a = false := by
        cases h : isConstB d a with | false => rfl | true => exact absurd (Or.inl ((isConstB_iff _ _).1 h)) hcab
      have hnb : isConstB d b = false := by
        cases h : isConstB d b with | false => rfl | true => exact absurd (Or.inr ((isConstB_iff _ _).1 h)) hcab
      have hreach' : NatReach u d roots (p + 1) (z0 :: bank) := ⟨bank, a, b, op, hop, rfl, hp, ha, hb⟩
      have hz_av : Avail u d (z0 :: bank) z1 := Or.inr (Or.inl ⟨z0, List.mem_cons_self, hz_eq.symm⟩)
      have hs' : ∀ w ∈ z1 :: kept ka a (kept kb b r), Avail u d (z0 :: bank) w := by
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

-- Normalization lemmas for backward extraction
theorem nrmD_mask (u : Bool) (d w : Nat) : nrmD u d w &&& d = nrmD u d w := by
  unfold nrmD; split <;> simp [negD, Nat.and_assoc, Nat.and_self]

theorem nrmD_of_bit0_false (u : Bool) (d w : Nat) (hw : w.testBit 0 = false) :
    nrmD u d w = w &&& d := by
  simp [nrmD, hw]

theorem nrmD_and_d {d : Nat} (hd0 : d.testBit 0 = true) (u : Bool) (w : Nat) :
    nrmD u d (w &&& d) = nrmD u d w := by
  unfold nrmD
  rw [Nat.testBit_and, hd0, Bool.and_true, negD_mask, Nat.and_assoc, Nat.and_self]

theorem nrmD_neg {d : Nat} (hd : d &&& mask256 = d) (hd0 : d.testBit 0 = true) (w : Nat) :
    nrmD true d (negD d w) = nrmD true d w := by
  have hm0 : mask256.testBit 0 = true := by decide
  unfold nrmD
  have hnb : (negD d w).testBit 0 = !w.testBit 0 := by
    simp only [negD, Nat.testBit_and, Nat.testBit_xor, hd0, hm0, Bool.and_true, Bool.xor_true]
  rw [hnb]
  cases hw : w.testBit 0
  · simp [negD_invol hd]
  · simp [negD, Nat.and_assoc, Nat.and_self]

theorem nrmD_const_iff {d : Nat} (hd : d &&& mask256 = d) (u : Bool) (w : Nat) :
    (nrmD u d w ≠ 0 ∧ nrmD u d w ≠ d) ↔ ¬ IsConst d w := by
  unfold nrmD
  have hnm : negD d w &&& d = negD d w := by simp [negD, Nat.and_assoc, Nat.and_self]
  split
  · constructor
    · rintro ⟨h0, h1⟩ hc
      rcases negD_const hd hc with hn0 | hn1
      · exact h0 (hnm.symm.trans hn0)
      · exact h1 (hnm.symm.trans hn1)
    · intro hnc; refine ⟨fun h0 => ?_, fun h1 => ?_⟩
      · have := negD_const hd (a := negD d w) (Or.inl (hnm.trans h0))
        rw [negD_invol hd] at this
        exact hnc (by rcases this with e | e <;> [exact Or.inl (by simpa [Nat.and_assoc, Nat.and_self] using e); exact Or.inr (by simpa [Nat.and_assoc, Nat.and_self] using e)])
      · have := negD_const hd (a := negD d w) (Or.inr (hnm.trans h1))
        rw [negD_invol hd] at this
        exact hnc (by rcases this with e | e <;> [exact Or.inl (by simpa [Nat.and_assoc, Nat.and_self] using e); exact Or.inr (by simpa [Nat.and_assoc, Nat.and_self] using e)])
  · simp [IsConst, not_or]

theorem opD_bit {d : Nat} (hd : d &&& mask256 = d) (op a b i : Nat) (hdi : d.testBit i = true) :
    (opD d op a b).testBit i =
      if op == 0 then a.testBit i && b.testBit i
      else if op == 1 then a.testBit i || b.testBit i
      else if op == 2 then a.testBit i && !(b.testBit i)
      else !(a.testBit i) && b.testBit i := by
  have hmi : mask256.testBit i = true := by
    have := congrArg (fun v => v.testBit i) hd; simp [Nat.testBit_and, hdi] at this; exact this
  unfold opD; split_ifs <;>
    simp only [andD, orD, negD, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, hdi, hmi, Bool.and_true, Bool.xor_true]

theorem nrmD_bit {d : Nat} (hd : d &&& mask256 = d) (w i : Nat) (hdi : d.testBit i = true) :
    (nrmD true d w).testBit i = if w.testBit 0 then !(w.testBit i) else w.testBit i := by
  have hmi : mask256.testBit i = true := by
    have := congrArg (fun v => v.testBit i) hd; simp [Nat.testBit_and, hdi] at this; exact this
  unfold nrmD
  cases hw0 : w.testBit 0 <;>
    simp only [hw0, Bool.true_and, Bool.and_false, Bool.false_eq_true, ite_true, ite_false,
      negD, Nat.testBit_and, Nat.testBit_xor, hdi, hmi, Bool.and_true, Bool.xor_true]

theorem nrmD_opD {d : Nat} (hd : d &&& mask256 = d) (hd0 : d.testBit 0 = true)
    (u : Bool) (op : Nat) (hop : allowedB u op = true) (a b : Nat) :
    ∃ op', allowedB u op' = true ∧
      nrmD u d (opD d op a b) = opD d op' (nrmD u d a) (nrmD u d b) := by
  cases u with
  | false =>
    rcases allowed_cases hop with rfl | rfl | ⟨h, _⟩ | ⟨h, _⟩
    · exact ⟨0, rfl, by
        apply Nat.eq_of_testBit_eq; intro i
        simp only [nrmD, opD, andD, Bool.false_and, Bool.false_eq_true, ite_false, beq_self_eq_true, ite_true, Nat.testBit_and]
        cases d.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1, rfl, by
        apply Nat.eq_of_testBit_eq; intro i
        simp only [nrmD, opD, orD, Bool.false_and, Bool.false_eq_true, ite_false]
        simp only [show (1 == 0) = false from rfl, show (1 == 1) = true from rfl, Bool.false_eq_true, ite_false, ite_true, Nat.testBit_and, Nat.testBit_or]
        cases d.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · contradiction
    · contradiction
  | true =>
    have h4 : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by
      rcases allowed_cases hop with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp
    have hbit : ∀ (e : Nat),
        (∀ i, d.testBit i = true →
          (nrmD true d (opD d op a b)).testBit i =
          (opD d e (nrmD true d a) (nrmD true d b)).testBit i) →
        nrmD true d (opD d op a b) = opD d e (nrmD true d a) (nrmD true d b) := by
      intro e h; apply Nat.eq_of_testBit_eq; intro i
      by_cases hdi : d.testBit i = true
      · exact h i hdi
      · have hf : d.testBit i = false := Bool.eq_false_iff.2 hdi
        have h1 := congrArg (fun v => v.testBit i) (nrmD_mask true d (opD d op a b))
        have h2 := congrArg (fun v => v.testBit i) (opD_mask_self d e (nrmD true d a) (nrmD true d b))
        simp only [Nat.testBit_and, hf, Bool.and_false] at h1 h2; exact h1.symm.trans h2
    rcases h4 with rfl | rfl | rfl | rfl <;>
      cases ha0 : a.testBit 0 <;> cases hb0 : b.testBit 0
    · exact ⟨0, by decide, hbit 0 fun i hdi => by rw [nrmD_bit hd _ i hdi, opD_bit hd _ _ _ 0 hd0, opD_bit hd _ _ _ i hdi, opD_bit hd _ _ _ i hdi, nrmD_bit hd a i hdi, nrmD_bit hd b i hdi, ha0, hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨2, by decide, hbit 2 fun i hdi => by rw [nrmD_bit hd _ i hdi, opD_bit hd _ _ _ 0 hd0, opD_bit hd _ _ _ i hdi, opD_bit hd _ _ _ i hdi, nrmD_bit hd a i hdi, nrmD_bit hd b i hdi, ha0, hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨3, by decide, hbit 3 fun i hdi => by rw [nrmD_bit hd _ i hdi, opD_bit hd _ _ _ 0 hd0, opD_bit hd _ _ _ i hdi, opD_bit hd _ _ _ i hdi, nrmD_bit hd a i hdi, nrmD_bit hd b i hdi, ha0, hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1, by decide, hbit 1 fun i hdi => by rw [nrmD_bit hd _ i hdi, opD_bit hd _ _ _ 0 hd0, opD_bit hd _ _ _ i hdi, opD_bit hd _ _ _ i hdi, nrmD_bit hd a i hdi, nrmD_bit hd b i hdi, ha0, hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1, by decide, hbit 1 fun i hdi => by rw [nrmD_bit hd _ i hdi, opD_bit hd _ _ _ 0 hd0, opD_bit hd _ _ _ i hdi, opD_bit hd _ _ _ i hdi, nrmD_bit hd a i hdi, nrmD_bit hd b i hdi, ha0, hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨3, by decide, hbit 3 fun i hdi => by rw [nrmD_bit hd _ i hdi, opD_bit hd _ _ _ 0 hd0, opD_bit hd _ _ _ i hdi, opD_bit hd _ _ _ i hdi, nrmD_bit hd a i hdi, nrmD_bit hd b i hdi, ha0, hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨2, by decide, hbit 2 fun i hdi => by rw [nrmD_bit hd _ i hdi, opD_bit hd _ _ _ 0 hd0, opD_bit hd _ _ _ i hdi, opD_bit hd _ _ _ i hdi, nrmD_bit hd a i hdi, nrmD_bit hd b i hdi, ha0, hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨0, by decide, hbit 0 fun i hdi => by rw [nrmD_bit hd _ i hdi, opD_bit hd _ _ _ 0 hd0, opD_bit hd _ _ _ i hdi, opD_bit hd _ _ _ i hdi, nrmD_bit hd a i hdi, nrmD_bit hd b i hdi, ha0, hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨2, by decide, hbit 2 fun i hdi => by rw [nrmD_bit hd _ i hdi, opD_bit hd _ _ _ 0 hd0, opD_bit hd _ _ _ i hdi, opD_bit hd _ _ _ i hdi, nrmD_bit hd a i hdi, nrmD_bit hd b i hdi, ha0, hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨0, by decide, hbit 0 fun i hdi => by rw [nrmD_bit hd _ i hdi, opD_bit hd _ _ _ 0 hd0, opD_bit hd _ _ _ i hdi, opD_bit hd _ _ _ i hdi, nrmD_bit hd a i hdi, nrmD_bit hd b i hdi, ha0, hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1, by decide, hbit 1 fun i hdi => by rw [nrmD_bit hd _ i hdi, opD_bit hd _ _ _ 0 hd0, opD_bit hd _ _ _ i hdi, opD_bit hd _ _ _ i hdi, nrmD_bit hd a i hdi, nrmD_bit hd b i hdi, ha0, hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨3, by decide, hbit 3 fun i hdi => by rw [nrmD_bit hd _ i hdi, opD_bit hd _ _ _ 0 hd0, opD_bit hd _ _ _ i hdi, opD_bit hd _ _ _ i hdi, nrmD_bit hd a i hdi, nrmD_bit hd b i hdi, ha0, hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨3, by decide, hbit 3 fun i hdi => by rw [nrmD_bit hd _ i hdi, opD_bit hd _ _ _ 0 hd0, opD_bit hd _ _ _ i hdi, opD_bit hd _ _ _ i hdi, nrmD_bit hd a i hdi, nrmD_bit hd b i hdi, ha0, hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1, by decide, hbit 1 fun i hdi => by rw [nrmD_bit hd _ i hdi, opD_bit hd _ _ _ 0 hd0, opD_bit hd _ _ _ i hdi, opD_bit hd _ _ _ i hdi, nrmD_bit hd a i hdi, nrmD_bit hd b i hdi, ha0, hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨0, by decide, hbit 0 fun i hdi => by rw [nrmD_bit hd _ i hdi, opD_bit hd _ _ _ 0 hd0, opD_bit hd _ _ _ i hdi, opD_bit hd _ _ _ i hdi, nrmD_bit hd a i hdi, nrmD_bit hd b i hdi, ha0, hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨2, by decide, hbit 2 fun i hdi => by rw [nrmD_bit hd _ i hdi, opD_bit hd _ _ _ 0 hd0, opD_bit hd _ _ _ i hdi, opD_bit hd _ _ _ i hdi, nrmD_bit hd a i hdi, nrmD_bit hd b i hdi, ha0, hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩

theorem avail_nrm_mem {u : Bool} {d : Nat} (hd : d &&& mask256 = d) (hd0 : d.testBit 0 = true)
    {b : List Nat} {w : Nat} (h : Avail u d b w) (hnc : ¬ IsConst d w) :
    nrmD u d w ∈ b.map (nrmD u d) := by
  rcases h with hc | ⟨v, hv, he⟩ | ⟨rfl, v, hv, he⟩
  · exact absurd hc hnc
  · refine List.mem_map.2 ⟨v, hv, ?_⟩
    rw [← nrmD_and_d hd0, he, nrmD_and_d hd0]
  · refine List.mem_map.2 ⟨v, hv, ?_⟩
    rw [← nrmD_and_d hd0, he, nrmD_neg hd hd0]

theorem pull_two {u : Bool} {d Y k ws} (hd : d &&& mask256 = d) (hd0 : d.testBit 0 = true)
    (hnd : ws.Nodup) (hprop : ∀ w ∈ ws, w ≠ 0 ∧ w ≠ d) (h : RunD u d Y k ws)
    {b : List Nat} {a c : Nat} (op : Nat) (hop : allowedB u op = true)
    (ha : Avail u d b a) (hc : Avail u d b c)
    (hsub : ∀ w ∈ ws, w ∈ nrmD u d (opD d op a c) :: b.map (nrmD u d)) :
    ∃ k' ws', k' ≤ k + 1 ∧ ws'.Nodup ∧ (∀ w ∈ ws', w ≠ 0 ∧ w ≠ d) ∧
      (∀ w ∈ ws', w ∈ b.map (nrmD u d)) ∧ RunD u d Y k' ws' := by
  set z := nrmD u d (opD d op a c)
  by_cases hzm : z ∈ ws
  · by_cases hzb : z ∈ b.map (nrmD u d)
    · exact ⟨k, ws, by omega, hnd, hprop, fun w hw => by
        rcases List.mem_cons.1 (hsub w hw) with rfl | hm
        · exact hzb
        · exact hm, h⟩
    · have hzp := hprop z hzm
      obtain ⟨op', hop', hez⟩ := nrmD_opD hd hd0 u op hop a c
      have ha_nc : ¬ IsConst d a := by
        intro hca
        have hznc : ¬ IsConst d (opD d op a c) := (nrmD_const_iff hd u _).1 hzp
        rcases opD_const_left hd hop hca with e0 | e1 | ec | ⟨rfl, en⟩
        · exact hznc (Or.inl e0)
        · exact hznc (Or.inr e1)
        · have hcn : ¬ IsConst d c := fun hcc => hznc (by rcases hcc with e | e <;> [exact Or.inl (ec.trans e); exact Or.inr (ec.trans e)])
          have hz_eq : z = nrmD u d c := by dsimp only [z]; rw [← nrmD_and_d hd0 u (opD d op a c), ec, nrmD_and_d hd0]
          exact hzb (hz_eq ▸ avail_nrm_mem hd hd0 hc hcn)
        · have hcn : ¬ IsConst d c := fun hcc => hznc (by
            rcases negD_const hd hcc with e | e
            · exact Or.inl (en.trans (by simpa [negD, Nat.and_assoc, Nat.and_self] using e))
            · exact Or.inr (en.trans (by simpa [negD, Nat.and_assoc, Nat.and_self] using e)))
          have hz_eq : z = nrmD true d c := by dsimp only [z]; rw [← nrmD_and_d hd0 true (opD d op a c), en, nrmD_neg hd hd0]
          exact hzb (hz_eq ▸ avail_nrm_mem hd hd0 hc hcn)
      have hc_nc : ¬ IsConst d c := by
        intro hcc
        have hznc : ¬ IsConst d (opD d op a c) := (nrmD_const_iff hd u _).1 hzp
        have hcm : opD d op a c = opD d (flipOp op) c a := opD_comm d hop a c
        rcases opD_const_left hd (flipOp_allowed hop) hcc with e0 | e1 | ea | ⟨rfl, en⟩
        · exact hznc (Or.inl (hcm.symm ▸ e0))
        · exact hznc (Or.inr (hcm.symm ▸ e1))
        · have hz_eq : z = nrmD u d a := by
            dsimp only [z]; rw [← nrmD_and_d hd0 u (opD d op a c), hcm, ea, nrmD_and_d hd0]
          exact hzb (hz_eq ▸ avail_nrm_mem hd hd0 ha ha_nc)
        · have hz_eq : z = nrmD true d a := by
            dsimp only [z]; rw [← nrmD_and_d hd0 true (opD d op a c), hcm, en, nrmD_neg hd hd0]
          exact hzb (hz_eq ▸ avail_nrm_mem hd hd0 ha ha_nc)
      set a' := nrmD u d a
      set c' := nrmD u d c
      have ha'_mem : a' ∈ b.map (nrmD u d) := avail_nrm_mem hd hd0 ha ha_nc
      have hc'_mem : c' ∈ b.map (nrmD u d) := avail_nrm_mem hd hd0 hc hc_nc
      have ha'_prop : a' ≠ 0 ∧ a' ≠ d := (nrmD_const_iff hd u a).2 ha_nc
      have hc'_prop : c' ≠ 0 ∧ c' ≠ d := (nrmD_const_iff hd u c).2 hc_nc
      have hne_ac : a' ≠ c' := by
        intro heq
        have hz_eq : opD d op' a' a' = a' ∨ opD d op' a' a' = 0 := by
          rcases allowed_cases hop' with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩
          · left; apply Nat.eq_of_testBit_eq; intro i
            have hm := congrArg (fun v => v.testBit i) (nrmD_mask u d a)
            change (a' &&& d).testBit i = a'.testBit i at hm
            simp only [opD, andD, Nat.testBit_and] at hm ⊢
            cases hd' : d.testBit i <;> cases ha' : a'.testBit i <;> simp_all
          · left; apply Nat.eq_of_testBit_eq; intro i
            have hm := congrArg (fun v => v.testBit i) (nrmD_mask u d a)
            change (a' &&& d).testBit i = a'.testBit i at hm
            simp only [opD, orD, Nat.testBit_and, Nat.testBit_or] at hm ⊢
            cases hd' : d.testBit i <;> cases ha' : a'.testBit i <;> simp_all
          · right; apply Nat.eq_of_testBit_eq; intro i
            have hdi := congrArg (fun v => v.testBit i) hd
            simp only [opD, andD, negD, Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit] at hdi ⊢
            cases hd' : d.testBit i <;> cases ha' : a'.testBit i <;> simp_all
          · right; apply Nat.eq_of_testBit_eq; intro i
            have hdi := congrArg (fun v => v.testBit i) hd
            simp only [opD, andD, negD, Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit] at hdi ⊢
            cases hd' : d.testBit i <;> cases ha' : a'.testBit i <;> simp_all
        have hez' : z = opD d op' a' a' := by
          have : z = opD d op' a' c' := hez
          rw [← heq] at this; exact this
        rcases hz_eq with e | e
        · exact hzb ((hez'.trans e).symm ▸ ha'_mem)
        · exact hzp.1 (hez'.trans e)
      set rest := ws.erase z
      have hrest_nd : rest.Nodup := hnd.erase z
      have hrest_sub : ∀ w ∈ rest, w ∈ b.map (nrmD u d) := by
        intro w hw
        have ⟨hne, hm⟩ := hnd.mem_erase_iff.1 hw
        rcases List.mem_cons.1 (hsub w hm) with rfl | hmb
        · exact absurd rfl hne
        · exact hmb
      have hrest_prop : ∀ w ∈ rest, w ≠ 0 ∧ w ≠ d := fun w hw => hprop w (List.mem_of_mem_erase hw)
      have hp1 : ws.Perm (z :: rest) := List.perm_cons_erase hzm
      have h1 : RunD u d Y k (opD d op' a' c' :: rest) := by
        rw [← hez]; exact Run.perm hp1 h
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
      have hne0 : opD d op' a' c' ≠ 0 := fun h0 => hzp.1 (hez.trans h0)
      have hned : opD d op' a' c' ≠ d := fun h1 => hzp.2 (hez.trans h1)
      have hnm : opD d op' a' c' ∉ (a' :: c' :: tail) := by
        rw [← hez, List.mem_cons, List.mem_cons]; rintro (e | e | hm)
        · exact hzb (by simpa [z, e] using ha'_mem)
        · exact hzb (by simpa [z, e] using hc'_mem)
        · exact hnd.not_mem_erase (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
      have h3 : RunD u d Y (k + 1) (a' :: c' :: tail) := Run.two op' ka kb hop' hne0 hned hnm h2
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

theorem reach_to_run_aux {u : Bool} {d : Nat} {roots : List Nat} {p bank}
    (hd : d &&& mask256 = d) (hd0 : d.testBit 0 = true)
    (hr : NatReach u d roots p bank) :
    ∀ {Y k ws}, ws.Nodup → (∀ w ∈ ws, w ≠ 0 ∧ w ≠ d) →
      (∀ w ∈ ws, w ∈ bank.map (nrmD u d)) → RunD u d Y k ws →
      ∃ k' ws', k' ≤ p + k ∧ ws'.Nodup ∧ (∀ w ∈ ws', w ≠ 0 ∧ w ≠ d) ∧
        (∀ w ∈ ws', w ∈ roots.map (nrmD u d)) ∧ RunD u d Y k' ws' := by
  induction p generalizing bank with
  | zero =>
    intro Y k ws hnd hprop hsub hrun
    subst hr
    exact ⟨k, ws, by omega, hnd, hprop, hsub, hrun⟩
  | succ p ih =>
    intro Y k ws hnd hprop hsub hrun
    obtain ⟨b, a, c, op, hop, rfl, hrb, ha, hc⟩ := hr
    have hsub' : ∀ w ∈ ws, w ∈ nrmD u d (opD d op a c) :: b.map (nrmD u d) := by
      intro w hw; simpa [List.map_cons] using hsub w hw
    obtain ⟨k1, ws1, hk1, hnd1, hprop1, hsub1, hrun1⟩ := pull_two hd hd0 hnd hprop hrun op hop ha hc hsub'
    obtain ⟨k2, ws2, hk2, hnd2, hprop2, hsub2, hrun2⟩ := ih hrb hnd1 hprop1 hsub1 hrun1
    exact ⟨k2, ws2, by omega, hnd2, hprop2, hsub2, hrun2⟩

theorem reach_to_run {u : Bool} {d : Nat} {roots : List Nat} {T : Nat} {p bank}
    (hd : d &&& mask256 = d) (hd0 : d.testBit 0 = true)
    (hT0 : T.testBit 0 = false) (hR0 : roots.all (fun r => !r.testBit 0) = true)
    (hnc : ¬ IsConst d T) (hr : NatReach u d roots p bank) (ha : Avail u d bank T) :
    ∃ s ws, s ≤ p ∧ ws.Nodup ∧ (∀ w ∈ ws, w ∈ roots.map (· &&& d)) ∧ RunD u d (T &&& d) s ws := by
  have hTmem : T &&& d ∈ bank.map (nrmD u d) := by
    have := avail_nrm_mem hd hd0 ha hnc
    rwa [nrmD_of_bit0_false u d T hT0] at this
  have hprop : ∀ w ∈ [T &&& d], w ≠ 0 ∧ w ≠ d := by
    intro w hw; rw [List.mem_singleton.1 hw]
    exact ⟨fun e => hnc (Or.inl e), fun e => hnc (Or.inr e)⟩
  have hsub : ∀ w ∈ [T &&& d], w ∈ bank.map (nrmD u d) := by
    intro w hw; rw [List.mem_singleton.1 hw]; exact hTmem
  obtain ⟨s, ws, hs, hnd, _, hsub', hrun⟩ := reach_to_run_aux hd hd0 hr (List.nodup_singleton _) hprop hsub Run.done
  have hrmap : roots.map (nrmD u d) = roots.map (· &&& d) := by
    apply List.map_congr_left
    intro r hr_m
    have h0 := List.all_eq_true.1 hR0 r hr_m
    simp only [Bool.not_eq_true'] at h0
    exact nrmD_of_bit0_false u d r h0
  rw [hrmap] at hsub'
  exact ⟨s, ws, by omega, hnd, hsub', hrun⟩

-- Bit separation lemmas
theorem runD_bits {u d y s ws} (hd : d &&& mask256 = d) (h : RunD u d y s ws) (i j : Nat)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (hw : ∀ w ∈ ws, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  have hmi : mask256.testBit i = true := by
    have := congrArg (fun v => v.testBit i) hd; simp [Nat.testBit_and, hi] at this; exact this
  have hmj : mask256.testBit j = true := by
    have := congrArg (fun v => v.testBit j) hd; simp [Nat.testBit_and, hj] at this; exact this
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | two op ka kb hop _ _ _ _ ih =>
    apply ih; have ha := hw _ List.mem_cons_self; have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hm
    rcases List.mem_cons.1 hm with rfl | hr
    · rcases allowed_cases hop with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
        simp [opD, andD, orD, negD, ha, hb, hi, hj, hmi, hmj]
    · rw [mem_kept, mem_kept] at hr
      rcases hr with ⟨_, rfl⟩ | ⟨_, rfl⟩ | hr
      · exact ha
      · exact hb
      · exact hw _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))

theorem runD_bits_le_mono {d y s ws} (h : RunD false d y s ws) (i j : Nat)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (hw : ∀ w ∈ ws, w.testBit i ≤ w.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | two op ka kb hop _ _ _ _ ih =>
    apply ih; have ha := hw _ List.mem_cons_self; have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hm
    rcases List.mem_cons.1 hm with rfl | hr
    · rcases allowed_cases hop with rfl | rfl | ⟨h, _⟩ | ⟨h, _⟩
      · simp only [opD, andD, beq_self_eq_true, ite_true, Nat.testBit_and, hi, hj, Bool.and_true]; grind
      · simp only [opD, orD, beq_self_eq_true, ite_true, ite_false, Nat.testBit_and, Nat.testBit_or, hi, hj, Bool.and_true]; grind
      · contradiction
      · contradiction
    · rw [mem_kept, mem_kept] at hr
      rcases hr with ⟨_, rfl⟩ | ⟨_, rfl⟩ | hr
      · exact ha
      · exact hb
      · exact hw _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))

theorem lower_base {u : Bool} {d : Nat} {roots : List Nat} {T : Nat} (h : availB u d roots T = false) :
    Lower u d roots T 1 := by
  intro p bank hr ha
  cases p with
  | zero =>
    dsimp only [NatReach] at hr; rw [hr] at ha
    have ht := (availB_iff u d roots T).2 ha
    rw [h] at ht; contradiction
  | succ p => omega

-- moveBits & lower_iso
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

theorem applyMoves_opD (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    {d1 d2 : Nat} (hd : applyMoves ms d2 = d1) (op a b : Nat) :
    applyMoves ms (opD d2 op a b) = opD d1 op (applyMoves ms a) (applyMoves ms b) := by
  obtain ⟨hand, hor, hxor, _, h256⟩ := applyMoves_hom ms hok
  unfold opD; split_ifs <;> simp only [andD, orD, negD, hand, hor, hxor, h256, hd]

theorem applyMoves_runD {u d Y s} (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    (hd : applyMoves ms d = d) (hY : applyMoves ms Y = Y) {ws} (h : RunD u d Y s ws) :
    RunD u d Y s (ws.map (applyMoves ms)) := by
  obtain ⟨_, _, _, h0, _⟩ := applyMoves_hom ms hok
  have hinj := applyMoves_inj ms hok
  rw [← hY]
  induction h using Run.fold with
  | done => exact Run.done
  | perm hp _ ih => exact Run.perm (hp.map _) ih
  | @two s a b r op ka kb hop hne0 hned hnm _ ih =>
    have eop := applyMoves_opD ms hok hd op a b
    have e1 : (opD d op a b :: kept ka a (kept kb b r)).map (applyMoves ms) =
        opD d op (applyMoves ms a) (applyMoves ms b) ::
          kept ka (applyMoves ms a) (kept kb (applyMoves ms b) (r.map (applyMoves ms))) := by
      simp [kept_map, eop]
    rw [e1] at ih
    refine Run.two op ka kb hop ?_ ?_ ?_ ih
    · intro e; rw [← eop] at e; exact hne0 (hinj (e.trans h0.symm))
    · intro e; rw [← eop] at e; exact hned (hinj (e.trans hd.symm))
    · rw [← eop, ← List.map_cons, ← List.map_cons, List.mem_map]; rintro ⟨x, hx, he⟩; exact hnm (hinj he ▸ hx)

theorem reach_map_moves {u : Bool} (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    {d1 d2 : Nat} (hd1 : d1 &&& mask256 = d1) (hd : applyMoves ms d2 = d1)
    {roots1 roots2 : List Nat} (hroots : ∀ r ∈ roots2, Avail u d1 roots1 (applyMoves ms r)) :
    ∀ {p bank}, NatReach u d2 roots2 p bank →
      ∃ bank', NatReach u d1 roots1 p bank' ∧ ∀ v ∈ bank, Avail u d1 bank' (applyMoves ms v) := by
  obtain ⟨hand, _, hxor, h0, h256⟩ := applyMoves_hom ms hok
  have hav : ∀ {b b' w}, (∀ v ∈ b, Avail u d1 b' (applyMoves ms v)) →
      Avail u d2 b w → Avail u d1 b' (applyMoves ms w) := by
    intro b b' w hbb hw
    rcases hw with (hz | h1) | ⟨v, hv, he⟩ | ⟨rfl, v, hv, he⟩
    · exact Or.inl (Or.inl (by rw [← hd, ← hand, hz, h0]))
    · exact Or.inl (Or.inr (by rw [← hd, ← hand, h1]))
    · have hve : applyMoves ms v &&& d1 = applyMoves ms w &&& d1 := by rw [← hd, ← hand, ← hand, he]
      exact avail_of_eq hve (hbb v hv)
    · have hve : applyMoves ms v &&& d1 = negD d1 (applyMoves ms w) &&& d1 := by
        rw [← hd, ← hand, he]; simp only [negD, hand, hxor, h256, hd, Nat.and_assoc, Nat.and_self]
      have hneg := avail_neg hd1 (avail_of_eq hve (hbb v hv))
      exact avail_of_eq (by rw [negD_invol hd1, Nat.and_assoc, Nat.and_self]) hneg
  intro p
  induction p with
  | zero =>
    intro bank hr; subst hr
    exact ⟨roots1, rfl, hroots⟩
  | succ p ih =>
    intro bank hr
    obtain ⟨b, a, c, op, hop, rfl, hrb, ha, hc⟩ := hr
    obtain ⟨b', hrb', hbb⟩ := ih hrb
    have ha' := hav hbb ha; have hc' := hav hbb hc
    refine ⟨opD d1 op (applyMoves ms a) (applyMoves ms c) :: b',
      ⟨b', applyMoves ms a, applyMoves ms c, op, hop, rfl, hrb', ha', hc'⟩, ?_⟩
    intro v hv; rcases List.mem_cons.1 hv with rfl | hv
    · exact Or.inr (Or.inl ⟨opD d1 op (applyMoves ms a) (applyMoves ms c), List.mem_cons_self, by
        rw [applyMoves_opD ms hok hd]⟩)
    · exact avail_cons _ _ (hbb v hv)

theorem lower_iso {u : Bool} {d1 d2 T1 T2 L : Nat} {roots1 roots2 : List Nat}
    (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    (hd1 : d1 &&& mask256 = d1) (hd : applyMoves ms d2 = d1) (hT : applyMoves ms T2 = T1)
    (hroots : roots2.all (fun r => availB u d1 roots1 (applyMoves ms r)) = true)
    (h1 : Lower u d1 roots1 T1 L) : Lower u d2 roots2 T2 L := by
  obtain ⟨hand, _, hxor, h0, h256⟩ := applyMoves_hom ms hok
  have hr : ∀ r ∈ roots2, Avail u d1 roots1 (applyMoves ms r) := fun r hr =>
    (availB_iff u _ _ _).1 (List.all_eq_true.1 hroots r hr)
  intro p bank hreach ha
  obtain ⟨bank', hrb', hbb⟩ := reach_map_moves ms hok hd1 hd hr hreach
  apply h1 p bank' hrb'
  rcases ha with (hz | ho) | ⟨v, hv, he⟩ | ⟨rfl, v, hv, he⟩
  · exact Or.inl (Or.inl (by rw [← hT, ← hd, ← hand, hz, h0]))
  · exact Or.inl (Or.inr (by rw [← hT, ← hd, ← hand, ho]))
  · have hve : applyMoves ms v &&& d1 = T1 &&& d1 := by rw [← hT, ← hd, ← hand, ← hand, he]
    exact avail_of_eq hve (hbb v hv)
  · have hve : applyMoves ms v &&& d1 = negD d1 T1 &&& d1 := by
      rw [← hT, ← hd, ← hand, he]; simp only [negD, hand, hxor, h256, hd, Nat.and_assoc, Nat.and_self]
    have hneg := avail_neg hd1 (avail_of_eq hve (hbb v hv))
    exact avail_of_eq (by rw [negD_invol hd1, Nat.and_assoc, Nat.and_self]) hneg

-- lower_slice
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

theorem lower_slice {u : Bool} {d dSub T TSub L : Nat} {roots rootsSub : List Nat}
    (hd : d &&& mask256 = d) (hd0 : d.testBit 0 = true)
    (hT0 : T.testBit 0 = false) (hR0 : roots.all (fun r => !r.testBit 0) = true)
    (hdSub : dSub &&& mask256 = dSub) (hsub : dSub &&& d = dSub)
    (hT : T &&& dSub = TSub &&& dSub)
    (hnc : isConstB d T = false) (hncSub : isConstB dSub TSub = false)
    (hcov : roots.all (availB u dSub rootsSub) = true)
    (singles : List (Nat × Nat × Nat))
    (hs_nd : (singles.map Prod.fst).Nodup)
    (hs_ok : singles.all (fun e => isConstB dSub e.1 && essOK d (T &&& d) (roots.map (· &&& d)) e.1 e.2) = true)
    (hprior : Lower u dSub rootsSub TSub L) :
    Lower u d roots T (L + singles.length) := by
  have hnc' : ¬ IsConst d T := fun h => by rw [(isConstB_iff _ _).2 h] at hnc; contradiction
  have hncSub' : ¬ IsConst dSub (T &&& d) := by
    intro h
    have e : (T &&& d) &&& dSub = TSub &&& dSub := by
      rw [Nat.and_assoc, Nat.and_comm d dSub, hsub, hT]
    rcases h with h0 | h1
    · exact absurd ((isConstB_iff _ _).2 (Or.inl (e.symm.trans h0))) (by simp [hncSub])
    · exact absurd ((isConstB_iff _ _).2 (Or.inr (e.symm.trans h1))) (by simp [hncSub])
  intro p bank hr ha
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run hd hd0 hT0 hR0 hnc' hr ha
  have hws_av : ∀ w ∈ ws, Avail u dSub rootsSub w := by
    intro w hw
    obtain ⟨r, hr_m, rfl⟩ := List.mem_map.1 (hws_sub w hw)
    have hav := (availB_iff u _ _ _).1 (List.all_eq_true.1 hcov r hr_m)
    exact avail_of_eq (by rw [Nat.and_assoc, Nat.and_comm d dSub, hsub]) hav
  obtain ⟨q, next, hq, ht, hle⟩ := contraction hdSub hsub hncSub' hrun (p := 0) (bank := rootsSub) rfl hws_av
  have hTSub_av : Avail u dSub next TSub := avail_of_eq (by
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

-- poolCut (52-bit compact hint)
def runChoices (u : Bool) (d : Nat) (pool : List Nat) : Nat → Nat → Option (List Nat)
  | 0, _ => some pool
  | p + 1, bits =>
    let code := bits &&& 1023
    let op := code &&& 3
    let ia := (code >>> 2) &&& 15
    let ib := (code >>> 6) &&& 15
    if allowedB u op && ia < pool.length && ib < pool.length then
      let a := pool.getD ia 0
      let b := pool.getD ib 0
      runChoices u d (pool ++ [opD d op a b]) p (bits >>> 10)
    else none

theorem getD_mem {xs : List Nat} {i : Nat} (hi : i < xs.length) : xs.getD i 0 ∈ xs := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem hi

theorem runChoices_sound {u : Bool} {d : Nat} {roots : List Nat} :
    ∀ (p bits q : Nat) (bank pool result : List Nat),
      NatReach u d roots q bank →
      (∀ v ∈ pool, Avail u d bank v) →
      runChoices u d pool p bits = some result →
      ∃ bank', NatReach u d roots (q + p) bank' ∧ ∀ v ∈ result, Avail u d bank' v
  | 0, _, q, bank, pool, result, hr, hsup, hok => by
    simp only [runChoices, Option.some.injEq] at hok; subst hok; exact ⟨bank, hr, hsup⟩
  | p + 1, bits, q, bank, pool, result, hr, hsup, hok => by
    simp only [runChoices] at hok
    split at hok
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      obtain ⟨⟨hop, hia⟩, hib⟩ := hcond
      set code := bits &&& 1023
      set op := code &&& 3
      set ia := (code >>> 2) &&& 15
      set ib := (code >>> 6) &&& 15
      set a := pool.getD ia 0
      set b := pool.getD ib 0
      set w := opD d op a b
      have ha : Avail u d bank a := hsup a (getD_mem hia)
      have hb : Avail u d bank b := hsup b (getD_mem hib)
      have hr1 : NatReach u d roots (q + 1) (w :: bank) := ⟨bank, a, b, op, hop, rfl, hr, ha, hb⟩
      have hsup1 : ∀ v ∈ pool ++ [w], Avail u d (w :: bank) v := by
        intro v hv; rcases List.mem_append.1 hv with hv | hv
        · exact avail_cons _ _ (hsup v hv)
        · rw [List.mem_singleton.1 hv]; exact Or.inr (Or.inl ⟨w, List.mem_cons_self, rfl⟩)
      obtain ⟨bank', hrb', hsb'⟩ := runChoices_sound p (bits >>> 10) (q + 1) (w :: bank) (pool ++ [w]) result hr1 hsup1 hok
      exact ⟨bank', by simpa [Nat.add_assoc, Nat.add_comm 1] using hrb', hsb'⟩
    · contradiction

def checkCutEntry (u : Bool) (dSub : Nat) (rootsSub : List Nat) (LSub s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  let p := (hint >>> 8) &&& 15
  decide (s + p < LSub + ws.countP (isConstB dSub)) &&
  match runChoices u dSub rootsSub p (hint >>> 12) with
  | none => false
  | some pool => ws.all (availB u dSub pool)

theorem checkCutEntry_sound {u : Bool} {d dSub T TSub LSub s : Nat} {rootsSub ws : List Nat}
    (hdSub : dSub &&& mask256 = dSub) (hsub : dSub &&& d = dSub)
    (hT : T &&& dSub = TSub &&& dSub) (hncSub : isConstB dSub TSub = false)
    (hprior : Lower u dSub rootsSub TSub LSub) (hint : Nat)
    (hchk : checkCutEntry u dSub rootsSub LSub s ws hint = true) :
    ¬ RunD u d (T &&& d) s ws := by
  intro hrun
  simp only [checkCutEntry, Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨hineq, hmatch⟩ := hchk
  cases hrc : runChoices u dSub rootsSub ((hint >>> 8) &&& 15) (hint >>> 12) with
  | none => rw [hrc] at hmatch; contradiction
  | some pool =>
    rw [hrc] at hmatch
    have hsup0 : ∀ v ∈ rootsSub, Avail u dSub rootsSub v := fun v hv => Or.inr (Or.inl ⟨v, hv, rfl⟩)
    obtain ⟨bank, hrb, hsb⟩ := runChoices_sound _ _ 0 rootsSub rootsSub pool rfl hsup0 hrc
    simp only [Nat.zero_add] at hrb
    have hws_av : ∀ w ∈ ws, Avail u dSub bank w := by
      intro w hw
      have hav := (availB_iff u _ _ _).1 (List.all_eq_true.1 hmatch w hw)
      rcases hav with hc | ⟨v, hv, he⟩ | ⟨rfl, v, hv, he⟩
      · exact Or.inl hc
      · exact avail_of_eq he (hsb v hv)
      · have hneg := avail_neg hdSub (hsb v hv)
        have he' : negD dSub v &&& dSub = w &&& dSub := by
          rw [← negD_mask, he, negD_invol hdSub, Nat.and_assoc, Nat.and_self]
        exact avail_of_eq he' hneg
    have hnc' : ¬ IsConst dSub (T &&& d) := by
      intro h; have e : (T &&& d) &&& dSub = TSub &&& dSub := by rw [Nat.and_assoc, Nat.and_comm d dSub, hsub, hT]
      rcases h with h0 | h1
      · exact absurd ((isConstB_iff _ _).2 (Or.inl (e.symm.trans h0))) (by simp [hncSub])
      · exact absurd ((isConstB_iff _ _).2 (Or.inr (e.symm.trans h1))) (by simp [hncSub])
    obtain ⟨q, next, hq, ht, hle⟩ := contraction hdSub hsub hnc' hrun hrb hws_av
    have hL := hprior q next hq (avail_of_eq (by rw [Nat.and_assoc, Nat.and_comm d dSub, hsub, hT]) ht)
    omega

-- covers, eval6, hw256, hk, bsr, bar, bar_all
def coversP (u : Bool) (pairs : List (Nat × Nat)) (ws : List Nat) : Bool :=
  if !u then
    pairs.all (fun p => ws.any (fun w => !w.testBit p.1 && w.testBit p.2))
  else
    pairs.all (fun p => ws.any (fun w => w.testBit p.1 != w.testBit p.2))

theorem coversP_ok {u : Bool} {d T s : Nat} (hd : d &&& mask256 = d)
    (pairs : List (Nat × Nat))
    (hpairs : pairs.all (fun p => d.testBit p.1 && d.testBit p.2 && !(T &&& d).testBit p.1 && (T &&& d).testBit p.2) = true)
    {ws : List Nat} (h : RunD u d (T &&& d) s ws) : coversP u pairs ws = true := by
  cases u with
  | false =>
    simp only [coversP, Bool.not_false, ite_true, List.all_eq_true, List.any_eq_true]
    intro ⟨u1, v1⟩ hm
    have hp := List.all_eq_true.1 hpairs (u1, v1) hm
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
    by_contra! hall
    have hle := runD_bits_le_mono h v1 u1 hp.1.1.2 hp.1.1.1 (fun w hw => by
      have hbad := hall w hw
      cases hu : w.testBit u1 <;> cases hv : w.testBit v1 <;> simp_all)
    rw [hp.1.2, hp.2] at hle; contradiction
  | true =>
    simp only [coversP, Bool.not_true, Bool.false_eq_true, ite_false, List.all_eq_true, List.any_eq_true, bne_iff_ne]
    intro ⟨u1, v1⟩ hm
    have hp := List.all_eq_true.1 hpairs (u1, v1) hm
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
    by_contra! hall
    have heq := runD_bits hd h u1 v1 hp.1.1.1 hp.1.1.2 hall
    rw [hp.1.2, hp.2] at heq; contradiction

def unorientedCov (pairs : List (Nat × Nat)) (ws : List Nat) : Bool :=
  pairs.all (fun p => ws.any (fun w => w.testBit p.1 != w.testBit p.2))

theorem unorientedCov_ok {u : Bool} {d T s : Nat} (hd : d &&& mask256 = d)
    (pairs : List (Nat × Nat))
    (hpairs : pairs.all (fun p => d.testBit p.1 && d.testBit p.2 && !(T &&& d).testBit p.1 && (T &&& d).testBit p.2) = true)
    {ws : List Nat} (h : RunD u d (T &&& d) s ws) : unorientedCov pairs ws = true := by
  simp only [unorientedCov, List.all_eq_true, List.any_eq_true, bne_iff_ne]
  intro ⟨u1, v1⟩ hm
  have hp := List.all_eq_true.1 hpairs (u1, v1) hm
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
  by_contra! hall
  have heq := runD_bits hd h u1 v1 hp.1.1.1 hp.1.1.2 hall
  rw [hp.1.2, hp.2] at heq; contradiction

-- Fast bitmask-decorated covers
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

def opP (mp op : Nat) (pa pb : Nat) : Nat :=
  if op == 0 then pa &&& pb
  else if op == 1 then pa ||| pb
  else if op == 2 then pa &&& (pb ^^^ mp)
  else (pa ^^^ mp) &&& pb

theorem projBit_opD {dm : Nat} (hd : dm &&& mask256 = dm) {rs : List Nat}
    (hrs : ∀ r ∈ rs, dm.testBit r = true) (op a b : Nat) :
    projBit rs (opD dm op a b) = opP (maskP rs.length) op (projBit rs a) (projBit rs b) := by
  apply Nat.eq_of_testBit_eq; intro i
  by_cases hi : i < rs.length
  · have hdr := hrs rs[i] (List.getElem_mem hi)
    have hmr : mask256.testBit rs[i] = true := by
      have := congrArg (fun v => v.testBit rs[i]) hd; simp [Nat.testBit_and, hdr] at this; exact this
    unfold opD opP
    split_ifs <;>
      simp only [projBit_testBit, hi, dite_true, andD, orD, negD, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor,
        maskP, Nat.testBit_two_pow_sub_one, decide_true, hdr, hmr, Bool.and_true, Bool.xor_true] <;>
      (cases a.testBit rs[i] <;> cases b.testBit rs[i] <;> rfl)
  · unfold opD opP
    split_ifs <;>
      simp only [projBit_testBit, hi, dite_false, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor,
        maskP, Nat.testBit_two_pow_sub_one, decide_false, Bool.false_and, Bool.and_false, Bool.false_or, Bool.xor_false]

theorem foldl_or_testBit {α : Type} (g : α → Nat) (xs : List α) (acc i : Nat) :
    (xs.foldl (fun a x => a ||| g x) acc).testBit i = (acc.testBit i || xs.any (fun x => (g x).testBit i)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, Nat.testBit_or, List.any_cons, Bool.or_assoc]

def colB (mp : Nat) (oriented : Bool) (p : Nat × Nat) : Nat :=
  if oriented then (p.1 ^^^ mp) &&& p.2 else p.1 ^^^ p.2

def coversD (u : Bool) (mp : Nat) (dws : List (Nat × Nat × Nat)) : Bool :=
  dws.foldl (fun acc d => acc ||| colB mp (!u) d.2) 0 == mp

theorem coversD_eq (u : Bool) (pairs : List (Nat × Nat)) (ws : List Nat) :
    coversD u (maskP pairs.length) (ws.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))) =
      coversP u pairs ws := by
  set r1s := pairs.map Prod.fst
  set r2s := pairs.map Prod.snd
  set mp := maskP pairs.length
  have hr1 : r1s.length = pairs.length := List.length_map _
  have hr2 : r2s.length = pairs.length := List.length_map _
  unfold coversD coversP
  cases u with
  | false =>
    simp only [Bool.not_false, colB, ite_true]
    apply Bool.eq_iff_iff.2; rw [beq_iff_eq, List.all_eq_true]
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
  | true =>
    simp only [Bool.not_true, colB, Bool.false_eq_true, ite_false]
    apply Bool.eq_iff_iff.2; rw [beq_iff_eq, List.all_eq_true]
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

theorem score_bound {d y s ws} (h : RunD false d y s ws) (hl : ws.length = s + 1)
    (v : Nat → Nat) (hand : ∀ a b, v (andD d a b) ≤ v a + v b)
    (hor : ∀ a b, v (orD d a b) ≤ v a + v b) : v y ≤ (ws.map v).sum := by
  induction h using Run.fold with
  | done => simp
  | perm p _ ih => rw [← (p.map v).sum_eq]; exact ih (p.length_eq.trans hl)
  | two op ka kb hop _ _ _ h ih =>
    have hh := run_len h; cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih' := ih (by simp [kept]; omega)
    rcases allowed_cases hop with rfl | rfl | ⟨hc, _⟩ | ⟨hc, _⟩
    · simp only [opD, beq_self_eq_true, ite_true, kept, Bool.false_eq_true, ite_false, List.map_cons, List.sum_cons] at ih' ⊢
      grw [← Nat.add_assoc, ← hand]; exact ih'
    · simp only [opD, beq_self_eq_true, ite_true, ite_false, kept, Bool.false_eq_true, List.map_cons, List.sum_cons] at ih' ⊢
      grw [← Nat.add_assoc, ← hor]; exact ih'
    · contradiction
    · contradiction

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

theorem eval6_bound {dm y s ws} (h : RunD false dm y s ws) (hl : ws.length = s + 1)
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

theorem scoreCheck_no {dm y s ws} (h : RunD false dm y s ws) (code : Nat) :
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

def scr (u : Bool) (dm y s : Nat) (pool : List Nat) (zs : List Nat) : Bool :=
  !u && zs.length == s + 1 && pool.any (scoreCheck dm y s zs)

theorem scr_no {u : Bool} {dm y s : Nat} (pool : List Nat) {zs : List Nat}
    (h : RunD u dm y s zs) : scr u dm y s pool zs = false := by
  cases u with
  | true => simp [scr]
  | false =>
    unfold scr; simp only [Bool.not_false, Bool.true_and]
    rw [Bool.and_eq_false_iff]; right; rw [List.any_eq_false]
    intro x _; rw [scoreCheck_no h x]; simp

def opsOf (u : Bool) : List Nat := if u then [0, 1, 2, 3] else [0, 1]

theorem mem_opsOf {u : Bool} {op : Nat} (hop : allowedB u op = true) : op ∈ opsOf u := by
  rcases allowed_cases hop with rfl | rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · cases u <;> decide
  · cases u <;> decide
  · decide
  · decide

def nextD (u : Bool) (dm : Nat) (slack : Nat) (ws : List Nat) (f : List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        (opsOf u).any fun op =>
          let w := opD dm op a b
          w != 0 && w != dm && !(ws.contains w) &&
            (f (w :: r) || (slack ≥ 1 && (f (w :: a :: r) || f (w :: b :: r))) ||
              (slack ≥ 2 && f (w :: a :: b :: r))))

theorem nextD_two_sorted {u : Bool} {dm y a b rest} {op : Nat} {ka kb : Bool} {s ws}
    (hop : allowedB u op = true) (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h0 : opD dm op a b ≠ 0) (hd : opD dm op a b ≠ dm) (hnm : opD dm op a b ∉ (a :: b :: rest))
    (h : RunD u dm y s (opD dm op a b :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool) (hf : ∀ ys, RunD u dm y s ys → f ys = true) :
    nextD u dm (s + 2 - ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := run_len h; have hl := p.length_eq; simp only [List.length_cons] at hl hh
  have hnc : ws.contains (opD dm op a b) = false := by
    cases h : ws.contains (opD dm op a b) with
    | false => rfl
    | true => exact absurd (p.mem_iff.2 (by simpa using h)) hnm
  have h0b : (opD dm op a b != 0) = true := bne_iff_ne.2 h0
  have hdb : (opD dm op a b != dm) = true := bne_iff_ne.2 hd
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  apply List.any_eq_true.2 ⟨b, hb, ?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab, ?_⟩
  apply List.any_eq_true.2 ⟨op, mem_opsOf hop, ?_⟩
  simp only [h0b, hdb, hnc, Bool.not_false, Bool.true_and]
  have ht := hf _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true] <;>
    first | (simp [show 2 ≤ s + 2 - ws.length by omega]) | (simp [show 1 ≤ s + 2 - ws.length by omega])

theorem nextD_two {u : Bool} {dm y a b rest} {op : Nat} {ka kb : Bool} {s ws}
    (hop : allowedB u op = true) (p : (a :: b :: rest).Perm ws)
    (h0 : opD dm op a b ≠ 0) (hd : opD dm op a b ≠ dm) (hnm : opD dm op a b ∉ (a :: b :: rest))
    (h : RunD u dm y s (opD dm op a b :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool) (hf : ∀ ys, RunD u dm y s ys → f ys = true) :
    nextD u dm (s + 2 - ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact nextD_two_sorted hop hab p h0 hd hnm h f hf
  · have he : opD dm op a b = opD dm (flipOp op) b a := opD_comm dm hop a b
    have hnm' : opD dm (flipOp op) b a ∉ (b :: a :: rest) := by
      rw [← he]; intro hm; exact hnm ((List.Perm.swap _ _ _).mem_iff.1 hm)
    apply nextD_two_sorted (op := flipOp op) (ka := kb) (kb := ka) (flipOp_allowed hop) hba
      ((List.Perm.swap _ _ _).trans p) (he ▸ h0) (he ▸ hd) hnm' _ f hf
    rw [he] at h; apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]; exact List.Perm.swap _ _ _

theorem nextD_complete {u : Bool} {dm y t ws} (h : RunD u dm y t ws) :
    ∀ s, t = s + 1 → ∀ zs, ws.Perm zs → ∀ f : List Nat → Bool,
      (∀ ys, RunD u dm y s ys → f ys = true) →
      nextD u dm (s + 2 - zs.length) zs f = true := by
  induction h using Run.fold with
  | done => simp
  | perm p _ ih => intro s he zs q; exact ih s he zs (p.trans q)
  | two op ka kb hop h0 hd hnm h _ => intro s he zs p f hf; cases he; exact nextD_two hop p h0 hd hnm h f hf

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
  let x := (((w &&& 4294967295) ^^^ seed) * 2654435761 +
            (((w >>> 32) &&& 4294967295) ^^^ seed) * 2246822519 +
            (((w >>> 64) &&& 4294967295) ^^^ seed) * 3266489917 +
            (((w >>> 96) &&& 4294967295) ^^^ seed) * 668265263 +
            (((w >>> 128) &&& 4294967295) ^^^ seed) * 374761393 +
            (((w >>> 160) &&& 4294967295) ^^^ seed) * 1274126177 +
            (((w >>> 192) &&& 4294967295) ^^^ seed) * 2869860233 +
            (((w >>> 224) &&& 4294967295) ^^^ seed) * 1640531527) &&& 4294967295
  let y := ((x ^^^ (x >>> 16)) * 2246822519) &&& 4294967295
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
  let i := idxH s h
  decide (i < N s) && (htAt s i == h) && zs.isPerm (S s i)

-- Decorated fast O(1) incremental cover check!
def nextD_decor (u : Bool) (dm mp : Nat) (slack : Nat) (dws : List (Nat × Nat × Nat))
    (f : List (Nat × Nat × Nat) → Bool) : Bool :=
  dws.any fun da =>
    let a := da.1
    let ra := dws.erase da
    ra.any fun db =>
      let b := db.1
      a ≤ b && (let r := ra.erase db
        (opsOf u).any fun op =>
          let w := opD dm op a b
          w != 0 && w != dm && !(dws.any (fun x => x.1 == w)) &&
            let dw := (w, opP mp op da.2.1 db.2.1, opP mp op da.2.2 db.2.2)
            (f (dw :: r) || (slack ≥ 1 && (f (dw :: da :: r) || f (dw :: db :: r))) ||
              (slack ≥ 2 && f (dw :: da :: db :: r))))

theorem nextD_decor_gen (u : Bool) (dm mp : Nat) (dec : Nat → Nat × Nat × Nat)
    (hfst : ∀ w, (dec w).1 = w)
    (hop : ∀ op a b, (opD dm op a b, opP mp op (dec a).2.1 (dec b).2.1, opP mp op (dec a).2.2 (dec b).2.2) = dec (opD dm op a b))
    (slack : Nat) (ws : List Nat) (g : List (Nat × Nat × Nat) → Bool) :
    nextD_decor u dm mp slack (ws.map dec) g = nextD u dm slack ws (fun zs => g (zs.map dec)) := by
  have hinj : Function.Injective dec := fun x y h => by rw [← hfst x, ← hfst y, h]
  have herase : ∀ (l : List Nat) x, (l.map dec).erase (dec x) = (l.erase x).map dec :=
    fun l x => erase_map_inj dec hinj l x
  have hcont : ∀ (l : List Nat) w, (l.map dec).any (fun x => x.1 == w) = l.contains w := by
    intro l w; apply Bool.eq_iff_iff.2; simp [hfst]
  unfold nextD_decor nextD
  simp only [List.any_map, Function.comp_def, hfst, herase, hcont, hop, List.map_cons]

theorem nextD_decor_eq (u : Bool) {dm : Nat} (hd : dm &&& mask256 = dm)
    (pairs : List (Nat × Nat))
    (hr1 : ∀ r ∈ pairs.map Prod.fst, dm.testBit r = true)
    (hr2 : ∀ r ∈ pairs.map Prod.snd, dm.testBit r = true)
    (slack : Nat) (ws : List Nat) (g : List (Nat × Nat × Nat) → Bool) :
    let dec := fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w)
    nextD_decor u dm (maskP pairs.length) slack (ws.map dec) g =
      nextD u dm slack ws (fun zs => g (zs.map dec)) := by
  intro dec
  apply nextD_decor_gen
  · intro w; rfl
  · intro op a b
    simp only [dec, projBit_opD hd hr1, projBit_opD hd hr2, List.length_map]

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

theorem cov3_coversD (u : Bool) (mp : Nat) (dw : Nat × Nat × Nat) (rest : List (Nat × Nat × Nat)) :
    ((cov3 mp (!u) rest).1 ||| colB mp (!u) dw.2 == mp) = coversD u mp (dw :: rest) := by
  have e : ((cov3 mp (!u) rest).1 ||| colB mp (!u) dw.2) =
      (dw :: rest).foldl (fun acc x => acc ||| colB mp (!u) x.2) 0 := by
    apply Nat.eq_of_testBit_eq; intro i
    obtain ⟨h1, _, _⟩ := cov3_bit mp (!u) rest i
    rw [foldl_or_testBit, Nat.zero_testBit, Bool.false_or, Nat.testBit_or, h1, List.any_cons]
    have hp : decide (1 ≤ rest.countP (fun dw => (colB mp (!u) dw.2).testBit i)) =
        rest.any (fun x => (colB mp (!u) x.2).testBit i) := by
      rw [Bool.eq_iff_iff, decide_eq_true_eq, Nat.succ_le_iff, List.countP_pos_iff, List.any_eq_true]
    rw [hp, Bool.or_comm]
  unfold coversD; exact congrArg (· == mp) e

def nextD_cov (u : Bool) (dm mp slack : Nat) (dws : List (Nat × Nat × Nat))
    (f : List (Nat × Nat × Nat) → Bool) : Bool :=
  let ori := !u
  let cov := cov3 mp ori dws
  dws.any fun da =>
    let a := da.1
    let ca := colB mp ori da.2
    let ra := dws.erase da
    ra.any fun db =>
      let b := db.1
      a ≤ b &&
        (let cb := colB mp ori db.2
         let base0 := takeTwo cov ca cb
         let base1a := takeOne cov cb
         let base1b := takeOne cov ca
         let r := ra.erase db
         (opsOf u).any fun op =>
           let pz := (opP mp op da.2.1 db.2.1, opP mp op da.2.2 db.2.2)
           let cz := colB mp ori pz
           let ok0 := (base0 ||| cz) == mp
           let ok1a := slack ≥ 1 && ((base1a ||| cz) == mp)
           let ok1b := slack ≥ 1 && ((base1b ||| cz) == mp)
           let ok2 := slack ≥ 2 && ((cov.1 ||| cz) == mp)
           (ok0 || ok1a || ok1b || ok2) &&
           (let w := opD dm op a b
            w != 0 && w != dm && !(dws.any (fun x => x.1 == w)) &&
              let dw := (w, pz)
              ((ok0 && f (dw :: r)) || (ok1a && f (dw :: da :: r)) ||
               (ok1b && f (dw :: db :: r)) || (ok2 && f (dw :: da :: db :: r)))))

theorem nextD_cov_eq (u : Bool) (dm mp slack : Nat) (dws : List (Nat × Nat × Nat))
    (g : List (Nat × Nat × Nat) → Bool) :
    nextD_cov u dm mp slack dws g =
      nextD_decor u dm mp slack dws (fun dzs => coversD u mp dzs && g dzs) := by
  unfold nextD_cov nextD_decor
  dsimp only
  apply Bool.eq_iff_iff.2; simp only [List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨da, hda, db, hdb, hab, op, hop, _, ⟨⟨hw0, hwdm⟩, hnw⟩, hfx⟩
    refine ⟨da, hda, db, hdb, hab, op, hop, ⟨⟨hw0, hwdm⟩, hnw⟩, ?_⟩
    set pz := (opP mp op da.2.1 db.2.1, opP mp op da.2.2 db.2.2)
    set dw := (opD dm op da.1 db.1, pz)
    set ra := dws.erase da
    set r := ra.erase db
    have hp : dws.Perm (da :: db :: r) := (List.perm_cons_erase hda).trans (List.Perm.cons _ (List.perm_cons_erase hdb))
    have hc2 := cov3_perm mp (!u) hp
    have hca := cov3_perm mp (!u) (hp.trans (List.Perm.swap _ _ _))
    have hcov0 : (takeTwo (cov3 mp (!u) dws) (colB mp (!u) da.2) (colB mp (!u) db.2) ||| colB mp (!u) pz == mp) =
        coversD u mp (dw :: r) := by rw [hc2, takeTwo_eq]; exact cov3_coversD u mp dw r
    have hcov1a : (takeOne (cov3 mp (!u) dws) (colB mp (!u) db.2) ||| colB mp (!u) pz == mp) =
        coversD u mp (dw :: da :: r) := by rw [hca, takeOne_eq]; exact cov3_coversD u mp dw (da :: r)
    have hcov1b : (takeOne (cov3 mp (!u) dws) (colB mp (!u) da.2) ||| colB mp (!u) pz == mp) =
        coversD u mp (dw :: db :: r) := by rw [hc2, takeOne_eq]; exact cov3_coversD u mp dw (db :: r)
    have hcov2 : ((cov3 mp (!u) dws).1 ||| colB mp (!u) pz == mp) =
        coversD u mp (dw :: da :: db :: r) := by rw [hc2]; exact cov3_coversD u mp dw (da :: db :: r)
    rcases hfx with ((⟨hu0, hf0⟩ | ⟨⟨hsl1, hu1a⟩, hf1a⟩) | ⟨⟨hsl1, hu1b⟩, hf1b⟩) | ⟨⟨hsl2, hu2⟩, hf2⟩
    · left; left; exact ⟨hcov0 ▸ hu0, hf0⟩
    · left; right; exact ⟨hsl1, Or.inl ⟨hcov1a ▸ hu1a, hf1a⟩⟩
    · left; right; exact ⟨hsl1, Or.inr ⟨hcov1b ▸ hu1b, hf1b⟩⟩
    · right; exact ⟨hsl2, hcov2 ▸ hu2, hf2⟩
  · rintro ⟨da, hda, db, hdb, hab, op, hop, ⟨⟨hw0, hwdm⟩, hnw⟩, hfx⟩
    refine ⟨da, hda, db, hdb, hab, op, hop, ?_⟩
    set pz := (opP mp op da.2.1 db.2.1, opP mp op da.2.2 db.2.2)
    set dw := (opD dm op da.1 db.1, pz)
    set ra := dws.erase da
    set r := ra.erase db
    have hp : dws.Perm (da :: db :: r) := (List.perm_cons_erase hda).trans (List.Perm.cons _ (List.perm_cons_erase hdb))
    have hc2 := cov3_perm mp (!u) hp
    have hca := cov3_perm mp (!u) (hp.trans (List.Perm.swap _ _ _))
    have hcov0 : (takeTwo (cov3 mp (!u) dws) (colB mp (!u) da.2) (colB mp (!u) db.2) ||| colB mp (!u) pz == mp) =
        coversD u mp (dw :: r) := by rw [hc2, takeTwo_eq]; exact cov3_coversD u mp dw r
    have hcov1a : (takeOne (cov3 mp (!u) dws) (colB mp (!u) db.2) ||| colB mp (!u) pz == mp) =
        coversD u mp (dw :: da :: r) := by rw [hca, takeOne_eq]; exact cov3_coversD u mp dw (da :: r)
    have hcov1b : (takeOne (cov3 mp (!u) dws) (colB mp (!u) da.2) ||| colB mp (!u) pz == mp) =
        coversD u mp (dw :: db :: r) := by rw [hc2, takeOne_eq]; exact cov3_coversD u mp dw (db :: r)
    have hcov2 : ((cov3 mp (!u) dws).1 ||| colB mp (!u) pz == mp) =
        coversD u mp (dw :: da :: db :: r) := by rw [hc2]; exact cov3_coversD u mp dw (da :: db :: r)
    rcases hfx with (⟨hc0, hg0⟩ | ⟨hsl1, ⟨hc1a, hg1a⟩ | ⟨hc1b, hg1b⟩⟩) | ⟨hsl2, hc2', hg2⟩
    · have u0 : (takeTwo (cov3 mp (!u) dws) (colB mp (!u) da.2) (colB mp (!u) db.2) ||| colB mp (!u) pz == mp) = true := hcov0.symm ▸ hc0
      exact ⟨Or.inl (Or.inl (Or.inl u0)), ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inl (Or.inl (Or.inl ⟨u0, hg0⟩))⟩
    · have u1a : (takeOne (cov3 mp (!u) dws) (colB mp (!u) db.2) ||| colB mp (!u) pz == mp) = true := hcov1a.symm ▸ hc1a
      exact ⟨Or.inl (Or.inl (Or.inr ⟨hsl1, u1a⟩)), ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inl (Or.inl (Or.inr ⟨⟨hsl1, u1a⟩, hg1a⟩))⟩
    · have u1b : (takeOne (cov3 mp (!u) dws) (colB mp (!u) da.2) ||| colB mp (!u) pz == mp) = true := hcov1b.symm ▸ hc1b
      exact ⟨Or.inl (Or.inr ⟨hsl1, u1b⟩), ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inl (Or.inr ⟨⟨hsl1, u1b⟩, hg1b⟩)⟩
    · have u2 : ((cov3 mp (!u) dws).1 ||| colB mp (!u) pz == mp) = true := hcov2.symm ▸ hc2'
      exact ⟨Or.inr ⟨hsl2, u2⟩, ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inr ⟨⟨hsl2, u2⟩, hg2⟩⟩

def bar (u : Bool) (dm Y : Nat) (mp : Nat)
    (SD : Nat → Nat → List (Nat × Nat × Nat)) (S : Nat → Nat → List Nat)
    (N : Nat → Nat) (htAt idxH : Nat → Nat → Nat)
    (ori : List Nat → List Nat) (seed : Nat) (pool : List Nat) (cutHitH : Nat → Nat → List Nat → Bool) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [Y])
  | s + 1, i =>
    let dws := SD (s + 1) i
    !(nextD_cov u dm mp (s + 2 - dws.length) dws fun dzs =>
        let zs := dzs.map Prod.fst
        !(scr u dm Y s pool zs) &&
        (let cz := ori zs
         let h := hk seed cz
         !(cutHitH s h cz) && !(foundH S N htAt idxH s h cz)))

theorem bar_all {u : Bool} {dm T : Nat} {pairs : List (Nat × Nat)} {r1s r2s mp SD S N htAt idxH ori seed pool cutHitH cap}
    (hd : dm &&& mask256 = dm)
    (hr1_eq : r1s = pairs.map Prod.fst) (hr2_eq : r2s = pairs.map Prod.snd) (hmp_eq : mp = maskP pairs.length)
    (hSD : ∀ s j, SD s j = (S s j).map (fun w => (w, projBit r1s w, projBit r2s w)))
    (hpairs : pairs.all (fun p => dm.testBit p.1 && dm.testBit p.2 && !(T &&& dm).testBit p.1 && (T &&& dm).testBit p.2) = true)
    (hr : ∀ {v ys}, RunD u dm (T &&& dm) v ys → RunD u dm (T &&& dm) v (ori ys))
    (hcut : ∀ {v ys}, cutHitH v (hk seed ys) ys = true → ¬ RunD u dm (T &&& dm) v ys)
    (hc : ∀ s ≤ cap, ∀ i < N s, bar u dm (T &&& dm) mp SD S N htAt idxH ori seed pool cutHitH s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ RunD u dm (T &&& dm) s (S s i) := by
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
        coversP u pairs zs && !(scr u dm (T &&& dm) s pool zs) &&
        (let cz := ori zs
         let h := hk seed cz
         !(cutHitH s h cz) && !(foundH S N htAt idxH s h cz))
      have hF (zs) (hz : RunD u dm (T &&& dm) s zs) : F zs = true := by
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
      rw [hSD, List.length_map, nextD_cov_eq, nextD_decor_eq u hd pairs hr1 hr2] at hb
      have hFeq : (fun zs => coversD u (maskP pairs.length) (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))) &&
          (let zs' := (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))).map Prod.fst
           !(scr u dm (T &&& dm) s pool zs') &&
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

theorem pickMin_runD {u : Bool} {dm Y v} (seed : Nat) (orig : List Nat) (h0 : RunD u dm Y v orig) :
    ∀ (syms : List (List (Nat × Nat))) (best : List Nat) (bestH : Nat),
      syms.all (fun ms => ms.all moveOK256 && (applyMoves ms dm == dm) && (applyMoves ms Y == Y)) = true →
      RunD u dm Y v best →
      RunD u dm Y v (pickMin seed orig syms best bestH)
  | [], _, _, _, hb => hb
  | ms :: rest, best, bestH, hok, hb => by
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at hok
    unfold pickMin; dsimp only; split
    · exact pickMin_runD seed orig h0 rest _ _ hok.2 (applyMoves_runD ms hok.1.1.1 hok.1.1.2 hok.1.2 h0)
    · exact pickMin_runD seed orig h0 rest best bestH hok.2 hb

-- Bridge: directSplit!
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

def isNotGate (g : Gate) : Bool := match g.op with | .not => true | _ => false

theorem execN_reach (u : Bool) (gs : List Gate) (roots : List Nat)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hmono : u = false → ∀ g ∈ gs, isNotGate g = false) :
    ∀ (p : Nat) (w bank : List Nat), NatReach u mask256 roots p bank →
      (∀ v ∈ w, Avail u mask256 bank v) →
      ∃ p' bank', p' ≤ p + gs.countP (fun g => !isNotGate g) ∧ NatReach u mask256 roots p' bank' ∧
        ∀ v ∈ execN gs w, Avail u mask256 bank' v := by
  have hm256 : mask256 &&& mask256 = mask256 := Nat.and_self _
  induction gs with
  | nil => intro p w bank hr hsup; exact ⟨p, bank, by simp, hr, hsup⟩
  | cons g gs ih =>
    intro p w bank hr hsup
    have hav_gd : ∀ i, Avail u mask256 bank (w.getD i 0) := by
      intro i; by_cases hi : i < w.length
      · exact hsup _ (getD_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
    have hstep : ∃ p1 bank1, p1 ≤ p + (if !isNotGate g then 1 else 0) ∧ NatReach u mask256 roots p1 bank1 ∧
        (∀ v ∈ w ++ [gvN w g], Avail u mask256 bank1 v) := by
      have hg := hfan g List.mem_cons_self
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      obtain ⟨hop, hlen⟩ := hg
      have hand_m : ∀ a, andD mask256 a mask256 &&& mask256 = a &&& mask256 := fun a => by
        simp [andD, Nat.and_assoc, Nat.and_self]
      have hor_0 : ∀ a, orD mask256 a 0 &&& mask256 = a &&& mask256 := fun a => by
        simp [orD, Nat.and_assoc, Nat.and_self]
      have lift_w : ∀ z, (∀ v ∈ w, Avail u mask256 (z :: bank) v) := fun z v hv => avail_cons z v (hsup v hv)
      rcases hop with h | h | h
      · have hn : (!isNotGate g) = true := by simp [isNotGate, h]
        rw [hn]; simp only [ite_true]
        rcases hgi : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inr (by simp [gvN, h, hgi]))⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi, List.foldr_cons, List.foldr_nil]
              exact avail_of_eq (hand_m _).symm (hav_gd i)⟩
        · refine ⟨p + 1, opD mask256 0 (w.getD i 0) (w.getD j 0) :: bank, le_rfl,
            ⟨bank, _, _, 0, by simp [allowedB], rfl, hr, hav_gd i, hav_gd j⟩, fun v hv => ?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi, List.foldr_cons, List.foldr_nil]
            exact Or.inr (Or.inl ⟨_, List.mem_cons_self, by simp [opD, andD, Nat.and_assoc, Nat.and_self]⟩)
        · rw [hgi] at hlen; simp at hlen
      · have hn : (!isNotGate g) = true := by simp [isNotGate, h]
        rw [hn]; simp only [ite_true]
        rcases hgi : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inl (by simp [gvN, h, hgi]))⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi, List.foldr_cons, List.foldr_nil]
              exact avail_of_eq (hor_0 _).symm (hav_gd i)⟩
        · refine ⟨p + 1, opD mask256 1 (w.getD i 0) (w.getD j 0) :: bank, le_rfl,
            ⟨bank, _, _, 1, by simp [allowedB], rfl, hr, hav_gd i, hav_gd j⟩, fun v hv => ?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi, List.foldr_cons, List.foldr_nil]
            exact Or.inr (Or.inl ⟨_, List.mem_cons_self, by apply Nat.eq_of_testBit_eq; intro r; simp [opD, orD]; cases mask256.testBit r <;> simp⟩)
        · rw [hgi] at hlen; simp at hlen
      · cases u with
        | false =>
          have hbad := hmono rfl g List.mem_cons_self
          simp [isNotGate, h] at hbad
        | true =>
          have hn : (!isNotGate g) = false := by simp [isNotGate, h]
          rw [hn]; simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
          rcases hgi : g.inputs with _ | ⟨i, l⟩
          · exact ⟨p, bank, le_rfl, hr, fun v hv => by
              rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
              · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inr (by simp [gvN, h, hgi]))⟩
          · exact ⟨p, bank, le_rfl, hr, fun v hv => by
              rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
              · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi]
                exact avail_neg hm256 (hav_gd i)⟩
    obtain ⟨p1, bank1, hp1, hr1, hsup1⟩ := hstep
    obtain ⟨p2, bank2, hp2, hr2, hsup2⟩ := ih (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))
      (fun hu g' hg' => hmono hu g' (List.mem_cons_of_mem _ hg')) p1 _ bank1 hr1 hsup1
    rw [List.countP_cons]
    cases hb : !isNotGate g <;> simp only [hb, ite_true, Bool.false_eq_true, ite_false] at hp1 ⊢ <;>
      exact ⟨p2, bank2, by omega, hr2, hsup2⟩

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

theorem countP_not_lt {gs : List Gate} {g : Gate} (hg : g ∈ gs) (hn : isNotGate g = true) :
    gs.countP (fun x => !isNotGate x) + 1 ≤ gs.length := by
  induction gs with
  | nil => simp at hg
  | cons x xs ih =>
    rw [List.countP_cons, List.length_cons]
    rcases List.mem_cons.1 hg with rfl | hxs
    · simp only [hn, Bool.not_true, Bool.false_eq_true, ite_false]
      have := List.countP_le_length (p := fun y => !isNotGate y) (l := xs); omega
    · have := ih hxs; cases hb : !isNotGate x <;> simp only [hb, ite_true, Bool.false_eq_true, ite_false] <;> omega

theorem directSplit_to_circuit (f : (Fin 8 → Bool) → Bool) (T lb : Nat)
    (hT : ∀ r : Fin 256, T.testBit r.val = f (pt8 r.val))
    (hS : Lower true mask256 xs256 T (lb - 1))
    (hM : Lower false mask256 xs256 T lb) :
    ∀ t : ℕ, HasCircuitSize 8 f t → lb ≤ t := by
  rintro t ⟨C, hfan, hsz, hev⟩
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
  by_cases hhas : ∃ g ∈ C.gates, isNotGate g = true
  · obtain ⟨g, hg, hgn⟩ := hhas
    have hsup0 : ∀ v ∈ xs256, Avail true mask256 xs256 v := fun v hv => Or.inr (Or.inl ⟨v, hv, rfl⟩)
    obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach true C.gates xs256 hfan (fun h => Bool.noConfusion h) 0 xs256 xs256 rfl hsup0
    have hav_out : Avail true mask256 bank ((execN C.gates xs256).getD C.output 0) := by
      by_cases hi : C.output < (execN C.gates xs256).length
      · exact hsup _ (getD_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
    have hL := hS p bank hr (avail_of_eq hout hav_out)
    have hlt := countP_not_lt hg hgn
    have : C.gates.length ≤ t := hsz
    omega
  · push_neg at hhas
    have hmono : ∀ g ∈ C.gates, isNotGate g = false := fun g hg => Bool.eq_false_iff.2 (hhas g hg)
    have hsup0 : ∀ v ∈ xs256, Avail false mask256 xs256 v := fun v hv => Or.inr (Or.inl ⟨v, hv, rfl⟩)
    obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach false C.gates xs256 hfan (fun _ => hmono) 0 xs256 xs256 rfl hsup0
    have hav_out : Avail false mask256 bank ((execN C.gates xs256).getD C.output 0) := by
      by_cases hi : C.output < (execN C.gates xs256).length
      · exact hsup _ (getD_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
    have hL := hM p bank hr (avail_of_eq hout hav_out)
    have hle := List.countP_le_length (p := fun y => !isNotGate y) (l := C.gates)
    have : C.gates.length ≤ t := hsz
    omega

def dom_27 : Nat := 0xf0f0f0f
def goal_27 : Nat := 0xeeaaaa00eeaaaa00eeaaaa00eeaaaa00eeaaaa00eeaaaa00eeaaaa00eeaaaa00
def roots_27 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_29 : Nat := 0x33333333
def goal_29 : Nat := 0xfaaaaa00faaaaa00faaaaa00faaaaa00faaaaa00faaaaa00faaaaa00faaaaa00
def roots_29 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_30 : Nat := 0x55555555
def goal_30 : Nat := 0xfcc0c0c0fcc0c0c0fcc0c0c0fcc0c0c0fcc0c0c0fcc0c0c0fcc0c0c0fcc0c0c0
def roots_30 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_31 : Nat := 0xffffffff
def goal_31 : Nat := 0xfeeaeac0feeaeac0feeaeac0feeaeac0feeaeac0feeaeac0feeaeac0feeaeac0
def roots_31 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_45 : Nat := 0x333300003333
def goal_45 : Nat := 0xfaaafaaaaa00aa00faaafaaaaa00aa00faaafaaaaa00aa00faaafaaaaa00aa00
def roots_45 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xfaeafaeaeac0eac0faeafaeaeac0eac0faeafaeaeac0eac0faeafaeaeac0eac0
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_51 : Nat := 0xf000f000f000f
def goal_51 : Nat := 0xeeeeaaaaaaaa0000eeeeaaaaaaaa0000eeeeaaaaaaaa0000eeeeaaaaaaaa0000
def roots_51 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xeeeeeaeaeaeac0c0eeeeeaeaeaeac0c0eeeeeaeaeaeac0c0eeeeeaeaeaeac0c0
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xeeeeaaaaeeaaaa00eeeeaaaaeeaaaa00eeeeaaaaeeaaaa00eeeeaaaaeeaaaa00
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfaaafaaafaaaaa00faaafaaafaaaaa00faaafaaafaaaaa00faaafaaafaaaaa00
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_62 : Nat := 0x5555555555555555
def goal_62 : Nat := 0xfcccf0c0fcc0c0c0fcccf0c0fcc0c0c0fcccf0c0fcc0c0c0fcccf0c0fcc0c0c0
def roots_62 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfeeefaeafeeaeac0feeefaeafeeaeac0feeefaeafeeaeac0feeefaeafeeaeac0
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

namespace S_27
def pairsG : List (Nat × Nat) := [(1, 9), (1, 17), (3, 11), (3, 19), (8, 9), (10, 11), (10, 26), (16, 17), (18, 19), (18, 26), (24, 25), (24, 26)]
def r1sG : List Nat := [1, 1, 3, 3, 8, 10, 10, 16, 18, 18, 24, 24]
def r2sG : List Nat := [9, 17, 11, 19, 9, 11, 26, 17, 19, 26, 25, 26]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_27.map (· &&& dom_27)
def goalM : Nat := goal_27 &&& dom_27
def NN : Nat → Nat
  | 2 => 2
  | 3 => 5
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x6a2e46a60051f16d
  | 3, 0 => 0x9d277db19c07f42f498c75643e65793b2668f2b2
  | 4, 0 => 0x9d277db1
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x3030000000000000000000000000000000000000000000000000000000000000c0c0000000000000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000e0e0e0e000000000000000000000000000000000000000000000000000000000c0f0000000000000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000e0e0000000000000000000000000000000000000000000000000000000000000a0a0a0a
  | 0, 1 => 0xc0c0c0c0000000000000000000000000000000000000000000000000000000004040404
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x23032103
  | 3, 0, 0 => 0x5290452084520745260452404
  | 4, 0, 0 => 0x52904
  | _, _, _ => 0
def stateW : Nat → Nat
  | 2 => 16
  | 3 => 20
  | 4 => 20
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xc80300f8036f380c7030000f
  | 0, 1 => 0x36c360
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x482b48fcafffbcae75fca5bf
  | 0, 1 => 0xb6ca40
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 12 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 12 (i % 8)
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
def CN0 : Nat → Nat
  | _ => 0
def CH0 : Nat → Nat → Nat
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 1 0 (CN0 s)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_27 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 12 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_27 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_27 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_27 == dom_27) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_27 goalM v ys) : RunD true dom_27 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_27 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z2 : ∀ i, 0 ≤ i → i < 2 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 2 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 5 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 5 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 4) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_27 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD true dom_27 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_27 roots_27 goal_27 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_27 goal_27 := by
    have h0 : isConstB dom_27 goal_27 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hnc hr ha
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
    rw [proper_failG zs (List.mem_sublists.2 hsub) heq] at hcov; contradiction

end S_27

theorem lowS_27 : Lower true dom_27 roots_27 goal_27 5 := S_27.noCircuit

namespace S_29
def pairsG : List (Nat × Nat) := [(1, 9), (1, 17), (5, 13), (5, 21), (8, 9), (12, 13), (12, 28), (16, 17), (20, 21), (20, 28), (24, 25), (24, 28)]
def r1sG : List Nat := [1, 1, 5, 5, 8, 12, 12, 16, 20, 20, 24, 24]
def r2sG : List Nat := [9, 17, 13, 21, 9, 13, 28, 17, 21, 28, 25, 28]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_29.map (· &&& dom_29)
def goalM : Nat := goal_29 &&& dom_29
def NN : Nat → Nat
  | 2 => 2
  | 3 => 5
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x7e74075e778914c1
  | 3, 0 => 0xe1d5fc9486580566576a1e27134890b10b4ff38e
  | 4, 0 => 0x86580566
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x323232320000000000000000000000000000000000000000000000000000000003000300000000000000000000000000000000000000000000000000000000003030000000000000000000000000000000000000000000000000000000000000330033000000000000000000000000000000000000000000000000000000000032320000000000000000000000000000000000000000000000000000000000003333000000000000000000000000000000000000000000000000000000000000300033000000000000000000000000000000000000000000000000000000000022222222
  | 0, 1 => 0x101010100000000000000000000000000000000000000000000000000000000030303030
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x43032103
  | 3, 0, 0 => 0x2409424804247042406424504
  | 4, 0, 0 => 0x24804
  | _, _, _ => 0
def stateW : Nat → Nat
  | 2 => 16
  | 3 => 20
  | 4 => 20
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x36fc10300c70300f8007000f
  | 0, 1 => 0x36036c
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfff411b48e75fcafcaa755bf
  | 0, 1 => 0xa40b6c
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 12 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 12 (i % 8)
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
def CN0 : Nat → Nat
  | _ => 0
def CH0 : Nat → Nat → Nat
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 1 0 (CN0 s)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_29 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 12 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_29 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_29 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_29 == dom_29) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_29 goalM v ys) : RunD true dom_29 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_29 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z2 : ∀ i, 0 ≤ i → i < 2 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 2 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 5 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 5 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 4) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_29 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD true dom_29 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_29 roots_29 goal_29 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_29 goal_29 := by
    have h0 : isConstB dom_29 goal_29 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hnc hr ha
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
    rw [proper_failG zs (List.mem_sublists.2 hsub) heq] at hcov; contradiction

end S_29

theorem lowS_29 : Lower true dom_29 roots_29 goal_29 5 := S_29.noCircuit

namespace S_30
def pairsG : List (Nat × Nat) := [(2, 6), (4, 6), (10, 14), (10, 26), (12, 14), (12, 28), (18, 22), (18, 26), (20, 22), (20, 28), (24, 26), (24, 28)]
def r1sG : List Nat := [2, 4, 10, 10, 12, 12, 18, 18, 20, 20, 24, 24]
def r2sG : List Nat := [6, 6, 14, 26, 14, 28, 22, 26, 22, 28, 26, 28]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_30.map (· &&& dom_30)
def goalM : Nat := goal_30 &&& dom_30
def NN : Nat → Nat
  | 2 => 1
  | 3 => 4
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0xe65a0c41
  | 3, 0 => 0xe65a0c41e17a4c91aa0e4f0b36044e10
  | 4, 0 => 0xe17a4c91
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x5555000000000000000000000000000000000000000000000000000000000000000055000000000000000000000000000000000000000000000000000000000055005500000000000000000000000000000000000000000000000000000000005500000000000000000000000000000000000000000000000000000000000000505050500000000000000000000000000000000000000000000000000000000044444444
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x883
  | 3, 0, 0 => 0x883ac8464446884
  | 4, 0, 0 => 0xac84
  | _, _, _ => 0
def stateW : Nat → Nat
  | 2 => 13
  | 3 => 16
  | 4 => 16
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xfc003cc3cc003320cd
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfe8014ebcea8b775df
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 12 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 12 (i % 8)
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 4 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN0 : Nat → Nat
  | _ => 0
def CH0 : Nat → Nat → Nat
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 1 0 (CN0 s)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_30 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 12 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_30 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_30 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_30 == dom_30) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_30 goalM v ys) : RunD true dom_30 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_30 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 4 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 4 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 4) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_30 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD true dom_30 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_30 roots_30 goal_30 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_30 goal_30 := by
    have h0 : isConstB dom_30 goal_30 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hnc hr ha
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
    rw [proper_failG zs (List.mem_sublists.2 hsub) heq] at hcov; contradiction

end S_30

theorem lowS_30 : Lower true dom_30 roots_30 goal_30 5 := S_30.noCircuit

namespace S_45
def pairsG : List (Nat × Nat) := [(1, 9), (1, 33), (5, 13), (5, 37), (8, 9), (12, 13), (12, 44), (32, 33), (36, 37), (36, 44), (40, 41), (40, 44)]
def r1sG : List Nat := [1, 1, 5, 5, 8, 12, 12, 32, 36, 36, 40, 40]
def r2sG : List Nat := [9, 33, 13, 37, 9, 13, 44, 33, 37, 44, 41, 44]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_45.map (· &&& dom_45)
def goalM : Nat := goal_45 &&& dom_45
def NN : Nat → Nat
  | 2 => 2
  | 3 => 5
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x2816da4b155a83ce
  | 3, 0 => 0xc79261eb90d2d75078a0c4e53db6e9743a35fac6
  | 4, 0 => 0x90d2d750
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x300000003000000000000000000000000000000000000000000000000000000323200003232000000000000000000000000000000000000000000000000000030000000300000000000000000000000000000000000000000000000000000003333000000000000000000000000000000000000000000000000000000000000300000003300000000000000000000000000000000000000000000000000000033000000330000000000000000000000000000000000000000000000000000003232000000000000000000000000000000000000000000000000000000000000222200002222
  | 0, 1 => 0x1010000010100000000000000000000000000000000000000000000000000000303000003030
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x43032103
  | 3, 0, 0 => 0x4209442804420744260442504
  | 4, 0, 0 => 0x42804
  | _, _, _ => 0
def stateW : Nat → Nat
  | 2 => 16
  | 3 => 20
  | 4 => 20
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xc1036f060f80070c7030000f
  | 0, 1 => 0x36036c
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x411fffa64fcaa75e75fca5bf
  | 0, 1 => 0xa40b6c
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 12 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 12 (i % 8)
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
def CN0 : Nat → Nat
  | _ => 0
def CH0 : Nat → Nat → Nat
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 1 0 (CN0 s)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_45 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 12 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_45 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_45 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_45 == dom_45) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_45 goalM v ys) : RunD true dom_45 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_45 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z2 : ∀ i, 0 ≤ i → i < 2 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 2 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 5 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 5 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 4) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_45 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD true dom_45 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_45 roots_45 goal_45 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_45 goal_45 := by
    have h0 : isConstB dom_45 goal_45 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hnc hr ha
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
    rw [proper_failG zs (List.mem_sublists.2 hsub) heq] at hcov; contradiction

end S_45

theorem lowS_45 : Lower true dom_45 roots_45 goal_45 5 := S_45.noCircuit

namespace S_51
def pairsG : List (Nat × Nat) := [(1, 17), (1, 33), (3, 19), (3, 35), (16, 17), (18, 19), (18, 50), (32, 33), (34, 35), (34, 50), (48, 49), (48, 50)]
def r1sG : List Nat := [1, 1, 3, 3, 16, 18, 18, 32, 34, 34, 48, 48]
def r2sG : List Nat := [17, 33, 19, 35, 17, 19, 50, 33, 35, 50, 49, 50]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_51.map (· &&& dom_51)
def goalM : Nat := goal_51 &&& dom_51
def NN : Nat → Nat
  | 2 => 2
  | 3 => 5
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x889722ac5c00296f
  | 3, 0 => 0xc3ccb8c4b50978168608439e33c1537129c5ac2a
  | 4, 0 => 0x29c5ac2a
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x3000300000000000000000000000000000000000000000000000000000000000c000c00000000000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000c000c000c000c000000000000000000000000000000000000000000000000000c000f00000000000000000000000000000000000000000000000000000000000f0000000f0000000000000000000000000000000000000000000000000000000e000e00000000000000000000000000000000000000000000000000000000000a000a000a000a
  | 0, 1 => 0xe000e000e000e0000000000000000000000000000000000000000000000000004000400040004
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x23032103
  | 3, 0, 0 => 0x5290452084520745260452404
  | 4, 0, 0 => 0x52404
  | _, _, _ => 0
def stateW : Nat → Nat
  | 2 => 16
  | 3 => 20
  | 4 => 20
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xc80300f8036c380c7030000f
  | 0, 1 => 0x36f360
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x482b48fcab6cbcae75fca5bf
  | 0, 1 => 0xfffa40
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 12 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 12 (i % 8)
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
def CN0 : Nat → Nat
  | _ => 0
def CH0 : Nat → Nat → Nat
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 1 0 (CN0 s)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_51 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 12 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_51 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_51 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_51 == dom_51) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_51 goalM v ys) : RunD true dom_51 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_51 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z2 : ∀ i, 0 ≤ i → i < 2 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 2 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 5 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 5 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 4) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_51 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD true dom_51 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_51 roots_51 goal_51 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_51 goal_51 := by
    have h0 : isConstB dom_51 goal_51 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hnc hr ha
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
    rw [proper_failG zs (List.mem_sublists.2 hsub) heq] at hcov; contradiction

end S_51

theorem lowS_51 : Lower true dom_51 roots_51 goal_51 5 := S_51.noCircuit

namespace S_31
def pairsG : List (Nat × Nat) := [(1, 9), (1, 17), (2, 6), (3, 7), (3, 11), (3, 19), (4, 6), (5, 7), (5, 13), (5, 21), (8, 9), (10, 11), (10, 14), (10, 26), (12, 13), (12, 14), (12, 28), (16, 17), (18, 19), (18, 22), (18, 26), (20, 21), (20, 22), (20, 28), (24, 25), (24, 26), (24, 28)]
def r1sG : List Nat := [1, 1, 2, 3, 3, 3, 4, 5, 5, 5, 8, 10, 10, 10, 12, 12, 12, 16, 18, 18, 18, 20, 20, 20, 24, 24, 24]
def r2sG : List Nat := [9, 17, 6, 7, 11, 19, 6, 7, 13, 21, 9, 11, 14, 26, 13, 14, 28, 17, 19, 22, 26, 21, 22, 28, 25, 26, 28]
def mpG : Nat := 0x7ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_31.map (· &&& dom_31)
def goalM : Nat := goal_31 &&& dom_31
def NN : Nat → Nat
  | 3 => 8
  | 4 => 39
  | 5 => 68
  | 6 => 10
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xe67083b8cf6347c0c04acc416fe876795cad29d21c77b5a00d9fcf8304791816
  | 4, 0 => 0xe67083b8dd6ee4f5d3392061d2b24f45d201ca2dce52c4faadfe94f5abea8af4a82d0d83a48043759fd9f58b9eb332a99a0787bf954bc44b8363db4a813e571a7d385bc17225db9b70e143926d17994e645efea857bce4bc4fc7e1b54ee139413fec512f36eb5069360db4013348542720f514d61c77b5a019ec9f2017273acf11f747091078bbb50cc5ee85091950bf087b1dd703d1c14500d6aac4
  | 5, 0 => 0xd201ca2dce52c4fac6a4dd9cbb6d5d4fb7ae5bedb58372c9abea8af4aacb8ff0a7a82bab966897d68860987f86981ddb7d2e058d77f7b44a74833b71712a8d656f92c96d6b1cb35a5db722105cf6f3ef5ac5cb8758fdc3c454b1cb12518b59704e9ea6914c1113e34a4e74df4188c1e53f4a3df73f1826db3d9291d5391cb6162f61f1a42beef5472b2489912ae9b58328c7924328ae69ed2806214e25bdec56241cb7b2239c8e7021109d8a20f514d620d08b5f1b035802197bee9417f89e001616dc9b15b639331495c9760d7a72cd0d2b81f70c1d77ec0a8ea06009a0ff5b0728aace05f43a9b055409fa043b779204362bd2042f0bce017db7bb0046f4b6
  | 5, 1 => 0xf0fb9201e80a975fe4f3c2c9d5d7a2ce
  | 6, 0 => 0xd5d7a2ceaacb8ff0974979bd6ec079dc2c56ab271f16380d1495c9760d59fc0a09e2bbbd090d6eb4
  | 7, 0 => 0x1f16380d
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffff0000000000000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000fafa000000000000000000000000000000000000000000000000000000000000ccccc0c000000000000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000cccccccc00000000000000000000000000000000000000000000000000000000aaffff0000000000000000000000000000000000000000000000000000000000aaaaaaaa
  | 0, 1 => 0xff0000000000000000000000000000000000000000000000000000000000ff000000000000000000000000000000000000000000000000000000000000005555550000000000000000000000000000000000000000000000000000000000aaaaaa0000000000000000000000000000000000000000000000000000000000aaffaa00000000000000000000000000000000000000000000000000000000005555000000000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000aa55aa00
  | 0, 2 => 0xaaaaff0000000000000000000000000000000000000000000000000000000000ffffcccc00000000000000000000000000000000000000000000000000000000eeee0000000000000000000000000000000000000000000000000000000000003332333200000000000000000000000000000000000000000000000000000000ffff55000000000000000000000000000000000000000000000000000000000000ff000000000000000000000000000000000000000000000000000000000000ff00ee0000000000000000000000000000000000000000000000000000000000ffaa0000
  | 0, 3 => 0xfefe00000000000000000000000000000000000000000000000000000000cccccfcc00000000000000000000000000000000000000000000000000000000fafafafa00000000000000000000000000000000000000000000000000000000ffff030000000000000000000000000000000000000000000000000000000000ffffff000000000000000000000000000000000000000000000000000000000055005500000000000000000000000000000000000000000000000000000000005555554400000000000000000000000000000000000000000000000000000000ff00aa00
  | 0, 4 => 0x33333330000000000000000000000000000000000000000000000000000000000f0c0c0c0000000000000000000000000000000000000000000000000000000000ff00ee00000000000000000000000000000000000000000000000000000000fefe000000000000000000000000000000000000000000000000000000000000f0c0f0c0000000000000000000000000000000000000000000000000000000003300330000000000000000000000000000000000000000000000000000000000fcff00000000000000000000000000000000000000000000000000000000000031303130
  | 0, 5 => 0x3333000000000000000000000000000000000000000000000000000000000000ffffffaa00000000000000000000000000000000000000000000000000000000f5f5f0f000000000000000000000000000000000000000000000000000000000ffff0f00000000000000000000000000000000000000000000000000000000005500000000000000000000000000000000000000000000000000000000000000ff00aaaa00000000000000000000000000000000000000000000000000000000ffaaaaaa00000000000000000000000000000000000000000000000000000000aa00ff00
  | 0, 6 => 0xffaaffaa000000000000000000000000000000000000000000000000000000000000ffaa000000000000000000000000000000000000000000000000000000003333303000000000000000000000000000000000000000000000000000000000ccffcccc00000000000000000000000000000000000000000000000000000000afafaaaa00000000000000000000000000000000000000000000000000000000fcfc000000000000000000000000000000000000000000000000000000000000fffff0f00000000000000000000000000000000000000000000000000000000033000000
  | 0, 7 => 0x323232320000000000000000000000000000000000000000000000000000000000ee00ee00000000000000000000000000000000000000000000000000000000fffffff00000000000000000000000000000000000000000000000000000000000fc00fc000000000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000005555505000000000000000000000000000000000000000000000000000000000fff0fff00000000000000000000000000000000000000000000000000000000033332222
  | 0, 8 => 0xfffafffa00000000000000000000000000000000000000000000000000000000fff0000000000000000000000000000000000000000000000000000000000000ffcccccc00000000000000000000000000000000000000000000000000000000333333000000000000000000000000000000000000000000000000000000000005000500000000000000000000000000000000000000000000000000000000003330333000000000000000000000000000000000000000000000000000000000ffccffcc000000000000000000000000000000000000000000000000000000000000ffcc
  | 0, 9 => 0xfffcfffc00000000000000000000000000000000000000000000000000000000fefefefe000000000000000000000000000000000000000000000000000000000303000000000000000000000000000000000000000000000000000000000000f3f0f3f0000000000000000000000000000000000000000000000000000000000000550000000000000000000000000000000000000000000000000000000000ccc0ccc000000000000000000000000000000000000000000000000000000000cc00ff0000000000000000000000000000000000000000000000000000000000000f0000
  | 0, 10 => 0xfcfcfcfc00000000000000000000000000000000000000000000000000000000aaffaaaa00000000000000000000000000000000000000000000000000000000545454540000000000000000000000000000000000000000000000000000000000ff00aa00000000000000000000000000000000000000000000000000000000ff55ff0000000000000000000000000000000000000000000000000000000000ffffaaaa00000000000000000000000000000000000000000000000000000000fa00fa0000000000000000000000000000000000000000000000000000000000eeeeeeee
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x1c0c10c40608687406086074060858a4120c1084060800740c14200406080804
  | 4, 0, 0 => 0x121819e00a2431d08014e060608029b060851a5121818232a24c030401400304003a060608b8052c1819500a0c1000e3d44860600a2930c0c10a5120c10c24a248830401480304007a8606080075
  | 4, 0, 1 => 0x6080121ea6c182001d418200a092900c0c11a512181804ea6c8030401448e060862890c08026536381821aa2418200954d8e06086286480c1005121918044a190830401448606010286060801f5
  | 4, 0, 2 => 0x70304310d8304015a8e060800750ca818200a2430304354d8e0608029b520c1005
  | 5, 0, 0 => 0x362418200699b86060803661218182003d848606080356121818200a183030400512612181b40401848606099806121990304019886060802f61218c0304018486060803062c2430300bd97090c0c10061219683040196090c0c1006
  | 5, 0, 1 => 0x1218182010d84b90c0c042612e60830401800606080365121818201018486060803f6121818200f99e890c0c1006121818200f1830304017bb6121818200e98009300c1005002430300d544b7060800f612e431d0401848606080386
  | 5, 0, 2 => 0x121a70304018486060804d6362430304358486980c1006120c100243d8486060804b612e43039401830e06080126362430304318486060a48061218182012184c70c0c10061318303040184c50c0c100612181821469848606080446
  | 5, 0, 3 => 0x243030435401b1c0c100512181820155a909300c10061218182015184a90c0c1006000c100243d4d890c0c1006134c30304018dd20c0c1006a42430304298486a20c10063624703040184863a0e80261218182003584cf0c0c1006
  | 5, 0, 4 => 0x362418200498486060ab006121818200ad84861c0c1006
  | 6, 0, 0 => 0x121870304018d890c0c1006121ab8304018486060801a6121818200bd80090c0c10051218182003d84860740100612dc303040184b90c0c1006
  | 7, 0, 0 => 0x90c0c1005
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 32
  | 4 => 39
  | 5 => 46
  | 6 => 46
  | 7 => 39
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x1fff801c07f00070000001c00001c38780070e0f07ffe0000003bb
  | 0, 1 => 0x3f801c000003fffe0000000001fc0001ff80003ff00000fe0000
  | 0, 2 => 0x3f801ff8e0f00e00007e1c7c3ffff8003f80003801c007000000
  | 0, 3 => 0x3f7fe070f0f070e1fdffe0400ffff801c07f003fffe027000000
  | 0, 4 => 0xfc78f81c70e0f07f01df8fc00000038001c0710007f00007e1c7c0
  | 0, 5 => 0xfc40001ffffeefffe1e07fe3c00e000001c000eef8001dd801fc00
  | 0, 6 => 0xe03ff76007feeff1e1e00fe383ce3c07763f00003ffe1e07000000
  | 0, 7 => 0x1c387860700effffffe00fc03fce3c0001fff0103f0ffe07e20383
  | 0, 8 => 0xfc3fff7f8000038e1c1e7e3c400e007801f871f038efe1e001fc3c
  | 0, 9 => 0xffbfff83f7efff8100007e1c7c0003f800000e00000fe0001e0000
  | 0, 10 => 0x1fbf7f83f80eec7efc220fe03bbffff801ff80eec00e00001c3bbf
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xddbe67e47f446f7811125cb0ec9d3a798972e3f0b76f999264fbb
  | 0, 1 => 0x1ba23e4480036cd8001264f332dc9e67b648003ff91111484d11
  | 0, 2 => 0x24dbe67ffeebf9bf11115a34703fff64441b8088bc8fe88fb72222
  | 0, 3 => 0x1bbba972f3f6f7effffff2623ffffe67a46c0036cd8227916d11
  | 0, 4 => 0xb468e06c50a0c03701777ff2222993a39960514077f91114a14300
  | 0, 5 => 0xb460405ffffeef7cf9e67ff2e33d224001e45b667dbb7dd900dd11
  | 0, 6 => 0xf6fff760037666d1a18127ebafe66cdf77bf48883fff9f75810000
  | 0, 7 => 0xb468e061b80bbbffffff86c02ec62c4045b66c113fcffeeda34703
  | 0, 8 => 0xffffffffe48803eedc7e5a3470342040016851c07eefefe800dddd
  | 0, 9 => 0xffbfffbffffffc8100015e9d7cd0012000962e371087e888060022
  | 0, 10 => 0xdfbf7f85b93eef6cd82206e02aafb3fa23ffdbeeec0ee88b7effff
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 27 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 27 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 88 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 88 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 88 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 88 then wireAt i else 0
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 8 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN0 : Nat → Nat
  | 4 => 28
  | 5 => 76
  | 6 => 9
  | _ => 0
def CH0 : Nat → Nat → Nat
  | 4, 0 => 0xc455e448c2e94eaeae865694989ce8d79639b7f079238a6e745f33c174064f5d6efe5e575f4048c9532d61ca4cc4e0614782c8ca472e25f7452bf8d5364724a5360930bc3058653d2f7dd14f2f79e7db2e349b591f16380d1edb554711e3336309b3068005aa645401b535c9005db616
  | 5, 0 => 0x894af9797f482aa17cfbddfb77c3088974e8015f74a13adf745f33c16ec079dc6d3f55556bf2120f69bbe548656abff264ecbd986432baff63da273962bef7746029e0ea5f4048c95bf0f26d581d1172579c512c52b9fb64524d93314d8640f6472e25f744f637be43e31893439f3ded431deb0142f19a6e3f63e2d23ebdd55e3b1e5a1b3b0b22843a3a53b335e7b92134b0cb8f3498462a33d80d65339fd5cb2f7dd14f2c56ab2728d75ccc267fe363249be68621c99be5205f4d0c202fbf561f16380d1e29e5df1c27b8bd16e0a5051437dad4129dfe450f0bfb1b0da5da0f0d59fc0a0cd5b6210a03e2b509e2bbbd090f6918090d6eb40578eca70382e388
  | 5, 1 => 0xee573519c57b2755c3e14ac6c2e94eaeb31a485aa2ce31689f9ebb499d4bf3ff989ce8d7974979bd8d0173dd8a0bf74c
  | 6, 0 => 0xc3e14ac6894af9796432baff579c512c34b0cb8f205f4d0c202fbf561e29e5df129dfe45
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 4, 0 => 0x20000000102000201010101000101000000010102000201
  | 5, 0 => 0x10100020001020001010100000000000000000000010000000001000202000101000001010202020101000001010200000102010100010100000000010100010101020001000002020200
  | 6, 0 => 0x10000020002000101
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 8 0 (CN0 s)
def CN : Nat → Nat
  | 3 => 10
  | 4 => 26
  | 5 => 6
  | _ => 0
def CH : Nat → Nat → Nat
  | 3, 0 => 0xf58ca3b3e0d6d11ac61c53b39012aba284a9e7bb405775792c51c5392aa8201a1fcf804f15eceae4
  | 4, 0 => 0x9ad7a5069ad150299724b8b593f7abf58d2a0fe588f1f4fc8873f2a2825e80c882155f436c37d5ca65ca473e4ad84c9c47a13c50443d9fe3405775793a9e1a41336835f12b034b142ae9b583268d350124b66a9d23ecc35e20d08b5f145bc5c20ce8490709265cbd
  | 5, 0 => 0xcfef4a4f7df7cdf77ae0cda0682835df59362dbb0713412c
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 3, 0 => 0x320c9200320c9200320c9200320c9200320c92000008c10034041201320c920034c872013248c200
  | 4, 0 => 0x8e100000c810000041102000871010008e100320c9200320c92000008410100043101000c8100000c8100000c7101000c8100000c81000008c100000841010004110100041101000ca100000c71010008c100000c8100000c7102000c7102000ca100000cb100
  | 5, 0 => 0xca100000c81000008e100000c710100041102000c8100
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 6 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry true dom_30 roots_30 5 s ws hint
  | 1 => checkCutEntry true dom_29 roots_29 5 s ws hint
  | 2 => checkCutEntry true dom_27 roots_27 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_31 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_30 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_29 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_27 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 32 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_31 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_31 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_31 == dom_31) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_31 goalM v ys) : RunD true dom_31 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_31 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 8 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 39 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 39 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 68 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 68 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 10 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 10 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
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
def RootG (s : Nat) : Bool :=
  scr true dom_31 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD true dom_31 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_31 roots_31 goal_31 8 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_31 goal_31 := by
    have h0 : isConstB dom_31 goal_31 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hnc hr ha
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
    rw [proper_failG zs (List.mem_sublists.2 hsub) heq] at hcov; contradiction

end S_31

theorem lowS_31 : Lower true dom_31 roots_31 goal_31 8 := S_31.noCircuit

theorem lowS_47 : Lower true dom_47 roots_47 goal_47 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcccc0000cccc, 4, 6)] (by decide +kernel) (by decide +kernel) lowS_45

theorem lowS_55 : Lower true dom_55 roots_55 goal_55 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf000f000f000f0, 2, 6)] (by decide +kernel) (by decide +kernel) lowS_51

theorem lowS_59 : Lower true dom_59 roots_59 goal_59 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf000f000f000f00, 1, 9)] (by decide +kernel) (by decide +kernel) lowS_51

theorem lowS_61 : Lower true dom_61 roots_61 goal_61 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x3333000033330000, 1, 17)] (by decide +kernel) (by decide +kernel) lowS_45

namespace S_62
def pairsG : List (Nat × Nat) := [(2, 6), (4, 6), (10, 14), (10, 26), (12, 14), (12, 28), (12, 44), (18, 22), (18, 26), (18, 50), (20, 22), (20, 28), (24, 26), (24, 28), (34, 38), (34, 50), (36, 38), (36, 44), (40, 44), (42, 46), (42, 58), (48, 50), (52, 54), (52, 60), (56, 58), (56, 60)]
def r1sG : List Nat := [2, 4, 10, 10, 12, 12, 12, 18, 18, 18, 20, 20, 24, 24, 34, 34, 36, 36, 40, 42, 42, 48, 52, 52, 56, 56]
def r2sG : List Nat := [6, 6, 14, 26, 14, 28, 44, 22, 26, 50, 22, 28, 26, 28, 38, 50, 38, 44, 44, 46, 58, 50, 54, 60, 58, 60]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_62.map (· &&& dom_62)
def goalM : Nat := goal_62 &&& dom_62
def NN : Nat → Nat
  | 3 => 4
  | 4 => 26
  | 5 => 14
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x7a502660640257ec40fe98b02dd8b08a
  | 4, 0 => 0xe48dcfade276f2b0e1585d38ddfe8cb7c7d06a8cbcda4e93ae4c141a9ec973067c4ebb7075aec8617599f484751ce62968920ce267685fe75dd695664f8d5a5a4bbd97f14606be113dec6787272628572495b66f223c2a7a156162e2143eac4b0d4f1233091b4521
  | 5, 0 => 0xe96adfead1229a47cfaf19ffaf9bf0da8159b5295f32b75e4b4bde274236b4083ee011902957f7c71a38d81412ad228510c692c60fda308c
  | 6, 0 => 0xc99170a
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x55005500550055000000000000000000000000000000000000000000000000001111444411114444000000000000000000000000000000000000000000000000555500005555000000000000000000000000000000000000000000000000000011441144114411440000000000000000000000000000000000000000000000005555555500000000000000000000000000000000000000000000000000000000505050505050505000000000000000000000000000000000000000000000000044444444444444440000000000000000000000000000000000000000000000000055550000555500
  | 0, 1 => 0x555550500000000000000000000000000000000000000000000000000055000000550000000000000000000000000000000000000000000000000000000055000000550000000000000000000000000000000000000000000000000055555555550000000000000000000000000000000000000000000000000000005550555055505550000000000000000000000000000000000000000000000000500050005000500000000000000000000000000000000000000000000000000011111010111110100000000000000000000000000000000000000000000000001414141414141414
  | 0, 2 => 0x55405540554055400000000000000000000000000000000000000000000000005555555550500000000000000000000000000000000000000000000000000000111100001111000000000000000000000000000000000000000000000000000000004444000044440000000000000000000000000000000000000000000000000055005000550050000000000000000000000000000000000000000000000000555555550500050000000000000000000000000000000000000000000000000055005544550055440000000000000000000000000000000000000000000000005454000054540000
  | 0, 3 => 0x40404040404040400000000000000000000000000000000000000000000000005544000055440000000000000000000000000000000000000000000000000000000000005555550000000000000000000000000000000000000000000000000015001500150015000000000000000000000000000000000000000000000000005505000055050000000000000000000000000000000000000000000000000000555555550050005000000000000000000000000000000000000000000000000010101010101010100000000000000000000000000000000000000000000000000404040404040404
  | 0, 4 => 0x5050000050500000000000000000000000000000000000000000000000000000000505000005050000000000000000000000000000000000000000000000000005400540054005400000000000000000000000000000000000000000000000000000000545454540000000000000000000000000000000000000000000000005544554455445544000000000000000000000000000000000000000000000000440044004400440000000000000000000000000000000000000000000000000055555555404040400000000000000000000000000000000000000000000000005454545454545454
  | 0, 5 => 0x50500000505000000000000000000000000000000000000000000000000000005555505055555050000000000000000000000000000000000000000000000000504050405040504000000000000000000000000000000000000000000000000055555500555555000000000000000000000000000000000000000000000000005500000055000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xc51c840c708640c508440c20404
  | 4, 0, 0 => 0xc508171436c708156851c2054314765850c55c2055614708150c7095514314205354851c2054315108150c740205451c204f50c204e354c14708150c52ca05431470895
  | 4, 0, 1 => 0xc51ea0543a6808150c70679943142065514708191431630a258451c2054314781f50de1c205451c205d5
  | 5, 0, 0 => 0xc51c2b0160e914708160c51c206660c51c204d60c51e808160c52c708160c51c206760c51c205960c51e008160c51c205f60eb14708160c51c228160c51c205460c51c20556
  | 6, 0, 0 => 0x31470815
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 28
  | 4 => 34
  | 5 => 40
  | 6 => 34
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xc70c1f3f8fc0df80fe0304f3f1fff0000c30c720630e34fc0ffc
  | 0, 1 => 0xffc8e00f8007001f3fff000f7cf1f8000070f8cf1c8dbcfff
  | 0, 2 => 0xc70c1f3ffcc00f80f00018c00d38c3e0bfff00cc73c1f4c00f80
  | 0, 3 => 0x3003380000fff31c307cc80ce03ffcc0230c31c818c38d
  | 0, 4 => 0xc80ce0003007230f3e0c000fffc73cff418000cfff0000dbcfff
  | 0, 5 => 0xc00c00f8cffc8000070ff0fff3003000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xe78e5f2896837fc2fea2e7eee3fff0902cf6cf75e75e7c6e86d4
  | 0, 1 => 0xf6fc6086800380153fffb68f7df7fe8e2874a18a183b6bb68
  | 0, 2 => 0xf7df7ffffeee0a00a0800940171871a0fffd348e7de5fff0bfa8
  | 0, 3 => 0x125125ff0bfa8000f6f3963968ec2eca3ffc6c3a18a181309308
  | 0, 4 => 0x4c24c200f40571871a0c003dbfffffffd18111cfff1b5fffffff
  | 0, 5 => 0x2c02ca0ffffffecf6cf7ffafff3903928
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 26 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 26 (i % 8)
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 6 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN0 : Nat → Nat
  | 4 => 9
  | 5 => 9
  | _ => 0
def CH0 : Nat → Nat → Nat
  | 4, 0 => 0xc7ffb4d0ad54f17b9dd4925762865e7d412b8d6f34d775bb0c99170a07984a0f07150476
  | 5, 0 => 0xef9457547d2307bf67ee39f25e0f38715c4358d920b8053b0de22c090c99170a01faf53b
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 4, 0 => 0x0
  | 5, 0 => 0x0
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 5 0 (CN0 s)
def CN : Nat → Nat
  | 3 => 1
  | _ => 0
def CH : Nat → Nat → Nat
  | 3, 0 => 0x73dab6e6
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 3, 0 => 0x324c8200
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 2 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry true dom_30 roots_30 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_62 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_30 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 32 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_62 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_62 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_62 == dom_62) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_62 goalM v ys) : RunD true dom_62 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_62 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 4 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 4 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 26 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 26 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 14 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 14 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
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
def RootG (s : Nat) : Bool :=
  scr true dom_62 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_62 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_62 roots_62 goal_62 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_62 goal_62 := by
    have h0 : isConstB dom_62 goal_62 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hnc hr ha
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
    rw [proper_failG zs (List.mem_sublists.2 hsub) heq] at hcov; contradiction

end S_62

theorem lowS_62 : Lower true dom_62 roots_62 goal_62 7 := S_62.noCircuit

namespace S_63
def pairsG : List (Nat × Nat) := [(1, 9), (1, 17), (1, 33), (2, 6), (3, 7), (3, 11), (3, 19), (3, 35), (4, 6), (5, 7), (5, 13), (5, 21), (5, 37), (8, 9), (10, 11), (10, 14), (10, 26), (12, 13), (12, 14), (12, 28), (12, 44), (16, 17), (18, 19), (18, 22), (18, 26), (18, 50), (20, 21), (20, 22), (20, 28), (24, 25), (24, 26), (24, 28), (32, 33), (34, 35), (34, 38), (34, 50), (36, 37), (36, 38), (36, 44), (40, 41), (40, 44), (42, 43), (42, 46), (42, 58), (48, 49), (48, 50), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [1, 1, 1, 2, 3, 3, 3, 3, 4, 5, 5, 5, 5, 8, 10, 10, 10, 12, 12, 12, 12, 16, 18, 18, 18, 18, 20, 20, 20, 24, 24, 24, 32, 34, 34, 34, 36, 36, 36, 40, 40, 42, 42, 42, 48, 48, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [9, 17, 33, 6, 7, 11, 19, 35, 6, 7, 13, 21, 37, 9, 11, 14, 26, 13, 14, 28, 44, 17, 19, 22, 26, 50, 21, 22, 28, 25, 26, 28, 33, 35, 38, 50, 37, 38, 44, 41, 44, 43, 46, 58, 49, 50, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0xfffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_63.map (· &&& dom_63)
def goalM : Nat := goal_63 &&& dom_63
def NN : Nat → Nat
  | 3 => 1
  | 4 => 26
  | 5 => 160
  | 6 => 384
  | 7 => 161
  | 8 => 18
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x765789b9
  | 4, 0 => 0xfc38cb23f2f37bc2be6ef42fb3e806dfa441f33e95489c1a8a32f5c38402693f7f0695c57d68ff7164b68e7960c110005f3e59765416c92d52f10c374d09dd2a4b61ba853b47780a38f23fd12458940e1ddb63071ad616ec0f7a1a3a0ae5c34a0676afe2042242a7
  | 5, 0 => 0x431ac80f3fe7e89d3f7756a83ccd53fc3a8a15b038f87069384afb43383ec7ee382214b43792603636db659335e27cb5358c7ada3570acaf356c45a333f0936c323c00cc31eb731f31e8f3ee315df5c12e4948ee2e324d522cc856042be3d00f2ae437f72a0ccfa02646f7da24fe24a122eb496e2266241f1f41c8681e1d41f41c7a17cf19162f011871657115fc6b8d15218cf414f071b613bf6ff613790fa113021a3012eb0110129f5c4e10a5a3001037829e0fe242470f933a990e02da490dedc5760de4f68e0d7bb2940cd5eafd0bdfc2bb0b9a42810b1007c3093b76fc05aa679904c17f5204b577180420b2d302a70f720257947d0100dfdf0012541d
  | 5, 1 => 0x99327bcd9826ac0896f6510993397fc18f52b9a68b7ebf038a87ee5a88c4fce7887410238638d5f985f7cae2834a6bed8228a28981b624927f0695c57ee6f5387ebdb9f37ddc4f087d6d347a789b967174f65a6074e9528d744953f7729bf16371c9d27971adc40b7146d0726ca362596c3c170e6b8de29f6b25e40668ab6c1968a9a2ca67ffb60c676f9165663c492f658306f661849cee5f59759e5f4205215e42cbae5df021fc5c36fc045bda7daa5adcd1605a7e48b55a066eea597ec898589c41e355a9a0e4519bfa8f517f59824f66c5274ec54a554e0159924dd86c454c06bb844b258a774ab395d4499d5267486c8af947648b46475dd0c945e4448f
  | 5, 2 => 0xfb4631d8f47e32b1edb69870e98d832ce324f80fdaf58f5ad6a1aa51d67f17bad47c25b3d3fb5db4d0b74bbad078378ccee0cdd3cb742b0bc9caf4c6c799ee66c45f1764c4398f4fc058d943bf6d32dbbbbff4e1ba4be4d3b97b4472b86e3c8eb55e538eb505a7dab0f731b2ad71826aa5d121f5a5ba75bea4849b2d99c411ac
  | 6, 0 => 0x1a7f59e81a016b1819e7646e19183d8b1819727316009904154ab092151450011413c66a13f46de613e760b513b75d6a134d33971299e0c8127f77081255154311f04eb911adfbc211a334e11143b37110dd35ef10683b96104a55570fe55a340f8b49d40f710b310f4bb2da0f4abc500f2150b10e8cc5dd0e77fb720e5b400a0dec7a450d205abe0c2bbff50b54450e0b43f1e409c0c72409ac5bd70968c09008eef02408ab7b550860af7e083bd14407c99231078ca4b207880bb907751ee2067fa422065f78b0060b50a00591d0580587e53a04e9653a03808a2b0362f6a70351202902725d1002013f5901ebfdf9016966d20119397f0114b2a80036d3c1
  | 6, 1 => 0x3179cccf311b23f2310d71e130e8d9c730952d0f301c93a030005af12f7e5e482f6fd92c2f6eea742ef40ace2e46bad12dea96002d400c042cf3547c2c9717512c8b9f5e2ab61cb72a250d1a298d120c294a86b928e532c9283a74ea27ee504027e5370e26dee8cb26806c8026775f4a26536b832536e24b25267c3724e64f60249d4592242d9e45240d114023df5c4d23887f09235d55f223432cab22a1578021f308b521df510c215abbe9215a12a6212ed80c210438af2075ef082000ef8b1ffc5afa1fa7779a1ed7bcaa1ec2cac61e0fac001df022191da3e4471c834ad01c7b30fe1c1f10511be3ee371bd066f21b5c974d1b271fa21abc19261a88df3b
  | 6, 2 => 0x505e17574fc42e9c4fbd01ed4e5b7aea4e4d99f94dc4814d4d4c97344d43b8eb4cf392694c804b8a4b49b1164adeb5f24ad5ffae4a6687094a5ada964a2c3dc749745717496c891c4904473348ada7d148858e0047250c4946b8bd32462c8cef45a99bf0443a7f6d4415c08f434775ec42c804ec42c73915428692e7409bbde63f6fce6b3f6ab1a73e4190b83e2ba39d3e0c38d23cfbb0553c81fa703c3a30f03bcdcb6e3b56119b3b1d81653ac4c91d3ab219e639e9653f3895ea4637f05509376f0946372558c936e4ee2135b0b81b353fe3093517afbb34a896ad341e5bf033ddd018335d231233508093332597043305828b32b4c334323263fc31d8e83f
  | 6, 3 => 0x757f6c6375385c40750dff0f74ab1ab6745709f27407fdf77352d381732a6513718f8e7d70dc66546fd9695b6fcdcce06f8f310f6f5452296ee638406e814aa66dd2d9196dc5f1206ce150186c6d406a6bbb18d26abc4bb06a8b50d3698d60e968ae0eeb6812feb8679f2f13676f9165670194e966cca63565b1be8b6596abb364a3a6606432ac736387a793630feeda630d409b6240d419621e66f25f8d1f6e5efdc9715eddb2cf5d189f145ce7f79e5cd097245c36f3cf5bb9e9785b76cbfa59f9571a599ae6b7582cb1c457cdfde55799a9d3568dda0e54f588a5543473c25401338753fd6ed7538f4368530e6d6352244b04519bfa8f512280e450f11de8
  | 6, 4 => 0xa39ddf4ca360845ca2c1116c9d9ef4ae9bfabaa09aa0a3eb9a4af57999648655989f6dd1982bffab977891ea96bea9189626c179959ebd8b955b1d22955239c394c825c693cdd38e939aebeb92c0b17b92628bba9211f00a91a3ceb791714e488f786f698ebec2c48cf159118c2c3b1f8bc720b38a64bb77899b82fb899b746c88af4029885c9d078804f41187ab0b2484c5da8e82b337ce825d99218173c4667ff71d4a7f2ff1957f094e9d7ebaa8bd7ead1be37df342237cd8936a7ccadda87c3235757c1d65e37bf2d4b17be645e07b4142347b40a22e7a63cb637a51e0027a2c4b4878208d1777403f1776fbc53176d1663376a58735760bbd917607e5a4
  | 6, 5 => 0xfbdbed88f68117a1f6060938f20a2f21f1f1e31cee6187ecedd6a083eb99ffa9e624383de53cd1dfdfa84c85debb37beddf476f3dd7e7190daf58f5ad9d85f96d91dae36d87b54b9d7f516b7d693bee9d67f17bad5b428dbcfc5e15cce9ad060cc81f286cc3e10e0cc0795a0cb5ff9e6caa3da0cca65e6f7c737f44ec5dd844cc49030a6c0c98d57c09ec305c099a1b8bea5df9fbcd06cb9bbe70990bb5e49bdba3d0c5cba131530b9f4b7c9b9662b97b90379a6b8ae759db73ad3e5b660feabb505a7dab42fccedb37a1fdbb2fd6c75aed39dcfae5f174eae0d299badbcde2dad2f775cac5fbf18ac22fd96a99b3f59a81444b6a65cc12fa574784ba4249521
  | 7, 0 => 0x371fc7053332c8ac316ec153311365ea2ff33f6d2eeb32c42e93e8dd2df574ca2d400c042a2246d8295a325f285c4d582536e24b248d0cda24881fcd22b6f3d821bf3c1f20635ecf1f84fad91e166e5c1e151ad01dd9d3ac1ba44b831a93182418fa334917ecb1a0177cafdd17222372165a931d1442863e141a845b14177f4513fa88241191f01d11855ffa117f857510333ffc0bc9a7b30bc4958f0bbdfb110adf322e0a948e340a81a6e509ff582e09d4320a0982d2c6087439520860af7e07d3b7220739549106bb5a1a06a3543f05576c42050e3999048e9be0045c266a043ac190039086ce0332c8ef027cee9501b929740119397f0101f1f200b358a7
  | 7, 1 => 0x972b607f972561c694af57739429d14e92db3fb99134a3bd8f44999b8c29834189a09f65865e205482b76bfc824f2cee818c0c1480e201497ed093617de33e517d7569f87c7eab2679bb382476679ec0755599fd746ad6827407fdf77296cfd06f05d97b6e6879856bbda42a6b6bc18e6a9de14769af10ee68d5c6136802048267db7a3666de80006432ac736346a562623a864360a9e8375fa48d9e5cc8f45a5a948b2f56acd9c0552cf14b53cddfe6535c7b5852e468e0521c46cc51cd900851b779944d87a09f4a3ef3444a3775da44f9244644c96a0843c3c2f5433506b94324f32c42a5a65e41d4ab9140a7bc453fc10d1b3bdcb0373b1014283914513c
  | 7, 2 => 0xfb21b774f8a8d990f37d2702edd6a083e801ecbfe0a0277adf106adedd65a083da0210d3d6ba4005d68d26c5d5c74468d4cebad4d38070e9cc5c881dca61fb61c9420fd4c6b92d9ec0233046bdd14985b8ee932ab4d54b79b4d46880afac192eaf7dae82ad113fd0ad1063e5abc29c79aa2524c2a4980c50a2eb78cc9f3dd11b9ad42e42
  | 8, 0 => 0xe1e5382cc9b9d25cc6b92d9e972b607f8f3271f680a859317a30672764559dca6106611b5533e30545b7ac423fe6b3ad3e60a6711d9823f718415b6a0eb8ce0b00b358a70093fbeb
  | 9, 0 => 0xeb4dbe4d
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffffccccffffcccc000000000000000000000000000000000000000000000000fcccf000fcccf000000000000000000000000000000000000000000000000000fff0fff0fff0fff0000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000ffffffff00000000000000000000000000000000000000000000000000000000aaaaaaaaaaaaaaaa0000000000000000000000000000000000000000000000003333cccc3333cccc0000000000000000000000000000000000000000000000000ff00ff00ff00ff0
  | 0, 1 => 0xf0ff0f00f0ff0f0000000000000000000000000000000000000000000000000ff00ff00ff00ff000000000000000000000000000000000000000000000000003e3e3e3e3e3e3e3e0000000000000000000000000000000000000000000000001414141414141414000000000000000000000000000000000000000000000000ffff0000ffff0000000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000000cccccccccccccccc00000000000000000000000000000000000000000000000000ff00ffcc33ff00
  | 0, 2 => 0xffffffaa00000000000000000000000000000000000000000000000033cc33cc33cc33cc0000000000000000000000000000000000000000000000000000ffee0000ffee0000000000000000000000000000000000000000000000003c3c3c3c3c3c3c3c0000000000000000000000000000000000000000000000000000fefe0000fefe00000000000000000000000000000000000000000000000000000000afaffafa0000000000000000000000000000000000000000000000000ff30ff00ff30ff00000000000000000000000000000000000000000000000003333323233333232
  | 0, 3 => 0xf000f000f000f000000000000000000000000000000000000000000000000000003e3e00003e3e000000000000000000000000000000000000000000000000000000003e3e3e3e00000000000000000000000000000000000000000000000000be00be00be00be0000000000000000000000000000000000000000000000000f0f0f0fc3c3f0f0000000000000000000000000000000000000000000000000fac8fac8fac8fac8000000000000000000000000000000000000000000000000eeeeeeeeeeeeeeee00000000000000000000000000000000000000000000000000ffff0000ffff00
  | 0, 4 => 0xfefefefe000000000000000000000000000000000000000000000000f00ef00ef00ef00e00000000000000000000000000000000000000000000000000000000aaffffaa000000000000000000000000000000000000000000000000545454545454545400000000000000000000000000000000000000000000000000fe00fe00fe00fe00000000000000000000000000000000000000000000000000000000ffeeffee000000000000000000000000000000000000000000000000ffffffff0f000f000000000000000000000000000000000000000000000000000f000f000f000f00
  | 0, 5 => 0xe0e0e0e0e0e0e0e000000000000000000000000000000000000000000000000ff0cff0cff0cff0c000000000000000000000000000000000000000000000000f00cf00cf00cf00c000000000000000000000000000000000000000000000000ffffffff33330000000000000000000000000000000000000000000000000000ff0fff0fff03ff00000000000000000000000000000000000000000000000000ffee0000ffee00000000000000000000000000000000000000000000000000000f0e0f0e0f0e0f0e00000000000000000000000000000000000000000000000000000000bebebebe
  | 0, 6 => 0xc0c0c0c0c0c0c0c00000000000000000000000000000000000000000000000000f0c0f0c0f0c0f0c000000000000000000000000000000000000000000000000ccccf0f0ccccf0f000000000000000000000000000000000000000000000000033333030333330300000000000000000000000000000000000000000000000001144114411441144000000000000000000000000000000000000000000000000aaeeaaeeaaeeaaee00000000000000000000000000000000000000000000000000fa00fa00fa00fa0000000000000000000000000000000000000000000000003232323232323232
  | 0, 7 => 0xffccffccffccffcc0000000000000000000000000000000000000000000000000000cccc0000cccc000000000000000000000000000000000000000000000000f0e0f0e0f0e0f0e0000000000000000000000000000000000000000000000000ffffff00ffffff0000000000000000000000000000000000000000000000000000ffffaa00ffffaa000000000000000000000000000000000000000000000000cccc0000cccc0000000000000000000000000000000000000000000000000000fffff0f0fffff0f0000000000000000000000000000000000000000000000000fefefefefefefefe
  | 0, 8 => 0xeeeeffee000000000000000000000000000000000000000000000000555550505555505000000000000000000000000000000000000000000000000000000000f0fff0fa000000000000000000000000000000000000000000000000fffffffff3f3f0f0000000000000000000000000000000000000000000000000f0f0f0f030300000000000000000000000000000000000000000000000000000f0fff0ff3033000000000000000000000000000000000000000000000000000055005500550055000000000000000000000000000000000000000000000000000f0ffafa0f0ffafa
  | 0, 9 => 0xfcfc0000fcfc000000000000000000000000000000000000000000000000ffff0000fffff0f0000000000000000000000000000000000000000000000000cc00cc00cc00cc0000000000000000000000000000000000000000000000000000000000fffffafa00000000000000000000000000000000000000000000000033332222333322220000000000000000000000000000000000000000000000000000eeee0000eeee000000000000000000000000000000000000000000000000f0f0fefef0f0fefe0000000000000000000000000000000000000000000000000000f0f00000f0f0
  | 0, 10 => 0xfafefafe000000000000000000000000000000000000000000000000ffffffff03030300000000000000000000000000000000000000000000000000fcfcfcfcfcfcfcfc0000000000000000000000000000000000000000000000000f2e0f2e0f2e0f2e000000000000000000000000000000000000000000000000fffffffffafa0000000000000000000000000000000000000000000000000000fafafafafafafafa000000000000000000000000000000000000000000000000ccccc8c8ccccc8c800000000000000000000000000000000000000000000000000ff00fa00ff00fa
  | 0, 11 => 0xf3f3f2f2f3f3f2f20000000000000000000000000000000000000000000000003030303030303030000000000000000000000000000000000000000000000000f000f000fc00ff00000000000000000000000000000000000000000000000000332233223322332200000000000000000000000000000000000000000000000000ee00ee00ee00ee00000000000000000000000000000000000000000000000000ff00ff0033000000000000000000000000000000000000000000000000000000000000cc00ff00000000000000000000000000000000000000000000000000fefe0000fefe0000
  | 0, 12 => 0xf0fff0f0f0fff0f0000000000000000000000000000000000000000000000000aaffffaaaaffffaa000000000000000000000000000000000000000000000000f0f00000f0f000000000000000000000000000000000000000000000000000000f0f0a0a0f0f0a0a000000000000000000000000000000000000000000000000f0e2f0e2f0e2f0e20000000000000000000000000000000000000000000000000f0f5a5a0f0f5a5a000000000000000000000000000000000000000000000000f0f0f0c0f0f0f0c00000000000000000000000000000000000000000000000003333330033333300
  | 0, 13 => 0xf0f0f0f0f0c0f0c000000000000000000000000000000000000000000000000ffffc0c0ffffc0c0000000000000000000000000000000000000000000000000ff00ffeeff00ffee0000000000000000000000000000000000000000000000000000ff000000ff0000000000000000000000000000000000000000000000000033330300333303000000000000000000000000000000000000000000000000004444444444444444000000000000000000000000000000000000000000000000ffffffffc0c0c0c0000000000000000000000000000000000000000000000000ffffffff33330300
  | 0, 14 => 0x33333f3033333f3000000000000000000000000000000000000000000000000000000000fffffefe000000000000000000000000000000000000000000000000cccccfcecccccfce000000000000000000000000000000000000000000000000fe00fe00fe00fe0000000000000000000000000000000000000000000000000000000000f0fef0fe000000000000000000000000000000000000000000000000fffffafafffffafa000000000000000000000000000000000000000000000000f0c0f0c0f0c0f0c000000000000000000000000000000000000000000000000000ff00aa00ff00aa
  | 0, 15 => 0x333333330300030000000000000000000000000000000000000000000000000000000000c0ccc0cc000000000000000000000000000000000000000000000000ffffffaaffffffaa0000000000000000000000000000000000000000000000000000ffae0000ffae00000000000000000000000000000000000000000000000000ff00fe00ff00fe000000000000000000000000000000000000000000000000ffffffff3f330f0000000000000000000000000000000000000000000000000011ee11ee11ee11ee000000000000000000000000000000000000000000000000aafaaafaaafaaafa
  | 1, 0 => 0xffff00f0ffff00f00000000000000000000000000000000000000000000000000f0f0d0c0f0f0d0c0000000000000000000000000000000000000000000000000000ffaa0000ffaa000000000000000000000000000000000000000000000000bebebebebebebebe00000000000000000000000000000000000000000000000000000000ffffbaba00000000000000000000000000000000000000000000000000000000feeefeee00000000000000000000000000000000000000000000000000555500005555000000000000000000000000000000000000000000000000000000323200003232
  | 1, 1 => 0xffeeffaa000000000000000000000000000000000000000000000000ffff5050ffff5050000000000000000000000000000000000000000000000000ffff3232ffff3232000000000000000000000000000000000000000000000000333300003333000000000000000000000000000000000000000000000000000000f300f000f300f00000000000000000000000000000000000000000000000000f0f0f000f0f0f0000000000000000000000000000000000000000000000000000ff00f000ff00f00000000000000000000000000000000000000000000000005555550055555500
  | 1, 2 => 0xfeee0000feee0000000000000000000000000000000000000000000000000000fafa0000fafa00000000000000000000000000000000000000000000000000000000fffffffa000000000000000000000000000000000000000000000000ccccccc0ccccccc0000000000000000000000000000000000000000000000000333333323333333200000000000000000000000000000000000000000000000000000000ffafffaa000000000000000000000000000000000000000000000000ff00fa00ff00fa00000000000000000000000000000000000000000000000000ccccc0c0ccccc0c0
  | 1, 3 => 0xf3f3f0f0f3f3f0f0000000000000000000000000000000000000000000000000cfcccfcccfcccfcc000000000000000000000000000000000000000000000000afaffafaafaffafa0000000000000000000000000000000000000000000000005544554455445544000000000000000000000000000000000000000000000000f0f3f0c0f0f3f0c0000000000000000000000000000000000000000000000000f0fef0fef0fef0fe000000000000000000000000000000000000000000000000ffffffffff33ff00000000000000000000000000000000000000000000000000ff00ff0033000000
  | 1, 4 => 0xff000000ff0000000000000000000000000000000000000000000000000000003636363636363636000000000000000000000000000000000000000000000000ccccffeeccccffee000000000000000000000000000000000000000000000000fffff000fffff000000000000000000000000000000000000000000000000000ffaaaaaaffaaaaaa0000000000000000000000000000000000000000000000000055ffaa0055ffaa00000000000000000000000000000000000000000000000031313130313131300000000000000000000000000000000000000000000000002e2e2e2e2e2e2e2e
  | 1, 5 => 0xfafafa00fafafa00000000000000000000000000000000000000000000000000fafafefefafafefe000000000000000000000000000000000000000000000000fcfcfc00fcfcfc00000000000000000000000000000000000000000000000000fcfca8a8fcfca8a8000000000000000000000000000000000000000000000000bbaabbaabbaabbaa0000000000000000000000000000000000000000000000003333101033331010000000000000000000000000000000000000000000000000ffaaffaaffaaffaa000000000000000000000000000000000000000000000000fff3fff0fff3fff0
  | 1, 6 => 0x50505050505050500000000000000000000000000000000000000000000000000f0f0f0a0f0f0f0a0000000000000000000000000000000000000000000000000c0c0c0c0c0c0c0c000000000000000000000000000000000000000000000000ffffaaaaffffaaaa000000000000000000000000000000000000000000000000aaaaffaaaaaaffaa00000000000000000000000000000000000000000000000033f300f033f300f00000000000000000000000000000000000000000000000000000cfcc0000cfcc0000000000000000000000000000000000000000000000000000fccc0000fccc
  | 1, 7 => 0xfffafffafffafffa0000000000000000000000000000000000000000000000000f0a0f0a0f0a0f0a0000000000000000000000000000000000000000000000005555110055551100000000000000000000000000000000000000000000000000ffff0f00ffff0f000000000000000000000000000000000000000000000000003332333233323332000000000000000000000000000000000000000000000000fffffaaafffffaaa0000000000000000000000000000000000000000000000003232fafa3232fafa0000000000000000000000000000000000000000000000000a0e0a0e0a0e0a0e
  | 1, 8 => 0xff00aa00ff00aa00000000000000000000000000000000000000000000000000faaafaaafaaafaaa000000000000000000000000000000000000000000000000ddddddccddddddcc000000000000000000000000000000000000000000000000ccff88aaccff88aa000000000000000000000000000000000000000000000000fffffff0fffffff0000000000000000000000000000000000000000000000000ddcc5500ddcc550000000000000000000000000000000000000000000000000044445544444455440000000000000000000000000000000000000000000000003222322232223222
  | 1, 9 => 0xfcccfcccfcccfccc0000000000000000000000000000000000000000000000003333110033331100000000000000000000000000000000000000000000000000ff33ff30ff33ff300000000000000000000000000000000000000000000000000302030203020302000000000000000000000000000000000000000000000000ffffffffffff0f000000000000000000000000000000000000000000000000000000faaa0000faaa00000000000000000000000000000000000000000000000000ff000000ff0000000000000000000000000000000000000000000000000000ffff0e0effff0e0e
  | 1, 10 => 0xffff00eeffff00ee000000000000000000000000000000000000000000000000ff00fffcff00fffc000000000000000000000000000000000000000000000000f444f444f444f444000000000000000000000000000000000000000000000000cfcfcececfcfcece000000000000000000000000000000000000000000000000ffffffccffffffcc0000000000000000000000000000000000000000000000000f0f0f0c0f0f0f0c000000000000000000000000000000000000000000000000ffeeffeeffeeffee000000000000000000000000000000000000000000000000f0f0fffcf0f0fffc
  | 1, 11 => 0xeeeeffeeeeeeffee000000000000000000000000000000000000000000000000eeeeaaaaeeeeaaaa000000000000000000000000000000000000000000000000e0e0e0e0e0e0e0e000000000000000000000000000000000000000000000000000000f0c00000f0c00000000000000000000000000000000000000000000000000fc00fc00fc00fc000000000000000000000000000000000000000000000000ffff00faffff00fa0000000000000000000000000000000000000000000000001111110011111100000000000000000000000000000000000000000000000000ee00ee00ee00ee00
  | 1, 12 => 0xf500f000f500f0000000000000000000000000000000000000000000000000000e000e000e000e000000000000000000000000000000000000000000000000ffffddccffffddcc000000000000000000000000000000000000000000000000fcfcf0f0fcfcf0f0000000000000000000000000000000000000000000000000ff0fff0aff0fff0a00000000000000000000000000000000000000000000000031313030313130300000000000000000000000000000000000000000000000002322232223222322000000000000000000000000000000000000000000000000ffff5454ffff5454
  | 1, 13 => 0xee000000ee000000000000000000000000000000000000000000000000cc88ffaacc88ffaa0000000000000000000000000000000000000000000000000000baba0000baba000000000000000000000000000000000000000000000000fefefafafefefafa0000000000000000000000000000000000000000000000005504550455045504000000000000000000000000000000000000000000000000fffefffefffefffe000000000000000000000000000000000000000000000000ffffffffbbbbaaaa000000000000000000000000000000000000000000000000afafa0a0afafa0a0
  | 1, 14 => 0xa0a0e0e0a0a0e0e0000000000000000000000000000000000000000000000005050545450505454000000000000000000000000000000000000000000000000fffffcccfffffccc000000000000000000000000000000000000000000000000ffff5500ffff5500000000000000000000000000000000000000000000000000ffff3030ffff3030000000000000000000000000000000000000000000000000e0eee0eee0eee0ee00000000000000000000000000000000000000000000000054445444544454440000000000000000000000000000000000000000000000005555000055550000
  | 1, 15 => 0x5f550f005f550f0000000000000000000000000000000000000000000000000033003300330033000000000000000000000000000000000000000000000000000303030003030300000000000000000000000000000000000000000000000000ff00ffccff00ffcc0000000000000000000000000000000000000000000000000044004400440044000000000000000000000000000000000000000000000000ffbbffaaffbbffaa000000000000000000000000000000000000000000000000fffffcfcfffffcfc0000000000000000000000000000000000000000000000000f0f00000f0f0000
  | 2, 0 => 0xbbbbbababbbbbaba0000000000000000000000000000000000000000000000005151505051515050000000000000000000000000000000000000000000000000fafa0000fafa000000000000000000000000000000000000000000000000000022223322222233220000000000000000000000000000000000000000000000000033003000330030000000000000000000000000000000000000000000000000f0f03030f0f03030000000000000000000000000000000000000000000000000aaffaa00aaffaa0000000000000000000000000000000000000000000000000000aa00ee00aa00ee
  | 2, 1 => 0xff44ff44ff44ff44000000000000000000000000000000000000000000000000ffaaf0a0ffaaf0a00000000000000000000000000000000000000000000000000000ffff00000f000000000000000000000000000000000000000000000000000000fffa0000fffa000000000000000000000000000000000000000000000000fffcfffcfffcfffc000000000000000000000000000000000000000000000000aaffaafaaaffaafa000000000000000000000000000000000000000000000000fffffffafffffffa0000000000000000000000000000000000000000000000004f444f444f444f44
  | 2, 2 => 0xf000f0c0f000f0c0000000000000000000000000000000000000000000000000000554400005544000000000000000000000000000000000000000000000000ff33ff22ff33ff220000000000000000000000000000000000000000000000005544550055445500000000000000000000000000000000000000000000000000ffccf0c0ffccf0c0000000000000000000000000000000000000000000000000ff55ff50ff55ff50000000000000000000000000000000000000000000000000ffffbbaaffffbbaa000000000000000000000000000000000000000000000000ee0eee0eee0eee0e
  | 2, 3 => 0xffff3300ffff3300000000000000000000000000000000000000000000000000ffffaafaffffaafa00000000000000000000000000000000000000000000000011111010111110100000000000000000000000000000000000000000000000000000afaa0000afaa000000000000000000000000000000000000000000000000f5f4f5f4f5f4f5f40000000000000000000000000000000000000000000000001010101010101010000000000000000000000000000000000000000000000000aaaafefeaaaafefe0000000000000000000000000000000000000000000000003333300033333000
  | 2, 4 => 0xee22ee22ee22ee220000000000000000000000000000000000000000000000000054005400540054000000000000000000000000000000000000000000000000ff0faa0aff0faa0a000000000000000000000000000000000000000000000000ffaeffaeffaeffae000000000000000000000000000000000000000000000000cfcf8a8acfcf8a8a000000000000000000000000000000000000000000000000ff0eff0eff0eff0e0000000000000000000000000000000000000000000000000000dcdc0000dcdc000000000000000000000000000000000000000000000000ffccff00ffccff00
  | 2, 5 => 0xfff0aaa0fff0aaa000000000000000000000000000000000000000000000000333333303333333000000000000000000000000000000000000000000000000000000000f0ff000000000000000000000000000000000000000000000000000000000f0a00000f0a00000000000000000000000000000000000000000000000055f500f055f500f0000000000000000000000000000000000000000000000000ffffccfcffffccfc000000000000000000000000000000000000000000000000fbfbfafafbfbfafa000000000000000000000000000000000000000000000000000f000a000f000a
  | 2, 6 => 0x5555005055550050000000000000000000000000000000000000000000000000ffffffffff0000000000000000000000000000000000000000000000000000005555555555000000000000000000000000000000000000000000000000000000f000fcccf000fccc000000000000000000000000000000000000000000000000cc88cc88cc88cc880000000000000000000000000000000000000000000000005050dcdc5050dcdc000000000000000000000000000000000000000000000000fa0afa0afa0afa0a0000000000000000000000000000000000000000000000005555554455555544
  | 2, 7 => 0xaeaeaeaeaeaeaeae000000000000000000000000000000000000000000000000f5f5f0f0f5f5f0f0000000000000000000000000000000000000000000000000fff4fff4fff4fff4000000000000000000000000000000000000000000000000fa32fa32fa32fa32000000000000000000000000000000000000000000000000cfcc0f00cfcc0f000000000000000000000000000000000000000000000000000032003200320032000000000000000000000000000000000000000000000000ff00aaaaff00aaaa0000000000000000000000000000000000000000000000005555050055550500
  | 2, 8 => 0x5554555455545554000000000000000000000000000000000000000000000000cfcfcfcccfcfcfcc0000000000000000000000000000000000000000000000000000bbaa0000bbaa00000000000000000000000000000000000000000000000000cc00cc00cc00cc000000000000000000000000000000000000000000000000ddccddccddccddcc000000000000000000000000000000000000000000000000f0fff0faf0fff0fa000000000000000000000000000000000000000000000000f0f0fffaf0f0fffa000000000000000000000000000000000000000000000000afafafaaafafafaa
  | 2, 9 => 0x11001100110011000000000000000000000000000000000000000000000000005054505450545054000000000000000000000000000000000000000000000000ffff00000f000000000000000000000000000000000000000000000000000000000000fc000000fc0000000000000000000000000000000000000000000000000000ccfc0000ccfc000000000000000000000000000000000000000000000000eeee00eeeeee00ee000000000000000000000000000000000000000000000000fafefafefafefafe000000000000000000000000000000000000000000000000ffffeeeeffffeeee
  | 2, 10 => 0xf0ccfc00f0ccfc000000000000000000000000000000000000000000000000f0ccf0ccf0ccf0cc0000000000000000000000000000000000000000000000000000ffcc0000ffcc000000000000000000000000000000000000000000000000ffffffffffaaaaaa0000000000000000000000000000000000000000000000003f330f003f330f000000000000000000000000000000000000000000000000005555555511110000000000000000000000000000000000000000000000000000afaaafaaafaaafaa000000000000000000000000000000000000000000000000fffffffcfffffffc
  | 2, 11 => 0xf0f0fcfcf0f0fcfc000000000000000000000000000000000000000000000000ccccfcfcccccfcfc000000000000000000000000000000000000000000000000aaaaeeeeaaaaeeee00000000000000000000000000000000000000000000000005050000050500000000000000000000000000000000000000000000000000000000550000005500000000000000000000000000000000000000000000000000ffffffffff00aa00000000000000000000000000000000000000000000000000eeeee0e0eeeee0e00000000000000000000000000000000000000000000000000000fffc0000fffc
  | 2, 12 => 0xeeaaeeaaeeaaeeaa000000000000000000000000000000000000000000000000afafaaaaafafaaaa000000000000000000000000000000000000000000000000ff55ff00ff55ff00000000000000000000000000000000000000000000000000ff0fff00ff0fff000000000000000000000000000000000000000000000000000055000000550000000000000000000000000000000000000000000000000000ffc0ffc0ffc0ffc0000000000000000000000000000000000000000000000000fffffffff0f00000000000000000000000000000000000000000000000000000babababababababa
  | 2, 13 => 0xf4f4f4f4f4f4f4f4000000000000000000000000000000000000000000000000ccccffccccccffcc0000000000000000000000000000000000000000000000003f003f003f003f00000000000000000000000000000000000000000000000000eaeaeaeaeaeaeaea000000000000000000000000000000000000000000000000aaaafafaaaaafafa000000000000000000000000000000000000000000000000ff33ff00ff33ff00
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x180802004
  | 4, 0, 0 => 0x180802200fa80c1c02068794160e010343aa0305808281c50583812020da80c16050d06541409010602ea03050082c15501838041409a8381202078494060b0480822a0307008200f50182c1c0d06282c140901021406070281804a030281004015
  | 4, 0, 1 => 0x160e010504ea0b070082828505838040d13a80c16260480941409010604aa0305838480d50182c040d11a82c14020b0894060b070081aa210702804015
  | 5, 0, 0 => 0x182c1c09010358160e1e82404226018f01409010ed8060b048e804006018e41c021a03d8060e1c0dc041360183812021b0558060e050d4043460182c14020b0cd8060b05024643160182c1c02120518060b07068141960182c1c02180bd8060b170b4120261602c560a048098062a0702404296
  | 5, 0, 1 => 0x161381c0a048098163f05134042260583814021a1318060e0500802206018381402259298060e24824044860583814090111d8060e048088c0f6058381409011158880b0710c1202605838840a048098060e05008820160182c1c38010358063907024044061082c7e09010d98060b04808003e6
  | 5, 0, 2 => 0x182c1c5f011798580b05174120260182c14022e16d8160a04808b459601838b00a010c18540e05024042260583814090115d8062a070f4120260182c1c55010358ac0b070281202601838aa370104d8060b07024045460182c1c52010358a63907148120260182c1451011418060e05008684f6
  | 5, 0, 3 => 0x182c3209010018420b1f828046a6001a4160e290654160e05008204c60182c1402081418d00b0702812026018141c0a010058060b3382404316018f01409330098580b0281012026018e41c65010418160a04808462760182c1c09231918060b0718c120260182c1c09011898060b0718404606
  | 5, 0, 4 => 0x182c14093c16d8060b07028047760182c1c0a010418160e05024047660182c1c0a3a8098167405024042760182c1c38010518160e05024047360182c1c02068bd8a67207028120260182ce209011c18420b07024046f60182c0a1a048098000337038a4195019b41409011b18060e05008d63e6
  | 5, 0, 5 => 0x18281202382158060b07210041460183814090104d8160e0502404836058381409012098063c050240481601838143a012018160e05008fe7e6019f41409010618060e05024047c6018e40e0e29065806071d008401f60182c1409011ed8f40b0702812026019c81c090103d8060b0502404796
  | 5, 0, 6 => 0x182c1c524a0098060b0702804936058381409012498060b48829200260583814090123d8588e070281202601a341c0a012318060a0480846136018a81c09010d98060b04808408b60182c1409441c18060e38824041560182c1202452258060a04809101861621c1c0a048098060b0702404866
  | 5, 0, 7 => 0x160e41c52048098580b04808401f6018281266010618060b04808d40060182c1c9b048098067405024041360182d34090107d8060b07149204660182c1c0a120c19320b4c028120260183814090125d8060b0700868366018381490012598160e05024049560000c160e010354060b07008280c6
  | 5, 0, 8 => 0x183814510125980602460803e3e60182812020c2058160a04808a04c6018381409012898060b0702804a16018e4ca09011418060b071486e24605838e209010898060e05024041560182c1c520ca818060b0727d3c0260182c0a06048098060b070e06e24601838129d0103d8060b05025385b6
  | 5, 0, 9 => 0x181c0a041d009806a907028040160182d5004048098160e2a8dc042761e29c14090105d8160e05024041760182c1c0a012998160e05024044c60183814a5010f9858a407028120260182c1c9f010c18060b38864045b60583870370109d806583a02812026018f1460a04a2180003058082c365
  | 6, 0, 0 => 0x182c1c19048086ce03058381409012c9c060b07028120258b80c160e0502404b070182c1caf0502404e0305aa41c0a48009c060b072b8140901380c160e1c02804307018f14e0a0480910e03058395a0a04809c060b072b0140901380c160e0506412ab7058fc1c0a0480844e03058381409010c1c060b07028740218380c160e0502404aa7
  | 6, 0, 1 => 0x1082c1c0a04808fce0303838143a01081c060b07028120214b80c1c5205024041370182c1c0a0480970e003482c1c0a0c8098060e050096e8c1f380c1c0a048092c3e70182c1c0a048096ce031e02c1c0a010d1c063c05aa4140901380c1c0a048e8049670181c1c0a1d00882e03058381402182d5c06b405838140959b80c160e04808c8487
  | 6, 0, 2 => 0x182c1c0a6282404e00019b81c0a0c8098060b07029880901380d860b07029200270182c1c0a6102404e0305838140901305c060b0727c12025bb80c160e0502404c070182d7e0e048097ce03058381409012f5c06b45e038140901380c160e29028123270182c1c0a0480976e0b54838140901089c06ba05838140901380c160e0502404b97
  | 6, 0, 3 => 0x182c1c0a048099ce030583814190112dc060b6683814021a380c160e0502404cc765884160e0502404e0305838140901329c067205a441409013884160e05024043e70182c1c0a0ca7804e0307028120264a15c420b07028123a01380d900b070281202701838aa0a0480826e031e2d18e0a04809c00031c838ca021a300c160e6302832097
  | 6, 0, 4 => 0x1b5c160e0502404e0305838a409010bdc06720702812024b380c16d607028120270182c1c550500860e0305839aa0a04809c063905838120232380c163f05064045b70182c1c0a6a02404e036982c1c6104809c060b07028120269380c16d1071c4120270182da20e0502538e0305839a00a04809c060e05010048c1f380c160e67828046a7
  | 6, 0, 5 => 0x1ad01c0a0480894e030583870dd04809c060b07028043444b80c160e29028323e70182c1c09010d9b8e21058381409011fdc063c5a038140944380c780b0502404db70182c1c0a0112cbce0305aa01c0a04809c06da05838140901380c160e4f8101202701a91680e0502404e03058140809011a9c060b0702812026cb80c163f05065b0027
  | 6, 0, 6 => 0x18a9520e0502404e000583814090109d8060b07024049c1b380c0e8707028120270000c160e38808d4c000182c1c0a013898060b07028120270b8b016a9070281202701b80160e0502404e030583814df04809c063903838141901380c160e050641278701af01c0a048087ce03058fc1c0a0c809c06bc07028123a01380c160e05378045e7
  | 6, 0, 7 => 0x182c3209010803ee031c82c1c0974009c060b07028120273b80c163f07028043470182c1c5f0502404e036182c140901225c060b07028120273380c720e328240446701b94160e0502404e03038141c0a1d009c060b07390a40901380c16e3070281202701b441c0a048082ae000182c1c0a010d18060b1f838e20235380c1c0a0c82404137
  | 6, 0, 8 => 0xc162e0480840c00018f01409010618060b0702812ee013800060b07148323760181c1c0a1d0083ee03058381409013b5c060b073b014090138b0160e0510c120270182c1c9e048086ce030583870521b809c060747038140901380c160e0502404eb70182dd40e0502404ee91602c1c0a04809c06390383814021a380058390702812026
  | 6, 0, 9 => 0x182c1c0a04809ece03058381409011adc06f505838140901380d68f407028120270182d520e0500868e037982c1c0a0c809c060b07029e40901380da60b07028046070182c1c9a0502404e030583870551b809c060b07028120278b80c160507148320970182c1202780803ee035a038140901215c060e1c160140901380c160e0502404ef7
  | 6, 0, 10 => 0x182c1c520480912e2c05838140901081c060b07028045c7db80de60b07028043470182da20e0480852e0305be81c0a04809c06f907028120227b800060b070dc04246018381409013e10ae5305838a40a04809c580b07028120220b80c160e0502404f770182c1c523382404e00019b81c5204809806b405838140944380c16052902404317
  | 6, 0, 11 => 0x182c1c0a0480a08e0307028123a01215c060b07028120281b80c160e0540832027018f0160a04c0404e0305838140901401c060b0702812027fb80d680b05024045070182c1c490502404e030582812027f16dc060e2c148140901380c163f0502404db70182c1c0a04809fae036182c1c0a010d1c060b7e0381419013884160e0506412027
  | 6, 0, 12 => 0x18e4160e0480914e0305c2c1c09010d9c060b07028130a01380e120b0702812027018e40e0e2902404e030382c12021007dc060b07028120284380c160e050260e02701aa41c0a012307ceb40583814090105dc060b07028120283380c160e05240044670182d520e048086ce000182c1c0a010418067207414140901380c1c0a048090a3e7
  | 6, 0, 13 => 0x1af01c0a04809e0e0305b441c0a04809c060b8a838140901380c160e05024051470182e260e0502404e0305c481c0a04809c060b07028120209b80e220b07028120270182c1c0a8802404e0305c3c140901081c060b87038140901380c160e03028120271082c1c0a0480a1ae0305838140901431c00000182812020c2800060b0714920026
  | 6, 0, 14 => 0x1ad23e0e0502404e038f02c1c0a04809c060b0702812028eb80c160e05024051c71602c0a0e0502404e030583a360a04809c060b07024051a17b80c160e05026320270000c160e2a80828c0305838e21904809c060b0702832094e3800060e0502404136018e4160e0500820e0305838140901461c060b0702812028bb80c160e0502405167
  | 6, 0, 15 => 0x18381402460807ce000182c7e0a010598060b92838140901380c172005024042070182da20e1e82404e0305838140901259c060b92038140901380c160e0548c1202700000060b050082ca031c82c1c5248009c060b91038140901380d860b07148120270182c1c0a0480a42e0305c80140901105c060b0714804305ab80c780b0502404707
  | 6, 1, 0 => 0x182d520e0502464e03058393e0901081c072a05838140901380da60b0702404d270182c7e0e0c8086ce0305838141901281c160e29028120226380c160e9482812027018e40e0e048096ee0305948140901141c060b7e028120210380c160e05024052870182c1c0a0cc9c04e0b68838140901089c06721c838ca0901380c160e0502405267
  | 6, 1, 1 => 0x182da20e054cc04e03058fc141901081c0003058393e022f300c1638050240423701ad016050202404e441602c1c0a04809c060b07028120299380c160e294c4120270182c1c0a0480a60e03058381409014bdc063c05838140297380c0e0e29028740271082c1c0a0480a5ae000000c1609010014060b07028120296380c160e05024052b7
  | 6, 1, 2 => 0x182c1c190480852e0305cf41c0a04809c060b074f0140901380c160e1c0281224701a900e0e0502404e0305838153b04809c06b405838140923380c160e05024053a70000c160e1c0dc04c031c838140901259c06b4074e4140901380c160e05024053870182c1c0a0480a6ee0307028120236129e6c0b0702812029ab80c160e054d012027
  | 6, 1, 3 => 0xc160e0500a5cc0305838140901141c060b07504140901380c1c0a012303e3e70182c1c0a04d0004e030581408091d009c420b07028120235380c720e05008688c70182c1c52050267ee030583a7c0a01389c060b1f838a40a0cb80c163f05024047070182c1c0a8380868e033e82c1409011c1c063905838a40923380c160e67828043e7
  | 6, 1, 4 => 0xc1c0a048082ac0305838154a04809c060b07524140901380e900e05024044a70182c1c0a010d23ae030583814090151dc060b07024042017b80ce40b07024046470182c1c0aa302404e0305838140901515c060b07148120232380c160e29028323070182c1409010c688e03058381419a1809c060b07148140912380c160ea102812027
  | 6, 1, 5 => 0x1d40160e0502404e03058281202a796dc060b070281202a7380c160e1e864120271082e9a0e0502404e000000c160e010514160e1c028120213b80cfa0b63828120270182da20e048086ce0305838140901531c000305838045e17b00c160e05024054b7018e4160e0500a5ce031f838140901055c060b071481419a238f0160e0502404177
  | 6, 1, 6 => 0x182c1c550500868e03058fc140235081c060b66838140901382c1c5505024042770002c1c0a0480898c0305838e20901555ea93605838140901382c1c5205024042770182c1c0a0480aa6e2c05838140901549c067d05838140944380c163f07008d436701ad0160e0500820e0305838a4196e825c060b07026a2025ab80c16a907029bc097
  | 6, 1, 7 => 0x182c1409011c2b6f5a5a02c1c0a04809c067d1e29c140901380c160e2a8dc042470182c1c0aac82404e031e02c140901225c067d058381409013800063c51828120260182c1c0a0480ab0e0305838a409010d9c060b02839c80901380c160e0502405577018f1520a048090ae7d0583814090105dc000b0702812020bb00c163f0555812027
  | 7, 0, 0 => 0x181c160e05024042080182e163f07028120280000de60b070281202700000060b1f8289a0260000c160e05026ba0270182c0a0e05064120280182d7e0e2902812028018e4163f07028120280182c1c5205024055c80000c170b07028120270182c1c0a048096e8c80181c160e050240441801be4160e2a828120280000c160e050240430701ad0160e63828120280000c720b0702812027
  | 7, 0, 1 => 0x182c1c520502404f880000c160e05578120270000c17200702812027018e416a9070281202801ad0160e2a828120280000c0e0b07028320270000c16a905024046c700000060b02810120260182c1c0a0c824041f80000c160e048096eb570182d520e0502404fb8018f0160e0502404608019c9680b07028120280000c720b07029200270000d860b07028120270000c780b5482812027
  | 7, 0, 2 => 0x182c7e0e05024055580182c1c3829028120280182d520e05024054480000c160e05024055570182c1c52050247402801b0c720b07028120280000c160e0202404b5700000060b05009fd4460000c160e05026c00270182c1c5205024049680000c160eaf8281202700000580b07028120260000c160e0502404db70182c1c0a02024048c80000c16fc07028120270182c1c0a04809e01f8
  | 7, 0, 3 => 0x182d520e05024056380000c160e050240424701ad0160e05024045e80000c160e290246e0270181c160e05024041f800000060bb1028120260000c160e050240460700002c20b070281202600000060b07028043460181c160507028120280182da20e05064120280182c1c382a828120280000c163f07028320270182c1c520502404b580000c780b05024044170000c160e2902832097
  | 7, 0, 4 => 0x182c1c0a02024740280182d520e05024048c80000c160e05024044670182c1c5282828120280000c160e05064054470000c160e05024046470000d1c0b070281202700000060e05009183e601ad0160e05024046c80000c720b07028043470182c1c0a048096e3e80182c1c0a048e804b78018f1680b070281202801ad0160e05010120280182c1c5529028120280000c17640702812027
  | 7, 0, 5 => 0x182da23f0702812028019f5680b07028120280000c16d1070281202701b4c780b07028120280000c160e05024047070000c16bf0702812027018e4160e050240446801ad0160e05024044b80000c160e9f028120270000c160e05026cc0270182c0a0e05024046a80000c160e050240431700000060a04809926c60182c1c0a02024043e80000c163f05024042070000c17650702812027
  | 7, 0, 6 => 0x182c1c0a0c824042f80000c160e1c02812027018e5680b07028120280000c160e0480840b570000c163f07028046a70000c16051f828120270000c160e0502404967018f0160e2a828120280182c1c0a04809182080000c160e05026a202701d21680b07028120280182c1c0a0c824044a8018f0160e29028120280182c1c0a04808828c80000c176807028120270000c160e0559c12027
  | 7, 0, 7 => 0xc160e2a828120270182c1c0a04809181f80182c1c0a0cb74120280000c160e67828120270182c7e0e29028120280182c1c0a0202404f080182c1c0a0c824046c80182d520e05024043e80000c160e05026d20270000c160e4f828120270182c1c5505024044f800000060b07008bcb560182c7e0e05024043680182d520e0502404f880000c160e63028120270000c160e0502404367
  | 7, 0, 8 => 0xc780b07028120270000c160e050256602701ad0160e050240464801ad0160507028120280000c160e055b01202700000060b05024056b60182c1c0a0c824044880182d520e05026660280000c160e29024041f70181c160e050101202800000060b0702ad409600000060b071546e026018e4160e290281202800000060b071c4120260182c1c0a0c824051a80182c7e0e2a82812028
  | 7, 0, 9 => 0x26c0b070281202600000063c53828120260000cfa0b07028120270000c160e2902404b570182c1c5205024048c80182c1c5505024042480000c160e055a8120270000c16a307028120270000c160e0502404be7018f0160e05024048880182c1c0a048083e3e80000c160eb68281202700000d20b07028120260182d520e0502404858018f0163f0702812028019f4780b0702812028
  | 7, 0, 10 => 0xc160e0502404887
  | 8, 0, 0 => 0x18f0160e0502404e0305838aa0a04809c060b07148140901380c160e0502404b570182c1c0a048e804e035a02c1c0a04809c060b07028124d01380c160e0502404fe70182c1c0a048083ee03058141c0a04809c060b07028120264b80c160e05024042070182c1c0a0480882e0305838140901511c063905838140901380c160e05024046a7
  | 8, 0, 1 => 0x60b0729c140901380c160e050246e027
  | 9, 0, 0 => 0x60b0702812026
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 40
  | 4 => 49
  | 5 => 58
  | 6 => 67
  | 7 => 76
  | 8 => 67
  | 9 => 58
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xffe0effe1c0f80000003de0000fcff0fc1fff0000000001e0000fffff000000000000000001ef7ffe0efc21c0f8fcff0fc01ff00
  | 0, 1 => 0xe3070e3fe1f00e0f80e01fe0001ce7e1fdfdfff1ce7e1fdfc108ff000ffe000001c0701c1e1f0000e0e03c1c0f81f07f1c3fe000
  | 0, 2 => 0xfffffef7e018ee3de20f800f8e001ffeff1ce7e1fdfdff800e7e001fdfff00000e3fe1ff7ffff0fc21ff00ff070fc3e1f07
  | 0, 3 => 0x1c0701c001f0000e7e001fdfff000001fdfdfff1c07e1fc01fffe3f8fe03e1f0000000001e00f000e0e03c1deff1ff801fffe000
  | 0, 4 => 0x1fdfdfff0000e03de00ff000001ffffef71ce7e1fdfc1081c07e1fc01fff00000e3dffefffffffe001e000e0f80e001e000
  | 0, 5 => 0xe0e03c1c0ffe0f8ee3dfe0f80000e03de00f8ffffffc200000e3f8fe03fe000e0000e3c00000e0f8ee3c1e0ff000001fdfdfff
  | 0, 6 => 0xe0f8ee3c1e0f80007003de1f00ff070fc3e1f00e018ee3de20080000e03c01eff1c0701c001ff71c0701c1e1f07
  | 0, 7 => 0xe0f8ee3dfe0f800e0e0001c0f800000001e1e00fff80ffffe0001ff801ffffef70000003c00000ff070fffe1f001ce7e1fdfdfff
  | 0, 8 => 0x3dffeffff070fffe0100000001ffe1ff7ffffffc3e1f001c0701c0000001f07f1c200000e0f80e01fe000e3070e3fe1ff7
  | 0, 9 => 0xe7e001fdff8ff000fffe1f0000e000001c00000000fffe1ff7ff000fc201e0700e0e0001deff1ce7e1c1fdfff00070001e1f00
  | 0, 10 => 0x1fde1ffffffffe02020001ce7e1fdfdff8e0f8ee3c1fefffffff1c0000001c0701c1e1ff70000003c000f01f0701fe01ff7
  | 0, 11 => 0xff070fc3e1f071c0701c1e1f0000000001fe000e0180e01e3e070000e03c01eff1f07f1c20000000000001fe0001c0001fc00000
  | 0, 12 => 0x1f0701ffe1f001ff801ffffef71c0001c000000e3000e3e000f700000001e1e07e3070e3fe01f71c0001c1e0000ff180fc3e2000
  | 0, 13 => 0xe3f8fe3c1e0f8ff000ffe00000e0f8ee01ffeff00f80001fe000ff180fc20200000e0e03c1c008fffff00000000ffffffc202000
  | 0, 14 => 0xffff0fc3fff0000000ffffdfff00f8e03c1e0ff00e00001fc000000001fde1fffff070fffe1ff700000001e00001f0001fe01ef7
  | 0, 15 => 0xff1f1e00020000000003c000f8fff80fffffef700f8e001ffeff1f07e1fe01fffffffffc21e000e018ee3de3eff1c0701c001ff7
  | 1, 0 => 0xff070ffe01f00e3f8ee3e1e0f800f80001ffef71ce7e1fdfdfff00000fffe1ff70000003dfdeff1ff801fffe00000070001e1f07
  | 1, 1 => 0xe3dffef7ff070fffe0100ff070fffe1f07ff000fc2000001f0701c201f00e3f80e3e1e0001f0701fe01f00fff80ffffe000
  | 1, 2 => 0xe0e001fdeff00070001e1ff700000fffffff700e0003c1c000ff1f0fc3e3f0700000e3fffef7e0000e01e00000000003c00000
  | 1, 3 => 0xff070fc3e1f00e0f8ee3c1e0f8e3070e3fe1ff7e0f8ee3dfe0081f0001c3e00001c07e1fde1fffffffffc3fe000e0f80e0000000
  | 1, 4 => 0xe0000e00000001ce7e1fdfdf0f00f8e03dffeffff000fffe0000e0000e0001ef71ff801ffffef7ff1f0fc3e3f0000e0e03c1deff
  | 1, 5 => 0x1c0001c1e00001ce7e1c1fdfff1ce001fdfc0001c0001fc01ef0e0180e01e3ef7ff070fc3e0100e0f80e01ffef7ffff0fc3fff00
  | 1, 6 => 0x1c0701c1e0100e3f80e3e1e0f700e0e03c1c0f8ff000ffe01ef700f80001ffef7ff070fc201f0000f8e0001e0f800e0e001fc0f8
  | 1, 7 => 0xfcff0fc1ffff7e0f80e001e0f7ff180fffe2000fff80ffe1e000fc1f0fc1e3f07ff000fffe1ef71c0701c1e1ff70000e03c000ff
  | 1, 8 => 0xe0000e000000000000001e1ef7fff8effffe0f81f0001fe01ef7ffff0ffffff00e0f80e3dfe00000f8e03dfe00800000001e1e07
  | 1, 9 => 0xe0e03dfc0f8ff180fc3e2000ffff0fc3fff00e0180e0002007fffffffe1e00000000001e1ef71f0001fe00000ffe0effe1c0ff
  | 1, 10 => 0xff00effe01effe0ffee01ffff800e0e03dfc008e3e0ee3e1c0fffff8effffe0f8e3f8ee3e1e0f8e0f8ee3dffeff1cffe1c1ffff8
  | 1, 11 => 0xf8e03dffeff0000003c01ef70000000001e0000f8e0001e0f81c07e1fc01ff8ff070ffe01ff7ff180fc3e200000e000001c000
  | 1, 12 => 0x1f0701fe01f000000e03c000fffff8effffe0f81c0701fde1f00e3f80e3ffe0f7ff070fc3e1f00e0180e0003e07ffe7effffc108
  | 1, 13 => 0xe00001eff00f80001ffef700070001e1ff71c0701fde1ff7e0f8ee3dfe008fcffeffdfffffffffffc201ef7e3000e3e01e00
  | 1, 14 => 0xe0e0001c0ff1ce7e1c1fc108ffe0effffc0f8fff80ffffe000ff070fffe1f000000e03c01eff00e0e03dfc008ff000ffe00000
  | 1, 15 => 0xfff80ffe1e000e0180e01e2000e3180e0202000e0f8ee01fe0f80000e03c00008fff80fc3ffef7ffe7effffdff8e3000e3e00000
  | 2, 0 => 0xff070fc3e1ff7ff070fc3e01001c0001c00000000180001e3e071f0701c201f001c0701c1e1f001f0001fe000000000e00001eff
  | 2, 1 => 0xe0f8ee3dfe008e0000e01e1e0000fff0001e00000ff0001ffff7fcffeffdffff81f0701fe01ff7ffff0fffffff7e0f8ee3c1e008
  | 2, 2 => 0xe0f8ee001e0f800f8e001fe008fff80fc3ffe07e0f80e3dfe000e0000e3de0000ffff0ffffe100ff180fffe3ef700e0e03c1c0ff
  | 2, 3 => 0xff180fffe2000ff070ffe01ff7ff070fc3e010000f800001fef7fcffeffdfff081c0701c1e010000e7e001fdfffff000fc3e0000
  | 2, 4 => 0xe000001de071c07e1fc00108e3000e3e000f7e0f8ee3dffeffe3000e3e000f7e0f8ee3dfe0ff00e7e001fc1f8e0f80e3dfe000
  | 2, 5 => 0xff000ffe01ef7ff1f0fc3e3f00000001fe0000000f800001e0f7ff070ffe01f00ffe7effe1dff8ff070fc3e1ff70300003e000f7
  | 2, 6 => 0xff070ffe00100fffffe0000000fffffe000000000e0e001fc0f800e000001c0f01ce7e1c1fc1f800000001e00f7fff8effffe008
  | 2, 7 => 0xe0e03c1deffff070fffe1f00fcffeffdfff081c0701c1e1f07e0f80e3c1e0001c0701c001f07e0000e0001ef7fff80ffe1e000
  | 2, 8 => 0xfcffeffdfe108e3f8ee3e1e0f800180001e3ef70000e03c000f8e0f8ee3dfe0f81f0701ffe1ff71cff01c1ffff7e3f80e3e1fef7
  | 2, 9 => 0xe0180e01e20001c07e1fde0108ff000e00000000007e00001ff800e7e0001dff80000e03c01eff1c07e1fde1fffffe0effe1deff
  | 2, 10 => 0x1ce7e1c01dff80000e03de00f800f8e001fe0f8fffffe0001ef7fff80fc21e000ffffffc200000e0f80e001fef7ffffefffffff8
  | 2, 11 => 0x1ce7e1c1fdff800e7e03dfdff800e0e0001deffe3000e3e0000000f80001fe000fffffe00000000000003c01e0000ffe001ffff8
  | 2, 12 => 0xe000001def7e3000e3e01ef7fff80ffffe000e3f80e3ffe0001f0001fe00000e0f80e01fe000fffff1c0000001c0701c1e1ff7
  | 2, 13 => 0x1ce7e1fdfdf0800f8e03dfe0f8e0f80e01fe0000000000001ef700070001e1ff7fff80fc3fe000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xffe2effedcbfadad48dbdf8440fcff4fd9fff3990540901e8400fffff021010842529324627ef7b5626b42ccbba6cab46d817b39
  | 0, 1 => 0x63d7c6377975af0fc0f11fe421f7bdbf77b7ce7d2948d3190000ff808ffe908429c5749c9e9f184ae2e4bc5c3f80f03f4727fca7
  | 0, 2 => 0xfdefee73ba1eebada27d9007f70016f7bdd6b5ad75b5ce0007f70016f7bd000006567ef7b6dab46da17b3bb51d1b43a3c07
  | 0, 3 => 0xc0340c801b18003d3001274a500000f56b6c630701b06601ad663a8b2aa6879eb87e6b8dee7f96febf6fe7ffff0f7c80ef6ec63
  | 0, 4 => 0xfdefef7b9354b927e84c6000002ce6ee73dad6cdb9d81080f03f0ee01bde00000fdefef7bfffff631170a560a8061016021
  | 0, 5 => 0x63a8b636160e7f2fcaf35fe4e19254a925e84c0fffffb6381886f3fcbf33fe4a7ff808ffe9084263a8b636160e700000f56b6e73
  | 0, 6 => 0x84240884831862a8a634160e14ad7c4bd79758b5150b43a1c029a16c9a9801082f2bf2ee27fff0d0370ce01bdeb51d1b43a3c07
  | 0, 7 => 0xfafeefbdfe7f9006260004c3b89c5749c9e9f18fffc8ffffec630f7db0ef6fef74a8084bc10040ffd7cffff9f5afffffffffffff
  | 0, 8 => 0x6de7ef7bdad6cdb9d8108000009cee8f5afffffbebe9f9e9c574941818009f57f96381886d0d40d11d800063fff6377f7ff
  | 0, 9 => 0x7760016d7b8ff808ffef8f5a40e004105c02000000fdefef7bb5091b42a3c07006b70006f7bd9c7f79c9effbd0057400169718
  | 0, 10 => 0xbceeef7bfffff22303087def7edfdfdff867a9b676178e7fffffbef818c6bd7f7bcfeffff4ae2e4bc5c3f80f03f0ee01bde
  | 0, 11 => 0xbd5f5bcbebf1f94150941a1c0090540d11fe421b51d1b43a3c070f03f0ee01bde0f03f06201886000004107e421ff808ffe90842
  | 0, 12 => 0x9f57c9efe9f5a2f7db2ef6fef79c0009c88080063a8b636160e79d5759cbe9f1e63fef6375e1ef9c5649c9e8f18b51c0b43a2c03
  | 0, 13 => 0x63a8b634160e5ffc2cffed8b5af0ff7f11ff7bd007c00016e421b5080b42828034ac2c4b858108fffff0a94939cfffffb6383887
  | 0, 14 => 0xb53d0b43a7c2300000fdefef7b4aeaf4bc5e3fdf0fc0f11fe421000009cee8f5afffffffffffff98564989e87180f01b0ee01ad6
  | 0, 15 => 0xb51d1201030050000008c48358fffdbfffffef7007d30016f6b50f03f0ee01bdeffffff73978a79f17f9ef81bde2d2b72ce27fff
  | 1, 0 => 0xff83cffe91b5a63a0a636140e2007d30016f6b5f7bdbf77b7ef700000fdeb6e7300000fdefef7b0a5480a948000001d100123405
  | 1, 1 => 0xfdefee73ffd6cfffd894aff9d9fffb3c47b5000b42808020d0340ca01b1a63a88636160630f03c0ee01b5adad48db9d8000
  | 1, 2 => 0x7f70016f7bd007f70016f7bd00000fdefef7b4ae2c4bc5c378b51d1b43a3c0700000f56fee73f0fc0f11fe4214ac2c4bc58358
  | 1, 3 => 0xbd574bcbe9f1a6aeae6bc5e3f967fff6777ffffdad6cdb9d81089d5649cbe8f1a9f57f9efe9fdeffffff73ffca7f0fc0b0180000
  | 1, 4 => 0xf0800f1090000f79d9f73b3c074afff4bd7f7fdffd48ffff8c42f5a93f56b7ef70a7db0a96f6b594150941a1c0067a9b67637ce7
  | 1, 5 => 0xbd7c0bcfeec63bd7f7bcfeffffdef48dfdfcc60dea1adfcb5ef0b53d3b47a7ef7b5140b4380802f5fd3f57ffef7fdff4fdbfff3b
  | 1, 6 => 0x98564989c810863a8b636160e742a0a434140e0ffa9bffeb7ef7257d32476fef7bd034bca81b1a006a60004e3b9007660016c7b8
  | 1, 7 => 0xfdff7fdffffff61a83616160e7da948db990000ffa88ffe96863b51d1b43a3c07fffdbfffffef7b57f7b43effbf2328b226060e7
  | 1, 8 => 0xf0a80f10b6421b57d3b47efef7daf6edbddc3f84fa1b4fe15af6ffffcffffff7bdad48dbdd80404ad6c4b958108b51d1b43a3c07
  | 1, 9 => 0xdaf6edbdfc7f8b5140b4380802f5fd0f53ffc232108120202007ffffffff978e7007d30016f6b50f0080ee00842ffa8bffe968e7
  | 1, 10 => 0xff83fffe91bdef0ff6f11ff7b9dad6cdb9f85086beaf6be5e3fffffeeffffeffb63a8a636160e3fffffffffffff9c7f69c9effb9
  | 1, 11 => 0x6ffff6ff7ffff6fa9b6fe37ef70c4340c869f1800282000060a10e03e0ec01bd8ff83fffe91bde901409018000060e806107e421
  | 1, 12 => 0xe03c0e801b180300b026000c6fff6efffdcbfaded7cdfdf9f58f3fcbf37fe4e794150941a1c002509124223c07ffd6cfffd894a
  | 1, 13 => 0x370000139c40fd34157f6f5003d3001276b5fffffffffffffd2d48d31d8000ffffffffffffffffffb67a7ef76781867631e52
  | 1, 14 => 0x21283206060e798564989c8108fff6effffcffaffd48fffd8842ff958fffb1c420f43f0ee69fdedad6cdb9d8108da808db890000
  | 1, 15 => 0xfaa88fb896021b01c0b01a24012108020202003f0fe6f11fe7b90a02c0a800108f5fd3f57ffef7fff7effffdffa6380863610042
  | 2, 0 => 0xb53d3b47a7ef798564989c8108bd000bce80842251d124323c0705010042018029c1509c9a1c002f2882ee26c630503704601bde
  | 2, 1 => 0xfafecfb9fe529f5d50f57f9e52007f7001070a5007f70016f7bdfeffeffdffff92f2bf2ee27ffffffffffffffff6aeac6b85e129
  | 2, 2 => 0x60a82610160a10056400148108f5fd1f53ffc27dad48db9d8000fad6cfbdf8758fafecfb9fe529ffbdbfffb7ef763e8b6367e4e7
  | 2, 3 => 0xff9c8fffb2c43ffabfffeb7fff901409018000000293000276b5ded7cdf9f9f189014090180000257f72476ffffb5140b43a0c02
  | 2, 4 => 0x65e916527fc270a02c0a800108f3a8bf36b64e7f7fdbf77ffef76ba8b6be162f7f3fcbf37fe4e7007660014c3b8fafc8fbdfe461
  | 2, 5 => 0x6fa9b6fe17af7b51d0b43a3c03000009ce8084200283000060a5de83cdf891b18ffe3effeddbfabd7f7bcfeffff0300b026000c6
  | 2, 6 => 0xda82cdb890108ffffff3191084dad6cd319000090766901ec7b840e024145c2f098766989cc3b8b17c3b07ee4e7dad6cdb9d8108
  | 2, 7 => 0x67a9b67637ef7ded7cdf9f9f18feffcff9fff39b57d1b43efc276aa886bc160610501104201806f0a93f10b76b5da808db890000
  | 2, 8 => 0xdad6cdb9d81086beae6be5e3fb003d3001276b50a02e0ac003d8daf6edbddc3f89f57f9efe9fde9c7f79c9effbd67a9b67637ef7
  | 2, 9 => 0x90140901800009a56c9a9c8108ff808630100000003600001398006360004d3b86f83f6fe11bdebf7ffbefeffffffebfffefffff
  | 2, 10 => 0xc6360c84dbb89a56e9ade87d8007e60016e7b9ffffff77b7ef7f5a80f5296823dad6c9218000065a9365637ef7ffffefffffffb
  | 2, 11 => 0x9c7769c9edfb84af7e4bd7d7f8256b72466ffff42808430100000054000148000ffffff31b74a56fc3c6fe79f5a007f60016f7b9
  | 2, 12 => 0x65e936567fef767a9b67637ef7fafc8fb9fe421f3fc8f37fe4630a0080a800000f8fe4f99fe739fffff9e981884b53d3b47a7ef7
  | 2, 13 => 0xded7cdf9f9f184afee4bd7e7f9f0bc0f11b64212d6b72ce6ffff257f72476fffff5fc0f53fec23
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 52 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 52 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 366 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 366 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 366 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 366 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 9 0) :: stateWiresD n (ids >>> 9)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 9 0) :: stateWiresS n (ids >>> 9)
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
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 1000003 zs)
def CN0 : Nat → Nat
  | 4 => 7
  | 5 => 227
  | 6 => 1228
  | 7 => 604
  | 8 => 17
  | _ => 0
def CH0 : Nat → Nat → Nat
  | 4, 0 => 0xcab0a09f99f5e47f81b3ebfc78e7abd9390638af292d48fc1f086857
  | 5, 0 => 0x1f15a39f1e6dff621e5a2fce1de35afe1daff8c81d5ff33e1c8aad8e1bf458b91bcc317d1bbf72901b3167af1ab538911aaf45d11a4f54801a1f64fe197181f51848de5a182b6478176426651743257716c7b1be162ef97d15c094ae1574422614aaa3621277241e11d3e14711adfbc21151fea90fe354dd0f861f580f5cebeb0f10d64f0ecee57e0e1d06410d3d6aa10d0b482d0c8e60ba0bbdfb110b67d07e0ae401380ac070440a821d9809fff53109e1e8ee088cc7e7084284a2081e3a5d07978baa0789be2106a3543f0691cbed06472ae006113388053e610b04402a8a04250e810312d2fd02f9e1a8024098dc00c62bfa00a22b0900643de2000caedd
  | 5, 1 => 0x51d98c78518697ee515e949250c45b0450b155d34fda153d4f9b775c4e4c7e9d4d2dc0ff4c3e847a48cec29347f79c974754e53e47060c39433e81ff42c7391542450942404774393fef61803fd16f653f633e6c3f47e49d3e54bee93c11cf6c3aa8625e3a25fd8738a867a03806e39b378e854d371508823653ad4735d84c3634229ed433a1f9e2339a75ca333d705a31b5ccef314ce44530e71dd630b9a13c307d78f52fbf4cd32e19cbb92cd616bf2b1917662aac41af2a407d78292d48fc28d30d01285fc33e27c81e0927b26232278b78de275e35ae269de2d625fe80362542c8042456b24b22313e9621cabe6721ac407a20e16f64203d89001fc631a5
  | 5, 2 => 0xa39865f5a2eb78cca2111c32a17b27e49f0014089db5860c9c5b7e4399bc55d699b1619d9992014b98934810983bdc0a982e3adf954d19db8fdbd9e38fbce6e38f06225e8b303fbc86f528d785bdcd3484d14e9d82e891fa822f7fd2819e18fb8025f6ef7fc65be77eac13c67d06e9a97a15de527976c86c78e0647d77f822ee750df1df726361d171d8b8ff70c6637270c5a90370732206704a3d256ef3abbc6eeaafdc6c143d136b41b3f26aa9974a6a99b11b69cb37b26730868267137a826708d1e766e4cdd3663c63e265d9d98a626a6a5860b855205ddbaf485d4ba9d95c07d5765ad9699f5a258a4859fd610059688d28595888d6580c6a3752908b1e
  | 5, 3 => 0xf63c290cf37d2702eb4dbe4deb13f03be5a5c98de1c12a78ddc857addd26c419dbff4883da7e97fcd4b0b276cfae558bced3bddbc97d7bb2c5540778c409a9abbfc3b1bebe410ebebc668b05bb339645bae04f79b7cedcd8b6ec6fd9b62170ddb372f22bb367e698b366ba40b0e3c988b0d6474db067dd1bafa21555a85c7836a72959eda4f4b99aa4583e8c
  | 6, 0 => 0x7e750a407d75e6607cf7354077507c1074589810743dbf907152ea207096d7b06dfa44a06db8b2906d2e52f06bb5a1a06a3e89006a3543f064b5c1006421e04062c8a6e062a88e40628a47a061ada3506113388060d42220609407105de8dfc05da293405cad693058a4a4d057c87370579256c053e610b04f371e304df5bf104d6d930045a2fd7044953d0040cc18303ee26f703b1489103973fdd039086ce034396d6033f652b02eb5c2402d3d90102cb9bb202a7b4b8027f5a230230426a02084a0f01ec68d7019ffeda019e786a0187392b01762ada015db69d0125cffa010d96c100d8424500ca458900b358a70093fbeb00740e06005b91d90016ba0b
  | 6, 1 => 0xdef172e0decae5b0ddedd280dcf3a700dc3a6f30db99d510db80b310db71a910db3eff60da807900da32bfa0d3eb0860d18496c0d0b482d0d0573f30cf90be50cef07920cc80fdd0cc4ca2c0cb9c8a90cb307eb0caa21390c7144ec0c6f25910c6188d90c5cd14f0c3e489a0bfe1f9c0bc9a7b30bc4958f0bb35e5a0bb05dcf0b998c9d0b4359820b3b44770aa795c20a9a4ac00a77b80e0a3f7bc20a00f7c609fff53109d5426609ccce0909ba014b09acaee80982d2c6097861a90975065e096d5de00960e41b08e2c15c08dec38008da1bdf08ce712108c41c2208c364a008a89fa2089422340879f77d08743952086142a40859e93e084320e8083cdbd0
  | 6, 2 => 0x16ec23c2166e481d165a931d1658f867162e4ee6162494f015a8c131158212cd15744e8f1538985a14b2edb714a953a314705e20141a845b13f765fe13e3913013b0cffb13a4e475133f557c1334dfce13204adf131c70a41307789912fb2bf212d1dbe012cfd7f912c24e7012ba5892126805971260f536124615de1220c1d111f7318011d3e14711cb089c11c26f5f1191f01d11855ffa1165a3d31159c969114f7cb510ad884d10a3a207107b6924107afe8b105c85221029aef30fdc409f0fd76d530fc937ce0faa37460fa48a8b0f78da370f5ffcd50f5cebeb0f213af60eb8ce0b0eb34ad40e7141bf0e3a43fe0e3986930e2fc8370e28ee890e0e73ea
  | 6, 3 => 0x1db552611da8796a1da2ab851d98b22d1d9823f71d6b16751d311bc01d12cc301cf759641cf749141ce408841cce5b9d1cc2282d1cb9f3e41c47ce271c3862891c276eef1c26bc301c140d191c13e94e1c08ee991bf866621bbf72901ba44b831b7825e21b1246761af3de921acaf1351abcee321aa300061a8f914c1a82e8b61a7e80611a5f52bf1a5b607d1a34343d1a27102b19e5145f19d3d07619c9ed1919abdfdc199e1bc01983052c1926c5ef190406ac188cbc0c18840144188009bf1869a8fa1847f33d18415b6a1838832f1832a690183107f517ed5b5d17ba343d1785f636177cafdd177b9f2f176f810d1764d9e817642665171f5b9e16fc3c48
  | 6, 4 => 0x259dbb20259c76ad259b8b6f2597ca052550f70f2550a85e252c7943251d316624cba3f424ca7bf624aa7853248ceea9246efac424539f322429a2892424f4992400c48e2400c39223c52ecf23bf68cb23ab67712395f7f4237ca80a232d043f232ac7042322fb7123140d5e2301c2c122ffd0cf22d3d54222c0184322bb8c3f229c7e59220aa36c21f27d3b21ba31b921ac407a21a6de76217b3f4720efe56720b1875520ac3c3e20801a5220759ee12069f209202db4f41fc631a51fc5ca041fbd4d701f92d1c81f6840531f442b261f2749db1ee61cc01ebf29001eba8d381ea388b31ea025ae1e85cb5b1e74f0791e5957371e35e9c41e320dcd1e166e5c
  | 6, 5 => 0x2dd642be2dbcd2a82d9e359d2d98a9c12d93e5f42d7b937c2d6e39982d3439402d325c592d2c49bf2d1b3bd32cdb5b0b2cc9c0bf2c87bdcc2c8434e82c8390072c7d6a5a2c48b4ea2c0891012bc3d22c2bb7f2252bb6a8c32bb6443c2b86ab602b6946512b5f44f22b31fbf62b1007372b01c59c2af33f3a2a40fe1c2a09fcd629fe148d297add82295e11c329588421293612b1291b831d28e9d01228e96b8428e4761628cc992328ba2c7d289c5dda285fc33e2831ed512819664927e442ca27d16df627c72e7c27c3673527652ff62758963f27156a9026b2b75c2693590d26539a372633e0972619c71326053d9125f0434125e841dc25cc098c25cb1d10
  | 6, 6 => 0x3847b246383cc4fd37fd3be737f8feb23763eca236c3519236a958ef368d42fe3653ad4735fef91635fe44ab35d9275d35d7937c35bc77a73580f8d0351fbb673512254a34e2bd1e345535d5343dec2733d6566b33d4398633988fc1336545d233632b4c3345f93b333561c1329a5e9a3294008732858a42326a56723266236a321a2fba3210209d320ba96431d1fb8131c88f67319e428d3178c71c30e71dd630e25a0d30def03b30ae7298306c02d230548ed7304775692ff8b27e2fe2cd0f2fbc51522faddf912fabd6802f8753ff2f7d34bc2f3483ed2f1e574b2eec7bb22eeb32c42e93e8dd2e3002fd2e2207b92e0ec6302dea5ede2de9d6532ddc47fd
  | 6, 7 => 0x407df6674047743940353f8c4034da1140076d2b400068bf3fe904363f86adf53f1578573eef26613ee916333eda539e3eb60c7c3ea74b873e8853d63e7d994f3e60a6713e0873de3df17df73d9591df3d6695a13cfb59403cdacc003cd241ad3cc7e5a73c68a3263c4e245e3c382f233c22afc33c14984f3bc21fd13bb384ca3bb192ab3ba2f93b3b4b2c113b3459663b0879e23ab507d93aa545533a893eda3a86957e3a8269f03a734e093a584c8b3a409e4539f7126d39ea33cf39d91aea39cfd1f2399c7eae396c044e394ff0d83945cef1393afded393088263914513c390c547338f82eeb38b4eea4388cc9613887c6403886c5cd387d0c583873a74f
  | 6, 8 => 0x493e2806493913b748f04eba48dee09648ac39974888254e486be488484bc25d4844c368483aae9b47e6e7cd476d14f6472a1ea3471a22fa46eb1c9846d02c754693f181468eb82346654533464cbfd94638af2045ccc37145b7ac424597909a458aedf0456ebb6c45623bed4553ca3f45407e45452ac1f54508e3e944fab2de44f9244644ca91d244bafc3f4450cd1e4431706243ca91b543b7115a43b2b6f3436d42fa4363c5ab435cf6d6435b0f24433bb26842d079e342af0fcd42a43d2a429c53a3427919ae4208bf024201c10541e590e441c98126417bbe4541744576416b8e45416052ce4142c5ee4125757c411d375d4103aaf840fcc6c0408ef32b
  | 6, 9 => 0x5312c78552c234e8525163575244edb1522b079d521c46cc519956ed5192b1fd516084885140b36d510149d750ec3db750e6c68b50d0f60750aefff1506451445028b3ba5018e0494feee01f4fc3e3f54fb99ab44fa750224ec91afe4e9346a74e5924bd4e4baaf64e498e524e3cef914e09d86b4dd2bac44d8e30d04d751c6b4d58f1664d41cef04cd8f4264cbc47b54c8850664c87e9974c57face4c5569904c5365b74c4661664c43c0724c31a21c4c0fcd5a4bce76dc4bc78bcd4bbbc1b44bb947a14babdbbe4ba53e164ba28b4f4b5d49c34b1b5ffb4b0945444aa76ad44aa3620b4a3b308b4a2f03644a0fcc6349c0568849b932bc4989e7d1495fd42c
  | 6, 10 => 0x5db617865d89a5b55d7a3a115d4e12c75d43d4375d167fb05cd041e85c8b9bce5c5d80b05c4863c55c42c5a65b76df3d5b72db965b3779e75b363c9b5afd07de5ae911e75ad9699f5a9fe9205a9af4d95a8877d95a7456665a654ad45a496dec5a434ef359df7ed659b94cda599aa0d9597543e1592fe5a6592baf5d58d4ef6258b91c295850ef325829c1935812d4b657ff865457ca698a57c681ad57a03eab5766b1c8574f880b56fe4e6156f89d6a56994a8d5676c6d9564ff5e95629e1e95625ec7455d5082055980818557a5490555f20ea554c07d25534678a5533e30554ff706354fae98c549596da548de1645448710153cddfe6537543e253429f9f
  | 6, 11 => 0x6804f89567f7949967eef51c67e42d4a67dc80ff6759e0d6674e890967139bc1666b72c365cbc4ca6559da8a655823736538f6a2650650e565035a9d6500180b64eae35964e3c09c64b2112f64b120ec64559dca6428a8266421f9aa641c220663fad21963d40d3d630a94a46306dee76304f19a628efe48626319c36250ff6b620d46d261ccb374618758ce6159439d611e82506106611b60f30a6b60b20ab260a9e83760997b3b6087202d60718f726070272c6066a958603ff60f603fda746037f7596035bbb56007e8ff5fa292195f8ef0f35f81569f5f1f7afd5edc39395ed7f8c55eab01615e874af35e7ef6055e56e5985e41f6365dece5a45dba9c3f
  | 6, 12 => 0x73abcef57386283f725b1fc07239f1977236ab4e72150aa071ea7843719b4271718ef4fc7117b9d070de8a5070c8406b70c0cee5704c2aa6704a3d2570026d1b6fb43a2b6f7f0daa6f63f8496f47a2a86f46018d6f3fd78e6f2235ec6ed902db6e617c5e6e4f16946e46c16d6e3b8fd46e351eb76d7a6e9b6d4b8dec6d2517e96d16844a6cee301b6ce653976caa2e496c94eb9d6c8c83596c1b39e86c06f88c6c01ccc76b6efad36b16e09a6b06a1006ad5cf626acbaae46a9a02ee6a77883f6a57745b6a4bbb576a2a1c116a251e8b69eb7c3669dd28a169c84ea069b8152a697b6b3468db0bcd68d5c61368b6ac3968533cb6684d2b106843d321680601e7
  | 6, 13 => 0x80a859318025ebc87fc4ec647fab33bc7f8f6eb47f83467e7f632a4e7f5e131b7f5259307f42e45a7f03704e7ee5ef667e5d8d707e56e81d7de33e517d3652297cd63dd37cbba99e7c6acb837bf8e77e7b7d24d47b4bbd9e7b40aed77b366fce7b1919e97afb446b7acfa06e7aac15577a847cbb7a79117f7a728b397a3067277a226f7c7a212c747992802179858c1479548bb779405ef978e6a6cd788539bb7884f7c5786741667855500f784be55e77d155bf77939a067783e7a87765249276f5070076cc204876bedfcc769f2432767a80f375f7bdc875e2a29075be80047581ee76751328bf7471dcfa7470c845746ad6827422badd7402b2ed73c19e09
  | 6, 14 => 0x90b3422090767ec4902a02ef8fcadc288fbce6e38f975dbc8f575dd58f3271f68f278d128e6257428e539c1c8e0374748db4ee2e8d9fa5cc8d9c26fe8d803c648d735aa18d5ab60c8d4660e18d27674c8d1a68078d17cde48cdb4d3c8c47475f8c40582f8b3eecce8ac186078a91f1db8a8877cb8a6bd4ca8a48e9df8a1501a489e84c5789b0364c89a9bc2688f47a2488d7c1e68813974d878b826a874b47b9872e0bca8729969186f64df1866e8970865e2054864ae5ac859094138565bade8526004e850478b68490e021845d0e3684422e0d84392c6583c398858393f27f8384282483579a7483469dc38304681d81d06e3881bd630981a28021811a24fb
  | 6, 15 => 0x9d0bb2f49d0220eb9cb1da3e9caf613b9ca4155d9c8d8d399c3d06f89bea39a09bcedd8f9bc20c2b9ba6be969b7da1f19b630aeb9b3c80c89b0e2ea69af9e2db9a8b295b9a7992489a6a67fd9a450bfc9a21855f9a19a7cd99f7c60799ef506d99ba569699b1619d9992014b9938d443984d68fc982f73d2982e3adf97e460409784487e9761daab9701f0a596e3436b96b3be4396566aa29648b91795d0f94095b4af3d95b1303f957be137952f9bc6952b79de950d237895035e9a94fa9e3b94f3e1899440d6d89429d14e93c6ec2e93442d0f931b59bc9311baae92e03eee9257d75e924fbb2792467c2391e563ba91bebb3f91b00efd914616a8910ee596
  | 6, 16 => 0xb25429ffb2477228b1f854f8b1373356affba1eaafa21555af6b6a3caf3abee1aeebe03aae530f3dadcdf285adcba8a9ad2b9ed3ad1b0362abf898a2abc29c79ab8cf64fab6be25faaf9716eaa650533aa62b89eaa46a928aa2640b5aa2524c2a97b65f4a972c6bea8d50411a8a93171a88e34aea886c910a7f31241a7239591a70aac96a70a2a74a6660099a64fe007a64b5616a5b6bfcaa5ae28dca5a19cf3a553ff32a4a61f8ca4867bc2a3f621ffa3f31982a3776d54a330cc03a2eb78cca275db9ca25a1658a249e994a24137e6a213d2faa1502d8ba13caefaa0bc9ea1a0952b73a07b96409f5b2e529f5ac9349f40d0259dbcc8bb9dacd5ee9d59e8e8
  | 6, 17 => 0xc8c374c5c786a348c76c34c6c7072d5cc6b92d9ec5eb6abdc5e7b6fec55bcc56c51a15f7c4209fdcc333736fc2c2b83ec2a1d1f0c23eafdec2377d54c1847113c11713aec10986fec06f06c3bfd76168bfd61932bfbb9b1ebe889baebe77cbcdbe410ebebe10267bbe050cf0bd641f49bd3bcf05bd0ce7cdbd028e72bc7e354abc46cb72bb9ba0fcbabeaa97ba14f429b9ac4dd5b90147a3b8fa90c5b8d91788b8d26536b87d3643b85c348ab8599dc1b8511326b6f50fffb6f39aa2b5fdb3eeb5f71d38b5b894f0b5b0459ab5ad9831b582df9cb4d54b79b49a0e12b487dd25b418f70ab40b3d75b3659b4cb2f4b7f4b2bd8af8b2b1137bb2a92c67b25575bb
  | 6, 18 => 0xec573d6cec0b75b6eb4dbe4deb13f03bea31bb06e92ef807e8f2afa1e86ed660e6caaa13e4e97d52e43d1fa6e2317988e1e5382ce1448323e0f88c35e05e250cdfa8491cde684b38de0d0223dc8f2ed9dbf76771dbcc0073da8cf733da2864b7d8ab79b8d89731fed832ce53d8179fffd7293eacd714ed9fd711471ed6da5928d6cabd22d5687a3fd5032742d4e70e95d41448e1d406ff51d3ae1b94d2b745ded1e93b11d1d91730d1013b56d09c0fefd0708f40cff4b5c2cf071cb0ceec76f7cded990ecdaabc83cd1aa95dcc4e6688cbfc0b4fcb5465a7cb3bfedecad8cfd7ca3a02daca325bc2ca17eac8c9d7a56ac9b9d25cc966df36c90074c4c8de8473
  | 6, 19 => 0xff3a1d8afc947e34fae9c6a1f9fb775bf729faaef5b0a26bf37d2702f14b22a3f124d9bbf0b3e325f02f068bec65f118
  | 7, 0 => 0xdefa3000d5746d30d18496c0cffd7360cef07920ce4034d0cc079740c2f01600bf564e20b79c9fa0b1b46d40b018c320a9ff33e0a3fff4d0a3b18130a3861270a071dfe09d4975a096ec28c0924bed20884742c083a517307fa6f4d07c71ef907a7c23d07731b730747301406ac2f2f065e08cb062924fa061ada3505f592a905cc009705706f5f055c5ffd055047ea053b580f04eb14c404d7fb8f04d6d93004a30531048730450485db22045237a5043e32af043cc9ae040ce6fd0407aa1703882c5d034877c5032db16d02d4d5e302bd17cb02384c300232b86101e2f9bd01bc646001126cc30111853700c6a76d0093fbeb00413eea002a808900256ca1
  | 7, 1 => 0x1d2ffbd31d2089d51cd43a8d1ccef8ec1cccba801c47ce271bf866621bee03d31bea292d1bc09ddd1bab38231ba1da451b8ac9331b5222fe1b4d3f551b31594a1b2787e01a816d6b1a5e7d251a5b607d1a520b1319cc15c21995312e1869a8fa185ece5518415b6a1826e322180a92f317b050e41778305f176dc61a175fab9a15f9964515e7b8de15cc945d157a8c30155099a3146aafa6142f9dd6140585ee13e6f09113e5d78713dc5362131f7df112b5b6bc12619bce124615de1211a3e711e4b93411e3b55b116028b9115efdf41140590b11365c9f111b7ab310c8c51210b7f157101dd5d90f8b020b0f7dd02b0efbb7b50ed8d5490ec4e3590eb8ce0b
  | 7, 2 => 0x2e8159822e6450c52e5b849b2e1f84a42df1ca722db05d022da6f5c42d8799082d7fcce12d1e1da62cbaf5722cadd7bb2c85fb632c3eced32c18839d2bc165582bb6a8c32a40fe1c297d23b6290d883828f45e3228f0d06628ba2c7d27944dfa273af8a526f706fc26819d642659781a26539a37262de7072619c713260e095925fa8b7625cc855f2550a85e250a6d4324c559d624abea49248701a4246efac42424f4992423c051241e68652406c30a2402f98223ff0ba92393b608238a582a23758aa4235b947922812646222df859218dadf72140f1ba21231b93202d630b1f5521bc1f1c7fe21eb6090f1e72c52f1e52c7bc1e20619e1daff8c81d9823f7
  | 7, 3 => 0x438f81704336012f42c1b1d94209743441672d164125757c40ec6bdc4084dc5f4051b2984034da1140293e7740171a6d3fe6b3ad3fd5b67d3f72752a3f6f76303f57ed133f1d88a23e75a77e3e60a6713e54954e3d977b663d9591df3d2ef8043cfb59403c71d06c3c4f26213bf248c63bac6b283baa22083b76f1d13a494ac339addbea390c547338d7d57738cdbebb388d73883760f4c036eebd8f36add9e0368d2999367e2d8c35a5f93c353d5a67353b279234f820503403386733e0298a33ca166033bcc2c633b91ecf339ff7143392d31f336545d23363498a32fdbe5132e325e232c18955309f5256308accb22f9c62fe2f3483ed2ee7105b2eb5e0ea
  | 7, 4 => 0x567d201a5657a5ce55ead64b55a9c714559bd678557b17af554c4e075533e30554ff7063546ab7fa5459f7e253c640cb53a6e40f5244edb1523f23d75201b16f51a2669151933dd55018e0494f52fcd24f082c344ee529dd4ea382274e9130f54e61bead4e5924bd4dd2bac44dc17cba4d8e30d04cdae9cd4ccb72944c9cd0384c066eb44bde58244bce76dc4bcb5ce44aa76ad44aa3620b4a01d25f49f3585649bd29764984d6d149607a05494e9f8248f04eba48ab837048903a2a487679fc48491b2c479ce6e847498ab0473799a0471fae4f46fa79ff46c32fd9463ca74645cfdf1d45b7ac4245502ba944ee813744ca91d24436256c43cf3a2343a45cc6
  | 7, 5 => 0x6ea55f046d9e86056d30646b6d28772e6cda50ca6baf43206b69641c6b54438e6b06a1006aea14116a997d5f6922bc00688fd8f6681a276d679aeb2b6758f58766000fd365f6b1f56598e99e658b338264b5c4ae64559dca63fad21963bebf176351c36b62d46e6e6265277d61cbb62f6106611b60a332d4609fdb1e6066a95860560de75fa292195f9d7e4d5f146d405e07bcde5dece5a45da2b59d5d9244f95d0d2eb25c47a9575c13c8825bf8525d5be85f655bc5debc5b1d469c5aed17a95a5167a65a47d5ca5a2cabd55a258a485a018edd595ff3e158dcb0c858b50275589c7b365812d4b657f9a517579ddafa576cb25c57558e4f56e344bf5683d910
  | 7, 6 => 0x87c0ad88877e48af86c6b4d9865c6da485c9ebd5857f84ca853df1fb8526004e847170d9845d188a845126f484381d1483f9136e8304681d82e7b02882711cc58166f3aa8157f562814ff47581076d9d80a85931804d74e47fdf2e267ede36f47ed5173c7ded13067dd934ea7d3652297ceaf6287c7ac5407c6f50277b58cf9c7b1919e97a81cded7a5ce0897a306727799bdb6879673c1c78f0dac1789248d8780211ec77d155bf773fd31077299acd76ec995776cc204876b67209766bfb75764c9eb975fab5e175affd6f7597748e7521ca98749dd3e37470c84573cdcc08739442567295b36c7118173370c7e10670915bc26f4ca9706f1a31866f0d2fd6
  | 7, 7 => 0xa8dd66fea88e34aea85c8d4aa7a0b0c2a78c4803a72f6eb8a652c231a62f0989a52541ada4aaf058a41368efa2a27501a2603a25a1a4261c9d9b76e59b7bace89ab0d7649a21855f9922d42798fa903c98b31592986a02779819a55f9736373896b3be4396b0aa6396623574962178ce960df38b95dec2d895670468952b79de951900a1946a426393407c8f92f99bd192d4a57092a051359175bac391493ae7908883759031277a8fce5bf58f9601818f3271f68e756fa98e6946eb8df9fe388dc2da5e8d6947e88d624c058d3082bc8c40582f8bc88e528b8c627b8b6adb628b41a1d58a2eb08889b5fb05894c25d889053ca688d7745a88cece1187fa1275
  | 7, 8 => 0xd0708f40cf23a363cef3ceeecea407adcd62a01fcd08d474cbfc0b4fcb9e1cabcb3bfedecad8cfd7ca9c7d49ca7fc270c9e8970cc9b9d25cc975c629c9330ea4c8f0a751c83ddf0bc781c6e2c76c34c6c70b5109c696104dc5f00293c55bcc56c4209fdcc2a1d1f0c1730595c0514c3bc03098c6bf7aa828beec8e33bec69cddbd890cfabd50a77dbc745684bbd1b492bbb85916bb9bbf5abb968728ba437b97b93cb98eb8599dc1b76885eeb6f50fffb6c240dcb5bed94cb59f567bb5467885b542dd97b50d3979b4888f23b487dd25b419493fb2f008ceb2ae3ab4b1ec84f8b049201aae5b2fc7ad79c6ebad6a26a2abc29a7caac75e20aa650533a99bda28
  | 7, 9 => 0xf9fb775bf9718777f6c1fa68f5304732f124d9bbef40536febddad18eb4dbe4deacd16fbe9d1cafce873320de6a12e6de58e05efe4b633f3e36adcf2e242d37de1e5382cdd3dc9a8d9fbf933d84da0cfd6da5928d61c7b14d584caa1d55d5457d5302329d3a0fd88d2160eb5d0998ab2
  | 8, 0 => 0xee9ed7b0eb4dbe4de6675ac6dbb03affcedbed26894c85118265440070706f8b5d3dfeb756dc861b4e2bbaba4d8e30d04034da113d9591df246efac41e762a730617a70d
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 4, 0 => 0x3000003000000
  | 5, 0 => 0x304020405050205000304060000020506010303010300050300030006030403000301030306020607040500050100000005020303030001030000020103050603000401010301050307020607010103000304060001030003000604000007060201030701000500060600010704060100020403070505060003050202030106
  | 5, 1 => 0x602020002010006040205060100010100010503030001030003000006020301010303050403030003040106060004040401050300020303030504050006070000060305030007000100040101070003010504000304040500060606010003040707
  | 6, 0 => 0x307010005070500070403010501040704000703050406070503000203060604010507050501000401000000010303060507070504040403060706000006040006070003010006040601070503040704050502020507060600050305030507020400060304060300040506040503060602040305050007000406050501000500
  | 6, 1 => 0x105040405040601070206040200050605010606000007050300060300030707000000060103000003050704010203040501010204070105040403060204040103070007000204010400030507040501000506050502040002040403060704050606040605040607000700050306030707050206020106040407000307040507
  | 6, 2 => 0x506040305010001020506040307040407050001020107010206040505060405060507010405020000010504050605000605000103040000070504000404040402060206020702070303000701040201070003030701060303050507000707060607060001000403050704000407060006050304040006040104050504070403
  | 6, 3 => 0x301070107070205030606050604050206000601040403040500040705050507010101030002040607040000050005050005030705060707040705040205070107030505030303010405070305040007000000030903000405030407040506060403050200000202000407070703000503020107030407050403000504050603
  | 6, 4 => 0x607060404060203000607020700030005040305060505040601010205040104030606030303050104050005040105060303040303060407050404050601030305040700050400050404030701040505020405060306050404000604000602040405050504000401040501050304050505060700050501030401050204040000
  | 6, 5 => 0x10604010100000404040501070001010504040301060100010602020a060407020407070004030400050702060504050705020707050405060301040504040005040304010004070300070604030200000606050103010204040405020406040504040106010504020107050707060405020405040202040404070002000603
  | 6, 6 => 0x407000300070704050507040500000605000503010500040206040405050504030602030207000503050502050401050401070303030406020605050006000404050005040501070105050401040104040504040406000506030604010107030001030205030300040604060400040301070600060402060404070604070304
  | 6, 7 => 0x50707050700040700000604020406050504040406010502010106000705040100000000010100030303010301000204040605010600070104070106010106040702070601030101050703000a070602050302020306060604030100050602040303030000030704000406040704000605010502020104030504070406070500
  | 6, 8 => 0x500010406020505020206020607030700070405020500000001070606010706000506050407070206040706050500030700070507060507010505050506030205020602050204050006040305070704020605050004020407020404010403050205050304040107000200040606030503000506070606000400000005050603
  | 6, 9 => 0x20101050306050104000003000202000402010203040606000606000205040505040302020506040009060506030406020705000105020202010403040004020105070501000604060704
  | 7, 0 => 0x604050500050001060100010700030604020200010702050101070505000502030600010706060107010505010407070605010507040405040604060406020400040505040407050100070003040505010304060601020503070001050402070503010605000004040704040404010603050005010301030407000101050607
  | 7, 1 => 0x2030305020404060104030006040304050707010701050406060706010606060402010602050105060603010606020201020406040600060706010404020707060104020300010506060104040005010401010706050704070207070404040507070201050601010503050004030101050601030600070007060305050106
  | 7, 2 => 0x5030106030706060400000700020506010403050101000001040304030105070305040004050100000301030205070704030104060606040103060402060004050301070100060400010703040504070604010307070301060404010105060605010607050104070400000704070405050402050500070405020505050703
  | 7, 3 => 0x501000404050704000104030006040703060201060303000101050103010401070504000606050103050707010105060002020003010501010404050205000603060306000105050403040406040707030402060406050501050406010505040201050401070606050500050101030004000404010505060104010700050104
  | 7, 4 => 0x101060201060402040404010606020106020006060307050006040602010107040402040707040505040000050401010101000502060100050505040406070404020207010607070201060200050407060307040501050204000605
  | 8, 0 => 0x202020202020202020202010101010202
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 12 0 (CN0 s)
def CN : Nat → Nat
  | 4 => 40
  | 5 => 280
  | 6 => 903
  | 7 => 580
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0xe5dad5dcde6def4ed9c75295d9c1dbabbcd06cb9bc969ea7af606120af2efd07ade44a4aa194c2a3a15349019fac3ee39dbff5769036c0308c9c5b92886874877eccc7b374e85753732bfa07718f8e7d6da034475bb9e97855f6f63c5335e5315289d1de515fccdd47648b4641efa3a63c8c12e03b9a48c53b1dd4e539c15a67398bb37b35e3e5852542c8041d38b86c165a3df815d003e40f1af8470bf4db48
  | 5, 0 => 0x1f10df3c1f03e1bf1ee5878b1e64a1841de36ab71d9ea5631d5125481d096e2d1d0163831cf58e731cd3b9751cd3425a1cc9437e1ca3d43f1c4bb16e1c3a67ff1bccfa511b2a247b1b1531291ae2dd881a9318241a8911681a40966f18374fa417f2b24c16c84d2d163cc968157b87c9156c2153146130a911c26f5f11b7887d1172cc63102327480fb337220f8e55410f2d97bf0f231dd90f1ce75c0f1b49cf0f1812f30db2913d0dad1f780d57c9d50c3ecf310bd39bfe0ad5e72b0a5f91d90917d42308e1523508974d2907e5ef5106a16b1b069e13e9067ae54b05ac753e054dbee8051cf99204832fa20315f36102b3104101d0780700f21ab700bbc2cc
  | 5, 1 => 0x4a931a044a27985549adc10f4976eaa247a25af0473e3876462c8cef45f278664580d0ea4556e3b5439d8898421360d341e590334099a0723fea4ecf3fa847133e20358c3d6c27f73d5291343c5189c33ac3725a3a6a89c239c2f6e739aa8be83916868b376f0946376749f737384ddd3669cb86364c74293643fd2535f9d97535b0b81b356f74b935634fc5355e3fac32be37f63252cb4a30edd8fc30e8ca202e5f3f8b2d400c042d3e656a2d34ee762d2fedc22ca340762bd35d9a2aeb17a02a94d1382a6596ac29c94834294a86b9285f348727e781d22788211526781b14261ed9f4260f4ba325d09f55254ed986245665f2231c2216223c45dd1fae6926
  | 5, 2 => 0x7717c274768705607683d23874e0a7e0740614d073ba58b1733fa007730fb468711a5ab271148d206fe1bbe16e9cbcad6e55bed56e3ae7286e17b6e76d962b0d6ce7fb306ce520866ca92af66c6941c16c26c5716a67a28668aef36a673fcfd46735c353666228c5658a714c6559da8a6551ea4664e5eca064b0d97a63dc40a46307c33761f20b2f61ccb374603ce9d65fa2467f5f0b02db5e4375595dcfc3f15d72a9d45d6025375b8699d25b76cbfa5b30d48259df7ed6593c8cb258ff199c57e640e156d385f156b25f70545fdfb953e7f26c535c7b58525163574fed4d954eab45e94e1745a84d6336df4c1c662a4c018e7d4b8fae894b6d7ea64b038998
  | 5, 3 => 0xbb9ba0fcb9f4b7c9b90ebca6b7ea0932b45c62e0b20cd2b4ae31cf1aae01bd0aad32e96babcd4801ab993214aa2524c2aa08e787a9eb56b0a8c0ea9ba39ddf4ca32240e6a11ea9cca05e9b929eb4815e9d7eb9bb9d0d26ad9c17d7ff9ba6b2f49b3c80c89b2b96c19b1d499b998de8b298bd2ae395a34e4894db25ef93acfc279304a24b92d30a1890d50dab8f786f698f3ea1578ee2559e8e0462e98dd5ab0b8cbc41358c7041758c59773d896713cb88dd4a5088ad0f2e8804f411878c353b85f9ef6d8566f99f824f2cee81445b867fe6036e7f9856a37f1663b07d1c8b567c0276c37b00fbe57a10e31a7959fee2791c3fde790cde9c79078f5077ab2205
  | 5, 4 => 0xf7a54eebed1e95c1ec08be9eeb854514e643556ee3e40b48d79a5579d64bbaf7d3683674d1c9ff46d12602d4d03c20c6cc3751e6c9264702c8a4b4adc8a0faf4c87effe1c4a902acc3c57963c05e0b0fc021861cc0049944be5623eebccf089b
  | 6, 0 => 0x9bb84440995fed50983e259097050d80913cd64090eeb7c090ac3af08c8f08908644f9a081914a907d2c86a07aaf9e307a2242907592b10071c3c1206e05e0f06d7978a06ce6a9b06c111bf06b6d34306af56fb06999661069654640693b434067a7105063894fa062924fa06032c7a05cc6b1805cc009705c9753905576c42053b580f052beb4f0523c06a0506a84a04e65c4e04c71e710461259f04507cff042bcd3103da8c8903d5bc7303b5957703879cc80370c89703371e3a02d408f002a541bc0260c296022ae0100220cd9601bcf0b801bc646001b0ba7301a0f02c0139080801072c010105094800f5354100c8593900a9b83d003f4cb9002a8089
  | 6, 1 => 0x12ec409912ccb65b12b56ab21289e4e0123bd3a31211a3e711b711471195d432117858f010f6720d10ce3add106494591049fae2101e984e0fb7f1390f8dc3ef0f629f130f4c07990f0f14740f0d8b4e0ee7212c0ea098e60e9611ad0e7a409a0e66d49b0e4a42ea0e470fc20e0ad22e0e030efc0db463210da3ca340d85b6900d69fe600d5746d30d2e4c950d087da40d03212f0cf3c6be0cf09d200cd19d840ccb1d8e0cc83fa60ca1ad600c6597450c562af50c5470010c528d270c1881fb0c0f61660bcb057c0bac20130b850e3b0b66eb3f0b25a32f0af9d6710af594d60ab60a4b0aa5dd510a9f7f4c0a948e340a699e710a436e6f09f46da209f1b78f
  | 6, 2 => 0x1db2dce31da288b61d87b1091d6de6501d0d05fb1ce6cdbd1cd2b56b1c5c71791c1c3d8e1bf3df8b1bc0baab1bab1ac71acc5c881ab7dffb1a8610321a48355a19d7729419bc3dd31966b2a119461886190add4a18fc2dca18fa334918df30a318cca6df18a41b9a189ce85518771ba818516316183667441774c06b175164471745df7a17324ed8167ac0cd163ec2321635c0cd162c8d3216234f5815ebbf3715e7c38b15d2a37d15c5580715b6ef2215b3ec9015acb49d159f635315671bd3152a8e2c14e8addd14dbb93614976759148ee1fe148d3927147d397913f7318b13e6f09113df9a8b13dec97813ad2b6013a1a95f1380cc31137212a71300aeac
  | 6, 3 => 0x277a8489273c4a81270452cb26c4a8ea26c3359226ac2ee726a59328269d8def2687e3d126679e162664e0802662ebd12640f1a426393cdc25fc3bca25f77f0725c8447b25b8fc052574640b253d2c412517ff2824fdb37624c16bb224881fcd2447887624185b6e23d785e323cba97d239026242387d6b6237e52bb22ed2f2b22c106b02225830b221cec92220c7dc121d006f721c499e3216d3cff2158c68b2152c66321334d242116bfc72110d589209ef81f2097ffcb20786bb62068fadc20615701205d3b1d2038dafe202773981fffe1001f8a13b21f4daf761f32d7c91ed0fde71ec2e2e41eb388481eb12f5a1e65cf2e1e5f9f1a1de431871de1d43e
  | 6, 4 => 0x32fb10f232e5c5f832cd9bd4328d2e21327f11fe323c4c2731ef9fc531e7618b31ce21a631ca1607319fc33b315164e7311365ea310edf1330e54db730ae44dc309d10543091256730047a722ff999e32feb7ca82fbb34322ef40b3a2eeb28302e25b1202dd54ba82db579192da5c2a62d7b25702d71945a2d1dc8a62cfad4652c9e63792c76e0f92c6e773b2c6861102c2587382bc165582bba52bc2b93fa342b93b1612a6e2a6d2a4e004a2a34c59e2a1a794b2a04cf3d29f7dc1729e46e3729dd6a3929610c10295c6a5c290e1de928b250bd289b83fc2887037b287c302328678cad285a58cd2859a87d28119de9280e2a0a27fde41827e322cd278807df
  | 6, 5 => 0x3f31499a3e4ea3323e4ba1f43e305e033db3f1813d6e0af03d5f79f33d3d40343d2f864d3d1667973cacc1723c1bf11f3bc8ab733b81da083b2f89ca3ac908b93a8d33303a73be723a7269563a6e3f9a3a69f02b3a56a0a93a4d980e3a04752d3a02fe7f39f719be39bdf0ed39152c1e38fe1df7386b0dc3384613b0380f45b937b615543799c9ca3786d11d3771e68537608a2a36fade9836eebd8f36e708b236dbc8dd36c397b036c3004036a4ca4b36a2eaf8369604ed365a56dc3643c9d335c0e36c3590f999355d00e43525121434ef842734db66cc3486951d3466e97f3453d256345033ed33fc2a683397836b3370000c336b25be3332c8ac33159322
  | 6, 6 => 0x4b2ea4e34af0ad224a4a8f984a3ef34449f4ef9b49c1633d49b51b84494e9c9b493a3d1d49091ad14904543048b62dcc48472bd04809f4c447dca31b47ce41d14782d42847302090472da5c647256a2347028dba46fc6d5546f22ad446c36e2646b4aea346a505714686201c468336944672ce274664bce2465e481c46572b3e46068db145dbb1d345c4fa94459662cc4570b153454a6c6144c96a0844611d7343c3c2f543bef80a43b6ef0543a4205d431dabbb4315c96342da222c42a5a65e429e351d427d69bb426b0610423a190f41baac4b41b34aa4413caa75411abd6e40ca914f4051b2984043c3d34011558b3fc490b63faf3e353f6556e03f59d6ea
  | 6, 7 => 0x5a7adb3b5a7682005a19729259fc951959f886e059e8b44859d0df6659a53efb5993821759563925591687ee5855c8b758066d6b57f792f3576cb25c56e0857456ad94bb56acd9c0569e5bd4565daaef563dd23b55fc444055afda8f555c87b3553bcb1855001aaf54d976c753eb54aa53d7983453b4549b53a1808852d6088952d32f4452b68ab2521ddb6451fe7b7851cd900851bfc8d951b3e3cb51933dd5517dc9a5516c38285132e4a25132503550e71458507ea8ba50435fe94ffa5e724fe2c9074f1b06b34f1876014f0a97234ee83b954e7617d14e6debf24e6207364e5178c24ddda91d4d8ff5544d7931334d5de5f14c76823a4bb5ac764ba3a3cf
  | 6, 8 => 0x6be1f86c6baf43206b7e323b6b76829b6b3b1fee6ade53916ad478f16ab0ec706a535d496a0e967a6969f704688fd8f667fb618367d3feb067cbef9067b6850d67a7d66467a4af0467659b236753bc256744a991669424ac6661487b65dd5bc765c0ec06659df3ce656d676c65252ee664b5c4ae64b13dd7648fb20a6370cbea630f7037628c14f7623a864362222bde60e8e7b060a6750860a516d5609056c5608a684b6068782a6062228160560de760423d6b5fab05f25f8a71ae5f84f7045ebaefd75e2489925dfeef795dce580b5d3d0c995cc0be6b5c99ebe85c8bca485c1cac135be85f655ba1e5b75b8a70035afc029a5ae94c135ae5b82d5a948b2f
  | 6, 9 => 0x801a56037fb464237f87df967f8548107e68e5d07e6278e57dae3b7b7d68c9677c7eab267c5643307c44dd147a795aad79f5391878f5ce2f78d4bbd878b25da7789fd840784eb4937819e6bd77cb93127751a948771b74ae76a40a2e768f974f766f01be76679ec0761cb6c17609777575d4150875bbcbd2756268a0755599fd74b0da6174808a5c73b339e373a283e072b1a9a072a1824a72852b3a72815481724e47c1723bd83671ed7ac7717f37ad7164bc847147f9b06f5a17146ebd348f6ebcd5ee6ebb0fda6ea337256e8b38706e8721546e6879856e4bbb536e2664186e20812d6d830afe6cdaebb66cc5dcb56c9e558a6c418d176c093f366bfa6a70
  | 6, 10 => 0x917695df91281eec911ed7d290e0ac4f904b7274901e08718fc05f438f9eba098f7149928f50cb528f50698d8f4158c58f0d490d8ef8a3e48ee1a14f8e244ec88db3539b8d671f5a8d65b9ac8c7db7cf8c533f428c187e2d8c17a45f8b198ac98af6a38f8ad371c48a47caad8a45a3568a2eb0888a2269dd89fd08f289ea9b3689e65d9a89a09f6588a6d40a8826485c880e49bf87fa127587a9f9f987961d8086c661d486b9b96e8684e77e8679a7a586760afb85a04651851a5edd84b442118417692c83d24e888348829e82f8065182b7ad0a82afdd8f81ff9dbe8189a74681578cdb811017e280feea4c80c5613780b82731804a6c0a803d485c8027c221
  | 6, 11 => 0xa6f71cfca6dc38f2a652c231a650920ea64a9d79a63c922fa5a44eeaa53ec13ba536e532a4a21b03a4361aa3a3a17b96a394ca33a34fb783a33ade49a2e129bda1dcc854a0ff53aaa0f5bb35a048909ba041200f9efbddee9edd29649e0515459db1a6f09d96a3819d1915ae9c8960299c25192b9c0d87f69bc9c8fc9bac2de99b7bace89af0b0359adde08a9abd8c139a9f56369a87a1749a46733099b8c7b699aeda6d9982f2ab98ced3d298c9fff397d23ba4972b607f972630bc96f1926d96562b30960cc3c995a42c76957cda4b957152b49535bc93942dd7509400accf939ff1c893839723935fd904934df57e93407c8f92aa70c5921bff30917bedc6
  | 6, 12 => 0xc26ac619c24a4a57c1505bacc0efa603c061d444c0233046bed03b03bec69cddbe6423edbe182b84bddd0caebdd2892dbdaddc39bd5544debd356506bbccb71fbab09efeb9f9bd52b9eef3acb9e1301cb98466e7b9380b86b831b66ab82581e3b7be4254b791b8b7b775965eb6cde97eb6bcc15ab62d38ecb5a32078b53b9ccbb4d725a5b4561ff6b41b582ab34eba8db34ae318b3485ea0b272e1fcb237955eb1ec84f8b18f5548b0a596caafee04f9afc09e0baf99ca8eaf16fbf7af13b5dcad763e25ad113fd0ace6e604ab5c5fabab3e42eeab38676caa0d9e4eaa0489aeaa02f432a9765ab2a95f46e3a8e4e9b7a7f5b37da7d3d5daa79b3de1a731bb98
  | 6, 13 => 0xf399ebbdf26107e7f20b3268ef40536fee96c37bedbe76d0ecbe1e2cec755780eb567721eac91c51eab0a903e9d1cafce801ecbfe7452a5ee480c032e4489c2ae3dfa3b4e1f11342e01be640dca2846fdc7104d1dc370869dc30f4b4dbd0450fd9ebd39fd9c69cafd9a086c7d9958c62d972a995d95d76a7d8ba3d78d7d6624fd6ba4005d6b2b91ad69b9ac7d55d5457d4cebad4d2ec8dced2427c36d1f3036fd1a4b738cf9e5140ce9ff63cce4fe1a2cde358a0cdaf4881cd217d36ccd17ba1cbb54a8ccb3871c6cae15587ca9c7d49c7841985c68c8539c67acf74c656888ac5893942c4f21481c4ef0d82c4ad970ec45791b7c3aad2d8c32e8d08c27d0b6f
  | 6, 14 => 0xff5a7956fd5fafe7fb21b774fa81887df960541ef8391d43f6ce4065
  | 7, 0 => 0x1274dc261209e76e11d5b98d11b8accd1147ecda10befdc710b96ef4102cab0d0fab0c6f0f784e4d0eaa8def0e6087c40e149b3f0dfaa0a90ddfc8fc0daa87070d53246a0d4dfd9a0d2b6d5f0cef44940c144c070b62a6670ab8c1990aaeb5680a8e3ecb0a675eb30a59e1fc0a2ba6ea0a233ec809d5290009d26a8409c074d0091ba0e908e90c2b08d67fe208b1bd9e08a3d81c0889006f079e1a210786b0b0076984ea072d5a2e067a7105061d6ffa05dc980d05cb0a6f054e7c020527e7450404720a03ead5be03e5154e03c6fd690344588c033e502602db0ed302ba284d0254648e01da190801746e23012f0de3012652d00122b26001082759008007b1
  | 7, 1 => 0x221ef8362203f36021eed54a21c07a4221617b5f212e802620e93d5a20cb3ed320cb153b20938af620769c1e2013f7481f042f731ebeac0d1eb18d201ea71ff51ea0ee201dca9a151dacff681d53db391d0dc38c1c8b8dbd1c64e7411c4e11bd1c040c071c01a5ee1ba049621b9274cd1b5de4ab1b0674a31aec66b21aa754591a8610321a5ef2c31a16361719e63d3119c59f1b195c1d371901013018b1c0701836c68c18309ed7182f2deb17bfdee417bbec7e1738daf81709d74016e3d3db16aa8f59168aa1d41678f84a15a163f4151ca44c150da45214bcdab314a41e0814a30fd8147474a81455233413a53d6b135af7e3135340a61338ba1412e59c19
  | 7, 2 => 0x337e4407330b442a3307feaa3247f56c3181f16e30e0241630833624307898bc3049305f302e58b22f860f7e2f4257412f34ef302f16662e2ef63c972ec323232ec1ed122eb3a6252ea84b762e42e6322e3cf8452db12ae12d61e45b2d33f9752d3138ba2d0318d62cfb101c2cb197942c9abdef2c97cec92c0645762bfa44df2b9dd1ba2b82c1162b777c1a2b6728412b63e0d72a8e0ef62a57224029972a0b29767f772945db1b28f9a02128a791d0286bffb02817c88727d1250a2782c2362649f7a92592e8422589f0c52540bfd4253c591e2515433d240cdb0623f5a9a423c5d8cd23b553d523a5cfb92374e28622a0b4b92267a866226584a32243a8b0
  | 7, 3 => 0x478aeecd477991e24748a06346b295b0465dff8145bed65a45965fb7457aad1944c3349944a9583144948ff44425aaaf43dda7d44337cd1042b5256a41b1bfd441a78c1d4195ffb9413e5fa241373a674118194640d148bb3fc48b4b3f6baf063f6618523ed0428e3e92570d3e2867a93db92f083d8b6a433d8993143d1d5a1a3ccc66d43c7063413c436cd53c0d54193baa12c63b870d6e3b0050263ae0179a3ad089183acd917639d4951e39b97409397a42ea38d8f73f38c211de38a96e0838674de538620cb736e7c4a936cc53f0362623ca361a28f435d5172535abdb7d3597f57735489a2a352a274334ebad5934c51124342d0bbe33f9da8933dbc4cd
  | 7, 4 => 0x5a8553de5a5d16605942c944592a8f3159101352589b207e5884fc685828373a57a568625776e8c75735261e57242e8d56d8680856b9606e568b0fd6568701695684893a5665a89a56135b1055cd868b55c20910559a746b553f810c54b81a7c54b680ae549d42cf546bd6e054615a1c5427ac1853f19ed153d57896532b579252fb2c3952e83b0e525a5ec651d4887d5168ddcd51641962514e06205136fe935135d6f650c5170350c0901d504d7f7e4fef277c4fc3da2f4edc839a4e740afd4ded082e4d73fffa4d628faf4cc505c54c0920ec4bdbdedc4972f116494d59114908c5a548dc991e488997e348552e0247fd89df47fb934147e3cca347da0a82
  | 7, 5 => 0x7196ca7871354e6e710ad5e370f9408e7080377e6ffe420e6ffdcbc56fe3dff76fdff7896fcd5ef96fa744806f52c7e16ed386016ea337256d51b2246d2dfdde6d11971e6ca0d72b6c4220756ba4fb786b2308676ac7a1356abefd6f6a92e3d96937f48967b8992067a6b72d677150b56707e96a6689c51265c09a076561cb0a64b7f4626461213064577a7e6436880a63e2a276639fe9cf6391551462f3cb2a61a559556152786b6134996261098b0860e6cc7a60dd09a260d3977e60d1580f60819502605d79806010b51f5f8e45915f6f3a435ef7e7885eca05a55dd0b3515dbe96005cb9d0dc5cb83a9f5c74d3ac5c53e0a15c3e4b795c1ffd945ab09c6d
  | 7, 6 => 0x8cf552d48cf4c2f28ca592208bd63ab18b6ee02c8a4c0e6f89fb925d89e9ca45898d4eb289790a5289477dbe893a99918926ebc588835a06885c4f2b879bccd5878ddd318774ead1860e11c385db29aa85d609e584c8a0c3847d86278417fd9a83f9729482afdd8f828abfd28253bcf382450bbd819c18f58145d05280a90e75807620647fe3fef07fb0ac827f94eea87ed8e8b97df2abc57d81808a7cd795147bec75477bc1f5aa7ab98f587a4795d979606c7379210ec2791dcc5378fcbddf78e0186877d9ad8177d71cd975dcb048758066d9754a03a0746247c674193d4e73c9a42e73c36e49738270077347b91a72c0a0cf72a39911724c04e87238cabf
  | 7, 7 => 0xaf94731caf038765aeabb43bad480135ad19978eacdeafe4accedc4dacb794cfab5a1cbdaa475c77a9fc5ab6a9f53655a9dc7847a93710f2a881054fa84a3b9fa77bb697a4e65e68a4d53860a379a34ea33e40a1a27d0eeaa227901da2272630a1b6e9d2a16f5cfba0ec2dd9a0a631f0a0a118f4a05d83d2a048909b9fdf19a49fd89d1c9f99703e9eb21f6b9e92c2af9e13166b9cc918b99b7241f19a7c79e29a5c8c0699e550d5999ba1b398c4a86e97ff7fd4965df89c964aac09959ccd7b957212e89553424494fa4fe794f98c7b94ec45ab94cdcf7193db7f4993a230c19347c235933170ce92838b599244fcf8910e8fc98f8864618f0269148e551f7c
  | 7, 8 => 0xf0ab44d9f0090156ed30ad92ebc7c111ea102889e6ec1e41e68a9263e536518fe483bb1ce39db05fe2a929a4e217d70de1864986e183165edf5908c2dda5de3fdd3ff1e8dcfed4a5dba49c49dae70ff4d94cad4ed7b9c5a8d7a8c8e5d6516ef4d5de6693d566e6acd4195d03d2f3d0e8d284bae9d247b4ded17e818ad141d39ecdaf06c6cd0aebbfcb706438ca53cca5ca0a4701c8478375c663b264c5d0f67dc5736705c4f21481c4d36ed5c346d39ec1de250fc1d2ca17c1505bacbf10a9dfbe8f1cf9bb8a261eba64b8b4ba1c4f0eba137eebb8da63a0b7dc3178b71baa50b691358ab5ed7cdfb5a32078b538d07eb4afa9aab47e92eab1f5493fb1d1bfa2
  | 7, 9 => 0xfcaf20ecf7e55ae5f7ac190ef1881e4d
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x15b100413010015b1004130157d0c5050d4020019531cc630100195018073010759531cc64020000000041103001593288e30167c84504854020019521c8630100197324c83010015b200813010759521c864020015b320c93010019530cc2301001592088330100197304c03017644a52c4140200000000411030019520c823010019521c863016750641ccb402000000004110300197324c83010015b2008130157cc4504c540200000434c52040015b2308d3010019510c4230100000000411030015b320c93010015920883301
  | 4, 1 => 0x1593288e301000002404120007559438d24020019510c423010015b1004130157c845048540200000000411030000000043103
  | 5, 0 => 0x20081201000003150d20400000000431040019531cc630200000454c4201000d85048530200000200812010000000086106001435050d3020019521c86301000000008710000000458c9201000002348c2010019531cc63020000051c812010015b421093020019531cc630200000458c520100000000431040019521c8630200000000431040000052cc520100153544c13020014b504c530200000000411030019541d0630200159438d23020019532cca3020000021085201000000008710400184505093020000000041104
  | 5, 1 => 0x19510c4230100150544c130200000000411040019531cc630100000000411040014420d093020015b1004130100000324c82010000010c072010015b2008130100000000411040019530cc230100000000411050000025440201000000008710400187505093020000000041103001593490e3020019532cca3020014420d09302000002088320100000510812010019530cc23010019532cca3020019531cc63020019531cc630100000350412010019532cca3020000000084100000000004110400000320c92010019501c06301
  | 5, 2 => 0x4110400000000871070000000087103001974350c30200104414cb30200000354042010000050cc5201000004548720100000000431040000050cc520100000454c82010015b310c53010008450485302000003588120100000454c3201000002188720100000000411040000045440201000000004110400000000431000019521c86302001593490e3020019531cc63010019542d0a3020000000041100001974350c302000000004110400000000411050019532cca30200159438d230200000100412010019521c86302
  | 5, 3 => 0x50cc5201000000008710300000304c020100000454c320100000000051040000051c8120100000100412010019530cc230100000000c810800000458c5201000004548720100000000411030000051c8120100119129073020000052cc520100000500c52010000021484201000002308d201000000008710400000000411000019541d06302000d8505093020019510c423010019542d0a3020010c5050d302000000008710400084104813020019532cca30200159438d230200000000431040019532cca3020019530cc2301
  | 5, 4 => 0x320c92010019531cc630200000354042010019521c863020000050cc520100159438d2302000000004110300000000871000000000041104000003288e201000004548c20100000500c52010019521c86302000004544020100000310c520100000000411040000030cc220100159438d23020015b310c530200159438d23020019521c863020000023c8e201001974350c30200000000411040019521c863020000000043105000000008710300159438d230200159438d2302000000004110300000000411000000000041103
  | 5, 5 => 0x87103001974350c30200159438d23020019531cc63020019520c823010000051c812010000020883201000005108120100000454402010019532cca302000000008410400000258412010019532cca3020019532cca30200000258052010000000043103000000008410400148104c53020019531cc63020000051081201000005210720200197324c83010015b4210930200148504c53020011a5044930200000500c520100000200812010000035404201000002584120100000100412010019531cc63020008410481302
  | 5, 6 => 0x411030015b210853020019542d0a3020000001005201000845048530200159438d230200000530812010019531cc63020015b310c530200000000431000019531cc630200000454c320100000000871000000050cc520100000000c710500000454c820100000454c320100000300c12010000010c422010019532cca3020000051c81201000000004110400000000411030019531cc6302000000004110500000354042010015b100413010011a504c530200000100412010019532cca30200000354042010000000041104
  | 5, 7 => 0x15b421093020000000041105001593288e3010019521c86302000003548620100000308c3201000001004120100159238ca3010019521c86302000000008710000000000411040015b21085302000002150920500084504853020014b310c530200000000871000019541d0630200148104c53020019521c8630200000218872010015b210853020019531cc63010000050cc520100000318c72010015b2108530200108505093020010641ccb30200000458412010019532cca3020015b2108530200159238ca3010000045440201
  | 5, 8 => 0x320c9201001593288e3010015b21085302001974350c3020019510c4230100143210853020019521c86302000000004110400084104813020000010041201000000008610600000000871000019530cc2301000003540420100000324c82010019531cc630200197324c830100000510812010019520c8230100000000431040019521c863020019531cc630200000100412010000000084104
  | 6, 0 => 0x4550a20200000510812010000031cc620200000000c7105000002050920200000000c710500000000c5101000000008610100000504842020000032cca20200000154c320200000421092020000031cc620200000454802010000031cc620200000504482020000041d0620200000000c410200000324c820100000054c720200000310c520200000000c2101000001048420200000324c82010000020507202000003550b2020000050d0d20200000218812020000052cc520200000000041010000020c8220100000000c8101
  | 6, 1 => 0x25c402010000050cc52010000051d0920200000000411010000053c812010000010cc520200000000c7105000002050a2020000000006101000005110920200000000411050000045c48202000002050920200000000c01010000025c40201000000550720200000324c82020000020509202000004150420200000000871070000025506202000003050d2020000032cca202000000008610600000354c62020000051c8120100000000c4102000000000510100000000c410500000000c610100000520c520200000000c2101
  | 6, 2 => 0x53d0920200000354842020000000087107000000004110100000210852020000052cc52020000000043103000000004810600000000871070000051081201000004540420100000100412010000030cc22010000000081101000005050d20200000504842020000000087100000000008710000000000c710500000000431050000050cc520200000154c82020000051d092020000031cc620200000000c7101000001004120100000000c8101000000004210100000324c8202000000010710200000310c520200000500c5201
  | 6, 3 => 0x50cc5201000003490e2020000032cca20200000504c820200000000c810100000000cb1010000051d092020000032d0320200000154c320200000000801010000051d0920200000310c520200000001091050000000086106000000008710300000000821010000041d06202000000000610100000324c82020000053d0120200000511092020000050484202000004544820200000520c52020000032cca202000004350c202000004350c20200000000c410500000000401010000031cc62020000035c042010000052cc5202
  | 6, 4 => 0x32cca2020000020c8620200000454c4201000004544a202000001550e20200000000c710500000000c3101000005108120100000000c410500000254402010000050cc5201000000004110000000210852020000031cc620200000000401010000054cc520200000000c41010000051d0920200000520c52020000025440201000003540420100000000871010000052cc520200000304c0201000000008e1010000005507202000002550420200000304c020100000454c42010000051d0920200000434c32020000000043105
  | 6, 5 => 0x504842020000051d092020000051d09202000004544a202000003288e20100000000c610100000000411030000035c8420200000000cb102000000008410000000358812020000050484202000005110920200000154ca202000002548620200000000411040000012c4a202000000010c1020000021c86202000000004110400000504c520200000310c52010000000043101000000004b106000000008710000000000841040000000041103000000544a2020000021c86202000000004110400000000c51010000050484202
  | 6, 6 => 0x434c320200000504c5202000000008d101000003548420200000310c5202000004350c20200000310c52020000000081101000000010910500000000411040000000108102000000008410000000000401010000031cc6201000000000610100000354432020000051d09202000005050820200000000c9101000000004b106000000004b106000003490e20200000354842020000035484202000003490e202000000004010100000000401010000025c40201000000008d10100000000411040000031cc620200000000c2101
  | 6, 7 => 0x2550620200000000c71050000051c812010000035c842020000041d0620200000054ca202000004350c202000005050820200000324c8202000000008410000000421092020000021c8620100000520c52020000020c8220100000000c2101000000004110400000454042010000051c812020000000087104000004350c20200000000c1101000003548620100000000c010100000000c91010000021c86202000003550320200000000871070000020d0720200000000861060000020c86202000002550720200000000c7105
  | 6, 8 => 0x2348c20100000000c710500000000c1101000000010d10400000504c520200000000841010000030cc22010000045c4820200000000871030000032cca20200000054c62020000020d0920200000310c5202000003548420200000154cb20200000355042020000051c812010000020d09202000000008210100000255042020000012c4a20200000000c210100000504c5202000005310120200000454042010000042d0a2020000051d0920200000000c010100000520c5202000003550620200000154c820200000000c4102
  | 6, 9 => 0x84104000000004310400000310c52010000050c8520200000454482020000035484202000004150920200000415042020000000084104000004548c2010000052cc52020000050cc520200000000411040000000041104000005048420200000454492020000021c862020000051d092020000000006101000000000510100000000071010000025841201000005250120200000205092020000010484202000000008f1010000035404201000005050920200000254c220100000414cb20200000304c02010000035507202
  | 6, 10 => 0x871040000042109202000000004110400000454832020000045c4820200000324c820200000000c41010000035484202000000008510100000000411040000035c0420100000520c52020000000087104000005050420200000054c720200000000c9101000004544020100000000c91010000031cc62020000041d0620200000454c32020000041cc820200000511092020000042d0a20200000000c7105000000004110000000404d12020000041d06202000005050d2020000042109202000000004110100000000c5101
  | 6, 11 => 0x35c842020000041d06202000004544820200000254432020000041504202000000550a2020000000081101000002044120200000520c520200000304c02010000000086101000004210920200000000831010000041d0920200000000431030000000043104000000010d10400000520c52020000000084101000004544920200000310c52010000051d0920200000520c5202000003550b20200000520c52020000035c842020000015483202000000004110000000000c910100000154c8202000000008410400000154c3202
  | 6, 12 => 0x841030000000081101000002348c20100000001081020000000084102000003540420100000000c710100000000c110100000000c510100000438d2202000005048420200000438d2202000004584120200000204ca20200000504842020000051d092020000021484201000004210920200000454c82020000000007101000000008f10100000544c12020000021085202000000008310100000204ca202000000008310100000000c41020000045c48202000002008120100000454c820200000000431030000052cc5202
  | 6, 13 => 0x51109202000004548c201000000010710200000000c510100000511092020000050448202000003548420200000520c520200000310c520100000054c720200000500c5201000000008410000000504c82020000051d09202000002108520200000000c11010000035c04201000000008410700000000c7105000000000410100000000421010000045448202000003540420100000504c820200000000c21010000031cc62020000041d0620200000458492020000045c482020000041504202000000008c1010000000041104
  | 6, 14 => 0x35c8420200000310c520200000001091050000021c8620100000000c91010000000084107000000000610100000000871010000020d09202000003490e202000001050620200000000cb102000004584120200000504c820200000454c32010000000087101000000008310100000504852020000035c8420200000000c710500000454c320100000438d2202000003540420100000324c820200000510812010000000081101000004548c2010000041441202000004544820200000324c8202000000008d1010000050484202
  | 6, 15 => 0x3550620200000238ca201000000004310400000454c82010000000087104000000004110400000454812020000045c48202000004350c2020000000043104000001550e202000003548420200000454402010000021d0420200000000c2101000000550b20200000438d220200000000c7101000000008710400000500c52010000041d09202000003504120200000421092020000021c862010000021d0420200000054d22020000045480201000000008210100000000051010000020c8220100000000431040000025503202
  | 6, 16 => 0x31cc620200000438d2202000000008e10100000000c6101000000004110500000000871010000021484201000004544820200000324c52020000051d0920200000000c410500000000c710100000324c820100000000421010000000087100000004350c202000000004110100000000cb1020000041d0620200000000811010000051cc12020000032cca2020000032cca202000000010910500000154c820200000000c1101000000010710200000200812010000020c8220100000454c820100000054ca20200000000c5101
  | 6, 17 => 0xc410100000000c110100000000c71050000042d0a2020000042d0a20200000520c52020000010c42201000004548720100000000c110100000000c310100000454c320100000001071020000001c062010000050cc520200000510812010000043d0120200000324c82020000042109202000001004120100000000041010000054cc120200000000811010000050cc52010000021c8620200000055062020000000082101000004350c2020000052cc12020000000084104000000008410400000000051050000000109105
  | 6, 18 => 0x411040000052cc52020000045849202000000004b1060000021c8620200000504c820200000454482020000045c48202000000008510100000000411050000041504202000000004810200000000431050000035c84202000001550e202000001550a2020000035c0420100000000c410100000354c620200000500c520100000520c52020000000087101000000004b10600000438d2202000003050720200000000c51010000020c8220100000000871000000045448202000002108520200000454c32010000000082101
  | 6, 19 => 0xc110100000000871040000050cc520100000358852020000041d0620200000454cb20200000324c82020000021c8620200000000411010000030cc220100000504852020000051c8120100000000c2101000004548020100000415042020000041d06202000004350c2020000053c8120100000000861010000052cc120200000000c710100000310c52020000053d0120200000458812020000045849202000000004b10600000454802010000051cc12020000053d0920200000544c520200000304c02010000000081101
  | 6, 20 => 0x4010100000000c610100000000801010000001c0620100000520c520200000000c810100000000c71050000000083101000000008410400000000c910100000438d220200000520c520200000000ca1010000021c8620200000324c8201000004210920200000104812020000025440201000004350c2020000021085202000000004310500000354c6202000000008710000000000841040000000084104000002148420100000454c3201000004544120200000000c4102000001004120100000454c42010000021085202
  | 6, 21 => 0x51cc120200000254d220200000000c610100000324c820200000000871000000051d09202000000010c1020000032d07202000003544320200000504842020000012841202000000008f1010000000087101000005148120200000000c010100000544c520200000210852020000000109105000000004810600000238ca20100000454c72020000000109105000000544a2020000031cc62010000005506202000002108520200000210852020000000041101000005048420200000454c3201000000550e2020000052c41202
  | 6, 22 => 0xc01010000042d0a202000004544820200000000c01010000052cc520200000210852020000041d0620200000454c72020000035c8420200000000481060000051d09202000004584120200000454c4201000000004110100000000871000000050485202000000004110500000520c520200000000c71050000030cc220100000254c620200000000871010000053d0120200000454802010000051c8120100000000c9101000003248120200000520c52020000035c842020000010041201000005110920200000344d0202
  | 6, 23 => 0xc7105000005048420200000000c4101000004544a202000000004310400000520c520200000238ca20100000210852020000035c8420200000310c52020000052cc52020000042d0a202000004544a20200000000481020000051cc1202000000008d1010000041504202000001050620200000454c4201000004550a2020000051d0d2020000012c4a202000005048420200000520c5202000001048420200000000c01010000021c8620200000310c520100000504842020000050cc5202000005048520200000000c7105
  | 6, 24 => 0x31cc6202000002550620200000421092020000042d0a20200000504c52020000052cc5202000000008e101000000004110500000000841020000021c86201000000008e1010000035c8420200000454c3201000000008e10100000000c51010000050484202000002108520200000000861010000052cc52020000000041101000000004b10600000000871030000053d092020000032cc52020000042d0a2020000025841201000000008010100000355042020000035c8420200000355062020000045448202000000010d104
  | 6, 25 => 0x5050c2020000050d0d202000002548620200000421092020000051c81201000000008f10100000000411010000000042101000004150420200000520c52020000031cc6201000004350c202000000008210100000000861010000042d0a20200000310c5201000000004110500000520c520200000458812020000050d0d20200000454c8201000004544020100000000841040000035c842020000041cca2020000000087103000004544120200000421092020000021085202000000008410300000354d22020000041d06202
  | 6, 26 => 0x8710100000000871040000034cc1202000001544a2020000000005101000000008410000000000c2101000005050d202000005050c2020000035c842020000051d0d20200000218cb202000002050a2020000001c06201000004350c20200000000831010000045448202000004150420200000000c910100000000c01010000051d0920200000504842020000052cc52020000000084104000004544820200000354d220200000210852020000052cc52020000051d09202000003544320200000000c51010000000084107
  | 6, 27 => 0x4110300000000c61010000025c40201000000010c102000004350c20200000210852020000051c8120100000000c0101000000004110100000000061010000000041105000000004010100000000421010000045487201000000004d1010000050d0d202000004350c20200000000c1101000000004310100000500c5201000003490e202000000010c10200000000871010000000081101000004548720100000415042020000041d0620200000454ca202000000004a10700000210852020000052cc520200000000c5101
  | 6, 28 => 0x5050d202000004350c202000000008d10100000100412010000050c8520200000000c9101000004350c202
  | 7, 0 => 0x8510200000001071020000000083102000000010510200000000c310200000000c3102000000010b102000000004110200000000c4102000000010b10200000000c5102000000008710100000000c31010000000086102000000010a10200000000ca1020000000109102000000010110200000000431020000000006101000000008710100000000ca10100000000041010000000085102000000010110200000000c61020000000105102000000010110200000000cb102000000008110200000000411010000000106102
  | 7, 1 => 0x10610200000000c6102000000004110200000001041020000000104102000000010310200000000cb102000000010c102000000010b102000000004a10200000000c110100000000c1101000000010b10200000000cb10200000000cb10200000000ca102000000008410200000000061010000000108102000000010b10200000000c910200000000c31020000000101102000000000610100000000d21020000000041102000000010b102000000004110100000000c510200000000d210200000000c610200000000c5102
  | 7, 2 => 0x851020000000082101000000004010100000000c810200000001041020000000106102000000008d10100000000cb102000000010610200000000861020000000104102000000008610200000000841010000000105102000000010410200000000c1102000000008610200000000c8102000000010b10200000001061020000000084101000000010c10200000000c010100000000c7102000000008310200000001041020000000081102000000010c10200000000c3102000000004110200000000831020000000106102
  | 7, 3 => 0xc5102000000008310200000000d2102000000010610200000000c7102000000010e10200000000cb10200000000481020000000107102000000010410200000000c410200000000c110200000000ca10100000000c8102000000010b1020000000086102000000000410100000000d1102000000010a1020000000083102000000010c102000000010310200000000ca101000000008510200000000411020000000004101000000008d10100000000c31020000000043102000000008c10100000000861020000000006101
  | 7, 4 => 0x10310200000000c410100000000801010000000006101000000008610100000000c4102000000004a102000000010d102000000008110200000000ca10200000000c910100000000831020000000085101000000008110100000000c110100000000cb10200000000811020000000085101000000010810200000000c310100000001031020000000084101000000008e101000000004a1020000000101102000000008310200000000c610100000000c9102000000008610200000000c310100000000411020000000006101
  | 7, 5 => 0xc910100000000c310200000000c9102000000010d10200000000d210200000000c11020000000101102000000004310200000000c910200000000c9102000000010b10200000000c110200000001061020000000081102000000008610200000000d21020000000086101000000004910200000000d2102000000008510200000000861010000000083101000000010610200000000c410200000000811020000000107102000000010e10200000000841010000000105102000000008410200000000c91020000000040101
  | 7, 6 => 0xc610100000000d2102000000010b102000000010e1020000000084102000000010710200000000c9102000000008310100000000c4101000000010610200000000c510100000000c910100000000d210200000000ca10200000000c7102000000010d102000000010510200000000cb1020000000083102000000008c10100000000ca10200000000ca1020000000084101000000010e10200000000411020000000084102000000004910200000000c210100000000c8102000000008c10100000000ca1010000000109102
  | 7, 7 => 0x106102000000010510200000000c410100000000801010000000104102000000004310200000000c7102000000008e101000000010c10200000000c410100000000c410200000000c8101000000008110100000000c9102000000004310200000000d21020000000103102000000010a10200000000811010000000104102000000010510200000000ca10200000000c710200000000c610100000000c1101000000010310200000000c910200000000c7102000000008310100000000c6101000000004a10200000000ca101
  | 7, 8 => 0xc51010000000081102000000010810200000000c510200000000c4102000000010c10200000000c410200000000811010000000103102000000010310200000000cb10200000000c7102000000004a102000000008310200000000841020000000041102000000010c102000000010c102000000010a10200000000c61010000000083102000000010d1020000000108102000000008310200000000ca102000000008310200000000c110100000000c71020000000041102000000010c10200000001011020000000082101
  | 7, 9 => 0xc510200000000c8102000000010310200000000d2102000000004a10200000000c710100000000c710200000000831020000000043102000000010110200000000c610200000000c61020000000041102000000008710100000001091020000000103102000000010d102000000004a102000000010a102000000010410200000000c710100000000c51010000000108102000000010110200000000411020000000101102000000004110100000000c610100000000c41020000000103102000000010c10200000000c1102
  | 7, 10 => 0xd1102000000010e10200000000c4102000000008610200000000c21010000000082101000000010910200000000c5101000000010e10200000000c1102000000010e10200000000c210100000000c5102000000010510200000000c8102000000008410200000000ca102000000010b10200000001031020000000081102000000010110200000000c1102000000004a102000000010d1020000000104102000000010110200000000c1102000000010a10200000000c310200000000c410100000000c410200000000c9102
  | 7, 11 => 0xc6102000000008310200000000861020000000082101000000010e102000000008510200000000c7102000000010710200000000871010000000105102000000010a10200000000c3102000000008e10100000000c5102000000010410200000000851020000000105102000000010510200000001091020000000106102000000010810200000000c41020000000106102000000010410200000000c8102000000004810200000001011020000000084102000000010c102000000010a102000000010a10200000000c4101
  | 7, 12 => 0xcb10200000000d010200000000411010000000081102000000008610100000000831020000000104102000000000510100000001051020000000086102000000008510200000000c610200000000c510100000001041020000000103102000000010c10200000000ca1020000000085102000000004a10200000000c310100000000cb102000000010410200000000d210200000000c51020000000086102000000010e10200000000c810100000001031020000000081102000000010910200000000c51020000000107102
  | 7, 13 => 0xc51020000000107102000000010810200000000841020000000043102000000008110200000001031020000000108102000000010e102000000010810200000000c310200000000c510200000000cb102000000010a10200000000c710200000000c81020000000085102000000008710100000000c510200000001031020000000109102000000010a10200000000c4102000000010e102000000008610200000000c510200000000c9102000000008110200000000c8102000000010a10200000000c710200000000c6102
  | 7, 14 => 0x86102000000010710200000001091020000000043102000000000610100000000ca10200000000861020000000085102000000008110100000000cb10200000000861020000000108102000000008610100000000c1102000000010e102000000008310100000000d21020000000083102000000010410200000001051020000000042101000000008510100000000c610200000000c1102000000008e10100000000c110200000000811020000000085102000000010d10200000000cb10200000000c81020000000083101
  | 7, 15 => 0x8610100000000811020000000107102000000008410200000000c41020000000083102000000010310200000000c61020000000084101000000010d10200000000811020000000103102000000008410200000000c710100000000841010000000107102000000008310100000000831020000000043102000000010b102000000010b10200000000c1102000000008310200000000851010000000105102000000010a1020000000006101000000010a102000000008e101000000010d10200000001091020000000040101
  | 7, 16 => 0xc1102000000008410200000000841020000000085102000000010d10200000000c110200000000851020000000105102000000010c102000000010d102000000008410200000000801010000000107102000000010d10200000000851020000000083101000000010810200000000c1102000000010e10200000000841020000000041102000000010310200000000cb102000000010d10200000001061020000000080101000000010d102000000008510100000000cb10200000000c210100000000851020000000108102
  | 7, 17 => 0xca10200000000c810100000000c0101000000010c10200000000c5102000000010610200000000c0101000000010c10200000000841020000000041102000000010810200000000c5102000000010d102000000010d10200000000c5102000000010a10200000000ca102000000010c102000000010b102000000010a102000000010e10200000000861020000000087101000000008410200000000c710200000000c910100000000c5102000000010b10200000000c5102000000010c10200000000c41020000000104102
  | 7, 18 => 0x10c102000000008410200000000411010000000006101
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 11 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry true dom_51 roots_51 5 s ws hint
  | 1 => checkCutEntry true dom_62 roots_62 7 s ws hint
  | 2 => checkCutEntry true dom_31 roots_31 8 s ws hint
  | 3 => checkCutEntry true dom_45 roots_45 5 s ws hint
  | 4 => checkCutEntry true dom_61 roots_61 6 s ws hint
  | 5 => checkCutEntry true dom_59 roots_59 6 s ws hint
  | 6 => checkCutEntry true dom_55 roots_55 6 s ws hint
  | 7 => checkCutEntry true dom_47 roots_47 6 s ws hint
  | 8 => checkCutEntry true dom_30 roots_30 5 s ws hint
  | 9 => checkCutEntry true dom_29 roots_29 5 s ws hint
  | 10 => checkCutEntry true dom_27 roots_27 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_63 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_62 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_31 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_45 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_61 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_59 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_55 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_47 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_30 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_29 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_27 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 1000003 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 1000003 ys) ys = true) : ¬ RunD true dom_63 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_63 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_63 == dom_63) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 1000003 zs symsG zs (hk 1000003 zs)
theorem ori_ok {v ys} (h : RunD true dom_63 goalM v ys) : RunD true dom_63 goalM v (ori ys) :=
  pickMin_runD 1000003 ys h symsG ys (hk 1000003 ys) symsG_ok h

def Z (s : Nat) := bar true dom_63 goalM mpG SD SS NN htAt idxH ori 1000003 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 26 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 26 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 128 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 128 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_128 : ∀ i, 128 ≤ i → i < 160 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 32 128 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 160 → Z 5 i = true := (range_split z5_0 z5_128)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_128 : ∀ i, 128 ≤ i → i < 256 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_256 : ∀ i, 256 ≤ i → i < 384 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 256 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 384 → Z 6 i = true := (range_split z6_0 (range_split z6_128 z6_256))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_128 : ∀ i, 128 ≤ i → i < 161 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 33 128 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 161 → Z 7 i = true := (range_split z7_0 z7_128)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8 : ∀ i, 0 ≤ i → i < 18 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 18 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 9) : ∀ i < NN s, Z s i = true := by
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
def RootG (s : Nat) : Bool :=
  scr true dom_63 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD true dom_63 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_63 roots_63 goal_63 10 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_63 goal_63 := by
    have h0 : isConstB dom_63 goal_63 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hnc hr ha
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
    rw [proper_failG zs (List.mem_sublists.2 hsub) heq] at hcov; contradiction

end S_63

theorem lowS_63 : Lower true dom_63 roots_63 goal_63 10 := S_63.noCircuit

def ptN (r : Nat) : Fin 6 → Bool := fun i => r.testBit i.val

theorem roots_bits : ∀ r : Fin 64, roots_63.map (·.testBit r.val) = List.ofFn (ptN r.val) := by
  decide +kernel

theorem goal_eq_f : ∀ r : Fin 64, goal_63.testBit r.val = (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4276808384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) (ptN r.val) := by
  decide +kernel

theorem dom_bit_lt : ∀ r : Nat, dom_63.testBit r = decide (r < 64) := by
  intro r
  by_cases h : r < 64
  · simp only [h, decide_true]
    have hfin : ∀ i : Fin 64, dom_63.testBit i.val = true := by decide +kernel
    exact hfin ⟨r, h⟩
  · simp only [h, decide_false]
    apply Nat.testBit_lt_two_pow
    have hlt : dom_63 < 2 ^ 64 := by decide +kernel
    exact lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) (by omega))

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4276808384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) x)
    (hhas : ∃ g ∈ gates, isNotGate g = true) : 11 ≤ gates.length := by
  obtain ⟨g, hg, hgn⟩ := hhas
  set out := (execN gates roots_63).getD o 0
  have hout : out &&& dom_63 = goal_63 &&& dom_63 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and, dom_bit_lt]
    by_cases hlt : r < 64
    · simp only [hlt, decide_true, Bool.and_true]
      have h1 := execN_bit gates roots_63 r (by omega) (fun g' hg' => (hfan g' hg').1)
      have h2 := congrArg (fun l => l.getD o false) h1
      rw [roots_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN gates roots_63).map (·.testBit r)).getD o false =
          ((execN gates roots_63).getD o 0).testBit r := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN gates roots_63)[o]? with | none => simp | some v => rfl
      rw [hgd] at h2
      exact h2.trans ((hev (ptN r)).trans (goal_eq_f ⟨r, hlt⟩).symm)
    · simp [hlt]
  have hsup0 : ∀ v ∈ roots_63, Avail true mask256 roots_63 v := fun v hv => Or.inr (Or.inl ⟨v, hv, rfl⟩)
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach true gates roots_63 hfan (fun h => Bool.noConfusion h) 0 roots_63 roots_63 rfl hsup0
  have hav_out : Avail true mask256 bank out := by
    by_cases hi : o < (execN gates roots_63).length
    · exact hsup _ (getD_mem hi)
    · rw [show out = 0 from List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hd_sub : dom_63 &&& mask256 = dom_63 := by decide +kernel
  have hm256 : mask256 &&& mask256 = mask256 := by decide +kernel
  have hncG : ¬ IsConst dom_63 goal_63 := by
    have h0 : isConstB dom_63 goal_63 = false := by decide +kernel
    intro hc; rw [(isConstB_iff _ _).2 hc] at h0; contradiction
  have houtm : (out &&& mask256) &&& dom_63 = goal_63 &&& dom_63 := by
    rw [Nat.and_assoc, Nat.and_comm mask256 dom_63, hd_sub, hout]
  have hnc_m : ¬ IsConst dom_63 (out &&& mask256) := fun hc => hncG (by
    rcases hc with h0 | h1; exact Or.inl (houtm.symm.trans h0); exact Or.inr (houtm.symm.trans h1))
  have hnc_256 : ¬ IsConst mask256 out := fun hc => hnc_m (by
    rcases hc with h0 | h1
    · exact Or.inl (by rw [h0]; simp)
    · exact Or.inr (by rw [h1, Nat.and_comm, hd_sub]))
  have hout0 : out.testBit 0 = false := by
    have h0 := congrArg (fun v => v.testBit 0) hout
    have hd0 : dom_63.testBit 0 = true := by decide +kernel
    have hg0 : goal_63.testBit 0 = false := by decide +kernel
    simp only [Nat.testBit_and, hd0, hg0, Bool.and_true, Bool.false_and] at h0
    exact h0
  obtain ⟨s, ws, hs, _, hws, hrun⟩ := reach_to_run hm256 (by decide +kernel) hout0 (by decide +kernel) hnc_256 hr hav_out
  have hws_sub : ∀ w ∈ ws, Avail true dom_63 roots_63 w := fun w hw => by
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (hws w hw)
    exact Or.inr (Or.inl ⟨u, hu, by rw [Nat.and_assoc, Nat.and_comm mask256 dom_63, hd_sub]⟩)
  obtain ⟨q, next, hq, hav_q, hqp⟩ := contraction hd_sub hd_sub hnc_m hrun (show NatReach true dom_63 roots_63 0 roots_63 from rfl) hws_sub
  have hL := lowS_63 q next hq (avail_of_eq houtm hav_q)
  have hlt := countP_not_lt hg hgn
  omega

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [3, 5] }, { op := GateOp.and, inputs := [4, 6] }, { op := GateOp.or, inputs := [2, 7] }, { op := GateOp.or, inputs := [0, 5] }, { op := GateOp.and, inputs := [6, 9] }, { op := GateOp.and, inputs := [1, 8] }, { op := GateOp.or, inputs := [4, 10] }, { op := GateOp.and, inputs := [2, 3] }, { op := GateOp.or, inputs := [0, 13] }, { op := GateOp.and, inputs := [12, 14] }, { op := GateOp.or, inputs := [11, 15] }]

theorem wit_mono : PEqualNP.MetaComplexity.Monotone2 ⟨witGates, 16⟩ := by
  simp [PEqualNP.MetaComplexity.Monotone2, witGates]

theorem wit_eval : ∀ x : Fin 6 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 16⟩ (List.ofFn x) = (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4276808384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) x := by
  decide +kernel

theorem main : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4276808384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074666 * 2 ^ 32 + 4276808384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s ⟨⟨gates, o⟩, hfan, hsz, hev⟩
  by_cases hhas : ∃ g ∈ gates, isNotGate g = true
  · have hlb : 11 ≤ gates.length := lb_with_not gates o hfan hev hhas
    refine ⟨⟨witGates, 16⟩, wit_mono, ?_, wit_eval⟩
    have hlen : witGates.length = 11 := rfl
    change witGates.length ≤ s
    change gates.length ≤ s at hsz
    omega
  · push_neg at hhas
    refine ⟨⟨gates, o⟩, ?_, hsz, hev⟩
    intro g hg
    obtain ⟨h1, h2⟩ := hfan g hg
    refine ⟨?_, h2⟩
    change g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not at h1
    rcases h1 with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exfalso; have := hhas g hg; simp [isNotGate, h1] at this

end PEqualNP.Outside.L_meta_37913_aux

theorem PEqualNP.Outside.L_meta_37913 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4276808384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074666 * 2 ^ 32 + 4276808384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := PEqualNP.Outside.L_meta_37913_aux.main
