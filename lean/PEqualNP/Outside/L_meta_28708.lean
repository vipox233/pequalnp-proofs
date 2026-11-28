import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

/- Finite certificate engine and data adapted from foudres, L-meta-14162, PR19594, commit23498653804. New graph: transported seven-variable slice, one additional essential input, and a new thirteen-gate monotone witness. -/
namespace PEqualNP.Outside.L_meta_28708
namespace Cert

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

def dom_51 : Nat := 0xf000f000f000f
def goal_51 : Nat := 0xeeeeeeeeaaaa0000eeeeeeeeaaaa0000eeeeeeeeaaaa0000eeeeeeeeaaaa0000
def roots_51 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_53 : Nat := 0x33003300330033
def goal_53 : Nat := 0xfafafafaaaaa0000fafafafaaaaa0000fafafafaaaaa0000fafafafaaaaa0000
def roots_53 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xfefefefeaaaa0000fefefefeaaaa0000fefefefeaaaa0000fefefefeaaaa0000
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_81 : Nat := 0x300030000000000030003
def goal_81 : Nat := 0xffffaaaaffffaaaaaaaa0000aaaa0000ffffaaaaffffaaaaaaaa0000aaaa0000
def roots_81 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_83 : Nat := 0xf000f00000000000f000f
def goal_83 : Nat := 0xffffeeeeffffeeeeaaaa0000aaaa0000ffffeeeeffffeeeeaaaa0000aaaa0000
def roots_83 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_101 : Nat := 0x33000000330000003300000033
def goal_101 : Nat := 0xfafafafaaaaaaaaafafafafa00000000fafafafaaaaaaaaafafafafa00000000
def roots_101 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_102 : Nat := 0x55000000550000005500000055
def goal_102 : Nat := 0xfcfcfcfcccccccccfcfcfcfc00000000fcfcfcfcccccccccfcfcfcfc00000000
def roots_102 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_103 : Nat := 0xff000000ff000000ff000000ff
def goal_103 : Nat := 0xfefefefeeeeeeeeefefefefe00000000fefefefeeeeeeeeefefefefe00000000
def roots_103 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_113 : Nat := 0x30003000300030003000300030003
def goal_113 : Nat := 0xffffaaaaffffaaaaaaaaaaaaaaaa0000ffffaaaaffffaaaaaaaaaaaaaaaa0000
def roots_113 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_114 : Nat := 0x50005000500050005000500050005
def goal_114 : Nat := 0xffffccccffffcccccccccccc00000000ffffccccffffcccccccccccc00000000
def roots_114 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffeeeeffffeeeeeeeeeeeeaaaa0000ffffeeeeffffeeeeeeeeeeeeaaaa0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfffffafaffffaaaafafafafaaaaa0000fffffafaffffaaaafafafafaaaaa0000
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffffcfcffffccccfcfcfcfc00000000fffffcfcffffccccfcfcfcfc00000000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfffffefeffffeeeefefefefeaaaa0000fffffefeffffeeeefefefefeaaaa0000
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_163 : Nat := 0xf0000000f00000000000000000000000f0000000f
def goal_163 : Nat := 0xeeeeeeeecccccccceeeeeeeecccccccceeeeeeee00000000eeeeeeee00000000
def roots_163 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_165 : Nat := 0x330000003300000000000000000000003300000033
def goal_165 : Nat := 0xfafafafaf0f0f0f0fafafafaf0f0f0f0fafafafa00000000fafafafa00000000
def roots_165 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_167 : Nat := 0xff000000ff0000000000000000000000ff000000ff
def goal_167 : Nat := 0xfefefefefcfcfcfcfefefefefcfcfcfcfefefefe00000000fefefefe00000000
def roots_167 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_181 : Nat := 0x3300330033003300000000000000000033003300330033
def goal_181 : Nat := 0xfafafafafafaf0f0fafafafafafaf0f0fafafafaaaaa0000fafafafaaaaa0000
def roots_181 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def goal_183 : Nat := 0xfefefefefefefcfcfefefefefefefcfcfefefefeaaaa0000fefefefeaaaa0000
def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_194 : Nat := 0x5000000000000000500000000000000050000000000000005
def goal_194 : Nat := 0xffffffffffffffffcccccccccccccccccccccccccccccccc0000000000000000
def roots_194 : List Nat := [xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_195 : Nat := 0xf000000000000000f000000000000000f000000000000000f
def goal_195 : Nat := 0xffffffffffffffffcccccccccccccccceeeeeeeeeeeeeeee0000000000000000
def roots_195 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_197 : Nat := 0x33000000000000003300000000000000330000000000000033
def goal_197 : Nat := 0xfffffffffffffffff0f0f0f0f0f0f0f0aaaaaaaaaaaaaaaa0000000000000000
def roots_197 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_198 : Nat := 0x55000000000000005500000000000000550000000000000055
def goal_198 : Nat := 0xfffffffffffffffffcfcfcfcfcfcfcfccccccccccccccccc0000000000000000
def roots_198 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_199 : Nat := 0xff00000000000000ff00000000000000ff00000000000000ff
def goal_199 : Nat := 0xfffffffffffffffffcfcfcfcfcfcfcfceeeeeeeeeeeeeeee0000000000000000
def roots_199 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_209 : Nat := 0x30003000000000003000300000000000300030000000000030003
def goal_209 : Nat := 0xffffffffffffffffaaaa0000aaaa0000ffffaaaaffffaaaaaaaa0000aaaa0000
def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_210 : Nat := 0x50005000000000005000500000000000500050000000000050005
def goal_210 : Nat := 0xffffffffffffffffccccccccccccccccffffccccffffcccc0000000000000000
def roots_210 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffffffffffffffeeeecccceeeeccccffffeeeeffffeeeeaaaa0000aaaa0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := 0x330033000000000033003300000000003300330000000000330033
def goal_213 : Nat := 0xfffffffffffffffffafaf0f0fafaf0f0ffffaaaaffffaaaaaaaa0000aaaa0000
def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffffffffffffffcfcfcfcfcfcfcfcffffccccffffcccc0000000000000000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffffffffffffffefefcfcfefefcfcffffeeeeffffeeeeaaaa0000aaaa0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_225 : Nat := 0x300000003000000030000000300000003000000030000000300000003
def goal_225 : Nat := 0xffffffffffffffffaaaaaaaa00000000aaaaaaaaaaaaaaaaaaaaaaaa00000000
def roots_225 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_226 : Nat := 0x500000005000000050000000500000005000000050000000500000005
def goal_226 : Nat := 0xffffffffffffffffcccccccccccccccccccccccccccccccccccccccc00000000
def roots_226 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffffffffffeeeeeeeecccccccceeeeeeeeeeeeeeeeeeeeeeee00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_228 : Nat := 0x1100000011000000110000001100000011000000110000001100000011
def goal_228 : Nat := 0xfffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f000000000
def roots_228 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033
def goal_229 : Nat := 0xfffffffffffffffffafafafaf0f0f0f0fafafafaaaaaaaaafafafafa00000000
def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffffffffffcfcfcfcfcfcfcfcfcfcfcfcccccccccfcfcfcfc00000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xfffffffffffffffffefefefefcfcfcfcfefefefeeeeeeeeefefefefe00000000
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffffffffffccffccffccffcccccccccccccccccccccccccc00000000
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffffffffffeeffeeffccffcceeeeeeeeeeeeeeeeeeeeeeee00000000
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_241 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
def goal_241 : Nat := 0xffffffffffffffffaaaaaaaaaaaa0000ffffaaaaffffaaaaaaaaaaaaaaaa0000
def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffffffccccccccccccccccffffccccffffcccccccccccc00000000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffffffeeeeeeeeeeeeccccffffeeeeffffeeeeeeeeeeeeaaaa0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_244 : Nat := 0x11001100110011001100110011001100110011001100110011001100110011
def goal_244 : Nat := 0xfffffffffffffffff0f0f0f0f0f0f0f0fffff0f0ffff0000f0f0f0f000000000
def roots_244 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xfffffffffffffffffafafafafafaf0f0fffffafaffffaaaafafafafaaaaa0000
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffffffcfcfcfcfcfcfcfcfffffcfcffffccccfcfcfcfc00000000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffffffefefefefefefcfcfffffefeffffeeeefefefefeaaaa0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffffffefffefffefffcfffffefeffffeeeefefefefeaaaa0000
def roots_255 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

namespace S_81
def pairsG : List (Nat × Nat) := [(1, 17), (1, 65), (16, 17), (16, 80), (64, 65), (64, 80)]
def r1sG : List Nat := [1, 1, 16, 16, 64, 64]
def r2sG : List Nat := [17, 65, 17, 80, 65, 80]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_81.map (· &&& dom_81)
def goalM : Nat := goal_81 &&& dom_81
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x4d99e3d8
  | 3, 0 => 0x4d99e3d8
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x30000000000000003000000000000000000000000000000000000000000000002000200000000000200020000000000000000000000000000000000000000000300030000000000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x243
  | 3, 0, 0 => 0x243
  | _, _, _ => 0
def stateW : Nat → Nat
  | 2 => 10
  | 3 => 10
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xc0f0
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x2d5fa
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 6 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 6 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 3 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 3 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 3 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 3 then wireAt i else 0
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
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_81 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 12 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_81 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_81 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)], [(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)], [(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_81 == dom_81) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_81 goalM v ys) : RunD true dom_81 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_81 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_81 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_81 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_81 roots_81 goal_81 4 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_81 goal_81 := by
    have h0 : isConstB dom_81 goal_81 = false := by decide +kernel
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

end S_81

theorem lowS_81 : Lower true dom_81 roots_81 goal_81 4 := S_81.noCircuit

def isoMvS_194 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff00000000ffffffff00000000, 96), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_194 : Lower true dom_194 roots_194 goal_194 4 :=
  lower_iso isoMvS_194 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_81

namespace S_51
def pairsG : List (Nat × Nat) := [(1, 17), (1, 33), (2, 34), (3, 19), (3, 35), (16, 17), (18, 19), (18, 50), (32, 33), (32, 34), (48, 49), (48, 50)]
def r1sG : List Nat := [1, 1, 2, 3, 3, 16, 18, 18, 32, 32, 48, 48]
def r2sG : List Nat := [17, 33, 34, 19, 35, 17, 19, 50, 33, 34, 49, 50]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_51.map (· &&& dom_51)
def goalM : Nat := goal_51 &&& dom_51
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x29c5ac2a
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf000f00000000000000000000000000000000000000000000000000000000000f0000000f0000000000000000000000000000000000000000000000000000000c000c000c000c000000000000000000000000000000000000000000000000000a000a000a000a
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xe44
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 12
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xf00ce00dc01b
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xf96ce9adc57b
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 12 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 12 (i % 8)
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

def symsG : List (List (Nat × Nat)) := [[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_51 == dom_51) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_51 goalM v ys) : RunD true dom_51 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_51 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_51 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_51 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_51 roots_51 goal_51 4 := by
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

theorem lowS_51 : Lower true dom_51 roots_51 goal_51 4 := S_51.noCircuit

theorem lowS_83 : Lower true dom_83 roots_83 goal_83 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc000c00000000000c000c, 64, 66)] (by decide +kernel) (by decide +kernel) lowS_81

def isoMvS_53 : List (Nat × Nat) := [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_53 : Lower true dom_53 roots_53 goal_53 4 :=
  lower_iso isoMvS_53 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51

def isoMvS_101 : List (Nat × Nat) := [(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_101 : Lower true dom_101 roots_101 goal_101 4 :=
  lower_iso isoMvS_101 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51

def isoMvS_102 : List (Nat × Nat) := [(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_102 : Lower true dom_102 roots_102 goal_102 4 :=
  lower_iso isoMvS_102 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51

def isoMvS_113 : List (Nat × Nat) := [(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)]
theorem lowS_113 : Lower true dom_113 roots_113 goal_113 5 :=
  lower_iso isoMvS_113 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_114 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_114 : Lower true dom_114 roots_114 goal_114 4 :=
  lower_iso isoMvS_114 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51

def isoMvS_163 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_163 : Lower true dom_163 roots_163 goal_163 4 :=
  lower_iso isoMvS_163 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51

def isoMvS_165 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_165 : Lower true dom_165 roots_165 goal_165 4 :=
  lower_iso isoMvS_165 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51

def isoMvS_195 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_195 : Lower true dom_195 roots_195 goal_195 5 :=
  lower_iso isoMvS_195 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_197 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]
theorem lowS_197 : Lower true dom_197 roots_197 goal_197 4 :=
  lower_iso isoMvS_197 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51

def isoMvS_198 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff00000000ffffffff00000000, 96), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_198 : Lower true dom_198 roots_198 goal_198 5 :=
  lower_iso isoMvS_198 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_209 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_209 : Lower true dom_209 roots_209 goal_209 5 :=
  lower_iso isoMvS_209 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_210 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_210 : Lower true dom_210 roots_210 goal_210 5 :=
  lower_iso isoMvS_210 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_225 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff0000ffff0000ffff0000, 112), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_225 : Lower true dom_225 roots_225 goal_225 4 :=
  lower_iso isoMvS_225 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51

def isoMvS_226 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff0000ffff0000ffff0000ffff0000, 112), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_226 : Lower true dom_226 roots_226 goal_226 5 :=
  lower_iso isoMvS_226 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_228 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff0000ffff0000ffff0000, 112), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_228 : Lower true dom_228 roots_228 goal_228 4 :=
  lower_iso isoMvS_228 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51

theorem lowS_55 : Lower true dom_55 roots_55 goal_55 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc00cc00cc00cc, 32, 34)] (by decide +kernel) (by decide +kernel) lowS_53

theorem lowS_103 : Lower true dom_103 roots_103 goal_103 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaa000000aa000000aa000000aa, 32, 33)] (by decide +kernel) (by decide +kernel) lowS_102

theorem lowS_115 : Lower true dom_115 roots_115 goal_115 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc000c000c000c000c000c000c000c, 32, 34)] (by decide +kernel) (by decide +kernel) lowS_113

namespace S_117
def pairsG : List (Nat × Nat) := [(1, 17), (1, 33), (1, 65), (4, 36), (5, 21), (5, 37), (5, 69), (16, 17), (16, 80), (20, 21), (20, 52), (20, 84), (32, 33), (32, 36), (48, 49), (48, 52), (48, 112), (64, 65), (64, 80), (68, 69), (68, 84), (68, 100), (96, 97), (96, 100), (96, 112)]
def r1sG : List Nat := [1, 1, 1, 4, 5, 5, 5, 16, 16, 20, 20, 20, 32, 32, 48, 48, 48, 64, 64, 68, 68, 68, 96, 96, 96]
def r2sG : List Nat := [17, 33, 65, 36, 21, 37, 69, 17, 80, 21, 52, 84, 33, 36, 49, 52, 112, 65, 80, 69, 84, 100, 97, 100, 112]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_117.map (· &&& dom_117)
def goalM : Nat := goal_117 &&& dom_117
def NN : Nat → Nat
  | 4 => 3
  | 5 => 4
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xee46669ab792528f466f4f7f
  | 5, 0 => 0xb71981989f6d97e34167af911d53bf89
  | 6, 0 => 0xb71c3dee
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x32003200000000003200320000000000000000000000000000000000300030003000300032003200320032000000000000000000000000000000000033003300330033000000000000000000000000000000000000000000000000003300330000000000330033000000000000000000000000000000000000000000000000000000000033002200330022000000000000000000000000000000000033000000330000003300000033000000000000000000000000000000000000003000300030003000300030003000300000000000000000000000000000000000220022002200220022002200220022
  | 0, 1 => 0x22000000220000002200000022000000000000000000000000000000000033003300330033003300000033000000000000000000000000000000000000003300330033003300220022002200220000000000000000000000000000000000320032003200320032003200320032
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x280755426055432105
  | 5, 0, 0 => 0x4210b5604280554a210564219056
  | 6, 0, 0 => 0x421055
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 24
  | 5 => 28
  | 6 => 24
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x1c073f8e039fffc0001c1f00000e7fb8073e00701cf0000077
  | 0, 1 => 0x3bfff3e03fc00ee380e7f
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xd056aae3fbeffe1289e1f42a006b59c573e45715cf04a52f7
  | 0, 1 => 0x2508337ff3f57feb7eefafeff
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 25 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 25 (i % 8)
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
def CN0 : Nat → Nat
  | 3 => 2
  | 4 => 14
  | 5 => 28
  | _ => 0
def CH0 : Nat → Nat → Nat
  | 3, 0 => 0x89586e8885928e4e
  | 4, 0 => 0xdd6e677dd1f09649b71c3deeb0fada0a8ce1638089586e888060803568f641d55c8909873b4e9cf138f0f586295e4f751aca24dc04b97464
  | 5, 0 => 0xe45581b5c9b7c66cb71c3deeb04743a8a2488b5091c226ec8184aebd78ce4709772516f571e7567f66b4c4ec6618de055f67a956590953f5422dbc5a4177936d3b4e9cf13355ce9f26aed65f21db681c1fdb40471e7bccf41b5a74a017b5ca6012b002740b370e0a04bb41130295c9fa
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 3, 0 => 0x0
  | 4, 0 => 0x1030100000300000300030202
  | 5, 0 => 0x3000303030001000300030003030000030003010203030203010303
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 6 0 (CN0 s)
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
  | 0 => checkCutEntry true dom_81 roots_81 4 s ws hint
  | 1 => checkCutEntry true dom_101 roots_101 4 s ws hint
  | 2 => checkCutEntry true dom_53 roots_53 4 s ws hint
  | 3 => checkCutEntry true dom_113 roots_113 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_117 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_81 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_101 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_53 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_113 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 12 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_117 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_117 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_117 == dom_117) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_117 goalM v ys) : RunD true dom_117 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_117 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 4 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 4 0 = true)
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
  scr true dom_117 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_117 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_117 roots_117 goal_117 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_117 goal_117 := by
    have h0 : isConstB dom_117 goal_117 = false := by decide +kernel
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

end S_117

theorem lowS_117 : Lower true dom_117 roots_117 goal_117 7 := S_117.noCircuit

theorem lowS_118 : Lower true dom_118 roots_118 goal_118 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x500050005000500050005000500050, 32, 36)] (by decide +kernel) (by decide +kernel) lowS_114

theorem lowS_199 : Lower true dom_199 roots_199 goal_199 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaa00000000000000aa00000000000000aa00000000000000aa, 64, 65)] (by decide +kernel) (by decide +kernel) lowS_198

namespace S_211
def pairsG : List (Nat × Nat) := [(1, 17), (1, 65), (2, 66), (2, 130), (3, 19), (3, 67), (3, 131), (16, 17), (16, 80), (18, 19), (18, 82), (18, 146), (64, 65), (64, 66), (64, 80), (64, 192), (128, 130), (128, 192), (129, 131), (129, 145), (129, 193), (144, 145), (144, 146), (144, 208)]
def r1sG : List Nat := [1, 1, 2, 2, 3, 3, 3, 16, 16, 18, 18, 18, 64, 64, 64, 64, 128, 128, 129, 129, 129, 144, 144, 144]
def r2sG : List Nat := [17, 65, 66, 130, 19, 67, 131, 17, 80, 19, 82, 146, 65, 66, 80, 192, 130, 192, 131, 145, 193, 145, 146, 208]
def mpG : Nat := 0xffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_211.map (· &&& dom_211)
def goalM : Nat := goal_211 &&& dom_211
def NN : Nat → Nat
  | 3 => 1
  | 4 => 4
  | 5 => 10
  | 6 => 4
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x40c15b89
  | 4, 0 => 0x1babcae40bfedd20026bfb8d0163af38
  | 5, 0 => 0x5f1230a553aa818c46df2ca5336466d22b7c22d2231c498f1d4f9bc904db0782033cdb2e030e6b11
  | 6, 0 => 0x746c246751127bde05d38d3003b74642
  | 7, 0 => 0x746c2467
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf000000000000000f000000000000000f000000000000000f000000000000000a000a00000000000a000a00000000000a000a00000000000a000a000000000003000300000000000300030000000000030003000000000003000000000000000f000f000000000000000000000000000f000f000000000000000000000000000f000f00000000000f000000000000000f000a00000000000f000000000000000c000c00000000000c000c00000000000c000c00000000000c000c00000000000f000f00000000000a000a00000000000f000f00000000000a000a00000000000f000f00000000000f000f00000000000000000000000000000000
  | 0, 1 => 0x5000500000000000500050000000000050005000000000000000000000000000c000f00000000000c000c00000000000c000f00000000000c000c00000000000f000f00000000000f000f00000000000a000a00000000000a000a000000000000000000000000000f000f000000000000000000000000000a000a00000000000f000f00000000000c000c00000000000f000f00000000000c000c00000000000f000c000000000000000000000000000f000c0000000000000000000000000005000000000000000500000000000000050005000000000005000000000000000f000e00000000000f000000000000000f000e00000000000f0000
  | 0, 2 => 0xf000f00000000000f000000000000000f000f00000000000f000000000000000f000f00000000000f000c00000000000f000f00000000000f000c00000000000f000f000000000000000000000000000f000000000000000000000000000000000000000000000000000000000000000f000f00000000000c000c000000000000000300000000000000000000000000000003000000000000000000000000000f000f00000000000f000f00000000000f000f00000000000000000000000000000000000000000000000000000000000f000f0000000000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x188204
  | 4, 0, 0 => 0x3acca029c492015023100a7314805
  | 5, 0, 0 => 0xa9c462018e231280601e623114eb988c46388c49018e2344906388c47818ee1188063882d2018e2330806
  | 6, 0, 0 => 0x1c462014e2698806388c4801ac7118806
  | 7, 0, 0 => 0x7118805
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 24
  | 4 => 29
  | 5 => 34
  | 6 => 34
  | 7 => 29
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xe00f801c0073fff18000f000e00f80000e7c1cf073ff0000
  | 0, 1 => 0xe3f00000fe7cff0073ff007300fe7c000000e0ff80e00f80
  | 0, 2 => 0xe0ff80e0fffc00000000fe7c00f000fff00000f000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xe84f913c12f3bad18392f526fadfb3452e7cbef7f7ff8848
  | 0, 1 => 0xc3ed0c57be7eff9afb6d0ad9d7ff7e806524c06d04f87fb7
  | 0, 2 => 0xfaffb7ffffff92c500007736129002fffd6e007526
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 24 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 24 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 23 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 23 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 23 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 23 then wireAt i else 0
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 5 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN0 : Nat → Nat
  | 4 => 11
  | 5 => 50
  | 6 => 7
  | _ => 0
def CH0 : Nat → Nat → Nat
  | 4, 0 => 0x80dcf803746c2467529e478b1cdcb6fc1246e4c50f8353500ef474e60af64f4109b596bf077b00780427d0ec
  | 5, 0 => 0xa3f0c29b9d14e3b08e6b1e2786b3b08680dcf8037eb6aaa87ba603a779ee4cf2746c24676809f67464138a065a5366d257e853735435a6ea530910b0526d576451127bde485946384646aaaf4338ec1840d489493c536f1a3bd6443239cb6c2f35f664983558f566330ef7d82a38fe2927d6293c1f2319551cdcb6fc1a4cab4f1848717013843a4f132be7b5121cc9e40eafec0f0c8f7b560bdb77b60b25386209d13aa20961f12906df5c45060b59fd05d38d300427d0ec03ca59f703b74642015b8c0d00896053
  | 6, 0 => 0x7ba603a764138a06526d576440d4894939cb6c2f330ef7d806df5c45
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 4, 0 => 0x200040204020301010300
  | 5, 0 => 0x500010102020002000404050204000300010100000400040303000204010202040502040401010302050301020002030300
  | 6, 0 => 0x50300040003
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 7 0 (CN0 s)
def CN : Nat → Nat
  | 4 => 1
  | 5 => 3
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0xebb6843
  | 5, 0 => 0x42ece86a352756f92d0ebd3b
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x87100
  | 5, 0 => 0xc51003144008f104
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 3 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry true dom_210 roots_210 5 s ws hint
  | 1 => checkCutEntry true dom_194 roots_194 4 s ws hint
  | 2 => checkCutEntry true dom_83 roots_83 5 s ws hint
  | 3 => checkCutEntry true dom_195 roots_195 5 s ws hint
  | 4 => checkCutEntry true dom_209 roots_209 5 s ws hint
  | 5 => checkCutEntry true dom_81 roots_81 4 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_211 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_210 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_194 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_195 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_209 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_81 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 22 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_211 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_211 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xcccccccccccccccccccccccccccccccc, 126)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xffff0000ffff0000ffff0000ffff0000, 112), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xcccccccccccccccccccccccccccccccc, 126), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xffff0000ffff0000ffff0000ffff0000, 112), (0xcccccccccccccccccccccccccccccccc, 126), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xffff0000ffff0000ffff0000ffff0000, 112), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_211 == dom_211) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_211 goalM v ys) : RunD true dom_211 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_211 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
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
  scr true dom_211 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD true dom_211 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_211 roots_211 goal_211 8 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_211 goal_211 := by
    have h0 : isConstB dom_211 goal_211 = false := by decide +kernel
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

end S_211

theorem lowS_211 : Lower true dom_211 roots_211 goal_211 8 := S_211.noCircuit

namespace S_229
def pairsG : List (Nat × Nat) := [(1, 33), (1, 65), (4, 36), (4, 132), (5, 37), (5, 69), (5, 133), (32, 33), (32, 36), (64, 65), (64, 192), (68, 69), (68, 100), (68, 196), (96, 97), (96, 100), (96, 224), (128, 132), (128, 192), (129, 133), (129, 161), (129, 193), (160, 161), (160, 164), (160, 224)]
def r1sG : List Nat := [1, 1, 4, 4, 5, 5, 5, 32, 32, 64, 64, 68, 68, 68, 96, 96, 96, 128, 128, 129, 129, 129, 160, 160, 160]
def r2sG : List Nat := [33, 65, 36, 132, 37, 69, 133, 33, 36, 65, 192, 69, 100, 196, 97, 100, 224, 132, 192, 133, 161, 193, 161, 164, 224]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_229.map (· &&& dom_229)
def goalM : Nat := goal_229 &&& dom_229
def NN : Nat → Nat
  | 4 => 1
  | 5 => 3
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x92b4d3dc
  | 5, 0 => 0x2f4a5dee0e080bd30bc5a921
  | 6, 0 => 0x2f4a5dee
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x33000000330000003300000033000000330000000000000033000000000000003300000033000000220000002200000033000000330000002200000022000000330000003300000033000000330000000000000000000000000000000000000033000000000000003300000000000000330000000000000033000000000000000000000000000000000000000000000033000000330000003000000030000000300000003000000030000000300000003000000030000000300000003000000022000000220000002200000022000000220000002200000022000000220000003300000033000000000000000000000033000000330000000000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x46885
  | 5, 0, 0 => 0x44455f1115a2c456
  | 6, 0, 0 => 0x44455
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 19
  | 5 => 22
  | 6 => 19
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xffe0c00e7f9cffc0001c1c18000ff3e000e1f07000e601fe00
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfffaeedf7fbcffe4891d1d195006d9b22ae5f0f095e725fe22
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 25 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 25 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 8 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 8 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 8 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 8 then wireAt i else 0
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
def CN0 : Nat → Nat
  | 4 => 4
  | 5 => 6
  | _ => 0
def CH0 : Nat → Nat → Nat
  | 4, 0 => 0x5d0fc6a05866862247510e6d2f4a5dee
  | 5, 0 => 0x422bf4051f1edb251cb9fc721c40222813aca401109a54d6
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 4, 0 => 0x1000101
  | 5, 0 => 0x30002000202
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 4 0 (CN0 s)
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
  | 0 => checkCutEntry true dom_197 roots_197 4 s ws hint
  | 1 => checkCutEntry true dom_228 roots_228 4 s ws hint
  | 2 => checkCutEntry true dom_165 roots_165 4 s ws hint
  | 3 => checkCutEntry true dom_225 roots_225 4 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_229 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_197 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_228 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_165 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_225 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 12 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_229 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_229 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 124)], [(0xffffffffffffffff0000000000000000, 64), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xffffffff00000000ffffffff00000000, 96), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xffffffffffffffff0000000000000000, 64), (0xffffffff000000000000000000000000ffffffff00000000, 32), (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 124), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xffffffffffffffff0000000000000000, 64), (0xffffffff000000000000000000000000ffffffff00000000, 32), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_229 == dom_229) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_229 goalM v ys) : RunD true dom_229 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_229 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
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
  scr true dom_229 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_229 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_229 roots_229 goal_229 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_229 goal_229 := by
    have h0 : isConstB dom_229 goal_229 = false := by decide +kernel
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

end S_229

theorem lowS_229 : Lower true dom_229 roots_229 goal_229 7 := S_229.noCircuit

def isoMvS_167 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_167 : Lower true dom_167 roots_167 goal_167 5 :=
  lower_iso isoMvS_167 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_103

def isoMvS_181 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]
theorem lowS_181 : Lower true dom_181 roots_181 goal_181 5 :=
  lower_iso isoMvS_181 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_118

def isoMvS_213 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]
theorem lowS_213 : Lower true dom_213 roots_213 goal_213 7 :=
  lower_iso isoMvS_213 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_117

def isoMvS_214 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]
theorem lowS_214 : Lower true dom_214 roots_214 goal_214 6 :=
  lower_iso isoMvS_214 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_199

def isoMvS_227 : List (Nat × Nat) := [(0xffff0000ffff0000ffff0000ffff0000, 112), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_227 : Lower true dom_227 roots_227 goal_227 6 :=
  lower_iso isoMvS_227 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_115

def isoMvS_230 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff0000ffff0000ffff0000ffff0000, 112), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_230 : Lower true dom_230 roots_230 goal_230 6 :=
  lower_iso isoMvS_230 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_115

def isoMvS_234 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcccccccccccccccccccccccccccccccc, 126), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]
theorem lowS_234 : Lower true dom_234 roots_234 goal_234 6 :=
  lower_iso isoMvS_234 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_199

def isoMvS_241 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)]
theorem lowS_241 : Lower true dom_241 roots_241 goal_241 6 :=
  lower_iso isoMvS_241 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_199

def isoMvS_242 : List (Nat × Nat) := [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcccccccccccccccccccccccccccccccc, 126), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]
theorem lowS_242 : Lower true dom_242 roots_242 goal_242 6 :=
  lower_iso isoMvS_242 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_199

def isoMvS_244 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120), (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]
theorem lowS_244 : Lower true dom_244 roots_244 goal_244 5 :=
  lower_iso isoMvS_244 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_118

theorem lowS_119 : Lower true dom_119 roots_119 goal_119 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc00cc00cc00cc00cc00cc00cc00cc, 32, 34)] (by decide +kernel) (by decide +kernel) lowS_117

theorem lowS_183 : Lower true dom_183 roots_183 goal_183 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc00cc00cc00cc000000000000000000cc00cc00cc00cc, 32, 34)] (by decide +kernel) (by decide +kernel) lowS_181

theorem lowS_215 : Lower true dom_215 roots_215 goal_215 9 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf000f00000000000f000f00000000000f000f00000000000f000f0, 128, 132)] (by decide +kernel) (by decide +kernel) lowS_211

namespace S_231
def pairsG : List (Nat × Nat) := [(1, 33), (1, 65), (2, 34), (2, 66), (2, 130), (3, 35), (3, 67), (3, 131), (4, 36), (4, 132), (5, 37), (5, 69), (5, 133), (6, 38), (6, 70), (6, 134), (7, 39), (7, 71), (7, 135), (32, 33), (32, 34), (32, 36), (64, 65), (64, 66), (64, 192), (68, 69), (68, 70), (68, 100), (68, 196), (96, 97), (96, 98), (96, 100), (96, 224), (128, 130), (128, 132), (128, 192), (129, 131), (129, 133), (129, 161), (129, 193), (160, 161), (160, 162), (160, 164), (160, 224)]
def r1sG : List Nat := [1, 1, 2, 2, 2, 3, 3, 3, 4, 4, 5, 5, 5, 6, 6, 6, 7, 7, 7, 32, 32, 32, 64, 64, 64, 68, 68, 68, 68, 96, 96, 96, 96, 128, 128, 128, 129, 129, 129, 129, 160, 160, 160, 160]
def r2sG : List Nat := [33, 65, 34, 66, 130, 35, 67, 131, 36, 132, 37, 69, 133, 38, 70, 134, 39, 71, 135, 33, 34, 36, 65, 66, 192, 69, 70, 100, 196, 97, 98, 100, 224, 130, 132, 192, 131, 133, 161, 193, 161, 162, 164, 224]
def mpG : Nat := 0xfffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_231.map (· &&& dom_231)
def goalM : Nat := goal_231 &&& dom_231
def NN : Nat → Nat
  | 4 => 5
  | 5 => 13
  | 6 => 29
  | 7 => 9
  | 8 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x6ce0f58768c4f4f32221a2fe1895022f038aa6e2
  | 5, 0 => 0xe07cb34dd68d7b49c1831ffc8e3efa40786625e85d6e2bf6568ae9914ce798143bec1fe12ad96ea112efe0d7055d3b6d01da1806
  | 6, 0 => 0xfcea52acbfd29120b92b9703a89e5f54a7e89290a377329796271dcd9394040791e3752b8748f8cb795be31a77e89df7770065e67091a3406bfd8cfd6b2383fc67e18c695715199052cce25b4c489abd4406891c3daa5bbf365e9f023057d3ec1ef5e16f1a16b47a168839640cc81b4c0854c534
  | 7, 0 => 0xa59827ca91e3752b77c6ef21561e35fe4e7413d929f60617252597bc21971ca60a1fa079
  | 8, 0 => 0xa26a090d
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff000000ff000000ff000000ff000000ff00000000000000cc000000cc000000cc000000cc000000cc000000cc000000cc000000cc00000000000000ff00000000000000ff00000000000000ff0000000000000000000000ff000000ff000000ff000000ff000000ff000000ff000000ff00000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000ff000000ff000000cc000000cc000000cc000000cc000000cc000000cc000000aa000000aa000000aa000000aa000000aa000000aa000000aa000000aa
  | 0, 1 => 0xf000000000000000f0000000f0000000f000000000000000f00000000000000ff000000ff0000000000000000000000ff000000ff0000000000000000000000ff000000ff000000f0000000f0000000f0000000f0000000f0000000f0000000ff000000ff000000ff000000ff00000000000000000000000000000000000000ff000000ff000000ff000000ff000000ff000000ff0000000000000000000000ff000000ff000000ff00000000000000ff000000ff000000ff00000000000000ff000000ff000000ff000000ff000000ff00000000000000ff00000000000000ff000000ff000000aa000000aa000000aa000000aa000000aa000000aa
  | 0, 2 => 0xf0000000f0000000f0000000f0000000f000000000000000f00000000000000aa000000ff000000aa000000ff000000aa000000aa000000aa000000aa000000330000003300000033000000330000003300000033000000330000000000000000000000000000000000000000000000ff000000ff000000ff000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000ff000000ff000000ff000000ff00000000000000000000000f0000000f0000000f0000000f0000000f0000000f0000000f00000000000000ff000000ff000000000000000000000000000000000000000000000000
  | 0, 3 => 0xaa000000aa000000aa000000aa000000ff000000ff000000aa000000aa0000000f0000000f0000000f0000000f0000000f0000000f0000000000000000000000ff000000ff000000ff000000ff00000000000000ff0000000000000000000000ff000000ff000000ff000000ff000000ff000000ff000000aa000000aa000000ff000000ff0000000f0000000f000000ff000000ff0000000000000000000000ff000000ff000000ff000000ff0000000f0000000f000000000000000000000000000000ff00000000000000ff0000000000000000000000000000000000000000000000000000000000000000000000ff000000ff0000000000000000
  | 0, 4 => 0xff000000ff000000ff000000ff000000f0000000f0000000f0000000f0000000ff00000000000000ff00000000000000ff000000ff000000ff00000000000000ff000000ff000000ff00000000000000ff00000000000000ff000000000000005500000055000000550000000000000055000000550000005500000000000000ff0000000f000000ff00000000000000ff0000000f000000ff0000000000000000000000000000000000000000000000ff000000ff000000aa000000aa000000ff000000ff000000ff000000ff000000aa000000aa000000aa000000aa0000000f0000000f00000000000000000000000f0000000f0000000000000000
  | 0, 5 => 0x55000000550000000000000000000000550000005500000000000000000000000000000000000000ff000000ff0000000000000000000000ff00000000000000ff000000ff000000f0000000f0000000ff000000ff000000f0000000f0
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0xa242040528908621470c218050c204015440c20405
  | 5, 0, 0 => 0xc201538c60c21801506103086010628308620c624308100e6003086012550308601360c21802d260c601138c628908601060c600f38c628334600c600308100b5
  | 6, 0, 0 => 0xc21a200e31c00c204038c60c21a100b39c00c218838c60c21802e031c30867c038c70c218039e31c308600e74c70c219c00e31c90c218039070c21806ce31c308600e68c70c218039865c90c218039872431805ce31c00c219638c6
  | 6, 0, 1 => 0xa24218038c700308600b41a50c218038c70c218038531c3a4218038c70e89c600e31e60c218038c710308600e31c308600b38c702508600e31800c2180613600308690e31808c218038c6
  | 7, 0, 0 => 0x308600ea8c70c21802ce31c3a0218038c70e708600e31c308600e80c70c218038c41c308600e319724308600e31c308600e60c7
  | 8, 0, 0 => 0xc218038c6
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 34
  | 5 => 40
  | 6 => 46
  | 7 => 46
  | 8 => 40
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xffffff800000000007e0fc0fe1fc00000ffffff80000f01e03800000001e07ff000000007e0fc0f000071ce3
  | 0, 1 => 0xfffe0380000001ffc000000001e07ff00ffe00000000fffffc00000f01fff80000fffe03800000f000071ce3
  | 0, 2 => 0xfffe03800000fe00071ce3ffffff80000001fff80000ffe00000000fffffc00000fffe1f8000000000000000
  | 0, 3 => 0xf1ffc71ce3fffe1c00000ffe1fc00000fffffc71ce3fffffc00000fffe1c000000fe00000000001ffc00000
  | 0, 4 => 0xffe1e07ff00f01fff80000f01e0380000f01fff80000f01e1f80000001ffc71ce3ffe00071ce3001e1c00000
  | 0, 5 => 0x1ffc00000ffe00380000001ffc7ff00
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x776eeffffff2124497e0fc0be17c6dadaffffffffffff41e83925254249e27ff00a9b5597e0fc1f0224f1ce3
  | 0, 1 => 0xb53601800b5889ffc2484acad9f27ff00fff11049290fffffc6dadafc9fffb6d6fffff93db7b59f9334f1ce3
  | 0, 2 => 0xbdb611800b51fe334f9ef3dedbb681f03000eefb6d6f77600049290776eec6dadabdb61d800ff88911000000
  | 0, 3 => 0x1f0eecf5cebbdb61c000dafff17c6dadafffffcfdefbbdbffc248dafff71c492da0be11049290000eec2484a
  | 0, 4 => 0xfff9f27ff90f41eefb6d6ffc9f9392525e09ddb0610cfc9e9f9256f000eecb4c6bfff334f9ef388961c0004a
  | 0, 5 => 0x809dd804008776003db7b5cadffe7ff4a
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 44 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 44 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 43 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 43 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 43 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 43 then wireAt i else 0
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
  | 4 => 2
  | 5 => 36
  | 6 => 172
  | 7 => 28
  | _ => 0
def CH0 : Nat → Nat → Nat
  | 4, 0 => 0x8da1a21a3801554d
  | 5, 0 => 0xe4fa2900e4967dd9c21a0a3fc2123605bfd29120b9d87b9fb743ffbeb3cc2125a4b180dea26a090da224ca44896615108748f8cb854a147c7a1397487803962477d8a06a749e92b47230431d71f5a51167e18c695fdcfe9b4ba13ffc4762ffbb45318bf83aa150d43a463a79384f6505331a3d6d26474fac1f0750861aeb4ff21a7cc8ad12e672ac0f647fa00afb1261
  | 6, 0 => 0x3d2ace0f3a9a393b39ed1a1838c99ade37ee90a5362b694b359b4cd134b248143392e96d32970bce30a725db300d1cc62e38b7e92e14db872c3a26602b63add62ad0b2aa29f6061726effea225367133252597bc2403347623ffd76123fbf09623a6fa72234bd3b6230a70b221971ca6206750af2005a9021f4488e21ef0f17d1e9ebbe81e5315fe1def961c1d5b8e2f1d3e42321cdab40b1a8662e919b6a010179f6903173300d817201295159ef12e13b7647013920513125cdeef11fcd2cd1111310b0f21e21b0ed4f5d50e6b992e0e6a75ff0b12edf40a1fa07909c3821f08a75f8e08452fab050860f70311a75601d2c296017dd762001e0a1d00016f25
  | 6, 1 => 0x8b1053e38af5bf5b88df3852877aea088568f6df852bfe318305986881342e0b800aaf1f7e336c537b471aaa77c6ef2177907d8d775754117755d6e97723635175d2f51b74ef80ab74d181b074618a4473e4327a7383260e722230bf71fd696c702e860b6fc7fdbf6d6035916b718bd46a98506869e5f62d670a06e36703b711668bcaa0661549ff636485326286cee96200e4bb617539d7610f204b6099806e60344981601b56215feb0b885c5ed30f5a336ded5a1ed074592e00d95913212358a1eb535740e0c1561e35fe548e1a8e52144b0d4e7413d94e6bc90c4e227f4d4cadbac649e1550148ef94bc471f64424540c51944833b9440865712404a15b4
  | 6, 2 => 0xf3898a07f174688deda143cfe0d314badda3eebbdbf6f923d8b11f22d469ca64d18c530dcf8e6038cbf595a1caaf9408ca5dff91c6927956c21a0a3fbac48b27b5c4b4f3b4503e79b3fc327bb13b5cb3adf3c9b6ac3abf6eaacc61dea8e3041ea7347fc3a59827caa37b6962a3590df3a26a090d9f8d9c959e245cf89c6ff38c9c4b2bf99bcd10729a7c2c7e950e6e0793e382f3937a182192e1c2e590af93299003e1298fa150408f11cd958d666e71
  | 7, 0 => 0xe27b6ddfd18c530dcf8e6038c90e5d9cb0a7ec87a26a090d9a834487937a1821877aea086c605ce1670a06e354aee0254eff90d64c78bdfc4b5fcefc3a43d76d395fc13331c3a9fb2ad3f3f7234ae2cf2025d4401d3537dd1cda2cfd1b6701fc1935560513b764700e6165d10e172dc2
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 4, 0 => 0x0
  | 5, 0 => 0x20207020202040202010002020206040606060202020202050504000506020204010305
  | 6, 0 => 0x60505050605010402040404070807050a040a0406040a01040801010504070b020a030a05010a0402050104080a0a05030704010704010304010a0405090107070406040406030a07060707050108050a0205050507070201020205050805080708020403010a050204030a07060307070102070706020607040105010a0405
  | 6, 1 => 0x201060405050504070503010602070702050407010b070a0707080701060a070b0205070504050204070502
  | 7, 0 => 0x1070501010105040508070a01040101040107010701010101070101
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 9 0 (CN0 s)
def CN : Nat → Nat
  | 4 => 2
  | 5 => 26
  | 6 => 65
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0xd7de4fe6683f83cd
  | 5, 0 => 0xe9f8ceecaf2137d3a00325f0925877b0921a50a2842d3af182b9f5ce81d1bdbd7bd73b4d596ff1865080095c4d31e3614af72a5a3a42b5102e3193212bc9ede41f358095136d086513261d0b110a43d60edcf0a0080b2ba3073488ea03aa444401f743c901b91cbb
  | 6, 0 => 0xe5fab044e3be4be5d3fd0647c21592c2b6bc56edab6dcf9aa4662a07a31378bca1ce01359f95bbac9cb4cd028fd9a7918d8e796a8bfb228d8acc1f32861cf3488127b6f27f1aae607ee55440790065977614849a7471a77172886dd26345cba85f873e6b5f4db6cd5a65ef5059456bb0541c43e34ea719db4e2890a84a0a9b6d474e3e07471d8ad4420f7a013d468886395fa78634c75dee3396b2d5319af7812ff6ef932e54126a2ac597542a10013b27cbf402240807b320084bba1e5e2e711e0e41c31d5bbcfe1b973a0f1a7fc6ad1658d2fd14f0f85014b2f739118f848e101814f40f754fdd0c53991b0c3c73ce0bf7b7450820d8f002f18d7f0149b64d
  | 6, 1 => 0xe6227495
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x564d2438c0559438d2301
  | 5, 0 => 0xd03448040051c912010001524880400254122010009543080400438d220100143234804002544e201000d0344804001550c20100147244804000010b1050005543080400340d12010005543080400340d120100095048804001548e2010001524880400438d2201000d03448040051c9120100015248804001550c2010009504880400254d0201
  | 6, 0 => 0x234404000008e10100000034404000000e10100000038404000010c10100000034404000010e10100000248404000009210100000244404000008d10100000234410000010d10100000038404000004d10100000248404000004e10100000234404000009110100000244404000010e10100000234410000000e10100000044414000004d1010000034440400000921010000004840400000d2101000003484040000092101
  | 6, 1 => 0x340404000004d10100000344404000005110100000238404000010e1010000034040400000d110100000438404000009210100000434404000004e10100000244404000008d1010000034440400000111010000024440400000121010000003440400000d01010000034840400000d210100000038404000009110100000144404000000d10100000044404000004e101000003404040000011101000002484140000052101
  | 6, 2 => 0x4e101
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 8 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry true dom_165 roots_165 4 s ws hint
  | 1 => checkCutEntry true dom_229 roots_229 7 s ws hint
  | 2 => checkCutEntry true dom_167 roots_167 5 s ws hint
  | 3 => checkCutEntry true dom_198 roots_198 5 s ws hint
  | 4 => checkCutEntry true dom_227 roots_227 6 s ws hint
  | 5 => checkCutEntry true dom_199 roots_199 6 s ws hint
  | 6 => checkCutEntry true dom_103 roots_103 5 s ws hint
  | 7 => checkCutEntry true dom_230 roots_230 6 s ws hint
  | 8 => checkCutEntry true dom_226 roots_226 5 s ws hint
  | 9 => checkCutEntry true dom_102 roots_102 4 s ws hint
  | 10 => checkCutEntry true dom_195 roots_195 5 s ws hint
  | 11 => checkCutEntry true dom_163 roots_163 4 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_231 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_165 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_229 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_167 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_198 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_227 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_199 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_103 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_230 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_226 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_102 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_195 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_163 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 42 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_231 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_231 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffffffffffffffff0000000000000000, 64), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_231 == dom_231) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_231 goalM v ys) : RunD true dom_231 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_231 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 13 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 13 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 29 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 29 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 9 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 9 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
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
  scr true dom_231 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 8) (h : RunD true dom_231 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_231 roots_231 goal_231 9 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_231 goal_231 := by
    have h0 : isConstB dom_231 goal_231 = false := by decide +kernel
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

end S_231

theorem lowS_231 : Lower true dom_231 roots_231 goal_231 9 := S_231.noCircuit

theorem lowS_235 : Lower true dom_235 roots_235 goal_235 7 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a, 32, 33)] (by decide +kernel) (by decide +kernel) lowS_234

theorem lowS_243 : Lower true dom_243 roots_243 goal_243 9 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf000f00000000000f000f00000000000f000f00000000000f000f00000000, 1, 33)] (by decide +kernel) (by decide +kernel) lowS_211

namespace S_245
def pairsG : List (Nat × Nat) := [(1, 17), (1, 33), (1, 65), (4, 36), (4, 132), (5, 21), (5, 37), (5, 69), (5, 133), (16, 17), (16, 80), (20, 21), (20, 52), (20, 84), (20, 148), (32, 33), (32, 36), (48, 49), (48, 52), (48, 112), (64, 65), (64, 80), (64, 192), (68, 69), (68, 84), (68, 100), (68, 196), (96, 97), (96, 100), (96, 112), (96, 224), (128, 132), (128, 192), (129, 133), (129, 145), (129, 161), (129, 193), (144, 145), (144, 148), (144, 208), (160, 161), (160, 164), (160, 224), (176, 177), (176, 180), (176, 240)]
def r1sG : List Nat := [1, 1, 1, 4, 4, 5, 5, 5, 5, 16, 16, 20, 20, 20, 20, 32, 32, 48, 48, 48, 64, 64, 64, 68, 68, 68, 68, 96, 96, 96, 96, 128, 128, 129, 129, 129, 129, 144, 144, 144, 160, 160, 160, 176, 176, 176]
def r2sG : List Nat := [17, 33, 65, 36, 132, 21, 37, 69, 133, 17, 80, 21, 52, 84, 148, 33, 36, 49, 52, 112, 65, 80, 192, 69, 84, 100, 196, 97, 100, 112, 224, 132, 192, 133, 145, 161, 193, 145, 148, 208, 161, 164, 224, 177, 180, 240]
def mpG : Nat := 0x3fffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_245.map (· &&& dom_245)
def goalM : Nat := goal_245 &&& dom_245
def NN : Nat → Nat
  | 4 => 3
  | 5 => 8
  | 6 => 18
  | 7 => 5
  | 8 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xed7985135c7f766a058917e4
  | 5, 0 => 0xb7ac1332b64f323a9287c36e8cfdd6205d2912d63ac1e2ad1ba766e609ec36e1
  | 6, 0 => 0xf9012b87edd3623fcdca6234c236a0e9c175ed97acc9e1cdac1851e78cfdd6206617cf0c51a52b6c3820e5bc3271e23430a0856b160e4ac511887efd0fe1718b0da198b805bbda1b
  | 7, 0 => 0xc44511c7c236a0e94eeb1b7e17aabe6614b93385
  | 8, 0 => 0xa31c2522
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x330033003300330000000000000000003300330033003300000000000000000033003300330033002200220022002200330033003300330022002200220022000000110000001100000022000000220000001100000011000000220000002200330033000000000033003300000000003300330000000000330033000000000030003000300030003000300030003000300030003000300030003000300030001100110011001100220022002200220011001100110011002200220022002200000033000000330000002200000022000000330000003300000022000000220033003300330033003300330033003300000000000000000000000000000000
  | 0, 1 => 0x30003000300030002000200020002000300030003000300020002000200020022002200220022000000000000000000220022002200220000000000000000003300220033002200330000003300000033002200330022003300000033000000000033000000330000003200000032000000330000003300000032000000320000000000330033000000000032003200000000003300330000000000320032003300000033000000330000003300000033000000330000003300000033000000000000000000000000000000000000003100310031003100300030003000300022002200220022002200220022002200220022002200220022002200220022
  | 0, 2 => 0x110011001100110000000000000000001100110011001100000000000000000032003200320032003200320032003200320032003200320032003200320032000000000032003200000000003200320000000000320032000000000032003200110011001100110010001000100010001100110011001100100010001000100033003300330033003200320032003200330033003300330032003200320032000000000000000000000000000000000033003300330033003000300030003000310031003100310030003000300030003100310031003100300030003000300033003300330033000200020002000200330033003300330002000200020002
  | 0, 3 => 0x300030003000300000000000000000003000300030003000000000000000000330033003300330030003000300030003300330033003300300030003000300032003200320032003000300030003000320032003200320030003000300030003300330003000300330033000000000033003300030003003300330000000000330033003300330033003300330033002200220022002200000000000000000000000000000000002200220022002200000000000000000022002200220022
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x10662814831140a4188205
  | 5, 0, 0 => 0x20cc170180468cc0520d0c381883404e0650d0b38188a1984060114310148a48d076
  | 6, 0, 0 => 0x11433380c450cc8381c8ad8d0703808d1a0e0620cc809c0e020d0138181a50d0703008a1a0f9601143c5c0cab0d15381c8a1a2870391531a0e07011521a0ec454468381c8a1a20703914343ce07
  | 6, 0, 1 => 0x456d07031156e20e07
  | 7, 0, 0 => 0x114341dc072286641c0e450d18381c8ab0d0703914341fa07
  | 8, 0, 0 => 0x8a1a0e06
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 29
  | 5 => 34
  | 6 => 39
  | 7 => 39
  | 8 => 34
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x1ffc0000001e7ff001e70079ffc0079ff00780f800000001e01e7e001e7ff001e70079ffc0079ffff80000000
  | 0, 1 => 0x79e1c0001c00000000000e3800039f80001e7ff001ff00781fc1e7ff8e0000e7e000001ffc1e7e001e000001e7
  | 0, 2 => 0x1ffc0000001e078079ff00781e01e7fc0007ff078180079ffc1e7fc0007ff079f80001ffc1e7e001e7ff00007
  | 0, 3 => 0x1e1c000000007ff079f800001e01e7e3f00787f8000fffe0000000001e000001e7
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x9245ffe09212dbf7ffaafe7142d5902050bf087a0f904a490a5e15e7e2daf776aaf63146d7b42071bfffc4404110
  | 0, 1 => 0xb6f5a1ea181c01008900084e3d0a6f9fa9471bded181de03de17c1bed78e4212e7e210000ceb4f3a093e08928be7
  | 0, 2 => 0x9205dda09001b7e9f97fbff01da1641aed76c1f76d7418fffffffffffc0003bbd3cecdb0fdfb5f7e2dbd7ffaa687
  | 0, 3 => 0x9245a1e010136d3fffd7dfc494a7e55e7f3f997a7f944effff3341065092e00028b63
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 46 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 46 (i % 8)
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
def CN0 : Nat → Nat
  | 5 => 19
  | 6 => 68
  | 7 => 30
  | _ => 0
def CH0 : Nat → Nat → Nat
  | 5, 0 => 0xf9012b87eb0a3da2d7781edfcf7aaa64cdca6234c66d726ca31c25229a54783d94ddae388dd5417e8bb996c47c53687e49b3f0323cd0538b23af6899219228cd1a725c7e13726c8403a57d78
  | 6, 0 => 0xca80d7f9c9b83eefc44511c7c2144499b8409541aeb70915aeb59650a46ca310a31c2522a18b2af594250cf79056c2938d476c2989fae725890e6ce1844ff11182cc79f8811dd56b80df2fdb7fe1065e78eaa66d753ba39572ce18116d6f08056a847b996327046c6298c64c5f9350f35785466c56b755cd5589d0fc5368cd7f52ecaec14eeb1b7e49b3f03247927b0241e3f7113d647f463b9eeda7390d58c732f93da9315bbcd92cc5c6e82b9bc67c1ffe63ec1edd0de01a2a182c19f3cf4d17aabe6616af61ba14b9338513570d44120e7efe104068720ca627760c5ae50a0a58b92109b464c00634fa2a04fb579d04d111900207ff9a01c5377301941679
  | 6, 1 => 0xe0300982cf7aaa64cdf2ce72ccd0cf39
  | 7, 0 => 0xe5ce9950d6a520e9ccd0cf39a31c2522968eb259929dbb1d8e2ef21a7aaad27770127cae6cb3a2df64a4f99c5e13b43653bd1678521652b24e81419f4cdbedae4a7f33ad4a252f953683d51035f166742bf641852173784f1f0f1a7e1c191e111830b6a614fc4faa0ec17b810ca6277603da2a1400d42d07
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 5, 0 => 0x1000100010100040401020103010101040301
  | 6, 0 => 0x500010502050100020104030005050000040201010504000503010505050100030303000301030005020001050205050002010205040500050505030501030301020300
  | 7, 0 => 0x30205000203000302000303020002030003000000000000000202050200
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 8 0 (CN0 s)
def CN : Nat → Nat
  | 4 => 3
  | 5 => 7
  | 6 => 53
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0x8f0450524805ec2834ed5ef7
  | 5, 0 => 0xfa28e776b7f5a93ba8e8cc6f816592df71942ad44066f7560f2760be
  | 6, 0 => 0xee95262be1c58b1bc72c0e3ab55e951db279f4c9ae7058cea22ce3849f637c029d1a812591e8708482ecdd52816f17587f97705577e0427273a50dfd6e8f300e6e06011e6d5f159f6baa7a3e6426d52862c65c7859bc10105706ed114c3ab3dd4bfb87ea42ad31a541011436408bf6043ee006493c5597ab3a11c39b386d3040362ee2fc32f70aa72910fe1728d729472489e09220a7d78620424ddd142d0ad112a784780ffa203f0cead7990c1a0a4d0c10cb4f0bdb277b0953a6bd0748baa905a21051043a5a6303b5b194029f0187018dcc90
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x340c20056c0c034c015b0300d300
  | 5, 0 => 0x300d2000000c034800000300d2000001004480c001044d20200000438414000300d200
  | 6, 0 => 0x134400000004210300000304400000004e1000000013440800000421030000014440c000004210000000038400000000e10000000038400000004d1020000030440800000511030000040840c00000c110200000134400000004110300000104408000000e1020000010440800000511030000013440000000c11000000004040c00000111030000004040c000000c100000000384080000012103000000384000000041100
  | 6, 1 => 0xd1000000014840c000005110300000108408000004d10200000030400000004110300000030400000000d1000000010440c000004e10200000108408000000d1000000004040c000004e10200000308408000005210300000304408000004e1020000014440c000000e102
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 7 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry true dom_229 roots_229 7 s ws hint
  | 1 => checkCutEntry true dom_244 roots_244 5 s ws hint
  | 2 => checkCutEntry true dom_213 roots_213 7 s ws hint
  | 3 => checkCutEntry true dom_117 roots_117 7 s ws hint
  | 4 => checkCutEntry true dom_181 roots_181 5 s ws hint
  | 5 => checkCutEntry true dom_241 roots_241 6 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_245 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_229 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_244 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_213 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_117 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_181 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_241 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 42 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_245 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_245 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffffffff00000000ffffffff00000000, 96), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_245 == dom_245) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_245 goalM v ys) : RunD true dom_245 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_245 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 8 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 18 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 18 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 5 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 5 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
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
  scr true dom_245 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 8) (h : RunD true dom_245 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_245 roots_245 goal_245 9 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_245 goal_245 := by
    have h0 : isConstB dom_245 goal_245 = false := by decide +kernel
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

end S_245

theorem lowS_245 : Lower true dom_245 roots_245 goal_245 9 := S_245.noCircuit

def isoMvS_246 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_246 : Lower true dom_246 roots_246 goal_246 7 :=
  lower_iso isoMvS_246 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_235

namespace S_247
def pairsG : List (Nat × Nat) := [(1, 17), (1, 33), (1, 65), (2, 34), (2, 66), (2, 130), (3, 19), (3, 35), (3, 67), (3, 131), (4, 36), (4, 132), (5, 21), (5, 37), (5, 69), (5, 133), (6, 38), (6, 70), (6, 134), (7, 23), (7, 39), (7, 71), (7, 135), (16, 17), (16, 80), (18, 19), (18, 50), (18, 82), (18, 146), (20, 21), (20, 52), (20, 84), (20, 148), (22, 23), (22, 54), (22, 86), (22, 150), (32, 33), (32, 34), (32, 36), (48, 49), (48, 50), (48, 52), (48, 112), (64, 65), (64, 66), (64, 80), (64, 192), (68, 69), (68, 70), (68, 84), (68, 100), (68, 196), (96, 97), (96, 98), (96, 100), (96, 112), (96, 224), (128, 130), (128, 132), (128, 192), (129, 131), (129, 133), (129, 145), (129, 161), (129, 193), (144, 145), (144, 146), (144, 148), (144, 208), (160, 161), (160, 162), (160, 164), (160, 224), (176, 177), (176, 178), (176, 180), (176, 240)]
def r1sG : List Nat := [1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 4, 4, 5, 5, 5, 5, 6, 6, 6, 7, 7, 7, 7, 16, 16, 18, 18, 18, 18, 20, 20, 20, 20, 22, 22, 22, 22, 32, 32, 32, 48, 48, 48, 48, 64, 64, 64, 64, 68, 68, 68, 68, 68, 96, 96, 96, 96, 96, 128, 128, 128, 129, 129, 129, 129, 129, 144, 144, 144, 144, 160, 160, 160, 160, 176, 176, 176, 176]
def r2sG : List Nat := [17, 33, 65, 34, 66, 130, 19, 35, 67, 131, 36, 132, 21, 37, 69, 133, 38, 70, 134, 23, 39, 71, 135, 17, 80, 19, 50, 82, 146, 21, 52, 84, 148, 23, 54, 86, 150, 33, 34, 36, 49, 50, 52, 112, 65, 66, 80, 192, 69, 70, 84, 100, 196, 97, 98, 100, 112, 224, 130, 132, 192, 131, 133, 145, 161, 193, 145, 146, 148, 208, 161, 162, 164, 224, 177, 178, 180, 240]
def mpG : Nat := 0x3fffffffffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_247.map (· &&& dom_247)
def goalM : Nat := goal_247 &&& dom_247
def NN : Nat → Nat
  | 5 => 4
  | 6 => 32
  | 7 => 62
  | 8 => 48
  | 9 => 8
  | 10 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0xba72231f9f7e76bf454045cd2a0399ad
  | 6, 0 => 0xffce2b19f88408ece899d924da969587d74e209cd0310c01cf35401fc5740eebc0e83a67ba3bed00b6c487a2ab1ea174a265e3389602fae18a09577986b64af281cfd8a77ff58b4f611abd7d5a92a32c56b4e3bc4cc575af4b7f001a48abf9e64148d2e62b87a6eb2698aa63244879932376ace21ff82afc07a1547800fd08e1
  | 7, 0 => 0xfde02344f9af9986ebb47d62ea784095ea50ffc9e1ead534df89fdc4ddc3c273da969587d18dd25bd0b84063cd90907dc9f69960c5740eebbbe4adf0b9c90e09b7005922b543ef2eb50c572faeedc59ca720e682a2645bf9a1778cf59d58fbe49bd002ff9729014a963ce49d8d6e3c068d5dd33b879d32ed84e0d0a5830660597e1583d97c65e0f275a977b46cee1bd06b0a9eb0640f0a6e5b42b7ff57a2880f54f1bee2529727fa5030b1664f69093d4dea824b3e588b2a372d507533dc74e733394e6e2fd413b72ec42df92ba2f6152a1662e42170db121d90a370177685951636c3ff13323d980d3406f809ea85a104b5599c00fbc1b7
  | 8, 0 => 0xfed211effc1e34b9fbd03612ec7c525eec06ca44e442d38ce1791443e14e869be0fa1a10e0602c3bd573ae55d06a4da3c87069aebef02d33b9fdf3ecb4103e059fb66cab98a0342e939b066b8fa7046487d51d967f575afb73d55b286e18f9066c3e85386b56d02a66583b975df6bc0c5af2d5d554dc0c4c4f69093d4ea2d8584b7b10b3429122ba3fccd9c03e588b2a3c77327638448c6f332fbd2b32a3ce452c02cb9927745f042170db122106c32519ba9af41636c3ff155593110a834203
  | 9, 0 => 0xfac654aef396b740e442d38cd2172daab4103e05868418da48d9328144e5307a
  | 10, 0 => 0xabd6bf33
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x5500000055000000ff000000ff0000005500000055000000aa000000aa000000ff000000ff000000ff000000ff000000ff000000ff000000aa000000aa00ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc005500550055005500aa00aa00aa00aa005500550055005500aa00aa00aa00aa000000ff000000ff000000ff000000ff0000005500000055000000aa000000aa00ff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000
  | 0, 1 => 0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00000000000000000000005500000055000000aa000000aa0000005500000055000000aa000000aa00ff00ff00ff00ff000000000000000000aa00aa00aa00aa0000000000000000000000ff000000ff000000aa000000aa000000ff000000ff000000aa000000aa00ff00ff00ff00ff00ff000000ff000000ff00aa00ff00aa00ff000000ff00000000000000000000000000aa000000aa0000005500000055000000aa000000aa00ff00ff00ff00ff00aa00aa00aa00aa00ff00ff00ff00ff00aa00aa00aa00aa
  | 0, 2 => 0x5500550055005500aa00aa00aa00aa0000000000000000000000aa000000aa000000ff000000ff000000aa000000aa00fc00fc00fc00fc00fc00fc00fc00fc00fe00fe00fe00fe00fe00fe00fe00fe003300330033003300000000000000000011001100110011000000000000000000cc00cc00cc00cc00cc00cc00cc00cc00ee00ee00ee00ee00ee00ee00ee00ee00ff00ff00ff00ff000000000000000000ff00ff00ff00ff000000000000000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00ff00ff00ff00cc00cc00cc00cc00ee00ee00ee00ee00cc00cc00cc00cc
  | 0, 3 => 0xff00aa00ff00aa00ff000000ff000000ff00aa00ff00aa00ff000000ff000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00aa00aa00aa0055005500550055000000000000000000550055005500550000000000000000000000aa000000aa000000aa000000aa000000ff000000ff000000aa000000aa00aa00aa00aa00aa000000000000000000aa00aa00aa00aa00000000000000000000000000000000000000000000000000ff00ff00ff00ff00aa00aa00aa00aa00ee00ee00ee00ee00cc00cc00cc00cc00ee00ee00ee00ee00cc00cc00cc00cc00bb00bb00bb00bb00aa00aa00aa00aa00bb00bb00bb00bb00aa00aa00aa00aa
  | 0, 4 => 0xff00ff00ff00ff00ff00ff00ff00ff000000000000000000aa00aa00aa00aa00ff00ff00ff00ff00ff00ff0000000000ff00ff00aa00aa00ff00ff0000000000ff00ff00ff00ff00ff00ff00ff00ff00aa00aa00aa00aa00aa00aa00aa00aa000000000000000000aa00aa00aa00aa000000000000000000aa00aa00aa00aa005500550055005500ff00ff00ff00ff005500550055005500aa00aa00aa00aa000000000000000000aa00aa00aa00aa005500550055005500aa00aa00aa00aa00ff00ff00ff00ff00ff00ff00ff00ff005500550055005500aa00aa00aa00aa00ff00ff00ff00ff00ff00ff00ff00ff00aa00aa00aa00aa0000000000000000
  | 0, 5 => 0xff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000aa000000aa0000005500000055000000000000000000000055000000550000000000000000000000000000000000aa00aa00aa00aa00ff00ff00ff00ff00aa00aa00aa00aa0000000000000000000000000000000000aa00aa00aa00aa00aa00aa00aa00aa00ff00ff00ff00ff00cc00cc00cc00cc00ff00ff00ff00ff00ee00ee00ee00ee0000000000000000000000000000000000ff00ff00ff00ff000000000000000000aa00aa00aa00aa00aa00aa00aa00aa00ff00ff00ff00ff00aa00aa00aa00aa00000000000000000000000000000000000000ff000000ff000000aa000000aa
  | 0, 6 => 0xff00ff00ff00ff000000000000000000aa00aa00aa00aa00f000f000f000f000f000f000f000f000fa00fa00fa00fa00fa00fa00fa00fa00ff00ff00ff00ff00f000f000f000f000fa00fa00fa00fa00f000f000f000f000cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00ee00ee00ee00ee00fe00fe00fe00fe00fc00fc00fc00fc00fe00fe00fe00fe00fc00fc00fc00fc00f000f000f000f000f000f000f000f000f000f000f000f000fa00fa00fa00fa00ff00ff00ff00ff00ff00ff00ff00ff0055005500550055000000000000000000ff00ff00ff00ff000000000000000000ff00ff00ff00ff00aa00aa00aa00aa
  | 0, 7 => 0xff00ff00ff00ff000000000000000000550055005500550000000000000000005500550055005500550055005500550055005500550055000000000000000000000000000000000000000000000000000000000000000000aa00aa00aa00aa000000000000000000000000000000000055005500550055000000000000000000ff00ff00aa00aa00ff00ff0000000000ff00ff00aa00aa00ff00ff0000000000fa00fa00fa00fa00f000f000f000f000fa00fa00fa00fa00f000f000f000f000aa00aa00aa00aa00aa00aa00aa00aa000000000000000000aa00aa00aa00aa
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x1440c824061440c81c061440c218061440c20406
  | 6, 0, 0 => 0x510308d01851032066c0715110368201c511920b480715111361201c510320d480715110309701c510320b34071440cf59201c54553d250071444c82d201c01511103ce600510320d018510320b30071440c808b01c014a1032006
  | 6, 0, 1 => 0x15155321201c510308b480715110322301c51033dc480715f10378801c54440c8880700510308b01851033c6480715110384201c510320234071440c82d281c510308d480715f10321a01c54440de08071440c235d01c51033dc3927
  | 7, 0, 0 => 0x1440c8b0b48080054440c274071440c82d26c081440de3c6480815112b4cf480800015110308061440cf2d2a808151103a4f48081440cf2e848081511033e7392815110378f48080054440c84a071440e53c6480800510320b6c070264440cf48071511039643928
  | 7, 0, 1 => 0x1440da3cb48080054444c848071511133d250080054440c830071440cf2ce480800015f1032006151103c0f38080054440c808071440cfbcb48081440cf2d274080054440c248071440cf2d2b8081440e93dc48080051033cb4807151103b4f48081511032254808
  | 7, 0, 2 => 0x547364f48071440de3cb480800544464848071440cf712a8080054554cf48071511036a53d28151c833ce48081440c82d2740800544440f48071440c82d2b80815110321a6c081440e53cb48080057c40c8480715110368f3928151103202480815110394f4b18
  | 7, 0, 3 => 0x1440c83c6480815110321a95281440cf18e480815110322539280054750cf48071440c894b48080052840cf48070054440cf38c70051033dc480715110379a3d281511037886c08151103a4f39281511343ce48080051033c64807
  | 8, 0, 0 => 0x15f1033d201c01511033d280081511033f84aa0240151103225480815110378f39202400054444cf48070054440cfdd202001511033ce4aa81511032253d202400054760cf48070054440e93d202054440cf90e480915110321a3d2024015110378f48080054440e449d02054440c83ce4809
  | 8, 0, 1 => 0x54440e53ce4a001511033d2ec080054440c8b1202001511032126c0800510320f2d2020003a4440cf4807000151e433d201c0151103c0f48080001511193d201c01511033e7480800015110321b01c54440de94f48090054440cf48c020015110396448080001440cf2d201c54440de20f4809
  | 8, 0, 2 => 0x54440c849d02054440e93d2a80915110394f49d02454440c83d2740900015110391d01c015110320f48080054440cf4be020015110368f48080054440cf4bd02054440e53d2ec091511033e44aa02454440cff0e48090001511033d281c54440c83d2a8090054440cf4b102001511033d27408
  | 9, 0, 0 => 0x1511033e4480815110394f480815110320f48081511033ce48081511033d274081511033d2a8081511033ec48081511033d26c08
  | 10, 0, 0 => 0x54440cf4807
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 40
  | 6 => 46
  | 7 => 52
  | 8 => 58
  | 9 => 52
  | 10 => 46
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xf0fffffc00001e3cf1c3c3fffff0000078f3c7ff000f803f8000000000000001f001fe07ffc0000000000007879fc0fe0003e3fff0000078f3c70f0fffffc00001e3cf1fffffc00000000000000
  | 0, 1 => 0xf8000000001e3cf1fffffffff00000000000000f8fffc00001e3cf1c0000000000000000000000f8fffc00001e3cf1fc3c00000f1fff800000000f8fffc00001e3cf1c003e3fff0000078f3c7
  | 0, 2 => 0xfffc00001e3cf1c003e3fff0000078f3c70000007c007ff9fffffc00003fff0000000000000000000007879ffcffc00003fff00000000000f0f000003c7ffe0000000000000001e1e7f03f8
  | 0, 3 => 0xf0f000003c7ffe000003ffffffff0000078f3c700000fffc00000000000003e3fff0000078f3c70000000000000000000000003fff0000078f3c700000000007879fc0fe0003e3fff0000078f3c7
  | 0, 4 => 0xfffff000000001e3cf1ffc003e00fe000000000fffff000000001e3cf1c003e00000000078f3c7ffffffffc00001e3cf1c003e3fff0000078f3c7ffffffffc00001e3cf1fffffc00000000000000
  | 0, 5 => 0xffffffffc00001e3cf1c00003fff00000000000000f8fffc00001e3cf1c000000000000078f3c700000fffc07879ffcffc00003fff00000000000000f8fffc00001e3cf1c00003fff0000078f3c7
  | 0, 6 => 0xfffff000000001e3cf1c000001f001fe07fffc70000007c007f81fff0000000000001e1e7ff3ff0000007c007ff9ffffe0000001f001fe07fffc7ffffffffc0000000000000003fff0000078f3c7
  | 0, 7 => 0x3fff00000000000fff07fffc00000000000000000000000078f3c700000fffc00000000003fc003e00fe0000000000000007c007f81fff000003e00000000078f3c7
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xf05fb6a8080015aaac83c37efbb0200076ebb6ff040fa03f9110449229110489f049fe07ffc0022209108897879fc0fe2665f3dee92aabdab2d30f0dfb6a8080015aaacbffffe10801110448a20
  | 0, 1 => 0x111f808444888be3cf1fffffffff8199966cb340905cb6a8080014a8a4a2221231900000204104090dcbeec08001cb8e5be3e9335df1fffa85145010583288080014a8a4a667f3fff92aabfaf3d7
  | 0, 2 => 0x739a4aaae68c34c04160eb30200072e3966661b3fcdffffbfffffe222139cc800810000002220918ccdf8fbfdcffe22213fff80889224114f0f204113c7ffe204106aaa3673b25e1e7f43fc
  | 0, 3 => 0xf0fa04957c7ffea14517ffffffff93bbbfefbf788804f7ba0222408004004360eb30200072e3960008008440000081041000001ef792aabba71d72228918cc97879fd0ff2667f3bdd922a3f8f3c7
  | 0, 4 => 0xfffff84204cccb72eb8ffe313f99fe44431658efffff8c644cccbf3ef9c445e000012222d8b2c3fff7ff7ba4eeef7aebcc445e1ce692aabdab2d3ffffff7ba4eeef7aebcfffffe3190111064cb24
  | 0, 5 => 0xfffffbeec0c441dbaed820012daa00000020010111787bde4aaafebcf5c0000021112222b871c7aaa8dfffedfafffdcffc00001ef780889224114111f87bde4aaafebcf5c00000eb302000326196
  | 0, 6 => 0x7777b00004cccb72eb8d11048bf15bfe2fffdc7ccc96afe527f81fff4108882442237e3eff33fb6669b3fcdb7ff9fffff1110489f05bfe2fffcc3ffffff7ba066651a28c222213fff92aabba71d7
  | 0, 7 => 0x222213dee80889020010eee07f7ba066641820c000000000122229830c300000739a02224080043fc303e91fe44431658e444922fc527f81fff410447e000012222d8b2c3
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 78 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 78 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 63 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 63 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 63 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 63 then wireAt i else 0
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
def CN0 : Nat → Nat
  | 5 => 1
  | 6 => 76
  | 7 => 372
  | 8 => 181
  | 9 => 79
  | _ => 0
def CH0 : Nat → Nat → Nat
  | 5, 0 => 0x5e77492
  | 6, 0 => 0xcd83da44c5aa88b5c53802bac12d5c44c01655fbc002fc95be74b3c9bbddb14bbae02188b3f1feccb0191f83aea6e7fdae3340c5acc065bfabd6bf33a8a72d07a52e05f99f088ebf9cc3c4589989e17b98ff8b6d95c87bf0932e8a478ba9b32f84f19816831687f47c65e0f27a928b907206aeb4701c3a8d6e88b25d6ca6dd45685ee9fc640f0a6e60ab43045fae756956b8ec2d56b0cc2c5446bad551e3648c4d97426048e379c3479b757746e10e4a44be015c40cf52d03f09177f3ae2e37739ca2ace38d30a4636a25cdc2a4bd1ae29b5beba2885965d1c3e0309186c6b1013d2a52813323d981177010410e84f1806a681da06504fbc031cb31102bce201
  | 6, 1 => 0xfe9c4ec2eea74950ec3960dfe6a08f46e5ad0a32e3a00fa1dca125d0d8de5162d5447b5bd457ff96d3649035cf100cd1
  | 7, 0 => 0x2dec10392d80a6182ca6afdb2c3ae82d2bbbedfa2b879f342a65c6b82a3ebc4c2a15157b29b5beba29143179288d23e6281d5ff2272cbac326d108f326c0019c26b7572926286a5a2583ba8024b6e6dd249ab38c2472de9d23cfe67f2352dcb122c346ba219a05f221182b0120900f9e2008d3a71e6d82031cbea7c41c59ce491b4923e51b4348f81a8a9487196fa082180d7b941782c370175fff29155593111357ed28124738bb121a7330114d566710d7ce76107fc69a103061bb0f38a63c0ee1ff3e0cacf0a10ca3b6440b0305ad09e3a03a0940f8860801e54f0719e0f107128b4005fc8d1704bfc7d600dc7e0700c11db300a9068900427cbf0027e852
  | 7, 1 => 0x5c6957755af2d5d55a985c3f5a04b4a257a5a05955fb029054dc0c4c5406b37354027c0653b48f8552ff0a6e52df5811527de1375138bcbd5093a397500eca694ea92f704e82b4cf4ba682524a22942749714d544930c5dd48f46fef48d93281487934f047bfb47a46ebdedf46e7ef7045a04ac744cc08b244bfe99944865947446c017343d9951a431d503242be694f424d08b7423f6f1c4121ce914105953e407e0b41407d0e1e400326203eb651923e5394833d45695d3c0019753bb838073b0fd1ae3ae2e37739dd8bda39d8d75f392000df386e5a983589a6083538ea6934aeac2733c6c251332fbd2b3084f26e302162d52fadddd62f4b55e42e56d78c
  | 7, 2 => 0x869f54da854aac3985153b8b83e7250c82f1e61282cc0a6282b6f85b810f2ecd80784edb7f6d37f47ec521537e47a3a27d2571c67c3dd2c57c0ed9fa7c07db517aa01ea07a928b907948b06f7906da9677dc47c877c91e2d77bdc68e778c805076c3ed9b7663f47f750876f174ae6fdd7478040a7440f92a7218ce7471bb7f2a71755678714e7de370b0a0c86e91ba696e3393ab6e0d97ac6dd67cd66d7c28de6ca6dd456c5e02c56b097ad06a10216166c5e6e066583b976572dcfc651f8019645aa646643eb4a563f957d8637e8cf96327a02c613a456c61183e6c60cd05f56030e5775ff4ce765fe0735d5f60d3935e4211005dafde6d5d4b83655d2b3db4
  | 7, 3 => 0xb19d089eb086883db0123566ae822c95ae1833a4acf18aeeace01a49acc065bfac416f81ac40aedfabd6bf33ab86db3baa29df2ca948fd26a9422881a84185afa62a8586a5b4a9bfa597c972a52e05f9a509083ba4aa9991a3e1545da3d677c6a31dc3559fba51279e7bc60c9cc3c4589c62c0559c0411d49bf3ccec9bd0686b9bac1dca9ac3afa29a6aa62e9a15c99f9989e17b99740857996d166b98ae55239635d4e5957c99819470117e93b9c5b4933b08c0927ef3af90a879718fa704648f61b7f28ea614668e74a6878e388a6c8dee30cf8d52f6a48c98aa0e8c9348248c1589dd8b5c9a278a6e04c789ee2cc187bc61638790d9cd873421ea87221ed2
  | 7, 4 => 0xd8d03f3fd7723c80d6c6f6b4d457ff96d37621bed152fdb6d0a9e880cf100cd1cf0e2d34ce46f076cd83da44ccd50beacb49ad5fca7a6de0ca4df9e1ca2359efc9f58483c9b94266c89695e4c88da8c7c87069aec86f7848c85ce6d2c8014610c7175308c6c389a7c6b423ebc68891d1c54d77d9c4b1675cc491c6d7c425d8ffc2c8fe79c2c4f0a3c25db499c1fe49f7c18341e8c082d04bc01655fbbf786cf1bd6d0bd2bc382ae1bc1a5c9bbc107b1fbb955335bb2e1ab3baba0ca8ba8de402ba009fbdb9fdf3ecb93bd319b930f5ceb7c36f54b7613b03b6f8ca45b66a6b9ab5e3df5cb547d112b539dea9b4103e05b3fe7d45b3d1703eb35e28abb35a815e
  | 7, 5 => 0xff68a53cfeaf796afe9774fafdddf1f6fdc0a1d6fd1d7bb5fd129f1efbc0d4b7fac654aefa2dfefdf9e5893af8e952d0f8b5f872f6c5fc92f6aa6959f6296f7ff396b740f2fb9ca8f1a2f99aef893717ef1b0e3fef02bc46eeb0d825ee49e03fee003029ed934baceca95f2dec06ca44ebbe236eea8a0248ea59ea3de9651ec8e87d8401e73509dee72f8719e483bc65e3620818e20026a9e0fa1a10e00dfe03dea1d9eede838d1dddd8a180dd18a595dcbf8a12db8c78c7db80d1c0db1bfc22d9d5510ad9b10ab3d90e7339d8de5162
  | 8, 0 => 0x56b8ec2d55fb029054027c0653fe6beb53f60a16538e6a2c517147425112b1534d1eaf4c4a15cb9c48d93281481e85df472c527a46e7ef704684d03a45df71c344e5307a4486594744632c9c43a7f968435c7592430d14144288e84742864cbb41969c6d407d0e1e3f6c64f63d45695d3c49f2a23ab6390e3a370f07378dc4de342f10a93332690730f443702fdd99402ee868272aa74149288e9625261c207a23cfe67f23868c2822c346ba1fa1f8e91f928a211ecb828b1b82497a19d725b71865cc4217f2c30416787182164b23bd13c660e9114d56670ffc78670ee2d8550ce3cc6f0b1b6c5409e3a03a073a888705d1d7a6054cf67f02ffd38002bfe943
  | 8, 1 => 0xba35ee45b086883daf2b1cdfae4fc9b5acc48751abd6bf33ab679b95aa29df2caa1e878da62a8586a32d9c5fa2b2cde2a149911da0d9b3009f891ee69d045c129bf3ccec9bb1ecb89acd8e459a0d459997c8c7fc97bdeab193d4c5f590992a8e9085db4f8ebd97ac8ca528878c1589dd87163740868418da8570c2b98505616a82b6f85b814546da80cebec87f6d37f47e7b87917e47a3a27d5144d37aefb5387948b06f76c3ed9b763a561974f87596734d8dd571cbec09717556786f19a0f86e3393ab6dd67cd66c9555146b630e056b259ef1651f8019645aa6466385d7d4617edaf561183e6c5f67557d5d86a70d5d4b83655b01d664590d4e74583358f6
  | 8, 2 => 0xfeaf796afd2fcb94fca923aafac654aef9621830f91974a7f8e952d0f67b6e48f396b740f2676bf9ef1b0e3feea3fa37ebfab00ee9651ec8e8f3333de48981fae2285a58e1e7a3c8def5c2e7dd18a595dcbf8a12dc6ae6d9db9f9401da50ac7cda47dcabd9da8f39d9d5510ad9b10ab3d95cd311d546ffbdd457ff96d2172daad1e4c7f9d1a80a0cd0d9a539d0a7e592ce4410e7ccdadb03ca71204ac89695e4c88da8c7c86f7848c4a619dac476d252c37723b5c23772bec108a87cc0a58946c01655fbbe83e5a8bd7d2e9ebd6d0bd2ba4665a5
  | 9, 0 => 0xc0b2518fb960121ab9311668b8a119d2b2ec1371b2b3d65eb0c0ade7af96d756ae1dc119abd6bf33aaa6dbfaa8b1ad5ea8573803a70a10baa178a6f6a11bdee7a0ee3d9b9f79c3309e7059689df3efb797b894d492af259a8a653b318276a67982113c997948b06f76ebb60d76c3ed9b744b814373f017a17306a372727bea1e70a9787b6eb7552a6e9266a86489b61a620058f4617a4e705fd703e3512c13b54e7ecc2848d83bb83ea5f4523e7e25903e2872193d45695d3a7596c234aab87c33daa8ae2c5d297b28dac08325d3e27a2520867f21d84215215de8a41f594ffd1f2b5da41e9b39e11c6ab42f114d56670b9176870983a2a9054ce95e02853d8d
  | 9, 1 => 0xfffe3a9cf04b31f9ef416068e2dd6e8fddb95d6bdd8af996dcf36382dc224928d5e28135cf81e007ccff5305c8abcd79c787e5cfc66b64d9c0c03c31
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 5, 0 => 0x5
  | 6, 0 => 0xb09060b07060802060106020806090c02020608060706070b080408010c0208060107060c050608060c060106080a0b02080c07060206060c06060207080606080606060908060d05060806
  | 7, 0 => 0x80608060801080008080203030806080c060f03080203020000060200010600010208080907040608020f0303020608070206080402010e0408090e09080808030406060704080301080402070801080006090000080803040202060806030808070608080208080b070902080408080908020808080208060807080b040804
  | 7, 1 => 0x70201010801010808080408080100020806070102080808060c04020909010e07020807080b06030203000808070e08010608080407070404080204030808010603080808080408010303000300080404080208000808060208010e08090007020e08080001000401000609000808080306080c080803030008080008070206
  | 7, 2 => 0x108040809080800080706020e020908020007080201070108000408000108020803070206040702080f080304040003020808020609020104080802020808060308080301030201080100080808060203080d090108000403080201020604080808000301070808080204010008060808060401
  | 8, 0 => 0x302040202040808080800090306020201080101080808020106080403020402040801030800080902020202060002020000030207080302080301040200020302010800020302080801020408020203080002010201040800020302040102020208010404020002080204040600040208020802020203010808080700080800
  | 8, 1 => 0x803040804080204020002020202000800080103040808070203020806080102030702000201030201010008040702020202020208
  | 9, 0 => 0x4010304010000030404000400010104040303000401000004040104010001040004040101040101020002040403000003010400040103040403040402000400000304030003000001040203000104
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 10 0 (CN0 s)
def CN : Nat → Nat
  | 5 => 31
  | 6 => 345
  | 7 => 1230
  | 8 => 857
  | _ => 0
def CH : Nat → Nat → Nat
  | 5, 0 => 0xfdbf19eef9410221f2ed79a9e6325ff2e4b22536d9c25636d87e5701abdb9aa9a14dda05952edbe689eec64e85f0592b831f9f5c81cfd8a77b692a717a252b3c71d3e6d46832631c617ff32c57ab873b542436784d826ee449bce5cc2ba2f6152b08cae325e3be7925bccaa424fa3cdb2376ace21accfba403e05125
  | 6, 0 => 0x347240cd33f647a333dc74e7339346bb3310dcb432db35f432b84a53314513e1308ce4c92fceb1c72f4af0482ed114d22ec11b9e2de9f7fb2de7cdb72c0d7b872a9ade952a7312dc2a6debad287de4402849daaf28236ee526d6479c2684301c25a112b72356727222a8c9ff2291ab0d2144ddd820ba747d1f45fa121e62e0021e3c904a1dc026991d2a02fc1d1e398f1c228d451bc003ce1a2efec01784cbb61651ac3b14181905127b5c7c124370520e00ee030be1c0bf0b1f118c0a65c8010a3172130a05c25609ef985509ea85a109af229e0995bfc607cf84750761262b059db5e404a257890372dba102832f3d0242dd5b01dd737b01910e03014162cd
  | 6, 1 => 0x60911fcd5fc32cd55faf825d5f0b4c545de836e95d85944d5d5730785d0b29895ce4dc775cbf9a645c8bc0f45bee800a5b751e265b63d7f65b3d1a6e5b1369e35975e60b588744f957b33fce569285b75655268455aeb817553fdff1542436785418d247539e035852d61dcf51ecc70450d843194fe091df4f69093d4f4e16e94db8c08c4ccb89e74cbdc92e4bb0edbc4b7c97ce4ad89cd04abd71dc48cf575f4878045b4862ccc64859dfa9483baf2a46379bbb4604d21e43ce54f84248a2014204602c41f2fb404114aed3408ffdf340849491407e887140560e623d3dff9a3bb37dfb3a600d0c392c48fc386d50b4380312aa37dbfd3f36387c1e3562dde0
  | 6, 2 => 0x94ef26359358203892f786d590993ca48f99144e8f03e6478ed97bfa8e1acc708e16afa28d75ba328cbf60618c904ad18c0897978b5dad698a8c7e808a8af3418a7f32f18a03218189c32a16891ba4e5885ebc7688476d5185f1d930851920408393c7bc82b0556282a00bdb8251746f81c9ae2c7fca717e7f4929367efd80e47d72ff457c8adb287c709b6c7ba2b4a57b692a717a776eb779b8766f7974cb3f78b589b277b46d307489f6bc70563be5701c8d0b6f351db66f0d974a6bbe38976b3e069b6b0d041f6a69df1369e0bbf269c909fb696e94a0693572b06843b16668216d57673054056681f22b66583b976655283063a8a00562059a38609903fb
  | 6, 3 => 0xbf7224a4bf43ee6cbe4a5c72bdfd1a4abdf4a8fbbd11a03fbc851e29bb120825babd88c8ba41cda4ba00af6db9c36333b7f5c1b1b7600311b7556607b6471f64b4f86ba5b476ef5eb3ff2209b3a6df90b058bd05b02514adac29605daba03d3cab87a0bcab79a93ea8a6f765a71b1387a671a2f4a6178797a5a0195ca519afdca4ecbd61a4e72155a4e46e94a4b7f33ea45ad539a3045560a28f7d9ca28d22b1a1a478f7a1703c00a116fa6ea09caeb59f7fd5229f2586df9ef794869ea256339e69329f9e6770c39e3002329e0ac01f9dd6e6af9d39a5c59cb07eeb9c36eb119baf90a39b1a96359ab7f9cc9a7beaf498ec089196f9ddd296e4b5d995200ed3
  | 6, 4 => 0xedffca8deda2b3b8ed748618ed34480deceba408eceb62f7ec93c6acec7f710bec4ec13aec06ca44eb0d99a8ea3769e0e9f21d20e742a573e6be62f6e68fa330e637e31ce62f944fe4b22536e455ecfce426dd28e2ef9eb2e2a24307e26d4608e2296fbde18840bbe1468552e0e4754ee070ac9ae042ba41dfa33ac5df819985df465e91dd8210ccdd79ddcbdd6c3adedd6b2169dd17ba47d9b3a5b3d68bc8d6d5c73972d4c63696d442ac90d3145f4cd1e92196d0f84a97d0bbdb32cfb71922ceb0c798cca8d324cc8e0d9cca524ba6c8cbfae0c8a4729ac871f0c9c75c5a2cc73cfeebc525bdddc4b1675cc4529029c39c9a2ac2566b6cc0a641bbc048a69f
  | 6, 5 => 0xff95822dff396ed6fe5cc5fafe13da84fdc995aefb8cf35ffad54eb1fa4b3637fa49ea12f914e751f6b7eceff6adcf6af5c21519f4c8c525f4b601b9f417b825f3e1fe70f2ea101df2482100f1418d5af075af5def7fd0edeec90913ee838c0cee3889d7
  | 7, 0 => 0xe4e958e0e4cc56b0e36b8280df6328a0d2f5e160ce4dc740ce3cc6f0cc413ef0c704ba50c5166af0be709d70bdb0ae30bad90190b84d6450b82101b0b5a489d0b05dc120abebc5f0aa12b5b0a9a706a09cfc6fe0968b22b0927d378090f0a3b090a691c08eda57908dbd88a08c6a0f508bdb3d8089f835908389da8081c0024075b447606a49047069b6fea067cc18506270e0e0625a24e0602db0205ced31705b67dab0592a2fe054cf67f054405520510214b050c987a04d624eb042e079a042a00d2037be67a0359b81c035983490331bad702e41e80027432b7023f085b0221b8ab01b63d2a01a4aa740135bee2011e9ff000e25ca000ddcd6f0015ffa7
  | 7, 1 => 0x1bce63b81b59d7ce1b1d35231a7e00171a5880471a5637a51a0df939193bc456192aafaa18ed01ef18c4d78c18a291c11865cc4217dfe79717ddcb4d17ccffc917c17fc2178261ab16eef1db169c85c11698ed7c1690078d167d681d16683f1b16128c46160e342814df4be3145102861401d78713efd2c313946921135634a5132b4ff313264a7612f1e61612b4d55a12aaf4f212852e4a12499f341226901a12203b9e120e40ce11fec15811e4b08811c5ddb511a90de11193d9ba114a65bb112700f110c6052510ac7246107c7ef4104a32fc100354ba0fb1eb180f9547230f8e0ac50f2b426f0f05eb760ee6922d0ee473b50eda85a10e7f09d50e5ba6aa
  | 7, 2 => 0x2a0e63862a098cb129c25dc129bb60ea2978ea652938d18e28ddd3f128c1fbef28b5100f289e89f3282b210227d59fd827c6226a275c4c422753525226d5d26726592d782649426526447bcb2620a41c261d4d2426025ca625a386a32552870f251837b22506f2982491c70124542356244f4d2f24468cd52426621023f4d7d4239931b022ff81fe22a7b08b22681ef921ff67f021e693d921d41cfc210f8c3820c3ab4d20895c4c203ec9e81fc224cc1f7789e01f25cdf81f1ee8081f1cf2d61f0b327e1dffa24c1de9687c1dbb04a71dadfc491dacd0951d236e931cf1a5321cdafa791cb97eb81cafaa221c97e5171c58d7801c5254391c17f7a31bfbcad4
  | 7, 3 => 0x37a8986a37537c12372bb3a03729dd2936fc4ccc36b5f11f3691029d364490ba36416fa435d959dd35b410453580f4bc352c8fde351f7a9a34fdb1eb34faea3834ee3ccf34ceb639349fbecb343eb9a334317d6b34161da933ca2cd33377ddf6336e697732e3b023322d2d9e31df4c8b3191c35831821ded316d327131113e803079bbe72f8521f32f716b792f699abb2f4b19502f1f1b2f2efa2cad2eccfda72e638c4b2e51762f2e2bdb292df7853b2de700e22de674322d9f42792d89ac232d5b0fc22cfd66822c9cff352c88520f2c5e4db82be7906c2be454702bd37ecd2bc7879a2ba296a02b980f2f2b5de4ef2b3477272b2af4df2aaaf5882a765ac7
  | 7, 4 => 0x4279029e426d8cf542130270420904aa41ba30fa41a51e64418639c1417c9ab841474c64413bd36e40da0ad940928f1b40428601402e45ad3ff23f1d3f6155133f59e0ad3f21a39a3f1e14b03ec289903eb804623e9725b33e71ec903df7931f3d9b76963d9841373d80cc213d3874bf3d2e7b233d2a8eb73d02e1593cf822dd3cd92ebb3cb7b1993c92b8fd3c5ddc023c4ff1603c04a4923c039e273bf2fa783bf0e5103beeb3963bc765ca3bc5081f3bc2b3233b702aba3b633f983b45d1433b34e45c3b053f673af151e63aa3b1ce3a8b8e553a1cb2d239f1c3fe39eeb45839edabcf39b076743958523f39045eaa38b318423827929d380a51e237fd04f5
  | 7, 5 => 0x505c8d754f3b28d64f09bad34e9e04bd4e3926044dc212994db4cd7b4d952f134d7fcdee4d668dc74d30a1fe4d2e096d4cc94c374cc1d6ba4c6293e74be9820d4bdfdafa4bc181984b7c9d144b3726bb4b1f7fd84b0757b34aac41494a75426e4a6c51d54a4b2d7a4a4489634a0fd88e4a0599cc4903667448f6d3f648b017a14855fede47fb898347cc1d0b47c267934770b369475436ec4732b7ea471711e546ae623a469ab6af459ee3a4457cf46f45746afe455ebb3045554c52451b0d83450ee70e44e6b79544e5307a44ae28f14497ffab448087a544496d4a442a14434382612843142991430c0d3a42de6c7e42b5489e42a529d2429d1c9c429122ba
  | 7, 6 => 0x5cd13ee15cc360725caf90475c9abf405c3998815c3363dc5bfa235a5bcb0d815b6fb9ff5b3f9ecd5b17d00b5ad8b17a5ac48b465ac21c945aadc18f5a4dadfe59fb3f9459df13d8596ed72e596d20415956fd3c59209dbe5904639a58f1d5cc58d567e858cf3d2158756c1b58456b5258205ad958086fd657e47b7f57bfe8f957bf5490574bdd0c570f413d56b179fb5675495056552684564620685621c00d5591d8615580904954f61fdc53f5b30b53c805d853a802025375573d532921605316eb9f52f7d40e52f0ce1452d9321552d59bc45263d726525827de523a11385216f6e551bf9d2551b15eb451b00b2351948ad8514462f75124a40550745329
  | 7, 7 => 0x69a7dc0e696130be691a7adc69197363690acb9468faa3d568ef6a52689f3d7d6890166468644d2c68501ef96835c5fd67e5ee8067a899c86771d6bf672c374f67272bc966d9cb8d666ef55d662fc162660eb5296603ed8b6571e633655091906528585e6452863b64449b9963fa91cc633329c262f351cb62d8b46762084d2661e483ee61e06cfb618b8d1e6183a4ec617edaf5612d00be60574fff6056a30f603b59ec5fe189355fc566825fb730c95f9a2ab65f9332ec5f895b0e5f5b68b55f5ac5215f313e015ef26aff5ecb44f25e84fae65e7b0e605e661e175e39482d5de5d6f95dd61e195daf18c35dacee7a5d3b7f2d5d3a23ad5d03433b5cf25c24
  | 7, 8 => 0x7568e79c7515ba2e74f942be74dac38d74c21342749c7aaf746ed9637439c913740ab3bf73e18e7e7353d97673229636731b9c6373142a1172fa5ef872a577ef71f0f53071e5151b7199db9f717ed3b471748b7f712873ec70b0495370919d0f708538877055d3f8700da4516ffe9d5b6f749b8b6f3457116f2631876f08acaf6e85871e6e8385046e3a186e6e18f9066dc5be306d6d8fd56d4107916d3a4e746d32c8786ce542596ca88ff96ca3a4856c9ce4bc6c8d348c6c828a586c7dc5f46c3e17836c17745a6c04116b6be8d1ca6b56d02a6b50af686b422a4b6b1a2fd96b1876a36adf00396acd49ff6ab3345c6a30b7fd6a272aa769f8c6d269cf4923
  | 7, 9 => 0x8489a6e6844149af832d49dd8317731e8281c00f82411a29819e5ce1815eae0f812fb25d8128023681236095811d43a0811a1794810a15ea80ece13d80ea892f80aaef9f809fb5c78085ad8c8051d41c8004847c7fb493327f5d66c37ee7ce4e7eae30a17e9a036f7e587d2a7e13f8eb7d75746e7d2f4b167cfde7837cb8ff357c97b5027c8c2c187c70ae5e7c3249267bfa7e0e7bc69aa87baf2da47b9bda6d7b8692b07b75dc547b33cdf37ab272537aa5a1d37a8aac827a496dd979fe596679a78b187998dc6d7974cb3f795b77667908dfd778bf49dc7825e68a781f596c77feab0277bb15817795734b7778fd747716983d76e0d327760ede747586d2b5
  | 7, 10 => 0x9063fd9990524cef8fef83798fa04ded8f2500868f1594998ee5b1e88ed97bfa8ed1debe8eb209908e6e092a8e6a00ce8d67190a8d4322f68cf1e1cb8ceaf6388ce0ade28cb1b2308b9bdec38b8d889b8b50ffa58b2c11238a99911f8a15d3598a069e218a035c6b89de3b8589db6fc089d3f8ef89a11656898d934f89524c9f8914e9f4890846c988bed82688b9ffd788b0ed84886e060e87efabd487e34e7087d51d9687c161d787a802ad879f9011879c63638781283c8780cf69874bcfc2872f16588718681586fde19086d32ade868f3f2b868418da866fb899866caf3986347226860f7cd485b01f528572b75e8521427a84fe97d784f7133184b2d944
  | 7, 11 => 0x9f97608e9f8d1a229f1050f49f02b1dd9eaae7149e8ebd799e589eb89e2123709df2bf9b9dbb23a39d9be9379d5b29879cfb88759c8a0f2d9c7b9cda9bfc6bd59b837c729b762ab19b1ed38d9b0881979af6efce9a97c7939a38d9b299ec00a19953650b993fa11498a0342e983ad9cf9824bb08981fc82a980c75fa9808540097ff43c397d5c0a0979a21f9978bcfd79783aaa497807bfc9774dfe69741067696d3249796a3c58c95f16fe595e25aea9562922c9507098494bf91059440d7f9943660309432ed5793e43f9c939b066b93856088935d981692d7a51d92d3aa72925c0d30922f239d91bab69a91a9c35a915c1ec690e52bbe90aa696e9089c21c
  | 7, 12 => 0xb04b4684b048584dafa9266dafa2e4f0af48d015af23c091af145a25af05593daf04ddf0aee7603bae460f51ae440e05ae072bc6ae0687e7adcbb5e0ada146d1ad75ea44ad15ecb3acb29569abfb626dabc71d39ab992ae0ab8a8aa6ab679b95ab35c807ab0f19f5ab09071daadc0a84aaa1b4cbaa2cdb4baa1e878da9c2dccca9b7ec58a9a0b542a9631cfda927f429a8d8816ba8d5a24da82d447ca6fee5aca6f542e9a634ebf8a6178797a5b7f960a553d214a5079bf4a4b9c12ba48ab157a4786054a420e51da3fafe1da3b2b2c0a3027bcfa25660bda2298f0da21f5fe5a1cc7126a1aa5981a171824ba148497da107f452a0be2650a07feecda0070ef4
  | 7, 13 => 0xbd87e816bd06b9f1bc7e790dbc5baf89bc29c1cebc234586bc1c46cebc168662bc136dabbc0f05afbb3890f3bb0cff2dbb0a03e3ba8d9a32ba7fb700ba439423ba1bc561b9c611eab9b2c666b978bb80b95ef654b9543a92b8e94367b8e3092eb8caf6b7b849cdeeb82844c7b8216797b7cef8eab77567f3b73ffc5db71bc11eb6bd99fdb65e0a57b5cc445fb57dd52db5488dbfb52880a7b50539a1b4e7529db4dfa071b4b33f17b47b8c54b4523f4fb438568cb416ad15b36acf34b3532b79b2abf52fb2a1b58eb28962d5b25f9d6cb21643fcb1fbf71ab1e0df98b1dc4779b1bb6d2db1a56189b1a1542fb18e53bbb0f1a7e7b0d9838cb0b2f7feb073ff4a
  | 7, 14 => 0xcb13c18ecaf13afacab76b94ca954642ca7df4cbca1c6bf9c9eb68aec9c22eadc9b33699c96454b9c8b2d089c87f1203c7fcd691c7be655ec7408675c6e363fec612f2ebc5ee3acbc5b4af63c56a8c1fc553cd64c54b57d9c51c9813c51b0e3cc4f4a615c4f0e27ec4f032aec4c77760c4c4d7ffc476d252c3cbcdc1c3a3bb35c38661cfc2eb9a07c2bda7aec2abf630c2a6b18ac28382d2c27c6b1fc249a176c24147aac2054e84c1a5d27dc17c9395c118f0f9c1023a24c0a71eb2c053540ac04f8b2fc04875eac022b36dbffcfe39bfce65c2bfac0c0abf43ee6cbefda17dbecfaf24bea8085abe96c556be77aeb3be6975f4be125171bdb58962bda6c86d
  | 7, 15 => 0xdad0fef0da19e842d9dacc61d9acda08d99ddbb2d995d947d9624394d94bf25cd91cb645d8cd8526d867be53d83d0286d7e89fe5d7a596fad6ec3093d68860d0d605d955d603c5ded5f9bc95d5cac0e3d57d4520d546ffbdd53ac44dd52fd8b1d469fc52d44f09fcd3ed30add3d1cc76d390127cd37ed664d2df30abd26ef353d25e374dd2172daad1bea867d1b51c6cd1823e9ed1770500d14be50ad1318c83d10c0c37d0c90df1d08cf550cfef7385cf85bdeccf4d80d9cee0da52ce274072cdec89aacdaccc57cd5a5862cd4b8553cd0fa541ccc9b386ccbfd79accabdfe1cca464c3cc6d0a8dcc4594eecc3081d1cc017afbcbf93c8ccbdbec6bcb6e7470
  | 7, 16 => 0xe4f9e8c7e4cdf22fe4af48bde4aac194e48e4e05e48981fae4695024e45f6767e442d38ce431cedfe421904ae409b5eee35c3ce7e3050f54e24da3c1e240f924e240081ae23b3261e2383e5ce2106f9ae1c5aea9e1a8b207e18ada6de1791443e1601119e14e869be1265f68e11e48ace0d7b367e0555edee02755ebdfc11602dfa9ce41dfa202e3df99b416df9323a9df12124fdf0d792cdf02ffe6dea06479de97f472de97925cde839bf0de6ab9edde4a45d2de23fac8de227710de1c0007de07e0ccdd9a1a52dd99e0f1dd59e6acdd4bfc0add17ee41dd0d0fdfdd043e71dce9badddc917e68dc59be79dc568a91dc109848db74a3b4daec9964dad217e3
  | 7, 17 => 0xf0d06535f09491ebf08f00aff086db28f047a825efeb4ff7ef8db772ef4eb288ef34e901ef2c34e0eea44343ee911ecaee6e2630ee5c2512ee4dcc2aee330985ee329aacee231da8ede81bacedd27e6fedbcabb6ed1f2274ecedfe06ecc4ef80ec6b7c8bec6a85c2ec44d11fec1b8a82ebf16c5eeb75bfd4eb3f94b4ead6e70bead1bfdcea78593fea6d5ae3ea54f4fbea4984c5ea300679ea16fe23e998fd80e97292c7e95c8499e9428688e9289e90e912db98e8fc84b7e8f29c96e8e1b86fe8874314e87c8d38e8777a84e875d56be83c1781e818a351e7e38176e75de0e2e73a1bcbe72f75c1e6dea5dfe699d5d6e65582bee5c59f6ae5884c84e54577f4
  | 7, 18 => 0xfd0a64abfcf51106fca95471fc1818d1fbe228c4fb7ce7ebfb6ac93cfb252266fb0033e4fafe8a82fadd5cc7fa986e0dfa8f2bf2fa815d57fa5307e6fa24a411f9e83394f9c6b1daf9901d2bf98d4c9af98d0dfdf9690c3df9547e42f9409de9f910d00cf8ffa1f4f8e96a58f8d124e3f8bbf3a3f8a9ee7df8826a54f7c6e5c1f794c610f6ee0e26f6cf8b76f6a2382cf6824218f664eb05f5f5c17bf5add7ebf58c351ef580ca1df56388b5f4f71326f4e65040f4be5dbff4be2692f45bc570f4426eb3f33439abf31c1e82f2d9ebc5f2b31d86f2a50de8f27c2bb0f26a2457f2618d6cf21bd5a9f2111632f1a7b69df1a1f6d0f1281b1ff0f0b8f8f0d95c78
  | 7, 19 => 0xffddc543ff77190aff761db8ff7470aeff0dba57ff07d5abfee9b75afee5eb95fed211effe14464afdaedc6afdad2f62fd75aa48fd1745b7
  | 8, 0 => 0xfafd1ac0fa1e70a0f7e5d6c0f5812230f47dddc0e8802550e4e958e0e2b5ce60dabebc90d9a03db0d8668300d7930570d59f28a0cfe88e80cc98dfc0cc413ef0c7fe3eb0c1514b90bb9c8780bb49b700b94d9f60b8a5b650b82101b0b1d9d520abebc5f0a6206fb09f2774109b7e9c209ac8ef409782090091ddd060880343e0872499c084fa7950837b96e0820abe30800285307edf46007c8251207c5c67107a0d7ef0790af4d07500eda070a832206589e030625a24e056b675e03f9cbe203cb680d03881a2a035d4f530333d1f902e41e800262b79f01f5e65201dba8ec01a36bd9018c296801200a270117e1d200f10e7500813c21006111df001afdb0
  | 8, 1 => 0x24b35b8f24a43301248af42e241ea79c23e241352385955f2373ac7822cbdf862205913d209755d31f7919c71f13afe71e7f34001e7175821e55530f1dd132161dbc3db21da279421d241a961ca13b811beee8801b8517c01b4982e81b1fade01a19be9d1986d5391960b5c519534df9192b7f3718d5cbc01867dd9f182eda2f179b62f41741d814173e2b2b168ba07016777b4a162571c415f70def1584b9ee1581cedf155f77db155afa54152b9e6b1522f06914bf4b12149ad310148e5d8113f92b6a13ee295b13caf5591395af55138c569f132b4ff3125721b6123e5b3611bd217b11588bd3114df49110f28aef106bc586100916c00ffa27540fd25ee2
  | 8, 2 => 0x3a2a502e39fcaee238883477386a4ef5380b2a06377ecaaf37207a6c370260fe3701587535af300b34bb08223496a84d347bd1c53412117931d1e4fe31cd040a315567293124f11a31143f5530c7061b3043e1662fc411202fb198e82e3bc3d32e0d614c2de558622d9f42792d6753f62d5a05512ca8f2e62ca2b5332c7a8f112c4dbae32be2f8fd2bd96d5c2bbd96e12b8d57d52b11dea32afcc58c2a9d669c2a8dee222a11c0e729e852652997677629944c96294ecf25292c25cf2902f92b290057ba28c5ac0428b74652284a46e727ad74c12792cecf27770e942767ae7f2764dc7626d4b8b3263ea91325795578254af1a3251837b224d216b024c32543
  | 8, 3 => 0x49cf1f2e49b96ac04964aed1493fc04f491389ab48a5489d4834d0f14818b08c47be32a947a94f48479e571b472c326046df732446b7a4624661f0eb45e9679345b420ac4599be74457ee82f456bcc1b4559ab51450bf10244dba8584422c39b440c840843fd8ae043b54d41437f501542e1a9f842af159442ab22a641efb70241c01ea54165a94a40da0ad9401882013fdc618c3f9b40bf3f3ac7743f370fc13e91b6a73e7b1a443e30f5e33e1e52353e0aa3ba3df0b0e93db8fdb73cf3262d3ce4374e3cadb29b3c7c367e3c56942b3c3c0da63c27a8173c1427803bc3cc0b3b72ccb63b6fcb3a3b45d1433af663053af151e63a87183d3a845d8a3a580264
  | 8, 4 => 0x5dc2af7f5db4c4dd5d8c9ad85d844c0b5d2400205cbe96405aeb26f35a810c025a44566e5a1b172559e140c259cead7859c9fcfd59c0c2d6596592875873382457c5645657a5b58f579771fd57655f9157074e3a56d929ea56b84afa568b9fe556628568563389b655a38d20559687bf54fb558c54d6c888543c7ed953516e94529d97f2526e8361523f87af51af8b1951990fb45174d30851439ab65111ba8a4fee86bf4fb649ac4f4367a24f1b2efa4ef8daea4eedd0174e9d71484dc321354db3fd194d2943c54d0ce16b4cc9b4ed4cc1d6ba4c994aa44c1450f14bfa84b84bc247a54b98b9254b97644c4b60f4f64b56d2224b2034674a45359a49dd9a87
  | 8, 5 => 0x72e4f48372e1ab1b7265ee7b7199db9f70c7d790709ab8907076bd09704d7e1f6f18aa2f6ef0f27c6ee73b476e48e5786e1af31f6d93da876d8acf5c6d5f93ad6d5c7f416d2959dc6d16ccd56ce07e8c6cc334ec6c9425186c8453556c828a586c46bd076bde9fa96b5a49aa6a39d7c66a01c65369b3cd4269983a226970aa316951bd3e691de0b16890514e682e0b39681082b56719480a66eb55b1665b31ee662c84f4660e1d1f660dc44c65ae40c7657fc785651294d864e662c964c93dd464be9407648a591d6468e090642aac3c636dd82762dfd260620c093d61ba3ec06146d4dc60f6a78560b6053960965716603cebe25f79d6205eef0a355e3ff6d3
  | 8, 6 => 0x8665ec5f863e1d9d8617725a85e86a26855435a183c71584839a4df783656c88835f0705830491aa82ca3e2982358ecf81b76a6181822f41814450117fdfe1dd7f33e71b7f2534df7efd6c6d7ecd2ebb7cf26da07c8500157c6ab0897c2996737c26009d7c22d34f7bebdfd67bc9388e7b9b97427b9aa0bb7b4cbef67b4022447b3d505e7b2c66e17abbd0b97ab568f07a8d6ce47a271cd779f5d6d079aed54a7924bc76791db30f78e2f74d78a1495e77ca55fe776c822c771208ab76f0d3fc76ea39e976cbe57a76c7ceb276a8603476996add76948672760ffba87601d4c975b17db67530ba6f74c377f574bf3a9f74bc092a741d218874101bfa73dd5bb7
  | 8, 7 => 0x9b6d95d89b5fab369b502b519ae8a46c9a8befba9a6c6d4d9a323ee29a30861899e662c9994711e9990cabe398ec0bc298bc58959843183c97c7d133978bcfd797795e7796e9e6f296648b7e963ec43595b797be94f7c3a194d2d51f94cf073e944f08af940d6bc193de700f938da29e937de1969369c853934e7379929eba039235a16e909833c59064e0a88f69df478e6716e98d996d188d9589cd8d6dbb0b8d6130058d4da5478d1807948c43d3b68c34fed88b6e078e8aca24918ab0254b8a99911f8a4abb6b8a4430fd89a5e6248998280e8967611e89652c3d8959a34088cb1ac0884fd1af8840c76b87babce7879c63638756e0db86eae08186812274
  | 8, 8 => 0xb0eb2c30b0a5a9a8b090b6d5b08fdadcb069e3ebaf57ca66af438f8caf3001f4af265faaaf04ddf0aec6995eae56eaf8ad56a5b7acb7959cac5c2bfaac49ae27ab72b7cbab4ccc7daae7fe77aaa1b4cbaa5bc7aeaa2f39aea9c05101a9b225c8a9825739a9555db9a93a467da927bc6da9158cd4a90ae9aea8b714f0a893e9d5a851ab10a7f1499ca7b34202a7acacaca7a8506da796fbf0a7236983a6fe7b01a6a9d83aa69fa804a6954b0aa68615f7a62d6e89a49fe7cea3592720a29213f0a24f5caca2353f76a1cc7126a17579a8a118be80a0d69659a01ba9309ff213a69f87b0db9ee048ed9e5b5aa59d6e61a39d2c24849d00adea9cf5ca739b93aed4
  | 8, 9 => 0xc19099c8c16b7f99c16a953ac10dfcbcc0da98a4c0bb8184bf990df6bee253c1bedab563beabae1abe605bf2be2ef7c6bdf9034bbda6eaa5bd8ac836bd81fc23bcc505f5bc5bc34bbc2dd0f2bc161092bc0b7950bbb00faebb9dad2fbb259243bb230cb4bb0cff2dbaed5530bae6b35cbae2bad2bac69b7fba7d50f2ba6c59ebba3be22bb96d277db9543a92b91092d8b8fa2cb9b8ef9411b8697088b867c144b866b712b8603facb839ceebb838533db7d94c4db7d05628b7cef8eab7a9ab28b7a0bd29b73e5cc2b6cfa2cfb6774d37b6573febb6525eb5b6328bddb5792576b490bac1b4554d21b3794b95b2e05accb2db339db1b4c4c8b16c9ec9b0efee6f
  | 8, 10 => 0xd1663bf4d165de31d10c0c37d100d214d0e74a71d0e54c4bd0dd1bfcd0d014b6d0c72799d0a8f71ad02eebb3d024a92dcfd7bbb4cfc164a1cf43f5c5cf1f99f2cef21bd5cea4e3abce97a67acdec89aacdd6ebb0cdb929c3cd4a7f31cd1e13adccffabd8cce919f5cb256495cb1b39f3caf88ba0caf13afacabaef4cca369e86ca02b4b7c9eeba0fc9d134a6c95f9cc9c8f9bb03c8ebd061c83845eac7be655ec7b9156dc75c4d5ec72eac12c5dd5f12c5dd33d1c5db4b88c5ba31a7c5b38316c5910973c56b9ac2c4b0c7dfc4345e2ec3e80b11c3a08ce4c33b16bec305a578c2dfad1cc2d655c8c2d14f8ac27c6b1fc222f9cdc1f638edc1e931cac19990ec
  | 8, 11 => 0xe6305175e5f2dc3de5daaf06e5c47868e5b3e7c4e52ce254e5227bfee45bc7fae430fc50e3b208cae312f053e1e6acffe1cd3da6e19ebb15e11dc1b7e0c34c5ce00f8762dffa4305dfa08091df788ce1df762513df7184dfdee18849de1c0007ddbbba55dd329734dc0b4b48dba867a0db9e58a7db97598edb8098dedb4d9aabdb2ae567daab9443daa50db4da6f1da7d9e4bb4fd98b7f65d987f340d95a51f4d954d0acd94c65f0d92c81e8d8f444d5d8d75dc6d7e5d789d7bb5ed9d7b46599d78c96d7d7780a10d736e360d7011c5ed6dc6dc1d6600410d653daa4d5d745cdd538d1d7d45fe145d45e2f90d3d1cc76d3840809d2ec285fd225333ed1ad2bca
  | 8, 12 => 0xf91e65e8f8e5752af884b0cbf880a5f4f81c697ff7db48b2f7a142d9f77bcf3bf77adf3af756cf63f746cd7ef7180dd6f6f9d218f6eb14ecf679ff84f5f9a635f5ddb926f5c24e7ef4175a27f3db9d38f33fc17cf266d407f1eb84d2f1cc2673f19d2ac1f141ca3df10d2e2bf100df39f071a56bf0683c71f0173010f00b7462efddd316efdcb66aef68487aeeec3bf0eeca08c7ee6958abee39b046ee2e8703edc85446ed5feee3ece38532ecabd350ec3a78e2eb813f76eb5827caeb3f94b4eb1feab7eb16ed61ea3a84fce9b7922ce9389f03e92cc240e8dbd6f4e8ae35a8e802ebafe78d3d6fe739bb3de700aaa8e6f2c006e6a82a4fe689d572e63ed02e
  | 8, 13 => 0xfff3fa28ffcde026ffb04362ff02cc42fed77932fe866cd1fe7cc1befd982761fd75aa48fd0d5694fcd97731fc859bbcfc22efacfc0b424bfb0eca3bfae87f78faac0b7efa88bfb7fa73ce6bfa4f5290fa06a9a4f9d8b74bf9967175f9489388f92c508a
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 5, 0 => 0x1d905c163022699f040114044545d64015400855d904c12401001d904c123010019f04011301289d904c12404289d904c12404000dd050153020019f040113010019504011301001d905c163020019f050153020019f040113010019f040113012899f04011404000dd050153020019f0401130100011640153010449d640154040019f040113012899f04011404044dd640154030019f050153020449d640154042699f04011404001d904c1230167d95040114010019f040113010019f04011301044dd64015403
  | 6, 0 => 0x1d904c12304001d904c1230400000000411080019f040113010009e065153040019f04011301001d504011303001d904c123010000000041108000dd05015302001d904c12301000dd04011303001d904c12301001d904c1230400000164172000019f04011304001d904c1230400011164173000009d04011304000000009210800011640153040009d640153040011564015304001d904c123040009d040113000009e06517304001d904c123010019f04011304001d904c12301001d904c12301001d905c163020009a04011300
  | 6, 1 => 0x115640153040009a04011304001d904c123040009d040113000009d640153030000036414202001d904c123000009e06517304001d904c12301000dd040113030009d04011300001d904c12301000dd64015304001d904c1230000000368152020009d040113040009d04011300001d904c12304001d904c12304001d904c12301000dd64015303001d904c12304001d904c1230100000000921080009d04011304000de06517303000dd040113030009d04011304001d904c12300001d904c12304001d904c12300000dd05015302
  | 6, 2 => 0x19f04011303001d904c1230000000040112010009d040113040009d04011304001d904c123010019f040113040001164015301001d904c12304001d905c16302001d904c12301001d904c12301001d904c123010009d040113000009d040113040019f040113030009d16410303000006584120200000164102000001116417301000dd04011303001d904c123040000036815202001d504011304001d504011301000dd05015302001d904c12304001d904c123030009d0401130000000368152020009d640153040009d04011304
  | 6, 3 => 0x9d04011300000000009210800195040113010009d04011304001d904c12304001d904c12301001d904c1230000000040112010019f04011303001d904c123000019f04011304001d904c12303001d904c12303000dd6401530400000164102040009d16417303001d904c12303001d904c12300001d904c1230000011164173010000016410200001d904c1230400115640153030019f040113010000036815202001d904c1230000000164142020009d040113040019f0401130100115640153040000065411201001d904c12304
  | 6, 4 => 0x19f04011301001d5040113040000036815202000000401120100000040112010009d04011304000dd040113030009e064123040019f050153020009d164103010005d0401130100000368152020005d640153000009d04011300001d904c123030009d0401130400000050152020011564015304001d504011300001d50401130400000040112010009d040113040009d0401130400000000921080000004011201001156401530400011164173030019f04011304001d904c1230100000368152020009d040113040009a04011304
  | 6, 5 => 0x681120100011640153010019f040113000009d040113040000000092108000dd0401130300000040112010019f040113040009d040113000005d64015304001d904c123040019f040113010009d04011304001d904c123030005d04011301001d904c123040009d1641730100011164173030009d04011304000000401120400000164172040009d164103030019f04011300001d904c12301000dd04011303001d904c123000001164015301001d904c123040009d04011304001d904c123040001164015303001d904c12304
  | 6, 6 => 0x1d904c1230300011640153010019f0401130100000040112010005d640153030005d64015304001d904c123040000004011204001d904c1230000000000921080005d040113000009a04011304001d904c12304001d904c12300001d904c123000009d040113000000016414202001d904c12301000dd040113030009d040113000009d04011304000dd040113030000004011201001d904c123040000026414202000000401120100000050152020005d0401130300011640153000009d040113040009d164173010000026417202
  | 6, 7 => 0x164102040000016417200001d904c123040005d04011303001d904c12304001d905c163020000000092108001d904c123030019f04011304001d904c12300000dd05015302001d904c12304000001641720200000000851060000005015202000da04011303001d504011300001d904c123040000016410204001d904c12300000dd04011303000dd04011303001d904c12300001d904c1230400011164173010009d04011300001d904c123030009d1641030100011640153040009e06412304001d904c123040019f04011301
  | 6, 8 => 0x368152020009d04011304000de06517303001d904c1230000000000921080019f050153020000036815202001d904c123000019f04011301000dd040113030009d0401130000011640153040000000092108001d904c12303001d50401130100000054142020000000014102000dd04011303001d904c1230400000000921080009d16417303001d904c12304001d50401130400000368152020009d0401130000011640153030019f040113040019f040113000009d04011304001d904c12301001d904c123010009d04011304
  | 6, 9 => 0x19f04011300001d904c123000009d040113000009d64015303001d904c123010009d0401130400000164172040019f04011301001d904c12303001d904c1230400000164172040005d64015303000dd040113030000026414202001d5040113010009d04011304000dd040113030000004011201001d904c12301001d904c12304001d904c123030009d04011300001d904c12303000dd6401530300000040112010000026441202001d904c12304001d904c123030009d040113000009d04011300001d904c123010005d04011301
  | 6, 10 => 0x9d040113040019f04011303000dd05015302001d904c123000009d040113000009d04011300000dd0501530200000368152020011564015300001d905c16302001d904c12300001d5040113030009d0401130400000164142020011564015301001d904c123040001164015303000dd04011303001d904c12300001d905c16302001d904c123000009e06515304001d905c16302001d904c12303001d904c12303
  | 7, 0 => 0x3641020000000264102030000004c12201000001641020400000164102040000006412200000001641720400000064122030000000041102000002681120000000000101040000026414202000002641720300000268112040000004c122000000026410204000006541020400000368112030000004011204000001641720000000000411020000060c112000000000010100000000691520100000000811020000045d152040000026410200000003641020300000264102040000004c1220400000368152020000065410201
  | 7, 1 => 0x64122040000026417201000000001010100000364102000000004c122000000065410201000001641020400000000111010000065c1220400000000141020000004c1220400000654102030000004011203000006481720400000064122010000065c1120400000069152040000060c112040000004c1220300000264102040000065c11201000006541020300000264102000000005515204000003681520200000054132040000004c122040000005c162020000004c122010000004c1220100000368112030000026811204
  | 7, 2 => 0x641220000000054132000000000041102000000401120300000364102030000064c152010000036811203000000001010300000264102000000065c1120400000364102040000005411201000002681120000000364102040000016410203000000001510200000164142020000046414202000006541220400000040112010000004c1220100000654102040000004c12204000006541020000000065152010000000081102000000001710200000000101040000016417201000000651520100000164172010000036410203
  | 7, 3 => 0x4c12204000001641720300000065172040000026811200000000401120100000368152020000016417204000000001010000000264102030000036414202000003641020000000000151020000036410204000000401120100000268112040000005015202000000401120400000268112040000000010104000000651720300000368112030000026410200000001641020400000364142020000004c122040000026811200000006541220000000648172010000004c12200000002641020400000264102040000026417201
  | 7, 4 => 0x54112010000036811203000002641720100000164102000000036410204000006541020100000054112030000065c122030000065410204000002641020300000164102010000065c1120000000000151020000004c1220100000654102040000016417201000000401120400000000171020000004c122010000004c12200000000541120100000065172000000004c122000000006517203000003681520200000264172010000065410201000006541020400000364102040000004c1220300000054112010000004011204
  | 7, 5 => 0x65c1120300000264102040000065412203000000001710000000164102040000004011203000000641220400000000101030000004011200000001641720400000654102030000026410201000000004110200000640152010000006412201000002641020100000040112040000026811204000001641720400000000151020000065410200000006541020300000000111010000004c1220100000064122010000005411204000002641020000000065172030000026417201000006441720000000164172010000016417204
  | 7, 6 => 0x2641020400000055152040000004c1220300000065152040000005c162020000016410203000001641020100000040112040000045d15203000001641720400000268112040000026811204000000001410200000164172000000006412204000001641720100000000811020000004011200000006541020400000164102040000026417201000001641720000000268112040000064c15201000001641020400000644172010000064c152030000016410201000000001710000000040112000000065c112040000000015102
  | 7, 7 => 0x6915204000001641020000000164142020000004c122030000005411201000002641020300000264102010000026410201000000001110100000069152000000005413204000003641020000000654122000000016417201000001641720400000364102040000065c12200000002641720300000000151020000026417203000000541320100000000411020000005015202000001641720100000164102030000016410200000004641420200000264142020000065413204000002641020100000040112000000016410200
  | 7, 8 => 0x4c12204000002681120400000040112010000026417201000001641720400000164172000000004011203000006541020000000164102030000016410204000000651720400000654102000000005c11200000006481720300000000171040000060c112030000065410201000002641020300000064122040000006517204000001641720000000054132010000005c1120400000040112030000065c112030000016414202000006541020300000654102040000064015200000006481720400000364102040000065c11204
  | 7, 9 => 0x164102010000065410204000003641020100000264172010000065410203000006441720100000268112040000005515200000002641420200000054112030000060c11201000002641020400000065152040000004c1220400000040112040000004c122040000016417200000000001710400000264102000000026414202000006541120100000040112010000065410200000006541020300000000171040000026410204000002681120000000040112040000016417201000000001010100000268112000000004011201
  | 7, 10 => 0x10101000002641020400000364102040000026410204000003641020400000065172010000016417200000000651520100000000101010000065c1120400000164172030000004c1220100000654102030000000011101000000541120300000040112040000016417203000000401120400000000141020000000011101000001641020000000268112040000016417204000003641020000000000161020000004c12200000002681120000000164102010000004c12204000001641720400000054112010000000014102
  | 7, 11 => 0x16410203000002641020000000364102040000065c122000000026811204000002641020000000000811020000045d15201000000541320100000654122040000004011201000001641720100000464142020000060c112040000064c15204000002681120400000000141020000004c1220300000065172040000065c11203000001641720400000040112010000065413201000002641020100000364102000000026410204000004641420200000264102010000064417203000001641020100000654102000000006517201
  | 7, 12 => 0x5413203000006481720300000654102000000064c15204000000401120100000164102000000026811204000000691520000000364102010000006412204000000551520400000164172000000005515204000002681120400000164172000000026811200000001641020100000268112000000016417203000001641720100000654132010000016410204000002641020400000040112010000065413200000002681120000000644172010000026811200000006441720300000654102040000005c112010000065410200
  | 7, 13 => 0x6541320300000368112030000045d152040000004c1220400000065172010000036811203000000401120000000040112030000004011204000006541020300000654102040000036815202000001641020100000654102040000026410201000001641020000000040112000000000014102000000001510200000164172000000026417201000000541320100000264102040000004011204000003641020300000654102010000004011204000003641020300000164102010000045d1520300000000141020000026417203
  | 7, 14 => 0x16410204000001641020000000040112010000016410201000006541020400000640152010000000092108000002641020400000054112000000016410200000002641720100000264102010000064c1520000000065152040000004c122000000004c122000000026417203000002641720100000000161020000004c12201000000004110200000164172040000065413204000001641720400000364102040000064015203000000401120000000164172000000064c15204000001641020000000164102040000026811204
  | 7, 15 => 0x40112040000016417200000002641020100000164102010000004c12203000001641720000000055152010000004011200000001641720300000054112040000026410204000000551520000000040112010000000010104000001641020100000264102000000005c1120100000054112010000016410204000003641020100000368112030000004c1220400000654102040000004c12203000000401120400000000111010000026811204000006541320100000040112010000004c1220400000040112040000004c12200
  | 7, 16 => 0x164102000000026811204000006541320300000000151020000065410203000000401120000000054112000000065410200000001641720100000065152040000026417201000002641020000000654102040000004c122000000060c112030000004c12203000002681120400000264142020000004c12204000002641720100000000171020000036811203000000401120100000268112000000065410204000002641720300000065172040000064c152030000006517203000001641720100000164172000000000017102
  | 7, 17 => 0x65410201000006441720300000364102000000004c1220400000000151020000036410201000003641020400000065172010000004c122000000004011204000001641020000000040112030000000010104000002681120400000364102000000016410204000003641020400000640152010000060c1120100000368112030000036410204000001641020100000264102010000026811200000000001610200000164102040000004c1220400000164102000000000092108000000008110200000264102040000026410201
  | 7, 18 => 0x264102000000064c1520400000654102010000036410201000006541020000000364102030000016417203000001641720400000000151020000004c12203000000401120400000164102040000004c1220000000364102010000005c112040000065c112010000000010101000001641020300000268112040000036410200000001641020300000264102010000065410203000000651720400000050152020000006515203000000001010000000640152000000005c112030000006d1520000000164172010000026410204
  | 7, 19 => 0x654132040000036410201000000401120400000364102000000026410204000006481720000000364102000000016410204000002641020300000164102010000065410204000002681120000000000101040000004c1220100000040112010000026417201000003681120300000264102030000026811200000002681120400000000411020000036811203000002641020300000054132040000004c1220400000654102000000004c1220400000654102040000005c16202000002641020000000040112030000016417201
  | 7, 20 => 0x65c112010000004c1220400000264102010000064015200000001641020400000040112030000016410200000002641720100000268112040000006915201000000651520100000040112010000060c11201000000401120400000040112000000064417204000002641720300000054112030000004011200000001641020100000069152030000045d152040000026811204000003641020000000364102040000004c12203000003681120300000040112040000000017100000006401520400000055152010000065413203
  | 7, 21 => 0x401120400000000161020000000010101000006541020300000000151020000065410200000003641020300000040112010000036811203000003641020300000164102010000026410201000001641020000000654102000000004c12204000000008110200000364102040000000010103000000641220100000040112010000065410203000006541020100000064122040000065410204000002641020000000040112040000064c152040000045d152000000065410200000000401120000000164172040000045d15204
  | 7, 22 => 0x164172030000004c1220400000040112030000060c1120300000064122040000016410204000000401120000000040112040000065c1220100000040112030000016417200000000001410200000654132040000005411204000006541020300000364102010000006915203000003641020400000364102010000000015102000006541020000000000141020000000016102000003681120300000644172040000016410204000001641720100000000151020000004c12203000006541020400000164102040000065410204
  | 7, 23 => 0x4c12201000002641020300000654102010000064817201000006541020100000000171000000000092108000001641020100000164102000000000041102000000541320300000164102000000026417203000001641020300000368152020000045d152040000065c1220300000055152030000036410201000003641020000000000171000000005c112030000026417201000003641020100000654122010000065410204000000001610200000040112010000064417204000006441720100000040112000000016417204
  | 7, 24 => 0x268112000000004c122000000036410204000002641020000000000171040000036811203000000001710200000654102040000064817204000003641020400000268112040000026410201000000001610200000000101000000004c122040000004c1220300000264172030000026410203000000551520100000640152030000036410204000006441720400000264102040000004c1220100000064122010000004c1220400000164172040000004c122030000026811204000002641720300000364102000000004c12201
  | 7, 25 => 0x1641720300000164172040000016410203000000001010300000654102010000036811203000000001110100000045172010000060c112010000004c12203000001641720000000000141020000004c122040000004c1220000000164172030000016417203000000009210800000268112000000004c122030000065410201000001641720000000164172000000005413204000000001410200000364102030000036410200000001641720100000164102040000060c112040000064c1520000000000171020000004011203
  | 7, 26 => 0x26811200000003641020400000055152000000005c1120000000164172030000005c1620200000648172010000064817200000003681520200000654132040000004c1220400000654102010000065c122040000065413203000000501520200000364102030000004c1220000000654122010000064c152010000065c1120000000654102030000004c122000000026811204000000691520400000054132040000005c162020000064015204000001641720300000364142020000004c1220000000164102010000036410200
  | 7, 27 => 0x65410204000000401120400000640152030000006412201000003641020400000000171020000005c112010000046414202000006541020000000264102040000005c112010000060c1120300000654102040000065410204000000401120400000264172030000016417204000001641720400000040112040000005c1620200000000171000000006412201000000551520400000000811020000016417200000002641020100000040112010000005c112040000006412201000006441720400000264102030000004c12200
  | 7, 28 => 0x5413200000002681120000000268112000000065c122040000004c122010000005c11200000000641220300000040112030000004c122010000065413204000001641020400000264102000000000015102000003641020300000040112000000004011200000000691520100000164172000000065c12201000002681120400000040112010000045d15201000001641720000000264102000000026410200000000001710200000264172030000004c122000000000017102000006541020000000654102010000005c11204
  | 7, 29 => 0x16417203000000641220400000654102000000004c1220400000040112030000016417204000001641020000000055152040000000041102000000401120100000368112030000036410203000001641020400000064122030000065410204000001641720000000040112030000005c1120400000164102010000026811200000000651520000000654102010000026410204000000551520300000648172030000065410204000003681120300000644172040000036410203000001641720400000364102010000065410201
  | 7, 30 => 0x64122010000045d152040000065413201000001641420200000000101000000036410203000000001610200000268112040000006412201000000001510200000065152040000026811200000006541020000000654102040000006517200000000541120400000064122030000004011200000006541020100000264102010000064015204000002641720300000040112000000065410201000000001510200000368112030000004c1220400000654102000000026410200000001641020300000264102010000006515201
  | 7, 31 => 0x6515203000002641020000000040112000000004011200000000691520100000000111010000036414202000002641420200000040112010000036410201000006541220100000268112040000004c12201000000401120100000040112040000016417204000003641020400000040112040000065410204000006541020300000164142020000000017104000006541020300000000151020000045d15200000002641020400000654102000000060c11200000002641020300000364102040000004c122010000064015203
  | 7, 32 => 0x4c122000000004011203000000401120100000164102000000000010103000003641020400000164102010000004c12204000006541020400000654122040000026811204000000001610200000364102030000004c1220400000264102040000060c112040000026811200000006541120100000164172030000065410201000006541020400000164172040000016417201000003641020000000364142020000006412201000000401120000000264102000000016410203000002641720100000000171040000000011101
  | 7, 33 => 0x6515200000004641420200000054112040000005413204000000001710200000264102040000016410204000006401520400000000151020000065c1120300000654102000000065412204000000401120300000654102010000006412203000000651720100000164102000000005c112010000036811203000002681120400000164102030000004c12200000006441720300000000161020000065c1220300000000151020000005c112040000004c122040000036815202000000401120400000164172040000016410200
  | 7, 34 => 0x4c122040000006515204000003641020100000264172030000005c1120400000264172010000065412203000006541020000000164172010000026410203000001641020300000000151020000005515204000006541220100000000151020000004c122010000004c12204000002641020400000000921080000064817203000006401520400000268112000000045d152040000006d152040000004c122010000036410201000000401120000000264102010000004011204000002641720300000164102030000065410204
  | 7, 35 => 0x364102030000064c15201000001641720400000654102000000000010103000003641020400000164172040000065c122040000004c12201000000401120400000264172030000004011201000001641720000000040112000000004c1220000000648172010000036410200000002641020400000000171040000016410204000002641020300000264102030000064415201000001641020000000000921080000026811204000001641720100000654102040000000016102000000401120100000064122030000004c12204
  | 7, 36 => 0x92108000000551520000000654132000000005515201000000651720100000055152040000064c15204000001641020300000065152010000065412204000000641220400000040112000000000081102000003681120300000164102000000000010100000001641020000000654122040000004c12200000003641020000000040112010000036414202000006541020400000054112040000000081102000003641020100000268112040000064817204000000401120300000640152030000004c122010000026410203
  | 7, 37 => 0x40112040000004c12201000001641020400000040112000000005411201000001641020400000268112040000016417203000001641720100000050152020000016410200000000451520100000069152040000065c1120400000654102010000065410200000000401120400000064122010000004c12204000000001110100000654102000000065c1220300000364102040000004c12200000006441720000000040112040000045d152040000004c122030000065410203000000401120400000000151020000005015202
  | 7, 38 => 0x3641020000000654102040000000017102000001641720300000164102030000004011200000001641720000000000101040000060c1120400000264172010000026417201000001641420200000064122040000016417200
  | 8, 0 => 0x151040000000013104000000001210400000000131030000000013100000000001110400000000101030000000010103000000001010100000000131030000000117103000000011710000000000111030000000011100000000001110000000001151010000000115100000000011710300000000111040000000115100000000001210000000001151030000000015103000000001310000000000131040000000017104000000001510400000000111040000000015103000000011710400000000151030000000115103
  | 8, 1 => 0x131010000000013104000000001710000000001171040000000015100000000011710000000000111040000000015101000000001710000000001151040000000012101000000001710100000000101040000000010104000000001510400000000111010000000017103000000001010300000000171030000000013101000000001710100000000101000000000011101000000001210000000000121040000000017104000000011510400000000101000000000015100000000001110100000001151040000000015101
  | 8, 2 => 0x131040000000015104000000011710000000001151010000000013100000000001110100000000111000000000011103000000011510300000000111000000000013101000000001110400000001171000000000015100000000001510100000000111030000000013104000000001710000000000121030000000013100000000011710100000000111000000000014102000000001010000000000121000000000017100000000001710400000000171040000000015104000000001710300000000101000000000014102
  | 8, 3 => 0x151000000000012104000000011710000000000151030000000015103000000011710400000000101040000000117104000000001310100000000151010000000017101000000001710100000000101040000000013104000000011710100000000171010000000115103000000001510400000000101010000000115104000000001310000000000101010000000011104000000001010100000001171030000000016102000000001310300000001171030000000117104000000011710400000000151000000000017104
  | 8, 4 => 0x131030000000013100000000011710300000000101010000000115101000000001310300000000121040000000015104000000001310400000000121000000000015100000000001210300000000101010000000115100000000011710400000001151010000000115100000000011510400000000111010000000117100000000001110300000000121000000000117104000000001710400000000121000000000012101000000011510400000000151010000000015100000000001110100000000131040000000117101
  | 8, 5 => 0x101010000000010104000000001010000000000111040000000015101000000001010400000000101030000000010104000000001510300000001171000000000017101000000001210000000000171010000000013101000000011510300000000131040000000015102000000011510000000000121030000000010101000000011710400000001151000000000017101000000011710300000000121040000000013101000000001110400000000171000000000012103000000001310100000001171030000000013100
  | 8, 6 => 0x101010000000010104000000001210100000000101010000000015100000000001510100000000131010000000117104000000001110000000000171000000000013103000000001710100000000171020000000017104000000001110100000000151040000000012104000000011710000000000171000000000015103000000001010000000001171040000000012100000000011710400000000171040000000115104000000001210300000000171040000000011104000000001010000000001171010000000010103
  | 8, 7 => 0x101010000000015102000000011710300000001171010000000012101000000001010000000000101040000000115100000000001510400000000171040000000115103000000001010000000000121030000000012104000000001210400000000131030000000017101000000011510000000000161020000000115100000000001710400000001151000000000115101000000001310400000000171010000000011103000000001010400000000121030000000115104000000001210000000001151040000000011100
  | 8, 8 => 0x1151000000000010104000000001010300000000101030000000117100000000001310400000000151000000000012104000000001710000000000171040000000115101000000011510300000001171040000000013104000000011710400000000171010000000117103000000011710000000000151010000000117104000000001210400000000171000000000115104000000001010000000000101040000000013104000000001110000000001151030000000117100000000001710000000000151040000000117100
  | 8, 9 => 0x171010000000017104000000001110300000000111010000000117101000000011710100000001151040000000013103000000001110000000001151000000000117103000000001010100000000111030000000010104000000001210300000000131000000000011100000000001310400000000111000000000115100000000001110100000000171030000000012104000000001410200000000171040000000017103000000001710300000001171040000000012104000000001110400000000131010000000015103
  | 8, 10 => 0x121030000000015103000000001010400000000101000000000012101000000001510000000000151000000000015101000000001010100000000101040000000010100000000001710400000001151040000000117104000000011510300000000111000000000115104000000001710000000001151040000000015104000000001710100000000171000000000017104000000001010400000000111030000000115101000000011510000000000101000000000017102000000001010100000000171000000000011104
  | 8, 11 => 0x171040000000011100000000011710100000000121010000000013100000000001510300000000171010000000013103000000011510400000000101040000000017103000000001310000000000131000000000015104000000001310100000000171040000000117101000000011510000000000111040000000015103000000001210400000000121030000000017104000000001210300000000111000000000015103000000001310400000000121000000000017100000000001210400000000151000000000013100
  | 8, 12 => 0x131030000000017104000000001710100000000121000000000017100000000011710000000000171000000000016102000000001710300000001171040000000012100000000011710400000000131030000000115103000000001110300000000121030000000011104000000001210100000000101010000000015104000000001010000000000111040000000012100000000001010000000000151020000000010103000000001310400000001151040000000012103000000001510000000000131030000000115100
  | 8, 13 => 0x151030000000015104000000011510100000000151040000000117104000000011510400000000131040000000015104000000011710100000001171040000000013100000000001510000000001171010000000016102000000001110400000000171040000000117103000000001210000000000161020000000013104000000001110000000000121040000000015104000000001210400000001171000000000117101000000001010400000001171010000000117104000000001510000000000131000000000012103
  | 8, 14 => 0x171040000000015104000000001710000000000171000000000011101000000011710000000000131030000000013104000000011710400000000171010000000013104000000001710300000000171020000000117101000000011510400000000121010000000011104000000001210100000001171000000000015103000000001110300000001171030000000013100000000001010100000001171000000000010103000000011510000000001151040000000012101000000011510400000000111040000000012100
  | 8, 15 => 0x1171010000000117104000000011510100000000121010000000115104000000001110000000000171030000000115104000000001110400000001151030000000010104000000001510300000001151000000000011101000000001310400000000121030000000017101000000011510000000000171040000000015104000000001510200000001151030000000115101000000001310300000000121040000000117104000000011710300000000151000000000017104000000011510000000001171030000000012104
  | 8, 16 => 0x1151010000000010101000000001210000000001171000000000015104000000001510100000000111030000000011101000000001210400000000111000000000013104000000001710000000000121040000000010103000000011710400000000101000000000017101000000011710000000000111010000000117101000000011710100000000101030000000013103000000001210100000000171040000000010100000000001010100000000131040000000115100000000001710400000000111040000000010104
  | 8, 17 => 0x121010000000115104000000001210400000001171040000000013104000000001110000000000121010000000015102000000001010400000000121010000000013101000000001310100000001151030000000011104000000001110400000000151040000000011103000000001010000000000111000000000012104000000001410200000001171040000000015100000000001210000000000171030000000012101000000001510400000000121040000000011100000000001010300000001151010000000017103
  | 8, 18 => 0x151000000000017104000000001110100000000131000000000012101000000011510100000000151000000000010100000000011710100000000131000000000010100000000011710000000000111030000000012100000000001110100000000101010000000117100000000001210100000001171030000000015103000000001210000000000151010000000010101000000001010400000000101040000000015103000000001310400000000121040000000012104000000001510200000001151010000000013100
  | 8, 19 => 0x1151010000000013100000000001210300000001151010000000012103000000001310000000000131000000000010104000000001710000000000151000000000017103000000001010300000001151010000000013103000000011710400000000131010000000013101000000001710000000000171000000000015100000000001510400000000151040000000017101000000001210000000000111040000000012103000000001210400000000101000000000011101000000001510300000000111010000000010103
  | 8, 20 => 0x101010000000117103000000001510100000000171000000000012101000000001210400000000171020000000011103000000011510000000001151010000000115104000000001710000000000171030000000013100000000011510000000000171020000000017100000000001010000000001151040000000115104000000001710200000001171000000000013104000000001110400000000131040000000017104000000001110400000000111030000000017103000000001310300000000101030000000012104
  | 8, 21 => 0x131010000000015103000000001110100000000131010000000115104000000001210400000000171000000000016102000000001210100000000121010000000010103000000001110100000000131010000000012100000000011710300000000101000000000115101000000001210100000001151040000000011103000000011510300000000101040000000115101000000001010100000000101040000000010100000000001510400000000111010000000117101000000001110400000001151010000000015101
  | 8, 22 => 0x171040000000117104000000001010000000000151010000000011100000000001410200000000111010000000011104000000001310400000000171040000000115100000000011510400000000151010000000011100000000001210400000000101030000000010104000000001710000000000101040000000115101000000001110400000000111040000000014102000000011510000000000121000000000011101000000011510000000000121000000000010100000000001510100000000151040000000017104
  | 8, 23 => 0x151040000000012101000000001710400000000121000000000015104000000001210000000000131010000000012103000000011710000000001151040000000011104000000001010400000000151010000000013101000000001110100000000111040000000017101000000011710100000001151040000000015101000000001110100000001151030000000115103000000001210400000001171000000000117104000000001210000000000171030000000013104000000001010400000000171040000000015100
  | 8, 24 => 0x131040000000117104000000001510400000001151040000000015101000000001310000000001171010000000017103000000011510000000000131040000000013104000000011510100000000151010000000017104000000001110000000000111030000000011104000000001210400000000101030000000115104000000001510000000000111010000000015101000000001510400000000111000000000010104000000001510000000001151010000000115104000000001310100000000111000000000117103
  | 8, 25 => 0x111040000000010101000000001210100000000151010000000015100000000001510100000000131010000000115103000000001210300000000151000000000013104000000011710400000000131030000000015104000000001510300000000131010000000015100000000011510400000001151030000000017103000000011510000000000151040000000117100000000001110400000000111030000000010103000000001110300000000171000000000015101000000001310000000000151040000000013101
  | 8, 26 => 0x11100000000011710300000000131010000000017100000000001110100000000131000000000017104000000001010400000000111040000000013100000000001710100000001171000000000115104000000011710300000000101000000000011103000000001510000000000101040000000015104000000011710400000001171000000000117100000000001310400000001171010000000011101
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 12 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry true dom_243 roots_243 9 s ws hint
  | 1 => checkCutEntry true dom_231 roots_231 9 s ws hint
  | 2 => checkCutEntry true dom_119 roots_119 8 s ws hint
  | 3 => checkCutEntry true dom_215 roots_215 9 s ws hint
  | 4 => checkCutEntry true dom_245 roots_245 9 s ws hint
  | 5 => checkCutEntry true dom_181 roots_181 5 s ws hint
  | 6 => checkCutEntry true dom_183 roots_183 6 s ws hint
  | 7 => checkCutEntry true dom_55 roots_55 5 s ws hint
  | 8 => checkCutEntry true dom_246 roots_246 7 s ws hint
  | 9 => checkCutEntry true dom_118 roots_118 5 s ws hint
  | 10 => checkCutEntry true dom_103 roots_103 5 s ws hint
  | 11 => checkCutEntry true dom_244 roots_244 5 s ws hint
  | 12 => checkCutEntry true dom_230 roots_230 6 s ws hint
  | 13 => checkCutEntry true dom_53 roots_53 4 s ws hint
  | 14 => checkCutEntry true dom_242 roots_242 6 s ws hint
  | 15 => checkCutEntry true dom_214 roots_214 6 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_247 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_243 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_231 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_119 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_215 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_245 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_181 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_183 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_55 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_246 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_118 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_103 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_244 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_230 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_53 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_242 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_214 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_247 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_247 goalM v ys := cutHitH_sound h

def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {v ys} (h : RunD true dom_247 goalM v ys) : RunD true dom_247 goalM v (ori ys) := h
def Z (s : Nat) := bar true dom_247 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 4 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 4 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 32 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 32 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 62 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 62 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8 : ∀ i, 0 ≤ i → i < 48 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 48 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9 : ∀ i, 0 ≤ i → i < 8 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
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
def RootG (s : Nat) : Bool :=
  scr true dom_247 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 6 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 10) (h : RunD true dom_247 goalM s xsM) : False := by
  have hmin : 6 ≤ s := by
    have hl := run_len h; change 7 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_247 roots_247 goal_247 11 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_247 goal_247 := by
    have h0 : isConstB dom_247 goal_247 = false := by decide +kernel
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

end S_247

theorem lowS_247 : Lower true dom_247 roots_247 goal_247 11 := S_247.noCircuit


end Cert
namespace Aux
open PEqualNP.CircuitLowerBounds
open Cert
def ownGoal : Nat := 0xfffffffffffffffeffffffffffffffeefffefffefffefffefefefcfcaaaa0000
def ownSubGoal : Nat := 0xfffffffffffffefeffffffffffffeeeefefefefefefefefefefefcfcaaaa0000
def ownMoves : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xffffffff000000000000000000000000ffffffff00000000, 32)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem ownSlice : Lower true dom_247 roots_247 ownSubGoal 11 :=
  lower_iso ownMoves (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_247
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem ownLower : Lower true dom_255 roots_255 ownGoal 12 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 72, 64)] (by decide +kernel) (by decide +kernel) ownSlice

theorem goal_eq_f : ∀ r : Fin 256, ownGoal.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
    (hhas : ∃ g ∈ gates, isNotGate g = true) : 13 ≤ gates.length := by
  obtain ⟨g, hg, hgn⟩ := hhas
  have hout : (execN gates xs256).getD o 0 &&& mask256 = ownGoal &&& mask256 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and, mask256_bit]
    by_cases hlt : r < 256
    · simp only [hlt, decide_true, Bool.and_true]
      have h1 := execN_bit gates xs256 r hlt (fun g' hg' => (hfan g' hg').1)
      have h2 := congrArg (fun l => l.getD o false) h1
      rw [xs256_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN gates xs256).map (·.testBit r)).getD o false =
          ((execN gates xs256).getD o 0).testBit r := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN gates xs256)[o]? with | none => simp | some v => rfl
      rw [hgd] at h2
      exact h2.trans ((hev (pt8 r)).trans (goal_eq_f ⟨r, hlt⟩).symm)
    · simp [hlt]
  have hsup0 : ∀ v ∈ xs256, Avail true mask256 xs256 v := fun v hv => Or.inr (Or.inl ⟨v, hv, rfl⟩)
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach true gates xs256 hfan (fun h => Bool.noConfusion h) 0 xs256 xs256 rfl hsup0
  have hav_out : Avail true mask256 bank ((execN gates xs256).getD o 0) := by
    by_cases hi : o < (execN gates xs256).length
    · exact hsup _ (getD_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hL := ownLower p bank hr (avail_of_eq hout hav_out)
  have hlt := countP_not_lt hg hgn
  omega

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [5, 1] }, { op := GateOp.and, inputs := [8, 7] }, { op := GateOp.or, inputs := [7, 0] }, { op := GateOp.and, inputs := [10, 4] }, { op := GateOp.or, inputs := [9, 11] }, { op := GateOp.or, inputs := [3, 0] }, { op := GateOp.or, inputs := [7, 6] }, { op := GateOp.and, inputs := [13, 14] }, { op := GateOp.or, inputs := [12, 15] }, { op := GateOp.or, inputs := [2, 1] }, { op := GateOp.or, inputs := [6, 5] }, { op := GateOp.and, inputs := [17, 18] }, { op := GateOp.or, inputs := [16, 19] }]

theorem wit_mono : ∀ g ∈ witGates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 20⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
  decide +kernel

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o hfan _h1not hev
  by_cases hhas : ∃ g ∈ gates, isNotGate g = true
  · have hfan' : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      obtain ⟨h1, h2⟩ := hfan g hg
      refine ⟨?_, h2⟩
      rcases h1 with h1 | h1 | h1 <;> simp [h1]
    have hlb : 13 ≤ gates.length := lb_with_not gates o hfan' hev hhas
    refine ⟨witGates, 20, wit_mono, ?_, wit_eval⟩
    have hlen : witGates.length = 13 := rfl
    omega
  · push_neg at hhas
    refine ⟨gates, o, ?_, le_rfl, hev⟩
    intro g hg
    obtain ⟨h1, h2⟩ := hfan g hg
    refine ⟨?_, h2⟩
    rcases h1 with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exfalso; have := hhas g hg; simp [isNotGate, h1] at this

end Aux
end PEqualNP.Outside.L_meta_28708

theorem PEqualNP.Outside.L_meta_28708 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_28708.Aux.main
