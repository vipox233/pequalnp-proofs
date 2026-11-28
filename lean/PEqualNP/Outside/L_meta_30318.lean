import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_30318_aux
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
def mask256:Nat:=2 ^ 256 - 1
def negD (d w:Nat):Nat:=(w^^^mask256)&&&d
def andD (d a b:Nat):Nat:=(a&&&b)&&&d
def orD (d a b:Nat):Nat:=(a|||b)&&&d
def opD (d:Nat) (op:Nat) (a b:Nat):Nat :=
  if op==0 then andD d a b
  else if op==1 then orD d a b
  else if op==2 then andD d a (negD d b)
  else andD d (negD d a) b
def allowedB (u:Bool) (op:Nat):Bool :=
  decide (op < 2)||(u&&decide (op < 4))
def flipOp (op:Nat):Nat :=
  if op==2 then 3 else if op==3 then 2 else op
def nrmD (u:Bool) (d w:Nat):Nat :=
  if u&&w.testBit 0 then negD d w else w&&&d
def kept {α : Type} (b:Bool) (x : α) (xs:List α):List α :=
  if b then x :: xs else xs
def RunD (u:Bool) (d y:Nat) (t : ℕ) (ws:List Nat) : Prop :=
  ∀ P : ℕ → List Nat → Prop,P 0 [y] →
    (∀ {s xs zs},List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a b r} (op:Nat) (ka kb:Bool),
      allowedB u op = true →
      opD d op a b ≠ 0 →
      opD d op a b ≠ d →
      opD d op a b ∉ (a :: b :: r) →
      P s (opD d op a b :: kept ka a (kept kb b r)) →
      P (s + 1) (a :: b :: r)) → P t ws
section
variable {u:Bool} {d y:Nat}
theorem Run.done : RunD u d y 0 [y]:=fun _ dn _ _=>dn
theorem Run.perm {s xs zs} (p : List.Perm xs zs) (h : RunD u d y s xs) :
    RunD u d y s zs:=fun P dn q b=>q p (h P dn q b)
theorem Run.two {s a b r} (op:Nat) (ka kb:Bool)
    (hop : allowedB u op = true)
    (h0 : opD d op a b ≠ 0) (hd : opD d op a b ≠ d) (hm : opD d op a b ∉ (a :: b :: r))
    (h : RunD u d y s (opD d op a b :: kept ka a (kept kb b r))) :
    RunD u d y (s + 1) (a :: b :: r):=fun P dn q v=>v op ka kb hop h0 hd hm (h P dn q v)
theorem Run.fold {P : ∀ t ws,RunD u d y t ws → Prop}
    (done : P 0 [y] Run.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : RunD u d y s xs),
      P s xs h → P s zs (Run.perm hp h))
    (two : ∀ {s a b r} (op:Nat) (ka kb:Bool)
      (hop : allowedB u op = true)
      (h0 : opD d op a b ≠ 0) (hd : opD d op a b ≠ d) (hm : opD d op a b ∉ (a :: b :: r))
      (h : RunD u d y s (opD d op a b :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (Run.two op ka kb hop h0 hd hm h))
    {t ws} (h : RunD u d y t ws) : P t ws h:=by
  have hex:=h (fun s xs=>∃ h' : RunD u d y s xs,P s xs h')
    ⟨Run.done,done⟩
    (fun hp ⟨h',ih⟩=>⟨Run.perm hp h',perm hp h' ih⟩)
    (fun op ka kb hop h0 hd hm ⟨h',ih⟩=>⟨Run.two op ka kb hop h0 hd hm h',two op ka kb hop h0 hd hm h' ih⟩)
  exact hex.elim fun _ hp=>hp
end
theorem allowed_cases {u:Bool} {op:Nat} (h : allowedB u op = true) :
    op = 0 ∨ op = 1 ∨ (u = true ∧ op = 2) ∨ (u = true ∧ op = 3):=by
  simp only [allowedB,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at h
  rcases h with h | ⟨hu,h⟩
  · omega
  · have : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3:=by omega
    rcases this with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl ⟨hu,rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hu,rfl⟩))
theorem opD_comm {u:Bool} (d:Nat) {op:Nat} (hop : allowedB u op = true) (a b:Nat) :
    opD d op a b = opD d (flipOp op) b a:=by
  rcases allowed_cases hop with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;>
    simp [opD,flipOp,andD,orD,Nat.and_comm,Nat.or_comm]
theorem flipOp_allowed {u:Bool} {op:Nat} (hop : allowedB u op = true) :
    allowedB u (flipOp op) = true:=by
  rcases allowed_cases hop with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [allowedB,flipOp]
theorem kept_map {α β : Type} (e : α → β) (b:Bool) (x : α) (xs:List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e):=by cases b <;> simp [kept]
theorem mem_kept {α : Type} (b:Bool) (x a : α) (xs:List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs:=by cases b <;> simp [kept]
theorem nodup_kept {α : Type} (b:Bool) (x : α) (xs:List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup:=by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h
theorem keep_perm {α : Type} {xs ys:List α} (p : xs.Perm ys) (b:Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys):=by cases b <;> simpa [kept] using p
theorem run_len {u d y s xs} (h : RunD u d y s xs) :
    xs.length ≤ s + 1:=by
  induction h using Run.fold with
  | done=>simp
  | perm hp _ ih=>rwa [← hp.length_eq]
  | two _ ka kb _ _ _ _ _ ih=>cases ka <;> cases kb <;> simp_all [kept] <;> omega
theorem zero_done {u d y t ws} (h : RunD u d y t ws) :
    t = 0 → ws = [y]:=by
  induction h using Run.fold with
  | done=>simp
  | perm p _ ih=>intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | two=>simp
def IsConst (d w:Nat) : Prop:=(w&&&d) = 0 ∨ (w&&&d) = d
def isConstB (d w:Nat):Bool:=(w&&&d==0)||(w&&&d==d)
theorem isConstB_iff (d w:Nat) : isConstB d w = true ↔ IsConst d w:=by
  simp [isConstB,IsConst]
def Avail (u:Bool) (d:Nat) (bank:List Nat) (w:Nat) : Prop :=
  IsConst d w ∨ (∃ v ∈ bank,(v&&&d) = (w&&&d)) ∨ (u = true ∧ ∃ v ∈ bank,(v&&&d) = negD d w)
def availB (u:Bool) (d:Nat) (bank:List Nat) (w:Nat):Bool :=
  let m:=w&&&d
  m==0||m==d||bank.any (fun v=>(v&&&d)==m) ||
    (u&&bank.any (fun v=>(v&&&d)==negD d w))
theorem availB_iff (u:Bool) (d:Nat) (bank:List Nat) (w:Nat) :
    availB u d bank w = true ↔ Avail u d bank w:=by
  simp [availB,Avail,IsConst,or_assoc]
def NatReach (u:Bool) (d:Nat) (roots:List Nat):Nat → List Nat → Prop
  | 0,bank=>bank = roots
  | p + 1,bank =>
    ∃ b a c op,allowedB u op = true ∧ bank = opD d op a c :: b ∧
      NatReach u d roots p b ∧ Avail u d b a ∧ Avail u d b c
def Lower (u:Bool) (d:Nat) (roots:List Nat) (T:Nat) (L:Nat) : Prop :=
  ∀ p bank,NatReach u d roots p bank → Avail u d bank T → L ≤ p
theorem mask256_bit (i:Nat) : mask256.testBit i = decide (i < 256):=by
  rw [mask256,Nat.testBit_two_pow_sub_one]
theorem opD_and_sub {d d1:Nat} (hd : d&&&mask256 = d) (hsub : d&&&d1 = d) (op a b:Nat) :
    opD d1 op a b&&&d = opD d op a b:=by
  apply Nat.eq_of_testBit_eq; intro i
  have h1:=congrArg (fun v=>v.testBit i) hd
  have h2:=congrArg (fun v=>v.testBit i) hsub
  unfold opD
  split_ifs <;> simp only [andD,orD,negD,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor] at * <;>
    cases hi : d.testBit i <;> simp_all
theorem negD_invol {d:Nat} (hd : d&&&mask256 = d) (a:Nat) :
    negD d (negD d a) = a&&&d:=by
  apply Nat.eq_of_testBit_eq; intro i
  have h1:=congrArg (fun v=>v.testBit i) hd
  simp only [negD,Nat.testBit_and,Nat.testBit_xor] at *
  cases hi : d.testBit i <;> cases ha : a.testBit i <;> simp_all
theorem negD_mask (d a:Nat) : negD d (a&&&d) = negD d a:=by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [negD,Nat.testBit_and,Nat.testBit_xor]
  cases d.testBit i <;> simp
theorem opD_mask_self (d op a b:Nat) : opD d op a b&&&d = opD d op a b:=by
  apply Nat.eq_of_testBit_eq; intro i
  unfold opD; split_ifs <;> simp only [andD,orD,negD,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor] <;>
    cases d.testBit i <;> simp
theorem negD_const {d:Nat} (hd : d&&&mask256 = d) {a:Nat} (hc : IsConst d a) :
    IsConst d (negD d a):=by
  rcases hc with h0 | h1
  · right; apply Nat.eq_of_testBit_eq; intro i
    have h0i:=congrArg (fun v=>v.testBit i) h0
    have hdi:=congrArg (fun v=>v.testBit i) hd
    simp only [negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit] at *
    cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
  · left; apply Nat.eq_of_testBit_eq; intro i
    have h1i:=congrArg (fun v=>v.testBit i) h1
    have hdi:=congrArg (fun v=>v.testBit i) hd
    simp only [negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit] at *
    cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
theorem avail_cons {u:Bool} {d:Nat} {bank:List Nat} (z w:Nat) (h : Avail u d bank w) :
    Avail u d (z :: bank) w:=by
  rcases h with hc | ⟨v,hv,he⟩ | ⟨hu,v,hv,he⟩
  · exact Or.inl hc
  · exact Or.inr (Or.inl ⟨v,List.mem_cons_of_mem _ hv,he⟩)
  · exact Or.inr (Or.inr ⟨hu,v,List.mem_cons_of_mem _ hv,he⟩)
theorem avail_of_eq {u:Bool} {d:Nat} {bank:List Nat} {v w:Nat}
    (he : v&&&d = w&&&d) (h : Avail u d bank v) : Avail u d bank w:=by
  rcases h with (h0 | h1) | ⟨x,hx,hxe⟩ | ⟨hu,x,hx,hxe⟩
  · exact Or.inl (Or.inl (he.symm.trans h0))
  · exact Or.inl (Or.inr (he.symm.trans h1))
  · exact Or.inr (Or.inl ⟨x,hx,hxe.trans he⟩)
  · exact Or.inr (Or.inr ⟨hu,x,hx,hxe.trans (by rw [← negD_mask,he,negD_mask])⟩)
theorem avail_neg {d:Nat} (hd : d&&&mask256 = d) {bank:List Nat} {w:Nat}
    (h : Avail true d bank w) : Avail true d bank (negD d w):=by
  rcases h with hc | ⟨v,hv,he⟩ | ⟨_,v,hv,he⟩
  · exact Or.inl (negD_const hd hc)
  · refine Or.inr (Or.inr ⟨rfl,v,hv,?_⟩)
    rw [negD_invol hd,he]
  · refine Or.inr (Or.inl ⟨v,hv,?_⟩)
    rw [he]; simp [negD,Nat.and_assoc,Nat.and_self]
theorem opD_const_left {u:Bool} {d:Nat} (hd : d&&&mask256 = d) {op:Nat}
    (hop : allowedB u op = true) {a b:Nat} (hc : IsConst d a) :
    (opD d op a b&&&d = 0) ∨ (opD d op a b&&&d = d) ∨
      (opD d op a b&&&d = b&&&d) ∨ (u = true ∧ opD d op a b&&&d = negD d b):=by
  rcases allowed_cases hop with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · rcases hc with h0 | h1
    · left; apply Nat.eq_of_testBit_eq; intro i
      have h0i:=congrArg (fun v=>v.testBit i) h0
      simp only [opD,andD,Nat.testBit_and,Nat.zero_testBit,beq_self_eq_true,ite_true] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
    · right; right; left; apply Nat.eq_of_testBit_eq; intro i
      have h1i:=congrArg (fun v=>v.testBit i) h1
      simp only [opD,andD,Nat.testBit_and,beq_self_eq_true,ite_true] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · rcases hc with h0 | h1
    · right; right; left; apply Nat.eq_of_testBit_eq; intro i
      have h0i:=congrArg (fun v=>v.testBit i) h0
      simp only [opD,orD,Nat.testBit_and,Nat.testBit_or,Nat.zero_testBit,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
    · right; left; apply Nat.eq_of_testBit_eq; intro i
      have h1i:=congrArg (fun v=>v.testBit i) h1
      simp only [opD,orD,Nat.testBit_and,Nat.testBit_or,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · rcases hc with h0 | h1
    · left; apply Nat.eq_of_testBit_eq; intro i
      have h0i:=congrArg (fun v=>v.testBit i) h0
      simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
    · right; right; right; refine ⟨hu,?_⟩
      apply Nat.eq_of_testBit_eq; intro i
      have h1i:=congrArg (fun v=>v.testBit i) h1
      have hdi:=congrArg (fun v=>v.testBit i) hd
      simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · rcases hc with h0 | h1
    · right; right; left; apply Nat.eq_of_testBit_eq; intro i
      have h0i:=congrArg (fun v=>v.testBit i) h0
      have hdi:=congrArg (fun v=>v.testBit i) hd
      simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
    · left; apply Nat.eq_of_testBit_eq; intro i
      have h1i:=congrArg (fun v=>v.testBit i) h1
      have hdi:=congrArg (fun v=>v.testBit i) hd
      simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
theorem countP_kept_ge {α : Type} (p : α → Bool) (b:Bool) (a : α) (xs:List α) :
    xs.countP p ≤ (kept b a xs).countP p:=by
  cases b <;> simp [kept,List.countP_cons] <;> split <;> omega
theorem contraction {u:Bool} {d d1 T:Nat} (hd : d&&&mask256 = d) (hsub : d&&&d1 = d)
    (hnc : ¬ IsConst d T) {s ws} (h : RunD u d1 T s ws) {roots p bank}
    (hp:NatReach u d roots p bank) (hs : ∀ w ∈ ws,Avail u d bank w) :
    ∃ q next,NatReach u d roots q next ∧ Avail u d next T ∧
      q + ws.countP (isConstB d) ≤ p + s:=by
  induction h using Run.fold generalizing p bank with
  | done =>
    have hfalse : isConstB d T = false:=by
      cases hc : isConstB d T with
      | false=>rfl
      | true=>exact absurd ((isConstB_iff d T).1 hc) hnc
    exact ⟨p,bank,hp,hs T (by simp),by simp [hfalse]⟩
  | perm eq _ ih =>
    obtain ⟨q,next,hq,ht,hle⟩:=ih hp (fun w hw=>hs w (eq.mem_iff.1 hw))
    rw [eq.countP_eq] at hle
    exact ⟨q,next,hq,ht,hle⟩
  | @two s a b r op ka kb hop _ _ _ _ ih =>
    have ha:=hs a List.mem_cons_self
    have hb:=hs b (List.mem_cons_of_mem _ List.mem_cons_self)
    set z1:=opD d1 op a b
    set z0:=opD d op a b
    have hz_eq : z1&&&d = z0&&&d:=by
      rw [opD_and_sub hd hsub,opD_mask_self]
    by_cases hcab : IsConst d a ∨ IsConst d b
    · have hz_av : Avail u d bank z1:=by
        apply avail_of_eq hz_eq.symm
        rcases hcab with hca | hcb
        · rcases opD_const_left hd hop hca with h0 | h1 | he | ⟨rfl,hn⟩
          · exact Or.inl (Or.inl h0)
          · exact Or.inl (Or.inr h1)
          · exact avail_of_eq he.symm hb
          · exact avail_of_eq (by rw [hn]; simp [negD,Nat.and_assoc,Nat.and_self]) (avail_neg hd hb)
        · dsimp only [z0]; rw [opD_comm d hop a b]
          rcases opD_const_left hd (flipOp_allowed hop) hcb with h0 | h1 | he | ⟨rfl,hn⟩
          · exact Or.inl (Or.inl h0)
          · exact Or.inl (Or.inr h1)
          · exact avail_of_eq he.symm ha
          · exact avail_of_eq (by rw [hn]; simp [negD,Nat.and_assoc,Nat.and_self]) (avail_neg hd ha)
      have hs' : ∀ w ∈ z1 :: kept ka a (kept kb b r),Avail u d bank w:=by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact hz_av
        · rw [mem_kept,mem_kept] at hw
          rcases hw with ⟨_,rfl⟩ | ⟨_,rfl⟩ | hw
          · exact ha
          · exact hb
          · exact hs w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw))
      obtain ⟨q,next,hq,ht,hle⟩:=ih hp hs'
      have hkr : r.countP (isConstB d) ≤ (kept ka a (kept kb b r)).countP (isConstB d) :=
        le_trans (countP_kept_ge _ kb b r) (countP_kept_ge _ ka a _)
      have hcost : (if isConstB d a = true then 1 else 0) + (if isConstB d b = true then 1 else 0)
          ≤ 1 + (if isConstB d z1 = true then 1 else 0):=by
        rcases hcab with hca | hcb
        · have ha1 : isConstB d a = true:=(isConstB_iff _ _).2 hca
          rcases opD_const_left hd hop hca with h0 | h1 | he | ⟨_,hn⟩
          · have hz1 : isConstB d z1 = true:=(isConstB_iff _ _).2 (Or.inl (hz_eq.trans h0))
            simp [ha1,hz1]; split <;> omega
          · have hz1 : isConstB d z1 = true:=(isConstB_iff _ _).2 (Or.inr (hz_eq.trans h1))
            simp [ha1,hz1]; split <;> omega
          · have hzb : isConstB d z1 = isConstB d b:=by simp only [isConstB,hz_eq.trans he]
            simp [ha1,hzb]
          · have hzb : isConstB d z1 = isConstB d b:=by
              apply Bool.eq_iff_iff.2; rw [isConstB_iff,isConstB_iff]
              have hnm : negD d b&&&d = negD d b:=by simp [negD,Nat.and_assoc,Nat.and_self]
              constructor
              · intro hz; have hnb : IsConst d (negD d b):=by
                  rcases hz with h0 | h1
                  · exact Or.inl (hnm.trans (hn.symm.trans (hz_eq.symm.trans h0)))
                  · exact Or.inr (hnm.trans (hn.symm.trans (hz_eq.symm.trans h1)))
                have h2:=negD_const hd hnb
                rw [negD_invol hd] at h2
                rcases h2 with e | e <;> [exact Or.inl (by simpa [Nat.and_assoc,Nat.and_self] using e); exact Or.inr (by simpa [Nat.and_assoc,Nat.and_self] using e)]
              · intro hb'; have hnb:=negD_const hd hb'
                rcases hnb with h0 | h1
                · exact Or.inl (hz_eq.trans (hn.trans (hnm.symm.trans h0)))
                · exact Or.inr (hz_eq.trans (hn.trans (hnm.symm.trans h1)))
            simp [ha1,hzb]
        · have hb1 : isConstB d b = true:=(isConstB_iff _ _).2 hcb
          have hz_eq' : z1&&&d = opD d (flipOp op) b a&&&d:=by rw [hz_eq]; dsimp only [z0]; rw [opD_comm d hop a b]
          rcases opD_const_left hd (flipOp_allowed hop) hcb with h0 | h1 | he | ⟨_,hn⟩
          · have hz1 : isConstB d z1 = true:=(isConstB_iff _ _).2 (Or.inl (hz_eq'.trans h0))
            simp [hb1,hz1]; split <;> omega
          · have hz1 : isConstB d z1 = true:=(isConstB_iff _ _).2 (Or.inr (hz_eq'.trans h1))
            simp [hb1,hz1]; split <;> omega
          · have hza : isConstB d z1 = isConstB d a:=by simp only [isConstB,hz_eq'.trans he]
            simp [hb1,hza]
          · have hza : isConstB d z1 = isConstB d a:=by
              apply Bool.eq_iff_iff.2; rw [isConstB_iff,isConstB_iff]
              have hnm : negD d a&&&d = negD d a:=by simp [negD,Nat.and_assoc,Nat.and_self]
              constructor
              · intro hz; have hna : IsConst d (negD d a):=by
                  rcases hz with h0 | h1
                  · exact Or.inl (hnm.trans (hn.symm.trans (hz_eq'.symm.trans h0)))
                  · exact Or.inr (hnm.trans (hn.symm.trans (hz_eq'.symm.trans h1)))
                have h2:=negD_const hd hna
                rw [negD_invol hd] at h2
                rcases h2 with e | e <;> [exact Or.inl (by simpa [Nat.and_assoc,Nat.and_self] using e); exact Or.inr (by simpa [Nat.and_assoc,Nat.and_self] using e)]
              · intro ha'; have hna:=negD_const hd ha'
                rcases hna with h0 | h1
                · exact Or.inl (hz_eq'.trans (hn.trans (hnm.symm.trans h0)))
                · exact Or.inr (hz_eq'.trans (hn.trans (hnm.symm.trans h1)))
            simp [hb1,hza]
      simp only [List.countP_cons] at hle ⊢
      exact ⟨q,next,hq,ht,by omega⟩
    · have hna : isConstB d a = false:=by
        cases h : isConstB d a with | false=>rfl | true=>exact absurd (Or.inl ((isConstB_iff _ _).1 h)) hcab
      have hnb : isConstB d b = false:=by
        cases h : isConstB d b with | false=>rfl | true=>exact absurd (Or.inr ((isConstB_iff _ _).1 h)) hcab
      have hreach':NatReach u d roots (p + 1) (z0 :: bank):=⟨bank,a,b,op,hop,rfl,hp,ha,hb⟩
      have hz_av : Avail u d (z0 :: bank) z1:=Or.inr (Or.inl ⟨z0,List.mem_cons_self,hz_eq.symm⟩)
      have hs' : ∀ w ∈ z1 :: kept ka a (kept kb b r),Avail u d (z0 :: bank) w:=by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact hz_av
        · rw [mem_kept,mem_kept] at hw
          rcases hw with ⟨_,rfl⟩ | ⟨_,rfl⟩ | hw
          · exact avail_cons _ _ ha
          · exact avail_cons _ _ hb
          · exact avail_cons _ _ (hs w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)))
      obtain ⟨q,next,hq,ht,hle⟩:=ih hreach' hs'
      have hkr : r.countP (isConstB d) ≤ (kept ka a (kept kb b r)).countP (isConstB d) :=
        le_trans (countP_kept_ge _ kb b r) (countP_kept_ge _ ka a _)
      simp only [List.countP_cons,hna,hnb,Bool.false_eq_true,ite_false] at hle ⊢
      exact ⟨q,next,hq,ht,by omega⟩
theorem nrmD_mask (u:Bool) (d w:Nat) : nrmD u d w&&&d = nrmD u d w:=by
  unfold nrmD; split <;> simp [negD,Nat.and_assoc,Nat.and_self]
theorem nrmD_of_bit0_false (u:Bool) (d w:Nat) (hw : w.testBit 0 = false) :
    nrmD u d w = w&&&d:=by
  simp [nrmD,hw]
theorem nrmD_and_d {d:Nat} (hd0 : d.testBit 0 = true) (u:Bool) (w:Nat) :
    nrmD u d (w&&&d) = nrmD u d w:=by
  unfold nrmD
  rw [Nat.testBit_and,hd0,Bool.and_true,negD_mask,Nat.and_assoc,Nat.and_self]
theorem nrmD_neg {d:Nat} (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true) (w:Nat) :
    nrmD true d (negD d w) = nrmD true d w:=by
  have hm0 : mask256.testBit 0 = true:=by decide
  unfold nrmD
  have hnb : (negD d w).testBit 0 = !w.testBit 0:=by
    simp only [negD,Nat.testBit_and,Nat.testBit_xor,hd0,hm0,Bool.and_true,Bool.xor_true]
  rw [hnb]
  cases hw : w.testBit 0
  · simp [negD_invol hd]
  · simp [negD,Nat.and_assoc,Nat.and_self]
theorem nrmD_const_iff {d:Nat} (hd : d&&&mask256 = d) (u:Bool) (w:Nat) :
    (nrmD u d w ≠ 0 ∧ nrmD u d w ≠ d) ↔ ¬ IsConst d w:=by
  unfold nrmD
  have hnm : negD d w&&&d = negD d w:=by simp [negD,Nat.and_assoc,Nat.and_self]
  split
  · constructor
    · rintro ⟨h0,h1⟩ hc
      rcases negD_const hd hc with hn0 | hn1
      · exact h0 (hnm.symm.trans hn0)
      · exact h1 (hnm.symm.trans hn1)
    · intro hnc; refine ⟨fun h0=>?_,fun h1=>?_⟩
      · have:=negD_const hd (a:=negD d w) (Or.inl (hnm.trans h0))
        rw [negD_invol hd] at this
        exact hnc (by rcases this with e | e <;> [exact Or.inl (by simpa [Nat.and_assoc,Nat.and_self] using e); exact Or.inr (by simpa [Nat.and_assoc,Nat.and_self] using e)])
      · have:=negD_const hd (a:=negD d w) (Or.inr (hnm.trans h1))
        rw [negD_invol hd] at this
        exact hnc (by rcases this with e | e <;> [exact Or.inl (by simpa [Nat.and_assoc,Nat.and_self] using e); exact Or.inr (by simpa [Nat.and_assoc,Nat.and_self] using e)])
  · simp [IsConst,not_or]
theorem opD_bit {d:Nat} (hd : d&&&mask256 = d) (op a b i:Nat) (hdi : d.testBit i = true) :
    (opD d op a b).testBit i =
      if op==0 then a.testBit i&&b.testBit i
      else if op==1 then a.testBit i||b.testBit i
      else if op==2 then a.testBit i&&!(b.testBit i)
      else !(a.testBit i)&&b.testBit i:=by
  have hmi : mask256.testBit i = true:=by
    have:=congrArg (fun v=>v.testBit i) hd; simp [Nat.testBit_and,hdi] at this; exact this
  unfold opD; split_ifs <;>
    simp only [andD,orD,negD,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,hdi,hmi,Bool.and_true,Bool.xor_true]
theorem nrmD_bit {d:Nat} (hd : d&&&mask256 = d) (w i:Nat) (hdi : d.testBit i = true) :
    (nrmD true d w).testBit i = if w.testBit 0 then !(w.testBit i) else w.testBit i:=by
  have hmi : mask256.testBit i = true:=by
    have:=congrArg (fun v=>v.testBit i) hd; simp [Nat.testBit_and,hdi] at this; exact this
  unfold nrmD
  cases hw0 : w.testBit 0 <;>
    simp only [hw0,Bool.true_and,Bool.and_false,Bool.false_eq_true,ite_true,ite_false,
      negD,Nat.testBit_and,Nat.testBit_xor,hdi,hmi,Bool.and_true,Bool.xor_true]
theorem nrmD_opD {d:Nat} (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (u:Bool) (op:Nat) (hop : allowedB u op = true) (a b:Nat) :
    ∃ op',allowedB u op' = true ∧
      nrmD u d (opD d op a b) = opD d op' (nrmD u d a) (nrmD u d b):=by
  cases u with
  | false =>
    rcases allowed_cases hop with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
    · exact ⟨0,rfl,by
        apply Nat.eq_of_testBit_eq; intro i
        simp only [nrmD,opD,andD,Bool.false_and,Bool.false_eq_true,ite_false,beq_self_eq_true,ite_true,Nat.testBit_and]
        cases d.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1,rfl,by
        apply Nat.eq_of_testBit_eq; intro i
        simp only [nrmD,opD,orD,Bool.false_and,Bool.false_eq_true,ite_false]
        simp only [show (1==0) = false from rfl,show (1==1) = true from rfl,Bool.false_eq_true,ite_false,ite_true,Nat.testBit_and,Nat.testBit_or]
        cases d.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · contradiction
    · contradiction
  | true =>
    have h4 : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3:=by
      rcases allowed_cases hop with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp
    have hbit : ∀ (e:Nat),
        (∀ i,d.testBit i = true →
          (nrmD true d (opD d op a b)).testBit i =
          (opD d e (nrmD true d a) (nrmD true d b)).testBit i) →
        nrmD true d (opD d op a b) = opD d e (nrmD true d a) (nrmD true d b):=by
      intro e h; apply Nat.eq_of_testBit_eq; intro i
      by_cases hdi : d.testBit i = true
      · exact h i hdi
      · have hf : d.testBit i = false:=Bool.eq_false_iff.2 hdi
        have h1:=congrArg (fun v=>v.testBit i) (nrmD_mask true d (opD d op a b))
        have h2:=congrArg (fun v=>v.testBit i) (opD_mask_self d e (nrmD true d a) (nrmD true d b))
        simp only [Nat.testBit_and,hf,Bool.and_false] at h1 h2; exact h1.symm.trans h2
    rcases h4 with rfl | rfl | rfl | rfl <;>
      cases ha0 : a.testBit 0 <;> cases hb0 : b.testBit 0
    · exact ⟨0,by decide,hbit 0 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨2,by decide,hbit 2 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨3,by decide,hbit 3 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1,by decide,hbit 1 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1,by decide,hbit 1 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨3,by decide,hbit 3 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨2,by decide,hbit 2 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨0,by decide,hbit 0 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨2,by decide,hbit 2 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨0,by decide,hbit 0 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1,by decide,hbit 1 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨3,by decide,hbit 3 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨3,by decide,hbit 3 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1,by decide,hbit 1 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨0,by decide,hbit 0 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨2,by decide,hbit 2 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
theorem avail_nrm_mem {u:Bool} {d:Nat} (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    {b:List Nat} {w:Nat} (h : Avail u d b w) (hnc : ¬ IsConst d w) :
    nrmD u d w ∈ b.map (nrmD u d):=by
  rcases h with hc | ⟨v,hv,he⟩ | ⟨rfl,v,hv,he⟩
  · exact absurd hc hnc
  · refine List.mem_map.2 ⟨v,hv,?_⟩
    rw [← nrmD_and_d hd0,he,nrmD_and_d hd0]
  · refine List.mem_map.2 ⟨v,hv,?_⟩
    rw [← nrmD_and_d hd0,he,nrmD_neg hd hd0]
theorem pull_two {u:Bool} {d Y k ws} (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (hnd : ws.Nodup) (hprop : ∀ w ∈ ws,w ≠ 0 ∧ w ≠ d) (h : RunD u d Y k ws)
    {b:List Nat} {a c:Nat} (op:Nat) (hop : allowedB u op = true)
    (ha : Avail u d b a) (hc : Avail u d b c)
    (hsub : ∀ w ∈ ws,w ∈ nrmD u d (opD d op a c) :: b.map (nrmD u d)) :
    ∃ k' ws',k' ≤ k + 1 ∧ ws'.Nodup ∧ (∀ w ∈ ws',w ≠ 0 ∧ w ≠ d) ∧
      (∀ w ∈ ws',w ∈ b.map (nrmD u d)) ∧ RunD u d Y k' ws':=by
  set z:=nrmD u d (opD d op a c)
  by_cases hzm : z ∈ ws
  · by_cases hzb : z ∈ b.map (nrmD u d)
    · exact ⟨k,ws,by omega,hnd,hprop,fun w hw=>by
        rcases List.mem_cons.1 (hsub w hw) with rfl | hm
        · exact hzb
        · exact hm,h⟩
    · have hzp:=hprop z hzm
      obtain ⟨op',hop',hez⟩:=nrmD_opD hd hd0 u op hop a c
      have ha_nc : ¬ IsConst d a:=by
        intro hca
        have hznc : ¬ IsConst d (opD d op a c):=(nrmD_const_iff hd u _).1 hzp
        rcases opD_const_left hd hop hca with e0 | e1 | ec | ⟨rfl,en⟩
        · exact hznc (Or.inl e0)
        · exact hznc (Or.inr e1)
        · have hcn : ¬ IsConst d c:=fun hcc=>hznc (by rcases hcc with e | e <;> [exact Or.inl (ec.trans e); exact Or.inr (ec.trans e)])
          have hz_eq : z = nrmD u d c:=by dsimp only [z]; rw [← nrmD_and_d hd0 u (opD d op a c),ec,nrmD_and_d hd0]
          exact hzb (hz_eq ▸ avail_nrm_mem hd hd0 hc hcn)
        · have hcn : ¬ IsConst d c:=fun hcc=>hznc (by
            rcases negD_const hd hcc with e | e
            · exact Or.inl (en.trans (by simpa [negD,Nat.and_assoc,Nat.and_self] using e))
            · exact Or.inr (en.trans (by simpa [negD,Nat.and_assoc,Nat.and_self] using e)))
          have hz_eq : z = nrmD true d c:=by dsimp only [z]; rw [← nrmD_and_d hd0 true (opD d op a c),en,nrmD_neg hd hd0]
          exact hzb (hz_eq ▸ avail_nrm_mem hd hd0 hc hcn)
      have hc_nc : ¬ IsConst d c:=by
        intro hcc
        have hznc : ¬ IsConst d (opD d op a c):=(nrmD_const_iff hd u _).1 hzp
        have hcm : opD d op a c = opD d (flipOp op) c a:=opD_comm d hop a c
        rcases opD_const_left hd (flipOp_allowed hop) hcc with e0 | e1 | ea | ⟨rfl,en⟩
        · exact hznc (Or.inl (hcm.symm ▸ e0))
        · exact hznc (Or.inr (hcm.symm ▸ e1))
        · have hz_eq : z = nrmD u d a:=by
            dsimp only [z]; rw [← nrmD_and_d hd0 u (opD d op a c),hcm,ea,nrmD_and_d hd0]
          exact hzb (hz_eq ▸ avail_nrm_mem hd hd0 ha ha_nc)
        · have hz_eq : z = nrmD true d a:=by
            dsimp only [z]; rw [← nrmD_and_d hd0 true (opD d op a c),hcm,en,nrmD_neg hd hd0]
          exact hzb (hz_eq ▸ avail_nrm_mem hd hd0 ha ha_nc)
      set a':=nrmD u d a
      set c':=nrmD u d c
      have ha'_mem : a' ∈ b.map (nrmD u d):=avail_nrm_mem hd hd0 ha ha_nc
      have hc'_mem : c' ∈ b.map (nrmD u d):=avail_nrm_mem hd hd0 hc hc_nc
      have ha'_prop : a' ≠ 0 ∧ a' ≠ d:=(nrmD_const_iff hd u a).2 ha_nc
      have hc'_prop : c' ≠ 0 ∧ c' ≠ d:=(nrmD_const_iff hd u c).2 hc_nc
      have hne_ac : a' ≠ c':=by
        intro heq
        have hz_eq : opD d op' a' a' = a' ∨ opD d op' a' a' = 0:=by
          rcases allowed_cases hop' with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
          · left; apply Nat.eq_of_testBit_eq; intro i
            have hm:=congrArg (fun v=>v.testBit i) (nrmD_mask u d a)
            change (a'&&&d).testBit i = a'.testBit i at hm
            simp only [opD,andD,Nat.testBit_and] at hm ⊢
            cases hd' : d.testBit i <;> cases ha' : a'.testBit i <;> simp_all
          · left; apply Nat.eq_of_testBit_eq; intro i
            have hm:=congrArg (fun v=>v.testBit i) (nrmD_mask u d a)
            change (a'&&&d).testBit i = a'.testBit i at hm
            simp only [opD,orD,Nat.testBit_and,Nat.testBit_or] at hm ⊢
            cases hd' : d.testBit i <;> cases ha' : a'.testBit i <;> simp_all
          · right; apply Nat.eq_of_testBit_eq; intro i
            have hdi:=congrArg (fun v=>v.testBit i) hd
            simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit] at hdi ⊢
            cases hd' : d.testBit i <;> cases ha' : a'.testBit i <;> simp_all
          · right; apply Nat.eq_of_testBit_eq; intro i
            have hdi:=congrArg (fun v=>v.testBit i) hd
            simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit] at hdi ⊢
            cases hd' : d.testBit i <;> cases ha' : a'.testBit i <;> simp_all
        have hez' : z = opD d op' a' a':=by
          have : z = opD d op' a' c':=hez
          rw [← heq] at this; exact this
        rcases hz_eq with e | e
        · exact hzb ((hez'.trans e).symm ▸ ha'_mem)
        · exact hzp.1 (hez'.trans e)
      set rest:=ws.erase z
      have hrest_nd : rest.Nodup:=hnd.erase z
      have hrest_sub : ∀ w ∈ rest,w ∈ b.map (nrmD u d):=by
        intro w hw
        have ⟨hne,hm⟩:=hnd.mem_erase_iff.1 hw
        rcases List.mem_cons.1 (hsub w hm) with rfl | hmb
        · exact absurd rfl hne
        · exact hmb
      have hrest_prop : ∀ w ∈ rest,w ≠ 0 ∧ w ≠ d:=fun w hw=>hprop w (List.mem_of_mem_erase hw)
      have hp1 : ws.Perm (z :: rest):=List.perm_cons_erase hzm
      have h1 : RunD u d Y k (opD d op' a' c' :: rest):=by
        rw [← hez]; exact Run.perm hp1 h
      set ka:=decide (a' ∈ rest)
      set kb:=decide (c' ∈ rest)
      set tail:=(rest.erase a').erase c'
      have htail_nd : tail.Nodup:=(hrest_nd.erase a').erase c'
      have hna_tail : a' ∉ tail:=by
        intro hm; exact hrest_nd.not_mem_erase (List.mem_of_mem_erase hm)
      have hnc_tail : c' ∉ tail:=(hrest_nd.erase a').not_mem_erase
      have hna_mid : a' ∉ kept kb c' tail:=by
        rw [mem_kept]; rintro (⟨_,h⟩ | h)
        · exact hne_ac h
        · exact hna_tail h
      have hrest_perm : rest.Perm (kept ka a' (kept kb c' tail)):=by
        refine (List.perm_ext_iff_of_nodup hrest_nd (nodup_kept ka a' _ (nodup_kept kb c' _ htail_nd hnc_tail) hna_mid)).2 ?_
        intro x
        rw [mem_kept,mem_kept,(hrest_nd.erase a').mem_erase_iff,hrest_nd.mem_erase_iff]
        by_cases hxa : x = a' <;> by_cases hxc : x = c' <;> by_cases hxr : x ∈ rest <;>
          simp_all [ka,kb]
      have h2:=Run.perm (hrest_perm.cons _) h1
      have hne0 : opD d op' a' c' ≠ 0:=fun h0=>hzp.1 (hez.trans h0)
      have hned : opD d op' a' c' ≠ d:=fun h1=>hzp.2 (hez.trans h1)
      have hnm : opD d op' a' c' ∉ (a' :: c' :: tail):=by
        rw [← hez,List.mem_cons,List.mem_cons]; rintro (e | e | hm)
        · exact hzb (by simpa [z,e] using ha'_mem)
        · exact hzb (by simpa [z,e] using hc'_mem)
        · exact hnd.not_mem_erase (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
      have h3 : RunD u d Y (k + 1) (a' :: c' :: tail):=Run.two op' ka kb hop' hne0 hned hnm h2
      have hnd3 : (a' :: c' :: tail).Nodup :=
        List.nodup_cons.2 ⟨by simp [hne_ac,hna_tail],List.nodup_cons.2 ⟨hnc_tail,htail_nd⟩⟩
      refine ⟨k + 1,a' :: c' :: tail,le_rfl,hnd3,?_,?_,h3⟩
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
  · exact ⟨k,ws,by omega,hnd,hprop,fun w hw=>by
      rcases List.mem_cons.1 (hsub w hw) with rfl | hm
      · exact absurd hw hzm
      · exact hm,h⟩
theorem reach_to_run_aux {u:Bool} {d:Nat} {roots:List Nat} {p bank}
    (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (hr:NatReach u d roots p bank) :
    ∀ {Y k ws},ws.Nodup → (∀ w ∈ ws,w ≠ 0 ∧ w ≠ d) →
      (∀ w ∈ ws,w ∈ bank.map (nrmD u d)) → RunD u d Y k ws →
      ∃ k' ws',k' ≤ p + k ∧ ws'.Nodup ∧ (∀ w ∈ ws',w ≠ 0 ∧ w ≠ d) ∧
        (∀ w ∈ ws',w ∈ roots.map (nrmD u d)) ∧ RunD u d Y k' ws':=by
  induction p generalizing bank with
  | zero =>
    intro Y k ws hnd hprop hsub hrun
    subst hr
    exact ⟨k,ws,by omega,hnd,hprop,hsub,hrun⟩
  | succ p ih =>
    intro Y k ws hnd hprop hsub hrun
    obtain ⟨b,a,c,op,hop,rfl,hrb,ha,hc⟩:=hr
    have hsub' : ∀ w ∈ ws,w ∈ nrmD u d (opD d op a c) :: b.map (nrmD u d):=by
      intro w hw; simpa [List.map_cons] using hsub w hw
    obtain ⟨k1,ws1,hk1,hnd1,hprop1,hsub1,hrun1⟩:=pull_two hd hd0 hnd hprop hrun op hop ha hc hsub'
    obtain ⟨k2,ws2,hk2,hnd2,hprop2,hsub2,hrun2⟩:=ih hrb hnd1 hprop1 hsub1 hrun1
    exact ⟨k2,ws2,by omega,hnd2,hprop2,hsub2,hrun2⟩
theorem reach_to_run {u:Bool} {d:Nat} {roots:List Nat} {T:Nat} {p bank}
    (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (hT0 : T.testBit 0 = false) (hR0 : roots.all (fun r=>!r.testBit 0) = true)
    (hnc : ¬ IsConst d T) (hr:NatReach u d roots p bank) (ha : Avail u d bank T) :
    ∃ s ws,s ≤ p ∧ ws.Nodup ∧ (∀ w ∈ ws,w ∈ roots.map (·&&&d)) ∧ RunD u d (T&&&d) s ws:=by
  have hTmem : T&&&d ∈ bank.map (nrmD u d):=by
    have:=avail_nrm_mem hd hd0 ha hnc
    rwa [nrmD_of_bit0_false u d T hT0] at this
  have hprop : ∀ w ∈ [T&&&d],w ≠ 0 ∧ w ≠ d:=by
    intro w hw; rw [List.mem_singleton.1 hw]
    exact ⟨fun e=>hnc (Or.inl e),fun e=>hnc (Or.inr e)⟩
  have hsub : ∀ w ∈ [T&&&d],w ∈ bank.map (nrmD u d):=by
    intro w hw; rw [List.mem_singleton.1 hw]; exact hTmem
  obtain ⟨s,ws,hs,hnd,_,hsub',hrun⟩:=reach_to_run_aux hd hd0 hr (List.nodup_singleton _) hprop hsub Run.done
  have hrmap : roots.map (nrmD u d) = roots.map (·&&&d):=by
    apply List.map_congr_left
    intro r hr_m
    have h0:=List.all_eq_true.1 hR0 r hr_m
    simp only [Bool.not_eq_true'] at h0
    exact nrmD_of_bit0_false u d r h0
  rw [hrmap] at hsub'
  exact ⟨s,ws,by omega,hnd,hsub',hrun⟩
theorem runD_bits {u d y s ws} (hd : d&&&mask256 = d) (h : RunD u d y s ws) (i j:Nat)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (hw : ∀ w ∈ ws,w.testBit i = w.testBit j) : y.testBit i = y.testBit j:=by
  have hmi : mask256.testBit i = true:=by
    have:=congrArg (fun v=>v.testBit i) hd; simp [Nat.testBit_and,hi] at this; exact this
  have hmj : mask256.testBit j = true:=by
    have:=congrArg (fun v=>v.testBit j) hd; simp [Nat.testBit_and,hj] at this; exact this
  induction h using Run.fold with
  | done=>exact hw _ (by simp)
  | perm hp _ ih=>exact ih (fun w h=>hw w (hp.mem_iff.1 h))
  | two op ka kb hop _ _ _ _ ih =>
    apply ih; have ha:=hw _ List.mem_cons_self; have hb:=hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hm
    rcases List.mem_cons.1 hm with rfl | hr
    · rcases allowed_cases hop with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;>
        simp [opD,andD,orD,negD,ha,hb,hi,hj,hmi,hmj]
    · rw [mem_kept,mem_kept] at hr
      rcases hr with ⟨_,rfl⟩ | ⟨_,rfl⟩ | hr
      · exact ha
      · exact hb
      · exact hw _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
theorem runD_bits_le_mono {d y s ws} (h : RunD false d y s ws) (i j:Nat)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (hw : ∀ w ∈ ws,w.testBit i ≤ w.testBit j) : y.testBit i ≤ y.testBit j:=by
  induction h using Run.fold with
  | done=>exact hw _ (by simp)
  | perm hp _ ih=>exact ih (fun w h=>hw w (hp.mem_iff.1 h))
  | two op ka kb hop _ _ _ _ ih =>
    apply ih; have ha:=hw _ List.mem_cons_self; have hb:=hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hm
    rcases List.mem_cons.1 hm with rfl | hr
    · rcases allowed_cases hop with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · simp only [opD,andD,beq_self_eq_true,ite_true,Nat.testBit_and,hi,hj,Bool.and_true]; grind
      · simp only [opD,orD,beq_self_eq_true,ite_true,ite_false,Nat.testBit_and,Nat.testBit_or,hi,hj,Bool.and_true]; grind
      · contradiction
      · contradiction
    · rw [mem_kept,mem_kept] at hr
      rcases hr with ⟨_,rfl⟩ | ⟨_,rfl⟩ | hr
      · exact ha
      · exact hb
      · exact hw _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
def moveBits (tag d w:Nat):Nat :=
  ((w&&&tag) <<< d)|||((w >>> d)&&&tag) |||
    (w^^^((w&&&tag)|||(w&&&(tag <<< d))))
theorem moved (tag d i w:Nat) (h : (tag&&&(tag <<< d)) = 0) :
    (moveBits tag d w).testBit i =
      (if tag.testBit i then w.testBit (d + i)
       else if (tag <<< d).testBit i then w.testBit (i - d) else w.testBit i):=by
  have ht:=congrArg (fun v:Nat=>v.testBit i) h
  simp only [Nat.testBit_and,Nat.zero_testBit] at ht
  simp only [moveBits,Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_and,
    Nat.testBit_shiftRight,Nat.testBit_xor] at *
  by_cases hi : d ≤ i <;> simp [hi] at * <;> grind
theorem move_hom (tag d:Nat) (h : (tag&&&(tag <<< d)) = 0) (a b:Nat) :
    moveBits tag d (a&&&b) = (moveBits tag d a&&&moveBits tag d b) ∧
    moveBits tag d (a|||b) = (moveBits tag d a|||moveBits tag d b) ∧
    moveBits tag d (a^^^b) = (moveBits tag d a^^^moveBits tag d b):=by
  refine ⟨?_,?_,?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    simp only [Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,moved tag d i _ h] <;>
    split_ifs <;> simp
theorem move_zero (tag d:Nat) (h : (tag&&&(tag <<< d)) = 0) : moveBits tag d 0 = 0:=by
  apply Nat.eq_of_testBit_eq; intro i; rw [moved tag d i 0 h]; split_ifs <;> simp
def applyMoves (ms:List (Nat × Nat)) (w:Nat):Nat :=
  ms.foldl (fun acc p=>moveBits p.1 p.2 acc) w
def moveOK256 (p:Nat × Nat):Bool :=
  (p.1&&&(p.1 <<< p.2)==0)&&(moveBits p.1 p.2 mask256==mask256)
theorem applyMoves_hom (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true) :
    (∀ a b,applyMoves ms (a&&&b) = applyMoves ms a&&&applyMoves ms b) ∧
    (∀ a b,applyMoves ms (a|||b) = applyMoves ms a|||applyMoves ms b) ∧
    (∀ a b,applyMoves ms (a^^^b) = applyMoves ms a^^^applyMoves ms b) ∧
    applyMoves ms 0 = 0 ∧ applyMoves ms mask256 = mask256:=by
  induction ms with
  | nil=>exact ⟨fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl,rfl,rfl⟩
  | cons p ps ih =>
    simp only [List.all_cons,Bool.and_eq_true,moveOK256,beq_iff_eq] at hok
    obtain ⟨⟨hz,hm⟩,hps⟩:=hok
    obtain ⟨hand,hor,hxor,h0,h256⟩:=ih hps
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro a b; simp only [applyMoves,List.foldl_cons,(move_hom p.1 p.2 hz a b).1]; exact hand _ _
    · intro a b; simp only [applyMoves,List.foldl_cons,(move_hom p.1 p.2 hz a b).2.1]; exact hor _ _
    · intro a b; simp only [applyMoves,List.foldl_cons,(move_hom p.1 p.2 hz a b).2.2]; exact hxor _ _
    · simp only [applyMoves,List.foldl_cons,move_zero p.1 p.2 hz]; exact h0
    · simp only [applyMoves,List.foldl_cons,hm]; exact h256
theorem move_invol (tag d w:Nat) (h : (tag&&&(tag <<< d)) = 0) :
    moveBits tag d (moveBits tag d w) = w:=by
  apply Nat.eq_of_testBit_eq; intro i
  have ht:=congrArg (fun v:Nat=>v.testBit i) h
  simp only [Nat.testBit_and,Nat.zero_testBit] at ht
  rw [moved tag d i _ h]
  by_cases h1 : tag.testBit i = true
  · simp only [h1,ite_true,moved tag d (d + i) w h]
    have h2 : tag.testBit (d + i) = false:=by
      have htd:=congrArg (fun v:Nat=>v.testBit (d + i)) h
      simp only [Nat.testBit_and,Nat.testBit_shiftLeft,Nat.zero_testBit] at htd
      have hge : d ≤ d + i:=Nat.le_add_right d i
      have hsub : d + i - d = i:=Nat.add_sub_cancel_left d i
      simp [hge,hsub,h1] at htd; exact htd
    have h3 : (tag <<< d).testBit (d + i) = true:=by
      simp [Nat.testBit_shiftLeft,Nat.le_add_right,Nat.add_sub_cancel_left,h1]
    simp [h2,h3,Nat.add_sub_cancel_left]
  · simp only [h1,ite_false]
    by_cases h2 : (tag <<< d).testBit i = true
    · simp only [h2,ite_true,moved tag d (i - d) w h]
      rw [Nat.testBit_shiftLeft] at h2
      simp only [Bool.and_eq_true,decide_eq_true_eq] at h2
      simp [h2.2,Nat.add_sub_of_le h2.1]
    · simp [h1,h2,moved tag d i w h]
theorem applyMoves_inj (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true) :
    Function.Injective (applyMoves ms):=by
  induction ms with
  | nil=>intro a b h; exact h
  | cons p ps ih =>
    simp only [List.all_cons,Bool.and_eq_true,moveOK256,beq_iff_eq] at hok
    intro a b h
    simp only [applyMoves,List.foldl_cons] at h
    have h1:=ih hok.2 h
    have:=congrArg (moveBits p.1 p.2) h1
    rwa [move_invol p.1 p.2 a hok.1.1,move_invol p.1 p.2 b hok.1.1] at this
theorem applyMoves_opD (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    {d1 d2:Nat} (hd : applyMoves ms d2 = d1) (op a b:Nat) :
    applyMoves ms (opD d2 op a b) = opD d1 op (applyMoves ms a) (applyMoves ms b):=by
  obtain ⟨hand,hor,hxor,_,h256⟩:=applyMoves_hom ms hok
  unfold opD; split_ifs <;> simp only [andD,orD,negD,hand,hor,hxor,h256,hd]
theorem applyMoves_runD {u d Y s} (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    (hd : applyMoves ms d = d) (hY : applyMoves ms Y = Y) {ws} (h : RunD u d Y s ws) :
    RunD u d Y s (ws.map (applyMoves ms)):=by
  obtain ⟨_,_,_,h0,_⟩:=applyMoves_hom ms hok
  have hinj:=applyMoves_inj ms hok
  rw [← hY]
  induction h using Run.fold with
  | done=>exact Run.done
  | perm hp _ ih=>exact Run.perm (hp.map _) ih
  | @two s a b r op ka kb hop hne0 hned hnm _ ih =>
    have eop:=applyMoves_opD ms hok hd op a b
    have e1 : (opD d op a b :: kept ka a (kept kb b r)).map (applyMoves ms) =
        opD d op (applyMoves ms a) (applyMoves ms b) ::
          kept ka (applyMoves ms a) (kept kb (applyMoves ms b) (r.map (applyMoves ms))):=by
      simp [kept_map,eop]
    rw [e1] at ih
    refine Run.two op ka kb hop ?_ ?_ ?_ ih
    · intro e; rw [← eop] at e; exact hne0 (hinj (e.trans h0.symm))
    · intro e; rw [← eop] at e; exact hned (hinj (e.trans hd.symm))
    · rw [← eop,← List.map_cons,← List.map_cons,List.mem_map]; rintro ⟨x,hx,he⟩; exact hnm (hinj he ▸ hx)
theorem reach_map_moves {u:Bool} (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    {d1 d2:Nat} (hd1 : d1&&&mask256 = d1) (hd : applyMoves ms d2 = d1)
    {roots1 roots2:List Nat} (hroots : ∀ r ∈ roots2,Avail u d1 roots1 (applyMoves ms r)) :
    ∀ {p bank},NatReach u d2 roots2 p bank →
      ∃ bank',NatReach u d1 roots1 p bank' ∧ ∀ v ∈ bank,Avail u d1 bank' (applyMoves ms v):=by
  obtain ⟨hand,_,hxor,h0,h256⟩:=applyMoves_hom ms hok
  have hav : ∀ {b b' w},(∀ v ∈ b,Avail u d1 b' (applyMoves ms v)) →
      Avail u d2 b w → Avail u d1 b' (applyMoves ms w):=by
    intro b b' w hbb hw
    rcases hw with (hz | h1) | ⟨v,hv,he⟩ | ⟨rfl,v,hv,he⟩
    · exact Or.inl (Or.inl (by rw [← hd,← hand,hz,h0]))
    · exact Or.inl (Or.inr (by rw [← hd,← hand,h1]))
    · have hve : applyMoves ms v&&&d1 = applyMoves ms w&&&d1:=by rw [← hd,← hand,← hand,he]
      exact avail_of_eq hve (hbb v hv)
    · have hve : applyMoves ms v&&&d1 = negD d1 (applyMoves ms w)&&&d1:=by
        rw [← hd,← hand,he]; simp only [negD,hand,hxor,h256,hd,Nat.and_assoc,Nat.and_self]
      have hneg:=avail_neg hd1 (avail_of_eq hve (hbb v hv))
      exact avail_of_eq (by rw [negD_invol hd1,Nat.and_assoc,Nat.and_self]) hneg
  intro p
  induction p with
  | zero =>
    intro bank hr; subst hr
    exact ⟨roots1,rfl,hroots⟩
  | succ p ih =>
    intro bank hr
    obtain ⟨b,a,c,op,hop,rfl,hrb,ha,hc⟩:=hr
    obtain ⟨b',hrb',hbb⟩:=ih hrb
    have ha':=hav hbb ha; have hc':=hav hbb hc
    refine ⟨opD d1 op (applyMoves ms a) (applyMoves ms c) :: b',
      ⟨b',applyMoves ms a,applyMoves ms c,op,hop,rfl,hrb',ha',hc'⟩,?_⟩
    intro v hv; rcases List.mem_cons.1 hv with rfl | hv
    · exact Or.inr (Or.inl ⟨opD d1 op (applyMoves ms a) (applyMoves ms c),List.mem_cons_self,by
        rw [applyMoves_opD ms hok hd]⟩)
    · exact avail_cons _ _ (hbb v hv)
theorem lower_iso {u:Bool} {d1 d2 T1 T2 L:Nat} {roots1 roots2:List Nat}
    (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    (hd1 : d1&&&mask256 = d1) (hd : applyMoves ms d2 = d1) (hT : applyMoves ms T2 = T1)
    (hroots : roots2.all (fun r=>availB u d1 roots1 (applyMoves ms r)) = true)
    (h1 : Lower u d1 roots1 T1 L) : Lower u d2 roots2 T2 L:=by
  obtain ⟨hand,_,hxor,h0,h256⟩:=applyMoves_hom ms hok
  have hr : ∀ r ∈ roots2,Avail u d1 roots1 (applyMoves ms r):=fun r hr =>
    (availB_iff u _ _ _).1 (List.all_eq_true.1 hroots r hr)
  intro p bank hreach ha
  obtain ⟨bank',hrb',hbb⟩:=reach_map_moves ms hok hd1 hd hr hreach
  apply h1 p bank' hrb'
  rcases ha with (hz | ho) | ⟨v,hv,he⟩ | ⟨rfl,v,hv,he⟩
  · exact Or.inl (Or.inl (by rw [← hT,← hd,← hand,hz,h0]))
  · exact Or.inl (Or.inr (by rw [← hT,← hd,← hand,ho]))
  · have hve : applyMoves ms v&&&d1 = T1&&&d1:=by rw [← hT,← hd,← hand,← hand,he]
    exact avail_of_eq hve (hbb v hv)
  · have hve : applyMoves ms v&&&d1 = negD d1 T1&&&d1:=by
      rw [← hT,← hd,← hand,he]; simp only [negD,hand,hxor,h256,hd,Nat.and_assoc,Nat.and_self]
    have hneg:=avail_neg hd1 (avail_of_eq hve (hbb v hv))
    exact avail_of_eq (by rw [negD_invol hd1,Nat.and_assoc,Nat.and_self]) hneg
def pairOK (d T:Nat) (p:Nat × Nat):Bool :=
  d.testBit p.1&&d.testBit p.2&&(T.testBit p.1 != T.testBit p.2)
def essOK (d T:Nat) (roots:List Nat) (a:Nat) (p:Nat × Nat):Bool :=
  pairOK d T p&&roots.all (fun v=>(v==a)||(v.testBit p.1==v.testBit p.2))
theorem countP_ge_sublist (p:Nat → Bool) {xs ys:List Nat}
    (hnd : xs.Nodup) (hsub : ∀ a ∈ xs,a ∈ ys) (hall : ∀ a ∈ xs,p a = true) :
    xs.length ≤ ys.countP p:=by
  induction xs generalizing ys with
  | nil=>simp
  | cons a xs ih =>
    have ⟨hna,hnd'⟩:=List.nodup_cons.1 hnd
    have ham : a ∈ ys:=hsub a List.mem_cons_self
    have hperm : ys.Perm (a :: ys.erase a):=List.perm_cons_erase ham
    rw [hperm.countP_eq,List.countP_cons,hall a List.mem_cons_self]
    have ih':=ih hnd' (fun x hx=>by
      have hne : x ≠ a:=fun e=>hna (e ▸ hx)
      exact (List.mem_erase_of_ne hne).2 (hsub x (List.mem_cons_of_mem _ hx)))
      (fun x hx=>hall x (List.mem_cons_of_mem _ hx))
    simp only [ite_true,List.length_cons]
    omega
theorem lower_slice {u:Bool} {d dSub T TSub L:Nat} {roots rootsSub:List Nat}
    (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (hT0 : T.testBit 0 = false) (hR0 : roots.all (fun r=>!r.testBit 0) = true)
    (hdSub : dSub&&&mask256 = dSub) (hsub : dSub&&&d = dSub)
    (hT : T&&&dSub = TSub&&&dSub)
    (hnc : isConstB d T = false) (hncSub : isConstB dSub TSub = false)
    (hcov : roots.all (availB u dSub rootsSub) = true)
    (singles:List (Nat × Nat × Nat))
    (hs_nd : (singles.map Prod.fst).Nodup)
    (hs_ok : singles.all (fun e=>isConstB dSub e.1&&essOK d (T&&&d) (roots.map (·&&&d)) e.1 e.2) = true)
    (hprior : Lower u dSub rootsSub TSub L) :
    Lower u d roots T (L + singles.length):=by
  have hnc' : ¬ IsConst d T:=fun h=>by rw [(isConstB_iff _ _).2 h] at hnc; contradiction
  have hncSub' : ¬ IsConst dSub (T&&&d):=by
    intro h
    have e : (T&&&d)&&&dSub = TSub&&&dSub:=by
      rw [Nat.and_assoc,Nat.and_comm d dSub,hsub,hT]
    rcases h with h0 | h1
    · exact absurd ((isConstB_iff _ _).2 (Or.inl (e.symm.trans h0))) (by simp [hncSub])
    · exact absurd ((isConstB_iff _ _).2 (Or.inr (e.symm.trans h1))) (by simp [hncSub])
  intro p bank hr ha
  obtain ⟨s,ws,hs_le,hnd,hws_sub,hrun⟩:=reach_to_run hd hd0 hT0 hR0 hnc' hr ha
  have hws_av : ∀ w ∈ ws,Avail u dSub rootsSub w:=by
    intro w hw
    obtain ⟨r,hr_m,rfl⟩:=List.mem_map.1 (hws_sub w hw)
    have hav:=(availB_iff u _ _ _).1 (List.all_eq_true.1 hcov r hr_m)
    exact avail_of_eq (by rw [Nat.and_assoc,Nat.and_comm d dSub,hsub]) hav
  obtain ⟨q,next,hq,ht,hle⟩:=contraction hdSub hsub hncSub' hrun (p:=0) (bank:=rootsSub) rfl hws_av
  have hTSub_av : Avail u dSub next TSub:=avail_of_eq (by
    rw [Nat.and_assoc,Nat.and_comm d dSub,hsub,hT]) ht
  have hL : L ≤ q:=hprior q next hq hTSub_av
  have hsin_mem : ∀ a ∈ singles.map Prod.fst,a ∈ ws:=by
    intro a ha
    obtain ⟨⟨a',r1,r2⟩,hm,rfl⟩:=List.mem_map.1 ha
    have hok:=List.all_eq_true.1 hs_ok (a',r1,r2) hm
    simp only [Bool.and_eq_true,essOK,pairOK,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at hok
    obtain ⟨_,⟨⟨hr1,hr2⟩,hdiff⟩,hiso⟩:=hok
    by_contra hnot
    apply hdiff
    apply runD_bits hd hrun r1 r2 hr1 hr2
    intro w hw
    rcases hiso w (hws_sub w hw) with rfl | heq
    · exact absurd hw hnot
    · exact heq
  have hsin_const : ∀ a ∈ singles.map Prod.fst,isConstB dSub a = true:=by
    intro a ha
    obtain ⟨⟨a',r1,r2⟩,hm,rfl⟩:=List.mem_map.1 ha
    have hok:=List.all_eq_true.1 hs_ok _ hm
    simp only [Bool.and_eq_true] at hok
    exact hok.1
  have hcnt:=countP_ge_sublist (isConstB dSub) hs_nd hsin_mem hsin_const
  simp only [List.length_map] at hcnt
  omega
def stepOp (u:Bool) (d:Nat) (st:Nat × List Nat) (g:Nat × Nat × Nat):Nat × List Nat :=
  if allowedB u g.1 then
    let om:=opD d g.1 g.2.1 g.2.2
    if availB u d st.2 om then st
    else if availB u d st.2 g.2.1&&availB u d st.2 g.2.2 then (st.1 + 1,om :: st.2)
    else st
  else st
def runOps (u:Bool) (d:Nat) (st:Nat × List Nat) (ops:List (Nat × Nat × Nat)):Nat × List Nat :=
  ops.foldl (stepOp u d) st
theorem getD_mem {xs:List Nat} {i:Nat} (hi : i < xs.length) : xs.getD i 0 ∈ xs:=by
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
  exact List.getElem_mem hi
theorem avail_of_availB_pool {u:Bool} {d:Nat} (hd : d&&&mask256 = d)
    {bank pool:List Nat} (hsup : ∀ v ∈ pool,Avail u d bank v) {w:Nat}
    (hb : availB u d pool w = true) : Avail u d bank w:=by
  rcases (availB_iff u d pool w).1 hb with hc | ⟨v,hv,he⟩ | ⟨rfl,v,hv,he⟩
  · exact Or.inl hc
  · exact avail_of_eq he (hsup v hv)
  · have hneg:=avail_neg hd (hsup v hv)
    have he' : negD d v&&&d = w&&&d:=by
      rw [← negD_mask,he,negD_invol hd,Nat.and_assoc,Nat.and_self]
    exact avail_of_eq he' hneg
theorem stepOp_sound {u:Bool} {d:Nat} (hd : d&&&mask256 = d) {roots bank:List Nat}
    (st:Nat × List Nat) (g:Nat × Nat × Nat)
    (hr:NatReach u d roots st.1 bank) (hsup : ∀ v ∈ st.2,Avail u d bank v) :
    ∃ bank',NatReach u d roots (stepOp u d st g).1 bank' ∧ ∀ v ∈ (stepOp u d st g).2,Avail u d bank' v:=by
  unfold stepOp; dsimp only
  split
  · rename_i hop
    split
    · exact ⟨bank,hr,hsup⟩
    · split
      · rename_i hab
        simp only [Bool.and_eq_true] at hab
        have ha:=avail_of_availB_pool hd hsup hab.1
        have hb:=avail_of_availB_pool hd hsup hab.2
        refine ⟨opD d g.1 g.2.1 g.2.2 :: bank,⟨bank,g.2.1,g.2.2,g.1,hop,rfl,hr,ha,hb⟩,?_⟩
        intro v hv
        rcases List.mem_cons.1 hv with rfl | hv
        · exact Or.inr (Or.inl ⟨_,List.mem_cons_self,rfl⟩)
        · exact avail_cons _ _ (hsup v hv)
      · exact ⟨bank,hr,hsup⟩
  · exact ⟨bank,hr,hsup⟩
theorem runOps_sound {u:Bool} {d:Nat} (hd : d&&&mask256 = d) {roots:List Nat}
    (ops:List (Nat × Nat × Nat)) :
    ∀ (st:Nat × List Nat) (bank:List Nat),
      NatReach u d roots st.1 bank → (∀ v ∈ st.2,Avail u d bank v) →
      ∃ bank',NatReach u d roots (runOps u d st ops).1 bank' ∧ ∀ v ∈ (runOps u d st ops).2,Avail u d bank' v:=by
  induction ops with
  | nil=>intro st bank hr hsup; exact ⟨bank,hr,hsup⟩
  | cons g ops ih =>
    intro st bank hr hsup
    obtain ⟨bank1,hr1,hsup1⟩:=stepOp_sound hd st g hr hsup
    exact ih (stepOp u d st g) bank1 hr1 hsup1
def checkPool (u:Bool) (dSub LSub s:Nat) (st:Nat × List Nat) (ws:List Nat):Bool :=
  decide (s + st.1 < LSub + ws.countP (isConstB dSub))&&ws.all (availB u dSub st.2)
theorem checkPool_sound {u:Bool} {d dSub T TSub LSub s:Nat} {rootsSub ws:List Nat}
    (hdSub : dSub&&&mask256 = dSub) (hsub : dSub&&&d = dSub)
    (hT : T&&&dSub = TSub&&&dSub) (hncSub : isConstB dSub TSub = false)
    (hprior : Lower u dSub rootsSub TSub LSub)
    (st:Nat × List Nat) (bank:List Nat)
    (hrb:NatReach u dSub rootsSub st.1 bank) (hsb : ∀ v ∈ st.2,Avail u dSub bank v)
    (hchk : checkPool u dSub LSub s st ws = true) :
    ¬ RunD u d (T&&&d) s ws:=by
  intro hrun
  simp only [checkPool,Bool.and_eq_true,decide_eq_true_eq] at hchk
  obtain ⟨hineq,hall⟩:=hchk
  have hws_av : ∀ w ∈ ws,Avail u dSub bank w:=fun w hw =>
    avail_of_availB_pool hdSub hsb (List.all_eq_true.1 hall w hw)
  have hnc' : ¬ IsConst dSub (T&&&d):=by
    intro h; have e : (T&&&d)&&&dSub = TSub&&&dSub:=by rw [Nat.and_assoc,Nat.and_comm d dSub,hsub,hT]
    rcases h with h0 | h1
    · exact absurd ((isConstB_iff _ _).2 (Or.inl (e.symm.trans h0))) (by simp [hncSub])
    · exact absurd ((isConstB_iff _ _).2 (Or.inr (e.symm.trans h1))) (by simp [hncSub])
  obtain ⟨q,next,hq,ht,hle⟩:=contraction hdSub hsub hnc' hrun hrb hws_av
  have hL:=hprior q next hq (avail_of_eq (by rw [Nat.and_assoc,Nat.and_comm d dSub,hsub,hT]) ht)
  omega
def subValidB (d dSub T TSub:Nat):Bool :=
  (dSub&&&mask256==dSub)&&(dSub&&&d==dSub)&&(T&&&dSub==TSub&&&dSub)&&!(isConstB dSub TSub)
theorem cpcs {u:Bool} {d dSub T TSub LSub s:Nat} {rootsSub ws:List Nat}
    (hv : subValidB d dSub T TSub = true)
    (hprior : Lower u dSub rootsSub TSub LSub)
    (ops:List (Nat × Nat × Nat)) (g:Nat × Nat × Nat)
    (hchk : checkPool u dSub LSub s (stepOp u dSub (runOps u dSub (0,rootsSub) ops) g) ws = true) :
    ¬ RunD u d (T&&&d) s ws:=by
  simp only [subValidB,Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true'] at hv
  have hsup0 : ∀ v ∈ rootsSub,Avail u dSub rootsSub v:=fun v hv=>Or.inr (Or.inl ⟨v,hv,rfl⟩)
  obtain ⟨bank1,hr1,hsup1⟩:=runOps_sound hv.1.1.1 ops (0,rootsSub) rootsSub rfl hsup0
  obtain ⟨bank2,hr2,hsup2⟩:=stepOp_sound hv.1.1.1 _ g hr1 hsup1
  exact checkPool_sound hv.1.1.1 hv.1.1.2 hv.1.2 hv.2 hprior _ bank2 hr2 hsup2 hchk
theorem checkRootSub_sound {u:Bool} {d dSub T TSub LSub s:Nat} {rootsSub ws:List Nat}
    (hv : subValidB d dSub T TSub = true)
    (hprior : Lower u dSub rootsSub TSub LSub)
    (hchk : checkPool u dSub LSub s (0,rootsSub) ws = true) :
    ¬ RunD u d (T&&&d) s ws:=by
  simp only [subValidB,Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true'] at hv
  exact checkPool_sound hv.1.1.1 hv.1.1.2 hv.1.2 hv.2 hprior (0,rootsSub) rootsSub rfl (fun v hv=>Or.inr (Or.inl ⟨v,hv,rfl⟩)) hchk
def coversP (u:Bool) (pairs:List (Nat × Nat)) (ws:List Nat):Bool :=
  if !u then
    pairs.all (fun p=>ws.any (fun w=>!w.testBit p.1&&w.testBit p.2))
  else
    pairs.all (fun p=>ws.any (fun w=>w.testBit p.1 != w.testBit p.2))
theorem coversP_ok {u:Bool} {d T s:Nat} (hd : d&&&mask256 = d)
    (pairs:List (Nat × Nat))
    (hpairs : pairs.all (fun p=>d.testBit p.1&&d.testBit p.2&&!(T&&&d).testBit p.1&&(T&&&d).testBit p.2) = true)
    {ws:List Nat} (h : RunD u d (T&&&d) s ws) : coversP u pairs ws = true:=by
  cases u with
  | false =>
    simp only [coversP,Bool.not_false,ite_true,List.all_eq_true,List.any_eq_true]
    intro ⟨u1,v1⟩ hm
    have hp:=List.all_eq_true.1 hpairs (u1,v1) hm
    simp only [Bool.and_eq_true,Bool.not_eq_true'] at hp
    by_contra! hall
    have hle:=runD_bits_le_mono h v1 u1 hp.1.1.2 hp.1.1.1 (fun w hw=>by
      have hbad:=hall w hw
      cases hu : w.testBit u1 <;> cases hv : w.testBit v1 <;> simp_all)
    rw [hp.1.2,hp.2] at hle; contradiction
  | true =>
    simp only [coversP,Bool.not_true,Bool.false_eq_true,ite_false,List.all_eq_true,List.any_eq_true,bne_iff_ne]
    intro ⟨u1,v1⟩ hm
    have hp:=List.all_eq_true.1 hpairs (u1,v1) hm
    simp only [Bool.and_eq_true,Bool.not_eq_true'] at hp
    by_contra! hall
    have heq:=runD_bits hd h u1 v1 hp.1.1.1 hp.1.1.2 hall
    rw [hp.1.2,hp.2] at heq; contradiction
def unorientedCov (pairs:List (Nat × Nat)) (ws:List Nat):Bool :=
  pairs.all (fun p=>ws.any (fun w=>w.testBit p.1 != w.testBit p.2))
theorem unorientedCov_ok {u:Bool} {d T s:Nat} (hd : d&&&mask256 = d)
    (pairs:List (Nat × Nat))
    (hpairs : pairs.all (fun p=>d.testBit p.1&&d.testBit p.2&&((T&&&d).testBit p.1 != (T&&&d).testBit p.2)) = true)
    {ws:List Nat} (h : RunD u d (T&&&d) s ws) : unorientedCov pairs ws = true:=by
  simp only [unorientedCov,List.all_eq_true,List.any_eq_true,bne_iff_ne]
  intro ⟨u1,v1⟩ hm
  have hp:=List.all_eq_true.1 hpairs (u1,v1) hm
  simp only [Bool.and_eq_true,bne_iff_ne] at hp
  by_contra! hall
  have heq:=runD_bits hd h u1 v1 hp.1.1 hp.1.2 hall
  exact hp.2 heq
def maskP (m:Nat):Nat:=2 ^ m - 1
def projBit (rs:List Nat) (w:Nat):Nat :=
  rs.foldr (fun r acc=>(acc <<< 1)|||(if w.testBit r then 1 else 0)) 0
theorem projBit_testBit (rs:List Nat) (w:Nat) (i:Nat) :
    (projBit rs w).testBit i = if h : i < rs.length then w.testBit rs[i] else false:=by
  induction rs generalizing i with
  | nil=>simp [projBit]
  | cons r rs ih =>
    cases i with
    | zero =>
      simp only [projBit,List.foldr_cons,Nat.testBit_or,Nat.testBit_shiftLeft,
        Nat.not_le.2 Nat.zero_lt_one,decide_false,Bool.false_and,Bool.false_or,
        List.length_cons,Nat.zero_lt_succ,dite_true,List.getElem_cons_zero]
      cases w.testBit r <;> simp
    | succ i =>
      simp only [projBit,List.foldr_cons,Nat.testBit_or,Nat.testBit_shiftLeft,
        Nat.succ_le_succ (Nat.zero_le i),decide_true,Bool.true_and,Nat.add_sub_cancel,
        List.length_cons,Nat.succ_lt_succ_iff,List.getElem_cons_succ]
      have h1 : (if w.testBit r = true then 1 else 0).testBit (i + 1) = false:=by
        cases w.testBit r <;> simp [Nat.testBit_succ]
      rw [h1,Bool.or_false]; exact ih i
def opP (mp op:Nat) (pa pb:Nat):Nat :=
  if op==0 then pa&&&pb
  else if op==1 then pa|||pb
  else if op==2 then pa&&&(pb^^^mp)
  else (pa^^^mp)&&&pb
theorem projBit_opD {dm:Nat} (hd : dm&&&mask256 = dm) {rs:List Nat}
    (hrs : ∀ r ∈ rs,dm.testBit r = true) (op a b:Nat) :
    projBit rs (opD dm op a b) = opP (maskP rs.length) op (projBit rs a) (projBit rs b):=by
  apply Nat.eq_of_testBit_eq; intro i
  by_cases hi : i < rs.length
  · have hdr:=hrs rs[i] (List.getElem_mem hi)
    have hmr : mask256.testBit rs[i] = true:=by
      have:=congrArg (fun v=>v.testBit rs[i]) hd; simp [Nat.testBit_and,hdr] at this; exact this
    unfold opD opP
    split_ifs <;>
      simp only [projBit_testBit,hi,dite_true,andD,orD,negD,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,
        maskP,Nat.testBit_two_pow_sub_one,decide_true,hdr,hmr,Bool.and_true,Bool.xor_true] <;>
      (cases a.testBit rs[i] <;> cases b.testBit rs[i] <;> rfl)
  · unfold opD opP
    split_ifs <;>
      simp only [projBit_testBit,hi,dite_false,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,
        maskP,Nat.testBit_two_pow_sub_one,decide_false,Bool.false_and,Bool.and_false,Bool.false_or,Bool.xor_false]
theorem foldl_or_testBit {α : Type} (g : α → Nat) (xs:List α) (acc i:Nat) :
    (xs.foldl (fun a x=>a|||g x) acc).testBit i = (acc.testBit i||xs.any (fun x=>(g x).testBit i)):=by
  induction xs generalizing acc with
  | nil=>simp
  | cons x xs ih =>
    simp only [List.foldl_cons,ih,Nat.testBit_or,List.any_cons,Bool.or_assoc]
def colB (mp:Nat) (oriented:Bool) (p:Nat × Nat):Nat :=
  if oriented then (p.1^^^mp)&&&p.2 else p.1^^^p.2
def coversD (u:Bool) (mp:Nat) (dws:List (Nat × Nat × Nat)):Bool :=
  dws.foldl (fun acc d=>acc|||colB mp (!u) d.2) 0==mp
theorem coversD_eq (u:Bool) (pairs:List (Nat × Nat)) (ws:List Nat) :
    coversD u (maskP pairs.length) (ws.map (fun w=>(w,projBit (pairs.map Prod.fst) w,projBit (pairs.map Prod.snd) w))) =
      coversP u pairs ws:=by
  set r1s:=pairs.map Prod.fst
  set r2s:=pairs.map Prod.snd
  set mp:=maskP pairs.length
  have hr1 : r1s.length = pairs.length:=List.length_map _
  have hr2 : r2s.length = pairs.length:=List.length_map _
  unfold coversD coversP
  cases u with
  | false =>
    simp only [Bool.not_false,colB,ite_true]
    apply Bool.eq_iff_iff.2; rw [beq_iff_eq,List.all_eq_true]
    constructor
    · intro heq pr hpr
      obtain ⟨i,hi,rfl⟩:=List.mem_iff_getElem.1 hpr
      have hb:=congrArg (fun v=>v.testBit i) heq
      rw [foldl_or_testBit,Nat.zero_testBit,Bool.false_or,List.any_map] at hb
      simp only [mp,maskP,Nat.testBit_two_pow_sub_one,hi,decide_true] at hb
      obtain ⟨w,hw,hwt⟩:=List.any_eq_true.1 hb
      simp only [Function.comp_def,Nat.testBit_and,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_true,
        Nat.testBit_two_pow_sub_one,decide_true,Bool.xor_true] at hwt
      exact List.any_eq_true.2 ⟨w,hw,by simpa [r1s,r2s] using hwt⟩
    · intro hall
      apply Nat.eq_of_testBit_eq; intro i
      rw [foldl_or_testBit,Nat.zero_testBit,Bool.false_or,List.any_map]
      simp only [mp,maskP,Nat.testBit_two_pow_sub_one]
      by_cases hi : i < pairs.length
      · simp only [hi,decide_true]
        obtain ⟨w,hw,hwt⟩:=List.any_eq_true.1 (hall pairs[i] (List.getElem_mem hi))
        exact List.any_eq_true.2 ⟨w,hw,by
          simp only [Function.comp_def,Nat.testBit_and,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_true,
            Nat.testBit_two_pow_sub_one,decide_true,Bool.xor_true,r1s,r2s,List.getElem_map]
          exact hwt⟩
      · simp only [hi,decide_false,List.any_eq_false]
        intro w _
        simp only [Function.comp_def,Nat.testBit_and,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_false,
          Nat.testBit_two_pow_sub_one,decide_false,Bool.xor_false,Bool.and_false,not_false_eq_true,Bool.false_eq_true]
  | true =>
    simp only [Bool.not_true,colB,Bool.false_eq_true,ite_false]
    apply Bool.eq_iff_iff.2; rw [beq_iff_eq,List.all_eq_true]
    constructor
    · intro heq pr hpr
      obtain ⟨i,hi,rfl⟩:=List.mem_iff_getElem.1 hpr
      have hb:=congrArg (fun v=>v.testBit i) heq
      rw [foldl_or_testBit,Nat.zero_testBit,Bool.false_or,List.any_map] at hb
      simp only [mp,maskP,Nat.testBit_two_pow_sub_one,hi,decide_true] at hb
      obtain ⟨w,hw,hwt⟩:=List.any_eq_true.1 hb
      simp only [Function.comp_def,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_true] at hwt
      exact List.any_eq_true.2 ⟨w,hw,by simpa [r1s,r2s,bne] using hwt⟩
    · intro hall
      apply Nat.eq_of_testBit_eq; intro i
      rw [foldl_or_testBit,Nat.zero_testBit,Bool.false_or,List.any_map]
      simp only [mp,maskP,Nat.testBit_two_pow_sub_one]
      by_cases hi : i < pairs.length
      · simp only [hi,decide_true]
        obtain ⟨w,hw,hwt⟩:=List.any_eq_true.1 (hall pairs[i] (List.getElem_mem hi))
        exact List.any_eq_true.2 ⟨w,hw,by
          simp only [Function.comp_def,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_true,r1s,r2s,List.getElem_map]
          simpa [bne] using hwt⟩
      · simp only [hi,decide_false,List.any_eq_false]
        intro w _
        simp only [Function.comp_def,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_false,
          Bool.xor_false,Bool.false_eq_true,not_false_eq_true]
theorem erase_map_inj {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (hinj : Function.Injective f) (xs:List α) (a : α) :
    (xs.map f).erase (f a) = (xs.erase a).map f:=by
  induction xs with
  | nil=>rfl
  | cons x xs ih =>
    simp only [List.map_cons,List.erase_cons]
    by_cases h : x = a
    · subst h; simp
    · have hf : (f x==f a) = false:=beq_false_of_ne (fun e=>h (hinj e))
      have hx : (x==a) = false:=beq_false_of_ne h
      simp [hf,hx,ih]
def value6 (a b c d e f:Bool):Nat :=
  let x:=b.toNat + c.toNat
  let y:=(!e).toNat + (!f).toNat
  if a then (if d then y else max x (max y (x + y - 1))) else (if d then 0 else x)
theorem value6_and : ∀ a b c d e f g h i j l m:Bool,
    value6 (a&&g) (b&&h) (c&&i) (d&&j) (e&&l) (f&&m)
      ≤ value6 a b c d e f + value6 g h i j l m:=by decide +kernel
theorem value6_or : ∀ a b c d e f g h i j l m:Bool,
    value6 (a||g) (b||h) (c||i) (d||j) (e||l) (f||m)
      ≤ value6 a b c d e f + value6 g h i j l m:=by decide +kernel
theorem score_bound {d y s ws} (h : RunD false d y s ws) (hl : ws.length = s + 1)
    (v:Nat → Nat) (hand : ∀ a b,v (andD d a b) ≤ v a + v b)
    (hor : ∀ a b,v (orD d a b) ≤ v a + v b) : v y ≤ (ws.map v).sum:=by
  induction h using Run.fold with
  | done=>simp
  | perm p _ ih=>rw [← (p.map v).sum_eq]; exact ih (p.length_eq.trans hl)
  | two op ka kb hop _ _ _ h ih =>
    have hh:=run_len h; cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih':=ih (by simp [kept]; omega)
    rcases allowed_cases hop with rfl | rfl | ⟨hc,_⟩ | ⟨hc,_⟩
    · simp only [opD,beq_self_eq_true,ite_true,kept,Bool.false_eq_true,ite_false,List.map_cons,List.sum_cons] at ih' ⊢
      grw [← Nat.add_assoc,← hand]; exact ih'
    · simp only [opD,beq_self_eq_true,ite_true,ite_false,kept,Bool.false_eq_true,List.map_cons,List.sum_cons] at ih' ⊢
      grw [← Nat.add_assoc,← hor]; exact ih'
    · contradiction
    · contradiction
def eval6 (a b c d e f v:Nat):=value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)
theorem eval6_bound {dm y s ws} (h : RunD false dm y s ws) (hl : ws.length = s + 1)
    (a b c d e f:Nat)
    (ha : dm.testBit a = true) (hb : dm.testBit b = true) (hc : dm.testBit c = true)
    (hd : dm.testBit d = true) (he : dm.testBit e = true) (hf : dm.testBit f = true) :
    eval6 a b c d e f y ≤ (ws.map (eval6 a b c d e f)).sum:=by
  apply score_bound h hl
  · intro v w
    simpa only [eval6,andD,Nat.testBit_and,ha,hb,hc,hd,he,hf,Bool.and_true] using value6_and
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
  · intro v w
    simpa only [eval6,orD,Nat.testBit_and,Nat.testBit_or,ha,hb,hc,hd,he,hf,Bool.and_true] using value6_or
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
def sumBelow (v:Nat → Nat):List Nat → Nat → Bool
  | [],n=>n != 0
  | w :: ws,n=>decide (v w < n)&&sumBelow v ws (n - v w)
theorem sumBelow_iff (v:Nat → Nat) (ws:List Nat) (n:Nat) :
    sumBelow v ws n = true ↔ (ws.map v).sum < n:=by
  induction ws generalizing n with
  | nil=>simp [sumBelow]
  | cons w ws ih=>rw [sumBelow,Bool.and_eq_true,decide_eq_true_eq,ih,List.map_cons,List.sum_cons]; omega
def scoreCheck (dm y s:Nat) (ws:List Nat) (code:Nat):Bool :=
  let a:=code&&&255
  let b:=(code >>> 8)&&&255
  let c:=(code >>> 16)&&&255
  let d:=(code >>> 24)&&&255
  let e:=(code >>> 32)&&&255
  let f:=(code >>> 40)&&&255
  dm.testBit a&&dm.testBit b&&dm.testBit c&&dm.testBit d&&dm.testBit e&&dm.testBit f &&
    ws.length==s + 1&&sumBelow (eval6 a b c d e f) ws (eval6 a b c d e f y)
theorem scoreCheck_no {dm y s ws} (h : RunD false dm y s ws) (code:Nat) :
    scoreCheck dm y s ws code = false:=by
  unfold scoreCheck
  by_cases hok : dm.testBit (code&&&255) = true ∧ dm.testBit ((code >>> 8)&&&255) = true ∧
      dm.testBit ((code >>> 16)&&&255) = true ∧ dm.testBit ((code >>> 24)&&&255) = true ∧
      dm.testBit ((code >>> 32)&&&255) = true ∧ dm.testBit ((code >>> 40)&&&255) = true ∧
      ws.length = s + 1
  · obtain ⟨ha,hb,hc,hd,he,hf,hl⟩:=hok
    simp only [ha,hb,hc,hd,he,hf,hl,beq_self_eq_true,Bool.true_and]
    by_contra hbad
    have hsum:=(sumBelow_iff _ _ _).1 (Bool.eq_true_of_not_eq_false hbad)
    exact (Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _ ha hb hc hd he hf)) hsum
  · by_contra hbad
    have ht:=Bool.eq_true_of_not_eq_false hbad
    simp only [Bool.and_eq_true,beq_iff_eq] at ht
    exact hok ⟨ht.1.1.1.1.1.1.1,ht.1.1.1.1.1.1.2,ht.1.1.1.1.1.2,ht.1.1.1.1.2,ht.1.1.1.2,ht.1.1.2,ht.1.2⟩
def scr (u:Bool) (dm y s:Nat) (pool:List Nat) (zs:List Nat):Bool :=
  !u&&zs.length==s + 1&&pool.any (scoreCheck dm y s zs)
theorem scr_no {u:Bool} {dm y s:Nat} (pool:List Nat) {zs:List Nat}
    (h : RunD u dm y s zs) : scr u dm y s pool zs = false:=by
  cases u with
  | true=>simp [scr]
  | false =>
    unfold scr; simp only [Bool.not_false,Bool.true_and]
    rw [Bool.and_eq_false_iff]; right; rw [List.any_eq_false]
    intro x _; rw [scoreCheck_no h x]; simp
def opsOf (u:Bool):List Nat:=if u then [0,1,2,3] else [0,1]
theorem mem_opsOf {u:Bool} {op:Nat} (hop : allowedB u op = true) : op ∈ opsOf u:=by
  rcases allowed_cases hop with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> decide
  · cases u <;> decide
  · decide
  · decide
def nextD (u:Bool) (dm:Nat) (slack:Nat) (ws:List Nat) (f : (Nat × Nat × Nat) → List Nat → Bool):Bool :=
  ws.any fun a =>
    let ra:=ws.erase a
    ra.any fun b =>
      a ≤ b&&(let r:=ra.erase b
        (opsOf u).any fun op =>
          let w:=opD dm op a b
          let g:=(op,a,b)
          w != 0&&w != dm&&!(ws.contains w) &&
            (f g (w :: r)||(slack ≥ 1&&(f g (w :: a :: r)||f g (w :: b :: r))) ||
              (slack ≥ 2&&f g (w :: a :: b :: r))))
theorem nextD_two_sorted {u:Bool} {dm y a b rest} {op:Nat} {ka kb:Bool} {s ws}
    (hop : allowedB u op = true) (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h0 : opD dm op a b ≠ 0) (hd : opD dm op a b ≠ dm) (hnm : opD dm op a b ∉ (a :: b :: rest))
    (h : RunD u dm y s (opD dm op a b :: kept ka a (kept kb b rest)))
    (f : (Nat × Nat × Nat) → List Nat → Bool) (hf : ∀ g ys,RunD u dm y s ys → f g ys = true) :
    nextD u dm (s + 2 - ws.length) ws f = true:=by
  have ha:=p.mem_iff.1 List.mem_cons_self
  have pp:=(p.trans (List.perm_cons_erase ha)).cons_inv
  have hb:=pp.mem_iff.1 List.mem_cons_self
  have pr:=(pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh:=run_len h; have hl:=p.length_eq; simp only [List.length_cons] at hl hh
  have hnc : ws.contains (opD dm op a b) = false:=by
    cases h : ws.contains (opD dm op a b) with
    | false=>rfl
    | true=>exact absurd (p.mem_iff.2 (by simpa using h)) hnm
  have h0b : (opD dm op a b != 0) = true:=bne_iff_ne.2 h0
  have hdb : (opD dm op a b != dm) = true:=bne_iff_ne.2 hd
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  apply List.any_eq_true.2 ⟨b,hb,?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab,?_⟩
  apply List.any_eq_true.2 ⟨op,mem_opsOf hop,?_⟩
  simp only [h0b,hdb,hnc,Bool.not_false,Bool.true_and]
  have ht:=hf (op,a,b) _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht,Bool.true_or,Bool.or_true,Bool.and_true] <;>
    first | (simp [show 2 ≤ s + 2 - ws.length by omega]) | (simp [show 1 ≤ s + 2 - ws.length by omega])
theorem nextD_two {u:Bool} {dm y a b rest} {op:Nat} {ka kb:Bool} {s ws}
    (hop : allowedB u op = true) (p : (a :: b :: rest).Perm ws)
    (h0 : opD dm op a b ≠ 0) (hd : opD dm op a b ≠ dm) (hnm : opD dm op a b ∉ (a :: b :: rest))
    (h : RunD u dm y s (opD dm op a b :: kept ka a (kept kb b rest)))
    (f : (Nat × Nat × Nat) → List Nat → Bool) (hf : ∀ g ys,RunD u dm y s ys → f g ys = true) :
    nextD u dm (s + 2 - ws.length) ws f = true:=by
  rcases le_total a b with hab | hba
  · exact nextD_two_sorted hop hab p h0 hd hnm h f hf
  · have he : opD dm op a b = opD dm (flipOp op) b a:=opD_comm dm hop a b
    have hnm' : opD dm (flipOp op) b a ∉ (b :: a :: rest):=by
      rw [← he]; intro hm; exact hnm ((List.Perm.swap _ _ _).mem_iff.1 hm)
    apply nextD_two_sorted (op:=flipOp op) (ka:=kb) (kb:=ka) (flipOp_allowed hop) hba
      ((List.Perm.swap _ _ _).trans p) (he ▸ h0) (he ▸ hd) hnm' _ f hf
    rw [he] at h; apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]; exact List.Perm.swap _ _ _
theorem nextD_complete {u:Bool} {dm y t ws} (h : RunD u dm y t ws) :
    ∀ s,t = s + 1 → ∀ zs,ws.Perm zs → ∀ f : (Nat × Nat × Nat) → List Nat → Bool,
      (∀ g ys,RunD u dm y s ys → f g ys = true) →
      nextD u dm (s + 2 - zs.length) zs f = true:=by
  induction h using Run.fold with
  | done=>simp
  | perm p _ ih=>intro s he zs q; exact ih s he zs (p.trans q)
  | two op ka kb hop h0 hd hnm h _=>intro s he zs p f hf; cases he; exact nextD_two hop p h0 hd hnm h f hf
def span (f:Nat → Bool):Nat → Nat → Bool
  | 0,_=>true
  | n + 1,i=>f i&&span f n (i + 1)
theorem span_ok {f n o} (h : span f n o = true) : ∀ i,o ≤ i → i < o + n → f i = true:=by
  induction n generalizing o with
  | zero=>omega
  | succ n ih =>
    simp only [span,Bool.and_eq_true] at h; intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)
def fld (T w i:Nat):Nat :=
  (T >>> (w * i))&&&(if w==32 then 4294967295 else if w==52 then 4503599627370495 else if w==256 then mask256 else 2 ^ w - 1)
def bsr (read:Nat → Nat) (h:Nat):Nat → Nat → Nat → Nat
  | 0,lo,_=>lo
  | f + 1,lo,hi =>
    if lo + 1 < hi then
      (if read ((lo + hi) / 2) ≤ h then bsr read h f ((lo + hi) / 2) hi
       else bsr read h f lo ((lo + hi) / 2))
    else lo
def hw256 (seed w:Nat):Nat :=
  let x:=(((w&&&4294967295)^^^seed) * 2654435761 +
            (((w >>> 32)&&&4294967295)^^^seed) * 2246822519 +
            (((w >>> 64)&&&4294967295)^^^seed) * 3266489917 +
            (((w >>> 96)&&&4294967295)^^^seed) * 668265263 +
            (((w >>> 128)&&&4294967295)^^^seed) * 374761393 +
            (((w >>> 160)&&&4294967295)^^^seed) * 1274126177 +
            (((w >>> 192)&&&4294967295)^^^seed) * 2869860233 +
            (((w >>> 224)&&&4294967295)^^^seed) * 1640531527)&&&4294967295
  let y:=((x^^^(x >>> 16)) * 2246822519)&&&4294967295
  ((y^^^(y >>> 13)) * 3266489917)&&&4294967295
def hz (seed:Nat):List Nat → Nat
  | []=>0
  | w :: t=>hw256 seed w + hz seed t
def hk (seed:Nat) (zs:List Nat):Nat:=hz seed zs&&&1048575
def found (S:Nat → Nat → List Nat) (N:Nat → Nat) (idx:Nat → List Nat → Nat)
    (s:Nat) (zs:List Nat):Bool :=
  decide (idx s zs < N s)&&zs.isPerm (S s (idx s zs))
def foundH (S:Nat → Nat → List Nat) (N:Nat → Nat) (htAt:Nat → Nat → Nat)
    (idxH:Nat → Nat → Nat) (s h:Nat) (zs:List Nat):Bool :=
  let i:=idxH s h
  decide (i < N s)&&(htAt s i==h)&&zs.isPerm (S s i)
def nextD_decor (u:Bool) (dm mp:Nat) (slack:Nat) (dws:List (Nat × Nat × Nat))
    (f : (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool):Bool :=
  dws.any fun da =>
    let a:=da.1
    let ra:=dws.erase da
    ra.any fun db =>
      let b:=db.1
      a ≤ b&&(let r:=ra.erase db
        (opsOf u).any fun op =>
          let w:=opD dm op a b
          let g:=(op,a,b)
          w != 0&&w != dm&&!(dws.any (fun x=>x.1==w)) &&
            let dw:=(w,opP mp op da.2.1 db.2.1,opP mp op da.2.2 db.2.2)
            (f g (dw :: r)||(slack ≥ 1&&(f g (dw :: da :: r)||f g (dw :: db :: r))) ||
              (slack ≥ 2&&f g (dw :: da :: db :: r))))
theorem nextD_decor_gen (u:Bool) (dm mp:Nat) (dec:Nat → Nat × Nat × Nat)
    (hfst : ∀ w,(dec w).1 = w)
    (hop : ∀ op a b,(opD dm op a b,opP mp op (dec a).2.1 (dec b).2.1,opP mp op (dec a).2.2 (dec b).2.2) = dec (opD dm op a b))
    (slack:Nat) (ws:List Nat) (g : (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool) :
    nextD_decor u dm mp slack (ws.map dec) g = nextD u dm slack ws (fun opab zs=>g opab (zs.map dec)):=by
  have hinj : Function.Injective dec:=fun x y h=>by rw [← hfst x,← hfst y,h]
  have herase : ∀ (l:List Nat) x,(l.map dec).erase (dec x) = (l.erase x).map dec :=
    fun l x=>erase_map_inj dec hinj l x
  have hcont : ∀ (l:List Nat) w,(l.map dec).any (fun x=>x.1==w) = l.contains w:=by
    intro l w; apply Bool.eq_iff_iff.2; simp [hfst]
  unfold nextD_decor nextD
  simp only [List.any_map,Function.comp_def,hfst,herase,hcont,hop,List.map_cons]
theorem nextD_decor_eq (u:Bool) {dm:Nat} (hd : dm&&&mask256 = dm)
    (pairs:List (Nat × Nat))
    (hr1 : ∀ r ∈ pairs.map Prod.fst,dm.testBit r = true)
    (hr2 : ∀ r ∈ pairs.map Prod.snd,dm.testBit r = true)
    (slack:Nat) (ws:List Nat) (g : (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool) :
    let dec:=fun w=>(w,projBit (pairs.map Prod.fst) w,projBit (pairs.map Prod.snd) w)
    nextD_decor u dm (maskP pairs.length) slack (ws.map dec) g =
      nextD u dm slack ws (fun opab zs=>g opab (zs.map dec)):=by
  intro dec
  apply nextD_decor_gen
  · intro w; rfl
  · intro op a b
    simp only [dec,projBit_opD hd hr1,projBit_opD hd hr2,List.length_map]
def addC (x:Nat) (c:Nat × Nat × Nat):Nat × Nat × Nat :=
  (c.1|||x,c.2.1|||(c.1&&&x),c.2.2|||(c.2.1&&&x))
def cov3 (mp:Nat) (d:Bool) (dws:List (Nat × Nat × Nat)):Nat × Nat × Nat :=
  dws.foldl (fun c dw=>addC (colB mp d dw.2) c) (0,0,0)
def takeOne (c:Nat × Nat × Nat) (x:Nat):Nat:=(c.1^^^x)|||c.2.1
def takeTwo (c:Nat × Nat × Nat) (x y:Nat):Nat :=
  (c.1^^^(x|||y))|||(c.2.1&&&(x^^^y))|||c.2.2
theorem cov3_bit (mp:Nat) (d:Bool) (dws:List (Nat × Nat × Nat)) (i:Nat) :
    let k:=dws.countP (fun dw=>(colB mp d dw.2).testBit i)
    (cov3 mp d dws).1.testBit i = decide (1 ≤ k) ∧
    (cov3 mp d dws).2.1.testBit i = decide (2 ≤ k) ∧
    (cov3 mp d dws).2.2.testBit i = decide (3 ≤ k):=by
  have hgen : ∀ (xs:List (Nat × Nat × Nat)) (c:Nat × Nat × Nat) (k0:Nat),
      (c.1.testBit i = decide (1 ≤ k0) ∧ c.2.1.testBit i = decide (2 ≤ k0) ∧ c.2.2.testBit i = decide (3 ≤ k0)) →
      let k:=k0 + xs.countP (fun dw=>(colB mp d dw.2).testBit i)
      (xs.foldl (fun acc dw=>addC (colB mp d dw.2) acc) c).1.testBit i = decide (1 ≤ k) ∧
      (xs.foldl (fun acc dw=>addC (colB mp d dw.2) acc) c).2.1.testBit i = decide (2 ≤ k) ∧
      (xs.foldl (fun acc dw=>addC (colB mp d dw.2) acc) c).2.2.testBit i = decide (3 ≤ k):=by
    intro xs
    induction xs with
    | nil=>intro c k0 ⟨h1,h2,h3⟩; simp [h1,h2,h3]
    | cons dw xs ih =>
      intro c k0 ⟨h1,h2,h3⟩
      simp only [List.foldl_cons,List.countP_cons]
      have hc : (addC (colB mp d dw.2) c).1.testBit i =
            decide (1 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) ∧
          (addC (colB mp d dw.2) c).2.1.testBit i =
            decide (2 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) ∧
          (addC (colB mp d dw.2) c).2.2.testBit i =
            decide (3 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)):=by
        simp only [addC,Nat.testBit_or,Nat.testBit_and,h1,h2,h3]
        cases hb : (colB mp d dw.2).testBit i <;>
          rcases k0 with _ | _ | _ | k0 <;>
          simp [hb,Nat.le_add_left]
      have ih':=ih (addC (colB mp d dw.2) c) (k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) hc
      cases hb : (colB mp d dw.2).testBit i <;> simp only [hb,↓reduceIte,Bool.false_eq_true,Nat.add_zero] at ih' ⊢
      · exact ih'
      · simpa only [Nat.add_assoc,Nat.add_comm 1] using ih'
  simpa only [cov3,Nat.zero_testBit,Nat.zero_add] using hgen dws (0,0,0) 0 (by simp)
theorem cov3_perm (mp:Nat) (d:Bool) {xs ys:List (Nat × Nat × Nat)} (p : xs.Perm ys) :
    cov3 mp d xs = cov3 mp d ys:=by
  have heq : ∀ i,(cov3 mp d xs).1.testBit i = (cov3 mp d ys).1.testBit i ∧
      (cov3 mp d xs).2.1.testBit i = (cov3 mp d ys).2.1.testBit i ∧
      (cov3 mp d xs).2.2.testBit i = (cov3 mp d ys).2.2.testBit i:=by
    intro i
    obtain ⟨a1,a2,a3⟩:=cov3_bit mp d xs i
    obtain ⟨b1,b2,b3⟩:=cov3_bit mp d ys i
    rw [p.countP_eq] at a1 a2 a3
    exact ⟨a1.trans b1.symm,a2.trans b2.symm,a3.trans b3.symm⟩
  apply Prod.ext
  · exact Nat.eq_of_testBit_eq (fun i=>(heq i).1)
  · apply Prod.ext
    · exact Nat.eq_of_testBit_eq (fun i=>(heq i).2.1)
    · exact Nat.eq_of_testBit_eq (fun i=>(heq i).2.2)
theorem takeOne_eq (mp:Nat) (d:Bool) (a:Nat × Nat × Nat) (rest:List (Nat × Nat × Nat)) :
    takeOne (cov3 mp d (a :: rest)) (colB mp d a.2) = (cov3 mp d rest).1:=by
  apply Nat.eq_of_testBit_eq; intro i
  obtain ⟨h1,h2,_⟩:=cov3_bit mp d (a :: rest) i
  obtain ⟨r1,_,_⟩:=cov3_bit mp d rest i
  simp only [takeOne,Nat.testBit_or,Nat.testBit_xor,h1,h2,r1,List.countP_cons]
  set k:=rest.countP (fun dw=>(colB mp d dw.2).testBit i)
  cases ha : (colB mp d a.2).testBit i <;> simp only [ha,Bool.false_eq_true,↓reduceIte] <;>
    rcases k with _ | _ | _ | k
  · decide
  · decide
  · decide
  · simp only [show 1 ≤ k + 3 by omega,show 2 ≤ k + 3 by omega,decide_true,Bool.xor_false,Bool.or_true]
  · decide
  · decide
  · decide
  · simp only [show 1 ≤ k + 3 + 1 by omega,show 2 ≤ k + 3 + 1 by omega,show 1 ≤ k + 3 by omega,
      decide_true,Bool.xor_true,Bool.or_true,Bool.or_false]
theorem takeTwo_eq (mp:Nat) (d:Bool) (a b:Nat × Nat × Nat) (rest:List (Nat × Nat × Nat)) :
    takeTwo (cov3 mp d (a :: b :: rest)) (colB mp d a.2) (colB mp d b.2) = (cov3 mp d rest).1:=by
  apply Nat.eq_of_testBit_eq; intro i
  obtain ⟨h1,h2,h3⟩:=cov3_bit mp d (a :: b :: rest) i
  obtain ⟨r1,_,_⟩:=cov3_bit mp d rest i
  simp only [takeTwo,Nat.testBit_or,Nat.testBit_and,Nat.testBit_xor,h1,h2,h3,r1,List.countP_cons]
  set k:=rest.countP (fun dw=>(colB mp d dw.2).testBit i)
  cases ha : (colB mp d a.2).testBit i <;> cases hb : (colB mp d b.2).testBit i <;>
    simp only [ha,hb,Bool.false_eq_true,↓reduceIte] <;>
    rcases k with _ | _ | _ | k <;>
    (first | decide | simp only [
      show 1 ≤ k + 3 by omega,show 2 ≤ k + 3 by omega,show 3 ≤ k + 3 by omega,
      show 1 ≤ k + 3 + 1 by omega,show 2 ≤ k + 3 + 1 by omega,show 3 ≤ k + 3 + 1 by omega,
      show 1 ≤ k + 3 + 1 + 1 by omega,show 2 ≤ k + 3 + 1 + 1 by omega,show 3 ≤ k + 3 + 1 + 1 by omega,
      decide_true,Bool.xor_true,Bool.xor_false,Bool.or_true,Bool.or_false,Bool.and_true,Bool.and_false])
theorem cov3_coversD (u:Bool) (mp:Nat) (dw:Nat × Nat × Nat) (rest:List (Nat × Nat × Nat)) :
    ((cov3 mp (!u) rest).1|||colB mp (!u) dw.2==mp) = coversD u mp (dw :: rest):=by
  have e : ((cov3 mp (!u) rest).1|||colB mp (!u) dw.2) =
      (dw :: rest).foldl (fun acc x=>acc|||colB mp (!u) x.2) 0:=by
    apply Nat.eq_of_testBit_eq; intro i
    obtain ⟨h1,_,_⟩:=cov3_bit mp (!u) rest i
    rw [foldl_or_testBit,Nat.zero_testBit,Bool.false_or,Nat.testBit_or,h1,List.any_cons]
    have hp : decide (1 ≤ rest.countP (fun dw=>(colB mp (!u) dw.2).testBit i)) =
        rest.any (fun x=>(colB mp (!u) x.2).testBit i):=by
      rw [Bool.eq_iff_iff,decide_eq_true_eq,Nat.succ_le_iff,List.countP_pos_iff,List.any_eq_true]
    rw [hp,Bool.or_comm]
  unfold coversD; exact congrArg (·==mp) e
def nextD_cov (u:Bool) (dm mp slack:Nat) (dws:List (Nat × Nat × Nat))
    (f : (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool):Bool :=
  let ori:=!u
  let cov:=cov3 mp ori dws
  dws.any fun da =>
    let a:=da.1
    let ca:=colB mp ori da.2
    let ra:=dws.erase da
    ra.any fun db =>
      let b:=db.1
      a ≤ b &&
        (let cb:=colB mp ori db.2
         let base0:=takeTwo cov ca cb
         let base1a:=takeOne cov cb
         let base1b:=takeOne cov ca
         let r:=ra.erase db
         (opsOf u).any fun op =>
           let pz:=(opP mp op da.2.1 db.2.1,opP mp op da.2.2 db.2.2)
           let cz:=colB mp ori pz
           let ok0:=(base0|||cz)==mp
           let ok1a:=slack ≥ 1&&((base1a|||cz)==mp)
           let ok1b:=slack ≥ 1&&((base1b|||cz)==mp)
           let ok2:=slack ≥ 2&&((cov.1|||cz)==mp)
           (ok0||ok1a||ok1b||ok2) &&
           (let w:=opD dm op a b
            let g:=(op,a,b)
            w != 0&&w != dm&&!(dws.any (fun x=>x.1==w)) &&
              let dw:=(w,pz)
              ((ok0&&f g (dw :: r))||(ok1a&&f g (dw :: da :: r)) ||
               (ok1b&&f g (dw :: db :: r))||(ok2&&f g (dw :: da :: db :: r)))))
theorem nextD_cov_eq (u:Bool) (dm mp slack:Nat) (dws:List (Nat × Nat × Nat))
    (g : (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool) :
    nextD_cov u dm mp slack dws g =
      nextD_decor u dm mp slack dws (fun opab dzs=>coversD u mp dzs&&g opab dzs):=by
  unfold nextD_cov nextD_decor
  dsimp only
  apply Bool.eq_iff_iff.2; simp only [List.any_eq_true,Bool.or_eq_true,Bool.and_eq_true]
  constructor
  · rintro ⟨da,hda,db,hdb,hab,op,hop,_,⟨⟨hw0,hwdm⟩,hnw⟩,hfx⟩
    refine ⟨da,hda,db,hdb,hab,op,hop,⟨⟨hw0,hwdm⟩,hnw⟩,?_⟩
    set pz:=(opP mp op da.2.1 db.2.1,opP mp op da.2.2 db.2.2)
    set dw:=(opD dm op da.1 db.1,pz)
    set ra:=dws.erase da
    set r:=ra.erase db
    have hp : dws.Perm (da :: db :: r):=(List.perm_cons_erase hda).trans (List.Perm.cons _ (List.perm_cons_erase hdb))
    have hc2:=cov3_perm mp (!u) hp
    have hca:=cov3_perm mp (!u) (hp.trans (List.Perm.swap _ _ _))
    have hcov0 : (takeTwo (cov3 mp (!u) dws) (colB mp (!u) da.2) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: r):=by rw [hc2,takeTwo_eq]; exact cov3_coversD u mp dw r
    have hcov1a : (takeOne (cov3 mp (!u) dws) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: da :: r):=by rw [hca,takeOne_eq]; exact cov3_coversD u mp dw (da :: r)
    have hcov1b : (takeOne (cov3 mp (!u) dws) (colB mp (!u) da.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: db :: r):=by rw [hc2,takeOne_eq]; exact cov3_coversD u mp dw (db :: r)
    have hcov2 : ((cov3 mp (!u) dws).1|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: da :: db :: r):=by rw [hc2]; exact cov3_coversD u mp dw (da :: db :: r)
    rcases hfx with ((⟨hu0,hf0⟩ | ⟨⟨hsl1,hu1a⟩,hf1a⟩) | ⟨⟨hsl1,hu1b⟩,hf1b⟩) | ⟨⟨hsl2,hu2⟩,hf2⟩
    · left; left; exact ⟨hcov0 ▸ hu0,hf0⟩
    · left; right; exact ⟨hsl1,Or.inl ⟨hcov1a ▸ hu1a,hf1a⟩⟩
    · left; right; exact ⟨hsl1,Or.inr ⟨hcov1b ▸ hu1b,hf1b⟩⟩
    · right; exact ⟨hsl2,hcov2 ▸ hu2,hf2⟩
  · rintro ⟨da,hda,db,hdb,hab,op,hop,⟨⟨hw0,hwdm⟩,hnw⟩,hfx⟩
    refine ⟨da,hda,db,hdb,hab,op,hop,?_⟩
    set pz:=(opP mp op da.2.1 db.2.1,opP mp op da.2.2 db.2.2)
    set dw:=(opD dm op da.1 db.1,pz)
    set ra:=dws.erase da
    set r:=ra.erase db
    have hp : dws.Perm (da :: db :: r):=(List.perm_cons_erase hda).trans (List.Perm.cons _ (List.perm_cons_erase hdb))
    have hc2:=cov3_perm mp (!u) hp
    have hca:=cov3_perm mp (!u) (hp.trans (List.Perm.swap _ _ _))
    have hcov0 : (takeTwo (cov3 mp (!u) dws) (colB mp (!u) da.2) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: r):=by rw [hc2,takeTwo_eq]; exact cov3_coversD u mp dw r
    have hcov1a : (takeOne (cov3 mp (!u) dws) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: da :: r):=by rw [hca,takeOne_eq]; exact cov3_coversD u mp dw (da :: r)
    have hcov1b : (takeOne (cov3 mp (!u) dws) (colB mp (!u) da.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: db :: r):=by rw [hc2,takeOne_eq]; exact cov3_coversD u mp dw (db :: r)
    have hcov2 : ((cov3 mp (!u) dws).1|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: da :: db :: r):=by rw [hc2]; exact cov3_coversD u mp dw (da :: db :: r)
    rcases hfx with (⟨hc0,hg0⟩ | ⟨hsl1,⟨hc1a,hg1a⟩ | ⟨hc1b,hg1b⟩⟩) | ⟨hsl2,hc2',hg2⟩
    · have u0 : (takeTwo (cov3 mp (!u) dws) (colB mp (!u) da.2) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) = true:=hcov0.symm ▸ hc0
      exact ⟨Or.inl (Or.inl (Or.inl u0)),⟨⟨hw0,hwdm⟩,hnw⟩,Or.inl (Or.inl (Or.inl ⟨u0,hg0⟩))⟩
    · have u1a : (takeOne (cov3 mp (!u) dws) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) = true:=hcov1a.symm ▸ hc1a
      exact ⟨Or.inl (Or.inl (Or.inr ⟨hsl1,u1a⟩)),⟨⟨hw0,hwdm⟩,hnw⟩,Or.inl (Or.inl (Or.inr ⟨⟨hsl1,u1a⟩,hg1a⟩))⟩
    · have u1b : (takeOne (cov3 mp (!u) dws) (colB mp (!u) da.2)|||colB mp (!u) pz==mp) = true:=hcov1b.symm ▸ hc1b
      exact ⟨Or.inl (Or.inr ⟨hsl1,u1b⟩),⟨⟨hw0,hwdm⟩,hnw⟩,Or.inl (Or.inr ⟨⟨hsl1,u1b⟩,hg1b⟩)⟩
    · have u2 : ((cov3 mp (!u) dws).1|||colB mp (!u) pz==mp) = true:=hcov2.symm ▸ hc2'
      exact ⟨Or.inr ⟨hsl2,u2⟩,⟨⟨hw0,hwdm⟩,hnw⟩,Or.inr ⟨⟨hsl2,u2⟩,hg2⟩⟩
def bar (u:Bool) (dm Y:Nat) (mp:Nat)
    (SD:Nat → Nat → List (Nat × Nat × Nat)) (S:Nat → Nat → List Nat)
    (N:Nat → Nat) (htAt idxH:Nat → Nat → Nat)
    (ori:List Nat → List Nat) (seed:Nat) (pool:List Nat)
    (mkCut:Nat → Nat → (Nat × Nat × Nat) → List Nat → Bool):Nat → Nat → Bool
  | 0,i=>!(S 0 i==[Y])
  | s + 1,i =>
    let dws:=SD (s + 1) i
    !(nextD_cov u dm mp (s + 2 - dws.length) dws fun g dzs =>
        let zs:=dzs.map Prod.fst
        !(scr u dm Y s pool zs)&&!(mkCut (s + 1) i g zs) &&
        (let cz:=ori zs
         let h:=hk seed cz
         !(foundH S N htAt idxH s h cz)))
def barP (u:Bool) (dm Y:Nat) (mp:Nat)
    (SD:Nat → Nat → List (Nat × Nat × Nat)) (S:Nat → Nat → List Nat)
    (N:Nat → Nat) (htAt idxH:Nat → Nat → Nat)
    (ori:List Nat → List Nat) (seed:Nat) (pool:List Nat)
    (mkPools:Nat → Nat → List (Nat × Nat × (Nat × List Nat))):Nat → Nat → Bool
  | 0,i=>!(S 0 i==[Y])
  | s + 1,i =>
    let dws:=SD (s + 1) i
    match mkPools (s + 1) i with
    | [] =>
      !(nextD_cov u dm mp (s + 2 - dws.length) dws fun _ dzs =>
          let zs:=dzs.map Prod.fst
          !(scr u dm Y s pool zs) &&
          (let cz:=ori zs; let h:=hk seed cz; !(foundH S N htAt idxH s h cz)))
    | p :: ps =>
      !(nextD_cov u dm mp (s + 2 - dws.length) dws fun g dzs =>
          let zs:=dzs.map Prod.fst
          !(scr u dm Y s pool zs) &&
          !((p :: ps).any fun e=>checkPool u e.1 e.2.1 s (stepOp u e.1 e.2.2 g) zs) &&
          (let cz:=ori zs; let h:=hk seed cz; !(foundH S N htAt idxH s h cz)))
theorem lower_of_search {u:Bool} {d T L:Nat} {roots:List Nat} {pairs:List (Nat × Nat)}
    (hinit : (d&&&mask256==d)&&d.testBit 0&&!(T.testBit 0)&&roots.all (fun r=>!r.testBit 0) &&
             !(isConstB d T)&&decide ((roots.map (·&&&d)).Nodup) &&
             pairs.all (fun p=>d.testBit p.1&&d.testBit p.2&&((T&&&d).testBit p.1 != (T&&&d).testBit p.2)) = true)
    (hpf : ∀ zs ∈ (roots.map (·&&&d)).sublists,zs ≠ roots.map (·&&&d) → unorientedCov pairs zs = false)
    (hno : ∀ s ≤ L - 1,RunD u d (T&&&d) s (roots.map (·&&&d)) → False) :
    Lower u d roots T L:=by
  simp only [Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true',decide_eq_true_eq] at hinit
  obtain ⟨⟨⟨⟨⟨⟨hd,hd0⟩,hT0⟩,hR0⟩,hncb⟩,hnd_xs'⟩,hpairs⟩:=hinit
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst d T:=fun h=>by rw [(isConstB_iff _ _).2 h] at hncb; contradiction
  obtain ⟨s,ws,hs_le,hnd,hws_sub,hrun⟩:=reach_to_run hd hd0 hT0 hR0 hnc hr ha
  have hperm_sub : ∃ zs,zs.Sublist (roots.map (·&&&d)) ∧ ws.Perm zs:=by
    refine ⟨(roots.map (·&&&d)).filter (fun x=>decide (x ∈ ws)),List.filter_sublist,?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ hnd_xs')).2 ?_
    intro x; simp only [List.mem_filter,decide_eq_true_eq]
    exact ⟨fun hx=>⟨hws_sub x hx,hx⟩,fun h=>h.2⟩
  obtain ⟨zs,hsub,hpz⟩:=hperm_sub
  have hrun':=Run.perm hpz hrun
  by_cases heq : zs = roots.map (·&&&d)
  · subst heq; exact hno s (by omega) hrun'
  · have hcov:=unorientedCov_ok hd pairs hpairs hrun'
    rw [hpf zs (List.mem_sublists.2 hsub) heq] at hcov; contradiction
theorem barP_eq (u:Bool) (dm Y mp:Nat) (SD S N htAt idxH ori seed pool mkPools s i) :
    barP u dm Y mp SD S N htAt idxH ori seed pool mkPools s i =
      bar u dm Y mp SD S N htAt idxH ori seed pool
        (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool u e.1 e.2.1 (s' - 1) (stepOp u e.1 e.2.2 g) zs) s i:=by
  cases s with
  | zero=>rfl
  | succ s =>
    unfold barP bar; dsimp only
    cases mkPools (s + 1) i with
    | nil=>simp
    | cons p ps=>rfl
theorem bar_all {u:Bool} {dm T:Nat} {pairs:List (Nat × Nat)} {r1s r2s mp SD S N htAt idxH ori seed pool mkCut cap}
    (hd : dm&&&mask256 = dm)
    (hr1_eq : r1s = pairs.map Prod.fst) (hr2_eq : r2s = pairs.map Prod.snd) (hmp_eq : mp = maskP pairs.length)
    (hSD : ∀ s j,SD s j = (S s j).map (fun w=>(w,projBit r1s w,projBit r2s w)))
    (hpairs : pairs.all (fun p=>dm.testBit p.1&&dm.testBit p.2&&!(T&&&dm).testBit p.1&&(T&&&dm).testBit p.2) = true)
    (hr : ∀ {v ys},RunD u dm (T&&&dm) v ys → RunD u dm (T&&&dm) v (ori ys))
    (hcut : ∀ {s i g ys},mkCut (s + 1) i g ys = true → ¬ RunD u dm (T&&&dm) s ys)
    (hc : ∀ s ≤ cap,∀ i < N s,bar u dm (T&&&dm) mp SD S N htAt idxH ori seed pool mkCut s i = true) :
    ∀ s ≤ cap,∀ i < N s,¬ RunD u dm (T&&&dm) s (S s i):=by
  subst hr1_eq hr2_eq hmp_eq
  have hr1 : ∀ r ∈ pairs.map Prod.fst,dm.testBit r = true:=by
    intro r hr'; obtain ⟨p,hp,rfl⟩:=List.mem_map.1 hr'
    have h:=List.all_eq_true.1 hpairs p hp; simp only [Bool.and_eq_true] at h; exact h.1.1.1
  have hr2 : ∀ r ∈ pairs.map Prod.snd,dm.testBit r = true:=by
    intro r hr'; obtain ⟨p,hp,rfl⟩:=List.mem_map.1 hr'
    have h:=List.all_eq_true.1 hpairs p hp; simp only [Bool.and_eq_true] at h; exact h.1.1.2
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    have hb:=hc s hs i hi
    cases s with
    | zero=>simp [bar,zero_done hh rfl] at hb
    | succ s =>
      by_contra! hn
      let F (g:Nat × Nat × Nat) (zs:List Nat) :=
        coversP u pairs zs&&!(scr u dm (T&&&dm) s pool zs)&&!(mkCut (s + 1) i g zs) &&
        (let cz:=ori zs
         let h:=hk seed cz
         !(foundH S N htAt idxH s h cz))
      have hF (g zs) (hz : RunD u dm (T&&&dm) s zs) : F g zs = true:=by
        have hcz:=hr hz
        have hcutf : mkCut (s + 1) i g zs = false:=by
          cases h : mkCut (s + 1) i g zs with
          | false=>rfl
          | true=>exact absurd hz (hcut h)
        simp only [F,coversP_ok hd pairs hpairs hz,scr_no pool hz,hcutf,Bool.not_false,Bool.true_and,foundH]
        simp only [Bool.not_eq_true',Bool.and_eq_false_imp,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq]
        rintro ⟨hj,_⟩
        by_contra! hp
        have p:=List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
        exact ih s (by omega) (by omega) _ hj (Run.perm p hcz)
      have hN:=nextD_complete hh s rfl _ (List.Perm.refl _) F hF
      dsimp only [bar] at hb
      rw [hSD,List.length_map,nextD_cov_eq,nextD_decor_eq u hd pairs hr1 hr2] at hb
      have hFeq : (fun g zs=>coversD u (maskP pairs.length) (zs.map (fun w=>(w,projBit (pairs.map Prod.fst) w,projBit (pairs.map Prod.snd) w))) &&
          (let zs':=(zs.map (fun w=>(w,projBit (pairs.map Prod.fst) w,projBit (pairs.map Prod.snd) w))).map Prod.fst
           !(scr u dm (T&&&dm) s pool zs')&&!(mkCut (s + 1) i g zs') &&
           (let cz:=ori zs'
            let h:=hk seed cz
            !(foundH S N htAt idxH s h cz)))) = F:=by
        funext g zs
        have hfst : (zs.map (fun w=>(w,projBit (pairs.map Prod.fst) w,projBit (pairs.map Prod.snd) w))).map Prod.fst = zs:=by
          simp [List.map_map,Function.comp_def]
        rw [coversD_eq,hfst]
        simp only [F,Bool.and_assoc]
      rw [hFeq,hN] at hb
      contradiction
def pickMin (seed:Nat) (orig:List Nat):List (List (Nat × Nat)) → List Nat → Nat → List Nat
  | [],best,_=>best
  | ms :: rest,best,bestH =>
    let img:=orig.map (applyMoves ms)
    let h:=hk seed img
    if h < bestH then pickMin seed orig rest img h else pickMin seed orig rest best bestH
theorem pickMin_runD {u:Bool} {dm Y v} (seed:Nat) (orig:List Nat) (h0 : RunD u dm Y v orig) :
    ∀ (syms:List (List (Nat × Nat))) (best:List Nat) (bestH:Nat),
      syms.all (fun ms=>ms.all moveOK256&&(applyMoves ms dm==dm)&&(applyMoves ms Y==Y)) = true →
      RunD u dm Y v best →
      RunD u dm Y v (pickMin seed orig syms best bestH)
  | [],_,_,_,hb=>hb
  | ms :: rest,best,bestH,hok,hb=>by
    simp only [List.all_cons,Bool.and_eq_true,beq_iff_eq] at hok
    unfold pickMin; dsimp only; split
    · exact pickMin_runD seed orig h0 rest _ _ hok.2 (applyMoves_runD ms hok.1.1.1 hok.1.1.2 hok.1.2 h0)
    · exact pickMin_runD seed orig h0 rest best bestH hok.2 hb
def gvN (w:List Nat) (g : Gate):Nat :=
  match g.op with
  | .and=>g.inputs.foldr (fun i acc=>andD mask256 (w.getD i 0) acc) mask256
  | .or =>g.inputs.foldr (fun i acc=>orD mask256 (w.getD i 0) acc) 0
  | .not=>match g.inputs with | []=>mask256 | i :: _=>negD mask256 (w.getD i 0)
  | _=>0
def execN (gs:List Gate) (w:List Nat):List Nat :=
  gs.foldl (fun l g=>l ++ [gvN l g]) w
theorem gvN_bit (w:List Nat) (g : Gate) (r:Nat) (hr : r < 256)
    (hop : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (gvN w g).testBit r = g.op.eval (g.inputs.map fun i=>(w.map (·.testBit r)).getD i false):=by
  have hm : mask256.testBit r = true:=by simp [mask256_bit,hr]
  have hgd : ∀ i,(w.map (·.testBit r)).getD i false = (w.getD i 0).testBit r:=by
    intro i; simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases w[i]? with | none=>simp | some v=>rfl
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop
  rcases hop with h | h | h
  · simp only [gvN,GateOp.eval,h]
    induction g.inputs with
    | nil=>simp [hm]
    | cons i l ih =>
      rw [List.foldr_cons,List.map_cons,List.all_cons,id_eq,andD,Nat.testBit_and,Nat.testBit_and,hm,Bool.and_true,hgd,ih]
  · simp only [gvN,GateOp.eval,h]
    induction g.inputs with
    | nil=>simp
    | cons i l ih =>
      rw [List.foldr_cons,List.map_cons,List.any_cons,id_eq,orD,Nat.testBit_and,Nat.testBit_or,hm,Bool.and_true,hgd,ih]
  · simp only [gvN,GateOp.eval,h]
    cases g.inputs with
    | nil=>simp [hm]
    | cons i l=>simp only [List.map_cons,List.headD_cons,negD,Nat.testBit_and,Nat.testBit_xor,hm,Bool.and_true,Bool.xor_true,hgd]
theorem execN_bit (gs:List Gate) (w:List Nat) (r:Nat) (hr : r < 256)
    (hfan : ∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execN gs w).map (·.testBit r) =
      gs.foldl (fun l g=>l ++ [g.op.eval (g.inputs.map fun i=>l.getD i false)]) (w.map (·.testBit r)):=by
  induction gs generalizing w with
  | nil=>rfl
  | cons g gs ih =>
    simp only [execN,List.foldl_cons] at ih ⊢
    rw [ih _ (fun g' hg'=>hfan g' (List.mem_cons_of_mem _ hg'))]
    simp [gvN_bit w g r hr (hfan g List.mem_cons_self)]
def isNotGate (g : Gate):Bool:=match g.op with | .not=>true | _=>false
theorem execN_reach (u:Bool) (gs:List Gate) (roots:List Nat)
    (hfan : ∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hmono : u = false → ∀ g ∈ gs,isNotGate g = false) :
    ∀ (p:Nat) (w bank:List Nat),NatReach u mask256 roots p bank →
      (∀ v ∈ w,Avail u mask256 bank v) →
      ∃ p' bank',p' ≤ p + gs.countP (fun g=>!isNotGate g) ∧ NatReach u mask256 roots p' bank' ∧
        ∀ v ∈ execN gs w,Avail u mask256 bank' v:=by
  have hm256 : mask256&&&mask256 = mask256:=Nat.and_self _
  induction gs with
  | nil=>intro p w bank hr hsup; exact ⟨p,bank,by simp,hr,hsup⟩
  | cons g gs ih =>
    intro p w bank hr hsup
    have hav_gd : ∀ i,Avail u mask256 bank (w.getD i 0):=by
      intro i; by_cases hi : i < w.length
      · exact hsup _ (getD_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
    have hstep : ∃ p1 bank1,p1 ≤ p + (if !isNotGate g then 1 else 0) ∧ NatReach u mask256 roots p1 bank1 ∧
        (∀ v ∈ w ++ [gvN w g],Avail u mask256 bank1 v):=by
      have hg:=hfan g List.mem_cons_self
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
      obtain ⟨hop,hlen⟩:=hg
      have hand_m : ∀ a,andD mask256 a mask256&&&mask256 = a&&&mask256:=fun a=>by
        simp [andD,Nat.and_assoc,Nat.and_self]
      have hor_0 : ∀ a,orD mask256 a 0&&&mask256 = a&&&mask256:=fun a=>by
        simp [orD,Nat.and_assoc,Nat.and_self]
      have lift_w : ∀ z,(∀ v ∈ w,Avail u mask256 (z :: bank) v):=fun z v hv=>avail_cons z v (hsup v hv)
      rcases hop with h | h | h
      · have hn : (!isNotGate g) = true:=by simp [isNotGate,h]
        rw [hn]; simp only [ite_true]
        rcases hgi : g.inputs with _ | ⟨i,_ | ⟨j,_ | ⟨k,l⟩⟩⟩
        · exact ⟨p,bank,by omega,hr,fun v hv=>by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inr (by simp [gvN,h,hgi]))⟩
        · exact ⟨p,bank,by omega,hr,fun v hv=>by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; simp only [gvN,h,hgi,List.foldr_cons,List.foldr_nil]
              exact avail_of_eq (hand_m _).symm (hav_gd i)⟩
        · refine ⟨p + 1,opD mask256 0 (w.getD i 0) (w.getD j 0) :: bank,le_rfl,
            ⟨bank,_,_,0,by simp [allowedB],rfl,hr,hav_gd i,hav_gd j⟩,fun v hv=>?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [gvN,h,hgi,List.foldr_cons,List.foldr_nil]
            exact Or.inr (Or.inl ⟨_,List.mem_cons_self,by simp [opD,andD,Nat.and_assoc,Nat.and_self]⟩)
        · rw [hgi] at hlen; simp at hlen
      · have hn : (!isNotGate g) = true:=by simp [isNotGate,h]
        rw [hn]; simp only [ite_true]
        rcases hgi : g.inputs with _ | ⟨i,_ | ⟨j,_ | ⟨k,l⟩⟩⟩
        · exact ⟨p,bank,by omega,hr,fun v hv=>by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inl (by simp [gvN,h,hgi]))⟩
        · exact ⟨p,bank,by omega,hr,fun v hv=>by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; simp only [gvN,h,hgi,List.foldr_cons,List.foldr_nil]
              exact avail_of_eq (hor_0 _).symm (hav_gd i)⟩
        · refine ⟨p + 1,opD mask256 1 (w.getD i 0) (w.getD j 0) :: bank,le_rfl,
            ⟨bank,_,_,1,by simp [allowedB],rfl,hr,hav_gd i,hav_gd j⟩,fun v hv=>?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [gvN,h,hgi,List.foldr_cons,List.foldr_nil]
            exact Or.inr (Or.inl ⟨_,List.mem_cons_self,by apply Nat.eq_of_testBit_eq; intro r; simp [opD,orD]; cases mask256.testBit r <;> simp⟩)
        · rw [hgi] at hlen; simp at hlen
      · cases u with
        | false =>
          have hbad:=hmono rfl g List.mem_cons_self
          simp [isNotGate,h] at hbad
        | true =>
          have hn : (!isNotGate g) = false:=by simp [isNotGate,h]
          rw [hn]; simp only [Bool.false_eq_true,ite_false,Nat.add_zero]
          rcases hgi : g.inputs with _ | ⟨i,l⟩
          · exact ⟨p,bank,le_rfl,hr,fun v hv=>by
              rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
              · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inr (by simp [gvN,h,hgi]))⟩
          · exact ⟨p,bank,le_rfl,hr,fun v hv=>by
              rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
              · rw [List.mem_singleton.1 hv]; simp only [gvN,h,hgi]
                exact avail_neg hm256 (hav_gd i)⟩
    obtain ⟨p1,bank1,hp1,hr1,hsup1⟩:=hstep
    obtain ⟨p2,bank2,hp2,hr2,hsup2⟩:=ih (fun g' hg'=>hfan g' (List.mem_cons_of_mem _ hg'))
      (fun hu g' hg'=>hmono hu g' (List.mem_cons_of_mem _ hg')) p1 _ bank1 hr1 hsup1
    rw [List.countP_cons]
    cases hb : !isNotGate g <;> simp only [hb,ite_true,Bool.false_eq_true,ite_false] at hp1 ⊢ <;>
      exact ⟨p2,bank2,by omega,hr2,hsup2⟩
def xs256:List Nat :=
  [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
   0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
   0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
   0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
   0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
   0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,
   0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
   0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
def pt8 (r:Nat) : Fin 8 → Bool:=fun i=>r.testBit i.val
theorem xs256_bits : ∀ r : Fin 256,xs256.map (·.testBit r.val) = List.ofFn (pt8 r.val):=by
  decide +kernel
theorem countP_not_lt {gs:List Gate} {g : Gate} (hg : g ∈ gs) (hn : isNotGate g = true) :
    gs.countP (fun x=>!isNotGate x) + 1 ≤ gs.length:=by
  induction gs with
  | nil=>simp at hg
  | cons x xs ih =>
    rw [List.countP_cons,List.length_cons]
    rcases List.mem_cons.1 hg with rfl | hxs
    · simp only [hn,Bool.not_true,Bool.false_eq_true,ite_false]
      have:=List.countP_le_length (p:=fun y=>!isNotGate y) (l:=xs); omega
    · have:=ih hxs; cases hb : !isNotGate x <;> simp only [hb,ite_true,Bool.false_eq_true,ite_false] <;> omega
abbrev rowMask0 : Nat := 0x2222222222222222222222222222222222222222222222222222222222222222
abbrev rowMask10 : Nat := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a
abbrev rowMask11 : Nat := 0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc
abbrev rowMask16 : Nat := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
abbrev rowMask22 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0
abbrev rowMask25 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff0000
abbrev rowMask26 : Nat := 0xffffffff000000000000000000000000ffffffff00000000
abbrev rowMask27 : Nat := 0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa
abbrev rowMask28 : Nat := 0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc
abbrev rowMask29 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0
abbrev rowMask32 : Nat := 0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa
abbrev rowMask33 : Nat := 0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa
abbrev rowMask34 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff0000
abbrev rowMask35 : Nat := 0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa
abbrev rowMask36 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0
abbrev rowMask37 : Nat := 0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc
abbrev rowMask39 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00
abbrev rowMask44 : Nat := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
abbrev rowMask46 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00
abbrev rowMask49 : Nat := 0xffffffff00000000ffffffff00000000
abbrev rowMask51 : Nat := 0xffffffffffffffff0000000000000000
abbrev rowMask87 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
abbrev rowMask144 : Nat := 0xcccccccccccccccc0000000000000000cccccccccccccccc
abbrev rowMask149 : Nat := 0x330033000000000033003300000000003300330000000000330033
abbrev rowMask151 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000
abbrev rowMask155 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
abbrev rowMask176 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
abbrev rowMask183 : Nat := 0xffff0000ffff0000ffff0000ffff0000
abbrev rowMask187 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
abbrev rowMask204 : Nat := 0x30003000000000003000300000000000300030000000000030003
abbrev rowMask205 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
abbrev rowMask214 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
abbrev rowMask217 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
abbrev rowMask218 : Nat := 0x11001100110011001100110011001100110011001100110011001100110011
abbrev rowMask219 : Nat := 0x33003300330033000000000000000000330033003300330000000000000000
abbrev rowMask220 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00
abbrev rowMask221 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
abbrev rowMask227 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f0
abbrev rowMask230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
abbrev rowMask231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
abbrev rowMask232 : Nat := 0xaa000000aa000000aa000000aa000000aa000000aa000000aa000000aa
abbrev rowMask234 : Nat := 0x30303030000000003030303000000000303030300000000030303030
abbrev rowMask241 : Nat := 0x110011000000000011001100000000001100110000000000110011
abbrev rowMask242 : Nat := 0x550055000000000055005500000000005500550000000000550055
abbrev rowMask245 : Nat := 0xc0c0000000000000c0c0000000000000c0c0000000000000c0c
abbrev rowMask246 : Nat := 0xf0f0000000000000f0f00000000000000000000000000000000
abbrev rowMask259 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
abbrev rowMask260 : Nat := 0x3300330033003300000000000000000033003300330033
abbrev rowMask262 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaaaaaa0000aaaa0000aaaa0000aaaa0000
abbrev rowMask263 : Nat := 0xfffffafafffffafafffffafafffffafaaaaa0000aaaa0000aaaa0000aaaa0000
abbrev rowMask264 : Nat := 0xffffffffccccccccffffffffcccccccccccccccc00000000cccccccc00000000
abbrev rowMask265 : Nat := 0xffffaaaaffffaaaaaaaaaaaaaaaa0000ffffaaaaffffaaaaaaaaaaaaaaaa0000
abbrev rowMask266 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f000000000f0f0f0f000000000
abbrev rowMask267 : Nat := 0xeeeeeeeeaaaa0000eeeeeeeeaaaa0000eeeeeeeeaaaa0000eeeeeeeeaaaa0000
abbrev rowMask268 : Nat := 0xfcfcfcfcfcfcfcfccccccccc00000000fcfcfcfcfcfcfcfccccccccc00000000
abbrev rowMask269 : Nat := 0xffffff00ffffff00ffffff00ffffff00ff00ff00ff00ff000000000000000000
abbrev rowMask270 : Nat := 0xfffffff0fffffff0fffffff0fffffff0ff00ff00ff00ff000000000000000000
abbrev rowMask271 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
abbrev rowMask273 : Nat := 0xfffffffefffffffefffffffefffffffeffeeffeeffeeffeeeeccaa00eeccaa00
abbrev rowMask274 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
abbrev rowMask275 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
abbrev rowMask276 : Nat := 0x303030300000000030303030000000003030303000000000303030300000000
abbrev rowMask277 : Nat := 0x33003300000000003300330000000000330033000000000033003300000000
abbrev rowMask278 : Nat := 0x55000000550000005500000055000000550000005500000055000000550000
abbrev rowMask279 : Nat := 0x3000300000000000300030000000000030003000000000003000300000000
abbrev rowMask280 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
abbrev rowMask282 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
abbrev rowMask285 : Nat := 0x1100000011000000110000001100000011000000110000001100000011
abbrev rowMask289 : Nat := 0x300000003000000030000000300000003000000030000000300000003
abbrev rowMask290 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00
abbrev rowMask291 : Nat := 0x11111111000000001111111100000000111111110000000011111111
abbrev rowMask292 : Nat := 0x33333333000000003333333300000000333333330000000033333333
abbrev rowMask293 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
abbrev rowMask294 : Nat := 0x1010101000000000101010100000000010101010000000001010101
abbrev rowMask295 : Nat := 0x3030303000000000303030300000000030303030000000003030303
abbrev rowMask296 : Nat := 0x3030303000000000303030300000000030203020000000002020000
abbrev rowMask297 : Nat := 0x3030303000000000303030300000000000000000000000000000000
abbrev rowMask298 : Nat := 0x33003300000000000000000000000000330033
abbrev rowMask299 : Nat := 0x50005000000000005000500000000000500050000000000050005
abbrev rowMask301 : Nat := 0x3333000000000000333300000000000033330000000000003333
abbrev rowMask306 : Nat := 0x303000000000000030300000000000003020000000000000200
abbrev rowMask307 : Nat := 0x303000000000000030300000000000000000000000000000000
abbrev rowMask308 : Nat := 0xf0f0000000000000f0f0000000000000f0e0000000000000e0c
abbrev rowMask310 : Nat := 0x33000000000000003300000000000000330000000000000033
abbrev rowMask311 : Nat := 0x55000000000000005500000000000000550000000000000055
abbrev rowMask312 : Nat := 0xff00000000000000ff00000000000000ff00000000000000ff
abbrev rowMask316 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0
abbrev rowMask319 : Nat := 0x300030003000300000000000000000003000300030003
abbrev rowMask320 : Nat := 0x500050005000500000000000000000005000500050005
namespace B5
def dom_85 : Nat := 0x3300330000000000330033

def goal_85 : Nat := 0xfafafafafafafafaaaaa0000aaaa0000fafafafafafafafaaaaa0000aaaa0000

def roots_85 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_145 : Nat := 0x3000300000000000000000000000000030003

def goal_145 : Nat := rowMask262

def roots_145 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_147 : Nat := 0xf000f000000000000000000000000000f000f

def goal_147 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeeeaaaa0000aaaa0000aaaa0000aaaa0000

def roots_147 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_149 : Nat := rowMask298

def goal_149 : Nat := rowMask263

def roots_149 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_151 : Nat := 0xff00ff00000000000000000000000000ff00ff

def goal_151 : Nat := 0xfffffefefffffefefffffefefffffefeaaaa0000aaaa0000aaaa0000aaaa0000

def roots_151 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_162 : Nat := 0x50000000500000000000000000000000500000005

def goal_162 : Nat := rowMask264

def roots_162 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_163 : Nat := 0xf0000000f00000000000000000000000f0000000f

def goal_163 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeecccccccc00000000cccccccc00000000

def roots_163 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_177 : Nat := rowMask319

def goal_177 : Nat := 0xffffffffffffaaaaffffffffffffaaaaaaaa0000aaaa0000aaaa0000aaaa0000

def roots_177 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_178 : Nat := rowMask320

def goal_178 : Nat := 0xffffffffffffccccffffffffffffcccccccccccc00000000cccccccc00000000

def roots_178 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_179 : Nat := rowMask274

def goal_179 : Nat := 0xffffffffffffeeeeffffffffffffeeeeeeeeccccaaaa0000eeeeccccaaaa0000

def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := rowMask259

def goal_183 : Nat := 0xfffffffffffffefefffffffffffffefeeeeeccccaaaa0000eeeeccccaaaa0000

def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_195 : Nat := 0xf000000000000000f000000000000000f000000000000000f

def goal_195 : Nat := 0xffffffffffffffffeeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaa0000000000000000

def roots_195 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_196 : Nat := 0x11000000000000001100000000000000110000000000000011

def goal_196 : Nat := 0xfffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000

def roots_196 : List Nat := [xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_197 : Nat := rowMask310

def goal_197 : Nat := 0xfffffffffffffffffafafafafafafafafafafafafafafafa0000000000000000

def roots_197 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_198 : Nat := rowMask311

def goal_198 : Nat := 0xfffffffffffffffffcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f00000000000000000

def roots_198 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_199 : Nat := rowMask312

def goal_199 : Nat := 0xfffffffffffffffffefefefefefefefefafafafafafafafa0000000000000000

def roots_199 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_209 : Nat := rowMask204

def goal_209 : Nat := 0xffffffffffffffffffffaaaaffffaaaaaaaaaaaaaaaaaaaaaaaa0000aaaa0000

def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := rowMask205

def goal_211 : Nat := 0xffffffffffffffffffffeeeeffffeeeeaaaaaaaaaaaaaaaaaaaa0000aaaa0000

def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_212 : Nat := rowMask241

def goal_212 : Nat := 0xfffffffffffffffffffff0f0fffff0f0f0f0f0f0f0f0f0f00000000000000000

def roots_212 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := rowMask149

def goal_213 : Nat := 0xfffffffffffffffffffffafafffffafafafafafafafafafaaaaa0000aaaa0000

def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := rowMask242

def goal_214 : Nat := 0xfffffffffffffffffffffcfcfffffcfcf0f0f0f0f0f0f0f00000000000000000

def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := rowMask187

def goal_215 : Nat := 0xfffffffffffffffffffffefefffffefefafafafafafafafaaaaa0000aaaa0000

def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := rowMask230

def goal_230 : Nat := 0xfffffffffffffffffffffffffcfcfcfcfcfcfcfcf0f0f0f0cccccccc00000000

def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := rowMask231

def goal_231 : Nat := 0xfffffffffffffffffffffffffefefefefefefefefafafafacccccccc00000000

def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := rowMask176

def goal_243 : Nat := 0xffffffffffffffffffffffffffffeeeeeeeeeeeeaaaaaaaaeeeeccccaaaa0000

def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := rowMask87

def goal_245 : Nat := 0xfffffffffffffffffffffffffffffafafafafafafafafafaaaaa0000aaaa0000

def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := rowMask217

def goal_246 : Nat := 0xfffffffffffffffffffffffffffffcfcfcfcfcfcf0f0f0f0cccccccc00000000

def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := rowMask155

def goal_247 : Nat := 0xfffffffffffffffffffffffffffffefefefefefefafafafaeeeeccccaaaa0000

def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

namespace S_145
def pairsG : List (Nat × Nat) := [(1,17), (1,129), (16,17), (16,144), (128,129), (128,144)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_145.map (· &&& dom_145)
def goalM : Nat := goal_145 &&& dom_145
def NN : Nat → Nat
|2=>1
|3=>1
|_=>0
def HT : Nat → Nat → Nat
|2,0=>0x82246
|3,0=>0x82246
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x3000000000000000000000000000000030000800080000000000000000000000000008000b000300000000000000000000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x924
|_=>0
def stOffB : Nat → Nat → Nat
|2,0=>3
|3,0=>0x33
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 3 then fld (dictB (i / 512) (i / 32 % 16)) 146 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 2 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 7 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))

def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
|_=>0
def opOffB : Nat → Nat → Nat
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 6 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 3), wireSAt ((code >>> 4) &&& 3)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 5 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmPalB : Nat → Nat
|0=>0
|_=>0
def pmB : Nat → Nat → Nat
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 1 (j % 128); fld (pmPalB (k / 32)) 1 (k % 32)
def mkPools (_ _ : Nat) : List (Nat × Nat × (Nat × List Nat)) := []
def mkCut (_ _ : Nat) (_ : Nat × Nat × Nat) (_ : List Nat) : Bool := false
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_145 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_145 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(rowMask183, 112)], [(rowMask35, 15)], [(rowMask44, 127)], [(rowMask183, 112), (rowMask44, 127)], [(rowMask183, 112), (rowMask35, 15)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_145 == dom_145) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_145 goalM v ys) : RunD true dom_145 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_145 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_145 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_145 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_145 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_145 roots_145 goal_145 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_145

theorem lowS_145 : Lower true dom_145 roots_145 goal_145 4 := S_145.noCircuit

def isoMvS_162 : List (Nat × Nat) := [(rowMask25, 16), (rowMask0, 1)]

theorem lowS_162 : Lower true dom_162 roots_162 goal_162 4 :=
  lower_iso isoMvS_162 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_145

def isoMvS_196 : List (Nat × Nat) := [(rowMask26, 32), (rowMask25, 16), (rowMask16, 2), (rowMask0, 1)]

theorem lowS_196 : Lower true dom_196 roots_196 goal_196 4 :=
  lower_iso isoMvS_196 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_145

namespace S_85
def pairsG : List (Nat × Nat) := [(1,17), (1,65), (4,68), (5,21), (5,69), (16,17), (20,21), (20,84), (64,65), (64,68), (80,81), (80,84)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_85.map (· &&& dom_85)
def goalM : Nat := goal_85 &&& dom_85
def NN : Nat → Nat
|3=>1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0x2451e
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xcc00000000000000cc0003000300000000000300030880088000000000088008b300330000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0xe4
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>4
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 4 then fld (dictB (i / 512) (i / 32 % 16)) 86 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 2 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 7 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))

def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
|_=>0
def opOffB : Nat → Nat → Nat
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 6 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 3), wireSAt ((code >>> 4) &&& 3)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 5 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmPalB : Nat → Nat
|0=>0
|_=>0
def pmB : Nat → Nat → Nat
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 1 (j % 128); fld (pmPalB (k / 32)) 1 (k % 32)
def mkPools (_ _ : Nat) : List (Nat × Nat × (Nat × List Nat)) := []
def mkCut (_ _ : Nat) (_ : Nat × Nat × Nat) (_ : List Nat) : Bool := false
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_85 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_85 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(rowMask22, 12), (rowMask32, 63)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_85 == dom_85) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_85 goalM v ys) : RunD true dom_85 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_85 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_85 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_85 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_85 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_85 roots_85 goal_85 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_85

theorem lowS_85 : Lower true dom_85 roots_85 goal_85 4 := S_85.noCircuit

theorem lowS_147 : Lower true dom_147 roots_147 goal_147 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc000c000000000000000000000000000c000c, 128, 130)] (by decide +kernel) (by decide +kernel) lowS_145

theorem lowS_197 : Lower true dom_197 roots_197 goal_197 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x22000000000000002200000000000000220000000000000022, 64, 65)] (by decide +kernel) (by decide +kernel) lowS_196

def isoMvS_149 : List (Nat × Nat) := [(rowMask16, 2)]

theorem lowS_149 : Lower true dom_149 roots_149 goal_149 5 :=
  lower_iso isoMvS_149 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_147

def isoMvS_163 : List (Nat × Nat) := [(rowMask25, 16), (rowMask0, 1)]

theorem lowS_163 : Lower true dom_163 roots_163 goal_163 5 :=
  lower_iso isoMvS_163 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_147

def isoMvS_177 : List (Nat × Nat) := [(rowMask46, 24), (rowMask29, 4), (rowMask16, 2)]

theorem lowS_177 : Lower true dom_177 roots_177 goal_177 5 :=
  lower_iso isoMvS_177 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_147

def isoMvS_178 : List (Nat × Nat) := [(rowMask25, 16), (rowMask46, 24), (rowMask29, 4), (rowMask16, 2), (rowMask10, 3)]

theorem lowS_178 : Lower true dom_178 roots_178 goal_178 5 :=
  lower_iso isoMvS_178 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_147

def isoMvS_195 : List (Nat × Nat) := [(rowMask26, 32), (rowMask25, 16)]

theorem lowS_195 : Lower true dom_195 roots_195 goal_195 5 :=
  lower_iso isoMvS_195 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_147

def isoMvS_198 : List (Nat × Nat) := [(rowMask26, 32), (rowMask25, 16), (rowMask10, 3)]

theorem lowS_198 : Lower true dom_198 roots_198 goal_198 5 :=
  lower_iso isoMvS_198 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_147

def isoMvS_209 : List (Nat × Nat) := [(rowMask34, 48), (rowMask39, 8), (rowMask29, 4), (rowMask32, 63)]

theorem lowS_209 : Lower true dom_209 roots_209 goal_209 5 :=
  lower_iso isoMvS_209 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_197

def isoMvS_212 : List (Nat × Nat) := [(rowMask26, 32), (rowMask25, 16), (rowMask46, 24), (rowMask11, 6), (rowMask10, 3)]

theorem lowS_212 : Lower true dom_212 roots_212 goal_212 5 :=
  lower_iso isoMvS_212 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_147

theorem lowS_151 : Lower true dom_151 roots_151 goal_151 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc00cc00000000000000000000000000cc00cc, 128, 130)] (by decide +kernel) (by decide +kernel) lowS_149

namespace S_179
def pairsG : List (Nat × Nat) := [(1,17), (1,129), (2,34), (2,130), (3,19), (3,35), (3,131), (16,17), (16,144), (18,19), (18,50), (18,146), (32,34), (32,160), (33,35), (33,49), (33,161), (48,49), (48,50), (48,176), (128,129), (128,130), (128,144), (128,160)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_179.map (· &&& dom_179)
def goalM : Nat := goal_179 &&& dom_179
def NN : Nat → Nat
|3=>1
|4=>4
|5=>10
|6=>4
|7=>1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0x4137a
|4,0=>0x33dbd2b6e918c150e2b2
|5,0=>0x3a0293448d2931525b1f227e21f54b0c09008a1e038bc034a6
|6,0=>0x7c7134fa944d5051d437
|7,0=>0x1d437
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf000f000f00000000000000000000000f000f000f0000f000f000f000f0000000000000000000c000c000c000cf000f000f000f0000000000000000000f000f000f000000000000000000000000000000000000f000c000f000c000000000000f00000000000000000000000000000000f000f000f000f0000000000000000000f0000000f00000000f0000000f00000000000000000000000000000000f000f000a000a0000000000000000000f000f000a000af000f000f000f0000000000000000000f000f000000000000f0000000f00000000000000000000000c0000000cc000f000c000f0000000000000000000c000c000c000c0000f0000000f00000000000000000000000a0000000a00000000c000f000000000000000000000000000c000cf000f000f000c0000000000000000000c000c000c000ca000a000a000a0000000000000000000a000a000a000a00000000f000f000000000000000000000000000e000ef000f000f000f00000000000000000000000000000000f0000000f00000000000000000000000f0000000f0000f000f000a000a00000000000000000000000000000000f000f000000000000000000000000000f000f00000000f000f000f000a0000000000000000000f0000000f0000c000c000c000c0000000000000000000c000c000c000cf000f000f000f0000000000000000000a000a000a000a
|_,_=>0
def stPool : Nat → Nat
|0=>0xca1418650a0d0b0ca141865a85061942830c2042cd41942830e650a0c32850690e2141a032850623dc50a0c32850d30cac0a0c30a1662850a30ca9418a141cc32840418820
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>4
|4,0=>0x26a3944a845
|5,0=>0x26b47682ced9ab2f652c8d8eb185
|6,0=>0xc8d79ac3535
|7,0=>0x6a5
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 23 then fld (dictB (i / 512) (i / 32 % 16)) 180 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 5 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 11 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))

def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 5 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
|0=>0x29a19509928241971519979819929a
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0x52320000002111000100
|6,0=>0x91817100
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 12 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 31), wireSAt ((code >>> 7) &&& 31)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 8 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmPalB : Nat → Nat
|0=>0x3fef7cd844f305100
|_=>0
def pmB : Nat → Nat → Nat
|5,0=>0x5300642010
|6,0=>0x9a87
|7,0=>0xa
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 4 (j % 128); fld (pmPalB (k / 32)) 6 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_178,5,runOps true dom_178 (0,roots_178) ops)] else [])++(if pm.testBit 1 then [(dom_147,5,runOps true dom_147 (0,roots_147) ops)] else [])++(if pm.testBit 2 then [(dom_145,4,runOps true dom_145 (0,roots_145) ops)] else [])++(if pm.testBit 3 then [(dom_162,4,runOps true dom_162 (0,roots_162) ops)] else [])++(if pm.testBit 4 then [(dom_163,5,runOps true dom_163 (0,roots_163) ops)] else [])++(if pm.testBit 5 then [(dom_177,5,runOps true dom_177 (0,roots_177) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_179 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · exact cpcs (by decide +kernel) lowS_145 _ g hchk
    · exact cpcs (by decide +kernel) lowS_162 _ g hchk
    · exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · exact cpcs (by decide +kernel) lowS_177 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_178 5 s (0, roots_178) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_179 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_178 h

def symsG : List (List (Nat × Nat)) := [[(rowMask28, 30)], [(rowMask35, 15)], [(rowMask25, 16), (rowMask0, 1)], [(rowMask28, 30), (rowMask35, 15)], [(rowMask37, 14), (rowMask33, 31)], [(rowMask25, 16), (rowMask28, 30), (rowMask33, 31)], [(rowMask25, 16), (rowMask37, 14), (rowMask0, 1)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_179 == dom_179) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_179 goalM v ys) : RunD true dom_179 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_179 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
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
theorem checked (s : Nat) (hs : s ≤ 7) : ∀ i < NN s, bar true dom_179 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_179 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD true dom_179 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_179 roots_179 goal_179 8 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_179

theorem lowS_179 : Lower true dom_179 roots_179 goal_179 8 := S_179.noCircuit

theorem lowS_199 : Lower true dom_199 roots_199 goal_199 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaa00000000000000aa00000000000000aa00000000000000aa, 64, 65)] (by decide +kernel) (by decide +kernel) lowS_198

namespace S_213
def pairsG : List (Nat × Nat) := [(1,17), (1,65), (1,129), (4,68), (4,132), (5,21), (5,69), (5,133), (16,17), (16,144), (20,21), (20,84), (20,148), (64,65), (64,68), (64,192), (80,81), (80,84), (80,208), (128,129), (128,132), (128,144), (128,192)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x7fffff
def pool6G : List Nat := []
def xsM : List Nat := roots_213.map (· &&& dom_213)
def goalM : Nat := goal_213 &&& dom_213
def NN : Nat → Nat
|6=>1
|_=>0
def HT : Nat → Nat → Nat
|6,0=>0x2bf94
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x330000000000000033000000000000003300000000000000330000c000c00000000000c000c00000000000c000c00000000000c000c220022000000000022002200000000002200220000000000220022cc00cc00000000000000000000000000cc00cc000000000000000330033000000000033003300000000000000000000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x4688
|_=>0
def stOffB : Nat → Nat → Nat
|6,0=>5
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 5 then fld (dictB (i / 512) (i / 32 % 16)) 214 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 3 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 7 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))

def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
|_=>0
def opOffB : Nat → Nat → Nat
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 8 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 7), wireSAt ((code >>> 5) &&& 7)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 5 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmPalB : Nat → Nat
|0=>0xf0
|_=>0
def pmB : Nat → Nat → Nat
|6,0=>1
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 1 (j % 128); fld (pmPalB (k / 32)) 4 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_212,5,runOps true dom_212 (0,roots_212) ops)] else [])++(if pm.testBit 1 then [(dom_149,5,runOps true dom_149 (0,roots_149) ops)] else [])++(if pm.testBit 2 then [(dom_209,5,runOps true dom_209 (0,roots_209) ops)] else [])++(if pm.testBit 3 then [(dom_197,5,runOps true dom_197 (0,roots_197) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_213 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_212 _ g hchk
    · exact cpcs (by decide +kernel) lowS_149 _ g hchk
    · exact cpcs (by decide +kernel) lowS_209 _ g hchk
    · exact cpcs (by decide +kernel) lowS_197 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_212 5 s (0, roots_212) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_213 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_212 h

def symsG : List (List (Nat × Nat)) := [[(rowMask22, 12), (rowMask32, 63)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_213 == dom_213) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_213 goalM v ys) : RunD true dom_213 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_213 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, bar true dom_213 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_213 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_213 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_213 roots_213 goal_213 7 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_213

theorem lowS_213 : Lower true dom_213 roots_213 goal_213 7 := S_213.noCircuit

def isoMvS_211 : List (Nat × Nat) := [(rowMask34, 48), (rowMask39, 8), (rowMask29, 4), (rowMask32, 63)]

theorem lowS_211 : Lower true dom_211 roots_211 goal_211 6 :=
  lower_iso isoMvS_211 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_199

def isoMvS_214 : List (Nat × Nat) := [(rowMask26, 32), (rowMask25, 16), (rowMask46, 24), (rowMask29, 4), (rowMask27, 7)]

theorem lowS_214 : Lower true dom_214 roots_214 goal_214 6 :=
  lower_iso isoMvS_214 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_151

def isoMvS_230 : List (Nat × Nat) := [(rowMask26, 32), (rowMask34, 48), (rowMask16, 2), (rowMask10, 3)]

theorem lowS_230 : Lower true dom_230 roots_230 goal_230 8 :=
  lower_iso isoMvS_230 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_179

theorem lowS_183 : Lower true dom_183 roots_183 goal_183 9 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(rowMask227, 128, 132)] (by decide +kernel) (by decide +kernel) lowS_179

def dzo_85_2:=0xcc00cc0000000000cc00cc

def gzo_85_2:=0xc800c80000000000880000

def gsh_85_2:=0x3200320000000000220000

theorem lowS_zo_85_2_85:Lower true dzo_85_2 roots_85 gzo_85_2 4:=lower_iso (d1:=dom_85) (roots1:=roots_85) (T1:=gsh_85_2) [(dom_85,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_85_2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [] (by decide +kernel) (by decide +kernel) lowS_85)

def dzo_213_2:=0xcc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc

def gzo_213_2:=0xcc00cc0000000000cc00cc0000000000c800c80000000000880000

def gsh_213_2:=0x330033000000000033003300000000003200320000000000220000

theorem lowS_zo_213_2_85:Lower true dzo_213_2 roots_213 gzo_213_2 5:=lower_iso (d1:=dom_213) (roots1:=roots_213) (T1:=gsh_213_2) [(dom_213,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_213_2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x330033000000000033003300000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_85)

namespace S_215
def pairsG : List (Nat × Nat) := [(1,17), (1,65), (1,129), (2,130), (3,19), (3,67), (3,131), (4,68), (4,132), (5,21), (5,69), (5,133), (6,70), (6,134), (7,23), (7,71), (7,135), (16,17), (16,144), (18,19), (18,146), (20,21), (20,84), (20,148), (22,23), (22,86), (22,150), (64,65), (64,68), (64,192), (66,67), (66,70), (66,194), (80,81), (80,84), (80,208), (82,83), (82,86), (82,210), (128,129), (128,130), (128,132), (128,144), (128,192)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_215.map (· &&& dom_215)
def goalM : Nat := goal_215 &&& dom_215
def NN : Nat → Nat
|3=>10
|4=>55
|5=>114
|6=>61
|7=>11
|8=>1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0xdeb48b9f97a43189ff3a80830384d31d2ad133800380501529
|4,0=>0xe72e9d60f4c836cc1fc5b410eb1fc8b1b2bb14e2b10bda6ef6a2bfea04d69de4f9cd7994b9b904198ac208730683c317a36779a20725ad70d8d70a8c6b46e649606361262db86030a50eb650799500ac4d0324c1af4bb864a4ca497b9468d540c0039a8437c6733b333179230f87290e026631262bf1fd501f5be127cd117fb0ba0c0aa2a0a16206709
|5,0=>0xfcd75e5279df46dd2ccbc5ae0bcda3bc0ccb95b2ae9caaaf4ca1bfe9df189dcf09858e97f839720993d85933c192f24926758fd9c8d1c58bb158b1d48873c87b5e87b22854e0849a7825c181c9b817d881625806777f7e97919277bf47586e6e09d6c8f26916d6789562dde611ce608a6605c4601e65e7155e0a05dc035d1495c30959d8b58fcc586de580b6533df51dcd5029a4fac74ecd64ebd64d2004c5ae474bf44b2a42f76406ea3eb5e3dda73c4f13b1c736b28350bd34407340cf333de315232be002b6fc289e32731b2591c24c32239e2229121fdd71fcae1f04d1e9e0197911927c1765e14ef1136ca1352f112860fbf30f9a90d4f70c2150b5400b3350a89a09a590805106ca505c1c05673025290189c010d500628004e3
|6,0=>0xe04dfdd5fbd4b67d414fb8f50b533db49beae5d0ac9a9a0dfc9a00d89e5488f7787594858f38589983cb77e4257e2917e00f7c9d77854175c2271eaa6bb245b73c59c5850e604dd524ce3149ff048cee42d0442bd53fccc3eb523e2fc3b8443a1ac3639a33bfa3210d2ccfb299e2289f52896c27963214d82066b1f6991ef391e02c1c6d914aa9144481396d1183a10d410d3fd060c704467
|7,0=>0xc35bbc344094ea3935e992f0137f6f34c3e2b05a1e5ed1ccd917b3d
|8,0=>0xda052
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x5000500000000000500050000000000fa00fa0000000000fa00fa0000000000000000fe00fe00000000000000000000000000fe00fe0f000f00000000000f000300000000000f000f00000000000f0000ff00ff0000000000ff00ff0000000000fa00fa0000000000fa00fa0000aa00000000000000bb00000000000000aa00000000000000aa0f000f00000000000b000b00000000000f000f00000000000a000aff00ff0000000000ff00cc0000000000ff00ff0000000000ff00ccaa00aa0000000000aa00aa0000000000aa00aa0000000000aa0000fe00fe0000000000fe00fe00000000000000000000000000000000fe00fe0000000000fe00fe0000000000fe00fe0000000000fe00feff00ff0000000000aa00aa0000000000ff00ff0000000000aa00aa0f000f000000000003000300000000000f000f0000000000030000ff00ff0000000000ff00000000000000ff00ff0000000000ff0000ff00ff0000000000bb00bb0000000000ff00ff0000000000aa00aaff00ff0000000000ff00ff00000000000000000000000000000000ff00ff0000000000cc00cc0000000000ff00ff0000000000cc00ccfa00fa0000000000fa00fa0000000000fa00fa0000000000000000ff00fe0000000000ff00fe0000000000ff00000000000000ff0000fa00fa0000000000fa00fa0000000000fa00fa0000000000fa00facc00cc0000000000cc00cc0000000000cc00cc0000000000cc00ccff00ff0000000000ff00000000000000aa00aa0000000000aa0000ff00ff0000000000ff00ee0000000000ff00000000000000ff0000ff00ff0000000000ff00ff0000000000aa00aa0000000000aa00aaff00ff0000000000ff00ff0000000000ff00ff0000000000000000ff00000000000000ff00000000000000ff00000000000000ff0000ff00ff0000000000ff00ff0000000000f000f00000000000f000f0aa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aaff00ff0000000000fe00fe0000000000ff00ff0000000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff0000f000f00000000000f000f00000000000f000f00000000000f000f0ff00ff0000000000ff00ee0000000000aa00aa0000000000aa00aaff00ff00000000000000000000000000ff00ff0000000000000000
|0,1=>0x5500550000000000550055000000000055005500000000005500000000af00000000000000af00000000000000aa00000000000000aa330033000000000033003300000000003300330000000000220022ff00ff0000000000ff00ff0000000000ff00ff0000000000aa00aaff00ff0000000000fe00fe0000000000f000f00000000000f000f0ff00ff0000000000ee00ee0000000000000000000000000000000055005500000000005500440000000000550055000000000055004400000000000000000000000000000000ff00ff0000000000aa00aa5100510000000000510051000000000050005000000000005000500000000000000000fb00fb00000000000000000000000000fa00fafe00fe0000000000fe00fe0000000000aa00aa0000000000aa00aa0000000000000000bb00bb00000000000000000000000000aa00aaff00ff00000000003300330000000000ff00ff0000000000000000ab00ab0000000000ab00ab0000000000aa00aa0000000000aa00aa33003300000000003300330000000000000000000000000000000000000000000000000000000000000000fa00fa0000000000fa00fa0f000f000000000003000300000000000f000f000000000002000255005500000000005500110000000000550055000000000055000000000000000000000000bb000000000000000000000000000000aaff00ff0000000000fa00fa0000000000ff00ff0000000000000000ff00ff0000000000ff00aa0000000000ff00000000000000ff0000bb00bb0000000000bb00bb0000000000aa00aa0000000000aa00aa0000bb00000000000000bb00000000000000aa00000000000000aa0000ab00000000000000ab00000000000000aa00000000000000aabb00bb0000000000bb00bb0000000000bb00bb0000000000aa00aaff00ff00000000000000bb0000000000ff00ff00000000000000aaff00ff0000000000ff00cc00000000000000000000000000000000ff00fa0000000000ff00fa0000000000ff00000000000000ff0000ff00ff0000000000ee00ee0000000000ff00ff0000000000ee00eeaa00aa0000000000bb00bb0000000000aa00aa0000000000aa00aaff00ff0000000000ff00ff0000000000ff00000000000000ff0000ff00ff0000000000ff00aa0000000000aa00aa0000000000aa00aa
|0,2=>0xcc00cc0000000000cc00cc0000000000ff00ff0000000000ee00ee0000330000000000000033000000000000000000000000000000000000ff00000000000000ff00000000000000ff00000000000000aaff00ff0000000000ff000000000000000000000000000000000000ff00ff00000000000000ff0000000000ff00ff00000000000000000000000000000000ff00ff00000000000000000000000000aa00aaff00330000000000ff00330000000000ff00000000000000ff0000550055000000000055005500000000000000000000000000000000ff00ff00000000000000000000000000fa00fa00000000000000000f000f000000000005000500000000000f000f0000000000000000ff00cc0000000000ff00cc0000000000ff00cc0000000000ff00ccff00ff0000000000ff00f00000000000f000f00000000000f000f0ff00330000000000ff00330000000000ff00330000000000ff000000000000000000000000ff000000000000000000000000000000000f000f00000000000f000f00000000000f000f00000000000000000000ff00000000000000ff00000000000000aa00000000000000aafe00fe0000000000fe00fe0000000000cc00cc0000000000cc00cc00000000000000000000aa0000000000aa00aa0000000000aa00aaff00ff0000000000ee00ee0000000000cc00cc0000000000cc00cc0f000f00000000000f000f00000000000f000f00000000000f0000330033000000000033003300000000003000300000000000300030330033000000000033003300000000003300330000000000330000ff00ff00000000000000ff0000000000ff00ff00000000000000aaff00ff0000000000ff00330000000000ff00ff0000000000ff0000fc00fc0000000000fc00fc0000000000fc00fc0000000000fc00fc00000000000000000000000000000000ff00ff0000000000ff0000bb00bb0000000000bb00bb0000000000ba00ba0000000000ba00ba330033000000000033003300000000002200220000000000220022cc00cc0000000000cc00cc0000000000ff00ff0000000000ff00ccfa00fa0000000000fa00fa00000000000000000000000000000000ff00ff0000000000fe00fe0000000000ff00ff0000000000fe00fecc00cc0000000000fe00fe0000000000cc00cc0000000000fe00fe
|0,3=>0x550055000000000000000000000000000000001100110000000000110011000000000000000000000000000000000300030000000000030003000000000000000000000000000000000000ff00000000000000ff00000000000000ff00000000000000000000000000000000ff000000000000000000000000000000ff00000000000000000000ff00ff00000000000000000000000000000000ff00000000000000ff00ff0000000000ff00000000000000ff0000000033000000000000003300000000000000220000000000000022ff00ff00000000003300330000000000ff00ff000000000022002200000000000000003300330000000000000000000000000000000000000000000000003300330000000000000000000000000022002200000000000000000000ff000000000000000000000000000000aa0000000000000000ff00ff00000000000000000000000000ff00000000000000000000ff00ff00000000000000000000000000fa00fa0000ff00000000000000ff00000000000000fa00000000000000fa000000000000000033003300000000000000000000000000330000330033000000000033003300000000003300330000000000000000ff00ff0000000000ff00000000000000ff00ff0000000000000000aa00aa0000000000ff00ff0000000000aa00aa0000000000aa00aa0300030000000000030003000000000002000200000000000200020b000b00000000000b000b00000000000a000a00000000000a000aff00ff00000000001100110000000000ff00ff00000000000000005500550000000000550000000000000055005500000000005500000f000f000000000003000300000000000f000f0000000000000000ee00ee0000000000ee00ee0000000000ee00ee0000000000ee00ee0000ff00000000000000ff00000000000000000000000000000000000000000000000011001100000000000000000000000000000000ff00ff0000000000aa00aa00000000000000000000000000000000ff00000000000000ff00330000000000ff00000000000000ff0000fb00fb0000000000fb00fb0000000000fa00fa0000000000fa00fa0000000000000000fa00fa00000000000000000000000000fa00fa000000000000000000003300000000000000000000000000000000
|0,4=>0xff00ff0000000000ff00aa0000000000ff00ff0000000000ff00aa550055000000000055005500000000005500550000000000000000550055000000000055005500000000005000500000000000500050
|_,_=>0
def stPool : Nat → Nat
|0=>0xc09080e0d050011070d22001121020c2000070c150f110706050017070c09000f071f0c0500071e0d151113051d0011071c05001702051b001107051a00111902180011070209001713160d15110705140011130c050f11130d12110e020900070d09040710090f0e0d09000d0c0b080a020900070201080706050403020100
|1=>0x8070205041107020c092c130d053311070d3200111302120511130d15113124020c09000e02050011071630090007052f001113022e0011070223090807051d001102052d0011070d0c092c13020100110710050f112b020c09000d2a2900110205280011070d27001102052600111302050825240d0c0900130d231511130d
|2=>0x440011240d0c050011070d09001131431302050011130d0c050811071c0c05004207022309001107410d05001107400d05001107020c3f0011020c053e00110702053d0011130d0c3c11073b050011070209003a070d153311130d390011130d0c3811070d3700110736020511071c0c052c070d350011070d340011070d1009
|3=>0x20c050052070205001125070500511131070d0c052c1147020550001107020c15090819210205001119460205001107024f05001113020c4e001107024d05001107060c050042070c054c0011070d054b00111302054a00112b020c050011020c0549001148070205001107471c0500111346020c0508070245050011130205
|4=>0x1107020534001113020c05085c43070205001107021009050813020c055b11130d05001131070d0c5a0011135902050011070d2a001113020c050858070232050011070d0c055711070c05005611070d10090011070d23150011070d0c150811130215051131070d0c09080055460205001107540c05001153070205001146
|5=>0x2150533110702056a0011130267690011070d2a0011310705006811026709500011070d1005081146020c05006613020539001107020500116513020c38051107020537001107020c052c1107020c09006463070205001107620d0500110702054a0011130d610c051113020500116007025f05001113020500115e020c055d
|6=>0x5c13020c3c051119130d050011070d05001117130205086f110702057000110705006811310705006f511107020500113a13020c056e11070d0c6d0011070d610c1511551302050811070d022a00110702056c00111913021505110705330068110702056b0011070d05330011020c050b001119130205081107021205001107
|7=>0x110730020c05001107160d0500117b02050011317907020c050011020550780011070d4f050011557302050011070205770011070d05001176190702050811070205750011020c057400111373020c0511190302050011130c05085111130d0c1511070d720c05110702050011600210055000110d0c0571001107020c0508
|8=>0x511107020500117e070602054b001107020c6d05001107020c055b00110313020c050011070205006f1107020c0508005807020c0500115c07020500117d07060267050011070d0c09001107020c05007c110747060500110702150500113107020c0500116413020c050011520702050800113107022a0500113119070205
|9=>0x113107020c3c05001113070205001131070d0c05001142020c09055000110307020c05001107470209050011130d0c05001107020c0500115207160d0205001113020c050011660702054b001113020c15051107020c38050011070d610c0500110702090544001107470d0500111307020c05081107020c0500117f070c05
|10=>0x50011580702231505001107020c090508008213020c05001107020c05008111070205330011070d1005001107020c1509001159070205001131070602050011311346020c050011070210050811070d060c0500110702670508001113020c0905001107022305001159070205001107020c05800011070d0c0500117a130205
|11=>0x7020c0500110706020c05001107020500113113020c0500111307020c05001107020c0500116607026705001107020c1505001107020c050800115507020500117b020c05001107020c
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>0x1220204038806100a20104018802100220004
|4,0=>0x4d9498a92c524ea48948ea9185226a439484a90451fea3e947aa8f051d6a399470a8dc51aea349466a8c85186a2f945ca8b4515ea2a9452a8a05136a259448a88c510ea20943ea87850e6a1b9434a86450bea16942aa8505096a119420a83c506ea0c9416a8285
|5,0=>0x568cab995432a26538ca59948328a6508c9f993c327264d8c999930325a64a8c939924aa43647ac8dd918b22b644ac87d90cb213641ac81d900b1fb63eac7bd8f4b1e363bac75d8e8b1cb638ac6fd8dcb1b3635ac69d8d0b19b632ac63d8c4b18362fac5dd8b8b16b62cac57d8acb153629ac51d8a0b13b6
|5,1=>0x1ef33d867a4cf319e333c06774ced19d733a86744ce755cbb3916716ce159bfb37966e6cdb59b3b36166b6cd559a7b3496686ccf599bb3316656cc9598fb3196626cc35983b30165f6cbd5977b2e965c8ab7996c32d26598cb1996032ba6
|6,0=>0x5757adcf59deb03d5a6aa8d535ea33d3f7a70f4c9a95bd247a3af45da88b50a7a06f3f5a7b3cef79d0f385e6d3cd3799ad319e5fbcb87964d2b1a52bc9e792ef245a453c8378fad1dda383c6978c4f16de2ab44e788ef105a1d3c34685af09da103c197824f02de023bfe67eeefc59f5b3e47
|7,0=>0x16f5edbb5b16b54f68deceb5967b1ef625ac1b57c7
|8,0=>0x5c46
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 131 then fld (dictB (i / 512) (i / 32 % 16)) 216 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 8 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 15 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))

def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 8 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
|0=>0x1141c01020541401070045445020544c31070045844020543022231100046001144c31050041c01130904c311305c1c010c11808ce0c1181c26051140045020546417130c41c011511034030700414451311800260c1183001191101445001141c450605408450c1184c47051143441020543403050840045231106417020541445001140015070043431020543420
|1=>0x70041833021141401070045447050043403020543026051140831020540045070045446050040822001143046060cc0845057a40046006641c46131141c010c0880045051184c440700408c60c1183015021141445020541c22001140831021143046151101401131181c010c1183046130c41c010d11c08150d0c408150700c3046077a400462100c0045131141c01
|2=>0x21143046070041c01071183015050040045070c41c03051183055050041445001144c150700414220011400c50c11830010205414450c11830461311c1c010011408150211430150011414450700430550731430460605c08450011808150c1181c011511414010c1183444020541c26051148401071141445020c40815070044c46070043431020541c46
|_=>0
def opOffB : Nat → Nat → Nat
|4,0=>0xa2000091000072000000000000000000000000000000000000000000000000000000052000000000000000000000000000000000000000000000000000000000000000000000000000000000000014000001
|5,0=>0x1f10000000001d20000000000000000000001c11b10001a10001910000000000001810000000000000000000000001710000000001521410000000000000000000000000000000001220000000000001111010000000f10d20c1000000000
|5,1=>0x4310000004210000000004023e23b30000000000000003a13733523410000000003310003210003110000002e30000000002d12c10000000002a2291272252232000203000000000
|6,0=>0xb12af2ad2ab2a92a72a61a51a41a22a119f29d29b29a19829629429229028f18d28b28928728528328127f27d27b27927727527327126f26d26c16a26826626426226115f25d25b25925725525415225024f14e14c24a2482462442
|7,0=>0xbd1bc1bb1ba1b91b81b71b61b51b41b31
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 18 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 255), wireSAt ((code >>> 10) &&& 255)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 12 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmPalB : Nat → Nat
|0=>0x3450321020001bc0185013901210120011101030102010101000084008200810080006000400021002000190018001400100009000800050004000200010000
|1=>0x41103b3338013339333131b3303130012a09201120021b3d13b113791371133913291321131112291101102110000b500a040880082c08290820081108010420
|2=>0xf339f011e268c114c029bb31b329aa699b31932988a982408201811180a85000
|_=>0
def pmB : Nat → Nat → Nat
|4,0=>0x240030008000000000000000000000000000000024000000000000000000000000000000000000000000000000038005
|5,0=>0x40000200000013ab800000000092a0428000009000e01a800054000001c280000020716108002c00000004c0000074000000000000982800e003800000007060000000000002200000303c000000000000000000018000000040200007a01a00000
|6,0=>0x1b305c34b662e0445514a25327271432b05292eadb285c04f8c6ebc09e84c9c0119321a27a1922373353ad032099a0305fba28c5ca1
|7,0=>0x1267af7729a308cf9dc7
|8,0=>0x3c
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 7 (j % 128); fld (pmPalB (k / 32)) 16 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_213,7,runOps true dom_213 (0,roots_213) ops)] else [])++(if pm.testBit 1 then [(dom_197,5,runOps true dom_197 (0,roots_197) ops)] else [])++(if pm.testBit 2 then [(dom_212,5,runOps true dom_212 (0,roots_212) ops)] else [])++(if pm.testBit 3 then [(dom_147,5,runOps true dom_147 (0,roots_147) ops)] else [])++(if pm.testBit 4 then [(dom_198,5,runOps true dom_198 (0,roots_198) ops)] else [])++(if pm.testBit 5 then [(dom_151,6,runOps true dom_151 (0,roots_151) ops)] else [])++(if pm.testBit 6 then [(dom_209,5,runOps true dom_209 (0,roots_209) ops)] else [])++(if pm.testBit 7 then [(dom_149,5,runOps true dom_149 (0,roots_149) ops)] else [])++(if pm.testBit 8 then [(dom_214,6,runOps true dom_214 (0,roots_214) ops)] else [])++(if pm.testBit 9 then [(dom_211,6,runOps true dom_211 (0,roots_211) ops)] else [])++(if pm.testBit 10 then [(dom_145,4,runOps true dom_145 (0,roots_145) ops)] else [])++(if pm.testBit 11 then [(dzo_85_2,4,runOps true dzo_85_2 (0,roots_85) ops)] else [])++(if pm.testBit 12 then [(dom_199,6,runOps true dom_199 (0,roots_199) ops)] else [])++(if pm.testBit 13 then [(dom_195,5,runOps true dom_195 (0,roots_195) ops)] else [])++(if pm.testBit 14 then [(dzo_213_2,5,runOps true dzo_213_2 (0,roots_213) ops)] else [])++(if pm.testBit 15 then [(dom_85,4,runOps true dom_85 (0,roots_85) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_215 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · exact cpcs (by decide +kernel) lowS_197 _ g hchk
    · exact cpcs (by decide +kernel) lowS_212 _ g hchk
    · exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · exact cpcs (by decide +kernel) lowS_198 _ g hchk
    · exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · exact cpcs (by decide +kernel) lowS_209 _ g hchk
    · exact cpcs (by decide +kernel) lowS_149 _ g hchk
    · exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · exact cpcs (by decide +kernel) lowS_145 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_85_2_85 _ g hchk
    · exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_213_2_85 _ g hchk
    · exact cpcs (by decide +kernel) lowS_85 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_213 7 s (0, roots_213) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_215 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_213 h

def symsG : List (List (Nat × Nat)) := [[(rowMask22, 12), (rowMask32, 63)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_215 == dom_215) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_215 goalM v ys) : RunD true dom_215 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_215 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 10 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 10 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 55 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 55 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 114 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 114 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 61 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 61 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 11 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 11 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 8) : ∀ i < NN s, bar true dom_215 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
  · exact z8 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_215 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 8) (h : RunD true dom_215 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_215 roots_215 goal_215 9 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_215

theorem lowS_215 : Lower true dom_215 roots_215 goal_215 9 := S_215.noCircuit

theorem lowS_231 : Lower true dom_231 roots_231 goal_231 9 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(rowMask232, 64, 65)] (by decide +kernel) (by decide +kernel) lowS_230

def isoMvS_243 : List (Nat × Nat) := [(rowMask34, 48), (rowMask39, 8), (rowMask29, 4), (rowMask32, 63)]

theorem lowS_243 : Lower true dom_243 roots_243 goal_243 9 :=
  lower_iso isoMvS_243 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_231

def isoMvS_245 : List (Nat × Nat) := [(rowMask46, 24), (rowMask11, 6)]

theorem lowS_245 : Lower true dom_245 roots_245 goal_245 9 :=
  lower_iso isoMvS_245 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_215

def isoMvS_246 : List (Nat × Nat) := [(rowMask26, 32), (rowMask34, 48), (rowMask220, 56), (rowMask29, 4), (rowMask11, 6), (rowMask27, 7)]

theorem lowS_246 : Lower true dom_246 roots_246 goal_246 9 :=
  lower_iso isoMvS_246 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_183

namespace S_247
def pairsG : List (Nat × Nat) := [(1,17), (1,65), (1,129), (2,34), (2,130), (3,19), (3,35), (3,67), (3,131), (4,68), (4,132), (5,21), (5,69), (5,133), (6,38), (6,70), (6,134), (7,23), (7,39), (7,71), (7,135), (16,17), (16,144), (18,19), (18,50), (18,146), (20,21), (20,84), (20,148), (22,23), (22,54), (22,86), (22,150), (32,34), (32,160), (33,35), (33,49), (33,97), (33,161), (36,38), (36,100), (36,164), (37,39), (37,53), (37,101), (37,165), (48,49), (48,50), (48,176), (52,53), (52,54), (52,116), (52,180), (64,65), (64,68), (64,192), (66,67), (66,70), (66,98), (66,194), (80,81), (80,84), (80,208), (82,83), (82,86), (82,114), (82,210), (96,97), (96,98), (96,100), (96,224), (112,113), (112,114), (112,116), (112,240), (128,129), (128,130), (128,132), (128,144), (128,160), (128,192)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x1ffffffffffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_247.map (· &&& dom_247)
def goalM : Nat := goal_247 &&& dom_247
def NN : Nat → Nat
|10=>1
|_=>0
def HT : Nat → Nat → Nat
|10,0=>0x6bf33
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00ccaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aaff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000ff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x1ac688
|_=>0
def stOffB : Nat → Nat → Nat
|10,0=>7
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 7 then fld (dictB (i / 512) (i / 32 % 16)) 248 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 3 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 7 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))

def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
|_=>0
def opOffB : Nat → Nat → Nat
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 8 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 7), wireSAt ((code >>> 5) &&& 7)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 5 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmPalB : Nat → Nat
|0=>0xfc0
|_=>0
def pmB : Nat → Nat → Nat
|10,0=>1
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 1 (j % 128); fld (pmPalB (k / 32)) 6 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_246,9,runOps true dom_246 (0,roots_246) ops)] else [])++(if pm.testBit 1 then [(dom_183,9,runOps true dom_183 (0,roots_183) ops)] else [])++(if pm.testBit 2 then [(dom_245,9,runOps true dom_245 (0,roots_245) ops)] else [])++(if pm.testBit 3 then [(dom_243,9,runOps true dom_243 (0,roots_243) ops)] else [])++(if pm.testBit 4 then [(dom_231,9,runOps true dom_231 (0,roots_231) ops)] else [])++(if pm.testBit 5 then [(dom_215,9,runOps true dom_215 (0,roots_215) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_247 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · exact cpcs (by decide +kernel) lowS_215 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_246 9 s (0, roots_246) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_247 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_246 h

def symsG : List (List (Nat × Nat)) := [[(rowMask28, 30)], [(rowMask22, 12), (rowMask32, 63)], [(rowMask22, 12), (rowMask28, 30), (rowMask32, 63)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_247 == dom_247) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_247 goalM v ys) : RunD true dom_247 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_247 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
private theorem z6 : ∀ i, 0 ≤ i → i < 0 → Z 6 i = true := by omega
private theorem z7 : ∀ i, 0 ≤ i → i < 0 → Z 7 i = true := by omega
private theorem z8 : ∀ i, 0 ≤ i → i < 0 → Z 8 i = true := by omega
private theorem z9 : ∀ i, 0 ≤ i → i < 0 → Z 9 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 10) : ∀ i < NN s, bar true dom_247 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
  · exact z8 i (Nat.zero_le i) hi
  · exact z9 i (Nat.zero_le i) hi
  · exact z10 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_247 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

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
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_247 roots_247 goal_247 11 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_247

theorem lowS_247 : Lower true dom_247 roots_247 goal_247 11 := S_247.noCircuit

end B5

namespace B6
def dom_53 : Nat := 0x33003300330033

def goal_53 : Nat := 0xfafafafaaaaa0000fafafafaaaaa0000fafafafaaaaa0000fafafafaaaaa0000

def roots_53 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_81 : Nat := 0x300030000000000030003

def goal_81 : Nat := 0xffffaaaaffffaaaaaaaa0000aaaa0000ffffaaaaffffaaaaaaaa0000aaaa0000

def roots_81 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_101 : Nat := 0x33000000330000003300000033

def goal_101 : Nat := 0xfafafafaaaaaaaaafafafafa00000000fafafafaaaaaaaaafafafafa00000000

def roots_101 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_113 : Nat := 0x30003000300030003000300030003

def goal_113 : Nat := rowMask265

def roots_113 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033

def goal_117 : Nat := 0xfffffafaffffaaaafafafafaaaaa0000fffffafaffffaaaafafafafaaaaa0000

def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_149 : Nat := rowMask298

def goal_149 : Nat := 0xfafafafafafafafafafafafafafafafaaaaa0000aaaa0000aaaa0000aaaa0000

def roots_149 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_161 : Nat := 0x30000000300000000000000000000000300000003

def goal_161 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaa00000000aaaaaaaa00000000

def roots_161 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_164 : Nat := 0x110000001100000000000000000000001100000011

def goal_164 : Nat := rowMask266

def roots_164 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_165 : Nat := 0x330000003300000000000000000000003300000033

def goal_165 : Nat := 0xfffffffffafafafafffffffffafafafafafafafa00000000fafafafa00000000

def roots_165 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_177 : Nat := rowMask319

def goal_177 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaa0000aaaaaaaaaaaa0000

def roots_177 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_181 : Nat := rowMask260

def goal_181 : Nat := 0xfffffffffafafafafffffffffafafafafafafafaaaaa0000fafafafaaaaa0000

def roots_181 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_193 : Nat := 0x3000000000000000300000000000000030000000000000003

def goal_193 : Nat := 0xffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000000000000

def roots_193 : List Nat := [xs256.getD 0 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_197 : Nat := rowMask310

def goal_197 : Nat := 0xfffffffffffffffffafafafafafafafaaaaaaaaaaaaaaaaa0000000000000000

def roots_197 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_209 : Nat := rowMask204

def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_212 : Nat := rowMask241

def goal_212 : Nat := 0xfffffffffffffffff0f0f0f0f0f0f0f0ffff0000ffff00000000000000000000

def roots_212 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := rowMask149

def goal_213 : Nat := 0xfffffffffffffffffafafafafafafafaffffaaaaffffaaaaaaaa0000aaaa0000

def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_225 : Nat := rowMask289

def goal_225 : Nat := 0xffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000

def roots_225 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_228 : Nat := rowMask285

def goal_228 : Nat := 0xfffffffffffffffffffffffff0f0f0f0f0f0f0f000000000f0f0f0f000000000

def roots_228 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033

def goal_229 : Nat := 0xfffffffffffffffffffffffffafafafafafafafaaaaaaaaafafafafa00000000

def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_241 : Nat := rowMask221

def goal_241 : Nat := 0xffffffffffffffffffffffffaaaaaaaaffffaaaaffffaaaaaaaaaaaaaaaa0000

def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_244 : Nat := rowMask218

def goal_244 : Nat := 0xfffffffffffffffffffffffff0f0f0f0fffff0f0ffff0000f0f0f0f000000000

def roots_244 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := rowMask87

def goal_245 : Nat := 0xfffffffffffffffffffffffffafafafafffffafaffffaaaafafafafaaaaa0000

def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

theorem lowS_81 : Lower true dom_81 roots_81 goal_81 4 := lower_iso (d1 := B5.dom_145) (roots1 := B5.roots_145) (T1 := B5.goal_145) [(rowMask51, 64)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_145

theorem lowS_161 : Lower true dom_161 roots_161 goal_161 4 := lower_iso (d1 := B5.dom_145) (roots1 := B5.roots_145) (T1 := B5.goal_145) [(rowMask25, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_145

theorem lowS_164 : Lower true dom_164 roots_164 goal_164 4 := lower_iso (d1 := B5.dom_145) (roots1 := B5.roots_145) (T1 := B5.goal_145) [(rowMask0, 1), (rowMask10, 3), (rowMask25, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_145

theorem lowS_193 : Lower true dom_193 roots_193 goal_193 4 := lower_iso (d1 := B5.dom_145) (roots1 := B5.roots_145) (T1 := B5.goal_145) [(rowMask25, 16), (rowMask34, 48)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_145

theorem lowS_165 : Lower true dom_165 roots_165 goal_165 5 := lower_iso (d1 := B5.dom_197) (roots1 := B5.roots_197) (T1 := B5.goal_197) [(rowMask26, 32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_197

theorem lowS_53 : Lower true dom_53 roots_53 goal_53 4 := lower_iso (d1 := B5.dom_85) (roots1 := B5.roots_85) (T1 := B5.goal_85) [(rowMask26, 32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_85

theorem lowS_101 : Lower true dom_101 roots_101 goal_101 4 := lower_iso (d1 := B5.dom_85) (roots1 := B5.roots_85) (T1 := B5.goal_85) [(rowMask25, 16), (rowMask34, 48)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_85

theorem lowS_113 : Lower true dom_113 roots_113 goal_113 5 := lower_iso (d1 := B5.dom_147) (roots1 := B5.roots_147) (T1 := B5.goal_147) [(rowMask44, 127), (rowMask16, 2), (rowMask11, 6), (rowMask28, 30), (rowMask35, 15), (rowMask34, 48)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_147

theorem lowS_149 : Lower true dom_149 roots_149 goal_149 4 := lower_iso (d1 := B5.dom_85) (roots1 := B5.roots_85) (T1 := B5.goal_85) [(rowMask51, 64)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_85

theorem lowS_177 : Lower true dom_177 roots_177 goal_177 5 := lower_iso (d1 := B5.dom_147) (roots1 := B5.roots_147) (T1 := B5.goal_147) [(rowMask44, 127), (rowMask16, 2), (rowMask11, 6), (rowMask28, 30), (rowMask37, 14), (rowMask35, 15)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_147

theorem lowS_197 : Lower true dom_197 roots_197 goal_197 5 := lower_iso (d1 := B5.dom_147) (roots1 := B5.roots_147) (T1 := B5.goal_147) [(rowMask16, 2), (rowMask25, 16), (rowMask34, 48)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_147

theorem lowS_212 : Lower true dom_212 roots_212 goal_212 4 := lower_iso (d1 := B5.dom_85) (roots1 := B5.roots_85) (T1 := B5.goal_85) [(rowMask0, 1), (rowMask27, 7), (rowMask33, 31), (rowMask44, 127), (rowMask32, 63)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_85

theorem lowS_225 : Lower true dom_225 roots_225 goal_225 5 := lower_iso (d1 := B5.dom_197) (roots1 := B5.roots_197) (T1 := B5.goal_197) [(rowMask32, 63), (rowMask29, 4), (rowMask22, 12), (rowMask36, 28), (rowMask10, 3)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_197

theorem lowS_228 : Lower true dom_228 roots_228 goal_228 5 := lower_iso (d1 := B5.dom_147) (roots1 := B5.roots_147) (T1 := B5.goal_147) [(rowMask10, 3), (rowMask11, 6), (rowMask28, 30), (rowMask34, 48), (rowMask37, 14)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_147

def dzo_113_4:=0x300030003000300030003000300030

def gzo_113_4:=0x300030003000200030003000200000

def gsh_113_4:=0x30003000300020003000300020000

theorem lowS_zo_113_4_81:Lower true dzo_113_4 roots_113 gzo_113_4 5:=lower_iso (d1:=dom_113) (roots1:=roots_113) (T1:=gsh_113_4) [(dom_113,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_113_4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x30003000000000003000300000000,0,32)] (by decide +kernel) (by decide +kernel) lowS_81)

namespace S_117
def pairsG : List (Nat × Nat) := [(1,17), (1,33), (1,65), (4,36), (5,21), (5,37), (5,69), (16,17), (16,80), (20,21), (20,52), (20,84), (32,33), (32,36), (48,49), (48,52), (48,112), (64,65), (64,80), (68,69), (68,84), (68,100), (96,97), (96,100), (96,112)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_117.map (· &&& dom_117)
def goalM : Nat := goal_117 &&& dom_117
def NN : Nat → Nat
|4=>2
|5=>3
|6=>1
|_=>0
def HT : Nat → Nat → Nat
|4,0=>0x8a56840839
|5,0=>0x7af916dc843bf89
|6,0=>0xc3dee
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xcc00cc00cc00cc00cc000000cc000000000000000000022002200220022cc000000cc000000cc000000cc0003300330033003300220022002200220000cc000000cc000000880000008b30033000000000033003300000000c000c000c000c000c000c000c000c220022002200220022002200220022cc000000cc0000008800000088000330033003300330000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x473204973204732804736204325043210
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>0x15405
|5,0=>0x166418a6
|6,0=>0x1c5
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 10 then fld (dictB (i / 512) (i / 32 % 16)) 118 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 4 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 10 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))

def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 3 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
|0=>0x83
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0x20
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 10 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 15), wireSAt ((code >>> 6) &&& 15)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 5 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmPalB : Nat → Nat
|0=>0x1f69040
|_=>0
def pmB : Nat → Nat → Nat
|5,0=>0x5a
|6,0=>4
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 3 (j % 128); fld (pmPalB (k / 32)) 5 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_113,5,runOps true dom_113 (0,roots_113) ops)] else [])++(if pm.testBit 1 then [(dom_101,4,runOps true dom_101 (0,roots_101) ops)] else [])++(if pm.testBit 2 then [(dom_53,4,runOps true dom_53 (0,roots_53) ops)] else [])++(if pm.testBit 3 then [(dzo_113_4,5,runOps true dzo_113_4 (0,roots_113) ops)] else [])++(if pm.testBit 4 then [(dom_81,4,runOps true dom_81 (0,roots_81) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_117 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · exact cpcs (by decide +kernel) lowS_101 _ g hchk
    · exact cpcs (by decide +kernel) lowS_53 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_113_4_81 _ g hchk
    · exact cpcs (by decide +kernel) lowS_81 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_113 5 s (0, roots_113) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_117 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_113 h

def symsG : List (List (Nat × Nat)) := [[(rowMask34, 48)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_117 == dom_117) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_117 goalM v ys) : RunD true dom_117 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_117 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, bar true dom_117 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_117 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

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
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_117 roots_117 goal_117 7 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_117

theorem lowS_117 : Lower true dom_117 roots_117 goal_117 7 := S_117.noCircuit

def dzo_165_16:=0x3300000033000000000000000000000033000000330000

def gzo_165_16:=0x3300000032000000000000000000000032000000220000

def gsh_165_16:=0x330000003200000000000000000000003200000022

theorem lowS_zo_165_16_164:Lower true dzo_165_16 roots_165 gzo_165_16 5:=lower_iso (d1:=dom_165) (roots1:=roots_165) (T1:=gsh_165_16) [(dom_165,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_165_16) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x220000002200000000000000000000002200000022,0,1)] (by decide +kernel) (by decide +kernel) lowS_164)

namespace S_181
def pairsG : List (Nat × Nat) := [(1,17), (1,33), (1,129), (4,36), (4,132), (5,21), (5,37), (5,133), (16,17), (20,21), (20,52), (20,148), (32,33), (32,36), (32,160), (48,49), (48,52), (48,176), (128,129), (128,132), (128,160), (144,145), (144,148), (144,176)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_181.map (· &&& dom_181)
def goalM : Nat := goal_181 &&& dom_181
def NN : Nat → Nat
|4=>1
|5=>1
|6=>1
|_=>0
def HT : Nat → Nat → Nat
|4,0=>0xb3b19
|5,0=>0x374a9
|6,0=>0xd7033
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x3300330033003300000000000000000033003300000000c000c000c000c0000000000000000000c000c000c000c3300330000000000000000000000000033003300000000cc000000cc0000000000000000000000cc000000cc00022002200220022000000000000000000220022002200220c000c000c000c0000000000000000000c000c00000003300330033003300000000000000000000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x8ea1a3a84688
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>5
|5,0=>0x56
|6,0=>0xb5
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 7 then fld (dictB (i / 512) (i / 32 % 16)) 182 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 3 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 9 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))

def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
|0=>0x81
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>1
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 8 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 7), wireSAt ((code >>> 5) &&& 7)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 5 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmPalB : Nat → Nat
|0=>0x3f3c0
|_=>0
def pmB : Nat → Nat → Nat
|5,0=>1
|6,0=>2
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 2 (j % 128); fld (pmPalB (k / 32)) 6 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_177,5,runOps true dom_177 (0,roots_177) ops)] else [])++(if pm.testBit 1 then [(dom_149,4,runOps true dom_149 (0,roots_149) ops)] else [])++(if pm.testBit 2 then [(dzo_165_16,5,runOps true dzo_165_16 (0,roots_165) ops)] else [])++(if pm.testBit 3 then [(dom_165,5,runOps true dom_165 (0,roots_165) ops)] else [])++(if pm.testBit 4 then [(dom_164,4,runOps true dom_164 (0,roots_164) ops)] else [])++(if pm.testBit 5 then [(dom_53,4,runOps true dom_53 (0,roots_53) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_181 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_177 _ g hchk
    · exact cpcs (by decide +kernel) lowS_149 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_165_16_164 _ g hchk
    · exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · exact cpcs (by decide +kernel) lowS_164 _ g hchk
    · exact cpcs (by decide +kernel) lowS_53 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_177 5 s (0, roots_177) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_181 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_177 h

def symsG : List (List (Nat × Nat)) := [[(rowMask49, 96)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_181 == dom_181) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_181 goalM v ys) : RunD true dom_181 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_181 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, bar true dom_181 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_181 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_181 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_181 roots_181 goal_181 7 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_181

theorem lowS_181 : Lower true dom_181 roots_181 goal_181 7 := S_181.noCircuit

theorem lowS_229 : Lower true dom_229 roots_229 goal_229 7 := lower_iso (d1 := B5.dom_213) (roots1 := B5.roots_213) (T1 := B5.goal_213) [(rowMask25, 16), (rowMask34, 48)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_213

def isoMvS_213 : List (Nat × Nat) := [(rowMask51, 64), (rowMask26, 32), (rowMask22, 12), (rowMask33, 31)]

theorem lowS_213 : Lower true dom_213 roots_213 goal_213 7 :=
  lower_iso isoMvS_213 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_181

theorem lowS_241 : Lower true dom_241 roots_241 goal_241 7 := lower_iso (d1 := B5.dom_213) (roots1 := B5.roots_213) (T1 := B5.goal_213) [(rowMask44, 127), (rowMask29, 4), (rowMask36, 28), (rowMask22, 12)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_213

def isoMvS_244 : List (Nat × Nat) := [(rowMask26, 32), (rowMask290, 120), (rowMask22, 12), (rowMask11, 6), (rowMask0, 1)]

theorem lowS_244 : Lower true dom_244 roots_244 goal_244 7 :=
  lower_iso isoMvS_244 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_117

def dzo_164_16:=0x1100000011000000000000000000000011000000110000

def gzo_164_16:=0x1100000010000000000000000000000010000000000000

def gsh_164_16:=0x110000001000000000000000000000001000000000

theorem lowS_zo_164_16_164:Lower true dzo_164_16 roots_164 gzo_164_16 4:=lower_iso (d1:=dom_164) (roots1:=roots_164) (T1:=gsh_164_16) [(dom_164,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_164_16) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [] (by decide +kernel) (by decide +kernel) lowS_164)

def dzo_81_4:=0x3000300000000000300030

def gzo_81_4:=0x3000200000000000200000

def gsh_81_4:=0x300020000000000020000

theorem lowS_zo_81_4_81:Lower true dzo_81_4 roots_81 gzo_81_4 4:=lower_iso (d1:=dom_81) (roots1:=roots_81) (T1:=gsh_81_4) [(dom_81,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_81_4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [] (by decide +kernel) (by decide +kernel) lowS_81)

def dzo_241_4:=0x30003000300030003000300030003000300030003000300030003000300030

def gzo_241_4:=0x30003000300030003000300030003000300030003000200030003000200000

def gsh_241_4:=0x3000300030003000300030003000300030003000300020003000300020000

theorem lowS_zo_241_4_81:Lower true dzo_241_4 roots_241 gzo_241_4 6:=lower_iso (d1:=dom_241) (roots1:=roots_241) (T1:=gsh_241_4) [(dom_241,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_241_4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(rowMask279,0,32),(0x3000300030003000300030003000300000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_81)

def dzo_209_4:=0x300030000000000030003000000000003000300000000000300030

def gzo_209_4:=0x300030000000000030003000000000003000200000000000200000

def gsh_209_4:=0x30003000000000003000300000000000300020000000000020000

theorem lowS_zo_209_4_81:Lower true dzo_209_4 roots_209 gzo_209_4 5:=lower_iso (d1:=dom_209) (roots1:=roots_209) (T1:=gsh_209_4) [(dom_209,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_209_4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x30003000000000003000300000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_81)

def dzo_228_16:=0x11000000110000001100000011000000110000001100000011000000110000

def gzo_228_16:=0x11000000110000001100000010000000110000001100000010000000000000

def gsh_228_16:=0x1100000011000000110000001000000011000000110000001000000000

theorem lowS_zo_228_16_164:Lower true dzo_228_16 roots_228 gzo_228_16 5:=lower_iso (d1:=dom_228) (roots1:=roots_228) (T1:=gsh_228_16) [(dom_228,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_228_16) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x1100000011000000000000000000000011000000110000000000000000,0,64)] (by decide +kernel) (by decide +kernel) lowS_164)

def dzo_229_16:=0x33000000330000003300000033000000330000003300000033000000330000

def gzo_229_16:=0x33000000330000003300000032000000330000003300000032000000220000

def gsh_229_16:=0x3300000033000000330000003200000033000000330000003200000022

theorem lowS_zo_229_16_164:Lower true dzo_229_16 roots_229 gzo_229_16 6:=lower_iso (d1:=dom_229) (roots1:=roots_229) (T1:=gsh_229_16) [(dom_229,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_229_16) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x2200000022000000220000002200000022000000220000002200000022,0,1),(0x3300000033000000000000000000000033000000330000000000000000,0,64)] (by decide +kernel) (by decide +kernel) lowS_164)

namespace S_245
def pairsG : List (Nat × Nat) := [(1,17), (1,33), (1,65), (1,129), (4,36), (4,132), (5,21), (5,37), (5,69), (5,133), (16,17), (16,80), (20,21), (20,52), (20,84), (20,148), (32,33), (32,36), (32,160), (48,49), (48,52), (48,112), (48,176), (64,65), (64,80), (64,192), (68,69), (68,84), (68,100), (68,196), (96,97), (96,100), (96,112), (96,224), (128,129), (128,132), (128,160), (128,192), (144,145), (144,148), (144,176), (144,208)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3ffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_245.map (· &&& dom_245)
def goalM : Nat := goal_245 &&& dom_245
def NN : Nat → Nat
|4=>7
|5=>18
|6=>46
|7=>36
|8=>12
|9=>1
|_=>0
def HT : Nat → Nat → Nat
|4,0=>0xb3d77ad9d09d7a29bd6713ac1125410a788
|5,0=>0xcb6859adbc93442830ec7dc10695a55c9c95877054c104b0544868f474133b0722b17219b74051f4034b402135
|6,0=>0xe9711e3ee5dbd57cd392be338bc5f8b712ab3f60b3a2da0ac88494b7f503755fa6b1a965e746284d5e4ba5b4a94fb9f4d93c4c5864abe745d4f3e3d53d17232c7f3131b2f68f2f36b28ee225cd9226e9220371a8f215b0d1453813de5123fe121a00ed620e5e50ba240a6d9036130134800557
|7,0=>0xceb70c0d44ba48caba99aaa649b8338f39f8c5bd88ca8848c17d8777ab79782fd76dc2746bb711fa6cb716305262b126272061fe1541b45090b4e915491e140f542dd0b28cd1263dc2019e145ed0e12e0b31406a80054e803d2b
|8,0=>0xf33adc2522b0adead277abe66860ff6e7726a0e9520e93d5101cd580b6a6
|9,0=>0xc2522
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xcc008800cc008800cc008800cc008800cc008800cc008800cc008800cc008b300330033003300330033003300330033003300330033003300330022002200000000cc00cc0000000000cc00cc0000000000cc00cc00000000000000032003200320032003200320032003200320032003200320032003200320032cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc0000000000000003300330000000000330033000000000033000000000000002200000000cc000000cc0000008800000088000000cc000000cc000000880000008b300330033003300330033003300330033000000330000003300000033000000000000cc00cc0000000000cc00cc000000000088008800000000008800880000000000000003300330022002200000000000000000033003300220022c000c000c000c000c000c000c000c000c000c00000000000c000c0000000033003300330033003300330022002200330033003300330033003300220022cc000000cc0000008800000088000000cc000000cc000000880000008800033003300220022003300330022002200330033002200220033003300220022cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00000000000000003000300030003000300030003000300030003000300000003000300020000cc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc000000022002200220022002200220022002200220022002200220022002200220022cc00cc00cc00cc00cc00cc00cc00cc00cc000000cc000000880000008800003000300030003000300030003000300030003000000000003000300000000cc00cc00cc00cc00cc00cc00cc00cc00cc00cc0000000000cc00cc000000033003300330033002200220022002200330033003300330022002200220022cc00cc00cc00cc00cc00cc00000000008800880088008800880088000000030003000300030003000300030003000300030003000300030003000300030cc00cc00cc00cc00cc00cc00cc00cc0088008800880088008800880088008b3003300220022003300330022002200330033002200220000000000000000cc00cc00cc00cc000000000000000000cc00cc00cc00cc00000000000000033003300330033003300330000000000330033003300330033003300000000cc000000cc000000cc000000cc000000cc000000cc000000cc000000cc00033003300330033003200320032003200330033003300330032003200220022c800c800c800c800c800c800c800c800c800c80088008800c800c80088008b3003300330033003300330033003300000000000000000000000000000000
|0,1=>0x33003000330030003300300033003000330030003300300033003000330030cc00cc00cc000000cc00cc00cc000000cc00cc00cc000000cc00cc00cc00033003300330033003300330033003300300030003000300030003000300030cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc000000cc00cc00cc000100010001000100010001000100010001000100010001000100010001000100000000000000000c800c800c800c8000000000000000000c800c800c800c80000000000000000000000000000000330000003300000033000000330000cc00cc00cc00cc00cc000000cc000000cc00cc00cc00cc00cc000000cc00000000000000000000000000000000000110011001100110011001100000000000000000000000000000000cc00cc000000000000000000000000008800891001100110011001100110000000000110011001100110011001100000000cc00cc00cc00cc00cc00cc00cc00cc000000000000000000cc00cc0088008b300330033003300330033003300330033003300330033002200220022002200000000000000000000000000000000cc00cc00cc00cc00cc00cc00880089100110011001100110011001100110011001100110011000000000000000000000000000000000000000000000000cc00cc00cc00cc00cc00cc0000000330033003000300033003300300030003300330030003000330033003000300000000000000000cc00cc00cc00cc0000000000000000008800880088008b3003300330033003300330033003300000033000000330000002200000022cc00cc00cc00cc00cc00cc00cc00cc0044004400440044004400440000000330033003300330033003300330033003300330022002200330033002200220000000000000000cc00cc00cc00cc000000000000000000cc00cc008800880000000110011000000000011001100000000001100110000000000000000cc00cc00cc00cc000000000000000000cc00cc00cc00cc00cc00cc0088008b3003300000000003300330033003300330033000000000033003300220022
|_,_=>0
def stPool : Nat → Nat
|0=>0xc82873c838d6853ce31914010b0c82873c32071464982075c53c30811403ce4cc1403c304a14058b0c81c510f20e34010354a38048320914050f0c81d14840c81d110f20e3442c838d48320944f38d4053ce34c14b0c82891032071840c2040
|1=>0xc83a514090320e5c50042c320a3804840dc1408cf0c838500f0c838518010b0c81ce14f0c838588084f0c83850203c320e1403df0ce30501e3c320e1403c304e1403c328e30500f0c81ce15d3d87071562c320e14010320e1803c320a2406cf
|2=>0x20739714f0c83a74403c354a3850040d538502b3c320e1406cf60839116410320e1403c370744510f0c83aa0123c32074456cf0c828e0122c320714f0c83891406cf0c81ce152a4320e140a0f20e64500f0c81ce9d110f0c81ce44f20e98500f
|3=>0x3c37333850123f220e1403c370e44500b3f10c83850043d820e14048f0c83911403c320eb850122c320e1403c320ec0500f0c83af1402c32073971643d820738550f0c839101210320e4402c320eb8502d3c320e1402cf0c828714f0c11403d8
|4=>0x3c320e4406c43c320e1403c320e5c500b3c320738510f0ced0500b3df0c838500b3c320a38500f0c81ce5c500f0ce3050042c320e140d4f0c838500fc8ed0502448f0c83850163c320e1403c320e16a01b3c320e44500fc9c38500f0c81ce445
|5=>0x1ce1403c370838500f0ced0500f7c320e1403c320a3850123c320e140dcf0c838500f60838500fc4320e1403d820738590f0c838500f61c3850243c320738500f20e4c50043c320738500f7c3d8838501b3c320e1403c3cc83850123c3705004
|6=>0xf0c838500fe0320e1403c320e14010f0c838500f0c8
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>0x1e5065414503d40a50154005
|5,0=>0x22188261f187661c186a619185e61618526131846610183a60d182e60a18235
|6,0=>0x6fddb876c5daa768dd9c7655d8e761dd8255edd7475b5d676581d597549d4c6515d3e74ddd3164a9d237471d157439d0774058fa73cdcec73998df7361cd17329cc372f1cb572b9ca86285c9a725548e7
|7,0=>0xb01ab97acdaab8a95a9d8a5628e7a1de8169e9e7289ade647975e55893624588fda3878c5e2b688e21c7855e0d881da0077e5df277adde38771dd48735dc67
|8,0=>0xc41f0a6c0defc7bd5eef6ba1ee17b69ed37b35ac67
|9,0=>0x3176
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 57 then fld (dictB (i / 512) (i / 32 % 16)) 246 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 6 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 14 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))

def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 7 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
|0=>0x14f4a0f14e471738040650ca853910ecf1d1cfcf0120e4f3914f52441404f39480c71720b8f013c0453954e482c3c0482e3c04f46140483938043011070f152c54f014c0432814e4f0149105013ce411554e482c3c045394c04a0c14e4e15107053d1524f394c04a0c3c5453914e4505
|1=>0x20e4501380457220e4f390c0c50120e4f010c54f150c045013ce443b14f4f393c0473f00e430100e44393c5443b14f4f0154e482c3c043011cfc039b05d139140482c14e4f012c8053d3c054030c045010124f39380450120e4e461404b153c0403d3ce40391070f153804f451404403
|2=>0xc84f15380483920ec33914e4f390cf43010c54e010c0473d00e48390c0473d00e432814e4f1538048010ce452d3c05c1720e4f3920e45013c544013c5473f00e4f013804f1520ecf010ce4f0114e473f00e482e3c0453d3c0432d3c0430320ed2013ce52173ce513b140513d1404303
|_=>0
def opOffB : Nat → Nat → Nat
|4,0=>0x11000000000000000001
|5,0=>0x1c21a21730001611330000f40000e10000b30a1082062000024
|6,0=>0x6b26926720006520006416135e35b35835535415225024d34b20004924634334123f23d23b20003833713523413130002e30000002d12c12a22822532322121e3000
|7,0=>0xb32b12af2ad2ab2a92a72a52a32a129f29d29b29929729529329128f28d28b28928728528328127f27d27b27927727527327126f26d2
|8,0=>0xbf1000be1bd1bc1bb1ba1b91b81b71b61b51
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 14 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 63), wireSAt ((code >>> 8) &&& 63)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 12 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmPalB : Nat → Nat
|0=>0x3440001900000c2000060000022c8000b540005a200028000010a80008500004020002000000bb80005d80002ea00017400004800002200001080000810000388000110000084000020000008000002000000a0000040000018000008000002000000
|1=>0x3c0fa81b0ddc0c8fea0481fd01e9fa80e07d404000a01d17500e30a8064fd403248a0189f500c42280605d402a6fa00f3790079ba8039dd401cc2a00e1fd0070ba80310540186ea0085770042ba80145d40086fa00261100130280098040011820006dd
|2=>0x41b05d507a2ea6281772000bb88804482c02ee1210210900898313dd4189ee80c47740620ba82307f4101ca0080e14
|_=>0
def pmB : Nat → Nat → Nat
|4,0=>0x80000000002
|5,0=>0xc021c0060a004800400382021000b
|6,0=>0x2c7469808003122e841901c74f351e000aa4054a881451c9c44198000a5000e3804f930255d80
|7,0=>0x74b9da4966a44670be2c052dd447365d3447c4d1ac69058b37095b4a7a6612d
|8,0=>0x9a461b2709e4bc5739fcc
|9,0=>0x11
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 7 (j % 128); fld (pmPalB (k / 32)) 25 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_244,7,runOps true dom_244 (0,roots_244) ops)] else [])++(if pm.testBit 1 then [(dom_193,4,runOps true dom_193 (0,roots_193) ops)] else [])++(if pm.testBit 2 then [(dom_117,7,runOps true dom_117 (0,roots_117) ops)] else [])++(if pm.testBit 3 then [(dom_164,4,runOps true dom_164 (0,roots_164) ops)] else [])++(if pm.testBit 4 then [(dom_213,7,runOps true dom_213 (0,roots_213) ops)] else [])++(if pm.testBit 5 then [(dom_241,7,runOps true dom_241 (0,roots_241) ops)] else [])++(if pm.testBit 6 then [(dom_181,7,runOps true dom_181 (0,roots_181) ops)] else [])++(if pm.testBit 7 then [(dzo_164_16,4,runOps true dzo_164_16 (0,roots_164) ops)] else [])++(if pm.testBit 8 then [(dom_229,7,runOps true dom_229 (0,roots_229) ops)] else [])++(if pm.testBit 9 then [(dzo_81_4,4,runOps true dzo_81_4 (0,roots_81) ops)] else [])++(if pm.testBit 10 then [(dom_81,4,runOps true dom_81 (0,roots_81) ops)] else [])++(if pm.testBit 11 then [(dom_53,4,runOps true dom_53 (0,roots_53) ops)] else [])++(if pm.testBit 12 then [(dzo_241_4,6,runOps true dzo_241_4 (0,roots_241) ops)] else [])++(if pm.testBit 13 then [(dom_212,4,runOps true dom_212 (0,roots_212) ops)] else [])++(if pm.testBit 14 then [(dzo_209_4,5,runOps true dzo_209_4 (0,roots_209) ops)] else [])++(if pm.testBit 15 then [(dzo_228_16,5,runOps true dzo_228_16 (0,roots_228) ops)] else [])++(if pm.testBit 16 then [(dzo_113_4,5,runOps true dzo_113_4 (0,roots_113) ops)] else [])++(if pm.testBit 17 then [(dzo_229_16,6,runOps true dzo_229_16 (0,roots_229) ops)] else [])++(if pm.testBit 18 then [(dzo_165_16,5,runOps true dzo_165_16 (0,roots_165) ops)] else [])++(if pm.testBit 19 then [(dom_149,4,runOps true dom_149 (0,roots_149) ops)] else [])++(if pm.testBit 20 then [(dom_228,5,runOps true dom_228 (0,roots_228) ops)] else [])++(if pm.testBit 21 then [(dom_165,5,runOps true dom_165 (0,roots_165) ops)] else [])++(if pm.testBit 22 then [(dom_161,4,runOps true dom_161 (0,roots_161) ops)] else [])++(if pm.testBit 23 then [(dom_225,5,runOps true dom_225 (0,roots_225) ops)] else [])++(if pm.testBit 24 then [(dom_197,5,runOps true dom_197 (0,roots_197) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_245 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · exact cpcs (by decide +kernel) lowS_193 _ g hchk
    · exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · exact cpcs (by decide +kernel) lowS_164 _ g hchk
    · exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_164_16_164 _ g hchk
    · exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_81_4_81 _ g hchk
    · exact cpcs (by decide +kernel) lowS_81 _ g hchk
    · exact cpcs (by decide +kernel) lowS_53 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_241_4_81 _ g hchk
    · exact cpcs (by decide +kernel) lowS_212 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_209_4_81 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_228_16_164 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_113_4_81 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_229_16_164 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_165_16_164 _ g hchk
    · exact cpcs (by decide +kernel) lowS_149 _ g hchk
    · exact cpcs (by decide +kernel) lowS_228 _ g hchk
    · exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · exact cpcs (by decide +kernel) lowS_161 _ g hchk
    · exact cpcs (by decide +kernel) lowS_225 _ g hchk
    · exact cpcs (by decide +kernel) lowS_197 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_244 7 s (0, roots_244) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_245 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_244 h

def symsG : List (List (Nat × Nat)) := [[(rowMask26, 32), (rowMask22, 12), (rowMask44, 127)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_245 == dom_245) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_245 goalM v ys) : RunD true dom_245 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_245 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 7 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 7 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 18 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 18 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 46 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 46 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 36 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 36 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8 : ∀ i, 0 ≤ i → i < 12 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 9) : ∀ i < NN s, bar true dom_245 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
  · exact z8 i (Nat.zero_le i) hi
  · exact z9 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_245 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD true dom_245 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_245 roots_245 goal_245 10 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_245

theorem lowS_245 : Lower true dom_245 roots_245 goal_245 10 := S_245.noCircuit

end B6

namespace B1
def dom_243 : Nat := rowMask176

def goal_243 : Nat := 0xffffffffffffffffffffffffeeeeeeeeffffeeeeffffeeeeeeeeccccaaaa0000

def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := rowMask275

def goal_251 : Nat := 0xffffffffffffffffffffffffffeeffeeffffeeeeffffeeeeeeeeccccaaaa0000

def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

theorem lowS_243 : Lower true dom_243 roots_243 goal_243 10 := lower_iso (d1 := B6.dom_245) (roots1 := B6.roots_245) (T1 := B6.goal_245) [(rowMask33, 31), (rowMask144, 62), (rowMask16, 2), (rowMask22, 12), (rowMask35, 15), (rowMask44, 127)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B6.lowS_245

theorem lowS_251 : Lower true dom_251 roots_251 goal_251 11 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00, 128, 136)] (by decide +kernel) (by decide +kernel) lowS_243

end B1

namespace B2
def dom_51 : Nat := 0xf000f000f000f

def goal_51 : Nat := rowMask267

def roots_51 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_87 : Nat := 0xff00ff0000000000ff00ff

def goal_87 : Nat := 0xfffffefefffffefeaaaa0000aaaa0000fffffefefffffefeaaaa0000aaaa0000

def roots_87 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_102 : Nat := 0x55000000550000005500000055

def goal_102 : Nat := rowMask268

def roots_102 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_103 : Nat := 0xff000000ff000000ff000000ff

def goal_103 : Nat := 0xfefefefefefefefeeeeeeeee00000000fefefefefefefefeeeeeeeee00000000

def roots_103 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_113 : Nat := 0x30003000300030003000300030003

def goal_113 : Nat := rowMask265

def roots_113 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_114 : Nat := 0x50005000500050005000500050005

def goal_114 : Nat := 0xffffccccffffcccccccccccc00000000ffffccccffffcccccccccccc00000000

def roots_114 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f

def goal_115 : Nat := 0xffffeeeeffffeeeeeeeeeeeeaaaa0000ffffeeeeffffeeeeeeeeeeeeaaaa0000

def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033

def goal_117 : Nat := 0xfffffafafffffafaaaaaaaaaaaaa0000fffffafafffffafaaaaaaaaaaaaa0000

def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055

def goal_118 : Nat := 0xfffffcfcfffffcfccccccccc00000000fffffcfcfffffcfccccccccc00000000

def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff

def goal_119 : Nat := 0xfffffefefffffefeeeeeeeeeaaaa0000fffffefefffffefeeeeeeeeeaaaa0000

def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_162 : Nat := 0x50000000500000000000000000000000500000005

def goal_162 : Nat := rowMask264

def roots_162 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_166 : Nat := 0x550000005500000000000000000000005500000055

def goal_166 : Nat := 0xfffffffffcfcfcfcfffffffffcfcfcfccccccccc00000000cccccccc00000000

def roots_166 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_167 : Nat := 0xff000000ff0000000000000000000000ff000000ff

def goal_167 : Nat := 0xfffffffffcfcfcfcfffffffffcfcfcfceeeeeeee00000000eeeeeeee00000000

def roots_167 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_179 : Nat := rowMask274

def goal_179 : Nat := 0xffffffffeeeeccccffffffffeeeecccceeeeeeeeaaaa0000eeeeeeeeaaaa0000

def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := rowMask259

def goal_183 : Nat := 0xfffffffffefefcfcfffffffffefefcfceeeeeeeeaaaa0000eeeeeeeeaaaa0000

def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_198 : Nat := rowMask311

def goal_198 : Nat := 0xfffffffffffffffffcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc0000000000000000

def roots_198 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := rowMask205

def goal_211 : Nat := 0xffffffffffffffffeeeecccceeeeccccffffeeeeffffeeeeaaaa0000aaaa0000

def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_212 : Nat := rowMask241

def goal_212 : Nat := 0xfffffffffffffffff0f0f0f0f0f0f0f0fffff0f0fffff0f00000000000000000

def roots_212 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := rowMask149

def goal_213 : Nat := 0xfffffffffffffffffafaf0f0fafaf0f0fffffafafffffafaaaaa0000aaaa0000

def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := rowMask242

def goal_214 : Nat := 0xfffffffffffffffffcfcfcfcfcfcfcfcfffffcfcfffffcfc0000000000000000

def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := rowMask187

def goal_215 : Nat := 0xfffffffffffffffffefefcfcfefefcfcfffffefefffffefeaaaa0000aaaa0000

def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_226 : Nat := 0x500000005000000050000000500000005000000050000000500000005

def goal_226 : Nat := 0xffffffffffffffffffffffffcccccccccccccccccccccccccccccccc00000000

def roots_226 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_228 : Nat := rowMask285

def goal_228 : Nat := 0xfffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f00000000000000000

def roots_228 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := rowMask230

def goal_230 : Nat := 0xfffffffffffffffffffffffffcfcfcfcfcfcfcfcfcfcfcfccccccccc00000000

def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := rowMask231

def goal_231 : Nat := 0xfffffffffffffffffffffffffcfcfcfcfefefefefefefefeeeeeeeee00000000

def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_240 : Nat := 0x1000100010001000100010001000100010001000100010001000100010001

def goal_240 : Nat := 0xffffffffffffffffffffffff00000000ffff0000ffff00000000000000000000

def roots_240 : List Nat := [xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := rowMask280

def goal_242 : Nat := 0xffffffffffffffffffffffffccccccccffffccccffffcccccccccccc00000000

def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := rowMask176

def goal_243 : Nat := 0xffffffffffffffffffffffffeeeeccccffffeeeeffffeeeeeeeeeeeeaaaa0000

def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_244 : Nat := rowMask218

def goal_244 : Nat := 0xfffffffffffffffffffffffff0f0f0f0fffff0f0fffff0f00000000000000000

def roots_244 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := rowMask87

def goal_245 : Nat := 0xfffffffffffffffffffffffffafaf0f0fffffafafffffafaaaaaaaaaaaaa0000

def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := rowMask217

def goal_246 : Nat := 0xfffffffffffffffffffffffffcfcfcfcfffffcfcfffffcfccccccccc00000000

def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := rowMask155

def goal_247 : Nat := 0xfffffffffffffffffffffffffefefcfcfffffefefffffefeeeeeeeeeaaaa0000

def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

theorem lowS_162 : Lower true dom_162 roots_162 goal_162 4 := lower_iso (d1 := B5.dom_145) (roots1 := B5.roots_145) (T1 := B5.goal_145) [(rowMask0, 1), (rowMask25, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_145

theorem lowS_51 : Lower true dom_51 roots_51 goal_51 4 := lower_iso (d1 := B5.dom_85) (roots1 := B5.roots_85) (T1 := B5.goal_85) [(rowMask16, 2), (rowMask26, 32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_85

theorem lowS_198 : Lower true dom_198 roots_198 goal_198 5 := lower_iso (d1 := B5.dom_197) (roots1 := B5.roots_197) (T1 := B5.goal_197) [(rowMask0, 1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_197

theorem lowS_102 : Lower true dom_102 roots_102 goal_102 4 := lower_iso (d1 := B5.dom_85) (roots1 := B5.roots_85) (T1 := B5.goal_85) [(rowMask0, 1), (rowMask25, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_85

theorem lowS_113 : Lower true dom_113 roots_113 goal_113 5 := lower_iso (d1 := B5.dom_147) (roots1 := B5.roots_147) (T1 := B5.goal_147) [(rowMask44, 127), (rowMask16, 2), (rowMask11, 6), (rowMask28, 30), (rowMask35, 15), (rowMask34, 48)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_147

theorem lowS_114 : Lower true dom_114 roots_114 goal_114 4 := lower_iso (d1 := B5.dom_85) (roots1 := B5.roots_85) (T1 := B5.goal_85) [(rowMask0, 1), (rowMask29, 4), (rowMask36, 28), (rowMask22, 12)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_85

theorem lowS_166 : Lower true dom_166 roots_166 goal_166 5 := lower_iso (d1 := B5.dom_147) (roots1 := B5.roots_147) (T1 := B5.goal_147) [(rowMask10, 3), (rowMask0, 1), (rowMask25, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_147

theorem lowS_212 : Lower true dom_212 roots_212 goal_212 5 := lower_iso (d1 := B5.dom_147) (roots1 := B5.roots_147) (T1 := B5.goal_147) [(rowMask10, 3), (rowMask11, 6), (rowMask28, 30), (rowMask37, 14), (rowMask34, 48), (rowMask183, 112)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_147

theorem lowS_226 : Lower true dom_226 roots_226 goal_226 5 := lower_iso (d1 := B5.dom_197) (roots1 := B5.roots_197) (T1 := B5.goal_197) [(rowMask0, 1), (rowMask32, 63), (rowMask29, 4), (rowMask22, 12), (rowMask36, 28), (rowMask10, 3)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_197

theorem lowS_228 : Lower true dom_228 roots_228 goal_228 5 := lower_iso (d1 := B5.dom_147) (roots1 := B5.roots_147) (T1 := B5.goal_147) [(rowMask10, 3), (rowMask11, 6), (rowMask28, 30), (rowMask34, 48)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_147

theorem lowS_240 : Lower true dom_240 roots_240 goal_240 4 := lower_iso (d1 := B5.dom_85) (roots1 := B5.roots_85) (T1 := B5.goal_85) [(rowMask0, 1), (rowMask27, 7), (rowMask36, 28), (rowMask44, 127), (rowMask22, 12)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_85

theorem lowS_87 : Lower true dom_87 roots_87 goal_87 6 := lower_iso (d1 := B5.dom_151) (roots1 := B5.roots_151) (T1 := B5.goal_151) [(rowMask51, 64)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_151

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

theorem lowS_117 : Lower true dom_117 roots_117 goal_117 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x300030003000300030003000300030, 64, 68)] (by decide +kernel) (by decide +kernel) lowS_113

theorem lowS_118 : Lower true dom_118 roots_118 goal_118 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x500050005000500050005000500050, 64, 68)] (by decide +kernel) (by decide +kernel) lowS_114

theorem lowS_179 : Lower true dom_179 roots_179 goal_179 7 := lower_iso (d1 := B6.dom_117) (roots1 := B6.roots_117) (T1 := B6.goal_117) [(rowMask33, 31), (rowMask37, 14), (rowMask16, 2), (rowMask51, 64)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B6.lowS_117

theorem lowS_211 : Lower true dom_211 roots_211 goal_211 8 := lower_iso (d1 := B5.dom_179) (roots1 := B5.roots_179) (T1 := B5.goal_179) [(rowMask26, 32), (rowMask49, 96)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_179

theorem lowS_230 : Lower true dom_230 roots_230 goal_230 7 := lower_iso (d1 := B5.dom_213) (roots1 := B5.roots_213) (T1 := B5.goal_213) [(rowMask0, 1), (rowMask25, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_213

def dzo_226_16:=0x5000000050000000500000005000000050000000500000005000000050000

def gzo_226_16:=0x5000000050000000500000004000000050000000500000004000000000000

def gsh_226_16:=0x500000005000000050000000400000005000000050000000400000000

theorem lowS_zo_226_16_162:Lower true dzo_226_16 roots_226 gzo_226_16 5:=lower_iso (d1:=dom_226) (roots1:=roots_226) (T1:=gsh_226_16) [(dom_226,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_226_16) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x500000005000000000000000000000005000000050000000000000000,0,64)] (by decide +kernel) (by decide +kernel) lowS_162)

theorem lowS_242 : Lower true dom_242 roots_242 goal_242 7 := lower_iso (d1 := B6.dom_181) (roots1 := B6.roots_181) (T1 := B6.goal_181) [(rowMask0, 1), (rowMask33, 31), (rowMask29, 4), (rowMask316, 60), (rowMask10, 3)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B6.lowS_181

def isoMvS_167 : List (Nat × Nat) := [(rowMask51, 64), (rowMask39, 8), (rowMask37, 14), (rowMask33, 31)]

theorem lowS_167 : Lower true dom_167 roots_167 goal_167 6 :=
  lower_iso isoMvS_167 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_117

theorem lowS_213 : Lower true dom_213 roots_213 goal_213 8 := lower_iso (d1 := B5.dom_179) (roots1 := B5.roots_179) (T1 := B5.goal_179) [(rowMask16, 2), (rowMask26, 32), (rowMask49, 96)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_179

theorem lowS_214 : Lower true dom_214 roots_214 goal_214 6 := lower_iso (d1 := B5.dom_199) (roots1 := B5.roots_199) (T1 := B5.goal_199) [(rowMask27, 7), (rowMask0, 1), (rowMask37, 14), (rowMask51, 64)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_199

def isoMvS_244 : List (Nat × Nat) := [(rowMask51, 64), (rowMask25, 16), (rowMask290, 120), (rowMask22, 12), (rowMask11, 6), (rowMask0, 1)]

theorem lowS_244 : Lower true dom_244 roots_244 goal_244 6 :=
  lower_iso isoMvS_244 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_117

def dzo_51_4:=0xf000f000f000f0

def gzo_51_4:=0xe000e000a00000

def gsh_51_4:=0xe000e000a0000

theorem lowS_zo_51_4_51:Lower true dzo_51_4 roots_51 gzo_51_4 4:=lower_iso (d1:=dom_51) (roots1:=roots_51) (T1:=gsh_51_4) [(dom_51,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_51_4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [] (by decide +kernel) (by decide +kernel) lowS_51)

def dzo_115_4:=0xf000f000f000f000f000f000f000f0

def gzo_115_4:=0xf000f000f000f000e000e000a00000

def gsh_115_4:=0xf000f000f000f000e000e000a0000

theorem lowS_zo_115_4_51:Lower true dzo_115_4 roots_115 gzo_115_4 5:=lower_iso (d1:=dom_115) (roots1:=roots_115) (T1:=gsh_115_4) [(dom_115,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_115_4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xf000f000f000f0000000000000000,0,64)] (by decide +kernel) (by decide +kernel) lowS_51)

namespace S_119
def pairsG : List (Nat × Nat) := [(1,17), (1,33), (1,65), (2,34), (2,66), (3,19), (3,35), (3,67), (4,68), (5,21), (5,37), (5,69), (6,38), (6,70), (7,23), (7,39), (7,71), (16,17), (16,80), (18,19), (18,50), (18,82), (20,21), (20,84), (22,23), (22,54), (22,86), (32,33), (32,34), (36,37), (36,38), (36,100), (48,49), (48,50), (48,112), (52,53), (52,54), (52,116), (64,65), (64,66), (64,68), (64,80), (96,97), (96,98), (96,100), (96,112)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3fffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_119.map (· &&& dom_119)
def goalM : Nat := goal_119 &&& dom_119
def NN : Nat → Nat
|3=>1
|4=>4
|5=>10
|6=>7
|7=>1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0x481ca
|4,0=>0xe0fe3c8757b1bb134cf7
|5,0=>0xe39b4d664abb7d7b52849f6f28272c4b9de4075d3e23e07050
|6,0=>0xf8931f7bfee8e24a8c394c84f2024719cf7
|7,0=>0x2c4d1
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xff00f000ff00f000ff00f000ff00f0fa00fa00fa00fa00fa00fa00fa00faff00ff00ff00ff00ff000000ff0000ff000f00ff000f00ff000000ff00000f000f000f000f0000000000000000fe00fe00fe00fe00fe00fe00fe00fe33003300330033003300330000000000000000ee00ee0000000000ee00ee0000ff000000ff000000aa000000aaaf00af00af00af00aa00aa00aa00aaff00ff0000000000ff00ff00000000cc00cc00cc00cc00cc00cc00cc00ccaa00aa00aa00aa00aa00aa00aa00aa0000af000000af000000aa000000aaff00ff00ff00ff0000000000000000ff00ff00ff00ff00ff00ff00000000ee00ee00ee00ee00ee00ee00ee00eeff000000ff000000ff000000ff0000f000f000f000f000f000f000f000f0ee00ee00ee00ee00ee00ee00000000ff00ff00ff00ff00aa00aa00aa00aa
|_,_=>0
def stPool : Nat → Nat
|0=>0x28c49419541a50650c444194312408328734a0ca90c49419434a0d05446941943220d050de4418a31110628c49020a3121c650d2b41862221a650c44019424a18650c8b30c414194941cc51888018820
|1=>0x14312506
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>4
|4,0=>0x1350e5095045
|5,0=>0x4e64864263c63663062a62461e6186
|6,0=>0x7a67466e66776165a7546
|7,0=>0x806
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 21 then fld (dictB (i / 512) (i / 32 % 16)) 120 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 5 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 12 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))

def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 5 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
|0=>0x5191894a141912119911a1114a1
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0x200000000000000
|6,0=>0x81716151413121
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 12 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 31), wireSAt ((code >>> 7) &&& 31)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 8 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmPalB : Nat → Nat
|0=>0xce6fdda89f52a63d46106603001001000
|_=>0
def pmB : Nat → Nat → Nat
|5,0=>0x30100020
|6,0=>0x7a64b59
|7,0=>8
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 4 (j % 128); fld (pmPalB (k / 32)) 11 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_117,6,runOps true dom_117 (0,roots_117) ops)] else [])++(if pm.testBit 1 then [(dzo_51_4,4,runOps true dzo_51_4 (0,roots_51) ops)] else [])++(if pm.testBit 2 then [(dom_102,4,runOps true dom_102 (0,roots_102) ops)] else [])++(if pm.testBit 3 then [(dom_113,5,runOps true dom_113 (0,roots_113) ops)] else [])++(if pm.testBit 4 then [(dom_87,6,runOps true dom_87 (0,roots_87) ops)] else [])++(if pm.testBit 5 then [(dom_118,5,runOps true dom_118 (0,roots_118) ops)] else [])++(if pm.testBit 6 then [(dom_115,6,runOps true dom_115 (0,roots_115) ops)] else [])++(if pm.testBit 7 then [(dom_103,5,runOps true dom_103 (0,roots_103) ops)] else [])++(if pm.testBit 8 then [(dom_51,4,runOps true dom_51 (0,roots_51) ops)] else [])++(if pm.testBit 9 then [(dzo_115_4,5,runOps true dzo_115_4 (0,roots_115) ops)] else [])++(if pm.testBit 10 then [(dom_114,4,runOps true dom_114 (0,roots_114) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_119 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_51_4_51 _ g hchk
    · exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · exact cpcs (by decide +kernel) lowS_113 _ g hchk
    · exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_115_4_51 _ g hchk
    · exact cpcs (by decide +kernel) lowS_114 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_117 6 s (0, roots_117) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_119 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_117 h

def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {v ys} (h : RunD true dom_119 goalM v ys) : RunD true dom_119 goalM v (ori ys) := h
def Z (s : Nat) := barP true dom_119 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
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
private theorem z6 : ∀ i, 0 ≤ i → i < 7 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 7 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 7) : ∀ i < NN s, bar true dom_119 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_119 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD true dom_119 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_119 roots_119 goal_119 8 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_119

theorem lowS_119 : Lower true dom_119 roots_119 goal_119 8 := S_119.noCircuit

theorem lowS_183 : Lower true dom_183 roots_183 goal_183 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(rowMask227, 128, 132)] (by decide +kernel) (by decide +kernel) lowS_179

theorem lowS_215 : Lower true dom_215 roots_215 goal_215 9 := lower_iso (d1 := B5.dom_231) (roots1 := B5.roots_231) (T1 := B5.goal_231) [(rowMask0, 1), (rowMask25, 16), (rowMask51, 64)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_231

theorem lowS_231 : Lower true dom_231 roots_231 goal_231 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(rowMask232, 32, 33)] (by decide +kernel) (by decide +kernel) lowS_230

theorem lowS_243 : Lower true dom_243 roots_243 goal_243 9 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf000f00000000000f000f00000000000f000f00000000000f000f00000000, 1, 33)] (by decide +kernel) (by decide +kernel) lowS_211

theorem lowS_245 : Lower true dom_245 roots_245 goal_245 9 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(rowMask277, 1, 33)] (by decide +kernel) (by decide +kernel) lowS_213

def dzo_166_16:=0x5500000055000000000000000000000055000000550000

def gzo_166_16:=0x5500000054000000000000000000000044000000000000

def gsh_166_16:=0x550000005400000000000000000000004400000000

theorem lowS_zo_166_16_166:Lower true dzo_166_16 roots_166 gzo_166_16 5:=lower_iso (d1:=dom_166) (roots1:=roots_166) (T1:=gsh_166_16) [(dom_166,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_166_16) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [] (by decide +kernel) (by decide +kernel) lowS_166)

def dzo_230_16:=rowMask278

def gzo_230_16:=0x55000000550000005500000054000000550000005500000044000000000000

def gsh_230_16:=0x5500000055000000550000005400000055000000550000004400000000

theorem lowS_zo_230_16_166:Lower true dzo_230_16 roots_230 gzo_230_16 6:=lower_iso (d1:=dom_230) (roots1:=roots_230) (T1:=gsh_230_16) [(dom_230,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_230_16) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x5500000055000000000000000000000055000000550000000000000000,0,64)] (by decide +kernel) (by decide +kernel) lowS_166)

namespace S_246
def pairsG : List (Nat × Nat) := [(2,34), (2,66), (2,130), (4,68), (4,132), (6,38), (6,70), (6,134), (16,80), (18,50), (18,82), (18,146), (20,84), (20,148), (22,54), (22,86), (22,150), (32,34), (32,160), (36,38), (36,100), (36,164), (48,50), (48,112), (48,176), (52,54), (52,116), (52,180), (64,66), (64,68), (64,80), (64,192), (96,98), (96,100), (96,112), (96,224), (128,130), (128,132), (128,160), (128,192), (144,146), (144,148), (144,176), (144,208)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_246.map (· &&& dom_246)
def goalM : Nat := goal_246 &&& dom_246
def NN : Nat → Nat
|3=>1
|4=>30
|5=>85
|6=>62
|7=>14
|8=>1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0xc5c9
|4,0=>0xfada5eb905db95ad80f2d0dd6d0135b3cd0afc02ad6839a8c391a9f914bf8ecd985cd8834b580d4c7f9307cc9d76f36745a342e7242ad53d6f83ca5739ee42cb7c1f2be1a08d198ba0d7ce
|5,0=>0xfddeafbf0dfaf3bf3d30f233ae9d3ae65e4e5bb6e4196e3c53e2749db9e5d9724d6b58d34fbc6285c56efbdd38bd097bb3edba476b51ffb3546aa233a7483a657da29959e7f29d9659cf0b9ccc49c8ff9c38a9bc5e985128cf96882d884df1834f4831c3824e4805907ef9378fa278cda72abe7261360e305fa215a08059713527e94f0ff4be544877547ab1462c743f3543c8f420103e02e3d4323a72533f5b2f46d27c1d2558b23a131c63619c6418fc317f76127c212203113330f1ac0e99b0d7e80cd990ae55092750922108580073210549d
|6,0=>0xf6faeef100ee45feb3b5e7c72e658ae578de4aece1b53e06c4ddd2cddcb5dc9b5d88c2d73b1cd17bc7ca0c16cbb64c0b3527aad76a9ea6a3437a31509561694a8088bec86c4d84f537f967795c4722976c06e6afbc6a5b06a31b678a36353861d3d6109c5be8453f604c0b948a8841a9f40954402e13f0f03bb193462d2f20327dc021b7a1fc3f1c0671b2df1ac2817b0616e4211b150f63c03079
|7,0=>0xff1f8ec056de9cdd7288ce003c8941c09338a1b57d6d4792373e2283c7ba25a4d1b8c9
|8,0=>0x8ae56
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xaa00aa00aa00aa008800880088008954015401540154015401540110011001540154000000000154015400000002a802a802a802a8000000000000000002a802a002a802a0000000000000000000000000000000000000000000000004400550044005500440044004400440000aa00aa00aa0000000000aa00aa000000aa008800aa000000000088008950015001500150015001500150015001500150015001500000000000000002280228022802280228022802280228022002280220022802200220022002255005500550055005500550055005500550055005500550055005500000000000000000000000000000000aa00aa00aa00aa00aa00aa00aa00aa0000000044004400440044004400440044004400440040004400400044004000440042a802a802a802a802a802a802a802a8000002a8000002a8000000000000000550055005500550055005500550055004400440044004400440044004400440a000a000a000a000a000a000a000a0008000a0008000a000800080008000954015401540154015401540154015401100154011001540110011001100112a802a802a802a8022002200220022002a802a802a802a802200220022002255005500550055005500550000000000550055005500550055005500000000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa008800880088008804000400040004000400040004000400000004000000040000000000000002a802a802a802a802a802a802a802a8000000000000000000000000000000055005500550055005400540054005400500050005000500050005000500050aa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa0000000000000000000000000000000000000001540150015401500154015001540152200220022002200220022002200220022002200220022002200220022002201000100010001000100010001000100000000000000000000000000000000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa0000000000aa00aa0000000140014001400140014001400140014001400140014001400140014001400142a802a802a802a802a802a802200220022002200220022002200220022002255005500550055000000000000000000550055005500550000000000000000aa000000aa000000aa000000aa000000aa000000aa000000aa000000aa000150015001500150015001500150015001500150015001500150015001500152a802a802a802a802a802a800000000022002200220022002200220000000055005500550055005500550055005500550055005500550000000000000000
|0,1=>0xa000a000a000a00000000000a000a000a000a000a000a00000000000000001400140014001400140014001400140014001400140014000000000000000000000002a802a80000000002a802a80000000002a002a00000000002a002a11001100110011001100110011001100110011001100110000000000000000aa000200aa000200aa000200aa000200aa000000aa000000aa000000aa000110011001100110011001100110011001100110011001100110011000000000000000000000000000000002a802a8000000000000000000000000000000055005500550055005500550055005500550044005500440055004400550044000000000000000000000000880088008800880088008800880088008800895401540154015401540154015401540154000001540000015400000154000088008800880088008800880088008800000000000000000000000000000000000000000000000000000000000000055005500550055005500550000000000000000aa00aa0000000000aa00aa00000000000000000000000000000000040004000400040004000400040004000400040004000400000000000000000002a8000002a80000000000000000000002a8000002a8000000000000000440055004400550044004400440044004400550044005500440044004400442200aa002200aa0022002200220022000000aa000000aa00000000000000004400440044004400440044004400440000004400000044000000000000000000000002a802a80000000002a802a8000000000220022000000000022002255005500550055005500550000000000550055005500550000000000000000a800aa00a800aa00a800a800a800a800a800aa00a800aa00a800a800a800a954015401540154015401540000000000000000000000000000000000000002280228022802280228022802280228022802280228022802200220022002244004400440044005500550055005500440044004400440044004400440044aa00aa00aa00aa00aa00aa00aa00aa00aa00a800aa00a800aa00a800aa00a954015401540154011001100110011000000000000000000000000000000002a802a002a802a002a802a002a802a002a802a002a802a002a802a002a802a000000000000000000000000550055000000000000000000000000004400440000aa00aa00aa0000000000aa00aa000000aa000000aa000000000000000000001400140014000000000014001400000014000000140000000000000002a802a802a802a802a802a802800280028002800280028002800280028002801000500010005000100010001000100000005000000050000000000000000
|0,2=>0xaa00aa00000000000000000000000000aa00aa0000000154011001540110015401100154011001540110015401100154011001540112a802a80000000002a802a802a802a802a802a80000000002a802a8000000000000000000000001100110011001100000000000000000000000000000000aa00aa00aa00aa00aa00aa00aa00aa00a800a800a800a800a800a800a800a800000001540154000000000154015400000000015401540000000000000002a8008802a8008802a8008802a8008802a8000002a8000002a8000002a8000550055005500550055005500440044005500550055005500550055004400442200220022002200220022002200220022000000220000002200000022000154000001540154015400000154015401540000015400000154000001540002a802a802a802a802a002a002a002a002a802a802a802a802a002a002a002a5500550055005500000000005500550055005500550055000000000044004402000200020002000200020002000200020000000200000002000000020000000000000000000154015401540154000000000000000000000000000000000000000000000002a802a802a802a8000000000000000002200220022002245004500450045004500450045004500440044004400440044004400440044aa000000aa00aa00aa000000aa00aa00aa000000aa008800aa000000aa008954015401540154004400440044004401540154015401540000000000000000880088008800880088008800880088008800880088008800880088000000000000000000000005500550055005500000000000000000055005500000000000000008800880000000000aa00aa00000000008800880000000000880089540154015401540000000001540154015401540154015400000000000000008800880088008800880088000000000088008800880088008800880000000050005000500050005000500050005000000050000000500000000000000000a000a000a000a000a000a000a000a000a000a000a000a000a000a000000001400140014001400040004000400040014001400140014000000000000000000000002a802a80000000002a802a80000000002a802a800000000022002205000500050005000500050005000500050005000500050004000400040004
|_,_=>0
def stPool : Nat → Nat
|0=>0x68448016242201a401823e34f030c5020b0424e8d1608e041a1849b08345832810d0b322420d300c305085c18612105822c106830c4408d1608a042a2c5022810803045000b124c20d160c30500401860a005822410690060878d162420e1a2c18c120058a121040706182840608080
|1=>0x1a2d582121068b06184805440186120150b06a44841a2c18250106900618a09004018222345a7042420d200c11408345821210a8d160c309009858a042420d161890908345830c1420d200c3050834186129020d16184844634583226868b121110d0618481000c10108345834224010
|2=>0x1211c8b0c704841a6018612115380c256841a401866e1068b6c08a041a401861201ab40618484662c1823e1068b06088801a2c3141210a9e06184841a2c18908c868b0618a044c184ad08c468b4a08a041a2c330281068b0c2422f1a2c30908b868304516841a2c189086869006184ac
|3=>0x1a40186131869006188c51a41a030c2400b06261841a2c4848834803130c20d160d0890834583121210d200d089083458260106830c260841a2c189801068b062423f1a4018900f868b0c242156a0c1097a1068b061889400401863e2469006184bc1a2dd8212106900619d041ad0186
|4=>0x9e1068b0608a049c1c18612115360c256841a2c18c121068b060a6841a2c182981068b4a2420d102c182280021006084801b2c3095a1069006184ca1a2dc02281068b06087841a2c1869210690061a4841a424030c246830c263841a2c4842b1069006188941a2c11408c46830c24084
|5=>0x16184d308345830c263041a40182121068b06084841a2038b6c184841a40186120068b6c18a0908345d20c2420d160c48008f8690160c30900348030c2420d6a2c1863e2420d160c311120068b06184847834583045020d160e8821210690060a2841a401861e246830c268041a2c109
|6=>0x9c1c586121188d160c309095868b6c084841a2c314121188d160c109001068b06184ca0835a0b06184841a2d2821210690680c3090834586602420d16184846235998160c3090834c1006184841a2c309085468b900c30908345830c44a041a2ea86121068b70184841b508030c2420d
|7=>0x160c328121069006188891a40186282420db22c186121068b06184841b605830c2420d4c2c10908c469006184c508348030c2420d662c186282424e16184846235a8b06184cd08345830c50480082c18222106830c256841a2c1d7042420d16e0314121068b06187890834583042420d
|8=>0x1a2c18612106ce16d830908345830c2420d662c186120020d200c309083480b06184841a2c186222420d17683090834583042420d161848462345830c2420d6a0c31412b420d160c3090835c9006184841ae480706184841a2c1861200235160c4847c345830c2420d544018612106aa
|9=>0xb06184841b6c1861210687160c30908345830c50484
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>4
|4,0=>0x4aa8905116a219440a87c50eea1c9436a86850c6a17942ca854509ea129422a8405076a0d9418a82c504ea08940ea8185026a039404a8045
|5,0=>0x422c82d902b1ff63f2c7cd8f6b1e763c4a7718eb31d06394c7154dfb1b96366c6b58d3b1a16336c6558c7b1896306c5f58bbb17162d6c5958afb15962a6c5358a3b1416276c4d5897b1296246c47588bb1116216c41587fb0f961e6c3b5873b0e161b6c35946830ca6188c2f985c30b26158c299850309a6
|5,1=>0x28f6512ca0d93eb27764e2c9ad932b25f64b2c94d926b2476482c8ed91ab22f6452c88d90eb2176
|6,0=>0x2183c297844f06de0a3c0e680ef001dfcbbf367d8ef95def3bd777a2cf29de1bbbc776aeeb9dd3bba16736ce51dc6bb8676feede1db8bb6b66c8ed75dab3b4f7692cd09d9e3335765cec9dd90b31a7626ec35983b30075f4cbcdd76b2e675beeb659693acc658aeaf9d5bbab07552ea89d4e32957
|7,0=>0x246b48678fef1e1e39346b78c8f179a2bbc507894d111a1f34377
|8,0=>0x4936
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 92 then fld (dictB (i / 512) (i / 32 % 16)) 247 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 7 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 15 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))

def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 8 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
|0=>0x83516111235063506cd16360c0208350835161112362237121108351202083512350c2504110c2520270c2522352813043604360c250c25065112010835123506122050202720370c560c2506120c02123508351235063512360c252234123506090c2512350400083520340836123512110c25161122344a370c2520502235
|1=>0x16111235083606121236281312351235083512110c251652123504350c2506511235120108350c25083606120c250635123506120c25083508d512362037161106090c252037161112c50612061216362035161120351611623506120e131635123506d5123606511235202516116c27063508cd16360c25161104360c250635
|2=>0x161316351235083606351636083516111611121106250c2506121236165212352036161120361611163512360c020835203416112034161113390836121116111235161122361211223412110c250612202716111636
|_=>0
def opOffB : Nat → Nat → Nat
|4,0=>0x11000000000000000000000000000000000000000000000000000000000000000001000000000000
|5,0=>0x2011f11e10001d11c10001b10000000000001920000000001810000001620000000000000000000001510001411310000001210000000001110000f20000000000d20b20000000000a1000091081053000000000041022000000000000000
|5,1=>0x2a2291000000000000000000281271252000241000000231212000000000000
|6,0=>0x9b29929729619519329128f28d28b28920008728528328127f27d27b27927727527327126f26d26b26a10006826626426226025e25c25a25825625425225024f14d24b24924724524324124013e23c23a23823713523323213022e22c2
|7,0=>0xaa1a91a81a71a61a51a41a31a21a11a019f19e19d1
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 16 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 127), wireSAt ((code >>> 9) &&& 127)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 12 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmPalB : Nat → Nat
|0=>0x57802b40158009f004e00250011a008c00420020801000040001e000e0005a002c001200080003c0019000a00040001e000e0006800300010000400018000800020000
|1=>0x442fe213f00bd805da08288118309f140d08068317e18970b5f842fc217610af084d84224204010120808020080c060408015f80aec047602080080002fc017a00bb
|_=>0
def pmB : Nat → Nat → Nat
|4,0=>0x2000000000000000000000000000000002000000
|5,0=>0xe080500000002085004000a830000000040820041005400000160000040006800000000008c0084000100000280a40000381014004002113000015a00000000
|6,0=>0x4861955d87d92216c019cc5360bac86a733adc96ce032b1b1d8cddbed247b905fdd0de1186439edb064f6c62c7979
|7,0=>0x8bbefcfbbf218a2d66c7b
|8,0=>0x20
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 6 (j % 128); fld (pmPalB (k / 32)) 17 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_242,7,runOps true dom_242 (0,roots_242) ops)] else [])++(if pm.testBit 1 then [(dom_212,5,runOps true dom_212 (0,roots_212) ops)] else [])++(if pm.testBit 2 then [(dzo_166_16,5,runOps true dzo_166_16 (0,roots_166) ops)] else [])++(if pm.testBit 3 then [(dom_230,7,runOps true dom_230 (0,roots_230) ops)] else [])++(if pm.testBit 4 then [(dom_244,6,runOps true dom_244 (0,roots_244) ops)] else [])++(if pm.testBit 5 then [(dom_214,6,runOps true dom_214 (0,roots_214) ops)] else [])++(if pm.testBit 6 then [(dzo_226_16,5,runOps true dzo_226_16 (0,roots_226) ops)] else [])++(if pm.testBit 7 then [(dom_166,5,runOps true dom_166 (0,roots_166) ops)] else [])++(if pm.testBit 8 then [(dom_198,5,runOps true dom_198 (0,roots_198) ops)] else [])++(if pm.testBit 9 then [(dom_240,4,runOps true dom_240 (0,roots_240) ops)] else [])++(if pm.testBit 10 then [(dom_226,5,runOps true dom_226 (0,roots_226) ops)] else [])++(if pm.testBit 11 then [(dom_228,5,runOps true dom_228 (0,roots_228) ops)] else [])++(if pm.testBit 12 then [(dzo_230_16,6,runOps true dzo_230_16 (0,roots_230) ops)] else [])++(if pm.testBit 13 then [(dom_102,4,runOps true dom_102 (0,roots_102) ops)] else [])++(if pm.testBit 14 then [(dom_162,4,runOps true dom_162 (0,roots_162) ops)] else [])++(if pm.testBit 15 then [(dom_114,4,runOps true dom_114 (0,roots_114) ops)] else [])++(if pm.testBit 16 then [(dom_118,5,runOps true dom_118 (0,roots_118) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_246 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · exact cpcs (by decide +kernel) lowS_212 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_166_16_166 _ g hchk
    · exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_226_16_162 _ g hchk
    · exact cpcs (by decide +kernel) lowS_166 _ g hchk
    · exact cpcs (by decide +kernel) lowS_198 _ g hchk
    · exact cpcs (by decide +kernel) lowS_240 _ g hchk
    · exact cpcs (by decide +kernel) lowS_226 _ g hchk
    · exact cpcs (by decide +kernel) lowS_228 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_230_16_166 _ g hchk
    · exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · exact cpcs (by decide +kernel) lowS_162 _ g hchk
    · exact cpcs (by decide +kernel) lowS_114 _ g hchk
    · exact cpcs (by decide +kernel) lowS_118 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_242 7 s (0, roots_242) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_246 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_242 h

def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {v ys} (h : RunD true dom_246 goalM v ys) : RunD true dom_246 goalM v (ori ys) := h
def Z (s : Nat) := barP true dom_246 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 30 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 30 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 85 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 85 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 62 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 62 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 14 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 14 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 8) : ∀ i < NN s, bar true dom_246 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
  · exact z8 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_246 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 8) (h : RunD true dom_246 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_246 roots_246 goal_246 9 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_246

theorem lowS_246 : Lower true dom_246 roots_246 goal_246 9 := S_246.noCircuit

def dzo_167_16:=0xff000000ff0000000000000000000000ff000000ff0000

def gzo_167_16:=0xff000000fe0000000000000000000000ee000000aa0000

def gsh_167_16:=0xff000000fe0000000000000000000000ee000000aa

theorem lowS_zo_167_16_166:Lower true dzo_167_16 roots_167 gzo_167_16 6:=lower_iso (d1:=dom_167) (roots1:=roots_167) (T1:=gsh_167_16) [(dom_167,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_167_16) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xaa000000aa0000000000000000000000aa000000aa,0,1)] (by decide +kernel) (by decide +kernel) lowS_166)

def dzo_231_16:=0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000

def gzo_231_16:=0xff000000ff000000ff000000fe000000ff000000ff000000ee000000aa0000

def gsh_231_16:=0xff000000ff000000ff000000fe000000ff000000ff000000ee000000aa

theorem lowS_zo_231_16_166:Lower true dzo_231_16 roots_231 gzo_231_16 7:=lower_iso (d1:=dom_231) (roots1:=roots_231) (T1:=gsh_231_16) [(dom_231,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_231_16) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(rowMask232,0,1),(0xff000000ff0000000000000000000000ff000000ff0000000000000000,0,64)] (by decide +kernel) (by decide +kernel) lowS_166)

namespace S_247
def pairsG : List (Nat × Nat) := [(1,17), (1,33), (1,65), (2,34), (2,66), (2,130), (3,19), (3,35), (3,67), (3,131), (4,68), (4,132), (5,21), (5,37), (5,69), (5,133), (6,38), (6,70), (6,134), (7,23), (7,39), (7,71), (7,135), (16,17), (16,80), (18,19), (18,50), (18,82), (18,146), (20,21), (20,84), (20,148), (22,23), (22,54), (22,86), (22,150), (32,33), (32,34), (32,160), (36,37), (36,38), (36,100), (36,164), (48,49), (48,50), (48,112), (48,176), (52,53), (52,54), (52,116), (52,180), (64,65), (64,66), (64,68), (64,80), (64,192), (96,97), (96,98), (96,100), (96,112), (96,224), (128,130), (128,132), (128,160), (128,192), (129,131), (129,133), (129,145), (129,161), (129,193), (144,145), (144,146), (144,148), (144,176), (144,208)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x7ffffffffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_247.map (· &&& dom_247)
def goalM : Nat := goal_247 &&& dom_247
def NN : Nat → Nat
|6=>3
|7=>7
|8=>5
|9=>4
|10=>1
|_=>0
def HT : Nat → Nat → Nat
|6,0=>0x68651161100d08b
|7,0=>0xe1c5ddefe0c36dfc2f37c0a62ab60a0013a
|8,0=>0xc5f83bf10cb4299acf6195634
|9,0=>0xce95e929b772daa1ad5e
|10,0=>0x6bf33
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000ff0000ff00ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000ff0000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000000300030003000300030003000300030003000300030003000300030000000000000000000000000000000000000000ff00ff00ff00ff00ff00ff00000000cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00ccff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00000000000000000f000f000f000f000f000f000f000f000f000f000f000f0000000000000000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff00000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa330033003300330033003300330033003300330033003300330033000000000f000f000f000f000f000f000f000f000f000f000f000f000f000f00000000ff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000ff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x38ad49101039e56a481038a922027038a9204e0328ad49020315a92200c315a92040c315a4184062b483081862a482080ca2b524418a920820619456a4813152441c062906b080ca2a488398a418820
|1=>0xe2b524081d02b524080c56a481
|_=>0
def stOffB : Nat → Nat → Nat
|6,0=>0xe7077007
|7,0=>0x4183a73282b72471c8157
|8,0=>0x678607588517498
|9,0=>0x8687f77786f8
|10,0=>0x8e7
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 17 then fld (dictB (i / 512) (i / 32 % 16)) 248 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 5 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 12 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))

def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 4 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
|0=>0x2817050812856a20816a20813037057050813017056273017056273017056373017053037050816373017053033017057056a208168e627
|_=>0
def opOffB : Nat → Nat → Nat
|6,0=>0x200000
|7,0=>0x14344ce32cc8314c23
|8,0=>0x1f2749b264972
|9,0=>0x9063188611
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 12 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 31), wireSAt ((code >>> 7) &&& 31)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 10 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmPalB : Nat → Nat
|0=>0x7bd7fa7fcfe9bd1fa2ec5887d03c01c01000
|_=>0
def pmB : Nat → Nat → Nat
|6,0=>0x100
|7,0=>0x3634527
|8,0=>0x9999a
|9,0=>0xb99c
|10,0=>8
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 4 (j % 128); fld (pmPalB (k / 32)) 11 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_246,9,runOps true dom_246 (0,roots_246) ops)] else [])++(if pm.testBit 1 then [(dom_87,6,runOps true dom_87 (0,roots_87) ops)] else [])++(if pm.testBit 2 then [(dom_119,8,runOps true dom_119 (0,roots_119) ops)] else [])++(if pm.testBit 3 then [(dom_243,9,runOps true dom_243 (0,roots_243) ops)] else [])++(if pm.testBit 4 then [(dom_245,9,runOps true dom_245 (0,roots_245) ops)] else [])++(if pm.testBit 5 then [(dom_215,9,runOps true dom_215 (0,roots_215) ops)] else [])++(if pm.testBit 6 then [(dzo_167_16,6,runOps true dzo_167_16 (0,roots_167) ops)] else [])++(if pm.testBit 7 then [(dom_183,8,runOps true dom_183 (0,roots_183) ops)] else [])++(if pm.testBit 8 then [(dom_231,8,runOps true dom_231 (0,roots_231) ops)] else [])++(if pm.testBit 9 then [(dzo_231_16,7,runOps true dzo_231_16 (0,roots_231) ops)] else [])++(if pm.testBit 10 then [(dom_167,6,runOps true dom_167 (0,roots_167) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_247 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · exact cpcs (by decide +kernel) lowS_87 _ g hchk
    · exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_167_16_166 _ g hchk
    · exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_231_16_166 _ g hchk
    · exact cpcs (by decide +kernel) lowS_167 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_246 9 s (0, roots_246) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_247 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_246 h

def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {v ys} (h : RunD true dom_247 goalM v ys) : RunD true dom_247 goalM v (ori ys) := h
def Z (s : Nat) := barP true dom_247 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 3 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 3 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 7 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 7 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8 : ∀ i, 0 ≤ i → i < 5 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 5 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9 : ∀ i, 0 ≤ i → i < 4 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 4 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 10) : ∀ i < NN s, bar true dom_247 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
  · exact z8 i (Nat.zero_le i) hi
  · exact z9 i (Nat.zero_le i) hi
  · exact z10 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_247 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

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
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_247 roots_247 goal_247 11 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_247

theorem lowS_247 : Lower true dom_247 roots_247 goal_247 11 := S_247.noCircuit

end B2

namespace B0
def dom_89 : Nat := 0x30303030000000003030303

def goal_89 : Nat := 0xffaaffaaffaaffaaaaaa0000aaaa0000ffaaffaaffaaffaaaaaa0000aaaa0000

def roots_89 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_93 : Nat := 0x333333330000000033333333

def roots_93 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303

def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333

def goal_125 : Nat := 0xfffafffaffaaffaafafaf0f0aaaa0000fffafffaffaaffaafafaf0f0aaaa0000

def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_164 : Nat := 0x110000001100000000000000000000001100000011

def goal_164 : Nat := rowMask266

def roots_164 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_172 : Nat := 0x11110000111100000000000000000000111100001111

def goal_172 : Nat := 0xfffffffffff0fff0fffffffffff0fff0f0f0f0f000000000f0f0f0f000000000

def roots_172 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333

def goal_173 : Nat := 0xfffffffffffafffafffffffffffafffaf0f0f0f000000000f0f0f0f000000000

def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_180 : Nat := 0x1100110011001100000000000000000011001100110011

def goal_180 : Nat := 0xfffffffffffff0f0fffffffffffff0f0f0f0f0f000000000f0f0f0f000000000

def roots_180 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_181 : Nat := rowMask260

def goal_181 : Nat := 0xfffffffffffffafafffffffffffffafafafaf0f0aaaa0000fafaf0f0aaaa0000

def roots_181 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303

def goal_185 : Nat := 0xffffffffffffffaaffffffffffffffaaaaaa0000aaaa0000aaaa0000aaaa0000

def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_188 : Nat := 0x111111111111111100000000000000001111111111111111

def goal_188 : Nat := 0xfffffffffffffff0fffffffffffffff0f0f0f0f000000000f0f0f0f000000000

def roots_188 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333

def goal_189 : Nat := 0xfffffffffffffffafffffffffffffffafafaf0f0aaaa0000fafaf0f0aaaa0000

def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_204 : Nat := 0x1111000000000000111100000000000011110000000000001111

def goal_204 : Nat := 0xfff0fff0fff0fff0fff0fff0fff0fff0ff00ff00ff00ff000000000000000000

def roots_204 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := rowMask301

def goal_205 : Nat := 0xfffafffafffafffafffafffafffafffaffaaffaaffaaffaa0000000000000000

def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_209 : Nat := rowMask204

def goal_209 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaaaaaaaaaaaaaaaaaaaaaa0000aaaa0000

def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := rowMask149

def goal_213 : Nat := 0xfffffafafffffafafffffafafffffafaaaaaaaaaaaaaaaaaaaaa0000aaaa0000

def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_216 : Nat := rowMask294

def goal_216 : Nat := rowMask269

def roots_216 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := rowMask295

def goal_217 : Nat := 0xffffffaaffffffaaffffffaaffffffaaffaaffaaffaaffaaaaaa0000aaaa0000

def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_220 : Nat := rowMask291

def goal_220 : Nat := rowMask270

def roots_220 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := rowMask292

def goal_221 : Nat := 0xfffffffafffffffafffffffafffffffaffaaffaaffaaffaaaaaa0000aaaa0000

def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303

def goal_233 : Nat := 0xffffffffffaaffaaffffffffffaaffaaffaaffaaffaaffaa0000000000000000

def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_236 : Nat := 0x111100001111000011110000111100001111000011110000111100001111

def goal_236 : Nat := 0xfffffffffff0fff0fffffffffff0fff0fff0fff0ff00ff00f0f0f0f000000000

def roots_236 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := rowMask282

def goal_237 : Nat := 0xfffffffffffafffafffffffffffafffafffafffaffaaffaaf0f0f0f000000000

def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_241 : Nat := rowMask221

def goal_241 : Nat := 0xffffffffffffaaaaffffffffffffaaaaaaaaaaaaaaaaaaaaaaaa0000aaaa0000

def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := rowMask87

def goal_245 : Nat := 0xfffffffffffffafafffffffffffffafafafafafaaaaaaaaafafaf0f0aaaa0000

def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_248 : Nat := 0x101010101010101010101010101010101010101010101010101010101010101

def goal_248 : Nat := 0xffffffffffffff00ffffffffffffff00ff00ff00ff00ff000000000000000000

def roots_248 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303

def goal_249 : Nat := 0xffffffffffffffaaffffffffffffffaaffaaffaaffaaffaaaaaa0000aaaa0000

def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111

def goal_252 : Nat := 0xfffffffffffffff0fffffffffffffff0fff0fff0ff00ff00f0f0f0f000000000

def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := rowMask271

def goal_253 : Nat := 0xfffffffffffffffafffffffffffffffafffafffaffaaffaafafaf0f0aaaa0000

def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

theorem lowS_164 : Lower true dom_164 roots_164 goal_164 4 := lower_iso (d1 := B5.dom_145) (roots1 := B5.roots_145) (T1 := B5.goal_145) [(rowMask0, 1), (rowMask10, 3), (rowMask25, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_145

theorem lowS_89 : Lower true dom_89 roots_89 goal_89 4 := lower_iso (d1 := B5.dom_85) (roots1 := B5.roots_85) (T1 := B5.goal_85) [(rowMask29, 4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_85

theorem lowS_172 : Lower true dom_172 roots_172 goal_172 5 := lower_iso (d1 := B5.dom_147) (roots1 := B5.roots_147) (T1 := B5.goal_147) [(rowMask10, 3), (rowMask11, 6), (rowMask25, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_147

theorem lowS_180 : Lower true dom_180 roots_180 goal_180 5 := lower_iso (d1 := B5.dom_147) (roots1 := B5.roots_147) (T1 := B5.goal_147) [(rowMask10, 3), (rowMask11, 6), (rowMask28, 30), (rowMask37, 14)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_147

theorem lowS_204 : Lower true dom_204 roots_204 goal_204 4 := lower_iso (d1 := B5.dom_85) (roots1 := B5.roots_85) (T1 := B5.goal_85) [(rowMask0, 1), (rowMask27, 7), (rowMask25, 16), (rowMask183, 112), (rowMask34, 48)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_85

theorem lowS_209 : Lower true dom_209 roots_209 goal_209 5 := lower_iso (d1 := B5.dom_147) (roots1 := B5.roots_147) (T1 := B5.goal_147) [(rowMask44, 127), (rowMask16, 2), (rowMask11, 6), (rowMask28, 30), (rowMask35, 15), (rowMask144, 62)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_147

theorem lowS_216 : Lower true dom_216 roots_216 goal_216 4 := lower_iso (d1 := B5.dom_85) (roots1 := B5.roots_85) (T1 := B5.goal_85) [(rowMask0, 1), (rowMask27, 7), (rowMask36, 28), (rowMask22, 12), (rowMask183, 112), (rowMask34, 48)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_85

theorem lowS_213 : Lower true dom_213 roots_213 goal_213 6 := lower_iso (d1 := B2.dom_117) (roots1 := B2.roots_117) (T1 := B2.goal_117) [(rowMask49, 96), (rowMask26, 32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B2.lowS_117

theorem lowS_173 : Lower true dom_173 roots_173 goal_173 6 := lower_iso (d1 := B5.dom_151) (roots1 := B5.roots_151) (T1 := B5.goal_151) [(rowMask0, 1), (rowMask27, 7), (rowMask10, 3), (rowMask25, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_151

theorem lowS_181 : Lower true dom_181 roots_181 goal_181 8 := lower_iso (d1 := B5.dom_179) (roots1 := B5.roots_179) (T1 := B5.goal_179) [(rowMask16, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_179

theorem lowS_185 : Lower true dom_185 roots_185 goal_185 6 := lower_iso (d1 := B5.dom_151) (roots1 := B5.roots_151) (T1 := B5.goal_151) [(rowMask11, 6), (rowMask36, 28)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_151

theorem lowS_188 : Lower true dom_188 roots_188 goal_188 6 := lower_iso (d1 := B5.dom_151) (roots1 := B5.roots_151) (T1 := B5.goal_151) [(rowMask27, 7), (rowMask28, 30), (rowMask10, 3), (rowMask16, 2), (rowMask22, 12)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_151

theorem lowS_205 : Lower true dom_205 roots_205 goal_205 5 := lower_iso (d1 := B2.dom_103) (roots1 := B2.roots_103) (T1 := B2.goal_103) [(rowMask11, 6), (rowMask49, 96), (rowMask26, 32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B2.lowS_103

theorem lowS_217 : Lower true dom_217 roots_217 goal_217 6 := lower_iso (d1 := B2.dom_115) (roots1 := B2.roots_115) (T1 := B2.goal_115) [(rowMask16, 2), (rowMask11, 6), (rowMask49, 96), (rowMask26, 32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B2.lowS_115

theorem lowS_220 : Lower true dom_220 roots_220 goal_220 5 := lower_iso (d1 := B2.dom_118) (roots1 := B2.roots_118) (T1 := B2.goal_118) [(rowMask11, 6), (rowMask49, 96), (rowMask26, 32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B2.lowS_118

theorem lowS_233 : Lower true dom_233 roots_233 goal_233 5 := lower_iso (d1 := B2.dom_103) (roots1 := B2.roots_103) (T1 := B2.goal_103) [(rowMask11, 6), (rowMask22, 12), (rowMask214, 124), (rowMask36, 28), (rowMask26, 32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B2.lowS_103

theorem lowS_236 : Lower true dom_236 roots_236 goal_236 7 := lower_iso (d1 := B6.dom_117) (roots1 := B6.roots_117) (T1 := B6.goal_117) [(rowMask0, 1), (rowMask27, 7), (rowMask22, 12), (rowMask33, 31), (rowMask214, 124), (rowMask32, 63), (rowMask10, 3)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B6.lowS_117

theorem lowS_241 : Lower true dom_241 roots_241 goal_241 6 := lower_iso (d1 := B2.dom_117) (roots1 := B2.roots_117) (T1 := B2.goal_117) [(rowMask29, 4), (rowMask214, 124), (rowMask36, 28), (rowMask26, 32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B2.lowS_117

theorem lowS_248 : Lower true dom_248 roots_248 goal_248 5 := lower_iso (d1 := B2.dom_118) (roots1 := B2.roots_118) (T1 := B2.goal_118) [(rowMask11, 6), (rowMask214, 124), (rowMask22, 12), (rowMask25, 16), (rowMask26, 32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B2.lowS_118

theorem lowS_125 : Lower true dom_125 roots_125 goal_125 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x30303030303030303030303030303030, 32, 36), (0x33333333000000003333333300000000, 4, 36)] (by decide +kernel) (by decide +kernel) lowS_89

theorem lowS_237 : Lower true dom_237 roots_237 goal_237 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x222200002222000022220000222200002222000022220000222200002222, 64, 65)] (by decide +kernel) (by decide +kernel) lowS_236

theorem lowS_245 : Lower true dom_245 roots_245 goal_245 9 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(rowMask219, 1, 65)] (by decide +kernel) (by decide +kernel) lowS_181

theorem lowS_252 : Lower true dom_252 roots_252 goal_252 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x1111000011110000111100001111000011110000111100001111000011110000, 128, 144)] (by decide +kernel) (by decide +kernel) lowS_236

theorem lowS_189 : Lower true dom_189 roots_189 goal_189 9 := lower_iso (d1 := B5.dom_183) (roots1 := B5.roots_183) (T1 := B5.goal_183) [(rowMask11, 6), (rowMask16, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_183

theorem lowS_221 : Lower true dom_221 roots_221 goal_221 8 := lower_iso (d1 := B2.dom_119) (roots1 := B2.roots_119) (T1 := B2.goal_119) [(rowMask11, 6), (rowMask49, 96), (rowMask26, 32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B2.lowS_119

theorem lowS_249 : Lower true dom_249 roots_249 goal_249 8 := lower_iso (d1 := B2.dom_119) (roots1 := B2.roots_119) (T1 := B2.goal_119) [(rowMask11, 6), (rowMask214, 124), (rowMask36, 28), (rowMask26, 32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B2.lowS_119

def dzo_221_32:=0x3333333300000000333333330000000033333333000000003333333300000000

def gzo_221_32:=0x3333333300000000333333330000000033323332000000003232303000000000

def gsh_221_32:=0x33333333000000003333333300000000333233320000000032323030

theorem lowS_zo_221_32_89:Lower true dzo_221_32 roots_221 gzo_221_32 6:=lower_iso (d1:=dom_221) (roots1:=roots_221) (T1:=gsh_221_32) [(dom_221,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_221_32) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(rowMask234,0,4),(0x33333333000000003333333300000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_89)

def dzo_121_4:=0x30303030303030303030303030303030

def gzo_121_4:=0x30303030302030203030303020200000

def gsh_121_4:=0x3030303030203020303030302020000

theorem lowS_zo_121_4_89:Lower true dzo_121_4 roots_121 gzo_121_4 5:=lower_iso (d1:=dom_121) (roots1:=roots_121) (T1:=gsh_121_4) [(dom_121,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_121_4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x3030303000000000303030300000000,0,32)] (by decide +kernel) (by decide +kernel) lowS_89)

def dzo_180_64:=0x11001100110011000000000000000000110011001100110000000000000000

def gzo_180_64:=0x11001100110010000000000000000000100010000000000000000000000000

def gsh_180_64:=0x1100110011001000000000000000000010001000000000

theorem lowS_zo_180_64_180:Lower true dzo_180_64 roots_180 gzo_180_64 5:=lower_iso (d1:=dom_180) (roots1:=roots_180) (T1:=gsh_180_64) [(dom_180,64)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_180_64) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [] (by decide +kernel) (by decide +kernel) lowS_180)

def dzo_188_64:=0x1111111111111111000000000000000011111111111111110000000000000000

def gzo_188_64:=0x1111111111111110000000000000000011101110110011000000000000000000

def gsh_188_64:=0x111111111111111000000000000000001110111011001100

theorem lowS_zo_188_64_180:Lower true dzo_188_64 roots_188 gzo_188_64 6:=lower_iso (d1:=dom_188) (roots1:=roots_188) (T1:=gsh_188_64) [(dom_188,64)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_188_64) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x110011001100110000000000000000001100110011001100,0,8)] (by decide +kernel) (by decide +kernel) lowS_180)

def dzo_189_64:=0x3333333333333333000000000000000033333333333333330000000000000000

def gzo_189_64:=0x3333333333333332000000000000000033323332332233220000000000000000

def gsh_189_64:=0x333333333333333200000000000000003332333233223322

theorem lowS_zo_189_64_180:Lower true dzo_189_64 roots_189 gzo_189_64 7:=lower_iso (d1:=dom_189) (roots1:=roots_189) (T1:=gsh_189_64) [(dom_189,64)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_189_64) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x222222222222222200000000000000002222222222222222,0,1),(0x330033003300330000000000000000003300330033003300,0,8)] (by decide +kernel) (by decide +kernel) lowS_180)

def dzo_173_64:=0x333300003333000000000000000000003333000033330000000000000000

def gzo_173_64:=0x333300003332000000000000000000003332000033220000000000000000

def gsh_173_64:=0x33330000333200000000000000000000333200003322

theorem lowS_zo_173_64_164:Lower true dzo_173_64 roots_173 gzo_173_64 6:=lower_iso (d1:=dom_173) (roots1:=roots_173) (T1:=gsh_173_64) [(dom_173,64)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_173_64) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x22220000222200000000000000000000222200002222,0,1),(0x33000000330000000000000000000000330000003300,0,8)] (by decide +kernel) (by decide +kernel) lowS_164)

def dzo_93_32:=0x33333333000000003333333300000000

def gzo_93_32:=0x33323332000000003232303000000000

def gsh_93_32:=0x333233320000000032323030

theorem lowS_zo_93_32_89:Lower true dzo_93_32 roots_93 gzo_93_32 5:=lower_iso (d1:=dom_93) (roots1:=roots_93) (T1:=gsh_93_32) [(dom_93,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_93_32) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x303030300000000030303030,0,4)] (by decide +kernel) (by decide +kernel) lowS_89)

def dzo_217_32:=rowMask276

def gzo_217_32:=0x303030300000000030303030000000003020302000000000202000000000000

def gsh_217_32:=rowMask296

theorem lowS_zo_217_32_89:Lower true dzo_217_32 roots_217 gzo_217_32 5:=lower_iso (d1:=dom_217) (roots1:=roots_217) (T1:=gsh_217_32) [(dom_217,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_217_32) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(rowMask297,0,128)] (by decide +kernel) (by decide +kernel) lowS_89)

def dzo_89_4:=0x303030300000000030303030

def gzo_89_4:=0x302030200000000020200000

def gsh_89_4:=0x30203020000000002020000

theorem lowS_zo_89_4_89:Lower true dzo_89_4 roots_89 gzo_89_4 4:=lower_iso (d1:=dom_89) (roots1:=roots_89) (T1:=gsh_89_4) [(dom_89,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_89_4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [] (by decide +kernel) (by decide +kernel) lowS_89)

def dzo_249_4:=0x3030303030303030303030303030303030303030303030303030303030303030

def gzo_249_4:=0x3030303030303030303030303030303030303030302030203030303020200000

def gsh_249_4:=0x303030303030303030303030303030303030303030203020303030302020000

theorem lowS_zo_249_4_89:Lower true dzo_249_4 roots_249 gzo_249_4 6:=lower_iso (d1:=dom_249) (roots1:=roots_249) (T1:=gsh_249_4) [(dom_249,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_249_4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(rowMask276,0,32),(0x303030303030303030303030303030300000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_89)

def dzo_217_4:=rowMask234

def gzo_217_4:=0x30303030000000003030303000000000302030200000000020200000

def gsh_217_4:=rowMask296

theorem lowS_zo_217_4_89:Lower true dzo_217_4 roots_217 gzo_217_4 5:=lower_iso (d1:=dom_217) (roots1:=roots_217) (T1:=gsh_217_4) [(dom_217,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_217_4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(rowMask297,0,128)] (by decide +kernel) (by decide +kernel) lowS_89)

def dzo_181_64:=rowMask219

def gzo_181_64:=0x33003300330032000000000000000000320032002200220000000000000000

def gsh_181_64:=0x3300330033003200000000000000000032003200220022

theorem lowS_zo_181_64_180:Lower true dzo_181_64 roots_181 gzo_181_64 6:=lower_iso (d1:=dom_181) (roots1:=roots_181) (T1:=gsh_181_64) [(dom_181,64)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_181_64) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x2200220022002200000000000000000022002200220022,0,1)] (by decide +kernel) (by decide +kernel) lowS_180)

def dzo_89_32:=0x3030303000000000303030300000000

def gzo_89_32:=0x3020302000000000202000000000000

def gsh_89_32:=0x30203020000000002020000

theorem lowS_zo_89_32_89:Lower true dzo_89_32 roots_89 gzo_89_32 4:=lower_iso (d1:=dom_89) (roots1:=roots_89) (T1:=gsh_89_32) [(dom_89,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_89_32) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [] (by decide +kernel) (by decide +kernel) lowS_89)

namespace S_253
def pairsG : List (Nat × Nat) := [(1,17), (1,65), (1,129), (4,36), (4,132), (5,21), (5,37), (5,69), (5,133), (8,72), (8,136), (9,25), (9,73), (9,137), (12,44), (12,76), (12,140), (13,29), (13,45), (13,77), (13,141), (16,17), (16,144), (20,21), (20,52), (20,148), (24,25), (24,88), (24,152), (28,29), (28,60), (28,92), (28,156), (32,36), (32,160), (33,37), (33,49), (33,97), (33,161), (40,44), (40,104), (40,168), (41,45), (41,57), (41,105), (41,169), (48,49), (48,52), (48,176), (56,57), (56,60), (56,120), (56,184), (64,65), (64,72), (68,69), (68,76), (68,100), (68,196), (80,81), (80,88), (80,208), (84,85), (84,92), (84,116), (84,212), (96,97), (96,100), (96,104), (96,224), (112,113), (112,116), (112,120), (112,240), (128,129), (128,132), (128,136), (128,144), (128,160), (192,193), (192,196), (192,200), (192,208), (192,224)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfffffffffffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_253.map (· &&& dom_253)
def goalM : Nat := goal_253 &&& dom_253
def NN : Nat → Nat
|3=>1
|4=>6
|5=>24
|6=>91
|7=>136
|8=>83
|9=>11
|10=>1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0x8e7ca
|4,0=>0x846557ab9d75d2a5249b32b070b3c2
|5,0=>0xf56ffd51dcb1405ab2479bf95903018fc876cb8e6a5576484b620fd57d144da2f4540c40e6d3e86e303ed2f4fd2d17f1fec61d6e011d8e0dff705615
|6,0=>0xf9115f1f27e2b22e2468dbb7ada23ad64b5cdafcc7868c76d7c401ebdb10bd273ba621b6031b12eaa8ff7a487aa444aa3c079fd509d6489bea19966e95bde957058d2b38caa68c5718a5bc88368883057bfae7be24790726b04969b6f68b9b669186422b6185f5e28d5c0c85b86d5aa7d5692a544fd5329c5287f5136d4d844481d4440e74403b42bff4129340cd040cc33bf2539f3838eab37f823442330b822f00d2d6c82994228fae28ca727d8d25e48251be243b9201cb1f69f1ed9d1c7c01c7141b8d0194a61190210d740e5850c1ed0aafb09703083c706de60610d04e3b0156d
|7,0=>0xe543ce301fe0814da9f2d99bfd97a8d2badd1222c7ea1c6561c0f78be09fbdd99b3aaab39feaf4bcae269a9646a84b1a80faa518aa2358a02569f18f9d6bd9b62799e539642a940c7932d7911668ff2e8c0778b7f98b6708609e807478032678e7976eb774b9a7415a6e2686c2e46a5c16a130693c66539964d495e6ed5ba485a47858da2569ee542ba52ec152d0251d1f506c4501434fff74d1504c6954bce049f7f48a6547b9446291450084409540b9f3f5c33f2013eba63cb2f3bbc23b6d136fdf357b034b15345a7344fb2f9862d6ce2d0a32b59a2b50d296be259a8243b9242a923ed822e5b1f1571e8601d4d21d2251cbe21ba621a3f3199ef169691668414fe91375b135ca119ba0fdc10ef050e9df0b0c40ab270a4380a35c094ec08be406e2c06caa0623205cb7055a103e22039460376502c60026d2020050022e
|7,1=>0xff9b8fa8acfa5e6f6d59f4507f1c0deb7e7e54e8
|8,0=>0xf42c2edd66ed0e1e13a1dcbeed6092ccd68c2884bfe9cbb6a3a72d9a1a4c9fe189ee329def39cfd49a1269192e8b4b68a3138777b84b9f8343a82b2a80a0880485803ee73a9f6abdb67726662e66285c5e70f5ba23596b2582bd57d715699254d4953449520ff50fef507c34f9014aa144a27349932483e04679f4338141bce41422405e13e5033dbe23c1a03b25439c2238bf038bbb35f0c347f13132f3044a2e89a2e70c23f3e220e121b8320ee81cbe217dff0f1820d9a70c96409816093f008932067c60671a0616402d3c02464
|9,0=>0x91f0c5c5325260d4901b42e4d4181b28ae1155a01140f0e3bf0a935
|10,0=>0x6412b
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xcccccccc00000000cccccccc00000000c0c0c0c000000000c0c0c0c0000000033333333000000003333333300000000000000000000000000000000cccccccc00000000cccccccc00000000c8c8c8c800000000c8c8c8c800000002222222233333333222222223333333322222222222222222222222222222222cccccccccccccccc0c0c0c0c0c0c0c0ccccccccccccccccc0000000000000000303030303030303030303030303030300000000000000000000000000000000cc88cc88cc88cc880c080c080c080c08cc88cc88cc88cc880000000000000003332333233323332333233323332333200000000000000000000000000000000ccc8ccc8ccc8ccc8ccc8ccc8ccc8ccc8ccc8ccc8ccc8ccc8ccc8ccc8ccc8cccb333333333323332333333333332333233333333000000003333333300000000ccccccccccccccccccccccccccccccccc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c3333333333223322333333333322332200000000000000000000000000000000cccccccccc88cc88cccccccccc88cc88cccccccccc88cc88cccccccccc88cc8b300330033003300330033003300330033003300330033003300330033003300cccccccccccccc88cccccccccccccc88cccc0000cccc0000cccc0000cccc0003333333333333333000000000000000033333333333333330000000000000000cc88cc88cc88cc88cc88cc88cc88cc88cc88cc88cc88cc88cc88cc88cc88cc88303030303030303030303030303030303030303020202020303030302020202cccccccccccccccccccccccccccccccccccccccccccccccc0000000000000000000000033333333000000003333333300000000323232320000000032323232888888888888888888888888888888888888888888888888888888888888888b3333333333333333333333333333333000000000000000000000000000000000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c000000000c0c0c0c000000030303030303030303030303030303030303030300000000030303030000000000000cccc0000cccc0000cccc0000cccc0000c8c80000c8c80000c8c80000c8cb333333300000000333333330000000033333333000000003333333300000000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c080808080c0c0c0c080808083322332233223322332233223322332233223322332233220000000000000000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0003030303030303030303030303030303030303030303030303030303030303030cccccccccc88cc88cccccccccc88cc88ccc8ccc8cc88cc88c0c0c0c000000003333333333333333333333333333333322222222222222222222222222222222
|0,1=>0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c080c080c0c0c0c0c080c0b333333300110011333333330011001133333333000000003333333300000000004400440044004400440044004400440000000000000000000000000000000030303030001000103030303000100010303030300000000030303030000000000008c8c00008c8c00008c8c00008c8c0000888800008888000088880000888b333333333333333333333333333333332323232323232323232323232323232ccccccc8ccccccc8ccccccc8ccccccc8cccc0000cccc0000cccc0000cccc0001111111111111111111111111111111100000000000000000000000000000000cccccccc88888888cccccccc8888888800000000000000000000000000000003333333322222222333333332222222233333333222222223333333322222222ccccccccc8c8c8c8ccccccccc8c8c8c8c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c00000000000000003322332233223322000000000000000033223322332233228888cccc8888cccc8888cccc8888cccc8888cc888888cc888888cc888888cc88000333300003333000033330000333300003322000033220000332200003322c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c080c080c0c0c0c0c080c083232323232323232323232323232323232323232323232323232323232323232888c888c888c888c888c888c888c888c8888888888888888888888888888888800000003333333333223322333333330000000000000000332233223322332244444444444444444444444444444444000000000000000044004400440044000003333000033330000333300003333000000000000000000003322000033220000cccc0000cccc0000cccc0000cccc0000888800008888000088880000888b333333333333333333333333333333333333333222222223333333322222222ccccccccc0c0c0c0ccccccccc0c0c0c0ccccccccc0c0c0c0ccccccccc0c0c0c2323232323232323232323232323232322222222222222222222222222222222000004040000040400000404000004040000888800008888000088880000888b333333333333333333333333333333333333333000000003333333300000000cccccccccccccccc00000000cccccccccccccccccccccccc0000000000000003322332233223322000000003322332233223322332233220000000000000000cccccccc00000000cccccccc00000000c0c0c0c000000000c0c0c0c0000000033223322332233220000000003020302332233223322332200000000000000000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c08080808080808080808080808080808000222200003333000022220000333300002222000022220000222200002222
|0,2=>0xcccccccccccccccccccccccccccccccc0000000000000000cc88cc88cc88cc88000111100001111000011110000111100000000000000000000000000000000c0c0cccc00000000c0c0cccc00000000c0c0c8c800000000c0c0c8c8000000000000000111111110000000011111111222222222222222222222222222222220000cc8c0000cc8c0000cc8c0000cc8c0000cc880000cc880000cc880000cc880000000000000000000000000000000333333333322332233333333332233224444444444444444444444444444444444004400440044004400440044004402233223322332233223322332233223322322232223222322232223222322232cccc0000cccccccccccc0000cccccccccccc0000cccc0000cccc0000cccc0003332333233323332333233323332333222222222222222222222222222222222cccccccccccccccccccccccccccccccccc88cc88cc88cc88cc88cc88cc88cc8b3333333333322223333333333332222222222222222222222222222222222224444444444444444444444444444444444444444440044004444444444004402233223322332233223322332233223322222222222222222222222222222222000088cc000088cc000088cc000088cc000088880000888800008888000088880003333000033330000333300003333000033330000332200003333000033224404440444044404440444044404440444004400440044004400440044004400000000033333333000000003333333300000000222222220000000022222222c0c0c0c000400040c0c0c0c000400040c0c0c0c000000000c0c0c0c00000000333333333333333333333333333333333333000033330000333300003333000000000c0c00000c0c00000c0c00000c0ccccc0000cccc0000cccc0000cccc0003333333333330000333333333333000000000000000000000000000000000000cccccccccccc0000cccccccccccc0000cccccccccccc0000cccccccccccc0003333333333333030333333333333303030303030303030303030303030303030cccccccccccc8888cccccccccccc8888cccc0000cccc0000cccc0000cccc000333333333333333300000000030303033333333333333333000000000000000000cc00cc00cc00cc00000000000c000c00cc00cc00cc00cc0000000000000002222222223232323222222222323232322222222222222222222222222222222000000000c0c0c0c000000000c0c0c0c0000000000000000000000000000000000022220000232300002222000023230000222200002222000022220000222200cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc0000000000000000000000000100010000000000010001030303030303030303030303030303030
|0,3=>0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c00000c0c0c0c0c0c00000000000030303333000000003030333300000000303030300000000030303030cccccccccccccccccccccccccccccccccccccccccccc0000cccccccccccc0000303030303030303030303030303030303030303030300000303030303030000c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c800000000000000000000000000000000101010100000000010101010000000033333333000000003333333300000000ccccccccccccccccccccccccccccccccccccc0c0ccccc0c0ccccc0c0ccccc0c3333333300000000333333330000000033333030000000003333303000000000cccccccc0c0c0c0ccccccccc0c0c0c0ccccccccc00000000cccccccc000000033333333111111113333333311111111333333330000000033333333000000000c0c0c0c040404040c0c0c0c040404040c0c0c0c000000000c0c0c0c00000000011001100110011001100110011001100110011000000000011001100000000000000000000cccc000000000000cccc0000000000008888000000000000888b323332333233323332333233323332333223322332233223322332233223322cccc0c0ccccc0c0ccccc0c0ccccc0c0ccccc0000cccc0000cccc0000cccc0003333333333333333333333333333333333333333303030303333333330303030c0c0ccccc0c0ccccc0c0ccccc0c0ccccc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c3030333300000000303033330000000030303030000000003030303000000000ccccccccccccccccccccccccccccccccccc8ccc8ccc8ccc8ccc8ccc8ccc8cccb333333333323332333333333332333233333333333233323333333333323332000000000000c0c0000000000000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c3333333333333333333333332222222233333333333333330000000000000000c0c0ccccc0c0ccccc0c0ccccc0c0ccccc0c0c8c8c0c0c8c8c0c0c8c8c0c0c8c800100010001000100010001000100010000000000000000000000000000000000000c0c00000c0c00000c0c00000c0c00000000000000000000000000000000000333300003333000033330000333300000000000000000000000000000000cccccccccccccccc00000c0c00000c0ccccccccccccccccc0000000000000003333303033333030333330303333303000000000000000000000000000000000ccccc0c0ccccc0c0ccccc0c0ccccc0c0ccccc0c0ccccc0c0ccccc0c0ccccc0c3333333333333030333333333333303033333333000000003333333300000000c0c4c0c4c0c4c0c4c0c4c0c4c0c4c0c4c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0303030300000303030303030000030303030303000002020303030300000202
|0,4=>0xccccccccccccc0c0ccccccccccccc0c0ccccccccccccc0c0ccccccccccccc0c030303030202020203030303020202020303030302020202030303030202020200000000ccccc0c000000000ccccc0c000000000ccccc0c000000000ccccc0c11111111111111111111111111111111111111110000000011111111000000000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c000000000000000000000000000000000000000000000003333333333330000333333333333000000000000000000000000000000000000c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8cb333333300003333333333330000333333333333000000003333333300000000cccccccccccccccc0000cccc0000cccccccccccccccccccc0000000000000000000333300003333000033330000333300003030000030300000303000003030ccccccccc8c8c8c8ccccccccc8c8c8c8ccccccccc8c8c8c8ccccccccc8c8c8cb3333333333333331111111111111111333333333333333300000000000000000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c00000c0c00000c0c00000c0c00003030303030203020303030303020302030303030302030203030303030203020000000044444444000000004444444400000000000000000000000000000003333333333333333000000001111111133333333333333330000000000000000cccc0000cccc0c0ccccc0000cccc0c0ccccc0000cccc0000cccc0000cccc00033333333333333333333303033333030333333333333333300000000000000000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c080c080c080c080c080c080c080c08000000033333333000000003333333300000000333330300000000033333030ccccccc0ccccccc0ccccccc0ccccccc0cc00cc00cc00cc00cc00cc00cc00cc00033003300330033000000000033003300330033003300330000000000000000ccc8ccc8ccc8ccc8ccc8ccc8ccc8ccc8cc00cc00cc00cc00cc00cc00cc00cc03131313131313131313131313131313130303030303030303030303030303030c4c4c4c400000000c4c4c4c400000000c0c0c0c000000000c0c0c0c000000000033003300330033000300030003000300330033003300330000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x30200040603021c240a06030b09040a030f0223000d0603020b220a06030200210412080b20100a0603080b040a030f02001f0d06030200041e030f1d02000d030f081c100a06030200190a16030f150b1006110f02001006030f000e0d0302000c040302010b0a060300090406030800040602000704060305000403020100
|1=>0x2000b0d06030f310b100a06120b092b100a060f02002b0d0312081c0b100a06123002002b0d13030f080b100a2a06030f02000d06030f021c0d0a06030f022f100a06030f2e020b0a06030200040a0602002b040a060f022d2c0a0602002b042a060302000429060302000406030228040a060f0200070d0612020027102606
|2=>0x26030f021c100a06030f0b3f100a06030f0b3c100a0612150b3b100a030f02000c100a061202002b103706390f020b100a061202002b0d380612020b200d0a260312350b1006030f3402280a030f020b1f100a060f023332100a12020b2b0c100a06030f0009100a030f020b1f0d0a031202000b1f0d0603020b040a1e03121d
|3=>0x24f100a06030f02001b0a0612020b3b1b0a260603020b040a030f34020b1f0a06030f02004e0d060f02002b0d0a06030f4d0b100a0612020b2b1b0a06030f02000d1a030f02230b0d0a03120223000b0d064c4b12020b10260312480b100647120200100603020b46450a0612020b42100a03020b1f0d410a06030f400b100a
|4=>0xa1202230b2b100a060355020b1018030f230b100a1a06030f0200101816030f020b100a060f3402002b0a290603020b040a26030f020b1014061202000b070d030f3402230b0a030f1d0200100a121d020b2b100a064c1202541006030f0253100a060f025251100a0603020b240a0302230b0d410a060f020b50100a06030f
|5=>0x21c20100a0603020b240a1e031202000b0c0d061202002b0d5e2606030f02000d125d020b2b100a06031202005c100603020004060f020b5b100a06030f0244100a5a06030f020010060f025932100a06030f020b460a06030f0258100a030f022300100a06030f021c250a570312080b100a2926030f150b1006030f025610
|6=>0x312020b103706550f020b32100a06030f020b100a6806030f150b100a1a260612020b2b100a060312020b650a06030f020b1b0a620312020b100a290603020b0d410a0603170f150b100a030f1502230b100a06030f61020b100a2906030f02000d06030f5f022d0a06120b602b100a060f5f020b2c0a060f020007100a060f
|7=>0x30f02000d031202000b0c100a0603123002000d2926030f020b100a0603120b090d0a061202002b100a5e2606030f0200100a06030f020b250a1e06036d0f020b100a060f020b32100a06030f021c100a060312000b09100a064c0312020b1b0a6c06030f020b100a0603126b0b100a060312020b6a0a061269020b2b100a26
|8=>0xb20100a2606030f15020b10064712020b100a4c0312020b1f100a0312020b0c100a06030f020b74100a0612020b2b73100a030f020b1f100a260312021c0b100a0603720f020b100a06030f0228100a1a0603123a02000b0d06710312150b100a06570312020b250a2906030f34020b0a0603120b09100a0312026e0b100a06
|9=>0xb7c100a06031202000b1b0a2a0612020b2b100a2906030f0200100a064c12020b104a060312350b100a06031202000b4e0d7a0312020b100a061202000b2b0d0a780312020b100a7706030f020b100a0603120b75100a290612020b2b100a0603120200103706031202000d3806030f020b0d0a1a06031202000b0d1a061202
|10=>0x20b1b800a06030f02000d0a031230230b100a060f02002b100a13060355020b100a06123002002b100a2a06030f0200100a4c031202230b100a490312080b100a0603020b0d410a1a0612020b2b0d0a1306030f0200100a064c03127f0b100a06710312020b0d0a0312020b7e100a030f02230b100a06030f0252100a060312
|11=>0xb100a060312021c0b250a13060317020b100a060385020b100a0612020b2b100a1a260312020b104a06030f020b100a4306030f020b100a1803121d020b100a061202002b100a382606030f0b09100a0603020b25840a1e06030f34020b0a1a060383020b100a06030f020b101a1e031202810b100a03121d02000b100a0603
|12=>0xd060312020b880a06030f020b87100a0603020b040a06030f0259100a06030f020b1f100a2606030f020b101a06031202440b100a0603550f0259100a06030f02004e100a5a06030f020b100a4c0312020b86100a031202230b0d0a06030f3402000a06030f0200100a1a0612020b3b100a1a0612020b2b4e100a0312022300
|13=>0x30f34020b0a2906030f020b0d0a2906031202000b0d0312230b100a1a06030f020b8c100a06030f0252100a3d0612020b07100a06031202280b0d0a06030f5f020b0a260603020b0d410a061202000b07100a0612021c0b20100a0603120254100a060312020b8a0a06890312020b100a2606030f020b0d0a2606031202000b
|14=>0x1a064c0312020b0d0a29060312150b100a26060312020b0d0a060312020b09100a0603121502000b100a06030f020b0d0a06031202000b0d0603550f020b100a06031230020b0d0a064c0312020b8d100a060355020b100a3d061202000b2b0d060312020b460a06030f0200100a3d7006030f020b100a29260312150b102606
|15=>0x49060312020b0d0a7d064c0312020b100a0603170f020b100a064c12020b100a66060312020b910a662906031202000b100a031215020b1f100a060312020b90100a49064c12020b100a0603020b0d410a8f060312020b100a060312020b100a37060312020b0d0a380603120b09100a060312020b8e0a3806031202280b100a
|16=>0x60312020b8d100a06630312150b100a060312020b910a06031202000b0d0a70060312020b100a94060312020b100a06031215020b101e061202000b2b100a064c0312020b100a1a06031293020b100a060312020b0d0a662a06031202000b100a06030f34020b0a92060312020b100a06030f020b100a1a29060312020b0d0a
|17=>0x100a38060312020b96100a06031202000b100a1a06031282020b100a060312020b0d950a060312020b250a1e06030f0200100a060312300200100a060312020b100a8b060312150b100a1a060312020b1b0a0612020b2b100a03121502230b100a060312020b100a6406710312020b100a060312020b8e0a2a060312020b100a
|18=>0x1a1e2606030f020b100a060312020b97100a031202230b100a49066312020b100a06030f020b100a3d36260312020b100a060312020b4e100a060312020b100a6777060312020b100a06031202000b4e100a060312020b0d0a1a7d060312020b100a360603123002100a2606031215020b1006710312020b100a1a0603120200
|19=>0xa6629060312020b100a49060312020b100a060312020b100a38064c0312020b100a26060312020b100a06030f020b100a06031230020b100a29064c0312020b100a99060312020b100a2906030f020b100a06031202280b100a060312020b0d38060312020b100a43060312020b98100a26064c0312020b100a060312020b10
|20=>0x60312020b100a060312020b100a1a060312020b0d0a06031202000b100a060312020b10
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>4
|4,0=>0x1d50185013500e500950045
|5,0=>0xab60a560a0509a6094608e60886082607c60766070606a6064605e60586052604c60466040603a6034602e602860226
|6,0=>0x263725c7255724e7247724072397232722b7225621e72177211620a720371fc71f571ee71e771e071d971d271cb71c471bd71b671af71a871a2619c6195718e7187718071797172716b7164715d7156714f71487141713b6134712d7126711f71187111710a710370fc70f570ee70e860e170da70d370cc70c570be70b770b16
|6,1=>0x31e731773107309730272fb72f472ed72e672df72d872d172cc52c572be72b772b072a972a2729b7294728d7286727f72787271726a7
|7,0=>0x50374fc74f484ec84e484dd74d674ce84c774bf84b874b084a974a1849a7493748b8483847c7474846d7465845e7456844e8447743f8437842f8427841f8417840f8408740173fb63f383ec73e483dd73d583cd83c583bd83b673af73a7839f8397839073897381837a7372836a8362835a8353734c7345733d8335832d83258
|7,1=>0x6ea86e376db86d386cc76c486bd76b586ad86a5869e7697768f8687867f86787670866a6663765b8653864b8643863b8633862b8624761d7615860d860585fd85f585ed85e675de85d775cf85c785c075b885b085a885a085997591858a7582857b7574756d7566755e8556854e8546853f753785307528852085188511750a7
|7,2=>0x7278720771977118709870276fa86f28
|8,0=>0x926891e8916890e890598fd88f588ec98e488dc88d488cd78c588bd88b588ae78a7789f8897888f8888788088788870886978618859885188498841883898308828881f981878108808880087f887ef97e787df87d787ce97c687be87b687af77a7879f879787907788877f9777876f8767875f8756974f774877408738872f9
|8,1=>0x9be99b689ae89a6899f7997898f8986997e8976896e8967795f8957894f8947893f8937892e9
|9,0=>0xa158a0e7a0689fe89f689ee89e689de89d689cf79c78
|10,0=>0xa1d7
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 154 then fld (dictB (i / 512) (i / 32 % 16)) 254 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 8 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 16 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))

def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 9 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
|0=>0xb0a40898060f4482d060a44029120b418010b0a440290b1e4482d060a83c6a020a83c34100a4482d0b0a43c34100a4482d0b0a40c020f0d04029120b42c290f0d04029120b418010b0a42c290f0d04029120b42c690f0d04029120b4082a0b1e43c94101e4482d060a83c34100a4482d0b0a43c6c101a4082a020a41861170a03c09120b40c51130a02c290f064482d
|1=>0x3a0600801030a42d29490a00c19035282cf50f0a8482d0f2504079120b4182a0b0a44069120b4082a0f0d04029120b44029120b42c29100a4482d0b0a41829024a52428030642c2903374d828060b40d120b434186a023e818f50f0a8482d3a06c0801031845c280f024482d03008182902374d828060b43c43020a8980b060a43c34100a4482d060a84029120b40c02
|2=>0x120b408f50f0a8482d120b42c29100a57c2f120b4482d020042c290b1e4482d060a83c94101e4482d060a840290f0d04029120b42c29120b42d0d061a8082a130ac0d56150fc08291506008290b1e44079120b4182a020a4482d060a45c000b0a43c09120b45c280b0a43c09120b41861170a03c09120b40c020f10c482d0b0a43c34100a4482d130a0183d120b41829
|3=>0x60a4980b100a41829030082c29120b41829101e4482d060a8543d120b40829035583c29120b42c79120b4182a2602c1829101a4082a290f41809120b4092b490a00c1910374d828060b40c020b0a41829360a0182d035583c29120b43c6a120b4082a021a4482d020a80c020b0a4419d026680c2a101a4482d020a81991630a00c09120d84029020f4482d020a45418
|4=>0x276818e10b0a80c020b0a42c29360a0182d0b0a440290b0a84029120b4082a100a4082a031c82c79060a80829120b4182903374d828060b4541b020a4e81b150b40829260fc482d060a40c020b0a4541b120b408290f1a4482d020a82c69120b4082a100a408010b0a43c43120b5c00b2602418296f0600999030a84029120b42c293a06c0801100a4082d0b0a4482d
|5=>0xb0a43c290f064482d030082c29120b418010b0a45418030a4082902260180d060a44836100a44029030082c290b0a43c19120b5f4084c0640c296f06c0999030a85418120b408290b3d43c2a120b5f40b260341829101a4082a0b0a42c2906024482d030a524280306408dd360a0182d100a418020b0a419ef300a0082d100a40c020b0a5e418150340829120b4082a
|6=>0xb1a4082a0b0a45418020a440790b1e4182a060f43c09120b44991630a00c0903008082a0b0a52428060341829061a8482d020a85c280f024482d3a060542d020a42c2a030082c292602c482d060a44896101e4182a0f10c482d020a849ed300a0082d060a8482d020a81a08023842c2a3a06008010b0a4486e101a4082a100a4482d0b0a4082d150600829120b40c02
|7=>0x150b408290b1a44029020a8d0290f10c482d120d840293a03c08010b0a42c79060a82d29490a00c19108b4d82a060b40d0d061a84029120b42c29100a41829106458c28030243c34100a4482d550bc3c29120b41829120b4082a0b434186a020a9542f0f0a4482d120b418020b0a44c2b0f064482d7906d3009150604029020a43c43120b42c290b0a4482d020a80ca2
|8=>0x6304082d360a0182d100a42c2a2602c1829103842c2a0b1a4082a100a40c29020640829100a418292602c18290b0a40829100a4482d100a42c290f0a4482d100a4082d4c02c0c290f3d43c2a120b44029030082c2910434186a020a82c290f0a8482d060a40819020a43c43120b44029120b42c29100a4180906150082a020a4084e0f064482d0b3d43c2a120b4e80f
|9=>0x30082c29150600829630a00c09031a4082a103842c2a260b418294c02c0c29020340829106640c2a100a42c29260241829490ac0c19060a80829030082c29030a4082a300ac082d100a40c2a060042c290f10c482d066640c2a120b4082a100a41809100a40c194c0640c290f024482d036640c2a106640c2a060242c291506c08291503c0829030640c29120d84029
|10=>0xb1a4082a100a42c2a061a8082a02368182d030a41829060a8082a120b418296306c0c09150600829030240c190f0a8482d060b41829060082c29026680c2a061a4082a060082c29100a4082a260341829060b4082d020a41829031a4082a0b0a82c29260bc1829020a82c29023842c2a020d84029101e4182a120b42c29020b42c29360a8182d020a80829101a4082a
|11=>0x82a100a42c29030a81809030642c2a030a41829120b4082d060240c29490240c1906024482d
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0xa5000009141f506d016500000000000115000000000000d4000000000000000000000028c0550014000
|6,0=>0x23d08b421d0843201000000007e200007a400007641c9000000000001b900001acc0001a0c65300000000000000000000018505d400005a3000000000000001590000150800014104f100004b41248000000000011c80000000434000000000003f400000000ed03740cd031200002d4
|6,1=>0xb932dc80000000b432c4cad40000ac100000000000a840000a4428c4a210000a0227889a4000097324d00000000000
|7,0=>0x574d5a355cc000550d513538d4b3520d453508d4024f4d3b24e0d3534c8d3024b4d2a349cd252488d1f347491a30001173450d113000000043c90c3424d06341090133fc8fc33ec4f833d4cf233bccec33a88e82394ce2337ccdd2368cd73350cd1333c8cc3324cc633108c132fc8bc3
|7,1=>0x828e073810e0137f8dfb37e0df627ccdf127b8deb37a49e72790de130001de376cc000760dd53748dcf3730dca271cdc43704dbe30001bb36e0db536c8daf36b0da93698da33680d9d3668d973650d913638d8b3620d853608d7f35f0d7a25dcd7435c4d6f25b0d693598c00058cd603
|7,2=>0x874e1a385ce143000211383ca0d2
|8,0=>0xa78a9c2a68a982a58a942a48a902a38a8c2a28a882a18a842a08a8029f8a7c29e8a7829d8a7429c8a7029b8a6c29a8a682998a642988a602978a5c2968a582958a542948a502938a4c2928a482918a442908a4028f8a3c28e8a3828d8a3428c8a3028b8a2c28a8a282898a242888a202
|8,1=>0x2c42b08ac02af8abc2ae8ab82ad8ab42ac8ab02ab8aac2aa8aa82a98aa42a88aa02
|9,0=>0x2d01b3c6ce1b346cc1b2c6ca1b246c81b1c6c61
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 18 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 255), wireSAt ((code >>> 10) &&& 255)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 14 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmPalB : Nat → Nat
|0=>0x2a400000009c000000026c0000000980000000248000000090000000023000000008a00000002240000000850000000210000000082000000020400000008000000001dc00000006100000000e0000000028000000008000000001c00000000500000000120000000044000000010000000003800000000c000000002800000000900000000180000000040000000008000000000
|1=>0x13b40000004e100000013800000004dc00000013240000004c50000001304000000484000000120800000048000000010800000004000000000afc0000002be0000000af40000002b70000000ab400000029f0000000a680000002890000000a040000002300000000870000000218000000080000000018d00000004240000000ff00000003b40000000e900000002fc0000000bb
|2=>0x80008800020000e00008000280001004ff00004003000000864ff00002183b40000840ed00001182fc000040085000008027c0000200060000040044000010000000002131800000848800000202000000064ff00000183fc0000060e900000182fc00000400000000093fc0000020a900000082240000020810000008180000002020000000806000000100000000020100000004ff
|3=>0x4900afc0012072bf0004818afc0012032bf000480c8140012022bf0004800afc0012002ad0004800a340012000bf0004000aec0010002b70004000a7c00100029300040002c000100009c000400024c00100001c0004000020000a2000e0002800088000a0000a00020008700008001bf000200005000040001800010000400002100b300008006fc00020009b000080022c000200085
|4=>0x1808006fc0602000bf0140000a7c044a001bf01009102fc0402000bf0100118aec0400062bf010001887c0400002bf00908006fc0240001af00828000880200000b7004400027001000009400240002ec0088003bb0020010aec0080002bf00200008c000800021c00200003fc00800001000108806fc00420019f001008063c0020004900006800aec0016000bb00049182fc0012442bf
|5=>0x20202001bf40001182fc95402009e2240000afc8002201bf1700000afc5640000bf1202000afc4010000b00804910afc1810000930600000afc1440201bf0424000a4c1082001bf04148002ec1040003bb0410000afc10400021304048002fc0d00002bf0220000afc088000293022000004c0808002bb02020002fc08000029f
|_=>0
def pmB : Nat → Nat → Nat
|5,0=>0xd001003080c000000030000000800000000000002121200
|6,0=>0x84a00000d0d05004100000011000b343400020203000a120000003612440812000002005300352300000015000100010d000000002700260b000800000000120002001242002502000000020000050000004500004f0307020024
|7,0=>0x286f1a3a2c6e58010f0d644708016a1600243e000a0b3a03500d7259901a0029031b321a941c3c2e040a14432d0a73294649a0223708542a636548515f002f213f6019520b92615d2c0e30012c08557b666d1d0a620d2c36011f00381e670000082b745a0697882b060318383b21060d84601708853d360901564c31085b0812
|7,1=>0x3948133a00a30108
|8,0=>0x8bac89767e8fae6b6f24b533b440869a76ab5e8295b8a871776891799975249d87b08120a2b3767d8796af807a8e9fad20b2b7b16c4d79248d9b935c78808aa2a19eb9a5b67ca97a707fa483aa694e4b40982a
|9,0=>0xa75721798cba79219c24a6
|10,0=>0x21
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 8 (j % 128); fld (pmPalB (k / 32)) 38 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_245,9,runOps true dom_245 (0,roots_245) ops)] else [])++(if pm.testBit 1 then [(dom_221,8,runOps true dom_221 (0,roots_221) ops)] else [])++(if pm.testBit 2 then [(dom_236,7,runOps true dom_236 (0,roots_236) ops)] else [])++(if pm.testBit 3 then [(dom_252,8,runOps true dom_252 (0,roots_252) ops)] else [])++(if pm.testBit 4 then [(dom_249,8,runOps true dom_249 (0,roots_249) ops)] else [])++(if pm.testBit 5 then [(dom_237,8,runOps true dom_237 (0,roots_237) ops)] else [])++(if pm.testBit 6 then [(dom_180,5,runOps true dom_180 (0,roots_180) ops)] else [])++(if pm.testBit 7 then [(dom_189,9,runOps true dom_189 (0,roots_189) ops)] else [])++(if pm.testBit 8 then [(dzo_221_32,6,runOps true dzo_221_32 (0,roots_221) ops)] else [])++(if pm.testBit 9 then [(dzo_121_4,5,runOps true dzo_121_4 (0,roots_121) ops)] else [])++(if pm.testBit 10 then [(dzo_180_64,5,runOps true dzo_180_64 (0,roots_180) ops)] else [])++(if pm.testBit 11 then [(dom_172,5,runOps true dom_172 (0,roots_172) ops)] else [])++(if pm.testBit 12 then [(dom_188,6,runOps true dom_188 (0,roots_188) ops)] else [])++(if pm.testBit 13 then [(dzo_188_64,6,runOps true dzo_188_64 (0,roots_188) ops)] else [])++(if pm.testBit 14 then [(dzo_189_64,7,runOps true dzo_189_64 (0,roots_189) ops)] else [])++(if pm.testBit 15 then [(dom_213,6,runOps true dom_213 (0,roots_213) ops)] else [])++(if pm.testBit 16 then [(dom_204,4,runOps true dom_204 (0,roots_204) ops)] else [])++(if pm.testBit 17 then [(dom_220,5,runOps true dom_220 (0,roots_220) ops)] else [])++(if pm.testBit 18 then [(dzo_173_64,6,runOps true dzo_173_64 (0,roots_173) ops)] else [])++(if pm.testBit 19 then [(dom_181,8,runOps true dom_181 (0,roots_181) ops)] else [])++(if pm.testBit 20 then [(dom_241,6,runOps true dom_241 (0,roots_241) ops)] else [])++(if pm.testBit 21 then [(dzo_93_32,5,runOps true dzo_93_32 (0,roots_93) ops)] else [])++(if pm.testBit 22 then [(dom_185,6,runOps true dom_185 (0,roots_185) ops)] else [])++(if pm.testBit 23 then [(dom_89,4,runOps true dom_89 (0,roots_89) ops)] else [])++(if pm.testBit 24 then [(dom_125,6,runOps true dom_125 (0,roots_125) ops)] else [])++(if pm.testBit 25 then [(dom_209,5,runOps true dom_209 (0,roots_209) ops)] else [])++(if pm.testBit 26 then [(dzo_217_32,5,runOps true dzo_217_32 (0,roots_217) ops)] else [])++(if pm.testBit 27 then [(dom_217,6,runOps true dom_217 (0,roots_217) ops)] else [])++(if pm.testBit 28 then [(dom_248,5,runOps true dom_248 (0,roots_248) ops)] else [])++(if pm.testBit 29 then [(dom_205,5,runOps true dom_205 (0,roots_205) ops)] else [])++(if pm.testBit 30 then [(dzo_89_4,4,runOps true dzo_89_4 (0,roots_89) ops)] else [])++(if pm.testBit 31 then [(dzo_249_4,6,runOps true dzo_249_4 (0,roots_249) ops)] else [])++(if pm.testBit 32 then [(dzo_217_4,5,runOps true dzo_217_4 (0,roots_217) ops)] else [])++(if pm.testBit 33 then [(dom_173,6,runOps true dom_173 (0,roots_173) ops)] else [])++(if pm.testBit 34 then [(dom_233,5,runOps true dom_233 (0,roots_233) ops)] else [])++(if pm.testBit 35 then [(dom_216,4,runOps true dom_216 (0,roots_216) ops)] else [])++(if pm.testBit 36 then [(dzo_181_64,6,runOps true dzo_181_64 (0,roots_181) ops)] else [])++(if pm.testBit 37 then [(dzo_89_32,4,runOps true dzo_89_32 (0,roots_89) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_253 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · exact cpcs (by decide +kernel) lowS_237 _ g hchk
    · exact cpcs (by decide +kernel) lowS_180 _ g hchk
    · exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_221_32_89 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_121_4_89 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_180_64_180 _ g hchk
    · exact cpcs (by decide +kernel) lowS_172 _ g hchk
    · exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_188_64_180 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_189_64_180 _ g hchk
    · exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · exact cpcs (by decide +kernel) lowS_204 _ g hchk
    · exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_173_64_164 _ g hchk
    · exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · exact cpcs (by decide +kernel) lowS_241 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_93_32_89 _ g hchk
    · exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · exact cpcs (by decide +kernel) lowS_125 _ g hchk
    · exact cpcs (by decide +kernel) lowS_209 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_217_32_89 _ g hchk
    · exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_89_4_89 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_249_4_89 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_217_4_89 _ g hchk
    · exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · exact cpcs (by decide +kernel) lowS_216 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_181_64_180 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_89_32_89 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_245 9 s (0, roots_245) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_253 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_245 h

def symsG : List (List (Nat × Nat)) := [[(rowMask36, 28)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_253 == dom_253) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_253 goalM v ys) : RunD true dom_253 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_253 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 6 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 6 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 24 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 24 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 91 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 91 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 136 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 136 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8 : ∀ i, 0 ≤ i → i < 83 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 83 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9 : ∀ i, 0 ≤ i → i < 11 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 11 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 10) : ∀ i < NN s, bar true dom_253 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
  · exact z8 i (Nat.zero_le i) hi
  · exact z9 i (Nat.zero_le i) hi
  · exact z10 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_253 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 6 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 10) (h : RunD true dom_253 goalM s xsM) : False := by
  have hmin : 6 ≤ s := by
    have hl := run_len h; change 7 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_253 roots_253 goal_253 11 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_253

theorem lowS_253 : Lower true dom_253 roots_253 goal_253 11 := S_253.noCircuit

end B0

namespace B3
def dom_51 : Nat := 0xf000f000f000f

def goal_51 : Nat := rowMask267

def roots_51 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_99 : Nat := 0xf0000000f0000000f0000000f

def goal_99 : Nat := 0xeeeeeeeecccccccceeeeeeee00000000eeeeeeeecccccccceeeeeeee00000000

def roots_99 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_102 : Nat := 0x55000000550000005500000055

def goal_102 : Nat := rowMask268

def roots_102 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_103 : Nat := 0xff000000ff000000ff000000ff

def goal_103 : Nat := 0xfefefefefcfcfcfceeeeeeee00000000fefefefefcfcfcfceeeeeeee00000000

def roots_103 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f

def goal_115 : Nat := 0xeeeeeeeeeeeecccceeeeeeeeaaaa0000eeeeeeeeeeeecccceeeeeeeeaaaa0000

def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff

def goal_119 : Nat := 0xfefefefefefefcfceeeeeeeeaaaa0000fefefefefefefcfceeeeeeeeaaaa0000

def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_145 : Nat := 0x3000300000000000000000000000000030003

def goal_145 : Nat := rowMask262

def roots_145 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_149 : Nat := rowMask298

def goal_149 : Nat := rowMask263

def roots_149 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_167 : Nat := 0xff000000ff0000000000000000000000ff000000ff

def goal_167 : Nat := 0xfffffffffafafafafffffffffafafafaeeeeeeee00000000eeeeeeee00000000

def roots_167 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_178 : Nat := rowMask320

def goal_178 : Nat := 0xffffffffffff0000ffffffffffff0000cccccccc00000000cccccccc00000000

def roots_178 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_179 : Nat := rowMask274

def goal_179 : Nat := 0xffffffffffffaaaaffffffffffffaaaaeeeeeeeeaaaa0000eeeeeeeeaaaa0000

def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_181 : Nat := rowMask260

def goal_181 : Nat := 0xfffffffffffffafafffffffffffffafaaaaaaaaaaaaa0000aaaaaaaaaaaa0000

def roots_181 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_182 : Nat := 0x5500550055005500000000000000000055005500550055

def goal_182 : Nat := 0xfffffffffffff0f0fffffffffffff0f0cccccccc00000000cccccccc00000000

def roots_182 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := rowMask259

def goal_183 : Nat := 0xfffffffffffffafafffffffffffffafaeeeeeeeeaaaa0000eeeeeeeeaaaa0000

def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_210 : Nat := rowMask299

def goal_210 : Nat := 0xffffffffffffffffffff0000ffff0000cccccccccccccccc0000000000000000

def roots_210 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := rowMask205

def goal_211 : Nat := 0xffffffffffffffffffffaaaaffffaaaaeeeecccceeeeccccaaaa0000aaaa0000

def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := rowMask187

def goal_215 : Nat := 0xfffffffffffffffffffffafafffffafafefefcfcfefefcfcaaaa0000aaaa0000

def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_225 : Nat := rowMask289

def goal_225 : Nat := 0xffffffffffffffffffffffffaaaaaaaaaaaaaaaa00000000aaaaaaaa00000000

def roots_225 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f

def goal_227 : Nat := 0xffffffffffffffffffffffffaaaaaaaaeeeeeeeecccccccceeeeeeee00000000

def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := rowMask230

def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := rowMask231

def goal_231 : Nat := 0xfffffffffffffffffffffffffafafafafefefefefcfcfcfceeeeeeee00000000

def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_241 : Nat := rowMask221

def goal_241 : Nat := 0xffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa0000aaaaaaaaaaaa0000

def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := rowMask280

def goal_242 : Nat := 0xffffffffffffffffffffffffffff0000cccccccccccccccccccccccc00000000

def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := rowMask176

def goal_243 : Nat := 0xffffffffffffffffffffffffffffaaaaeeeeeeeeeeeecccceeeeeeeeaaaa0000

def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_244 : Nat := rowMask218

def goal_244 : Nat := 0xfffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f00000000000000000

def roots_244 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := rowMask87

def goal_245 : Nat := 0xfffffffffffffffffffffffffffffafafafafafafafaf0f0aaaaaaaaaaaa0000

def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := rowMask217

def goal_246 : Nat := 0xfffffffffffffffffffffffffffff0f0fcfcfcfcfcfcfcfccccccccc00000000

def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := rowMask155

def goal_247 : Nat := 0xfffffffffffffffffffffffffffffafafefefefefefefcfceeeeeeeeaaaa0000

def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

theorem lowS_145 : Lower true dom_145 roots_145 goal_145 4 := lower_iso (d1 := B5.dom_145) (roots1 := B5.roots_145) (T1 := B5.goal_145) [] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_145

theorem lowS_51 : Lower true dom_51 roots_51 goal_51 4 := lower_iso (d1 := B5.dom_85) (roots1 := B5.roots_85) (T1 := B5.goal_85) [(rowMask16, 2), (rowMask26, 32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_85

theorem lowS_149 : Lower true dom_149 roots_149 goal_149 5 := lower_iso (d1 := B5.dom_147) (roots1 := B5.roots_147) (T1 := B5.goal_147) [(rowMask16, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_147

theorem lowS_99 : Lower true dom_99 roots_99 goal_99 4 := lower_iso (d1 := B5.dom_85) (roots1 := B5.roots_85) (T1 := B5.goal_85) [(rowMask10, 3), (rowMask0, 1), (rowMask25, 16), (rowMask34, 48)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_85

theorem lowS_102 : Lower true dom_102 roots_102 goal_102 4 := lower_iso (d1 := B5.dom_85) (roots1 := B5.roots_85) (T1 := B5.goal_85) [(rowMask0, 1), (rowMask25, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_85

theorem lowS_178 : Lower true dom_178 roots_178 goal_178 4 := lower_iso (d1 := B5.dom_85) (roots1 := B5.roots_85) (T1 := B5.goal_85) [(rowMask0, 1), (rowMask10, 3), (rowMask27, 7), (rowMask33, 31), (rowMask32, 63), (rowMask44, 127)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_85

theorem lowS_210 : Lower true dom_210 roots_210 goal_210 4 := lower_iso (d1 := B5.dom_85) (roots1 := B5.roots_85) (T1 := B5.goal_85) [(rowMask0, 1), (rowMask10, 3), (rowMask27, 7), (rowMask33, 31), (rowMask44, 127)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_85

theorem lowS_225 : Lower true dom_225 roots_225 goal_225 5 := lower_iso (d1 := B5.dom_147) (roots1 := B5.roots_147) (T1 := B5.goal_147) [(rowMask16, 2), (rowMask11, 6), (rowMask28, 30), (rowMask34, 48), (rowMask37, 14)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_147

theorem lowS_103 : Lower true dom_103 roots_103 goal_103 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaa000000aa000000aa000000aa, 32, 33)] (by decide +kernel) (by decide +kernel) lowS_102

theorem lowS_167 : Lower true dom_167 roots_167 goal_167 6 := lower_iso (d1 := B2.dom_117) (roots1 := B2.roots_117) (T1 := B2.goal_117) [(rowMask35, 15), (rowMask16, 2), (rowMask28, 30), (rowMask11, 6), (rowMask27, 7), (rowMask32, 63), (rowMask44, 127)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B2.lowS_117

theorem lowS_179 : Lower true dom_179 roots_179 goal_179 7 := lower_iso (d1 := B6.dom_181) (roots1 := B6.roots_181) (T1 := B6.goal_181) [(rowMask33, 31), (rowMask37, 14), (rowMask16, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B6.lowS_181

theorem lowS_181 : Lower true dom_181 roots_181 goal_181 6 := lower_iso (d1 := B5.dom_199) (roots1 := B5.roots_199) (T1 := B5.goal_199) [(rowMask32, 63), (rowMask11, 6), (rowMask16, 2), (rowMask22, 12), (rowMask10, 3), (rowMask36, 28)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_199

theorem lowS_211 : Lower true dom_211 roots_211 goal_211 7 := lower_iso (d1 := B6.dom_117) (roots1 := B6.roots_117) (T1 := B6.goal_117) [(rowMask35, 15), (rowMask16, 2), (rowMask32, 63), (rowMask49, 96), (rowMask33, 31)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B6.lowS_117

theorem lowS_227 : Lower true dom_227 roots_227 goal_227 6 := lower_iso (d1 := B2.dom_115) (roots1 := B2.roots_115) (T1 := B2.goal_115) [(rowMask35, 15), (rowMask44, 127), (rowMask26, 32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B2.lowS_115

def isoMvS_115 : List (Nat × Nat) := [(rowMask26, 32), (rowMask25, 16), (rowMask39, 8), (rowMask29, 4), (rowMask144, 62), (rowMask33, 31)]

theorem lowS_115 : Lower true dom_115 roots_115 goal_115 5 :=
  lower_iso isoMvS_115 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_103

theorem lowS_182 : Lower true dom_182 roots_182 goal_182 5 := lower_iso (d1 := B2.dom_118) (roots1 := B2.roots_118) (T1 := B2.goal_118) [(rowMask28, 30), (rowMask51, 64)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B2.lowS_118

theorem lowS_241 : Lower true dom_241 roots_241 goal_241 6 := lower_iso (d1 := B5.dom_199) (roots1 := B5.roots_199) (T1 := B5.goal_199) [(rowMask32, 63), (rowMask11, 6), (rowMask22, 12), (rowMask28, 30), (rowMask10, 3), (rowMask16, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_199

theorem lowS_242 : Lower true dom_242 roots_242 goal_242 5 := lower_iso (d1 := B2.dom_103) (roots1 := B2.roots_103) (T1 := B2.goal_103) [(rowMask27, 7), (rowMask28, 30), (rowMask22, 12), (rowMask44, 127), (rowMask0, 1), (rowMask144, 62)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B2.lowS_103

theorem lowS_244 : Lower true dom_244 roots_244 goal_244 6 := lower_iso (d1 := B5.dom_151) (roots1 := B5.roots_151) (T1 := B5.goal_151) [(rowMask27, 7), (rowMask28, 30), (rowMask10, 3), (rowMask316, 60), (rowMask37, 14), (rowMask22, 12)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_151

def dzo_115_4:=0xf000f000f000f000f000f000f000f0

def gzo_115_4:=0xf000f000f000f000e000e000a00000

def gsh_115_4:=0xf000f000f000f000e000e000a0000

theorem lowS_zo_115_4_51:Lower true dzo_115_4 roots_115 gzo_115_4 5:=lower_iso (d1:=dom_115) (roots1:=roots_115) (T1:=gsh_115_4) [(dom_115,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_115_4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xf000f000f000f0000000000000000,0,64)] (by decide +kernel) (by decide +kernel) lowS_51)

def dzo_103_16:=0xff000000ff000000ff000000ff0000

def gzo_103_16:=0xfe000000fe000000ee000000aa0000

def gsh_103_16:=0xfe000000fe000000ee000000aa

theorem lowS_zo_103_16_102:Lower true dzo_103_16 roots_103 gzo_103_16 5:=lower_iso (d1:=dom_103) (roots1:=roots_103) (T1:=gsh_103_16) [(dom_103,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_103_16) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xaa000000aa000000aa000000aa,0,1)] (by decide +kernel) (by decide +kernel) lowS_102)

namespace S_119
def pairsG : List (Nat × Nat) := [(1,17), (1,33), (2,34), (2,66), (3,19), (3,35), (3,67), (4,68), (5,21), (5,37), (5,69), (6,38), (6,70), (7,23), (7,39), (7,71), (16,17), (18,19), (18,50), (18,82), (20,21), (20,84), (22,23), (22,54), (22,86), (32,33), (32,34), (36,37), (36,38), (36,100), (48,49), (48,50), (52,53), (52,54), (52,116), (64,66), (64,68), (65,67), (65,69), (65,81), (65,97), (80,81), (80,82), (80,84), (96,97), (96,98), (96,100), (112,113), (112,114), (112,116)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3ffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_119.map (· &&& dom_119)
def goalM : Nat := goal_119 &&& dom_119
def NN : Nat → Nat
|6=>1
|_=>0
def HT : Nat → Nat → Nat
|6,0=>0x2c4d1
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xff00ff0000000000ff00ff00000000ff000000ff000000ff000000ff0000f000f000f000f000f000f000f000f0cc00cc00cc00cc00cc00cc00cc00ccaa00aa00aa00aa00aa00aa00aa00aaff00ff00ff00ff0000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x2c688
|_=>0
def stOffB : Nat → Nat → Nat
|6,0=>6
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 6 then fld (dictB (i / 512) (i / 32 % 16)) 120 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 3 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 7 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))

def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
|_=>0
def opOffB : Nat → Nat → Nat
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 8 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 7), wireSAt ((code >>> 5) &&& 7)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 5 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmPalB : Nat → Nat
|0=>0xf0
|_=>0
def pmB : Nat → Nat → Nat
|6,0=>1
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 1 (j % 128); fld (pmPalB (k / 32)) 4 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_115,5,runOps true dom_115 (0,roots_115) ops)] else [])++(if pm.testBit 1 then [(dzo_115_4,5,runOps true dzo_115_4 (0,roots_115) ops)] else [])++(if pm.testBit 2 then [(dom_103,5,runOps true dom_103 (0,roots_103) ops)] else [])++(if pm.testBit 3 then [(dzo_103_16,5,runOps true dzo_103_16 (0,roots_103) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_119 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_115_4_51 _ g hchk
    · exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_103_16_102 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_115 5 s (0, roots_115) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_119 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_115 h

def symsG : List (List (Nat × Nat)) := [[(rowMask22, 12), (rowMask28, 30), (rowMask32, 63)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_119 == dom_119) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_119 goalM v ys) : RunD true dom_119 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_119 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, bar true dom_119 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_119 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_119 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_119 roots_119 goal_119 7 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_119

theorem lowS_119 : Lower true dom_119 roots_119 goal_119 7 := S_119.noCircuit

theorem lowS_183 : Lower true dom_183 roots_183 goal_183 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(rowMask227, 128, 132)] (by decide +kernel) (by decide +kernel) lowS_179

theorem lowS_215 : Lower true dom_215 roots_215 goal_215 9 := lower_iso (d1 := B0.dom_245) (roots1 := B0.roots_245) (T1 := B0.goal_245) [(rowMask10, 3), (rowMask144, 62), (rowMask35, 15), (rowMask11, 6), (rowMask33, 31), (rowMask27, 7)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B0.lowS_245

theorem lowS_231 : Lower true dom_231 roots_231 goal_231 9 := lower_iso (d1 := B2.dom_245) (roots1 := B2.roots_245) (T1 := B2.goal_245) [(rowMask10, 3), (rowMask28, 30), (rowMask35, 15), (rowMask11, 6), (rowMask27, 7), (rowMask44, 127), (rowMask32, 63)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B2.lowS_245

def dzo_241_2:=0xc000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c

def gzo_241_2:=0xc000c000c000c000c000c000c0008000c000c000c000c000c000c00080000

def gsh_241_2:=0x3000300030003000300030003000200030003000300030003000300020000

theorem lowS_zo_241_2_145:Lower true dzo_241_2 roots_241 gzo_241_2 6:=lower_iso (d1:=dom_241) (roots1:=roots_241) (T1:=gsh_241_2) [(dom_241,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_241_2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(rowMask279,0,32),(0x3000300030003000000000000000000030003000300030000000000000000,0,64)] (by decide +kernel) (by decide +kernel) lowS_145)

namespace S_243
def pairsG : List (Nat × Nat) := [(1,17), (1,33), (1,129), (2,34), (2,66), (3,19), (3,35), (3,67), (3,131), (16,17), (16,144), (18,19), (18,50), (18,82), (18,146), (32,33), (32,34), (32,160), (48,49), (48,50), (48,176), (64,66), (64,192), (65,67), (65,81), (65,97), (65,193), (80,81), (80,82), (80,208), (96,97), (96,98), (96,224), (112,113), (112,114), (112,240), (128,129), (128,144), (128,160), (128,192), (130,131), (130,146), (130,162), (130,194)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_243.map (· &&& dom_243)
def goalM : Nat := goal_243 &&& dom_243
def NN : Nat → Nat
|4=>5
|5=>15
|6=>37
|7=>10
|8=>1
|_=>0
def HT : Nat → Nat → Nat
|4,0=>0xf9364ae3dc97bf23be3e2c4e3
|5,0=>0xfe476ccee8be064b5108b28bab065591cd5564284dc3844f463f2623bb0e1fd6418ab00b0a1
|6,0=>0xff565fa029f40a1f283dec721e6e64df79aceebfc98d7c4823bd69abd61db8111aefbda0ebf97df191cd586de47c04371895703456669b6491f6229661a155100047a38458a33f83a3acb6366e62853a282f6132a0110a40a35605184
|7,0=>0xf70868c8ad8c3516ee8b6726b5b03d545713dcd4157f605184
|8,0=>0xaa738
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf000f000f000f000a000a000a000a000f000f000f000f0000000000000000500050005000500050005000500050000000000000000000000000000000040004000400040004000400040004000c000c000c000c000c000c000c000ca0000000a0000000a0000000a0000000a000a000a000a000a000a000a000a00000000000000000000000000000000a000a000a000a000a000a000a000ac000f000c000f000c000f000c000f000c000c000c000c000c000c000c000ce000e000e000e000e000e000e000e000c000c000c000c000c000c000c000c00000000000000000000000000000000f000a000f000a000f000a000f000af000a000f000a000f000a000f000a000f000a000f000a000f000a000f000af000f000f000f000f000f000f000f000f0000000f0000000f0000000f0000f0000000f0000000f0000000f0000000a0000000a0000000a0000000a0000f000f000f000f000f000f000f000f0000000a0000000a0000000a0000000af000a000f000a000f000a000f000a000f0000000f0000000f0000000f000000000000000000000000000000000000c000c000c000c000c000c000c000ca000a000a000a000a000a000a000a00000000000000000000000000000000a000f000a000f000a000f000a000f000a000a000a000a000a000a000a000af000f000f000f000f000f000f000f000c000c000c000c000c000c000c000c0000a0000000a0000000a0000000a0000000a0000000a0000000a0000000a0000f0000000f0000000f0000000f00000000000000000000000000000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000050000000500000005000000050000000a0000000a0000000a0000000af000f00000000000f000f00000000000f000f00000000000f000f0000000050005000500050005000500050005000a000a000a000a000a000a000a000af000f000f000f000f000f000f0000000f000f000f000f000f000f000a0000f000f000f0000000f000f000f0000000f000f000a0000000f000f000a0000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a000af000f000f000f000f000f000f000f00000000000000000000000000000000f000f000a000a000f000f000a000a000f000f00000000000f000f00000000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000cf000f000f000f000f000f000f000f000a000a000a000a000a000a000a000a0000f0000000f0000000f0000000f0000000a0000000a0000000a0000000af000f000f000f0000000000000000000f000f000f000f0000000000000000
|0,1=>0xa0000000a0000000a0000000a80008000800080008000800080008000c000c000c000c000c000c000c000cd000d000d000d000d000d000d000d000c000c000c000c000c000c000c000c50000000500000005000000050000000f0000000f0000000f0000000f0000f0000000f0000000f0000000f0000000f000a000f000a000f000a000f000af000f000f000f000f000f000f000f000f000a000f000a000f000a000f000a
|_,_=>0
def stPool : Nat → Nat
|0=>0x18e00528c64600528c0c218014a60c3c600a5d60c20070c600528319400d2930c200a30324028318100529218100528308101110c0c200a0d038014a3c604014a0c23803470c218014a30308900a0c22c028324b00a0c90402070c61440c2040
|1=>0x2831950052831810052a130318014a5d60c60052a030318014a30319f14a30308044a3036c078a31d18014a4c318014a31219b00528c0d018014a58c0c21802973036c014a30319c00528c3c66c014a30308600d28c0c238014a31a18014a30f
|2=>0x28c3c600528c0c600534a30318015128c0c218014a3031a500528c90600510c0c600528308654014a0c218100528c8c60052a20c600528318e00534a31208600529830318014a30319400528c0c604014a5cc0c200528c3c218014a5cc3c6005
|3=>0xa30318014a5cc0c600528c0c66c014a30318015e28c48600528c0c638014a58c0c6005
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>0x14507a82940aa005
|5,0=>0x1a58c6c5e52c314d49ca4862130f186ea31615b09583ec196
|6,0=>0x15e7ac3549a96f4479f34e1a62f2a791bc71e2af0e783bc01df4cf4676bb99dbeed9669b33598ecc165d3acdd58ea574f3a5dd20e89741b1f1cecc6f7
|7,0=>0x344f9b7ca3e39b0ef807bd35cded8f657
|8,0=>0x1a96
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 38 then fld (dictB (i / 512) (i / 32 % 16)) 244 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 6 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 13 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))

def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 7 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
|0=>0xc19185c6160c5cc1a30543153058614185437b1858a4518506150de4616311c61418546150c54c081854c0a18540451850614185461718583471850c451850615185c63718546150cd4c160c5434518506152954c081854c451850615091c61418546152914614
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0x30493000630cc000000000c000000000000
|6,0=>0xbcad2002c1a8a82002710000000261002518ca1200000001f2749b2649720000058551504004c521408f134800
|7,0=>0xe8791e0771d8751d0731c8711
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 14 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 63), wireSAt ((code >>> 8) &&& 63)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 10 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmPalB : Nat → Nat
|0=>0xfafe9eef7bde76bca709c04cc304a022c8218051140421003b088200680e00c0200400
|_=>0
def pmB : Nat → Nat → Nat
|5,0=>0xe500c600008000042
|6,0=>0x9c846a300b0000751d01008117c671480e66a5b0a9a6e
|7,0=>0x33addf38b5f7a
|8,0=>0x15
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 5 (j % 128); fld (pmPalB (k / 32)) 10 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_211,7,runOps true dom_211 (0,roots_211) ops)] else [])++(if pm.testBit 1 then [(dom_99,4,runOps true dom_99 (0,roots_99) ops)] else [])++(if pm.testBit 2 then [(dom_210,4,runOps true dom_210 (0,roots_210) ops)] else [])++(if pm.testBit 3 then [(dom_179,7,runOps true dom_179 (0,roots_179) ops)] else [])++(if pm.testBit 4 then [(dom_225,5,runOps true dom_225 (0,roots_225) ops)] else [])++(if pm.testBit 5 then [(dom_227,6,runOps true dom_227 (0,roots_227) ops)] else [])++(if pm.testBit 6 then [(dom_115,5,runOps true dom_115 (0,roots_115) ops)] else [])++(if pm.testBit 7 then [(dom_242,5,runOps true dom_242 (0,roots_242) ops)] else [])++(if pm.testBit 8 then [(dzo_241_2,6,runOps true dzo_241_2 (0,roots_241) ops)] else [])++(if pm.testBit 9 then [(dom_241,6,runOps true dom_241 (0,roots_241) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_243 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · exact cpcs (by decide +kernel) lowS_99 _ g hchk
    · exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · exact cpcs (by decide +kernel) lowS_225 _ g hchk
    · exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_241_2_145 _ g hchk
    · exact cpcs (by decide +kernel) lowS_241 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_211 7 s (0, roots_211) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_243 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_211 h

def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {v ys} (h : RunD true dom_243 goalM v ys) : RunD true dom_243 goalM v (ori ys) := h
def Z (s : Nat) := barP true dom_243 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 15 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 15 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 37 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 37 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 10 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 10 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 8) : ∀ i < NN s, bar true dom_243 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
  · exact z8 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_243 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 8) (h : RunD true dom_243 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_243 roots_243 goal_243 9 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_243

theorem lowS_243 : Lower true dom_243 roots_243 goal_243 9 := S_243.noCircuit

theorem lowS_245 : Lower true dom_245 roots_245 goal_245 9 := lower_iso (d1 := B5.dom_231) (roots1 := B5.roots_231) (T1 := B5.goal_231) [(rowMask32, 63), (rowMask11, 6), (rowMask16, 2), (rowMask22, 12), (rowMask10, 3), (rowMask36, 28)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_231

theorem lowS_246 : Lower true dom_246 roots_246 goal_246 8 := lower_iso (d1 := B2.dom_119) (roots1 := B2.roots_119) (T1 := B2.goal_119) [(rowMask27, 7), (rowMask28, 30), (rowMask22, 12), (rowMask44, 127), (rowMask32, 63)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B2.lowS_119

def dzo_102_16:=0x550000005500000055000000550000

def gzo_102_16:=0x540000005400000044000000000000

def gsh_102_16:=0x54000000540000004400000000

theorem lowS_zo_102_16_102:Lower true dzo_102_16 roots_102 gzo_102_16 4:=lower_iso (d1:=dom_102) (roots1:=roots_102) (T1:=gsh_102_16) [(dom_102,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_102_16) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [] (by decide +kernel) (by decide +kernel) lowS_102)

def dzo_181_2:=0xcc00cc00cc00cc000000000000000000cc00cc00cc00cc

def gzo_181_2:=0xcc00cc00cc00c8000000000000000000cc00cc00880000

def gsh_181_2:=0x3300330033003200000000000000000033003300220000

theorem lowS_zo_181_2_149:Lower true dzo_181_2 roots_181 gzo_181_2 6:=lower_iso (d1:=dom_181) (roots1:=roots_181) (T1:=gsh_181_2) [(dom_181,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_181_2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x3300330000000000000000000000000033003300000000,0,32)] (by decide +kernel) (by decide +kernel) lowS_149)

def dzo_245_2:=rowMask11

def gzo_245_2:=0xcc00cc00cc00cc00cc00cc00cc00c800cc00cc00cc00cc00cc00cc00880000

def gsh_245_2:=0x33003300330033003300330033003200330033003300330033003300220000

theorem lowS_zo_245_2_149:Lower true dzo_245_2 roots_245 gzo_245_2 7:=lower_iso (d1:=dom_245) (roots1:=roots_245) (T1:=gsh_245_2) [(dom_245,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_245_2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(rowMask277,0,32),(rowMask219,0,64)] (by decide +kernel) (by decide +kernel) lowS_149)

def dzo_51_4:=0xf000f000f000f0

def gzo_51_4:=0xe000e000a00000

def gsh_51_4:=0xe000e000a0000

theorem lowS_zo_51_4_51:Lower true dzo_51_4 roots_51 gzo_51_4 4:=lower_iso (d1:=dom_51) (roots1:=roots_51) (T1:=gsh_51_4) [(dom_51,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_51_4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [] (by decide +kernel) (by decide +kernel) lowS_51)

def dzo_230_16:=rowMask278

def gzo_230_16:=0x55000000550000005500000055000000540000005400000044000000000000

def gsh_230_16:=0x5500000055000000550000005500000054000000540000004400000000

theorem lowS_zo_230_16_102:Lower true dzo_230_16 roots_230 gzo_230_16 5:=lower_iso (d1:=dom_230) (roots1:=roots_230) (T1:=gsh_230_16) [(dom_230,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_230_16) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x5500000055000000550000005500000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_102)

def dzo_179_4:=rowMask227

def gzo_179_4:=0xf000f000f000f0000000000000000000e000e000a00000

def gsh_179_4:=0xf000f000f000f0000000000000000000e000e000a0000

theorem lowS_zo_179_4_51:Lower true dzo_179_4 roots_179 gzo_179_4 5:=lower_iso (d1:=dom_179) (roots1:=roots_179) (T1:=gsh_179_4) [(dom_179,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_179_4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xf000f000f000f00000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_51)

namespace S_247
def pairsG : List (Nat × Nat) := [(1,17), (1,33), (1,129), (2,34), (2,66), (3,19), (3,35), (3,67), (3,131), (4,68), (4,132), (5,21), (5,37), (5,69), (5,133), (6,38), (6,70), (6,134), (7,23), (7,39), (7,71), (7,135), (16,17), (16,144), (18,19), (18,50), (18,82), (18,146), (20,21), (20,84), (20,148), (22,23), (22,54), (22,86), (22,150), (32,33), (32,34), (32,160), (36,37), (36,38), (36,100), (36,164), (48,49), (48,50), (48,176), (52,53), (52,54), (52,116), (52,180), (64,66), (64,68), (64,192), (65,67), (65,69), (65,81), (65,97), (65,193), (80,81), (80,82), (80,84), (80,208), (96,97), (96,98), (96,100), (96,224), (112,113), (112,114), (112,116), (112,240), (128,129), (128,132), (128,144), (128,160), (128,192), (130,131), (130,134), (130,146), (130,162), (130,194)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x7fffffffffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_247.map (· &&& dom_247)
def goalM : Nat := goal_247 &&& dom_247
def NN : Nat → Nat
|6=>13
|7=>42
|8=>27
|9=>6
|10=>1
|_=>0
def HT : Nat → Nat → Nat
|6,0=>0xfcfefe4defe3871d8f08d7791af03da6a7897398940c453ccb26f3e1520a0f1f1
|7,0=>0xfff10e57b6e5162d6981d4b3dd1eeccfd12c673cbf5d8be919a3f6ea30d4a11afa039f9ffe09be2d9ab0f99f8995f9694f5d8b42f8907684a8483c747f1df7e5207517e6c3ff5f1ab5389f47d62413b740eeb3ad703726e32abd0ed850e8b90e0c60656c02e8202344
|8,0=>0xfbd2be869be5a98d731fc5f83bf10cb8365b00e0a1a10a05f29dd8596fd8952d08a61f88b2a845b883dc582fb57ed13797be73276725b76c3ff6bc0c4793644c012d858
|9,0=>0xd56678b06f837a872daa6b7402d38c
|10,0=>0x6bf33
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xff00ff00ff00ff000000000000000000aa00aa00aa00aacc00cc00cc00cc00ff00ff00ff00ff00cc00cc00cc00cc00ee00ee00ee00eecc00cc00cc00cc00dd00dd00dd00dd00cc00cc00cc00cc00cc00cc00cc00ccff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000aa000000aaff00ff00ff00ff005500550055005500ff00ff00ff00ff0000000000000000550055005500550055005500550055000000000000000000000000000000000f000f000f000f0005000500050005000f000f000f000f00000000000000005500550055005500550055005500550044004400440044004400440044004400000000000000005500550055005500000000000000000000000000000000aa00aa00aa00aa00ff00ff00ff00ff00aa00aa00aa00aa00aa00aa00aa00aaff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00aa00aa00aa0f000f000f000f0000000f0000000f000f000f000f000f0000000a0000000aff00ff00ff00ff00ff00aa00ff00aa00ff000000ff000000ff000000ff0000ff00ff00ff00ff00ff00ff00aa00aa00ff00ff0000000000ff00ff00000000ff00ff00ff00ff00ff00ff00ff00ff00aa00aa00aa00aa00aa00aa00aa00aaff00ff00ff00ff00ff00ff00ff00ff00cc00cc00cc00cc00cc00cc00cc00cc0000ff000000ff000000ff000000ff000000ff000000ff000000aa000000aa0f000f000f000f000f000f000f000f000f000f000f000f000a000a000a000a0000ff000000ff000000ff000000ff000000aa000000aa000000aa000000aaf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0ff00ff00ff00ff00aa00aa00aa00aa00000000000000000000000000000000ff00ff00ff00ff00aa00aa00aa00aa00ff00ff00ff00ff00aa00aa00aa00aaff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000ff00ff00ff00ff00fa00fa00fa00fa00f000f000f000f000f000f000f000f0ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00ccaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa0000af000000af000000af000000af000000af000000af000000aa000000aaff00ff00ff00ff000000000000000000ff00ff00ff00ff00000000000000000f000f000f000f000f000f000f000f000f000f000f000f0000000000000000ff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000
|0,1=>0xcc00cc00cc00cc00ff00ff00ff00ff00cc00cc00cc00cc00cc00cc00cc00cc55005500550055005500550055005500550055005500550000000000000000dd00dd00dd00dd00dd00dd00dd00dd00cc00cc00cc00cc00cc00cc00cc00cc00000000000000000000000000000000ff00ff00ff00ff00aa00aa00aa00aaaf00af00af00af00af00af00af00af00af00af00af00af00aa00aa00aa00aaff00ff00ff00ff00ee00ee00ee00ee00cc00cc00cc00cc00cc00cc00cc00cc0000000000000000ff00ff00ff00ff000000000000000000000000000000000000aa000000aa000000ff000000ff000000aa000000aa000000aa000000aa
|_,_=>0
def stPool : Nat → Nat
|0=>0x8018914438200624544438200624814408018930529608018c14a10f08018510d5020064cc15108614438f08048930544218510d08100624c40a44718940a10704631010d1c218510f08100631010f1c218510e3420062481441c61440c2040
|1=>0x14434708048930510200630554434200624c41510200624c41510708624c41110708624c14a11b00624c15510200624c40a10700624c40a10718c1443c708018c15510f08018c1443c200630511c34200624510264018931045808018915510e
|2=>0x25010204018931d10200625010708118914a10e08018932210200624554408100624544408100624c1441cb1893052911c018c14a44d08018931029108018c14480200631010d08018914a10704018931e10200624c74a1020064cc14408018c
|3=>0x14a44200630510d08018c15110d08018931044408018931010708624c14a1020171893055441c200624c15110708018930554408018930555110200624c14a10700624c40a10200624c1552840801893109040801891631020401893054422c6
|4=>0x624c15110200624c14a10200624c1447c200624c16410200624c15610200624c40460200624510708100624510204018930510201718932710200624c1440a600624c1446c200624c94408018931010284624c1440802c624c4041c200624c
|5=>0x624c14408018930510201a18930510202118931010200624c1441c2
|_=>0
def stOffB : Nat → Nat → Nat
|6,0=>0x51712d84470f983770c1c297089c1b7051c0d701d8007
|7,0=>0x6421888605d7a75cdd6c759215d755614d8519d3e84da12e849dd207462111742610273ea0f373ae0e3836e0d3832e0c382ee0b472b20a48275c958239c8681fa07771be06871820588
|8,0=>0x267897e257893e2478901e3888c5e29888621a784de0b880e1fb87d1dec87921dd77525cb970a5ba86c65a986861989
|9,0=>0xa5a28e8a1de7f89de26f8
|10,0=>0x29e7
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 40 then fld (dictB (i / 512) (i / 32 % 16)) 248 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 6 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 14 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))

def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 7 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
|0=>0x14044010974a021024a5d2808409080440914044091404201255841d0804956442440125591091004d09251840131b82691008401404c50131591091004c56442440131591091004c2d28004091174a021024956280492d1004a00102462d1004a001024201140440130b42012800409
|1=>0x102450130782011574a021024c1e14042013158a0114b4a00102441d30782013078201100420128004091024201100494610044091404401256848508089461404401307820115f510b100455d280892d28004092518201100462d280040925191091005109140440110745010804201
|2=>0x8085010804401102510b1004a03102448508090131404c1e0804c1e0804a021024585080841e0804269100856910085010808a001024501080440910049461004946100450110045010804a02102441d080420110051091005109100440908044091404a01102440530782011004a00
|3=>0x402
|_=>0
def opOffB : Nat → Nat → Nat
|6,0=>0xb4000074000043000000000000000004000
|7,0=>0x8237f37c37937637427136e36b36836536326035d35a35825535325034d34a34734434133e33b33833533232f32c32932632332031d31a31731431130f2
|8,0=>0xb92b72b52b32b12af2ad2ab2a92a72a52a32a129f29d29b29929729529329128f28d28b2892872852
|9,0=>0xc01bf1be1bd1bc1bb1
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 14 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 63), wireSAt ((code >>> 8) &&& 63)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 12 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmPalB : Nat → Nat
|0=>0x593005910058b0058000511005000049300481004800041100220001f3001e6001b7001b3001860018000133001200011300104000c000082000810008000072000220001900016000130000e00000
|1=>0x805b3481e6405f3405b7404e640481401f7401ee401b321db3105b3080a60802a08013041120200201df301df201db3019b300df300d33005f3005b7005b3
|_=>0
def pmB : Nat → Nat → Nat
|6,0=>0xc00403c0000000180
|7,0=>0x984e0a31cca4989c2da6d62aa1de35d56cb5062c5e734510d64816b25f607
|8,0=>0x12c21962e209948a6be0935ba1868cf74f2c769b4
|9,0=>0x8209a2870
|10,0=>0x11
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 6 (j % 128); fld (pmPalB (k / 32)) 20 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_245,9,runOps true dom_245 (0,roots_245) ops)] else [])++(if pm.testBit 1 then [(dom_231,9,runOps true dom_231 (0,roots_231) ops)] else [])++(if pm.testBit 2 then [(dom_102,4,runOps true dom_102 (0,roots_102) ops)] else [])++(if pm.testBit 3 then [(dzo_102_16,4,runOps true dzo_102_16 (0,roots_102) ops)] else [])++(if pm.testBit 4 then [(dom_215,9,runOps true dom_215 (0,roots_215) ops)] else [])++(if pm.testBit 5 then [(dom_243,9,runOps true dom_243 (0,roots_243) ops)] else [])++(if pm.testBit 6 then [(dom_51,4,runOps true dom_51 (0,roots_51) ops)] else [])++(if pm.testBit 7 then [(dom_246,8,runOps true dom_246 (0,roots_246) ops)] else [])++(if pm.testBit 8 then [(dom_183,8,runOps true dom_183 (0,roots_183) ops)] else [])++(if pm.testBit 9 then [(dom_167,6,runOps true dom_167 (0,roots_167) ops)] else [])++(if pm.testBit 10 then [(dom_119,7,runOps true dom_119 (0,roots_119) ops)] else [])++(if pm.testBit 11 then [(dzo_181_2,6,runOps true dzo_181_2 (0,roots_181) ops)] else [])++(if pm.testBit 12 then [(dzo_245_2,7,runOps true dzo_245_2 (0,roots_245) ops)] else [])++(if pm.testBit 13 then [(dom_178,4,runOps true dom_178 (0,roots_178) ops)] else [])++(if pm.testBit 14 then [(dom_244,6,runOps true dom_244 (0,roots_244) ops)] else [])++(if pm.testBit 15 then [(dzo_51_4,4,runOps true dzo_51_4 (0,roots_51) ops)] else [])++(if pm.testBit 16 then [(dzo_230_16,5,runOps true dzo_230_16 (0,roots_230) ops)] else [])++(if pm.testBit 17 then [(dom_181,6,runOps true dom_181 (0,roots_181) ops)] else [])++(if pm.testBit 18 then [(dom_182,5,runOps true dom_182 (0,roots_182) ops)] else [])++(if pm.testBit 19 then [(dzo_179_4,5,runOps true dzo_179_4 (0,roots_179) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_247 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_102_16_102 _ g hchk
    · exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_181_2_149 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_245_2_149 _ g hchk
    · exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_51_4_51 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_230_16_102 _ g hchk
    · exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_179_4_51 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_245 9 s (0, roots_245) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_247 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_245 h

def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {v ys} (h : RunD true dom_247 goalM v ys) : RunD true dom_247 goalM v (ori ys) := h
def Z (s : Nat) := barP true dom_247 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 13 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 13 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 42 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 42 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8 : ∀ i, 0 ≤ i → i < 27 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 27 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9 : ∀ i, 0 ≤ i → i < 6 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 6 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 10) : ∀ i < NN s, bar true dom_247 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
  · exact z8 i (Nat.zero_le i) hi
  · exact z9 i (Nat.zero_le i) hi
  · exact z10 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_247 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

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
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_247 roots_247 goal_247 11 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_247

theorem lowS_247 : Lower true dom_247 roots_247 goal_247 11 := S_247.noCircuit

end B3

namespace B4
def dom_73 : Nat := 0x3030000000000000303

def goal_73 : Nat := 0xffaaffaaffaaffaaaa00aa00aa00aa00ffaaffaaffaaffaaaa00aa00aa00aa00

def roots_73 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_75 : Nat := 0xf0f0000000000000f0f

def goal_75 : Nat := 0xffeeffeeffeeffeeaa00aa00aa00aa00ffeeffeeffeeffeeaa00aa00aa00aa00

def roots_75 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_83 : Nat := 0xf000f00000000000f000f

def goal_83 : Nat := 0xeeeeeeeeeeeeeeeecccc0000cccc0000eeeeeeeeeeeeeeeecccc0000cccc0000

def roots_83 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_90 : Nat := 0x50505050000000005050505

def goal_90 : Nat := 0xffccffccffccffcccccc0000cccc0000ffccffccffccffcccccc0000cccc0000

def roots_90 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f

def goal_91 : Nat := 0xffeeffeeffeeffeeeeccaa00eeccaa00ffeeffeeffeeffeeeeccaa00eeccaa00

def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_150 : Nat := 0x55005500000000000000000000000000550055

def goal_150 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfccccc0000cccc0000cccc0000cccc0000

def roots_150 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_151 : Nat := 0xff00ff00000000000000000000000000ff00ff

def goal_151 : Nat := 0xfffffefefffffefefffffefefffffefecccc0000cccc0000cccc0000cccc0000

def roots_151 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f

def goal_155 : Nat := 0xffffffeeffffffeeffffffeeffffffeeeeccaa00eeccaa00eeccaa00eeccaa00

def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_157 : Nat := 0x3333333300000000000000000000000033333333

def goal_157 : Nat := 0xfffffffafffffffafffffffafffffffaaa00aa00aa00aa00aa00aa00aa00aa00

def roots_157 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_158 : Nat := 0x5555555500000000000000000000000055555555

def goal_158 : Nat := 0xfffffffcfffffffcfffffffcfffffffccccc0000cccc0000cccc0000cccc0000

def roots_158 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_159 : Nat := 0xffffffff000000000000000000000000ffffffff

def goal_159 : Nat := 0xfffffffefffffffefffffffefffffffeeeccaa00eeccaa00eeccaa00eeccaa00

def roots_159 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_199 : Nat := rowMask312

def goal_199 : Nat := 0xfefefefefefefefefefefefefefefefeeeeeeeeeeeeeeeee0000000000000000

def roots_199 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303

def goal_201 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00aa00aa00

def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f

def goal_203 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeaa00aa00aa00aa00

def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := rowMask301

def goal_205 : Nat := 0xfffafffafffafffafffafffafffafffaffaaffaaffaaffaaaa00aa00aa00aa00

def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff

def goal_207 : Nat := 0xfffefffefffefffefffefffefffefffeffeeffeeffeeffeeaa00aa00aa00aa00

def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_209 : Nat := rowMask204

def goal_209 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaaaaaaaaaaaaaaaaaa0000000000000000

def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_210 : Nat := rowMask299

def goal_210 : Nat := 0xffffccccffffccccffffccccffffcccccccccccccccccccccccc0000cccc0000

def roots_210 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := rowMask205

def goal_211 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeeeeeeeeeeeeeeeeeeecccc0000cccc0000

def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := rowMask149

def goal_213 : Nat := 0xfffffafafffffafafffffafafffffafaaaaaaaaaaaaaaaaa0000000000000000

def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := rowMask242

def goal_214 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfccccccccccccccccccccc0000cccc0000

def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := rowMask187

def goal_215 : Nat := 0xfffffefefffffefefffffefefffffefeeeeeeeeeeeeeeeeecccc0000cccc0000

def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_216 : Nat := rowMask294

def goal_216 : Nat := rowMask269

def roots_216 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := rowMask295

def goal_217 : Nat := 0xffffffaaffffffaaffffffaaffffffaaffaaffaaffaaffaaaa00aa00aa00aa00

def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505

def goal_218 : Nat := 0xffffffccffffffccffffffccffffffccffccffccffccffcccccc0000cccc0000

def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f

def goal_219 : Nat := 0xffffffeeffffffeeffffffeeffffffeeffeeffeeffeeffeeeeccaa00eeccaa00

def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_220 : Nat := rowMask291

def goal_220 : Nat := rowMask270

def roots_220 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := rowMask292

def goal_221 : Nat := 0xfffffffafffffffafffffffafffffffaffaaffaaffaaffaaaa00aa00aa00aa00

def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555

def goal_222 : Nat := 0xfffffffcfffffffcfffffffcfffffffcffccffccffccffcccccc0000cccc0000

def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := rowMask293

def goal_223 : Nat := rowMask273

def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

theorem lowS_73 : Lower true dom_73 roots_73 goal_73 4 := lower_iso (d1 := B5.dom_145) (roots1 := B5.roots_145) (T1 := B5.goal_145) [(rowMask39, 8), (rowMask51, 64)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_145

theorem lowS_75 : Lower true dom_75 roots_75 goal_75 5 := lower_iso (d1 := B5.dom_147) (roots1 := B5.roots_147) (T1 := B5.goal_147) [(rowMask39, 8), (rowMask51, 64)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_147

theorem lowS_201 : Lower true dom_201 roots_201 goal_201 5 := lower_iso (d1 := B5.dom_197) (roots1 := B5.roots_197) (T1 := B5.goal_197) [(rowMask32, 63), (rowMask29, 4), (rowMask214, 124)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_197

theorem lowS_83 : Lower true dom_83 roots_83 goal_83 4 := lower_iso (d1 := B5.dom_85) (roots1 := B5.roots_85) (T1 := B5.goal_85) [(rowMask10, 3), (rowMask0, 1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_85

theorem lowS_90 : Lower true dom_90 roots_90 goal_90 4 := lower_iso (d1 := B5.dom_85) (roots1 := B5.roots_85) (T1 := B5.goal_85) [(rowMask0, 1), (rowMask29, 4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_85

theorem lowS_150 : Lower true dom_150 roots_150 goal_150 5 := lower_iso (d1 := B5.dom_147) (roots1 := B5.roots_147) (T1 := B5.goal_147) [(rowMask10, 3), (rowMask0, 1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_147

theorem lowS_209 : Lower true dom_209 roots_209 goal_209 4 := lower_iso (d1 := B5.dom_85) (roots1 := B5.roots_85) (T1 := B5.goal_85) [(rowMask29, 4), (rowMask36, 28), (rowMask22, 12), (rowMask183, 112), (rowMask34, 48)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_85

theorem lowS_210 : Lower true dom_210 roots_210 goal_210 5 := lower_iso (d1 := B5.dom_147) (roots1 := B5.roots_147) (T1 := B5.goal_147) [(rowMask10, 3), (0xcccccccccccccccccccccccccccccccc, 126), (rowMask27, 7), (rowMask33, 31), (rowMask35, 15), (rowMask34, 48), (rowMask37, 14)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_147

theorem lowS_216 : Lower true dom_216 roots_216 goal_216 4 := lower_iso (d1 := B5.dom_85) (roots1 := B5.roots_85) (T1 := B5.goal_85) [(rowMask0, 1), (rowMask27, 7), (rowMask36, 28), (rowMask22, 12), (rowMask183, 112), (rowMask34, 48)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_85

def dzo_75_16:=0xf0f0000000000000f0f0000

def gzo_75_16:=0xf0e0000000000000e0c0000

def gsh_75_16:=0xf0e0000000000000e0c

theorem lowS_zo_75_16_73:Lower true dzo_75_16 roots_75 gzo_75_16 5:=lower_iso (d1:=dom_75) (roots1:=roots_75) (T1:=gsh_75_16) [(dom_75,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_75_16) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xc0c0000000000000c0c,0,2)] (by decide +kernel) (by decide +kernel) lowS_73)

theorem lowS_91 : Lower true dom_91 roots_91 goal_91 7 := lower_iso (d1 := B6.dom_117) (roots1 := B6.roots_117) (T1 := B6.goal_117) [(rowMask35, 15), (rowMask28, 30), (rowMask16, 2), (rowMask220, 56), (rowMask10, 3), (rowMask27, 7)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B6.lowS_117

theorem lowS_155 : Lower true dom_155 roots_155 goal_155 8 := lower_iso (d1 := B5.dom_179) (roots1 := B5.roots_179) (T1 := B5.goal_179) [(rowMask39, 8), (rowMask46, 24)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_179

theorem lowS_203 : Lower true dom_203 roots_203 goal_203 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(rowMask245, 64, 66)] (by decide +kernel) (by decide +kernel) lowS_201

def dzo_201_4:=0x3030000000000000303000000000000030300000000000003030

def gzo_201_4:=0x3030000000000000303000000000000030200000000000002000

def gsh_201_4:=rowMask306

theorem lowS_zo_201_4_73:Lower true dzo_201_4 roots_201 gzo_201_4 5:=lower_iso (d1:=dom_201) (roots1:=roots_201) (T1:=gsh_201_4) [(dom_201,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_201_4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(rowMask307,0,128)] (by decide +kernel) (by decide +kernel) lowS_73)

theorem lowS_205 : Lower true dom_205 roots_205 goal_205 7 := lower_iso (d1 := B6.dom_181) (roots1 := B6.roots_181) (T1 := B6.goal_181) [(rowMask33, 31), (rowMask22, 12), (rowMask290, 120), (rowMask29, 4), (rowMask32, 63), (rowMask10, 3)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B6.lowS_181

theorem lowS_151 : Lower true dom_151 roots_151 goal_151 6 := lower_iso (d1 := B5.dom_151) (roots1 := B5.roots_151) (T1 := B5.goal_151) [(rowMask0, 1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_151

theorem lowS_157 : Lower true dom_157 roots_157 goal_157 6 := lower_iso (d1 := B5.dom_151) (roots1 := B5.roots_151) (T1 := B5.goal_151) [(rowMask11, 6), (rowMask16, 2), (rowMask22, 12)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_151

theorem lowS_158 : Lower true dom_158 roots_158 goal_158 6 := lower_iso (d1 := B5.dom_151) (roots1 := B5.roots_151) (T1 := B5.goal_151) [(rowMask27, 7), (rowMask0, 1), (rowMask16, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_151

theorem lowS_199 : Lower true dom_199 roots_199 goal_199 5 := lower_iso (d1 := B2.dom_103) (roots1 := B2.roots_103) (T1 := B2.goal_103) [(rowMask49, 96), (rowMask26, 32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B2.lowS_103

theorem lowS_211 : Lower true dom_211 roots_211 goal_211 6 := lower_iso (d1 := B2.dom_115) (roots1 := B2.roots_115) (T1 := B2.goal_115) [(rowMask0, 1), (rowMask49, 96), (rowMask26, 32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B2.lowS_115

theorem lowS_213 : Lower true dom_213 roots_213 goal_213 5 := lower_iso (d1 := B2.dom_118) (roots1 := B2.roots_118) (T1 := B2.goal_118) [(rowMask0, 1), (rowMask49, 96), (rowMask26, 32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B2.lowS_118

theorem lowS_214 : Lower true dom_214 roots_214 goal_214 6 := lower_iso (d1 := B2.dom_117) (roots1 := B2.roots_117) (T1 := B2.goal_117) [(rowMask0, 1), (rowMask49, 96), (rowMask26, 32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B2.lowS_117

theorem lowS_217 : Lower true dom_217 roots_217 goal_217 7 := lower_iso (d1 := B6.dom_181) (roots1 := B6.roots_181) (T1 := B6.goal_181) [(rowMask33, 31), (rowMask29, 4), (rowMask214, 124), (rowMask32, 63), (rowMask10, 3)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B6.lowS_181

theorem lowS_218 : Lower true dom_218 roots_218 goal_218 6 := lower_iso (d1 := B2.dom_115) (roots1 := B2.roots_115) (T1 := B2.goal_115) [(rowMask10, 3), (rowMask0, 1), (rowMask11, 6), (rowMask49, 96), (rowMask26, 32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B2.lowS_115

theorem lowS_220 : Lower true dom_220 roots_220 goal_220 5 := lower_iso (d1 := B2.dom_118) (roots1 := B2.roots_118) (T1 := B2.goal_118) [(rowMask11, 6), (rowMask49, 96), (rowMask26, 32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B2.lowS_118

theorem lowS_159 : Lower true dom_159 roots_159 goal_159 9 := lower_iso (d1 := B5.dom_183) (roots1 := B5.roots_183) (T1 := B5.goal_183) [(rowMask39, 8), (rowMask46, 24)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_183

theorem lowS_207 : Lower true dom_207 roots_207 goal_207 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcccc000000000000cccc000000000000cccc000000000000cccc, 64, 66)] (by decide +kernel) (by decide +kernel) lowS_205

theorem lowS_219 : Lower true dom_219 roots_219 goal_219 9 := lower_iso (d1 := B2.dom_243) (roots1 := B2.roots_243) (T1 := B2.goal_243) [(rowMask0, 1), (rowMask290, 120), (rowMask46, 24), (rowMask26, 32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B2.lowS_243

theorem lowS_221 : Lower true dom_221 roots_221 goal_221 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(rowMask234, 128, 132)] (by decide +kernel) (by decide +kernel) lowS_217

theorem lowS_215 : Lower true dom_215 roots_215 goal_215 8 := lower_iso (d1 := B2.dom_119) (roots1 := B2.roots_119) (T1 := B2.goal_119) [(rowMask0, 1), (rowMask49, 96), (rowMask26, 32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B2.lowS_119

theorem lowS_222 : Lower true dom_222 roots_222 goal_222 8 := lower_iso (d1 := B2.dom_119) (roots1 := B2.roots_119) (T1 := B2.goal_119) [(rowMask27, 7), (rowMask0, 1), (rowMask49, 96), (rowMask26, 32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B2.lowS_119

def dzo_91_4:=0xf0f0f0f000000000f0f0f0f0

def gzo_91_4:=0xf0e0f0e000000000e0c0a000

def gsh_91_4:=0xf0e0f0e000000000e0c0a00

theorem lowS_zo_91_4_91:Lower true dzo_91_4 roots_91 gzo_91_4 7:=lower_iso (d1:=dom_91) (roots1:=roots_91) (T1:=gsh_91_4) [(dom_91,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_91_4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [] (by decide +kernel) (by decide +kernel) lowS_91)

def dzo_73_16:=0x30300000000000003030000

def gzo_73_16:=0x30200000000000002000000

def gsh_73_16:=0x3020000000000000200

theorem lowS_zo_73_16_73:Lower true dzo_73_16 roots_73 gzo_73_16 4:=lower_iso (d1:=dom_73) (roots1:=roots_73) (T1:=gsh_73_16) [(dom_73,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_73_16) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [] (by decide +kernel) (by decide +kernel) lowS_73)

def dzo_219_4:=rowMask36

def gzo_219_4:=0xf0f0f0f000000000f0f0f0f000000000f0e0f0e000000000e0c0a000

def gsh_219_4:=0xf0f0f0f000000000f0f0f0f000000000f0e0f0e000000000e0c0a00

theorem lowS_zo_219_4_91:Lower true dzo_219_4 roots_219 gzo_219_4 8:=lower_iso (d1:=dom_219) (roots1:=roots_219) (T1:=gsh_219_4) [(dom_219,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_219_4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xf0f0f0f000000000f0f0f0f00000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_91)

def dzo_211_4:=0xf000f00000000000f000f00000000000f000f00000000000f000f0

def gzo_211_4:=0xf000f00000000000f000f00000000000e000e00000000000c00000

def gsh_211_4:=0xf000f00000000000f000f00000000000e000e00000000000c0000

theorem lowS_zo_211_4_83:Lower true dzo_211_4 roots_211 gzo_211_4 5:=lower_iso (d1:=dom_211) (roots1:=roots_211) (T1:=gsh_211_4) [(dom_211,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_211_4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xf000f00000000000f000f00000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_83)

def dzo_203_20:=0xf0f0000000000000f0f0000000000000f0f0000000000000f0f00000

def gzo_203_20:=0xf0f0000000000000f0f0000000000000f0e0000000000000e0c00000

def gsh_203_20:=rowMask308

theorem lowS_zo_203_20_73:Lower true dzo_203_20 roots_203 gzo_203_20 6:=lower_iso (d1:=dom_203) (roots1:=roots_203) (T1:=gsh_203_20) [(dom_203,20)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_203_20) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(rowMask245,0,2),(rowMask246,0,128)] (by decide +kernel) (by decide +kernel) lowS_73)

def dzo_218_4:=0x50505050000000005050505000000000505050500000000050505050

def gzo_218_4:=0x50505050000000005050505000000000504050400000000040400000

def gsh_218_4:=0x5050505000000000505050500000000050405040000000004040000

theorem lowS_zo_218_4_90:Lower true dzo_218_4 roots_218 gzo_218_4 5:=lower_iso (d1:=dom_218) (roots1:=roots_218) (T1:=gsh_218_4) [(dom_218,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_218_4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x5050505000000000505050500000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_90)

def dzo_203_16:=0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0000

def gzo_203_16:=0xf0f0000000000000f0f0000000000000f0e0000000000000e0c0000

def gsh_203_16:=rowMask308

theorem lowS_zo_203_16_73:Lower true dzo_203_16 roots_203 gzo_203_16 6:=lower_iso (d1:=dom_203) (roots1:=roots_203) (T1:=gsh_203_16) [(dom_203,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_203_16) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(rowMask245,0,2),(rowMask246,0,128)] (by decide +kernel) (by decide +kernel) lowS_73)

def dzo_203_4:=0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0

def gzo_203_4:=0xf0f0000000000000f0f0000000000000f0e0000000000000a000

def gsh_203_4:=0xf0f0000000000000f0f0000000000000f0e0000000000000a00

theorem lowS_zo_203_4_75:Lower true dzo_203_4 roots_203 gzo_203_4 6:=lower_iso (d1:=dom_203) (roots1:=roots_203) (T1:=gsh_203_4) [(dom_203,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_203_4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(rowMask246,0,128)] (by decide +kernel) (by decide +kernel) lowS_75)

def dzo_201_16:=0x3030000000000000303000000000000030300000000000003030000

def gzo_201_16:=0x3030000000000000303000000000000030200000000000002000000

def gsh_201_16:=rowMask306

theorem lowS_zo_201_16_73:Lower true dzo_201_16 roots_201 gzo_201_16 5:=lower_iso (d1:=dom_201) (roots1:=roots_201) (T1:=gsh_201_16) [(dom_201,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_201_16) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(rowMask307,0,128)] (by decide +kernel) (by decide +kernel) lowS_73)

namespace S_223
def pairsG : List (Nat × Nat) := [(1,9), (1,65), (1,129), (2,18), (2,66), (2,130), (3,11), (3,19), (3,67), (3,131), (4,132), (5,13), (5,69), (5,133), (6,22), (6,70), (6,134), (7,15), (7,23), (7,71), (7,135), (8,9), (8,72), (8,136), (10,11), (10,26), (10,74), (10,138), (12,13), (12,76), (12,140), (14,15), (14,30), (14,78), (14,142), (16,18), (16,144), (17,19), (17,25), (17,81), (17,145), (20,22), (20,148), (21,23), (21,29), (21,85), (21,149), (24,25), (24,26), (24,88), (24,152), (28,29), (28,30), (28,92), (28,156), (64,65), (64,66), (64,72), (68,69), (68,70), (68,76), (68,196), (80,81), (80,82), (80,88), (80,208), (84,85), (84,86), (84,92), (84,212), (128,129), (128,130), (128,132), (128,136), (128,144), (192,193), (192,194), (192,196), (192,200), (192,208)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xffffffffffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_223.map (· &&& dom_223)
def goalM : Nat := goal_223 &&& dom_223
def NN : Nat → Nat
|3=>1
|4=>3
|5=>12
|6=>75
|7=>103
|8=>46
|9=>11
|10=>1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0x75aee
|4,0=>0xa0c7b4b24a3b14a
|5,0=>0x6d504662d76059f4637e3c7372fa772466b1093b0b920074df03b360113b
|6,0=>0xffea5ff2d8f2fbbe5f8bdfbfcd4613ce0a3c94acc5982c5004bf2dab6388b5c1eafe52ae098ab979aaa709ec7b9db559b4bf98a4398691910fb8ed658ae2089e8388c42853328387f7fe9e784e27555b738e672100717db70489689a4678c4650ed604655e5ad5b00755b615435853c135303252d9d51e704f7f84d3164c117481a5466e643d1e43bcd40b393b00a327b63235b2bf2f2a5d6254f024099200e116ec116cca14c0412f4f09fd7068750606503e7a03b2302a7601c56
|7,0=>0xfa7e2f9230eeedbe639ee2659e24fde1b4add43adc912d9f07d5a4ecee17cc629c65b8c5da5c53e4c2ad4c0ea4bfa72b9949b897ab3d7cb21b2afe52aea16aa746a97b0a9192a6e92a2b28a17e29d48c9b6169ab5897f7f97c0797370968dc95bda9451b8b55e882e9872078416b7a2a97954a7596874f4c734c77240d721b670bcb6dc316953569367655a26553a6447f5f4205d9435c47d570bc56f7356d7c564734f6be4c8eb4a08943bd541d6641ac73f73e3ee233edcc3984433db133b88300a22ecb02e1ee2cde32a263257032555a20c401e6051e4a81de341a53617c9415e3b151ab1506f134c80eafd0e1550c3840b74a07bbf0748c0611a050b604642
|8,0=>0xf704af0e9eeeac8cc01ac9b81c5ba1bc59eb526db363aa753ea40408d57d8b3a28696285028802ee7a5d179c7c739ea6d24a6bb99649e75878e57afd525b14c4364bbc64985348e323a89435280316e82fbbc2ce97225af21bfc1f6a41d5d11ce73197cd17f72085c705678052ec00f5600d57
|9,0=>0xf36ecf1194e40f29db0a86d5d4b76c2b23c2a8e71d6b617c0402883
|10,0=>0xfc3d7
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x5544554400000000554455440000000055445544000000005544554455555555000000005555555500000000555555550000000000000000111111110000000011111111000000001111111100000000000000000033003300000000003300330000000000330033000000000000000000bb00bb0000000000bb00bb0000000000bb00bb0000000000aa00aa0f0f0f0f00000000ffefffef000000000000000000000000ffeeffeeeeeeeeee00000000eeeeeeee00000000eeeeeeee00000000eeeeeeeeff00ff0000000000ff00ff0000000000ff00ff0000000000aa00aa00ffeeffee00000000ffeeffee00000000ffeeffee00000000ffeeffeeffeeffee00000000ffeeffee00000000ffeeffee0000000000000000ffccffcc00000000ffccffcc00000000ffccffcc00000000ffccffcceeeeeeee00000000eeeeeeee00000000ee00ee0000000000ee00ee00ffffffff00000000ffffffff00000000aaaaaaaa00000000aaaaaaaaffffffff000000000000000000000000ffffffff0000000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00eeeeeeee00000000eeeeeeee00000000eeeeeeee0000000000000000ffffffff00000000ffffffff00000000ffffffff00000000ccccccccaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaaffffffff00000000ffffffff00000000ff00ff0000000000ff00ff00ffffffff00000000ffffffff00000000ffffffff0000000000000000ffffffff00000000ffffffff00000000ffffffff00000000ff00ff00ffeeffee00000000ffeeffee00000000ffeeffee00000000aaaaaaaacccccccc00000000cccccccc00000000cccccccc00000000ccccccccffffffff00000000ffffffff00000000000000000000000000000000ffeeffee00000000ffeeffee00000000ffeeffee00000000ff00ff00ffffffff00000000ffffffff00000000ffffffff00000000aaaaaaaaaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aa00aa00ffccffcc00000000ffccffcc00000000ffccffcc0000000000000000ffff000000000000ffff000000000000ffff000000000000ffff0000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0ffffffff00000000ffffffff00000000cccccccc00000000ccccccccffeeffee00000000ffeeffee00000000ffeeffee00000000aa00aa00
|0,1=>0xffffffff00000000ffffffff00000000ffeeffee00000000ffeeffee555555550000000055555555000000005500550000000000550055005f4f5f4f000000005f4f5f4f0000000055445544000000005544554433333333000000003333333300000000333333330000000000000000ff33ff3300000000ff33ff3300000000ff33ff3300000000ff00ff0000330033000000000033003300000000002200220000000000220022ffcfffcf00000000ffcfffcf00000000ffccffcc00000000ffccffccccffccff00000000ccffccff00000000ccffccff00000000cccccccc00230023000000000023002300000000002200220000000000220022ccffccff00000000ccffccff00000000cceeccee00000000cceecceeaaffaaff00000000aaffaaff00000000aaffaaff00000000aaaaaaaaffaaffaa00000000ffaaffaa00000000ffaaffaa00000000ffaaffaa0000cfcf000000000000cfcf000000000000cccc000000000000cccc55555555000000005555555500000000555555550000000044444444ffefffef00000000ffefffef00000000ffeeffee00000000ffeeffeeffffffff00000000ffffffff0000000000ee00ee0000000000ee00ee3323332300000000332333230000000033223322000000003322332200ee00ee0000000000ee00ee0000000000ee00ee0000000000ee00eefefefefe00000000fefefefe00000000fefefefe00000000fefefefeffffffff00000000ffffffff000000000000000000000000ffccffcc00ff00ff0000000000ff00ff0000000000ff00ff00000000000000000055005500000000005500550000000000550055000000000000000000ff00ff0000000000ff00ff0000000000ee00ee0000000000ee00ee33333333000000003333333300000000333333330000000022222222bbbbbbbb00000000bbbbbbbb00000000bbaabbaa00000000bbaabbaabb00bb0000000000bb00bb0000000000bb00bb0000000000aa00aa000f0f0f0f000000000f0f0f0f00000000000000000000000000000000cfcfcfcf00000000cfcfcfcf00000000cccccccc00000000ccccccccffffffff00000000ffffffff00000000eeeeeeee00000000eeeeeeeef0f0f0f000000000fffefffe00000000f0f0f0f000000000fffefffe0000000000000000ffeeffee000000000000000000000000ffeeffeeafafafaf00000000afafafaf00000000aaaaaaaa00000000aaaaaaaa
|0,2=>0xdddddddd00000000dddddddd00000000ddccddcc00000000ddccddccffff0f0f00000000ffff0f0f00000000ffff000000000000ffff0000fffcfffc00000000fffcfffc00000000fffcfffc00000000fffcfffc5554555400000000555455540000000055545554000000005554555433333333000000003333333300000000330033000000000033003300bbbbbbbb00000000bbbbbbbb00000000bbbbbbbb00000000aaaaaaaa00000000000000000000000000000000eeeeeeee00000000eeeeeeeeff00ff0000000000ff00ff0000000000ffeeffee00000000ffeeffeeffffffff00000000ffffffff00000000554455440000000055445544ff0fff0f00000000ff0fff0f00000000ff00ff0000000000ff00ff0000ff00ff0000000000ff00ff0000000000ff00ff0000000000cc00ccfffffff000000000fffffff000000000fffffff000000000fffffff0ffffff0000000000ffffff0000000000ffffff0000000000ffffff0055555550000000005555555000000000555555500000000055555550fffefffe00000000fffefffe00000000fffefffe00000000fffefffeffccffcc00000000ffccffcc00000000aa88aa8800000000aa88aa88ffffffff00000000ffffffff000000000000000000000000ffeeffee00000000000000000000000000000000ffffffff00000000eeeeeeee00ff00ff0000000000ff00ff0000000000aa00aa0000000000aa00aaff23ff2300000000ff23ff2300000000ff22ff2200000000ff22ff2200ff00ff0000000000ff00ff0000000000ff00ff0000000000ee00ee55555555000000005555555500000000555555550000000055005500000000000000000000000000000000000000000000000000ffeeffeeff00ff0000000000ff00ff0000000000ff00ff0000000000ee00ee00110011000000000011001100000000001100110000000000ff00ff00550555050000000055055505000000005500550000000000550055000000000000000000aaaaaaaa000000000000000000000000ffeeffee333333330000000033333333000000003322332200000000332233220000000000000000ffffffff000000000000000000000000ffeeffee00ef00ef0000000000ef00ef0000000000ee00ee0000000000ee00eeccefccef00000000ccefccef00000000cceeccee00000000cceecceeffffffff00000000ffffffff00000000ffccffcc00000000ffccffcc
|0,3=>0xfffffafa00000000fffffafa00000000fffffafa00000000fffffafa0000fafa000000000000fafa000000000000fafa000000000000fafaffffffff00000000ffffffff00000000ffff000000000000ffff000033333333000000003333333300000000222222220000000022222222fcfcfcfc00000000fcfcfcfc00000000fcfcfcfc00000000fcfcfcfc00000000000000000000000000000000ffeeffee00000000ffeeffeeffffffff00000000ffffffff00000000ffffffff00000000ffaaffaa000000000000000000000000000000000000000000000000eeeeeeee0000ffff000000000000ffff000000000000cccc000000000000ccccffffffff00000000ffffffff00000000ffaaffaa00000000ffaaffaa32323232000000003232323200000000323232320000000032323232ffff323200000000ffff323200000000ffff323200000000ffff3232f5f4f5f400000000f5f4f5f400000000f5f4f5f400000000f5f4f5f40000000000000000000000000000000000ee00ee0000000000ee00eeff55ff5500000000ff55ff5500000000ff55ff5500000000ff00ff00fafafafa00000000fafafafa00000000fafafafa00000000fafafafa00fa00fa0000000000fa00fa0000000000fa00fa0000000000fa00fa00550050000000000055005000000000005500500000000000550050ffffffaa00000000ffffffaa00000000ffffffaa00000000ffffffaafffffffa00000000fffffffa00000000fffffffa00000000fffffffaffffffff00000000ffffffff00000000ffffffff00000000ffccffcc55505550000000005550555000000000555055500000000055505550fff0fff000000000fff0fff000000000fff0fff000000000fff0fff0dddcdddc00000000dddcdddc00000000dddcdddc00000000dddcdddc00000000000000000000000000000000ffccffcc00000000ffccffccffafffaf00000000ffafffaf00000000ffaaffaa00000000ffaaffaa00ff00f00000000000ff00f00000000000ff00f00000000000ff00f0fffff0f000000000fffff0f000000000fffff0f000000000fffff0f0aaffaafa00000000aaffaafa00000000aaffaafa00000000aaffaafa00ff00ff0000000000ff00ff0000000000ff00ff0000000000aa00aa23232323000000002323232300000000222222220000000022222222efefefef00000000efefefef00000000eeeeeeee00000000eeeeeeee
|0,4=>0xfffafffa00000000fffafffa00000000fffafffa00000000fffafffa5555550000000000555555000000000055555500000000005555550033303330000000003330333000000000333033300000000033303330ffffaaaa00000000ffffaaaa00000000ffffaaaa00000000ffffaaaa
|_,_=>0
def stPool : Nat → Nat
|0=>0xc0403171109201208030b02090e0408031102010e1f0c03110209130c1d031102010e0c1c0302010e1b0c030209050408031102091316031a11090e0803021901180c031102010a0c031102010e16031502141312031102010610030d020f0e04030d02090a0c030b02090a0803020900080307020106030201050403020100
|1=>0x202e12080321112d090e08030201090e180c032c1102090e0c030d02090e0c2a03110214091312031102010e0c04031102090e290c031102010e280c030702090e0c0803110209270e0c0302090e260c08031711240e12080315110219130c03151102230e0c03222111090e08031511192012080317110209130c030d02090e
|2=>0x1102090e3a0c033911190e120803150b02010e0c030d0238090e0c03021909180c080311090e37120803340b0209130c0311020f0e040803110236090e0c0311240e1f1208030d0209350e0c3411090e3312080311020913320c033111090e1208031102090e300c031102090e16080311090e2f120803110209132e0c031109
|3=>0x8030248090e0c08034702090e0c0803150d020f0e0c0311190946120803340b0209060803451102090e080302090e1b0c08032111090e0825031102090e440c03431102090e080311090e421208031141090e1208033f1102090e0c031102093e0c1e0311090e3d1208033b1102010e0c030d02090e1e2b030b110209131e03
|4=>0x3151102190e0c08031502090e4d120803110201090e0c2b03150d0219131203512111090e0803170d0209131203110219501208034f1102090e08030209050c2b0803171102010e0c0311024e090e0c03110201094a0c031502090e4d0c034c11090e120803110209134a0c0302090e4b0c08031102094a0c0803491102090e
|5=>0x90e12080311090e5c1208031102090e5b0c0315110209130e0c031102095a0e0c0803151109200e1208030d02090e1f120803581102090e1208031102090e57120803511711090e1208033456090e120803110209130e0c3c03171102010e12080311022319090e0c031102090e550c080311090e52120803150d0209130e12
|6=>0x180c080317110209131208031102010e1f120803211102090e08031102090e620c080311090e611208031511240e1208031160090e12080311025f090e120803511511090e120803341124090e120803110209060e2b08031102090e1f0c080302090e180c08031102090e0c1c0803110214090e120811090e3312085e033411
|7=>0x2090e0c2b080321110219090e0803116019090e120803110209130c1e0315112d190e120803110209270e1208030d1102090e0c1e0311090e461208031556090e1208031102090e0c04080317112d090e1208031102090e280c08031511021913120803151102230e120803395611090e120803340b02090e0c08030209060e
|8=>0x201090e0c03711102090e0c08031102090e0c2a08030b1102094a0c080315090e6f120803401102090e0c0311090e6e1208030b110209130e0c6c0311090e1208036b1102090e0c0803400d1102090e0c031168090e120803671102190e120803665611090e120803340d02090e0c031109630e1208031102090e291208030b
|9=>0x20f09130e0c03150d02090e0c03110238090e0c08035111090e12087411090e1208031511190e120825031102090e3a1208031102094a0c08031102090e4d0c031102190f0e0c08031173090e1208031102090e721208031711090e120825036611090e120803110219010e0c0317211102090e0803150b02090e0c08030b11
|10=>0x803761102090e0c03171102090e0c08037a1102090e12080311020f0e0c3c0803791102090e0c080376110209130e0c0334110201090e0c031102010e0c3c0311090e1f12082503110278090e0c08341102090e771208031102090e441208031102090e1e2b08030b110209060e0803340d02091312033f1102090e12080311
|11=>0x1102090e7c120803691119090e120803112d19090e120803151102010e12080376110209130e12080334110201090e12080334117b090e120803110223090e12080334110209131208030d110219090e120803151102090e0c08031102090e0c3c08031124090e12080311022309130e120803150d02090e120803112d090e12
|12=>0xe1208030b1102090e0c080311090e6f1208031119090e120825033411090e1208256d031102090e12080311090e8112087f0311090e120803151102190e1208031102090e0c1e0803171102090e12080311090e7e12080311022319090e12087d03341102090e12080311090e651208035611090e120803761102090e120803
|13=>0x7d031102090e120853031102090e1208036911090e12085e0311090e1208030d110209130e12031102090e4d120803341102090e0c08038311090e1208031102090e8212080311020f090e0c0864033411090e120803110201090e0c1102090e77120803110209130e0c031102090e1f120803671102090e1208031711021909
|14=>0x31102090e120803110201090e120803117b090e120803110209130e1208031102090e0c08640311090e12080311090e12082503110219090e120803341102090e1208
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>4
|4,0=>0x39404a8045
|5,0=>0xaac13d824b043607ac0dd818b02b604ac07d80cb0136
|6,0=>0x428e835d0339ff73f0e7c5cf539e373b8e755ce739c77380e6e5cd939ab7348e675ccb398f7310e605cbd397372d8e595caf395772a0e525ca1393b7268e4b5c93391f7230e445c85390371f8e3d5c7738e771c0e365c6938cb7188e2f5c5b38af7150e285c4d38937118e215c3f387770e0e1a5c31385b7
|6,1=>0x985d2d3a537498e915d1f3a377460e8a5d113a1b7
|7,0=>0x89cf11a21fbc37885f10a1e1044188822f029e0143fa87e50faa1f1bbdb87a70f2e1e23bbd776b0eb61d2c39d872b0e361c2c37d86eb0db61b33b5e86aeed41da4bb4186730cc6194c3218634ec4a185430465f90bd5d773ae685bd0b5a16742c6857d0ada157baa7853f0a5e147c288750109e213842688
|7,1=>0x15e1eb845688ac115622a845488a82f4e6298c5298a431466288c50a7a0513ea279bceb89c8f379a6b44ce898ef301e5c44b17953128624d3c937917120e23dc47388d7118e22e3c557
|8,0=>0x3713eda8da51b2a361bebb8d671aae3523e9d7d2cfa3a343467d9ceb19b9f33465e8cad193df243e408c7118c2314be209c2f3841f04be018bf317c62f4c5e18bb1373e6e3c5bf8b6f16ba6d3459e8b2ef63a6c3457f7
|9,0=>0x1cd2396bf258e3cfc5df883f088e011be237846e97
|10,0=>0x73c7
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 132 then fld (dictB (i / 512) (i / 32 % 16)) 224 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 8 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 15 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))

def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 8 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
|0=>0x110c448212011d0039150842445113c42432110c44821110c44821092b44432110c448210925424450208838ad110c80c920925408220f0ec2431111945c30150e42445120846447090e418440e0c438ae110c834640e09454300911448210609c383109254446502088543909114543009114482109084543b091144821091e83832150c82445170c02421091144821
|1=>0xe3c424321208424450e2540822150ec2445591146423090e47c210e158244517024d025110e444391125408220e084243212084d025090844439190842439120843c47090c44821540ed4c090311444211109424390911448211311c382109084443212084442111094d025110e444210e15444250908454390911448210b0ec44310b0ec4431090c44421120843831
|2=>0x1208418440e0c448210e15444250e08424210e15824451712cd025110e418470e0c448212009c38950208824950911408222009438950208824f90e0d844211702438550911444390925408220e0c4443212084543b0911448210611038311208454320911448210d1903825110840c92092540822032540822110e43976021542445120842436110844821110943821
|3=>0x911448211208424351108425a9690ec08451508c24451125408221108448210e11439956411c0c0911238244d0e08444ad110c848211712c4465090e46495090e408220e0c848210e08444250219424390e5b42436110843832120844421560ec4495020884425112540822150c024451208408651119424390609c38311208438250e0844c250e0844495020884431
|4=>0x7009c0839110942439020884c571109438210b0ec443112084444e120843821090c44821021f438560911434660e0944421111942439020895839112540822090842439120845c4b340944439110c448210908444311208444790e0c84821340c84821110e42c3b110c4482111095c047020e454210911448216434c0c09110e444311208438216d0240cd1110e45431
|5=>0x110840865090e4d021120844439150e42445120845c23340944439090c8243112084d03112084443912084444d0e0842421120844439090842432120843856091140822190cc2439120840c060908444397609c444d0e08444320e0c848210e0c444311208444391108438210d1943825110843821090c448211108424451208424ad110c8482117024d025110e40dd5
|6=>0x91144465090e4443112085c047020e42439020880822110e40cd1110e5a427021160009030e44425090e4383212084d025110e40dc2020e46421090e40c21110e5904703024449502088444d0e084244e0e0842439021140865090e4244509084444d0e0842421110e40825110e4244d0e08444390e084382511084244512084243212084249502088244d0e0842445
|7=>0x908408250e0844821030240822090e44439030840c45021140c950208844210e084444e0e0844821110e4d009110e54c3b031142431120840c09110e44821090840c060908448210e0843856091145423
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0x80000000000000000
|6,0=>0x221000000000000000008260001f1800000000000000000003d11d180000003820000d880000001a10c8800000018100000002d31590a0c4c425100008500001f200000003a40000d906482c60000a10000000000089800000000000003c818600000002100c4042
|6,1=>0x14489e44c300000000004840001188000000
|7,0=>0x839c10e026fe37d9be0dec4f42789bb8dd66e83729b88dbe6dc36c9b58da66d03669b28d8e6c5261930497e4bc35c9ad8d666b03569aa8d4e6a43509a78d3669834a9a48d1e68c3449a18d0668033e99e8cf047533919bccd8669333198ccc065d32d9160cac4533
|7,1=>0x5e8eee7743b89db8ed67683b29d88ebe75c3ac9d58ea67503a69d28e8e7443a09cf8e7673839a9cc8e6052d3951c9ce4872138f1c70a327163899c40e1a70a3
|8,0=>0x3ae5d52e99744b9e5cd2e59724b8e5c52e19704b7e5bd2dd96e4b6e5b52d996c4b5e5ad2d596a4b4e5a52d19684b3e59d2cd9664b2e5952c99644b1e58d2c59624b0e5852c19604afe57d2
|9,0=>0x78c7c43e11f00f7c7bc3dd1ee0f6c7b43d91
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 18 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 255), wireSAt ((code >>> 10) &&& 255)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 13 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmPalB : Nat → Nat
|0=>0x8000000000aa4000000114800000021800000004100000000800000000081000000009f0000000136000000022c0000000448000000083000000010400000002000000000200000000030000000005c00000000a800000000e00000000120000000020000000003c000000007000000000c0000000016000000002800000000480000000080000000008000000000c0000000010000000000
|1=>0x4697e000008d2dc000009a5a000000c6b90000018c5200000292fc00000429580000084a9000001087e000002102c00000321e8000003cba0000006b7e000000d2fc000001a5f00000034b70000004b6e00000092fc00000125b80000014bf000000297c000000420800000080100000006bd0000000c10000000126400000024580000004330000000836000000102c0000002048000000402
|2=>0xa0813e00014092fc00028124f800050019f000090493e000101047c0002012cf80004024bf000080493e000100067c000200045800022049f000044092e000060006c000084007800010411b0000208136000041006400008125f80000804190000100800000020040800004004e800008001b000010002200001c025c00002800100000334b7000006232c00000c0258000011e5f8000023597
|3=>0x22000697e040000d2fc0210004090040000083004000697e00800092fc01000125f00100004be0010000812002000007400400000580040412020008080d4e0010041880002001a5b80040014b600080008040008101298001001a5f80012034b70002404004000400f2fc00040221c80008026bf0001000c56000200108400040011c8000800022000100003200018896dc00031125b800050659f
|4=>0x1000080927d00010125fa00020210b3000004b6e60000092ccc000000c9900000a4bf200000c97e40000092fc80000125b8842003cbf1000214d7e20004218ac40008411788000024b70800c4496e08000000240e00000418140000c00
|_=>0
def pmB : Nat → Nat → Nat
|5,0=>0x10000000000
|6,0=>0x11109000000060004000004000000000010000c0000000000001a12000004000100001f1b0000190000010401041a001300040000040004032700040000000100000000041c0000060404
|7,0=>0x4f0a1566824e3638290507050c0c561e6735652b540c054952642c212a4637144b4c481648343c7a48311d3b7801455a7905470274557d2117423d287c770b10724a750d0e24766e70731d806f0c0a18150a536b2b692277200815058143250f516331060c1f26
|8,0=>0x6c5f5d597e8368333a925e898a8d5b413040627f328e578f6a85907b44604d7e888c50396d875c232e2e71868b32
|9,0=>0x3a6d5e58323e842f91613f
|10,0=>0x2d
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 8 (j % 128); fld (pmPalB (k / 32)) 39 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_219,9,runOps true dom_219 (0,roots_219) ops)] else [])++(if pm.testBit 1 then [(dom_222,8,runOps true dom_222 (0,roots_222) ops)] else [])++(if pm.testBit 2 then [(dom_91,7,runOps true dom_91 (0,roots_91) ops)] else [])++(if pm.testBit 3 then [(dzo_91_4,7,runOps true dzo_91_4 (0,roots_91) ops)] else [])++(if pm.testBit 4 then [(dom_215,8,runOps true dom_215 (0,roots_215) ops)] else [])++(if pm.testBit 5 then [(dom_205,7,runOps true dom_205 (0,roots_205) ops)] else [])++(if pm.testBit 6 then [(dom_155,8,runOps true dom_155 (0,roots_155) ops)] else [])++(if pm.testBit 7 then [(dom_159,9,runOps true dom_159 (0,roots_159) ops)] else [])++(if pm.testBit 8 then [(dom_214,6,runOps true dom_214 (0,roots_214) ops)] else [])++(if pm.testBit 9 then [(dzo_73_16,4,runOps true dzo_73_16 (0,roots_73) ops)] else [])++(if pm.testBit 10 then [(dom_221,8,runOps true dom_221 (0,roots_221) ops)] else [])++(if pm.testBit 11 then [(dom_218,6,runOps true dom_218 (0,roots_218) ops)] else [])++(if pm.testBit 12 then [(dzo_219_4,8,runOps true dzo_219_4 (0,roots_219) ops)] else [])++(if pm.testBit 13 then [(dom_207,8,runOps true dom_207 (0,roots_207) ops)] else [])++(if pm.testBit 14 then [(dom_83,4,runOps true dom_83 (0,roots_83) ops)] else [])++(if pm.testBit 15 then [(dom_73,4,runOps true dom_73 (0,roots_73) ops)] else [])++(if pm.testBit 16 then [(dzo_211_4,5,runOps true dzo_211_4 (0,roots_211) ops)] else [])++(if pm.testBit 17 then [(dzo_203_20,6,runOps true dzo_203_20 (0,roots_203) ops)] else [])++(if pm.testBit 18 then [(dzo_218_4,5,runOps true dzo_218_4 (0,roots_218) ops)] else [])++(if pm.testBit 19 then [(dom_151,6,runOps true dom_151 (0,roots_151) ops)] else [])++(if pm.testBit 20 then [(dom_90,4,runOps true dom_90 (0,roots_90) ops)] else [])++(if pm.testBit 21 then [(dzo_203_16,6,runOps true dzo_203_16 (0,roots_203) ops)] else [])++(if pm.testBit 22 then [(dzo_75_16,5,runOps true dzo_75_16 (0,roots_75) ops)] else [])++(if pm.testBit 23 then [(dom_157,6,runOps true dom_157 (0,roots_157) ops)] else [])++(if pm.testBit 24 then [(dzo_203_4,6,runOps true dzo_203_4 (0,roots_203) ops)] else [])++(if pm.testBit 25 then [(dom_217,7,runOps true dom_217 (0,roots_217) ops)] else [])++(if pm.testBit 26 then [(dzo_201_4,5,runOps true dzo_201_4 (0,roots_201) ops)] else [])++(if pm.testBit 27 then [(dom_158,6,runOps true dom_158 (0,roots_158) ops)] else [])++(if pm.testBit 28 then [(dom_211,6,runOps true dom_211 (0,roots_211) ops)] else [])++(if pm.testBit 29 then [(dom_203,6,runOps true dom_203 (0,roots_203) ops)] else [])++(if pm.testBit 30 then [(dom_216,4,runOps true dom_216 (0,roots_216) ops)] else [])++(if pm.testBit 31 then [(dom_209,4,runOps true dom_209 (0,roots_209) ops)] else [])++(if pm.testBit 32 then [(dom_210,5,runOps true dom_210 (0,roots_210) ops)] else [])++(if pm.testBit 33 then [(dom_150,5,runOps true dom_150 (0,roots_150) ops)] else [])++(if pm.testBit 34 then [(dom_199,5,runOps true dom_199 (0,roots_199) ops)] else [])++(if pm.testBit 35 then [(dom_220,5,runOps true dom_220 (0,roots_220) ops)] else [])++(if pm.testBit 36 then [(dom_213,5,runOps true dom_213 (0,roots_213) ops)] else [])++(if pm.testBit 37 then [(dom_75,5,runOps true dom_75 (0,roots_75) ops)] else [])++(if pm.testBit 38 then [(dzo_201_16,5,runOps true dzo_201_16 (0,roots_201) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_223 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_91_4_91 _ g hchk
    · exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_73_16_73 _ g hchk
    · exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_219_4_91 _ g hchk
    · exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · exact cpcs (by decide +kernel) lowS_73 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_211_4_83 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_203_20_73 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_218_4_90 _ g hchk
    · exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_203_16_73 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_75_16_73 _ g hchk
    · exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_203_4_75 _ g hchk
    · exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_201_4_73 _ g hchk
    · exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · exact cpcs (by decide +kernel) lowS_216 _ g hchk
    · exact cpcs (by decide +kernel) lowS_209 _ g hchk
    · exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · exact cpcs (by decide +kernel) lowS_220 _ g hchk
    · exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_201_16_73 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_219 9 s (0, roots_219) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_223 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_219 h

def symsG : List (List (Nat × Nat)) := [[(rowMask27, 7)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_223 == dom_223) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_223 goalM v ys) : RunD true dom_223 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_223 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 12 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 75 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 75 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 103 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 103 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8 : ∀ i, 0 ≤ i → i < 46 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 46 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9 : ∀ i, 0 ≤ i → i < 11 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 11 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 10) : ∀ i < NN s, bar true dom_223 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
  · exact z8 i (Nat.zero_le i) hi
  · exact z9 i (Nat.zero_le i) hi
  · exact z10 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_223 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 6 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 10) (h : RunD true dom_223 goalM s xsM) : False := by
  have hmin : 6 ≤ s := by
    have hl := run_len h; change 7 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_223 roots_223 goal_223 11 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_223

theorem lowS_223 : Lower true dom_223 roots_223 goal_223 11 := S_223.noCircuit

end B4

abbrev Cofactor := Nat × Nat × Nat
def Cofactor.domain (c : Cofactor) := c.1
def Cofactor.target (c : Cofactor) := c.2.1
def Cofactor.lower (c : Cofactor) := c.2.2

abbrev PaidExtra := Nat × Nat × Nat
def PaidExtra.kind (e : PaidExtra) := e.1
def PaidExtra.left (e : PaidExtra) := e.2.1
def PaidExtra.right (e : PaidExtra) := e.2.2

def PaidExtra.signal (d : Nat) (e : PaidExtra) : Nat :=
  opD d e.kind (xs256.getD e.left 0) (xs256.getD e.right 0)

def extraBank (d : Nat) : Option PaidExtra → List Nat
  | none => xs256
  | some e => e.signal d :: xs256

def extraCost : Option PaidExtra → Nat
  | none => 0
  | some _ => 1

def extraGood (d : Nat) : Option PaidExtra → Bool
  | none => true
  | some e => allowedB true e.kind && availB true d xs256 (xs256.getD e.left 0) &&
      availB true d xs256 (xs256.getD e.right 0)

theorem reach_trans {u d xs ys} {k : Nat} (hpre : NatReach u d xs k ys) :
    ∀ {p bs}, NatReach u d ys p bs → NatReach u d xs (k+p) bs := by
  intro p
  induction p with
  | zero => rintro bs rfl; simpa using hpre
  | succ n ih =>
    intro bs h
    obtain ⟨bb,a,b,o,ho,rfl,hr,ha,hb⟩ := h
    exact ⟨bb,a,b,o,ho,rfl,ih hr,ha,hb⟩

theorem lower_extra (c : Cofactor) (ex : Option PaidExtra) (he : extraGood c.domain ex = true)
    (hs : Lower true c.domain xs256 c.target c.lower) :
    Lower true c.domain (extraBank c.domain ex) c.target (c.lower - extraCost ex) := by
  cases ex with
  | none => exact hs
  | some e =>
    simp only [extraGood,Bool.and_eq_true] at he
    have hpre : NatReach true c.domain xs256 1 (e.signal c.domain :: xs256) :=
      ⟨xs256,_,_,e.kind,he.1.1,rfl,rfl,(availB_iff ..).1 he.1.2,(availB_iff ..).1 he.2⟩
    intro p bs hr ha
    have hb := hs (1+p) bs (reach_trans hpre hr) ha
    change c.lower - 1 ≤ p
    omega

abbrev LeafCertificate := Nat × Option PaidExtra × List (Nat × Nat × Nat)
def LeafCertificate.index (c : LeafCertificate) := c.1
def LeafCertificate.extra (c : LeafCertificate) := c.2.1
def LeafCertificate.singles (c : LeafCertificate) := c.2.2

def leafGood (cof : Nat → Cofactor) (target : Nat) (pool : List Nat) (L : Nat)
    (cert : LeafCertificate) : Bool :=
  let c := cof cert.index
  let xs := cert.singles
  let sub := extraBank c.domain cert.extra
  (target.testBit 0 == false) && pool.all (fun r => !r.testBit 0) &&
    (c.domain &&& mask256 == c.domain) && (target &&& c.domain == c.target &&& c.domain) &&
    (!isConstB mask256 target) && (!isConstB c.domain c.target) &&
    pool.all (availB true c.domain sub) && decide ((xs.map Prod.fst).Nodup) &&
    xs.all (fun e => isConstB c.domain e.1 && essOK mask256 (target &&& mask256)
      (pool.map (· &&& mask256)) e.1 e.2) && extraGood c.domain cert.extra &&
    decide (L ≤ c.lower - extraCost cert.extra + xs.length)

theorem leaf_sound (cof : Nat → Cofactor) (known : ∀ i, Lower true (cof i).domain
    xs256 (cof i).target (cof i).lower) {target pool L cert}
    (hc : leafGood cof target pool L cert = true) : Lower true mask256 pool target L := by
  simp only [leafGood, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ht,hr⟩,hd⟩,hh⟩,hn⟩,hns⟩,hs⟩,hnd⟩,hess⟩,he⟩,hl⟩ := hc
  have prior := lower_extra (cof cert.index) cert.extra he (known cert.index)
  have joined := lower_slice (d := mask256) (dSub := (cof cert.index).domain)
    (T := target) (TSub := (cof cert.index).target) (roots := pool)
    (by decide +kernel) (by decide +kernel) ht hr hd hd hh hn hns hs
    cert.singles hnd hess prior
  intro p bs hp ha
  exact Nat.le_trans hl (joined p bs hp ha)
def goalWord : Nat := 0xfffffffffffffffefffffffffffffffefffefffeffeeffeefefefafaeeccaa00

def co0 : Cofactor := ⟨0x5555555555555555555555555555555555555555555555555555555555555555, 0xfffffffffffffffcfffffffffffffffcfffcfffcffccffccfcfcf0f0cccc0000, 11⟩
set_option maxRecDepth 70000 in
set_option maxHeartbeats 0 in
theorem co0_sound : Lower true co0.domain xs256 co0.target co0.lower :=
  lower_iso (d1 := B0.dom_253) (roots1 := B0.roots_253) (T1 := B0.goal_253)
    [(rowMask0, 1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B0.lowS_253

def co1 : Cofactor := ⟨rowMask271, 0xfffffffffffffffafffffffffffffffafffafffaffaaffaafafafafaaa00aa00, 11⟩
set_option maxRecDepth 70000 in
set_option maxHeartbeats 0 in
theorem co1_sound : Lower true co1.domain xs256 co1.target co1.lower :=
  lower_iso (d1 := B1.dom_251) (roots1 := B1.roots_251) (T1 := B1.goal_251)
    [(rowMask32, 63), (rowMask16, 2), (rowMask28, 30), (rowMask27, 7), (rowMask39, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B1.lowS_251

def co2 : Cofactor := ⟨rowMask275, 0xffffffffffffffeeffffffffffffffeeffeeffeeffeeffeeeeeeaaaaeeccaa00, 11⟩
set_option maxRecDepth 70000 in
set_option maxHeartbeats 0 in
theorem co2_sound : Lower true co2.domain xs256 co2.target co2.lower :=
  lower_iso (d1 := B2.dom_247) (roots1 := B2.roots_247) (T1 := B2.goal_247)
    [(rowMask44, 127), (rowMask0, 1), (rowMask29, 4), (rowMask16, 2), (rowMask36, 28), (rowMask26, 32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B2.lowS_247

def co3 : Cofactor := ⟨rowMask155, 0xfffffffffffffefefffffffffffffefefefefefeeeeeeeeefefefafacccc0000, 11⟩
set_option maxRecDepth 70000 in
set_option maxHeartbeats 0 in
theorem co3_sound : Lower true co3.domain xs256 co3.target co3.lower :=
  lower_iso (d1 := B3.dom_247) (roots1 := B3.roots_247) (T1 := B3.goal_247)
    [(rowMask33, 31), (rowMask144, 62), (rowMask22, 12)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B3.lowS_247

def co4 : Cofactor := ⟨rowMask293, rowMask273, 11⟩
set_option maxRecDepth 70000 in
set_option maxHeartbeats 0 in
theorem co4_sound : Lower true co4.domain xs256 co4.target co4.lower :=
  lower_iso (d1 := B4.dom_223) (roots1 := B4.roots_223) (T1 := B4.goal_223)
    [] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B4.lowS_223

def co5 : Cofactor := ⟨0xffffffffffffffff0000000000000000ffffffffffffffff, 0xfffffffffffffffefffffffffffffffefefefafaeeccaa00fefefafaeeccaa00, 11⟩
set_option maxRecDepth 70000 in
set_option maxHeartbeats 0 in
theorem co5_sound : Lower true co5.domain xs256 co5.target co5.lower :=
  lower_iso (d1 := B5.dom_247) (roots1 := B5.roots_247) (T1 := B5.goal_247)
    [(rowMask39, 8), (rowMask46, 24), (rowMask220, 56)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5.lowS_247

def co6 : Cofactor := ⟨rowMask282, 0xfffffffffffafffafffffffffffafffafffafffaffaaffaafafafafaaa00aa00, 10⟩
set_option maxRecDepth 70000 in
set_option maxHeartbeats 0 in
theorem co6_sound : Lower true co6.domain xs256 co6.target co6.lower :=
  lower_iso (d1 := B6.dom_245) (roots1 := B6.roots_245) (T1 := B6.goal_245)
    [(rowMask220, 56), (rowMask39, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) B6.lowS_245

def cof : Nat → Cofactor
  | 0 => co0
  | 1 => co1
  | 2 => co2
  | 3 => co3
  | 4 => co4
  | 5 => co5
  | _ => co6
theorem cof_sound (i : Nat) : Lower true (cof i).domain xs256 (cof i).target (cof i).lower := by
  match i with
  | 0 => exact co0_sound
  | 1 => exact co1_sound
  | 2 => exact co2_sound
  | 3 => exact co3_sound
  | 4 => exact co4_sound
  | 5 => exact co5_sound
  | _ + 6 => exact co6_sound

def unpackEntry (pool : List Nat) (q : Nat) : Nat × LeafCertificate :=
  let part := fun (s bits : Nat) => (q >>> s) % (2^bits)
  let z := opD mask256 (part 0 2) (pool.getD (part 2 4) 0) (pool.getD (part 6 4) 0)
  let ex : Option PaidExtra := if q.testBit 13 then
    some ⟨part 14 2, part 16 3, part 19 3⟩ else none
  let single := fun (s : Nat) =>
    let v := part s 3
    let r := part (s+3) 8
    (xs256.getD v 0, r, r ||| (1 <<< v))
  let xs := (List.range (part 22 2)).map (fun i => single (24+11*i))
  (z, ⟨part 10 3, ex, xs⟩)
def terms0 : List (Nat × LeafCertificate) := ([
  0x40400040, 0x50400041, 0x50400042, 0x40400043, 0x40400080, 0x60400081, 0x60400082, 0x40400083, 0x1004000c0, 0x404000c1, 0x404000c2, 0x1004000c3,
  0x40400100, 0xc0400101, 0xc0400102, 0x40400103, 0x40400140, 0x100400141, 0x100400142, 0x40400143, 0x40400180, 0x200400181, 0x200400182, 0x40400183,
  0x404001c0, 0x4004001c1, 0x4004001c2, 0x404001c3, 0x81400484, 0xa1400485, 0xa1400486, 0x81400487, 0x814004c4, 0xc14004c5, 0xc14004c6, 0x814004c7,
  0x201400504, 0x81400505, 0x81400506, 0x201400507, 0x81400544, 0x181400545, 0x181400546, 0x81400547, 0x81400584, 0x201400585, 0x201400586, 0x81400587,
  0x814005c4, 0x4014005c5, 0x4014005c6, 0x814005c7, 0x1024008c8, 0x1424008c9, 0x1424008ca, 0x1024008cb, 0x102400908, 0x182400909, 0x18240090a, 0x10240090b,
  0x402400948, 0x102400949, 0x10240094a, 0x40240094b, 0x102400988, 0x302400989, 0x30240098a, 0x10240098b, 0x1024009c8, 0x4024009c9, 0x4024009ca, 0x1024009cb,
  0xb400d0c, 0x8b400d0d, 0x8b400d0e, 0xb400d0f, 0xb400d4c, 0x303400d4d, 0x303400d4e, 0xb400d4f, 0xb400d8c, 0x203400d8d, 0x203400d8e, 0xb400d8f,
  0xb400dcc, 0x403400dcd, 0x403400dce, 0xb400dcf, 0xd401150, 0x8d401151, 0xd401152, 0x8d401153, 0xe401590, 0x8e401591, 0xe401592, 0x8e401593,
  0xa0818019d0, 0x2020818019d1, 0x2020818019d2, 0xa0818019d3, 0xd401194, 0x225401195, 0x225401196, 0xd401197, 0xd4011d4, 0x4054011d5, 0x4054011d6, 0xd4011d7,
  0xe4015d8, 0xe4015db] : List Nat).map (unpackEntry xs256)
set_option maxRecDepth 70000 in
set_option maxHeartbeats 0 in
theorem terms0_checked : (terms0.all (fun e => leafGood cof goalWord (xs256 ++ [e.1]) 12 e.2)) = true := by decide +kernel
def terms1 : List (Nat × LeafCertificate) := ([
  0x407ea040, 0x507ea041, 0x507ea042, 0x407ea043, 0x407ea080, 0x607ea081, 0x607ea082, 0x407ea083, 0x1007ea0c0, 0x407ea0c1, 0x407ea0c2, 0x1007ea0c3,
  0x407ea100, 0xc07ea101, 0xc07ea102, 0x407ea103, 0x407ea140, 0x1007ea141, 0x1007ea142, 0x407ea143, 0x407ea180, 0x2007ea181, 0x2007ea182, 0x407ea183,
  0x407ea1c0, 0x4007ea1c1, 0x4007ea1c2, 0x407ea1c3, 0x407ea200, 0x2007ea201, 0x2007ea202, 0x407ea203, 0x817ea484, 0xa17ea485, 0xa17ea486, 0x817ea487,
  0x817ea4c4, 0xc17ea4c5, 0xc17ea4c6, 0x817ea4c7, 0x2017ea504, 0x817ea505, 0x817ea506, 0x2017ea507, 0x817ea544, 0x1817ea545, 0x1817ea546, 0x817ea547,
  0x817ea584, 0x2017ea585, 0x2017ea586, 0x817ea587, 0x817ea5c4, 0x4017ea5c5, 0x4017ea5c6, 0x817ea5c7, 0x817ea604, 0x2017ea605, 0x2017ea606, 0x817ea607,
  0x1027ea8c8, 0x1427ea8c9, 0x1427ea8ca, 0x1027ea8cb, 0x1027ea908, 0x1827ea909, 0x1827ea90a, 0x1027ea90b, 0x4027ea948, 0x1027ea949, 0x1027ea94a, 0x4027ea94b,
  0x1027ea988, 0x3027ea989, 0x3027ea98a, 0x1027ea98b, 0x1027ea9c8, 0x4027ea9c9, 0x4027ea9ca, 0x1027ea9cb, 0x1027eaa08, 0x3027eaa09, 0x3027eaa0a, 0x1027eaa0b,
  0xb7ead0c, 0x8b7ead0d, 0x8b7ead0e, 0xb7ead0f, 0xb7ead4c, 0x3037ead4d, 0x3037ead4e, 0xb7ead4f, 0xb7ead8c, 0x2037ead8d, 0x2037ead8e, 0xb7ead8f,
  0xb7eadcc, 0x4037eadcd, 0x4037eadce, 0xb7eadcf, 0xb7eae0c, 0x2037eae0d, 0x2037eae0e, 0xb7eae0f, 0xd7eb150, 0x8d7eb151, 0xd7eb152, 0x8d7eb153,
  0x1590, 0x1591, 0x1592, 0x1593, 0xa081beb9d0, 0x202081beb9d1, 0x202081beb9d2, 0xa081beb9d3, 0x1610, 0x1611, 0x1612, 0x1613,
  0xd7eb194, 0x2257eb195, 0x2257eb196, 0xd7eb197, 0xd7eb1d4, 0x4057eb1d5, 0x4057eb1d6, 0xd7eb1d7, 0xd7eb214, 0x2257eb215, 0x2257eb216, 0xd7eb217,
  0x15d8, 0x15d9, 0x15db] : List Nat).map (unpackEntry (xs256 ++ [rowMask51]))
set_option maxRecDepth 70000 in
set_option maxHeartbeats 0 in
theorem terms1_checked : (terms1.all (fun e => leafGood cof goalWord ((xs256 ++ [rowMask51]) ++ [e.1]) 11 e.2)) = true := by decide +kernel
def terms2 : List (Nat × LeafCertificate) := ([
  0x407e6040, 0x507e6041, 0x507e6042, 0x407e6043, 0x407e6080, 0x607e6081, 0x607e6082, 0x407e6083, 0x1007e60c0, 0x407e60c1, 0x407e60c2, 0x1007e60c3,
  0x407e6100, 0xc07e6101, 0xc07e6102, 0x407e6103, 0x407e6140, 0x1007e6141, 0x1007e6142, 0x407e6143, 0x407e6180, 0x2007e6181, 0x2007e6182, 0x407e6183,
  0x407e61c0, 0x4007e61c1, 0x4007e61c2, 0x407e61c3, 0x407e6200, 0x2007e6201, 0x2007e6202, 0x407e6203, 0x817e6484, 0xa17e6485, 0xa17e6486, 0x817e6487,
  0x817e64c4, 0xc17e64c5, 0xc17e64c6, 0x817e64c7, 0x2017e6504, 0x817e6505, 0x817e6506, 0x2017e6507, 0x817e6544, 0x1817e6545, 0x1817e6546, 0x817e6547,
  0x817e6584, 0x2017e6585, 0x2017e6586, 0x817e6587, 0x817e65c4, 0x4017e65c5, 0x4017e65c6, 0x817e65c7, 0x817e6604, 0x2017e6605, 0x2017e6606, 0x817e6607,
  0x1027e68c8, 0x1427e68c9, 0x1427e68ca, 0x1027e68cb, 0x1027e6908, 0x1827e6909, 0x1827e690a, 0x1027e690b, 0x4027e6948, 0x1027e6949, 0x1027e694a, 0x4027e694b,
  0x1027e6988, 0x3027e6989, 0x3027e698a, 0x1027e698b, 0x1027e69c8, 0x4027e69c9, 0x4027e69ca, 0x1027e69cb, 0x1027e6a08, 0x3027e6a09, 0x3027e6a0a, 0x1027e6a0b,
  0xb7e6d0c, 0x8b7e6d0d, 0x8b7e6d0e, 0xb7e6d0f, 0xb7e6d4c, 0x3037e6d4d, 0x3037e6d4e, 0xb7e6d4f, 0xb7e6d8c, 0x2037e6d8d, 0x2037e6d8e, 0xb7e6d8f,
  0xb7e6dcc, 0x4037e6dcd, 0x4037e6dce, 0xb7e6dcf, 0xb7e6e0c, 0x2037e6e0d, 0x2037e6e0e, 0xb7e6e0f, 0xd7e7150, 0x8d7e7151, 0xd7e7152, 0x8d7e7153,
  0x1590, 0x1591, 0x1592, 0x1593, 0xa081be79d0, 0x202081be79d1, 0x202081be79d2, 0xa081be79d3, 0xa081be7a10, 0x202081be7a11, 0x202081be7a12, 0xa081be7a13,
  0xd7e7194, 0x2257e7195, 0x2257e7196, 0xd7e7197, 0xd7e71d4, 0x4057e71d5, 0x4057e71d6, 0xd7e71d7, 0xd7e7214, 0x2257e7215, 0x2257e7216, 0xd7e7217,
  0x15d8, 0x15da, 0x15db] : List Nat).map (unpackEntry (xs256 ++ [rowMask151]))
set_option maxRecDepth 70000 in
set_option maxHeartbeats 0 in
theorem terms2_checked : (terms2.all (fun e => leafGood cof goalWord ((xs256 ++ [rowMask151]) ++ [e.1]) 11 e.2)) = true := by decide +kernel

theorem lower_step {xs : List Nat} {T L : Nat}
    (hmask : ∀ x ∈ xs, x &&& mask256 = x)
    (hbits : xs.all (fun x => !x.testBit 0) = true)
    (htmask : T &&& mask256 = T) (htbit : T.testBit 0 = false)
    (hna : availB true mask256 xs T = false)
    (next : ∀ a ∈ xs, ∀ b ∈ xs, ∀ op : Fin 4,
      opD mask256 op.val a b ≠ 0 → opD mask256 op.val a b ∉ xs →
      Lower true mask256 (xs ++ [opD mask256 op.val a b]) T L) :
    Lower true mask256 xs T (L+1) := by
  intro p bank hr ha
  have hna' : ¬ Avail true mask256 xs T := by
    intro hav
    have := (availB_iff _ _ _ _).2 hav
    simp_all
  have hnc : ¬ IsConst mask256 T := fun hc => hna' (Or.inl hc)
  have hd : mask256 &&& mask256 = mask256 := Nat.and_self _
  obtain ⟨s, ws, hsp, hnd, sub, run⟩ := reach_to_run hd (by decide) htbit hbits hnc hr ha
  rw [htmask] at run
  have sub' : ∀ w ∈ ws, w ∈ xs := by
    intro w hw
    obtain ⟨x,hx,e⟩ := List.mem_map.1 (sub w hw)
    change x &&& mask256 = w at e
    rw [hmask x hx] at e
    exact e ▸ hx
  suffices hs : L + 1 ≤ s by omega
  clear sub hsp hnd
  induction run using Run.fold with
  | done => exact False.elim <| hna' (Or.inr (Or.inl ⟨T,sub' _ (by simp),rfl⟩))
  | perm hp _ ih => exact ih (fun w hw => sub' w (hp.mem_iff.1 hw))
  | @two s a b r op ka kb hop h0 _ _ child ih =>
    let z := opD mask256 op a b
    have ha := sub' a List.mem_cons_self
    have hb := sub' b (List.mem_cons_of_mem _ List.mem_cons_self)
    have rest : ∀ w ∈ kept ka a (kept kb b r), w ∈ xs := by
      intro w hw
      rw [mem_kept,mem_kept] at hw
      rcases hw with ⟨_,rfl⟩ | ⟨_,rfl⟩ | hw
      · exact ha
      · exact hb
      · exact sub' w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw))
    by_cases hz : z ∈ xs
    · have := ih fun w hw => (List.mem_cons.1 hw).elim (fun e => e.symm ▸ hz) (rest w)
      omega
    · have hop4 : op < 4 := by
        rcases allowed_cases hop with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> decide
      have lower := next a ha b hb ⟨op,hop4⟩ h0 hz
      have av : ∀ w ∈ z :: kept ka a (kept kb b r), Avail true mask256 (xs ++ [z]) w := by
        intro w hw
        refine Or.inr (Or.inl ⟨w,?_,rfl⟩)
        rcases List.mem_cons.1 hw with rfl | hw
        · simp
        · exact List.mem_append_left _ (rest w hw)
      obtain ⟨q,bank,hq,hT,hcost⟩ := contraction hd hd hnc child
        (roots := xs ++ [z]) (p := 0) (bank := xs ++ [z]) rfl av
      have bound := lower q bank hq hT
      omega

def nodeGood (pool : List Nat) (terms : List (Nat × LeafCertificate)) (deeper : List Nat) : Bool :=
  pool.all (fun w => w &&& mask256 == w) && pool.all (fun w => !w.testBit 0) &&
    (!availB true mask256 pool goalWord) &&
    pool.all (fun a => pool.all (fun b => (List.range 4).all (fun op =>
      let z := opD mask256 op a b
      decide (z = 0 ∨ z ∈ pool ∨ z ∈ terms.map Prod.fst ∨ z ∈ deeper))))

theorem node_sound (pool : List Nat) (L : Nat) (terms : List (Nat × LeafCertificate)) (more : List Nat)
    (hg : nodeGood pool terms more = true)
    (ht : terms.all (fun e => leafGood cof goalWord (pool ++ [e.1]) L e.2) = true)
    (hm : ∀ z ∈ more, Lower true mask256 (pool ++ [z]) goalWord L) :
    Lower true mask256 pool goalWord (L+1) := by
  simp only [nodeGood, Bool.and_eq_true, Bool.not_eq_true'] at hg
  obtain ⟨⟨⟨hmask,hbits⟩,hne⟩,hc⟩ := hg
  apply lower_step (fun x hx => beq_iff_eq.mp (List.all_eq_true.mp hmask x hx)) hbits
    (by decide +kernel) (by decide +kernel) hne
  intro a ha b hb op hz hn
  have opts := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hc a ha) b hb)
    op.val (List.mem_range.mpr op.isLt)
  simp only [decide_eq_true_eq] at opts
  rcases opts with h | h | h | h
  · exact (hz h).elim
  · exact (hn h).elim
  · obtain ⟨entry,he,hv⟩ := List.mem_map.mp h
    have hsol := leaf_sound cof cof_sound (List.all_eq_true.mp ht entry he)
    rw [hv] at hsol
    exact hsol
  · exact hm _ h
set_option maxRecDepth 70000 in
set_option maxHeartbeats 0 in
theorem step1 : Lower true mask256 (xs256 ++ [rowMask51]) goalWord 12 :=
  node_sound _ 11 terms1 [] (by decide +kernel) terms1_checked (by simp)
set_option maxRecDepth 70000 in
set_option maxHeartbeats 0 in
theorem step2 : Lower true mask256 (xs256 ++ [rowMask151]) goalWord 12 :=
  node_sound _ 11 terms2 [] (by decide +kernel) terms2_checked (by simp)
set_option maxRecDepth 70000 in
set_option maxHeartbeats 0 in
theorem newLower : Lower true mask256 xs256 goalWord 13 := by
  apply node_sound _ 12 terms0 [rowMask51, rowMask151] (by decide +kernel) terms0_checked
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl
  · exact step1
  · exact step2

def targetGraph (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)

set_option maxRecDepth 70000 in
set_option maxHeartbeats 0 in
theorem goal_eq_f : ∀ r : Fin 256, goalWord.testBit r.val = targetGraph (pt8 r.val) := by decide +kernel

theorem lb_with_not (gates : List Gate) (o : Nat)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = targetGraph x)
    (hhas : ∃ g ∈ gates, isNotGate g = true) : 14 ≤ gates.length := by
  obtain ⟨g, hg, hgn⟩ := hhas
  have hout : (execN gates xs256).getD o 0 &&& mask256 = goalWord &&& mask256 := by
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
  have hL := newLower p bank hr (avail_of_eq hout hav_out)
  have hlt := countP_not_lt hg hgn
  omega

def witness : List Gate := [⟨.or, [3, 5]⟩, ⟨.or, [0, 7]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [1, 7]⟩, ⟨.and, [4, 11]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [2, 13]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [15, 3]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [16, 17]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [19, 14]⟩, ⟨.or, [20, 18]⟩]

theorem witnessBasis : ∀ g ∈ witness, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  simp [witness]

set_option maxRecDepth 70000 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool, Circuit.eval ⟨witness, 21⟩ (List.ofFn x) = targetGraph x := by
  decide +kernel

end PEqualNP.Outside.L_meta_30318_aux

open PEqualNP.Outside.L_meta_30318_aux PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_30318 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _ computes
  by_cases hn : ∃ g ∈ gates, g.op = GateOp.not
  · obtain ⟨g, hg, hop⟩ := hn
    have fan : ∀ t ∈ gates, t.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ t.inputs.length ≤ 2 := by
      intro t ht
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using legal t ht
    have bound := lb_with_not gates o fan computes ⟨g, hg, by simp [isNotGate, hop]⟩
    exact ⟨witness, 21, witnessBasis, bound, witnessCorrect⟩
  · refine ⟨gates, o, ?_, le_rfl, computes⟩
    intro g hg
    obtain ⟨hop, fan⟩ := legal g hg
    refine ⟨?_, fan⟩
    rcases hop with ha | ho | hnot
    · exact Or.inl ha
    · exact Or.inr ho
    · exact (hn ⟨g, hg, hnot⟩).elim
