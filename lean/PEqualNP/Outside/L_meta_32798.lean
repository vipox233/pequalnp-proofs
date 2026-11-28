import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_32798_aux
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
theorem avail_mono {d:Nat} {bank:List Nat} {w:Nat} (h : Avail false d bank w) :
    Avail true d bank w:=by
  rcases h with h | h | ⟨h,_⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · contradiction
theorem reach_up {d:Nat} {roots:List Nat} {p bank} (h:NatReach false d roots p bank) :
    NatReach true d roots p bank:=by
  induction p generalizing bank with
  | zero=>exact h
  | succ p ih =>
    obtain ⟨b,a,c,op,hop,rfl,hrb,ha,hc⟩:=h
    have hop' : allowedB true op = true:=by
      rcases allowed_cases hop with rfl | rfl | ⟨hc,_⟩ | ⟨hc,_⟩ <;> first | decide | contradiction
    exact ⟨b,a,c,op,hop',rfl,ih hrb,avail_mono ha,avail_mono hc⟩
theorem lower_down {d:Nat} {roots:List Nat} {T L:Nat} (h : Lower true d roots T L) :
    Lower false d roots T L:=fun p bank hr ha=>h p bank (reach_up hr) (avail_mono ha)
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
theorem andD_mask (d a b:Nat) : andD d (a&&&d) (b&&&d) = andD d a b:=by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [andD,Nat.testBit_and]
  cases d.testBit i <;> simp
theorem orD_mask (d a b:Nat) : orD d (a&&&d) (b&&&d) = orD d a b:=by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [orD,Nat.testBit_and,Nat.testBit_or]
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
  cases b
  · simp [kept]
  · simp [kept,List.countP_cons]
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
theorem perm_erase_two {α : Type} [DecidableEq α] {rest:List α} {a' c' : α}
    (hnd : rest.Nodup) (hne : a' ≠ c') :
    rest.Perm (kept (decide (a' ∈ rest)) a' (kept (decide (c' ∈ rest)) c' ((rest.erase a').erase c'))):=by
  refine (List.perm_ext_iff_of_nodup hnd (nodup_kept _ a' _ (nodup_kept _ c' _ ((hnd.erase a').erase c')
    ((hnd.erase a').not_mem_erase)) (by
      rw [mem_kept]; rintro (⟨_,h⟩ | h)
      · exact hne h
      · exact hnd.not_mem_erase (List.mem_of_mem_erase h)))).2 ?_
  intro x
  rw [mem_kept,mem_kept,(hnd.erase a').mem_erase_iff,hnd.mem_erase_iff]
  by_cases hxa : x = a' <;> by_cases hxc : x = c' <;> by_cases hxr : x ∈ rest <;> simp_all
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
      have hrest_perm : rest.Perm (kept ka a' (kept kb c' tail)) :=
        perm_erase_two hrest_nd hne_ac
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
theorem lower_base {u:Bool} {d:Nat} {roots:List Nat} {T:Nat} (h : availB u d roots T = false) :
    Lower u d roots T 1:=by
  intro p bank hr ha
  cases p with
  | zero =>
    dsimp only [NatReach] at hr; rw [hr] at ha
    have ht:=(availB_iff u d roots T).2 ha
    rw [h] at ht; contradiction
  | succ p=>omega
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
theorem lower_ess_count {u:Bool} {d T:Nat} {roots:List Nat}
    (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (hT0 : T.testBit 0 = false) (hR0 : roots.all (fun r=>!r.testBit 0) = true)
    (hnc : isConstB d T = false)
    (singles:List (Nat × Nat × Nat))
    (hs_nd : (singles.map Prod.fst).Nodup)
    (hs_ok : singles.all (fun e=>essOK d (T&&&d) (roots.map (·&&&d)) e.1 e.2) = true) :
    Lower u d roots T (singles.length - 1):=by
  have hnc' : ¬ IsConst d T:=fun h=>by rw [(isConstB_iff _ _).2 h] at hnc; contradiction
  intro p bank hr ha
  obtain ⟨s,ws,hs_le,_,hws_sub,hrun⟩:=reach_to_run hd hd0 hT0 hR0 hnc' hr ha
  have hsin_mem : ∀ a ∈ singles.map Prod.fst,a ∈ ws:=by
    intro a ha
    obtain ⟨⟨a',r1,r2⟩,hm,rfl⟩:=List.mem_map.1 ha
    have hok:=List.all_eq_true.1 hs_ok (a',r1,r2) hm
    simp only [essOK,pairOK,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at hok
    obtain ⟨⟨⟨hr1,hr2⟩,hdiff⟩,hiso⟩:=hok
    by_contra hnot
    apply hdiff
    apply runD_bits hd hrun r1 r2 hr1 hr2
    intro w hw
    rcases hiso w (hws_sub w hw) with rfl | heq
    · exact absurd hw hnot
    · exact heq
  have hcnt:=countP_ge_sublist (fun _=>true) hs_nd hsin_mem (fun _ _=>rfl)
  simp only [List.length_map,List.countP_true] at hcnt
  have hlen:=run_len hrun
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
theorem range_split {P:Nat → Prop} {lo mid hi:Nat}
    (h1 : ∀ i,lo ≤ i → i < mid → P i) (h2 : ∀ i,mid ≤ i → i < hi → P i) :
    ∀ i,lo ≤ i → i < hi → P i:=fun i hlo hhi =>
  if h : i < mid then h1 i hlo h else h2 i (Nat.le_of_not_lt h) hhi
def fld (T w i:Nat):Nat :=
  (T >>> (w * i))&&&(if w==6 then 63 else if w==11 then 2047 else if w==13 then 8191 else if w==14 then 16383 else if w==19 then 524287 else if w==20 then 1048575 else if w==32 then 4294967295 else if w==52 then 4503599627370495 else if w==256 then mask256 else 2 ^ w - 1)
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
theorem directSplit_to_circuit (f : (Fin 8 → Bool) → Bool) (T lb:Nat)
    (hT : ∀ r : Fin 256,T.testBit r.val = f (pt8 r.val))
    (hS : Lower true mask256 xs256 T (lb - 1))
    (hM : Lower false mask256 xs256 T lb) :
    ∀ t : ℕ,HasCircuitSize 8 f t → lb ≤ t:=by
  rintro t ⟨C,hfan,hsz,hev⟩
  have hout : (execN C.gates xs256).getD C.output 0&&&mask256 = T&&&mask256:=by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and,Nat.testBit_and,mask256_bit]
    by_cases hlt : r < 256
    · simp only [hlt,decide_true,Bool.and_true]
      have h1:=execN_bit C.gates xs256 r hlt (fun g hg=>(hfan g hg).1)
      have h2:=congrArg (fun l=>l.getD C.output false) h1
      rw [xs256_bits ⟨r,hlt⟩] at h2
      have hgd : ((execN C.gates xs256).map (·.testBit r)).getD C.output false =
          ((execN C.gates xs256).getD C.output 0).testBit r:=by
        simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
        cases (execN C.gates xs256)[C.output]? with | none=>simp | some v=>rfl
      rw [hgd] at h2
      have h3 : (C.wires (List.ofFn (pt8 r))).getD C.output false = f (pt8 r):=hev (pt8 r)
      exact h2.trans (h3.trans (hT ⟨r,hlt⟩).symm)
    · simp [hlt]
  by_cases hhas : ∃ g ∈ C.gates,isNotGate g = true
  · obtain ⟨g,hg,hgn⟩:=hhas
    have hsup0 : ∀ v ∈ xs256,Avail true mask256 xs256 v:=fun v hv=>Or.inr (Or.inl ⟨v,hv,rfl⟩)
    obtain ⟨p,bank,hp,hr,hsup⟩:=execN_reach true C.gates xs256 hfan (fun h=>Bool.noConfusion h) 0 xs256 xs256 rfl hsup0
    have hav_out : Avail true mask256 bank ((execN C.gates xs256).getD C.output 0):=by
      by_cases hi : C.output < (execN C.gates xs256).length
      · exact hsup _ (getD_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
    have hL:=hS p bank hr (avail_of_eq hout hav_out)
    have hlt:=countP_not_lt hg hgn
    have : C.gates.length ≤ t:=hsz
    omega
  · push Not at hhas
    have hmono : ∀ g ∈ C.gates,isNotGate g = false:=fun g hg=>Bool.eq_false_iff.2 (hhas g hg)
    have hsup0 : ∀ v ∈ xs256,Avail false mask256 xs256 v:=fun v hv=>Or.inr (Or.inl ⟨v,hv,rfl⟩)
    obtain ⟨p,bank,hp,hr,hsup⟩:=execN_reach false C.gates xs256 hfan (fun _=>hmono) 0 xs256 xs256 rfl hsup0
    have hav_out : Avail false mask256 bank ((execN C.gates xs256).getD C.output 0):=by
      by_cases hi : C.output < (execN C.gates xs256).length
      · exact hsup _ (getD_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
    have hL:=hM p bank hr (avail_of_eq hout hav_out)
    have hle:=List.countP_le_length (p:=fun y=>!isNotGate y) (l:=C.gates)
    have : C.gates.length ≤ t:=hsz
    omega
def dom_45 : Nat := 0x333300003333
def goal_45 : Nat := 0xfafafafaaa00aa00fafafafaaa00aa00fafafafaaa00aa00fafafafaaa00aa00
def roots_45 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xfafafafaaa00aa00fafafafaaa00aa00fafafafaaa00aa00fafafafaaa00aa00
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfafafafaaa00aa00fafafafaaa00aa00fafafafaaa00aa00fafafafaaa00aa00
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfefefafaeeccaa00fefefafaeeccaa00fefefafaeeccaa00fefefafaeeccaa00
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_75 : Nat := 0xf0f0000000000000f0f
def goal_75 : Nat := 0xeeeeeeeeeeeeeeeeaa00aa00aa00aa00eeeeeeeeeeeeeeeeaa00aa00aa00aa00
def roots_75 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_77 : Nat := 0x33330000000000003333
def goal_77 : Nat := 0xfafafafafafafafaaa00aa00aa00aa00fafafafafafafafaaa00aa00aa00aa00
def roots_77 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_79 : Nat := 0xffff000000000000ffff
def goal_79 : Nat := 0xfefefefefefefefeaa00aa00aa00aa00fefefefefefefefeaa00aa00aa00aa00
def roots_79 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_82 : Nat := 0x500050000000000050005
def goal_82 : Nat := 0xffffccccffffcccccccc0000cccc0000ffffccccffffcccccccc0000cccc0000
def roots_82 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_83 : Nat := 0xf000f00000000000f000f
def goal_83 : Nat := 0xffffeeeeffffeeeecccc0000cccc0000ffffeeeeffffeeeecccc0000cccc0000
def roots_83 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_86 : Nat := 0x5500550000000000550055
def goal_86 : Nat := 0xfffffcfcfffffcfccccc0000cccc0000fffffcfcfffffcfccccc0000cccc0000
def roots_86 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_87 : Nat := 0xff00ff0000000000ff00ff
def goal_87 : Nat := 0xfffffefefffffefecccc0000cccc0000fffffefefffffefecccc0000cccc0000
def roots_87 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_89 : Nat := 0x30303030000000003030303
def goal_89 : Nat := 0xffffaaaaffffaaaaaa00aa00aa00aa00ffffaaaaffffaaaaaa00aa00aa00aa00
def roots_89 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffffeeeeffffeeeeeeccaa00eeccaa00ffffeeeeffffeeeeeeccaa00eeccaa00
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xfffffefefffffefeeeccaa00eeccaa00fffffefefffffefeeeccaa00eeccaa00
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_102 : Nat := 0x55000000550000005500000055
def goal_102 : Nat := 0xfcfcfcfcfcfcfcfcf0f0f0f000000000fcfcfcfcfcfcfcfcf0f0f0f000000000
def roots_102 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_103 : Nat := 0xff000000ff000000ff000000ff
def goal_103 : Nat := 0xfefefefefefefefefafafafa00000000fefefefefefefefefafafafa00000000
def roots_103 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xeeeeeeeeeeeeeeeeaaaaaaaaaa00aa00eeeeeeeeeeeeeeeeaaaaaaaaaa00aa00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xfafafafafafafafafafafafaaa00aa00fafafafafafafafafafafafaaa00aa00
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xfefefefefefefefefafafafaaa00aa00fefefefefefefefefafafafaaa00aa00
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_116 : Nat := 0x110011001100110011001100110011
def goal_116 : Nat := 0xfffff0f0fffff0f0f0f0f0f000000000fffff0f0fffff0f0f0f0f0f000000000
def roots_116 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffffcfcfffffcfcfcfcf0f0cccc0000fffffcfcfffffcfcfcfcf0f0cccc0000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfffffefefffffefefefefafacccc0000fffffefefffffefefefefafacccc0000
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_139 : Nat := 0xf0f00000000000000000000000000000f0f
def goal_139 : Nat := 0xffccffccffccffccffccffccffccffccaa00aa00aa00aa00aa00aa00aa00aa00
def roots_139 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_141 : Nat := 0x333300000000000000000000000000003333
def goal_141 : Nat := 0xfff0fff0fff0fff0fff0fff0fff0fff0aa00aa00aa00aa00aa00aa00aa00aa00
def roots_141 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_143 : Nat := 0xffff0000000000000000000000000000ffff
def goal_143 : Nat := 0xfffcfffcfffcfffcfffcfffcfffcfffcaa00aa00aa00aa00aa00aa00aa00aa00
def roots_143 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_146 : Nat := 0x5000500000000000000000000000000050005
def goal_146 : Nat := 0xffffccccffffccccffffccccffffcccccccc0000cccc0000cccc0000cccc0000
def roots_146 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_150 : Nat := 0x55005500000000000000000000000000550055
def goal_150 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfccccc0000cccc0000cccc0000cccc0000
def roots_150 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_153 : Nat := 0x303030300000000000000000000000003030303
def goal_153 : Nat := 0xffffff00ffffff00ffffff00ffffff00aa00aa00aa00aa00aa00aa00aa00aa00
def roots_153 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_154 : Nat := 0x505050500000000000000000000000005050505
def goal_154 : Nat := 0xffffffccffffffccffffffccffffffcccccc0000cccc0000cccc0000cccc0000
def roots_154 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffffffccffffffccffffffccffffffcceeccaa00eeccaa00eeccaa00eeccaa00
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_157 : Nat := 0x3333333300000000000000000000000033333333
def goal_157 : Nat := 0xfffffff0fffffff0fffffff0fffffff0aa00aa00aa00aa00aa00aa00aa00aa00
def roots_157 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_158 : Nat := 0x5555555500000000000000000000000055555555
def goal_158 : Nat := 0xfffffffcfffffffcfffffffcfffffffccccc0000cccc0000cccc0000cccc0000
def roots_158 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_159 : Nat := 0xffffffff000000000000000000000000ffffffff
def goal_159 : Nat := 0xfffffffcfffffffcfffffffcfffffffceeccaa00eeccaa00eeccaa00eeccaa00
def roots_159 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_164 : Nat := 0x110000001100000000000000000000001100000011
def goal_164 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f000000000f0f0f0f000000000
def roots_164 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_165 : Nat := 0x330000003300000000000000000000003300000033
def goal_165 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0fafafafa00000000fafafafa00000000
def roots_165 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_166 : Nat := 0x550000005500000000000000000000005500000055
def goal_166 : Nat := 0xfffffffffcfcfcfcfffffffffcfcfcfcf0f0f0f000000000f0f0f0f000000000
def roots_166 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_167 : Nat := 0xff000000ff0000000000000000000000ff000000ff
def goal_167 : Nat := 0xfffffffffcfcfcfcfffffffffcfcfcfcfafafafa00000000fafafafa00000000
def roots_167 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffffffffffccffccffffffffffccffccaaaaaaaaaa00aa00aaaaaaaaaa00aa00
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_172 : Nat := 0x11110000111100000000000000000000111100001111
def goal_172 : Nat := 0xfffffffffff0fff0fffffffffff0fff0f0f0f0f000000000f0f0f0f000000000
def roots_172 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xfffffffffff0fff0fffffffffff0fff0fafafafaaa00aa00fafafafaaa00aa00
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_174 : Nat := 0x55550000555500000000000000000000555500005555
def goal_174 : Nat := 0xfffffffffffcfffcfffffffffffcfffcf0f0f0f000000000f0f0f0f000000000
def roots_174 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xfffffffffffcfffcfffffffffffcfffcfafafafaaa00aa00fafafafaaa00aa00
def roots_175 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_178 : Nat := 0x500050005000500000000000000000005000500050005
def goal_178 : Nat := 0xffffffffffffccccffffffffffffcccccccc0000cccc0000cccc0000cccc0000
def roots_178 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_180 : Nat := 0x1100110011001100000000000000000011001100110011
def goal_180 : Nat := 0xfffffffffffff0f0fffffffffffff0f0f0f0f0f000000000f0f0f0f000000000
def roots_180 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_181 : Nat := 0x3300330033003300000000000000000033003300330033
def goal_181 : Nat := 0xfffffffffffff0f0fffffffffffff0f0fafafafa00000000fafafafa00000000
def roots_181 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_182 : Nat := 0x5500550055005500000000000000000055005500550055
def goal_182 : Nat := 0xfffffffffffffcfcfffffffffffffcfcfcfcf0f0cccc0000fcfcf0f0cccc0000
def roots_182 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def goal_183 : Nat := 0xfffffffffffffcfcfffffffffffffcfcfefefafacccc0000fefefafacccc0000
def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303
def goal_185 : Nat := 0xffffffffffffff00ffffffffffffff00aaaaaaaaaa00aa00aaaaaaaaaa00aa00
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def goal_186 : Nat := 0xffffffffffffffccffffffffffffffcccccc0000cccc0000cccc0000cccc0000
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffffffffffccffffffffffffffcceeeeaaaaeeccaa00eeeeaaaaeeccaa00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_188 : Nat := 0x111111111111111100000000000000001111111111111111
def goal_188 : Nat := 0xfffffffffffffff0fffffffffffffff0f0f0f0f000000000f0f0f0f000000000
def roots_188 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333
def goal_189 : Nat := 0xfffffffffffffff0fffffffffffffff0fafafafaaa00aa00fafafafaaa00aa00
def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xfffffffffffffffcfffffffffffffffcfcfcf0f0cccc0000fcfcf0f0cccc0000
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffffffffffcfffffffffffffffcfefefafaeeccaa00fefefafaeeccaa00
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_195 : Nat := 0xf000000000000000f000000000000000f000000000000000f
def goal_195 : Nat := 0xeeeeeeeeeeeeeeeecccccccccccccccceeeeeeeeeeeeeeee0000000000000000
def roots_195 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_197 : Nat := 0x33000000000000003300000000000000330000000000000033
def goal_197 : Nat := 0xfafafafafafafafaf0f0f0f0f0f0f0f0fafafafafafafafa0000000000000000
def roots_197 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_199 : Nat := 0xff00000000000000ff00000000000000ff00000000000000ff
def goal_199 : Nat := 0xfefefefefefefefefcfcfcfcfcfcfcfcfefefefefefefefe0000000000000000
def roots_199 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303
def goal_201 : Nat := 0xffaaffaaffaaffaaff00ff00ff00ff00aaaaaaaaaaaaaaaaaa00aa00aa00aa00
def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_202 : Nat := 0x505000000000000050500000000000005050000000000000505
def goal_202 : Nat := 0xffccffccffccffccffccffccffccffcccccccccccccccccc0000000000000000
def roots_202 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffeeffeeffeeffeeffccffccffccffcceeeeeeeeeeeeeeeeaa00aa00aa00aa00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := 0x3333000000000000333300000000000033330000000000003333
def goal_205 : Nat := 0xfffafffafffafffafff0fff0fff0fff0fafafafafafafafaaa00aa00aa00aa00
def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_206 : Nat := 0x5555000000000000555500000000000055550000000000005555
def goal_206 : Nat := 0xfffcfffcfffcfffcfffcfffcfffcfffcfcfcfcfcfcfcfcfc0000000000000000
def roots_206 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xfffefffefffefffefffcfffcfffcfffcfefefefefefefefeaa00aa00aa00aa00
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_209 : Nat := 0x30003000000000003000300000000000300030000000000030003
def goal_209 : Nat := 0xffffaaaaffffaaaaffff0000ffff0000ffffaaaaffffaaaa0000000000000000
def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_210 : Nat := 0x50005000000000005000500000000000500050000000000050005
def goal_210 : Nat := 0xffffccccffffccccffffccccffffccccffffccccffffcccccccc0000cccc0000
def roots_210 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffeeeeffffeeeeffffccccffffccccffffeeeeffffeeeecccc0000cccc0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcfffffcfcfffffcfccccc0000cccc0000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffefefffffefefffffcfcfffffcfcfffffefefffffefecccc0000cccc0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_216 : Nat := 0x1010101000000000101010100000000010101010000000001010101
def goal_216 : Nat := 0xffffff00ffffff00ffffff00ffffff00ffff0000ffff00000000000000000000
def roots_216 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def goal_217 : Nat := 0xffffffaaffffffaaffffff00ffffff00ffffaaaaffffaaaaaa00aa00aa00aa00
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffccffffffccffffffccffffffccffffccccffffcccccccc0000cccc0000
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffeeffffffeeffffffccffffffccffffeeeeffffeeeeeeccaa00eeccaa00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffcfffffffcfffffffcfffffffcfffffcfcfffffcfccccc0000cccc0000
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffefffffffefffffffcfffffffcfffffefefffffefeeeccaa00eeccaa00
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_226 : Nat := 0x500000005000000050000000500000005000000050000000500000005
def goal_226 : Nat := 0xffffffffccccccccffffffffcccccccccccccccccccccccc0000000000000000
def roots_226 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffeeeeeeeeffffffffcccccccceeeeeeeeeeeeeeeeaaaaaaaa00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_228 : Nat := 0x1100000011000000110000001100000011000000110000001100000011
def goal_228 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000
def roots_228 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033
def goal_229 : Nat := 0xfffffffffafafafafffffffff0f0f0f0fafafafafafafafafafafafa00000000
def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffcfcfcfcfffffffffcfcfcfcfcfcfcfcfcfcfcfcf0f0f0f000000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xfffffffffefefefefffffffffcfcfcfcfefefefefefefefefafafafa00000000
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffaaffaaffffffffff00ff00aaaaaaaaaaaaaaaaaaaaaaaaaa00aa00
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffccffccffffffffffccffcccccccccccccccccc0000000000000000
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffeeffeeffffffffffccffcceeeeeeeeeeeeeeeeaaaaaaaaaa00aa00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_236 : Nat := 0x111100001111000011110000111100001111000011110000111100001111
def goal_236 : Nat := 0xfffffffffff0fff0fffffffffff0fff0f0f0f0f0f0f0f0f0f0f0f0f000000000
def roots_236 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffafffafffffffffff0fff0fafafafafafafafafafafafaaa00aa00
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xfffffffffffcfffcfffffffffffcfffcfcfcfcfcfcfcfcfcf0f0f0f000000000
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffefffefffffffffffcfffcfefefefefefefefefafafafaaa00aa00
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_240 : Nat := 0x1000100010001000100010001000100010001000100010001000100010001
def goal_240 : Nat := 0xffffffffffff0000ffffffffffff0000ffff0000ffff00000000000000000000
def roots_240 : List Nat := [xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffccccffffffffffffccccffffccccffffcccccccc0000cccc0000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffeeeeffffffffffffccccffffeeeeffffeeeeeeeeaaaacccc0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_244 : Nat := 0x11001100110011001100110011001100110011001100110011001100110011
def goal_244 : Nat := 0xfffffffffffff0f0fffffffffffff0f0fffff0f0fffff0f0f0f0f0f000000000
def roots_244 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffcfcfffffffffffffcfcfffffcfcfffffcfcfcfcf0f0cccc0000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffefefffffffffffffcfcfffffefefffffefefefefafacccc0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_248 : Nat := 0x101010101010101010101010101010101010101010101010101010101010101
def goal_248 : Nat := 0xffffffffffffff00ffffffffffffff00ffff0000ffff00000000000000000000
def roots_248 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffccffffffffffffffccffffccccffffcccccccc0000cccc0000
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffeeffffffffffffffccffffeeeeffffeeeeeeeeaaaaeeccaa00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def goal_252 : Nat := 0xfffffffffffffff0fffffffffffffff0fffff0f0fffff0f0f0f0f0f000000000
def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffafffffffffffffff0fffffafafffffafafafafafaaa00aa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffcfffffffffffffffcfffffcfcfffffcfcfcfcf0f0cccc0000
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffefffffffffffffffcfffffefefffffefefefefafaeeccaa00
def roots_255 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

namespace S_82
def pairsG : List (Nat × Nat) := [(2,18), (2,66), (16,18), (16,80), (64,66), (64,80)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_82.map (· &&& dom_82)
def goalM : Nat := goal_82 &&& dom_82
def NN : Nat → Nat
|2=>1
|3=>1
|_=>0
def HT : Nat → Nat → Nat
|2,0=>0xe8a40
|3,0=>0xe8a40
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x140000000000000014000200020000000000020002500050000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x924
|_=>0
def stOffB : Nat → Nat → Nat
|2,0=>3
|3,0=>0x33
|_,_=>0
def dictMask : Nat := 0x7ffffffffffffffffffff
def wireSAt (i : Nat) : Nat := if i < 3 then (dictB (i / 512) (i / 32 % 16) >>> (83 * (i % 32))) &&& dictMask else 0
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
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_82 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_82 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccccccccccccccc0000000000000000cccccccccccccccc, 62)], [(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62)], [(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_82 == dom_82) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_82 goalM v ys) : RunD true dom_82 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_82 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_82 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_82 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_82 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_82 roots_82 goal_82 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_82

theorem lowS_82 : Lower true dom_82 roots_82 goal_82 4 := S_82.noCircuit

def isoMvS_146 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64)]
theorem lowS_146 : Lower true dom_146 roots_146 goal_146 4 :=
  lower_iso isoMvS_146 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_82

def isoMvS_164 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_164 : Lower true dom_164 roots_164 goal_164 4 :=
  lower_iso isoMvS_164 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_82

namespace S_45
def pairsG : List (Nat × Nat) := [(1,9), (1,33), (4,36), (5,13), (5,37), (8,9), (12,13), (12,44), (32,33), (32,36), (40,41), (40,44)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_45.map (· &&& dom_45)
def goalM : Nat := goal_45 &&& dom_45
def NN : Nat → Nat
|3=>1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0x2d750
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xcccc0000000330000003300c0c00000c0c222200002222
|_,_=>0
def stPool : Nat → Nat
|0=>0xe4
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>4
|_,_=>0
def dictMask : Nat := 0x3fffffffffff
def wireSAt (i : Nat) : Nat := if i < 4 then (dictB (i / 512) (i / 32 % 16) >>> (46 * (i % 32))) &&& dictMask else 0
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
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_45 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_45 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_45 == dom_45) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_45 goalM v ys) : RunD true dom_45 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_45 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_45 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_45 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_45 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_45 roots_45 goal_45 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_45

theorem lowS_45 : Lower true dom_45 roots_45 goal_45 4 := S_45.noCircuit

theorem lowS_83 : Lower true dom_83 roots_83 goal_83 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa000a00000000000a000a, 64, 65)] (by decide +kernel) (by decide +kernel) lowS_82

theorem lowS_210 : Lower true dom_210 roots_210 goal_210 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x50005000000000000000000000000000500050000000000000000, 2, 66)] (by decide +kernel) (by decide +kernel) lowS_146

def isoMvS_75 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_75 : Lower true dom_75 roots_75 goal_75 4 :=
  lower_iso isoMvS_75 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_45

def isoMvS_77 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32)]
theorem lowS_77 : Lower true dom_77 roots_77 goal_77 4 :=
  lower_iso isoMvS_77 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_45

def isoMvS_86 : List (Nat × Nat) := [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_86 : Lower true dom_86 roots_86 goal_86 5 :=
  lower_iso isoMvS_86 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_89 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)]
theorem lowS_89 : Lower true dom_89 roots_89 goal_89 4 :=
  lower_iso isoMvS_89 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_45

def isoMvS_102 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_102 : Lower true dom_102 roots_102 goal_102 4 :=
  lower_iso isoMvS_102 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_45

def isoMvS_116 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_116 : Lower true dom_116 roots_116 goal_116 4 :=
  lower_iso isoMvS_116 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_45

def isoMvS_139 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff000000000000000000000000ffffffff00000000, 32), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]
theorem lowS_139 : Lower true dom_139 roots_139 goal_139 4 :=
  lower_iso isoMvS_139 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_45

def isoMvS_141 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff000000000000000000000000ffffffff00000000, 32), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]
theorem lowS_141 : Lower true dom_141 roots_141 goal_141 4 :=
  lower_iso isoMvS_141 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_45

def isoMvS_150 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_150 : Lower true dom_150 roots_150 goal_150 5 :=
  lower_iso isoMvS_150 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_153 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff000000000000000000000000ffffffff00000000, 32), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]
theorem lowS_153 : Lower true dom_153 roots_153 goal_153 4 :=
  lower_iso isoMvS_153 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_45

def isoMvS_154 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_154 : Lower true dom_154 roots_154 goal_154 5 :=
  lower_iso isoMvS_154 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_165 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_165 : Lower true dom_165 roots_165 goal_165 5 :=
  lower_iso isoMvS_165 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_166 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_166 : Lower true dom_166 roots_166 goal_166 5 :=
  lower_iso isoMvS_166 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_172 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_172 : Lower true dom_172 roots_172 goal_172 5 :=
  lower_iso isoMvS_172 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_178 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_178 : Lower true dom_178 roots_178 goal_178 5 :=
  lower_iso isoMvS_178 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_180 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_180 : Lower true dom_180 roots_180 goal_180 5 :=
  lower_iso isoMvS_180 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_195 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_195 : Lower true dom_195 roots_195 goal_195 4 :=
  lower_iso isoMvS_195 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_45

def isoMvS_197 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_197 : Lower true dom_197 roots_197 goal_197 4 :=
  lower_iso isoMvS_197 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_45

def isoMvS_201 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)]
theorem lowS_201 : Lower true dom_201 roots_201 goal_201 4 :=
  lower_iso isoMvS_201 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_45

def isoMvS_202 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_202 : Lower true dom_202 roots_202 goal_202 4 :=
  lower_iso isoMvS_202 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_45

def isoMvS_209 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff00000000ffffffff00000000, 96), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_209 : Lower true dom_209 roots_209 goal_209 4 :=
  lower_iso isoMvS_209 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_45

def isoMvS_216 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_216 : Lower true dom_216 roots_216 goal_216 4 :=
  lower_iso isoMvS_216 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_45

def isoMvS_226 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff0000ffff0000ffff0000, 112), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_226 : Lower true dom_226 roots_226 goal_226 4 :=
  lower_iso isoMvS_226 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_45

def isoMvS_228 : List (Nat × Nat) := [(0xffff0000ffff0000ffff0000ffff0000, 112), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_228 : Lower true dom_228 roots_228 goal_228 5 :=
  lower_iso isoMvS_228 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_240 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff000000000000000000000000ffffffff00000000, 32), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120), (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_240 : Lower true dom_240 roots_240 goal_240 4 :=
  lower_iso isoMvS_240 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_45

theorem lowS_79 : Lower true dom_79 roots_79 goal_79 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcccc000000000000cccc, 64, 66)] (by decide +kernel) (by decide +kernel) lowS_77

theorem lowS_87 : Lower true dom_87 roots_87 goal_87 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaa00aa0000000000aa00aa, 64, 65)] (by decide +kernel) (by decide +kernel) lowS_86

def dzo_83_8:=0xf000f00000000000f000f00
def gzo_83_8:=0xf000e00000000000e000a00
def gsh_83_8:=0xf000e00000000000e000a
theorem lowS_zo_83_8_82:Lower true dzo_83_8 roots_83 gzo_83_8 5:=lower_iso (d1:=dom_83) (roots1:=roots_83) (T1:=gsh_83_8) [(dom_83,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_83_8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xa000a00000000000a000a,0,1)] (by decide +kernel) (by decide +kernel) lowS_82)
namespace S_91
def pairsG : List (Nat × Nat) := [(1,9), (1,65), (2,18), (2,66), (3,11), (3,19), (3,67), (8,9), (10,11), (10,26), (10,74), (16,18), (16,80), (17,19), (17,25), (17,81), (24,25), (24,26), (24,88), (64,65), (64,66), (64,80), (72,73), (72,74), (72,88)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_91.map (· &&& dom_91)
def goalM : Nat := goal_91 &&& dom_91
def NN : Nat → Nat
|4=>2
|5=>3
|6=>1
|_=>0
def HT : Nat → Nat → Nat
|4,0=>0x2a3690a3a9
|5,0=>0xa92a04be7518ce6
|6,0=>0x3f37a
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf0f0c0c000000000f0f0c0c0000f0f0000000000000000f0f0000000000000f0f0000f0f0f0f000000000c0c0c0cf0f0000000000000c0c0000f000f00000000000f000f00c0c0c0c000000000c0c0c0ca0a0a0a000000000a0a0a0a0000f0f0000000000000c0cf0f0f0f0000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x743209743207432087463204352043210
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>0x15405
|5,0=>0x166418a6
|6,0=>0x1c5
|_,_=>0
def dictMask : Nat := 0xfffffffffffffffffffffff
def wireSAt (i : Nat) : Nat := if i < 10 then (dictB (i / 512) (i / 32 % 16) >>> (92 * (i % 32))) &&& dictMask else 0
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
|0=>0x1c2
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
|0=>0xfb440
|_=>0
def pmB : Nat → Nat → Nat
|5,0=>0x19
|6,0=>3
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 2 (j % 128); fld (pmPalB (k / 32)) 5 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_83,5,runOps true dom_83 (0,roots_83) ops)] else [])++(if pm.testBit 1 then [(dom_89,4,runOps true dom_89 (0,roots_89) ops)] else [])++(if pm.testBit 2 then [(dzo_83_8,5,runOps true dzo_83_8 (0,roots_83) ops)] else [])++(if pm.testBit 3 then [(dom_75,4,runOps true dom_75 (0,roots_75) ops)] else [])++(if pm.testBit 4 then [(dom_82,4,runOps true dom_82 (0,roots_82) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_91 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_83_8_82 _ g hchk
    · exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · exact cpcs (by decide +kernel) lowS_82 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_83 5 s (0, roots_83) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_91 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_83 h

def symsG : List (List (Nat × Nat)) := [[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_91 == dom_91) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_91 goalM v ys) : RunD true dom_91 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_91 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, bar true dom_91 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_91 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_91 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_91 roots_91 goal_91 7 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_91

theorem lowS_91 : Lower true dom_91 roots_91 goal_91 7 := S_91.noCircuit

theorem lowS_103 : Lower true dom_103 roots_103 goal_103 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaa000000aa000000aa000000aa, 32, 33)] (by decide +kernel) (by decide +kernel) lowS_102

theorem lowS_167 : Lower true dom_167 roots_167 goal_167 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaa000000aa0000000000000000000000aa000000aa, 32, 33)] (by decide +kernel) (by decide +kernel) lowS_166

theorem lowS_173 : Lower true dom_173 roots_173 goal_173 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x22220000222200000000000000000000222200002222, 8, 9)] (by decide +kernel) (by decide +kernel) lowS_172

namespace S_182
def pairsG : List (Nat × Nat) := [(2,18), (2,130), (4,36), (4,132), (6,22), (6,38), (6,134), (16,18), (16,144), (20,22), (20,52), (20,148), (32,36), (32,160), (34,38), (34,50), (34,162), (48,50), (48,52), (48,176), (128,130), (128,132), (128,144), (128,160)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_182.map (· &&& dom_182)
def goalM : Nat := goal_182 &&& dom_182
def NN : Nat → Nat
|3=>1
|4=>4
|5=>10
|6=>4
|7=>1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0x764f
|4,0=>0x1ef290e98c0bc7700c37
|5,0=>0xa22e38fff08ae654fb7c3ef0f1cc451b33f163740d46e0388f
|6,0=>0x5584c1e9561cb0b0a009
|7,0=>0x5584c
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x1400140014001400000000000000000000000000000002a8028002a80280000000000000000000000000000000055005000550050000000000000000000550050005500502200220022002200000000000000000022002200000001540154015401540000000000000000015001500150015000000002a802a800000000000000000000000002800280500050005000500000000000000000005000500000000aa00aa00aa00aa000000000000000000aa00aa000000000000000154015400000000000000000000000000000000080008000800080000000000000000000000000000000440044005500550000000000000000004400440044004400000000000000000000000000000000aa00a000aa00a00000000154015400000000000000000000000001500152a802a802a80220000000000000000002a8000002a8000500050005000500000000000000000005000500050005000000000a200a200000000000000000000000000a000a15401540154015400000000000000000000000000000002a802a800000000000000000000000002a802a800000005400540054005400000000000000000000000000000000aa00aa00a800a8000000000000000000aa00aa000000015400000154000000000000000000000154000001540002a802a802a802a800000000000000000280028002800284400440044004400000000000000000044004400440044
|_,_=>0
def stPool : Nat → Nat
|0=>0x1448018a2400cf2890031682400c512006b144801aa5a08203144804cc51490030900899e51020678900338a2400cd2890c018ab120061200a315280184801cc51040418820
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>4
|4,0=>0x26a3944a845
|5,0=>0x26b47682ced9b2b0654c918f3186
|6,0=>0xcab7dacb536
|7,0=>0x6a5
|_,_=>0
def dictMask : Nat := 0x7fffffffffffffffffffffffffffffffffffffffffffff
def wireSAt (i : Nat) : Nat := if i < 23 then (dictB (i / 512) (i / 32 % 16) >>> (183 * (i % 32))) &&& dictMask else 0
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
|0=>0x29940941aa184190814197a329929a
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0x61510032001200000100
|6,0=>0x918171
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
|0=>0xffcbeb91440a180
|_=>0
def pmB : Nat → Nat → Nat
|5,0=>0x8504021030
|6,0=>0x6797
|7,0=>9
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 4 (j % 128); fld (pmPalB (k / 32)) 6 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_180,5,runOps true dom_180 (0,roots_180) ops)] else [])++(if pm.testBit 1 then [(dom_150,5,runOps true dom_150 (0,roots_150) ops)] else [])++(if pm.testBit 2 then [(dom_146,4,runOps true dom_146 (0,roots_146) ops)] else [])++(if pm.testBit 3 then [(dom_178,5,runOps true dom_178 (0,roots_178) ops)] else [])++(if pm.testBit 4 then [(dom_164,4,runOps true dom_164 (0,roots_164) ops)] else [])++(if pm.testBit 5 then [(dom_166,5,runOps true dom_166 (0,roots_166) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_182 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_180 _ g hchk
    · exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · exact cpcs (by decide +kernel) lowS_146 _ g hchk
    · exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · exact cpcs (by decide +kernel) lowS_164 _ g hchk
    · exact cpcs (by decide +kernel) lowS_166 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_180 5 s (0, roots_180) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_182 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_180 h

def symsG : List (List (Nat × Nat)) := [[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_182 == dom_182) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_182 goalM v ys) : RunD true dom_182 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_182 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 7) : ∀ i < NN s, bar true dom_182 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
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
  scr true dom_182 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD true dom_182 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_182 roots_182 goal_182 8 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_182

theorem lowS_182 : Lower true dom_182 roots_182 goal_182 8 := S_182.noCircuit

namespace S_203
def pairsG : List (Nat × Nat) := [(1,9), (1,65), (2,66), (2,130), (3,11), (3,67), (3,131), (8,9), (8,136), (10,11), (10,74), (10,138), (64,65), (64,66), (72,73), (72,74), (72,200), (128,130), (128,136), (129,131), (129,137), (129,193), (192,193), (192,194), (192,200)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_203.map (· &&& dom_203)
def goalM : Nat := goal_203 &&& dom_203
def NN : Nat → Nat
|4=>2
|5=>3
|6=>1
|_=>0
def HT : Nat → Nat → Nat
|4,0=>0x40e9712eaa
|5,0=>0xb96376b01507e6e
|6,0=>0x6b015
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf0a0000000000000f0a0000000000000f0a0000000000000f0af0f0000000000000f000000000000000f0f0000000000000f00a0a0000000000000a000000000000000a0a0000000000000a00f0f0000000000000f0f0000000000000000000000000000000000000000000000000000000000000000f0c0000000000000f0cf000000000000000f000000000000000f000000000000000f00c0c0000000000000c0c0000000000000c0c0000000000000c0ca0a0000000000000a0a0000000000000a0a0000000000000a0af0f00000000000000000000000000000f0f0000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x32105832105321057321053260543210
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>0x15405
|5,0=>0x156414a6
|6,0=>0x1b5
|_,_=>0
def dictMask : Nat := 0xfffffffffffffffffffffffffffffffffffffffffffffffffff
def wireSAt (i : Nat) : Nat := if i < 9 then (dictB (i / 512) (i / 32 % 16) >>> (204 * (i % 32))) &&& dictMask else 0
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
|_=>0
def opOffB : Nat → Nat → Nat
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
|0=>0xf8820
|_=>0
def pmB : Nat → Nat → Nat
|5,0=>0x12
|6,0=>3
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 2 (j % 128); fld (pmPalB (k / 32)) 5 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_202,4,runOps true dom_202 (0,roots_202) ops)] else [])++(if pm.testBit 1 then [(dom_195,4,runOps true dom_195 (0,roots_195) ops)] else [])++(if pm.testBit 2 then [(dom_139,4,runOps true dom_139 (0,roots_139) ops)] else [])++(if pm.testBit 3 then [(dom_75,4,runOps true dom_75 (0,roots_75) ops)] else [])++(if pm.testBit 4 then [(dom_201,4,runOps true dom_201 (0,roots_201) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_203 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · exact cpcs (by decide +kernel) lowS_201 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_202 4 s (0, roots_202) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_203 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_202 h

def symsG : List (List (Nat × Nat)) := [[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xcccccccccccccccccccccccccccccccc, 126)], [(0xff00ff00ff00ff00ff00ff00ff00ff00, 120), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xffffffffffffffff0000000000000000, 64), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)], [(0xcccccccccccccccc0000000000000000cccccccccccccccc, 62), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xffffffffffffffff0000000000000000, 64), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120), (0xcccccccccccccccccccccccccccccccc, 126), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xffffffffffffffff0000000000000000, 64), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xcccccccccccccccccccccccccccccccc, 126), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_203 == dom_203) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_203 goalM v ys) : RunD true dom_203 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_203 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, bar true dom_203 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_203 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_203 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_203 roots_203 goal_203 7 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_203

theorem lowS_203 : Lower true dom_203 roots_203 goal_203 7 := S_203.noCircuit

def dzo_210_1:=0xa000a00000000000a000a00000000000a000a00000000000a000a
def gzo_210_1:=0xa000a00000000000a000800000000000a000a0000000000080000
def gsh_210_1:=0x50005000000000005000400000000000500050000000000040000
theorem lowS_zo_210_1_146:Lower true dzo_210_1 roots_210 gzo_210_1 5:=lower_iso (d1:=dom_210) (roots1:=roots_210) (T1:=gsh_210_1) [(dom_210,1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_210_1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x50005000000000000000000000000000500050000000000000000,0,64)] (by decide +kernel) (by decide +kernel) lowS_146)
namespace S_211
def pairsG : List (Nat × Nat) := [(1,65), (2,18), (2,66), (2,130), (3,19), (3,67), (3,131), (16,18), (16,80), (16,144), (17,19), (17,81), (17,145), (64,65), (64,66), (64,80), (128,130), (128,144), (129,131), (129,145), (129,193), (192,193), (192,194), (192,208)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_211.map (· &&& dom_211)
def goalM : Nat := goal_211 &&& dom_211
def NN : Nat → Nat
|4=>1
|5=>1
|6=>1
|_=>0
def HT : Nat → Nat → Nat
|4,0=>0xd2eaa
|5,0=>0xe505d
|6,0=>0xc2467
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf000c00000000000f000c00000000000f000c00000000000f000cf000f00000000000f000f0000000000000000000000000000000000000000000000000000000000000000f000c00000000000f000cf000000000000000f000000000000000f000000000000000f0000c000c00000000000c000c00000000000c000c00000000000c000ca000a00000000000a000a00000000000a000a00000000000a000af000f000000000000000000000000000f000f0000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x688b9a22c688
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>5
|5,0=>0x56
|6,0=>0xb5
|_,_=>0
def dictMask : Nat := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffff
def wireSAt (i : Nat) : Nat := if i < 7 then (dictB (i / 512) (i / 32 % 16) >>> (212 * (i % 32))) &&& dictMask else 0
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
|0=>0x69
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
    (if pm.testBit 0 then [(dom_210,5,runOps true dom_210 (0,roots_210) ops)] else [])++(if pm.testBit 1 then [(dom_83,5,runOps true dom_83 (0,roots_83) ops)] else [])++(if pm.testBit 2 then [(dzo_210_1,5,runOps true dzo_210_1 (0,roots_210) ops)] else [])++(if pm.testBit 3 then [(dom_209,4,runOps true dom_209 (0,roots_209) ops)] else [])++(if pm.testBit 4 then [(dom_146,4,runOps true dom_146 (0,roots_146) ops)] else [])++(if pm.testBit 5 then [(dom_195,4,runOps true dom_195 (0,roots_195) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_211 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_210_1_146 _ g hchk
    · exact cpcs (by decide +kernel) lowS_209 _ g hchk
    · exact cpcs (by decide +kernel) lowS_146 _ g hchk
    · exact cpcs (by decide +kernel) lowS_195 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_210 5 s (0, roots_210) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_211 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_210 h

def symsG : List (List (Nat × Nat)) := [[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_211 == dom_211) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_211 goalM v ys) : RunD true dom_211 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_211 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, bar true dom_211 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_211 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_211 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_211 roots_211 goal_211 7 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_211

theorem lowS_211 : Lower true dom_211 roots_211 goal_211 7 := S_211.noCircuit

theorem lowS_214 : Lower true dom_214 roots_214 goal_214 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x500050000000000050005000000000005000500000000000500050, 64, 68)] (by decide +kernel) (by decide +kernel) lowS_210

def isoMvS_107 : List (Nat × Nat) := [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)]
theorem lowS_107 : Lower true dom_107 roots_107 goal_107 5 :=
  lower_iso isoMvS_107 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_79

def isoMvS_109 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)]
theorem lowS_109 : Lower true dom_109 roots_109 goal_109 5 :=
  lower_iso isoMvS_109 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_103

def isoMvS_118 : List (Nat × Nat) := [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_118 : Lower true dom_118 roots_118 goal_118 7 :=
  lower_iso isoMvS_118 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_91

def isoMvS_143 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]
theorem lowS_143 : Lower true dom_143 roots_143 goal_143 5 :=
  lower_iso isoMvS_143 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_79

def isoMvS_155 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]
theorem lowS_155 : Lower true dom_155 roots_155 goal_155 7 :=
  lower_iso isoMvS_155 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_91

def isoMvS_157 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]
theorem lowS_157 : Lower true dom_157 roots_157 goal_157 5 :=
  lower_iso isoMvS_157 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_79

def isoMvS_158 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]
theorem lowS_158 : Lower true dom_158 roots_158 goal_158 6 :=
  lower_iso isoMvS_158 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_87

def isoMvS_171 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]
theorem lowS_171 : Lower true dom_171 roots_171 goal_171 5 :=
  lower_iso isoMvS_171 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_103

def isoMvS_174 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]
theorem lowS_174 : Lower true dom_174 roots_174 goal_174 6 :=
  lower_iso isoMvS_174 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_87

def isoMvS_181 : List (Nat × Nat) := [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]
theorem lowS_181 : Lower true dom_181 roots_181 goal_181 6 :=
  lower_iso isoMvS_181 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_167

def isoMvS_185 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]
theorem lowS_185 : Lower true dom_185 roots_185 goal_185 5 :=
  lower_iso isoMvS_185 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_103

def isoMvS_186 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]
theorem lowS_186 : Lower true dom_186 roots_186 goal_186 6 :=
  lower_iso isoMvS_186 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_87

def isoMvS_188 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]
theorem lowS_188 : Lower true dom_188 roots_188 goal_188 6 :=
  lower_iso isoMvS_188 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_87

def isoMvS_199 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_199 : Lower true dom_199 roots_199 goal_199 5 :=
  lower_iso isoMvS_199 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_103

def isoMvS_205 : List (Nat × Nat) := [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_205 : Lower true dom_205 roots_205 goal_205 7 :=
  lower_iso isoMvS_205 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_203

def isoMvS_206 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff00000000ffffffff00000000, 96), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]
theorem lowS_206 : Lower true dom_206 roots_206 goal_206 5 :=
  lower_iso isoMvS_206 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_103

def isoMvS_217 : List (Nat × Nat) := [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_217 : Lower true dom_217 roots_217 goal_217 7 :=
  lower_iso isoMvS_217 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_203

def isoMvS_218 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_218 : Lower true dom_218 roots_218 goal_218 7 :=
  lower_iso isoMvS_218 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_211

def isoMvS_227 : List (Nat × Nat) := [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem lowS_227 : Lower true dom_227 roots_227 goal_227 7 :=
  lower_iso isoMvS_227 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_203

def isoMvS_229 : List (Nat × Nat) := [(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 124)]
theorem lowS_229 : Lower true dom_229 roots_229 goal_229 6 :=
  lower_iso isoMvS_229 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_173

def isoMvS_230 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 124), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_230 : Lower true dom_230 roots_230 goal_230 6 :=
  lower_iso isoMvS_230 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_173

def isoMvS_233 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff0000ffff0000ffff0000, 112), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)]
theorem lowS_233 : Lower true dom_233 roots_233 goal_233 5 :=
  lower_iso isoMvS_233 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_103

def isoMvS_234 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff0000ffff0000ffff0000ffff0000, 112), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]
theorem lowS_234 : Lower true dom_234 roots_234 goal_234 5 :=
  lower_iso isoMvS_234 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_79

def isoMvS_236 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 124), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]
theorem lowS_236 : Lower true dom_236 roots_236 goal_236 6 :=
  lower_iso isoMvS_236 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_167

def isoMvS_242 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_242 : Lower true dom_242 roots_242 goal_242 7 :=
  lower_iso isoMvS_242 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_211

def isoMvS_244 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 124), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_244 : Lower true dom_244 roots_244 goal_244 6 :=
  lower_iso isoMvS_244 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_173

def isoMvS_248 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff00000000ffffffff00000000, 96), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 124), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]
theorem lowS_248 : Lower true dom_248 roots_248 goal_248 5 :=
  lower_iso isoMvS_248 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_79

theorem lowS_63 : Lower true dom_63 roots_63 goal_63 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcccccccccccccccc, 16, 18), (0xffff0000ffff0000, 2, 18)] (by decide +kernel) (by decide +kernel) lowS_45

theorem lowS_95 : Lower true dom_95 roots_95 goal_95 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f0f0f000000000f0f0f0f0, 64, 68)] (by decide +kernel) (by decide +kernel) lowS_91

def dzo_109_2:=0xcccc0000cccc0000cccc0000cccc
def gzo_109_2:=0xcccc0000cccc0000c8c800008800
def gsh_109_2:=0x3333000033330000323200002200
theorem lowS_zo_109_2_45:Lower true dzo_109_2 roots_109 gzo_109_2 5:=lower_iso (d1:=dom_109) (roots1:=roots_109) (T1:=gsh_109_2) [(dom_109,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_109_2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x3333000033330000000000000000,0,64)] (by decide +kernel) (by decide +kernel) lowS_45)
def dzo_103_8:=0xff000000ff000000ff000000ff00
def gzo_103_8:=0xfe000000fe000000fa000000aa00
def gsh_103_8:=0xfe000000fe000000fa000000aa
theorem lowS_zo_103_8_102:Lower true dzo_103_8 roots_103 gzo_103_8 5:=lower_iso (d1:=dom_103) (roots1:=roots_103) (T1:=gsh_103_8) [(dom_103,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_103_8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xaa000000aa000000aa000000aa,0,1)] (by decide +kernel) (by decide +kernel) lowS_102)
namespace S_111
def pairsG : List (Nat × Nat) := [(1,9), (1,33), (1,65), (2,66), (3,11), (3,35), (3,67), (4,36), (4,68), (5,13), (5,37), (5,69), (6,38), (6,70), (7,15), (7,39), (7,71), (8,9), (10,11), (10,74), (12,13), (12,44), (12,76), (14,15), (14,46), (14,78), (32,33), (32,36), (34,35), (34,38), (34,98), (40,41), (40,44), (42,43), (42,46), (42,106), (64,65), (64,66), (64,68), (72,73), (72,74), (72,76), (96,97), (96,98), (96,100), (104,105), (104,106), (104,108)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_111.map (· &&& dom_111)
def goalM : Nat := goal_111 &&& dom_111
def NN : Nat → Nat
|6=>1
|_=>0
def HT : Nat → Nat → Nat
|6,0=>0x6842f
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xffff000000000000ffff00000000ff000000ff000000ff000000ff00f0f00000f0f00000f0f00000f0f0cccc0000cccc0000cccc0000ccccaaaa0000aaaa0000aaaa0000aaaaffff0000ffff0000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x2c688
|_=>0
def stOffB : Nat → Nat → Nat
|6,0=>6
|_,_=>0
def dictMask : Nat := 0xffffffffffffffffffffffffffff
def wireSAt (i : Nat) : Nat := if i < 6 then (dictB (i / 512) (i / 32 % 16) >>> (112 * (i % 32))) &&& dictMask else 0
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
|0=>0xff00
|_=>0
def pmB : Nat → Nat → Nat
|6,0=>1
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 1 (j % 128); fld (pmPalB (k / 32)) 8 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_109,5,runOps true dom_109 (0,roots_109) ops)] else [])++(if pm.testBit 1 then [(dzo_109_2,5,runOps true dzo_109_2 (0,roots_109) ops)] else [])++(if pm.testBit 2 then [(dzo_103_8,5,runOps true dzo_103_8 (0,roots_103) ops)] else [])++(if pm.testBit 3 then [(dom_103,5,runOps true dom_103 (0,roots_103) ops)] else [])++(if pm.testBit 4 then [(dom_45,4,runOps true dom_45 (0,roots_45) ops)] else [])++(if pm.testBit 5 then [(dom_79,5,runOps true dom_79 (0,roots_79) ops)] else [])++(if pm.testBit 6 then [(dom_102,4,runOps true dom_102 (0,roots_102) ops)] else [])++(if pm.testBit 7 then [(dom_107,5,runOps true dom_107 (0,roots_107) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_111 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_109_2_45 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_103_8_102 _ g hchk
    · exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · exact cpcs (by decide +kernel) lowS_79 _ g hchk
    · exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · exact cpcs (by decide +kernel) lowS_107 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_109 5 s (0, roots_109) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_111 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_109 h

def symsG : List (List (Nat × Nat)) := [[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_111 == dom_111) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_111 goalM v ys) : RunD true dom_111 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_111 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, bar true dom_111 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_111 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_111 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_111 roots_111 goal_111 7 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_111

theorem lowS_111 : Lower true dom_111 roots_111 goal_111 7 := S_111.noCircuit

theorem lowS_119 : Lower true dom_119 roots_119 goal_119 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaa00aa00aa00aa00aa00aa00aa00aa, 32, 33)] (by decide +kernel) (by decide +kernel) lowS_118

def dzo_45_2:=0xcccc0000cccc
def gzo_45_2:=0xc8c800008800
def gsh_45_2:=0x323200002200
theorem lowS_zo_45_2_45:Lower true dzo_45_2 roots_45 gzo_45_2 4:=lower_iso (d1:=dom_45) (roots1:=roots_45) (T1:=gsh_45_2) [(dom_45,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_45_2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [] (by decide +kernel) (by decide +kernel) lowS_45)
def dzo_173_2:=0xcccc0000cccc00000000000000000000cccc0000cccc
def gzo_173_2:=0xcccc0000cccc00000000000000000000c8c800008800
def gsh_173_2:=0x33330000333300000000000000000000323200002200
theorem lowS_zo_173_2_45:Lower true dzo_173_2 roots_173 gzo_173_2 5:=lower_iso (d1:=dom_173) (roots1:=roots_173) (T1:=gsh_173_2) [(dom_173,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_173_2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x33330000333300000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_45)
namespace S_175
def pairsG : List (Nat × Nat) := [(1,9), (1,33), (2,130), (3,11), (3,35), (3,131), (4,36), (4,132), (5,13), (5,37), (5,133), (6,38), (6,134), (7,15), (7,39), (7,135), (8,9), (8,136), (10,11), (10,138), (12,13), (12,44), (12,140), (14,15), (14,46), (14,142), (32,33), (32,36), (32,160), (34,35), (34,38), (34,162), (40,41), (40,44), (40,168), (42,43), (42,46), (42,170), (128,130), (128,132), (128,136), (128,160), (129,131), (129,133), (129,137), (129,161)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3fffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_175.map (· &&& dom_175)
def goalM : Nat := goal_175 &&& dom_175
def NN : Nat → Nat
|3=>1
|4=>4
|5=>10
|6=>7
|7=>1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0xbf714
|4,0=>0xf07b6cca35b6f918c0bc
|5,0=>0xff2b1fdad7fce2cd8e78727ce59cf85508027b4c1bda0062fc
|6,0=>0xcb952c2b8ac1b39c13b0a5d142993e11d97
|7,0=>0xd5670
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xffff0000ffff00000000000000000000f0f00000f0f0fcfc0000fcfc00000000000000000000fcfc0000fcfcffff0000cccc00000000000000000000ffff0000cccc33330000333300000000000000000000000000000000ffff0000ffcc00000000000000000000ffff0000ffccf3f30000f3f300000000000000000000f0f00000f0f0555500005500000000000000000000005555000055000f0f00000f0f000000000000000000000f0f0000000000ff000000ff0000000000000000000000aa000000aaffff0000ffff00000000000000000000aaaa0000aaaaffff0000ff0000000000000000000000ffff0000ff00ffff0000333300000000000000000000ffff00000000ffff0000000000000000000000000000ffff00000000ff000000ff0000000000000000000000ff000000ff00aaaa0000aaaa00000000000000000000aaaa0000aaaa0f0f00000303000000000000000000000f0f00000000ffff0000ffff00000000000000000000000000000000ffff0000ffff00000000000000000000ffff00000000f0f00000f0f000000000000000000000f0f00000f0f0cccc0000cccc00000000000000000000cccc0000ccccffff0000ff0000000000000000000000aaaa0000aa00
|_,_=>0
def stPool : Nat → Nat
|0=>0x41e8209888388c488d07104c441c4159107988c4920e231148104c45204624548105648290231107788c450c4131148105c441c26691020ad841a0e20ad28388c440820228620ad4911888398a418820
|1=>0x107104c4
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>4
|4,0=>0x1350e5095045
|5,0=>0x4e64864263c63663062a62461e6186
|6,0=>0x7977366c76666065a6546
|7,0=>0x806
|_,_=>0
def dictMask : Nat := 0xffffffffffffffffffffffffffffffffffffffffffff
def wireSAt (i : Nat) : Nat := if i < 21 then (dictB (i / 512) (i / 32 % 16) >>> (176 * (i % 32))) &&& dictMask else 0
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
|0=>0x11109241131110540541d50541d
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
|0=>0xf8aff5dcb995c2a94c609401001001800
|_=>0
def pmB : Nat → Nat → Nat
|5,0=>0x10300020
|6,0=>0x4756ab8
|7,0=>9
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 4 (j % 128); fld (pmPalB (k / 32)) 11 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_174,6,runOps true dom_174 (0,roots_174) ops)] else [])++(if pm.testBit 1 then [(dom_165,5,runOps true dom_165 (0,roots_165) ops)] else [])++(if pm.testBit 2 then [(dzo_45_2,4,runOps true dzo_45_2 (0,roots_45) ops)] else [])++(if pm.testBit 3 then [(dom_139,4,runOps true dom_139 (0,roots_139) ops)] else [])++(if pm.testBit 4 then [(dom_171,5,runOps true dom_171 (0,roots_171) ops)] else [])++(if pm.testBit 5 then [(dom_45,4,runOps true dom_45 (0,roots_45) ops)] else [])++(if pm.testBit 6 then [(dzo_173_2,5,runOps true dzo_173_2 (0,roots_173) ops)] else [])++(if pm.testBit 7 then [(dom_173,6,runOps true dom_173 (0,roots_173) ops)] else [])++(if pm.testBit 8 then [(dom_143,5,runOps true dom_143 (0,roots_143) ops)] else [])++(if pm.testBit 9 then [(dom_167,6,runOps true dom_167 (0,roots_167) ops)] else [])++(if pm.testBit 10 then [(dom_141,4,runOps true dom_141 (0,roots_141) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_175 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_45_2_45 _ g hchk
    · exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_173_2_45 _ g hchk
    · exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · exact cpcs (by decide +kernel) lowS_141 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_174 6 s (0, roots_174) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_175 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_174 h

def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {v ys} (h : RunD true dom_175 goalM v ys) : RunD true dom_175 goalM v (ori ys) := h
def Z (s : Nat) := barP true dom_175 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 7 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 7) : ∀ i < NN s, bar true dom_175 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
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
  scr true dom_175 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD true dom_175 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_175 roots_175 goal_175 8 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_175

theorem lowS_175 : Lower true dom_175 roots_175 goal_175 8 := S_175.noCircuit

theorem lowS_183 : Lower true dom_183 roots_183 goal_183 9 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaa00aa00aa00aa000000000000000000aa00aa00aa00aa, 32, 33)] (by decide +kernel) (by decide +kernel) lowS_182

theorem lowS_190 : Lower true dom_190 roots_190 goal_190 9 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x550055005500550000000000000000005500550055005500, 128, 136)] (by decide +kernel) (by decide +kernel) lowS_182

theorem lowS_207 : Lower true dom_207 roots_207 goal_207 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcccc000000000000cccc000000000000cccc000000000000cccc, 64, 66)] (by decide +kernel) (by decide +kernel) lowS_205

theorem lowS_215 : Lower true dom_215 roots_215 goal_215 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf000f00000000000f000f00000000000f000f00000000000f000f0, 64, 68)] (by decide +kernel) (by decide +kernel) lowS_211

def dzo_154_1:=0xa0a0a0a0000000000000000000000000a0a0a0a
def gzo_154_1:=0xa0a0a080000000000000000000000000a080a00
def gsh_154_1:=0x505050400000000000000000000000005040500
theorem lowS_zo_154_1_146:Lower true dzo_154_1 roots_154 gzo_154_1 5:=lower_iso (d1:=dom_154) (roots1:=roots_154) (T1:=gsh_154_1) [(dom_154,1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_154_1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x500050000000000000000000000000005000500,0,8)] (by decide +kernel) (by decide +kernel) lowS_146)
def dzo_218_1:=0xa0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a
def gzo_218_1:=0xa0a0a0a000000000a0a0a08000000000a0a0a0a000000000a080a00
def gsh_218_1:=0x5050505000000000505050400000000050505050000000005040500
theorem lowS_zo_218_1_146:Lower true dzo_218_1 roots_218 gzo_218_1 6:=lower_iso (d1:=dom_218) (roots1:=roots_218) (T1:=gsh_218_1) [(dom_218,1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_218_1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x5000500000000000500050000000000050005000000000005000500,0,8),(0x5050505000000000000000000000000050505050000000000000000,0,64)] (by decide +kernel) (by decide +kernel) lowS_146)
def dzo_146_1:=0xa000a000000000000000000000000000a000a
def gzo_146_1:=0xa000800000000000000000000000000080000
def gsh_146_1:=0x5000400000000000000000000000000040000
theorem lowS_zo_146_1_146:Lower true dzo_146_1 roots_146 gzo_146_1 4:=lower_iso (d1:=dom_146) (roots1:=roots_146) (T1:=gsh_146_1) [(dom_146,1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_146_1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [] (by decide +kernel) (by decide +kernel) lowS_146)
def dzo_211_8:=0xf000f00000000000f000f00000000000f000f00000000000f000f00
def gzo_211_8:=0xf000f00000000000f000f00000000000f000e00000000000e000a00
def gsh_211_8:=0xf000f00000000000f000f00000000000f000e00000000000e000a
theorem lowS_zo_211_8_82:Lower true dzo_211_8 roots_211 gzo_211_8 6:=lower_iso (d1:=dom_211) (roots1:=roots_211) (T1:=gsh_211_8) [(dom_211,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_211_8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xa000a00000000000a000a00000000000a000a00000000000a000a,0,1),(0xf000f00000000000f000f00000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_82)
def dzo_82_8:=0x50005000000000005000500
def gzo_82_8:=0x50004000000000004000000
def gsh_82_8:=0x500040000000000040000
theorem lowS_zo_82_8_82:Lower true dzo_82_8 roots_82 gzo_82_8 4:=lower_iso (d1:=dom_82) (roots1:=roots_82) (T1:=gsh_82_8) [(dom_82,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_82_8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [] (by decide +kernel) (by decide +kernel) lowS_82)
namespace S_219
def pairsG : List (Nat × Nat) := [(1,9), (1,65), (2,18), (2,66), (2,130), (3,11), (3,19), (3,67), (3,131), (8,9), (8,136), (10,11), (10,26), (10,74), (10,138), (16,18), (16,80), (16,144), (17,19), (17,25), (17,81), (17,145), (24,25), (24,26), (24,88), (24,152), (64,65), (64,66), (64,80), (72,73), (72,74), (72,88), (72,200), (128,130), (128,136), (128,144), (129,131), (129,137), (129,145), (129,193), (192,193), (192,194), (192,200), (192,208)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_219.map (· &&& dom_219)
def goalM : Nat := goal_219 &&& dom_219
def NN : Nat → Nat
|4=>2
|5=>15
|6=>56
|7=>31
|8=>8
|9=>1
|_=>0
def HT : Nat → Nat → Nat
|4,0=>0x96cef037a9
|5,0=>0xa4a5e71ad170ab76ef8f600db53bdb4a3c23c3af390fc3458930f642c6ae231f21ea460de48
|6,0=>0xcdd5fc43b4c07ccb8239af0fd9fc3189393774d972d6968cbf689e0648055eeb35878457acb55eb75462b510c04ce1d4cc5c4bd444b776478f94379b418143de7f3c3af387523514e30e4d2f3972eca22ca902646b22d101d3641c1261a6a119d2f18e9c18ba817ea1171a814beb13efa128cd110fa0eb910e0300b0bc08d37082f907c2007ab50796e04f98
|7,0=>0xd8b22d2123c7fd6c6c1caaba39dbe49aeb994af79302f7e34b74b3771e81710b3696e169552583795474848a493a8f43994c395e2281cf26e99212b81c7371aa321a25b147671298d0cc8508223
|8,0=>0xfde86f3d39db4c8a089a6f0dd653454337a06c10
|9,0=>0x6f0dd
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f00000000f0f0000000000000f0f0000000000000f0f0000000000000000f0f0f0f000000000f0f0f0f0000000000000e0e0000000000000e0ef0f0f0f000000000f0f0f0f000000000c0c0c0c000000000c0c0c0c0000000000000000f0f0f0f0000000000000000000000000c0c0c0c0000000000000000f0f0f0f0000000000000000000000000f0f0e0ef000f00000000000f0f0f0c00000000000000000000000000000000f0f0f0f0000000000000000000000000f0f0e0e0000000000000000f0f0f0f000000000f0f0000000000000f0f0f0f000000000f0f000000000000000000000000000000000000f0f0f0f000000000c0c0c0cf0f0000000000000f0f0000000000000f0f0000000000000c0c000030303030000000003030303000000000303030300000000000000003030303000000000303030300000000030303030000000003030000f0f0f0f000000000f0f0000000000000c0c0c0c000000000c0c00000000000000000000f0f0c0c0000000000000000000000000f0f0c0ca0a0a0a000000000a000a00000000000a0a0a0a000000000a000a00f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000c0c0c0cf0f0f0c000000000f0f0f0c000000000f0f0f0c000000000f000f00000030000000000000003000000000000000300000000000f000f0000000000000000000000000000000000f000f00000000000f0f0f0cc0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0cf0f0000000000000f0f0000000000000f0f0000000000000f0f0000f0f0f0f0000000000000000000000000f0f0f0f0000000000000000f0f0f0f000000000f0f0f0f00000000000000000000000000000000f0f0f0f000000000f0f0f0f000000000f0f0000000000000f0f0000f0f0f0f000000000c0c0c0c000000000f0f0f0f000000000c0c0c0cf0f0c0c000000000f0f0c0c000000000f0f0c0c0000000000000000f0f0c0c000000000f0f0c0c000000000f0f0c0c000000000f0f0c0cf000f00000000000f000f00000000000f000f00000000000f000f00f0f0f0f000000000c0c0c0c000000000f0f0000000000000c0c0000a0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0af0f0f0f000000000f0f0f0f000000000f0f0f0f0000000000000000
|0,1=>0xf0f0000000000000f0f0000000000000f0f0f0f000000000f0f0c0c00003030000000000000303000000000000030300000000000000000000f0f0000000000000f0c0000000000000f0f0000000000000f0c000000000000000000000000000000000000e0e0000000000000e0e0000000000000000f0f0f0c0000000000000000000000000f0f0f0cf0f0f0f000000000f0f0f0c000000000f0f0f0f000000000f0f0f0c00000000000000000000000000000000f0f0f0c000000000f0f0f0c00000000000000000000f0f00000000000000000000000000000c0c0000f0f0000000000000f0f0000000000000f0f0000000000000c0c00000000000000000000000000000000f0f0f0f000000000f0f0c0cf050f04000000000f050f04000000000f050f04000000000f050f04f0c0f0c000000000f0c0f0c000000000f0c0f0c000000000f0c0f0cf0c0f0c000000000f0c0000000000000f0c0f0c000000000f0c0000f0f0f0c000000000f0f0f0c000000000f0f0f0c000000000f0f0f0cf0f0f0c000000000f0f0f0c00000000000000000000000000000000f0f0e0e000000000f0f0e0e000000000f0f0e0e000000000f0f0e0ef0f0e0e0000000000000000000000000f0f0e0e000000000000000000f000c00000000000f000c00000000000f000c00000000000f000ca000a02000000000a000a02000000000a000a02000000000a000a02000000000000000000000000000000000000000000000000f0f0c0cf0f0000000000000f0f0000000000000f0f0e0e000000000f0f0e0ef000f0f000000000f000f0c000000000f000f0f000000000f000f0cf0f000f000000000f0f000c000000000f0f000f000000000f0f000ce0e0e0e000000000e0e0e0e000000000e0e0e0e000000000e0e0e0e3030303000000000303030300000000030300000000000003030000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0c0cf0f0f0f000000000f0f0f0f00000000030303030000000003030000c0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0000f0f0f0f000000000f0f0f0f000000000a0a0a0a000000000a0a0a0af000f00000000000f000f00000000000a000a00000000000a000a00f0f0f0f000000000f000f00000000000f0f0f0f000000000f000f00c0c0f0f000000000c0c0f0f000000000c0c0f0f000000000c0c0c0c
|0,2=>0xf0a0f0a000000000f0a0f0a000000000f0a0f0a000000000f0a0f0af0f0f00000000000f0f0f00000000000f0f0f00000000000f0f0f003030300000000000303030000000000030303000000000003030300505040400000000050504040000000005050404000000000505040400f000f00000000000f000000000000000f000f00000000000f0000f0f0f0f000000000f0f0f0f000000000e0e0e0e000000000e0e0e0ef0f0a0a000000000f0f0a0a000000000f0f0a0a000000000f0f0a0a00000000000000000000000000000000f0f0a0a000000000f0f0a0af0f0f0f000000000a0a0a0a000000000f0f0f0f000000000a0a0a0a00f000f00000000000f000f00000000000a000a00000000000a000a50505050000000005050505000000000505040400000000050504045050505000000000500050000000000050505050000000005000500f0f0f0f000000000f0f0f0f00000000050504040000000005050404f0f0f0f0000000000000000000000000f0f0f0f000000000f0f0c0ca0a0a0a000000000a0a0a0a000000000f0f0e0e000000000f0f0e0ef0f0f0f000000000f0f0c0c000000000f0f0f0f000000000f0f0c0c
|_,_=>0
def stPool : Nat → Nat
|0=>0x140d00b022441f062c0893c205031604e8910105033604488081c1860200d0a062c088140c58112645031604c080e0c5811214217065808806540892820503024c488140c592020088a062c808081c18f022450e16044881434581122060a062c089080c10112203830c042840608080
|1=>0x62c0af102818b029c009140c5ad122160a062c089100ce0b2a044882e2818f160442b140c581122052a062c08910a45031604488140d4014e24426140c5811220503160528910281a40224407062c080127820a1605109105c5032c2c08822290831604404140c30100202170618088
|2=>0x127840a062c0897c2018b02dc009102818b02f4488140c581782443b140c5811221d0a062c08910e420a062c089140c581702440a062c901122038a062c089280ce0b02dc488140c0931221b0a062c0891029a8b022440316540801220533062c089107c5034804488082818b022588a
|3=>0x140c581122240a062c089101c503171c08910285818c2440a062c0c512205031604485102818b02dc488082818b88244040e0c3011220503160618911085031604488722818b022608a062c089110050316040087e2818b02244043e0c581122038a0618581007c503024c4880e0c581
|4=>0x82818b8e0448880105031604488140c5819a2440a062c0a7122038a061858112205031606609102818f1604488140cb0b022440a1605109102818b02004941010521062c08910105033804488805c5031604488140c5819624407140d40b022440a07285811220f8a062c0801220f97
|5=>0x62c080122054f062c089101c5031604488140c5c7022440a062c08910290831604488082818b022440a680c581122088a062c08910105031604009101054f062c08910c85031604488140c5811250440140c5811221904140c581122038a062c08012281ca382c089101c503382c089
|6=>0x2818b022440a
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>0x154005
|5,0=>0x5e61618526131846610183a60d182e60a18226071816604180a6
|6,0=>0x779dd77741dc97709dbb76d1dae669dda07665d92762dd8475f5d7675bdd687585d5a754dd4c7515d3e74ddd3074a99237475916743dd087405cfb63d1cee639dce07365cd2732dcc472f5cb672bdca96289c9b7251c8d7219c8061e5c7271adc647
|7,0=>0x2c37aee2b38ab1ea57a79e968a3de878a01e7889c22697989e5a894de4c7915e3f68de22f88a1e208865e118829e0287ea1f377ae1e56
|8,0=>0xbe9ef37bb1ee57b7dad87b45eca7
|9,0=>0x3016
|_,_=>0
def dictMask : Nat := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffff
def wireSAt (i : Nat) : Nat := if i < 80 then (dictB (i / 512) (i / 32 % 16) >>> (220 * (i % 32))) &&& dictMask else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 7 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 14 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))

def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 7 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
|0=>0xe25080212211e2b16010ea214212e2d6423080d385c14251621160212211e2b38251e28160112212ed014256420080d60240805142d0e2f142102bb080f142d1e283825160110250c2b0e2f14212e2f1425140112211221460c142d02210827142d14251629162514021221122138271621080012210c2116250e1816251421
|1=>0x12212e2d1425080d142d142112213805162116211421142d02250825142d173a140d0e2f1421162514210807142d160112210c231625460c022116021221142d0625162916212e2d14252e0f14251421160538051621140112212e2114259223140502251421460f02210800142d1221420706250825142d0e25142114011221
|2=>0x12210605142102250625142d160d0827142d142d1221142d0605080d142d1602
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0x52000000000000000032000000000003
|6,0=>0x4830004620000000000000004420004220004023f13d23b20003920003813620003333122f20000000002c32a20002822532322030001e21c20001b10001920001721521411130000f20000c30a2091000072
|7,0=>0x8728528328127f27d27b27927727527327126f26d26b26926726526326125f25d25b25925725525325124f24d24b2
|8,0=>0x8f18e18d18c10008b18a1891
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
|0=>0x2020c007026001819800417b00105dc00413f00044fc0011370002188000852000210800060000006fc00019700004dc000117000041c0001000000294000087000010800003600000d00000200000078000014000004000000600000100000020000004000000
|1=>0x20141bf8000215c0008530806fc20613f08104fc20193f080605020180604806fc0d010401d04dc03433700d04dc03013f00a06dc0201bf0040c50008085
|_=>0
def pmB : Nat → Nat → Nat
|5,0=>0x2000000002000004
|6,0=>0xa0030000000080030032c31400405030040830000060c00d214f00308050004020308d00e0070d5002
|7,0=>0x192b195ab28730760ae76ca8aeb532617aa94cbd65e97e4
|8,0=>0x6b26e3426625
|9,0=>0x11
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 6 (j % 128); fld (pmPalB (k / 32)) 26 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_218,7,runOps true dom_218 (0,roots_218) ops)] else [])++(if pm.testBit 1 then [(dom_203,7,runOps true dom_203 (0,roots_203) ops)] else [])++(if pm.testBit 2 then [(dom_217,7,runOps true dom_217 (0,roots_217) ops)] else [])++(if pm.testBit 3 then [(dzo_154_1,5,runOps true dzo_154_1 (0,roots_154) ops)] else [])++(if pm.testBit 4 then [(dom_155,7,runOps true dom_155 (0,roots_155) ops)] else [])++(if pm.testBit 5 then [(dom_91,7,runOps true dom_91 (0,roots_91) ops)] else [])++(if pm.testBit 6 then [(dom_75,4,runOps true dom_75 (0,roots_75) ops)] else [])++(if pm.testBit 7 then [(dzo_218_1,6,runOps true dzo_218_1 (0,roots_218) ops)] else [])++(if pm.testBit 8 then [(dom_211,7,runOps true dom_211 (0,roots_211) ops)] else [])++(if pm.testBit 9 then [(dom_146,4,runOps true dom_146 (0,roots_146) ops)] else [])++(if pm.testBit 10 then [(dzo_146_1,4,runOps true dzo_146_1 (0,roots_146) ops)] else [])++(if pm.testBit 11 then [(dom_139,4,runOps true dom_139 (0,roots_139) ops)] else [])++(if pm.testBit 12 then [(dom_201,4,runOps true dom_201 (0,roots_201) ops)] else [])++(if pm.testBit 13 then [(dom_89,4,runOps true dom_89 (0,roots_89) ops)] else [])++(if pm.testBit 14 then [(dzo_83_8,5,runOps true dzo_83_8 (0,roots_83) ops)] else [])++(if pm.testBit 15 then [(dom_154,5,runOps true dom_154 (0,roots_154) ops)] else [])++(if pm.testBit 16 then [(dzo_211_8,6,runOps true dzo_211_8 (0,roots_211) ops)] else [])++(if pm.testBit 17 then [(dzo_210_1,5,runOps true dzo_210_1 (0,roots_210) ops)] else [])++(if pm.testBit 18 then [(dom_195,4,runOps true dom_195 (0,roots_195) ops)] else [])++(if pm.testBit 19 then [(dom_209,4,runOps true dom_209 (0,roots_209) ops)] else [])++(if pm.testBit 20 then [(dom_202,4,runOps true dom_202 (0,roots_202) ops)] else [])++(if pm.testBit 21 then [(dom_153,4,runOps true dom_153 (0,roots_153) ops)] else [])++(if pm.testBit 22 then [(dom_82,4,runOps true dom_82 (0,roots_82) ops)] else [])++(if pm.testBit 23 then [(dzo_82_8,4,runOps true dzo_82_8 (0,roots_82) ops)] else [])++(if pm.testBit 24 then [(dom_216,4,runOps true dom_216 (0,roots_216) ops)] else [])++(if pm.testBit 25 then [(dom_210,5,runOps true dom_210 (0,roots_210) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_219 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_154_1_146 _ g hchk
    · exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_218_1_146 _ g hchk
    · exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · exact cpcs (by decide +kernel) lowS_146 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_146_1_146 _ g hchk
    · exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · exact cpcs (by decide +kernel) lowS_201 _ g hchk
    · exact cpcs (by decide +kernel) lowS_89 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_83_8_82 _ g hchk
    · exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_211_8_82 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_210_1_146 _ g hchk
    · exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · exact cpcs (by decide +kernel) lowS_209 _ g hchk
    · exact cpcs (by decide +kernel) lowS_202 _ g hchk
    · exact cpcs (by decide +kernel) lowS_153 _ g hchk
    · exact cpcs (by decide +kernel) lowS_82 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_82_8_82 _ g hchk
    · exact cpcs (by decide +kernel) lowS_216 _ g hchk
    · exact cpcs (by decide +kernel) lowS_210 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_218 7 s (0, roots_218) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_219 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_218 h

def symsG : List (List (Nat × Nat)) := [[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xffffffffffffffff0000000000000000, 64), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xffffffffffffffff0000000000000000, 64), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_219 == dom_219) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_219 goalM v ys) : RunD true dom_219 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_219 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 15 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 56 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 56 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 31 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 31 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 8 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 9) : ∀ i < NN s, bar true dom_219 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
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
  scr true dom_219 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD true dom_219 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_219 roots_219 goal_219 10 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_219

theorem lowS_219 : Lower true dom_219 roots_219 goal_219 10 := S_219.noCircuit

namespace S_231
def pairsG : List (Nat × Nat) := [(1,33), (1,65), (2,66), (2,130), (3,35), (3,67), (3,131), (4,36), (4,68), (4,132), (5,37), (5,69), (5,133), (6,38), (6,70), (6,134), (7,39), (7,71), (7,135), (32,33), (32,36), (32,160), (34,35), (34,38), (34,98), (34,162), (64,65), (64,66), (64,68), (96,97), (96,98), (96,100), (96,224), (128,130), (128,132), (128,160), (129,131), (129,133), (129,161), (129,193), (192,193), (192,194), (192,196), (192,224)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_231.map (· &&& dom_231)
def goalM : Nat := goal_231 &&& dom_231
def NN : Nat → Nat
|4=>5
|5=>16
|6=>36
|7=>9
|8=>1
|_=>0
def HT : Nat → Nat → Nat
|4,0=>0xe4419b231457ff72d2a2120c3
|5,0=>0xdcc1cd2f2ccf661cb34dc1fe1ab058aab17a09fa3511631cb925aa516faf15cb80e8510537504809
|6,0=>0xe7235e5f54e200ed2f2cbe3f3b62059be118ed1b892907edf57b6f27240071ca66cfb66a01068965655755f7ec5cba85bee859593533b0484f8404073add636351351a830940307152d6012a3d4261e81ef741cd950e4bb0e302
|7,0=>0xcfe69aea08956897ec8772dc271ca6597bc3752b32cc3
|8,0=>0xa090d
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xff000000ff000000000000000000000000000000000000000000000000000000000000000055000000000000005500000000ff000000ff0000000000000000000000ff000000ff000000ff00000000ff000000cc000000ff000000cc000000ff000000cc000000ff000000cc5500000055000000550000005500000000000000000000000000000000000000000000000000000000000000000000000000000000ff00000000ff000000ff000000ff00000000000000ff000000ff000000000000000000000000000000000000000000000000ff00000000000000ff0000000033000000330000003300000033000000330000003300000033000000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000000000000ff00000000000000ff000000ff00000000000000ff00000000330000003300000000000000330000003300000033000000000000000000000000000000000000000000000000ff000000ff000000ff0000000000000000ff00000000000000ff00000000000000000000000000000000ff00000000000000ff0000000000000000000000000000000000000000ff00000000000000ff00000000000000ff000000000000000000000000ff000000ff000000ff000000ff000000ff00000000000000ff00000000aa000000aa000000aa000000ff000000aa000000aa000000aa000000aaff000000ff000000ff000000ff00000000000000000000000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000ff000000aa000000ff000000aa000000aa000000aa000000aa000000aaff000000ff000000ff000000ff000000ff000000ff000000ff00000000ff000000ff000000ff00000000000000ff000000ff000000ff00000000ff000000cc000000ff000000cc000000cc000000cc000000cc000000ccff000000ff000000ff000000ff000000ff000000ff00000000000000000000000000000000ff000000ff0000000000000000000000ff00000000ff000000f0000000ff000000f0000000f0000000f0000000f0000000f000000000ff00000000000000ff000000ff000000ff000000ff00000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f0cc000000cc000000cc000000cc000000cc000000cc000000cc000000ccaa000000aa000000aa000000aa000000aa000000aa000000aa000000aaff000000ff0000000000000000000000ff000000ff0000000000000000
|0,1=>0x3300000033000000330000003300000000000000000000000000000000550000005500000055000000000000005500000055000000550000000000000000ff00000000000000ff00000000000000ff000000000000000000000000ff0000000000000000000000ff000000ff0000000000000000ff00000055000000ff00000055000000ff00000000000000ff0000000000000000000000000000000000000000ff000000aa000000ff000000aaff000000ff000000ff000000ff000000cc000000cc000000cc000000cc3300000033000000330000003300000033000000000000003300000000aa000000aa000000aa000000aa000000ff000000aa000000ff000000aaaa000000aa000000ff000000ff000000aa000000aa000000aa000000aa0000000000000000ff000000000000000000000000000000ff00000000ff000000ff000000ff000000ff0000000000000000000000ff000000003300000033000000330000003300000033000000330000000000000000ff000000ff000000ff000000ff00000055000000000000005500000000ff000000ff000000ff000000ff000000ff000000cc000000ff000000cc00000000cc00000000000000cc000000cc000000cc000000cc000000ccff000000ff0000005500000055000000ff000000ff0000000000000000ff000000000000000000000000000000ff00000000000000ff00000000aa00000000000000aa00000000000000ff00000000000000ff00000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x1124c0c204734a0c204044c0c20593550c204030305700d30205600d3032011c02430811d13d50c204030304050d4c308101218308101124308140d3c508100c0c238034c14204700c0c22c700a1420402450811c90c80471850810040c2040
|1=>0x4034c0c102634c0c206500d90c0c204034c0c804034c0c205900d3038c100d30308188d28c0c204034c84308100d3200c204034c6030811c03180c20407cc0c205e00d60308101274c0c204035c3c308100d3cc0c20406cc68308100d3c3081
|2=>0xd30308100d48c0c204700d30308100d7c93030b100d3030810303490c204035130308164d303081bcd30508100db8c0c204036d30308100d3060c204035c303b0100d303081ac036a30308100d3cc0c204034c0c2a4034c0c204040d3270c2
|3=>0x30308100d30308100dc8c0c204035130308100d6dc30308100d303b0204034f303081
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>0x14507a82940aa005
|5,0=>0x38b1ad8cca6062d315189cc4862130f186cc30615a89583ec196
|6,0=>0xb13d6dea8f4e6a43509a76f34796bc99e3ef18788bc2da08efd77bb3c1dd2ee366e3b599a0cc97613aedd68ead7533a81932e92745ba11cfcc777
|7,0=>0x1a17cd3e4df18f857bf3dddee0f697
|8,0=>0x1a86
|_,_=>0
def dictMask : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def wireSAt (i : Nat) : Nat := if i < 51 then (dictB (i / 512) (i / 32 % 16) >>> (232 * (i % 32))) &&& dictMask else 0
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
|0=>0x8d8c3404d823108d4c3530d803500d812600c4c1e34c004530d004730d017d00d8da108780350914d30091cd3001b41363c04c3531bcc3730dcc3634c8d31307cc3430d584930dcc36
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0xc00000000000000000000000000000000
|6,0=>0x7c9e1745b2648000000000000000000017200161508000012200102388c2000b128400000821c461000510c800
|7,0=>0x291a0671986519063188611
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
|0=>0xb9db997d17b55f15bd3f139930020e209180088081080061060040020014009008006004001000
|_=>0
def pmB : Nat → Nat → Nat
|5,0=>0x20000000000018000
|6,0=>0x72d6164000008002040d0800f0042a0456003d0601ca9
|7,0=>0x16cde9696273
|8,0=>0x15
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 5 (j % 128); fld (pmPalB (k / 32)) 12 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_227,7,runOps true dom_227 (0,roots_227) ops)] else [])++(if pm.testBit 1 then [(dom_195,4,runOps true dom_195 (0,roots_195) ops)] else [])++(if pm.testBit 2 then [(dom_197,4,runOps true dom_197 (0,roots_197) ops)] else [])++(if pm.testBit 3 then [(dom_199,5,runOps true dom_199 (0,roots_199) ops)] else [])++(if pm.testBit 4 then [(dom_229,6,runOps true dom_229 (0,roots_229) ops)] else [])++(if pm.testBit 5 then [(dom_165,5,runOps true dom_165 (0,roots_165) ops)] else [])++(if pm.testBit 6 then [(dom_166,5,runOps true dom_166 (0,roots_166) ops)] else [])++(if pm.testBit 7 then [(dom_167,6,runOps true dom_167 (0,roots_167) ops)] else [])++(if pm.testBit 8 then [(dom_230,6,runOps true dom_230 (0,roots_230) ops)] else [])++(if pm.testBit 9 then [(dom_103,5,runOps true dom_103 (0,roots_103) ops)] else [])++(if pm.testBit 10 then [(dom_228,5,runOps true dom_228 (0,roots_228) ops)] else [])++(if pm.testBit 11 then [(dom_102,4,runOps true dom_102 (0,roots_102) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_231 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · exact cpcs (by decide +kernel) lowS_197 _ g hchk
    · exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · exact cpcs (by decide +kernel) lowS_166 _ g hchk
    · exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · exact cpcs (by decide +kernel) lowS_103 _ g hchk
    · exact cpcs (by decide +kernel) lowS_228 _ g hchk
    · exact cpcs (by decide +kernel) lowS_102 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_227 7 s (0, roots_227) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_231 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_227 h

def symsG : List (List (Nat × Nat)) := [[(0xffffffff00000000ffffffff00000000, 96), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_231 == dom_231) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_231 goalM v ys) : RunD true dom_231 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_231 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 36 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 36 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 9 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 8) : ∀ i < NN s, bar true dom_231 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
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
  scr true dom_231 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 8) (h : RunD true dom_231 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_231 roots_231 goal_231 9 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_231

theorem lowS_231 : Lower true dom_231 roots_231 goal_231 9 := S_231.noCircuit

theorem lowS_246 : Lower true dom_246 roots_246 goal_246 9 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x55005500550055000000000000000000550055005500550000000000000000, 2, 66)] (by decide +kernel) (by decide +kernel) lowS_182

theorem lowS_250 : Lower true dom_250 roots_250 goal_250 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x500050005000500050005000500050005000500050005000500050005000500, 128, 136)] (by decide +kernel) (by decide +kernel) lowS_242

def isoMvS_159 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]
theorem lowS_159 : Lower true dom_159 roots_159 goal_159 8 :=
  lower_iso isoMvS_159 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_95

def isoMvS_187 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]
theorem lowS_187 : Lower true dom_187 roots_187 goal_187 8 :=
  lower_iso isoMvS_187 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_119

def isoMvS_189 : List (Nat × Nat) := [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)]
theorem lowS_189 : Lower true dom_189 roots_189 goal_189 8 :=
  lower_iso isoMvS_189 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_175

def isoMvS_222 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]
theorem lowS_222 : Lower true dom_222 roots_222 goal_222 8 :=
  lower_iso isoMvS_222 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_215

def isoMvS_235 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcccccccccccccccccccccccccccccccc, 126), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)]
theorem lowS_235 : Lower true dom_235 roots_235 goal_235 8 :=
  lower_iso isoMvS_235 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_207

def isoMvS_237 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 124), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)]
theorem lowS_237 : Lower true dom_237 roots_237 goal_237 9 :=
  lower_iso isoMvS_237 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_231

def isoMvS_238 : List (Nat × Nat) := [(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]
theorem lowS_238 : Lower true dom_238 roots_238 goal_238 8 :=
  lower_iso isoMvS_238 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_175

def isoMvS_243 : List (Nat × Nat) := [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]
theorem lowS_243 : Lower true dom_243 roots_243 goal_243 10 :=
  lower_iso isoMvS_243 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_219

def isoMvS_252 : List (Nat × Nat) := [(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]
theorem lowS_252 : Lower true dom_252 roots_252 goal_252 8 :=
  lower_iso isoMvS_252 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_175

def dzo_158_1:=0xaaaaaaaa000000000000000000000000aaaaaaaa
def gzo_158_1:=0xaaaaaaa8000000000000000000000000aa88aa00
def gsh_158_1:=0x5555555400000000000000000000000055445500
theorem lowS_zo_158_1_150:Lower true dzo_158_1 roots_158 gzo_158_1 6:=lower_iso (d1:=dom_158) (roots1:=roots_158) (T1:=gsh_158_1) [(dom_158,1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_158_1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x5500550000000000000000000000000055005500,0,8)] (by decide +kernel) (by decide +kernel) lowS_150)
def dzo_175_16:=0xffff0000ffff00000000000000000000ffff0000ffff0000
def gzo_175_16:=0xffff0000ffff00000000000000000000fefe0000eecc0000
def gsh_175_16:=0xffff0000ffff00000000000000000000fefe0000eecc
theorem lowS_zo_175_16_45:Lower true dzo_175_16 roots_175 gzo_175_16 6:=lower_iso (d1:=dom_175) (roots1:=roots_175) (T1:=gsh_175_16) [(dom_175,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_175_16) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xcccc0000cccc00000000000000000000cccc0000cccc,0,2),(0xffff0000ffff00000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_45)
def dzo_61_2:=0xcccccccccccccccc
def gzo_61_2:=0xccccc8c8cccc8800
def gsh_61_2:=0x3333323233332200
theorem lowS_zo_61_2_45:Lower true dzo_61_2 roots_61 gzo_61_2 5:=lower_iso (d1:=dom_61) (roots1:=roots_61) (T1:=gsh_61_2) [(dom_61,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_61_2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x3333000033330000,0,16)] (by decide +kernel) (by decide +kernel) lowS_45)
def dzo_189_2:=0xcccccccccccccccc0000000000000000cccccccccccccccc
def gzo_189_2:=0xcccccccccccccccc0000000000000000ccccc8c8cccc8800
def gsh_189_2:=0x333333333333333300000000000000003333323233332200
theorem lowS_zo_189_2_45:Lower true dzo_189_2 roots_189 gzo_189_2 6:=lower_iso (d1:=dom_189) (roots1:=roots_189) (T1:=gsh_189_2) [(dom_189,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_189_2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x333300003333000000000000000000003333000033330000,0,16),(0x333333333333333300000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_45)
def dzo_150_1:=0xaa00aa00000000000000000000000000aa00aa
def gzo_150_1:=0xaa00a800000000000000000000000000880000
def gsh_150_1:=0x55005400000000000000000000000000440000
theorem lowS_zo_150_1_150:Lower true dzo_150_1 roots_150 gzo_150_1 5:=lower_iso (d1:=dom_150) (roots1:=roots_150) (T1:=gsh_150_1) [(dom_150,1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_150_1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [] (by decide +kernel) (by decide +kernel) lowS_150)
def dzo_190_1:=0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa
def gzo_190_1:=0xaaaaaaaaaaaaaaa80000000000000000aaaaaaaaaa88aa00
def gsh_190_1:=0x555555555555555400000000000000005555555555445500
theorem lowS_zo_190_1_150:Lower true dzo_190_1 roots_190 gzo_190_1 7:=lower_iso (d1:=dom_190) (roots1:=roots_190) (T1:=gsh_190_1) [(dom_190,1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_190_1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x550055005500550000000000000000005500550055005500,0,8),(0x555555550000000000000000000000005555555500000000,0,32)] (by decide +kernel) (by decide +kernel) lowS_150)
def dzo_47_16:=0xffff0000ffff0000
def gzo_47_16:=0xfefe0000eecc0000
def gsh_47_16:=0xfefe0000eecc
theorem lowS_zo_47_16_45:Lower true dzo_47_16 roots_47 gzo_47_16 5:=lower_iso (d1:=dom_47) (roots1:=roots_47) (T1:=gsh_47_16) [(dom_47,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_47_16) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xcccc0000cccc,0,2)] (by decide +kernel) (by decide +kernel) lowS_45)
def dzo_173_16:=0x333300003333000000000000000000003333000033330000
def gzo_173_16:=0x333300003333000000000000000000003232000022000000
def gsh_173_16:=0x33330000333300000000000000000000323200002200
theorem lowS_zo_173_16_45:Lower true dzo_173_16 roots_173 gzo_173_16 5:=lower_iso (d1:=dom_173) (roots1:=roots_173) (T1:=gsh_173_16) [(dom_173,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_173_16) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x33330000333300000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_45)
def dzo_186_1:=0xa0a0a0a0a0a0a0a00000000000000000a0a0a0a0a0a0a0a
def gzo_186_1:=0xa0a0a0a0a0a0a0800000000000000000a0a0a0a0a080a00
def gsh_186_1:=0x50505050505050400000000000000000505050505040500
theorem lowS_zo_186_1_146:Lower true dzo_186_1 roots_186 gzo_186_1 6:=lower_iso (d1:=dom_186) (roots1:=roots_186) (T1:=gsh_186_1) [(dom_186,1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_186_1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x50005000500050000000000000000000500050005000500,0,8),(0x50505050000000000000000000000000505050500000000,0,32)] (by decide +kernel) (by decide +kernel) lowS_146)
def dzo_182_1:=0xaa00aa00aa00aa000000000000000000aa00aa00aa00aa
def gzo_182_1:=0xaa00aa00aa00a8000000000000000000aa00aa00880000
def gsh_182_1:=0x5500550055005400000000000000000055005500440000
theorem lowS_zo_182_1_150:Lower true dzo_182_1 roots_182 gzo_182_1 6:=lower_iso (d1:=dom_182) (roots1:=roots_182) (T1:=gsh_182_1) [(dom_182,1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_182_1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x5500550000000000000000000000000055005500000000,0,32)] (by decide +kernel) (by decide +kernel) lowS_150)
def dzo_45_16:=0x3333000033330000
def gzo_45_16:=0x3232000022000000
def gsh_45_16:=0x323200002200
theorem lowS_zo_45_16_45:Lower true dzo_45_16 roots_45 gzo_45_16 4:=lower_iso (d1:=dom_45) (roots1:=roots_45) (T1:=gsh_45_16) [(dom_45,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_45_16) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [] (by decide +kernel) (by decide +kernel) lowS_45)
namespace S_191
def pairsG : List (Nat × Nat) := [(1,9), (1,33), (2,18), (2,130), (3,11), (3,19), (3,35), (3,131), (4,36), (4,132), (5,13), (5,37), (5,133), (6,22), (6,38), (6,134), (7,15), (7,23), (7,39), (7,135), (8,9), (8,136), (10,11), (10,26), (10,138), (12,13), (12,44), (12,140), (14,15), (14,30), (14,46), (14,142), (16,18), (16,144), (17,19), (17,25), (17,49), (17,145), (20,22), (20,52), (20,148), (21,23), (21,29), (21,53), (21,149), (24,25), (24,26), (24,152), (28,29), (28,30), (28,60), (28,156), (32,33), (32,36), (32,160), (34,35), (34,38), (34,50), (34,162), (40,41), (40,44), (40,168), (42,43), (42,46), (42,58), (42,170), (48,49), (48,50), (48,52), (48,176), (56,57), (56,58), (56,60), (56,184), (128,130), (128,132), (128,136), (128,144), (128,160), (129,131), (129,133), (129,137), (129,145), (129,161)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfffffffffffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_191.map (· &&& dom_191)
def goalM : Nat := goal_191 &&& dom_191
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
|3,0=>0x549be
|4,0=>0x96ebb4514e40d10407492233a1fcbd
|5,0=>0xf1dc3ec637c4e4baabe6a18fb9471f903788d9ba7b9fd6ce886a45b677476483760e2b4fb8e4b7504b1892af902a6fd1760c116350e68c0d6240ac98
|6,0=>0xe85eadac88da774da6c1d9825d925ed8982d6511d5b7ed5ab2cf88bcecf1cb20fc2e8ac1097bf73fb7bfdb4cedaaf9da8c49a65ae9f15f9bc899adb899e0d982a1919728f6ad8e2da8a09a87815861c585e617beec77c8b778c8774fa74e9b74df472c017218770c5c704306f2776c5866a74e625a8617fa5bb455a2ce5966b5779e547b6532044f0384eaff4d8df4d7684c47c4c16c4803a3a80437dd735b4833fb630e333001a2f9d02ed562c8902bc5d2bb6821f3c21df720e94209941f8841ca561c48f1b90c1a28d190cc18064156d812b1a11e23110c70bd790a20005b76015b3
|7,0=>0xc7ba3c4ef1c158abffd3bb79bb847ab7cdcb28bab272faea82ac401abf8eab9c7a8607a81d7a62fea484da0c0ba0b919fd889dacb9753f94826939259239d906818f04f8ecff8e6018cd678b6f38a2ac88924887118487b804ea7f9d37e5a77c1837710674c0972aa672975725a8704656c0be6b27a6af1d6ad846a45c6938e6640965a4964fa6623b562046612335edc35e7045d9605c1925be295bcbb5a7475976558b1b56d64504344ee9e4a49949e7548bce488004774c46d9f46cbe465ae461a145244442c8439094348d42817417363b5043a304327f0321642d5c92c88729a0d27437232d221ca81fa271ebe51e1e71d8121ce661b4651b4131a74a1a05b19b8c18bf8171f9171c51434910f13107f61004f0bff30ab900aa230a2370998608803080d806e00069d405a660599d043d30379602f700213901c2a016bf
|7,1=>0xef46fe78a1e4159e3a86e33c2de8bcd5b7ec89d9
|8,0=>0xfd87df517fec497e64a0e4eabe2252dd2f9d8106d6d6cd6c84d56d9d29c5ceb9bcaa4cc8f45c86a3c81acc7c8cba4fcb9a7cb94f5b4889b46c8b292eb1fd1b1e5cb0d3eaec39abb4ba911ea0c0b993049622a95ab89471a8ea4d8bf10852637b84475f1674f45728fa71cb8714976f8da6d7246b44768845649e75f8b35db0d5b8155b3435a11459ec050a764b5774aa60404f93afa83770f3441b300c92d0d3294de26413236a8213771f7c61f5de1dd9d196e2177f11666515270150c8149e813e9213be7102d10d8a40b15400007
|9,0=>0x7bdcb7b9cf76bd8741ab43c00424f63379831353203831764517374
|10,0=>0xe26d2
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xffffccccffffcccc0000000000000000ffffccccffffcccc0f0f0f0f0f0f0f0f00000000000000000f0f0f0f00000000bbbbbbbbbbbbbbbb0000000000000000aaaaaaaaaaaaaaaa333333333333333300000000000000000000000000000000bbbbbbbbbb00bb000000000000000000aaaaaaaaaa00aa00aaaabbbbaa00bb000000000000000000aaaaaaaaaa00aa00ffffffffffccffcc00000000000000000000000000000000ffffffffffccffcc0000000000000000ffffffffffccffccffffffffffffffcc0000000000000000ffff0000ffff0000aaaaffffaaaaffff0000000000000000aaaaaaaaaaaaaaaa0000ffff0000ffff00000000000000000000000000000000ffffffff0000ffff0000000000000000ffffffff00000000aaaaffffaa00ff000000000000000000aaaaaaaaaa00aa00ffffffffffffffff0000000000000000ccccccccccccccccffffffffff00ff000000000000000000ffffffffff00ff00ffffffffffffffff0000000000000000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaaff00ff00ff00ff000000000000000000ff00ff00ff00ff00ffffffffffffffff0000000000000000ffffffffcccccccc3333333333333333000000000000000033330000333300000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0000ffff0000ffff00000000000000000000cccc0000cccc00000000ffff0000ffff00000000000000000000ffff0000ccccffffffff000000000000000000000000ffffffff00000000ffffffffffffffff00000000000000000000000000000000ffff0000ffff00000000000000000000ffff0000cccc0000cccccccccccccccc0000000000000000ccccccccccccccccffffffffff00ff000000000000000000aaaaaaaaaa00aa00ffffffffffffffff0000000000000000ffffffff00000000ffff0000ffff00000000000000000000ffff0000ffff0000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0ffffffffffccffcc0000000000000000eeeeaaaaeeccaa00
|0,1=>0xcccccccccccccccc0000000000000000cccccccccccc0000ffffffffffffffff0000000000000000ffffffffff00ff00f0f0fffff0f0ffff0000000000000000f0f0f0f0f0f0f0f0cccccccccccccccc0000000000000000cccc0000cccc000000ff00ff00ff00ff000000000000000000aa00aa00aa00aa0000000000ff00ff00000000000000000000000000000000ffffffff00ff00ff0000000000000000ffffffff000000000f0f0f0f000f000f00000000000000000f0f0f0f00000000555555555500550000000000000000005555555555005500ffffffffffffff00000000000000000000000000000000000f0f0f0f00000f0f00000000000000000f0f0f0f0000000000000000ffffffff000000000000000000000000ffccffccffffffffffffffff00000000000000005555555555005500fffff0f0fffff0f000000000000000000000000000000000fffff0f0fffff0f00000000000000000fffff0f0fffff0f0ffffffffffffffff0000000000000000ffff0000ffff0000fffffcfcfffffcfc0000000000000000ccccccccccccccccffffffffffffff000000000000000000ffffffffffffff0000000000000000000000000000000000ffffffffffffff00ffffffffffff000000000000000000000000000000000000ffffffffffff00000000000000000000ffffffffffff0000fffffffffffff0f00000000000000000f0f0f0f0f0f0f0f0aaaabbbbaaaabbbb0000000000000000aaaaaaaaaaaaaaaa00aa00bb00aa00bb000000000000000000aa00aa00aa00aa0f0f0f0f0f030f0300000000000000000f0f0f0f0f000f00fffffffffffcfffc0000000000000000f0f0f0f0f0f0f0f00f0f0f0f0f0f0f0f0000000000000000050505050500050000000000ffffffff000000000000000000000000550055000000ffff0000ffff00000000000000000000ffff00000000ffffffff333333330000000000000000ffffffff000000000f0f0f0f0303030300000000000000000f0f0f0f000000000000000000000f0f00000000000000000f0f0f0f00000000
|0,2=>0xf0f0f0f0000030300000000000000000f0f0f0f00000000ffffffffcccccccc00000000000000000000000000000000ffffffffffffcccc0000000000000000ffff0000ffff000000000000ffffffff0000000000000000000000000000000000000000ffffffff000000000000000000000000ff00ff00000000000f0f0f0f000000000000000000000000000000000000cfcf0000cfcf00000000000000000000cfcf0000cccc000033330000333300000000000000000000000000000000ffffffff000033330000000000000000ffffffff00000000ffffffff0f0f0f0f0000000000000000ffffffff0f000f000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f000f00fffffffffffff0f00000000000000000ffffffff000000007777777777337733000000000000000055555555550055000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0c0f0ccfcf0000cfcf00000000000000000000cfcf0000cccc0000ffffffffcccccccc0000000000000000ffffffffccccccccffffffffffffffff0000000000000000f0f0f0f0f0f0f0f003030303030303030000000000000000f0f0f0f0f0f0f0f00f0f0f0f0f0f0f0f00000000000000000f0f0f0f0c0c0c0ccccc0000cccc00cc0000000000000000cccc0000cccc0000ffff0000ffff00000000000000000000ffff0000ffcc000000000000003300000000000000000000ffff0000ffff0000ffffffffffffffcc0000000000000000ccccccccccccccccffffffff00ff00ff0000000000000000ffffffff00ff0000ccccccccccffccff0000000000000000cccccccccccccccc0000cccc0000ccff00000000000000000000cccc0000cccc0000ffff0000ffff00000000000000000000ffff0000ffccffffffffffffff000000000000000000ffffffff0000000000000000ff00ffff000000000000000000000000ff00ff00ffffffff003300330000000000000000ffffffff00000000ffffffffffffffff0000000000000000ffffffffffff000000000000333333330000000000000000ffffffff00000000
|0,3=>0x333333333333333300000000000000003333303033333030333300003333333300000000000000003333000033330000ffff0000ffff00ff0000000000000000ffff0000ffff000000000f0f00000f0f000000000000000000000f0f000000000000cfcf0000cfcf00000000000000000000cccc0000cccc00000000333300000000000000000000ffff0000ffff000000bb00bb00bb00bb000000000000000000aa00aa00aa00aaffffffffffccffcc0000000000000000ff00ff00ff00ff00cfcfcfcfcfcfcfcf0000000000000000cccccccccccccccc0f0f0f0f0f0f0f0f00000000000000000000000000000000cfcf0000cfcf00000000000000000000cccc0000cccc0000000000003333333300000000000000000000000000000000aaaaaaaabbbbbbbb0000000000000000aaaaaaaaaaaaaaaa333333333333333300000000000000003333333333003300ffffffffffffffff0000000000000000fffff0f0fffff0f0cccccccccccccccc0000000000000000ccccc0c0ccccc0c00000ffff0000ffff00000000000000000000cccc0000ccccffff0000ffffffff0000000000000000ffff0000ffff0000cccc0000cccccccc0000000000000000cccc0000cccc000003030000030300000000000000000000ffff0000ffff0000ccccffffccccffff0000000000000000cccccccccccccccc030303030303030300000000000000000000000000000000abababababababab0000000000000000aaaaaaaaaaaaaaaaffffffffff33ff330000000000000000ffffffffff00ff00fcfcfcfcfcfcfcfc00000000000000000000000000000000fcfcfcfcfcfcfcfc0000000000000000fcfcfcfcfcfcfcfcfffffffffcfcfcfc0000000000000000ffffffff00000000ffffffffffffffff0000000000000000ffffffffffffff00fffffff0fffffff00000000000000000ff00ff00ff00ff00ffffffffeeeeeeee0000000000000000aaaaaaaaaaaaaaaaf3f3f3f3f3f3f3f30000000000000000f0f0f0f0f0f0f0f0fffffafafffffafa0000000000000000aaaaaaaaaaaaaaaa
|0,4=>0xffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffff0000afafafafafafafaf0000000000000000aaaaaaaaaaaaaaaa0000fcfc0000fcfc00000000000000000000fcfc0000fcfcffffffffffffffff0000000000000000fcfcfcfcfcfcfcfc0f0f0f0f0f0f0f0f00000000000000000c0c0c0c0c0c0c0c00000000000000000000000000000000fffff0f0fffff0f0fffffcfcfffffcfc0000000000000000fffffcfcfffffcfcffffffffffffcccc0000000000000000ffffffffffffccccffff3333ffff33330000000000000000ffff0000ffff0000333333333333333300000000000000003030303030303030ccccccccffffffff0000000000000000cccccccccccccccc33333333333333330000000000000000222222222222222200000000ffffffff000000000000000000000000cccccccc00000f0f00000f0f000000000000000000000000000000000000ffff0000cccc00000000000000000000ffff0000cccc0000ffff0000ffff00000000000000000000f0f00000f0f0aaaaaaaaffffffff0000000000000000aaaaaaaaaaaaaaaa0000000000ff00ff00000000000000000000000000cc00ccfffffffffcfcfcfc0000000000000000f0f0f0f0f0f0f0f0f0f0f3f3f0f0f3f30000000000000000f0f0f0f0f0f0f0f0ffffffffffffcccc0000000000000000ccccccccccccccccffffffffffffffff0000000000000000ffffccccffffcccc00000000000000000000000000000000ffffffffffccffcccfcfcfcfcfcfcfcf0000000000000000cfcfcfcfccccccccfffffcfcfffffcfc0000000000000000ffff0000ffff0000ffffffffffffffcc0000000000000000ffffffffffffffcc333333333333330000000000000000003333333333333300000000000033003300000000000000000000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x20e050f20031f02010504030201050415030205041e080201040c07030201051b0711030205100b110301050a10110301051009080201051a0711030601051011081701120f1402010513070801050a04070302011205040d0302010504030201040c030205040b0301050a0403010504090802010007030601050403020100
|1=>0x2010533240708300e012f0f110801050a100711030201120510110d03020105102d11030201050f03020e2a050f181108010a0f0708020105292807110802050f2707080201051b0703020105040711030226050f1102052524070302010504231122010a0f0711030201100c140201050407030205041e07080e0a0f210703
|2=>0x36081f0201050407080201050407153e080201050f19080e3d013c0f07110302010f0c070801050a103b0708020e0f0c1e07113902050f380703020e050f1e2c11080201370c0711030201050f36111402050f3507110302010516070308020e05100b08020e05161e07110201050f340703080e01050a1003080e0105100911
|3=>0x51d0711080201100c0711480201050f07110801050f4607110801050f4507110802010529071114020105370708020e120f210711440201050f0711030205371e07110201050f430708020e051d210711420201050f071108010a0f071c110302013f0f070340020e01050f08020e3f0f1e0711081f3001120f11083001050f
|4=>0x30020105040708020e05103507080e51050f1e070308020e013f105003020e05101e08020e4f4e050f110302050f4d07080201100c3b07110802014c0f0722080e010a0f0711084b01050f0711031f0201051011220201120f071103020105101511084a01050f070308020e01100c11030205101e11080201490f0711220201
|5=>0xf1e0907030201050403020e05101e5c110802010f0c07110801050a3707110302010510231102050f555b0703020e05101e5a080e050f1e590711570201050f0711080226050f07115602050f55070802010513071554020e4f050f110802010553071108020533250711140201051007110802050f520711030205101e0708
|6=>0x8020e050f210708020e0105620711031f0201050f0708020e610105100711140201050f07081f020e050f1e0711030201050f071508020e0105600708020e050f1e07150308020e010f0c0711081f0201053707110302050f1e0708020e050f5f07110301050a0f07085d0e01120f110301050f0907080e050a0f1e07080e05
|7=>0x71108020105330711080201120f071c086c0e01050f074111030201050f07080e010a0f071c4108020e050f1e07081f300e01120f110830020112050f11080201051d071c110802016b050f0708020e010569076811080201050f071103020105100708020e05101e0765020e01050f076411080201050f0708026301050f07
|8=>0x80201051007152208020e01051d0708310e013c0f0708020e01100c0711080201050f1c1511080201050f720708020e01700f0708020e0105290708060e01050f072e11030201050f0711081f3001050f0711080112050f6f07110802010537071c0308020e013f0f0708020e016d0f075003020e050f1e072208020e050f21
|9=>0x308020e050f4d07183e080201050f0711030201050f073a08020e050f0b07080e01050f09072b03020e01051003081f020e0105102208020e01120f0703020e0105105c080e0105750f0708020e01057307110201050f5b070308020e0105101511081f020105100708020e4f050f672e11083001050f070308020e05101e11
|10=>0x51d07087a0e01050f0711080201050f6f071103300201050f0703020e050f1e075c0830020e050f1e0711390201050f073a11080201051d07110830020105370711030201050f2307080201051d79071c08020e050f1e2307081f020105103b07410308020e01051008027801050f0703020e050f1e075a08020105103b0715
|11=>0x78211080201050f07080e4f01050a0f0711390201050f0711083002013c0f07110801050a0f0711080201050f810711080201050f07802b080e013c0f0708020e010f7f0708020e010f7e0711087d0201050f0708020e050f1e7c071408020e010510070308020e05101e0708020e4f01700f07080e01050f7b0708020e4f01
|12=>0x80201050407110830020105100708020e010f0c070308020e01051023110802050f550703020e01050f2c11140201050f07151108300201050f1c11080201050f07195708020e01050f0708020e050f35071508300e01050f328511080201050f070308020e01051d0708020e84050f1e0708830e01050f073e110201050f5b
|13=>0x2010f0c07110302010537072e18080201050f0711080201050f8a0708020e89050f073e080201050f073a0830020105103b0708020e8801050f0708020e6101051d0708020e4f010f7f0708300e3d01050f0708020e01870f07080201051d790703080e01050a0f0703080e01050f090708020e01120f5e030830020e010510
|14=>0x8020e4f01050f8c0708020e4f050f077608020e010510075c0d08020e01050f070830020e4f01050f0708020e6601120f07081f020e0105100708020e01051007151108300201050f0708020e01058b071108860201050f0711080201050f0758080e01050a10073e110802050f550711030201051008020e4f010f0c071108
|15=>0xe01050a0f0708020e01050f073208020e3d01050f07030830020e01050f0708020e01050f6f070308020e01050f230708020e01051d0708020e0191050f070831020e4f050f0708020e010516071508020e010510900708020e01050f8f0708020e6101050f071c08020e01050f078e08020e01050f8d072b08020e01051007
|16=>0x711030201050f0708020e0177050f0708020e050f1e070830020e010510071108020105370708020e01050f072c1408020e01050f07150896020e01050f070830020e01050f1c0895020e01050f0708020e66010510073e11080201050f079408020e01050f070893020e01050f0708020e01050f92070830020e013c0f0708
|17=>0x79c08020e4f01050f0715110802010510079b08020e01050f0711081f0201050f0711080201050f071508020e010f0c0708020e01058b075c08020e01059a0708020e01050f99070830020e010f0c075003020e01050f071811080201050f075008020e01120f0708020e9801050f070d0308020e01050f0708020e01050f97
|18=>0x703020e01050f075c0308020e01050f07150308020e050f1e0708020e01050f230708020e01051007762b50020e01050f07081f020e01120f070831020e66050f0708020105103b070886020e01050f0708020e4f0105100708020e984f01050f07081f020e4f01050f070308020e01051008020e01050f075808020e01050f
|19=>0x7150308020e01050f070831020e01050f075008020e01050f0708020e01050f077608020e4f01050f0711080201050f0708020e0112050f0708020e01050f1c1511080201050f073a08020e0105105c08020e01120f071c08020e01059a07760830020e0112050f0308020e0105100703081f020e01050f071408020e01050f
|20=>0x8020e01050f0708020e0105100708020e01050f075c081f020e01050f0708020e01050f
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>4
|4,0=>0x1d50185013500e500950045
|5,0=>0xab60a5609f60996093608d60876081607b6075606f606a5064605e60586052604c60466040603a6034602e602860226
|6,0=>0x265725e7257725072497242723b7234722d7226721f72187211720b620471fd71f671ef71e871e171da71d371cc71c571be71b771b071a971a2719b7194718d7186717f71787171716a7163715c7155714e7147714071397132712b7124711d7116710f7108710170fa70f460ed70e670df70d870d260cb70c470bd70b760b16
|6,1=>0x31e73177311630a730372fc72f752f072e972e272db72d472cd72c672bf72b872b172aa72a4629d7296728f72887281727a7273726c7
|7,0=>0x50084f884f084e884e174da74d374cb84c384bc74b574ae74a7749f849784907488848174798471846a7463745b8453844c7445743e7436842e8426841e8416840f740783ff83f873f083e973e183da73d283cb73c383bb83b383ac73a4839d7396738f7387838073797372736a8362835b7353834b8344733c8334832c83257
|7,1=>0x6ec86e486dd76d586cd86c586bd86b586ad86a6769f7697868f86887680867a6672866b7663865c7655764d8645863d8635862d8626761e8616860e860775ff85f785ef85e875e085d975d185c985c275bb75b475ac85a4859c8594858c8585757d8576756e8566855e8556854e8547753f8537852f8527851f8517851075088
|7,2=>0x727871f87187710870a670286fb76f47
|8,0=>0x927891e9915990e790688fe88f598ee78e688de88d688cf78c788c078b888b088a888a0889888908887987f8878787088697861885a7852884998418839883188298821881988118809880187fa77f287ea87e197d987d097c977c187b987b187a987a187989790878887808777976f8767875f8756974e8746873e8736872f7
|8,1=>0x9bf89b789b079a889a0899889908987997f8977896e9966895e8956894e8946893e8937792f8
|9,0=>0xa167a0e8a0689fe89f689ee89e689de89d689cf79c78
|10,0=>0xa1d7
|_,_=>0
def dictMask : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffff
def wireSAt (i : Nat) : Nat := if i < 157 then (dictB (i / 512) (i / 32 % 16) >>> (192 * (i % 32))) &&& dictMask else 0
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
|0=>0x80e4201d2e07c04b108074ac1c080244808050744415080e44474080e43c71050784440080e43c1d08074201d01194601c110542039111003c1d080e4201d111002055020783c1d080e44440080e43c1d080744440080743c1d080e444400f0740c07080e4201d111d03c7105078141d02194601c110542039081544458080e43c550207844400f0740c15080e4201d
|1=>0x80e43c71080e420710507844c2020751c0b053a4441e080e4081e110fcb80c080744409080e4443f0301c203908074601e11055041403024141d080e4081d2e070081d110242039111003c1d080e44440020783c1d080e4c01702074e407083a4441e080e4b81c080744409080e4203908154081e080e4201d0f154081e0833820390207414c93107004090f0740c15
|2=>0x80e40c07080e4201d5701c216102078084805074141d025e5401c08054340b030544440080743c1d080e40c070f074203908074f8070f0742039085841456020780465180704415080e44458080e43c5502078041d08324c41c010242055020783c1d080e43c1d080e4201d111003c1d080e4203903054201d080743c1d080e43c1d0301c20390807414d92e0704409
|3=>0x3024203908074141e02120141d02074081505074141d020742039080e43c71050782039020783da9011c8141e111c420390507820390f074201d0301c3c1d08074219d6607004152e0744409080e438c93107004092201c2071050783d79500702015080e4081508074203908154081e0301c201d080e4081e080743cc93107004090301c081e0807414c202074443f
|4=>0x80e4041d660700415020744409080e43c1d0301c201d020783c1d080e420710f1c4141e0102414c0020743c1d05308081d080e4141e0207815c44f024041d0f584145602078340803054201d080744409080e4203902074480b05074203905078443f080e5041403024201d056e00971080780c0708074207105078dc1d110fc2039080e4147105078099f660700415
|5=>0x80740c070807420e9110782039080e43c7105078443f080e40c0b080e4201d0e1d83c710507838420f0743c1d03024201d0e5e5401c080540c070e1083c1d0d01c0c1508074441d11054203911078203908075040703024201d0d02c0c1508074201d0f07420090807408150f074201e0f074201d0277015d9010783dd1081c8141e3e08c441d080e4081e0f0743c1d
|6=>0x301c201d02675981c01054f823110742039180244415080e4041d02120141d083a4441e080e4c014080e4203902120141d2e05c4409080e4601e1105420390802414c00207415c64f024041d056e809710807808e91107820390301c201d081543c1d020780c070f074201d057113c090107409de05764041e0f1c4141e025ed401c08054081d080e4201d0301c201e
|7=>0x80e438420f07405610207815c64f02414b12b07020090e1d83c7105078201d02120141d0d02c0c1505075401c08054081d0f074201d111003c1d080e43c1d080e6181702124141d0f074201d3e01c441d080e4201d2b0702009080e4205502078203902074141e180704415080e4216105158081e1401c205502078081d3107004091807c4415080e4201d0f1c4141e
|8=>0x207814420f074204a05074047105078045602079400b080543c1d080253c0b01074041e010743c1d080780c1508074081d0107404150507408150f0743c1d02078081d080e43d7108078203905158081e0f074084805074f807110742039080743c1d080e414c202074c01702074203908074443f080e4440911054203911128141d080e40579500702015113a4441e
|9=>0x20742015080744415080e4141d080553c15010740c1508074044a0507420390807415d9010780c07080743c1d02074443f080e4ac1c08024205502078c41f01024081d05078c415010243c1d01054441d080e54009080540871050793c170107414c002074084805074c41c01024045502078081d08074084a050740c0b080743c71050781571080780409010743c55
|10=>0x80781471050783dd901078081d050743c1d08074081508074205502078201e08074081e080740c07080740c0b08074041e0f07420090805408150507404150102438420f0740849050743c1d010753c15010740815010743c1d08074145602078205602078041d020783c1d080e4ac1f080240815080e420390207814c2020743d71080783dd901079980b0105414c2
|11=>0xf074201e02054081e08074040908054041e01074203905074141e02078441e080e43c1d
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0xa14000091000000001f506d00000000174000012500000f30000000000000000000a501540000000005
|6,0=>0x8a30000000000000021cc000000000000008341fd07b400007921d50000000073200006f41ad0000000069200006720000000190c604174c594000000015c80000000534000000013d04c3121000000000000000000118842400000000f903d10e5035400000000c502d4
|6,1=>0xb932dc8b342c480000000ad42b040000000a932a04a710000a3427d000026d0974000000024d0000240c8d30000000
|7,0=>0x5909613578d5b3560d553548d4f300014c3524d46350cd4124fc93c34e4d3634ccd3034b4d2a349cc000490d213478d1b3464916344cd103434d0b2424906340cd0033f4cfa30000f733d0cf133bc8ec33a4ce6338cce03374cda335ccd43344c000338ccc2324cc6330ccc122fc8bc3
|7,1=>0x820e053808dff37f49fb20001f920001f637ccdf037b89eb37a0de5378c9e037789db3760dd53748dcf3730dc93718dc33700dbe26ecdb836d4db236bcdad26a8da73690da13678d9b3660d96264cd903634d8a3620985300018235fcd7d25e8d7735d497235bcc0005b496a359cd661
|7,2=>0x21c3864e16384ce112838e0b3
|8,0=>0xa74a9b2a64a972a54a932a44a8f2a34a8b2a24a872a14a832a04a7f29f4a7b29e4a7729d4a7329c4a6f29b4a6b29a4a672994a632984a5f2974a5b2964a572954a532944a4f2934a4b2924a472914a432904a3f28f4a3b28e4a3728d4a3328c4a2f28b4a2b28a4a272894a232884a1f2
|8,1=>0x2c32b04abf2af4abb2ae4ab72ad4ab32ac4aaf2ab4aab2aa4aa72a94aa32a84a9f2
|9,0=>0x2cf1b386cd1b306cb1b286c91b206c71b186c51
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
|0=>0x6320000000c2400000018080000002050000000402000000058000000009f8000000128000000024200000004200000000838000000105000000020800000004080000000808000000058000000009000000000fc0000000120000000023000000004400000000840000000100000000019000000001000000000180000000028000000004000000000600000000080000000008000000000
|1=>0x426a000000808400000100c800000201500000040220000008020000001002800000200100000040000000004c00000000400800000072f0000000e5a0000001c9c000000391800000070d0000000e02000000181400000030080000005240000000a4600000014800000002140000000400000000071a0000000d240000001a0800000033f000000065e0000000cac000000191800000031d
|2=>0x10044e0000200814000040097800008010600001000140000200008000020397800004072b0000080c5e000010188c0000201118000040107000008020000001000a4000020003000002237f00000406fe0000080dbc0000101ac8000020000000002044000000400000000040000000004004000000567e000000a4040000011bf800000233f000000463a0000008c6400000110c8000002215
|3=>0x10806560002081cac000400b97800080162300010024440002001cbc0004002920000800428000100067e00020000800002200838000400327000080000e000100001800010100b80002000110000280e56000040040800008000100000e876f00001c0ede0000321dbc00006432280000c076f0000180e5e0000301c3400006038280000c0327000010075e0000200e9c0000401818000080301
|4=>0x10004063a0200000cfc0208103b5804102072f00801c0e5e0100380dbc020060397804002036f008000040a00800018ac00c0001c7801484022300281806560050204cac00a0003978014000622001210075e0024200cbc004020005800700172f000c00264a0012200ebc002020911800400172f0008002e4e000c005cbc001800397800300072700021406de0004280d98000840197800100072f
|5=>0x420400172f801010075e8100381cbc80ba0009390004803af10000040421100080dbc2000001208300000428041010075e0808001490100400b9582000c072b04001007560800200418100040081020008000a040000265e080000001808e800197810500172f0202000e5e04000008bc0400111bf808002035d
|_=>0
def pmB : Nat → Nat → Nat
|5,0=>0x1000200000607000009000800040000000000010600000d
|6,0=>0x904360400000e490000023748000d0100124b00000600070200000000000700000000090000000010010d00040100000400010f000004000400000b01091200000400003a000038070500000028004c2700000d370d3500002019
|7,0=>0xc38313b020900070061b12c138ba99e022d5a4274150b3f0d0395461409333cb3294302230a38625e2f010251165b30072f000611023c4d02060a0009a62b136d183e40602f822a00695725415309a270266e0d632d0b005f1b3271760b1a5c6409079f0a2e72554a7b0b17099739452696395d211d0d002309731c0313091f
|7,1=>0x17563da1071ea0
|8,0=>0x55446c899b9068795965752281b6b57ca5b2ad99b0784e7f598d50b4772491689ba4ab844787a3aea7246722ac4fb4548f948a9c447d9380ab34af59aa925c9a678e589da752598c835b666a85a8887e6f246b
|9,0=>0x98677a5923b786672324b8
|10,0=>0x23
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 8 (j % 128); fld (pmPalB (k / 32)) 39 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_190,9,runOps true dom_190 (0,roots_190) ops)] else [])++(if pm.testBit 1 then [(dom_175,8,runOps true dom_175 (0,roots_175) ops)] else [])++(if pm.testBit 2 then [(dom_155,7,runOps true dom_155 (0,roots_155) ops)] else [])++(if pm.testBit 3 then [(dom_187,8,runOps true dom_187 (0,roots_187) ops)] else [])++(if pm.testBit 4 then [(dom_150,5,runOps true dom_150 (0,roots_150) ops)] else [])++(if pm.testBit 5 then [(dom_189,8,runOps true dom_189 (0,roots_189) ops)] else [])++(if pm.testBit 6 then [(dzo_158_1,6,runOps true dzo_158_1 (0,roots_158) ops)] else [])++(if pm.testBit 7 then [(dzo_175_16,6,runOps true dzo_175_16 (0,roots_175) ops)] else [])++(if pm.testBit 8 then [(dom_159,8,runOps true dom_159 (0,roots_159) ops)] else [])++(if pm.testBit 9 then [(dom_183,9,runOps true dom_183 (0,roots_183) ops)] else [])++(if pm.testBit 10 then [(dzo_61_2,5,runOps true dzo_61_2 (0,roots_61) ops)] else [])++(if pm.testBit 11 then [(dom_181,6,runOps true dom_181 (0,roots_181) ops)] else [])++(if pm.testBit 12 then [(dzo_189_2,6,runOps true dzo_189_2 (0,roots_189) ops)] else [])++(if pm.testBit 13 then [(dzo_150_1,5,runOps true dzo_150_1 (0,roots_150) ops)] else [])++(if pm.testBit 14 then [(dom_154,5,runOps true dom_154 (0,roots_154) ops)] else [])++(if pm.testBit 15 then [(dom_158,6,runOps true dom_158 (0,roots_158) ops)] else [])++(if pm.testBit 16 then [(dom_139,4,runOps true dom_139 (0,roots_139) ops)] else [])++(if pm.testBit 17 then [(dzo_190_1,7,runOps true dzo_190_1 (0,roots_190) ops)] else [])++(if pm.testBit 18 then [(dom_63,6,runOps true dom_63 (0,roots_63) ops)] else [])++(if pm.testBit 19 then [(dzo_47_16,5,runOps true dzo_47_16 (0,roots_47) ops)] else [])++(if pm.testBit 20 then [(dom_174,6,runOps true dom_174 (0,roots_174) ops)] else [])++(if pm.testBit 21 then [(dom_167,6,runOps true dom_167 (0,roots_167) ops)] else [])++(if pm.testBit 22 then [(dom_143,5,runOps true dom_143 (0,roots_143) ops)] else [])++(if pm.testBit 23 then [(dom_173,6,runOps true dom_173 (0,roots_173) ops)] else [])++(if pm.testBit 24 then [(dzo_45_2,4,runOps true dzo_45_2 (0,roots_45) ops)] else [])++(if pm.testBit 25 then [(dom_157,5,runOps true dom_157 (0,roots_157) ops)] else [])++(if pm.testBit 26 then [(dzo_173_2,5,runOps true dzo_173_2 (0,roots_173) ops)] else [])++(if pm.testBit 27 then [(dom_171,5,runOps true dom_171 (0,roots_171) ops)] else [])++(if pm.testBit 28 then [(dzo_173_16,5,runOps true dzo_173_16 (0,roots_173) ops)] else [])++(if pm.testBit 29 then [(dom_153,4,runOps true dom_153 (0,roots_153) ops)] else [])++(if pm.testBit 30 then [(dzo_186_1,6,runOps true dzo_186_1 (0,roots_186) ops)] else [])++(if pm.testBit 31 then [(dom_182,8,runOps true dom_182 (0,roots_182) ops)] else [])++(if pm.testBit 32 then [(dom_185,5,runOps true dom_185 (0,roots_185) ops)] else [])++(if pm.testBit 33 then [(dom_45,4,runOps true dom_45 (0,roots_45) ops)] else [])++(if pm.testBit 34 then [(dzo_182_1,6,runOps true dzo_182_1 (0,roots_182) ops)] else [])++(if pm.testBit 35 then [(dom_165,5,runOps true dom_165 (0,roots_165) ops)] else [])++(if pm.testBit 36 then [(dom_141,4,runOps true dom_141 (0,roots_141) ops)] else [])++(if pm.testBit 37 then [(dom_186,6,runOps true dom_186 (0,roots_186) ops)] else [])++(if pm.testBit 38 then [(dzo_45_16,4,runOps true dzo_45_16 (0,roots_45) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_191 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_158_1_150 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_175_16_45 _ g hchk
    · exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_61_2_45 _ g hchk
    · exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_189_2_45 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_150_1_150 _ g hchk
    · exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · exact cpcs (by decide +kernel) lowS_139 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_190_1_150 _ g hchk
    · exact cpcs (by decide +kernel) lowS_63 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_47_16_45 _ g hchk
    · exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_45_2_45 _ g hchk
    · exact cpcs (by decide +kernel) lowS_157 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_173_2_45 _ g hchk
    · exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_173_16_45 _ g hchk
    · exact cpcs (by decide +kernel) lowS_153 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_186_1_146 _ g hchk
    · exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_182_1_150 _ g hchk
    · exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · exact cpcs (by decide +kernel) lowS_141 _ g hchk
    · exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_45_16_45 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_190 9 s (0, roots_190) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_191 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_190 h

def symsG : List (List (Nat × Nat)) := [[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_191 == dom_191) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_191 goalM v ys) : RunD true dom_191 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_191 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 6 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 6 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 24 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 24 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 91 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 91 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 136 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 136 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 83 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 83 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 11 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 11 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 10) : ∀ i < NN s, bar true dom_191 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
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
  scr true dom_191 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 6 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 10) (h : RunD true dom_191 goalM s xsM) : False := by
  have hmin : 6 ≤ s := by
    have hl := run_len h; change 7 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_191 roots_191 goal_191 11 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_191

theorem lowS_191 : Lower true dom_191 roots_191 goal_191 11 := S_191.noCircuit

theorem lowS_223 : Lower true dom_223 roots_223 goal_223 11 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 64, 68)] (by decide +kernel) (by decide +kernel) lowS_219

def dzo_230_8:=0x550000005500000055000000550000005500000055000000550000005500
def gzo_230_8:=0x550000005500000055000000550000005400000054000000500000000000
def gsh_230_8:=0x5500000055000000550000005500000054000000540000005000000000
theorem lowS_zo_230_8_102:Lower true dzo_230_8 roots_230 gzo_230_8 5:=lower_iso (d1:=dom_230) (roots1:=roots_230) (T1:=gsh_230_8) [(dom_230,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_230_8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x5500000055000000550000005500000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_102)
def dzo_102_8:=0x5500000055000000550000005500
def gzo_102_8:=0x5400000054000000500000000000
def gsh_102_8:=0x54000000540000005000000000
theorem lowS_zo_102_8_102:Lower true dzo_102_8 roots_102 gzo_102_8 4:=lower_iso (d1:=dom_102) (roots1:=roots_102) (T1:=gsh_102_8) [(dom_102,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_102_8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [] (by decide +kernel) (by decide +kernel) lowS_102)
def dzo_237_2:=0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc
def gzo_237_2:=0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000c8c800008800
def gsh_237_2:=0x333300003333000033330000333300003333000033330000323200002200
theorem lowS_zo_237_2_45:Lower true dzo_237_2 roots_237 gzo_237_2 6:=lower_iso (d1:=dom_237) (roots1:=roots_237) (T1:=gsh_237_2) [(dom_237,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_237_2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x333300003333000000000000000000003333000033330000000000000000,0,64),(0x333300003333000033330000333300000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_45)
def dzo_231_8:=0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00
def gzo_231_8:=0xff000000ff000000ff000000ff000000fe000000fe000000fa000000aa00
def gsh_231_8:=0xff000000ff000000ff000000ff000000fe000000fe000000fa000000aa
theorem lowS_zo_231_8_102:Lower true dzo_231_8 roots_231 gzo_231_8 6:=lower_iso (d1:=dom_231) (roots1:=roots_231) (T1:=gsh_231_8) [(dom_231,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_231_8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xaa000000aa000000aa000000aa000000aa000000aa000000aa000000aa,0,1),(0xff000000ff000000ff000000ff00000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_102)
namespace S_239
def pairsG : List (Nat × Nat) := [(1,9), (1,33), (1,65), (2,66), (2,130), (3,11), (3,35), (3,67), (3,131), (4,36), (4,68), (4,132), (5,13), (5,37), (5,69), (5,133), (6,38), (6,70), (6,134), (7,15), (7,39), (7,71), (7,135), (8,9), (8,136), (10,11), (10,74), (10,138), (12,13), (12,44), (12,76), (12,140), (14,15), (14,46), (14,78), (14,142), (32,33), (32,36), (32,160), (34,35), (34,38), (34,98), (34,162), (40,41), (40,44), (40,168), (42,43), (42,46), (42,106), (42,170), (64,65), (64,66), (64,68), (72,73), (72,74), (72,76), (72,200), (96,97), (96,98), (96,100), (96,224), (104,105), (104,106), (104,108), (104,232), (128,130), (128,132), (128,136), (128,160), (129,131), (129,133), (129,137), (129,161), (129,193), (192,193), (192,194), (192,196), (192,200), (192,224)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x7fffffffffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_239.map (· &&& dom_239)
def goalM : Nat := goal_239 &&& dom_239
def NN : Nat → Nat
|5=>17
|6=>130
|7=>197
|8=>73
|9=>8
|10=>1
|_=>0
def HT : Nat → Nat → Nat
|5,0=>0xac450a78bc79ba767851603105e0c85df504ead44a2993a79a314ff292e81ef131ed2f166f71570301302
|6,0=>0xe6ae1e6727dee53d6cccd51cecf535ccd4dc3e4fbdb82bc4bdb623aaa73ea9edba6b37a07d89eb819e9cf9d9bc9d2259cf749ba7799b8695ee89439c92e4f8fc9e8fb9d8f8dd8f52d8bbc2829ca81be2810af7c7537b4a278e9076f5372d2e6ef896e1ff6b6876b4e768280653f56035a5f0b95f0155ddff5d4a25bb775a4d45a1b95554453a41537a35364352dd04f9c44d9934c9ae4bd3b47afb4705345de943b2843382411583e5393d4823ca583abc63a6cf394a038d55370453700936b4130912305ba2f69f2ef2f2e1072d6be2b9c02b68c2a963294bd289c7270e826fae26b93266d623d402239d2211a203fd202911eda71eb0b1d4481cede1cc2a1cae01c26a1c1241b9ec1791f1768f1515f148ec147aa145db143a3116440f1f80d1e10d1280ccfa0b6200b4370b0f309d660870007c6204f7303fc0024e0023a8
|6,1=>0xf0fa5e896e
|7,0=>0x6fa5b6e15b6b8b56a49c6a20c673f26715866f206439f60804607f66037a5f0155e4915cfd65b9135b33d5878557f8556e9a558de5533853daa53c2e505614fe174f5f04f5734e4594d0344cd4f4ca264acaa49b3248bdc4860048543474f1467204596644dd744d9c44d7b43f3042429415ab401393f9b73ed623ec083d50f3c75d3a0fc3991439784392a43904038cbf389d737f43320d330f423015f2fb792f0f12ef9f2d5802d1d22b8eb2a506296d728e62289c7283d427e5f26fae2695a241c922ce1224e92223521986203fd1d6151d1f81c8a21b48f1a7d719e2618128169cc16876167f9159621562f155c9154d21546b1508713c4413a4512e2711f590f3ad0d9450d9310d6d20d6bb0c75e0c65d0b9d2099f9099f30809407d240787e07555074820601405d8f05a6604d1f04357041da02dc9021da011ba01008
|7,1=>0xef4a2e6a65e4ed9df95cde03bdd2abd91fcd4faacf1e4ca1eec3808c3721befb9be88ebe064bc00fb9e8eb7594b623ab60e3b5504b40ecaf8c9af894af7a5aeaa2ad67eaba9daba77aaa77a9121a6f9fa6cce9ecc69e8b89b35697bff972b1966a595eff94d979406d9386e8f5d58e5f18d74389b86877238576f833ee82b56829f081a4380fbc7fb117b4ea7a19d79b2a795da78eff78b1c7593374f1a74c9773c607365070ddb702406fac2
|8,0=>0xe109fdcb09d6524d1d19cc537c6f5ac6256bb000ac154a51c2a2daea29949d8279bd38956d68aac08998286404859b781b5d806507e9177dac87c2487a9dc6db956d1f1679bb59b765594651ec4513684e7004d98f48c974847446ecb432ae3e65b3d68d3d0c73c2d63b7c33745b32a72327153254d30fa32e3902da2429bd428dac224e921a911b07815cf11546b145f212f9311b361057a0f68d0d36d0cd210b4c2099f308b2f083660815f0775803ef302ab0001fb
|9,0=>0xe35c1c8747c43f4855ef5a2d544a4b3b16b19ad7
|10,0=>0x52192
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xffff0000ffff0000fcfc0000fcfc0000ffff0000ffff0000000000000000ffff0000ffff0000f0f00000f0f00000aaaa0000aaaa0000a0a00000a0a00000000000ff00000000000000ff0000ffff0000ff000000ffff0000ff00ffff0000fcfc0000ffff0000fcfc0000ffff000000000000ffff00000000fcfc0000fcfc0000fcfc0000fcfc0000fcfc0000fcfc0000fcfc0000fcfcffff0000ffff0000ffff0000ffff0000fafa0000fafa0000fafa0000fafaffff0000ffff0000ffff000000000000aaaa0000aaaa0000aaaa000000000000000000000000ffff0000ffff00000000000000000000ffff00000000ffff0000ffaa0000ffff0000ffaa0000aaaa0000aaaa0000aaaa0000aaaaffff0000aaaa0000ffff0000aaaa0000ffff0000aaaa0000ffff0000aaaaffff0000ffcc0000ffff0000ffcc0000cccc0000cccc0000cccc0000cccc0000000000ff00000000000000000000ffff0000ffff0000ffff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff00000000ffff0000ff000000ffff0000ff000000aaaa0000aa000000aaaa0000aa000000000000000000fafa0000fafa00000000000000000000fafa0000fafafcfc0000fcfc0000fcfc0000fcfc0000fcfc0000fcfc0000000000000000ffff0000fff00000ffff0000fff00000f0f00000f0f00000f0f00000f0f0ffff000000000000ffff000000000000ffff000000000000ffff00000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00fafa0000fafa0000fafa0000fafa0000fafa0000fafa0000fafa0000fafafcfc0000fcfc0000fcfc0000fcfc0000fcfc0000fcfc0000a8a80000a8a8ffff0000ffff00000000000000000000ffff0000ffff0000000000000000ffff0000ffff0000ffff0000ffff00000000000000000000000000000000ffff0000ff000000ffff0000ff000000ffff0000ff000000ffff0000ff00aaaa0000aaaa0000aaaa000000000000ffff0000ffff0000ffff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff00000000000000000000000000000000ffff0000ffff00000000000000000000ffff0000ff00ffff0000ffff0000ffff000000000000ffff0000ffff0000ffff00000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000ccccaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaaffff0000ff000000ffff0000ff0000000000000000000000000000000000
|0,1=>0x555500005555000055550000000000005555000055550000555500000000ffff0000ffff0000ffff0000ffff000055550000555500005555000000000000000000aa00000000000000aa0000aaaa0000aaaa0000aaaa0000aaaafcfc0000fcfc0000fcfc0000fcfc00000000000000000000000000000000fffc0000fffc0000fffc0000fffc0000ff000000ff000000ff000000ff0000ff000000ff000000ff000000ff0000000000000000000000ff000000aa33330000333300003333000033330000333300003333000022220000222200ff000000ff000000ff000000ff000000ff000000ff000000aa000000aaffff0000ffff0000ffff000055550000ffff0000ffff0000ffff00000000ffff0000ffff00005555000055550000ffff0000ffff0000000000000000ff540000ff540000ff540000ff540000ff540000ff540000ff540000ff5400ff000000ff000000ff000000ff000000aa000000aa000000aa000000aa0f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000aaaa0000aaaaffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000aaaafefe0000fefe0000fefe0000fefe0000fafa0000fafa0000fafa0000fafafefe0000fefe0000fefe0000fefe0000aaaa0000aaaa0000aaaa0000aaaa00ff000000ff000000ff000000ff000000fa000000fa000000fa000000fa00000000ffff000000000000ffff000000000000fafa000000000000fafaffff0000ffff00000000000000000000ffff0000ffff0000ffff0000aaaaafaf0000afaf0000afaf0000afaf0000aeae0000aeae0000aeae0000aeae000000000000000055550000555500000000000000000000505000005050050500000505000005050000050500000404000004040000040400000404ffff0000ffff0000ffff0000ff000000ffff0000ffff0000ffff000000000000000000000000ffff0000ffff00000000000000000000fafa0000fafaffff0000ffff0000f0f00000f0f00000ffff0000ffff0000f0f00000f0f0fafa0000fafa0000fafa0000fafa0000fafa0000fafa0000000000000000ffff000000ff0000ffff000000ff0000ffff000000ff0000ffff000000aa030300000303000003030000030300000303000003030000020200000202ffff0000ffff000005050000050500000000000000000000000000000000ffff0000ffff0000ffff0000ffff0000f0f00000f0f00000f0f00000f0f0ffff0000ffff0000ffff0000ffff0000aaaa0000aaaa0000aaaa0000aaaa
|0,2=>0xffff0000ffff0000ffff0000ffff0000ffff0000aaaa0000ffff0000aaaaff000000ff000000ff000000ff000000ff550000aa000000ff550000aa00ffff0000aaaa0000ffff0000aaaa0000ffff0000aaaa0000000000000000ffff0000ffff00005555000055550000ffff0000ffff000055550000000000aa000000ff000000aa000000ff000000aa000000aa000000aa000000aa00000000000000000000000000000000fafa0000fafa0000fafa0000fafafcfc0000fcfc0000fcfc0000fcfc00000404000004040000040400000404aaaa0000aaaa0000ffff0000ffff0000aaaa0000aaaa0000aaaa0000aaaaffff0000ffff0000ffff0000ffff0000fcfc0000fcfc0000fcfc0000fcfc333300003333000033330000333300003333000033330000333300000000fafa0000fafa0000ffff0000ffff0000fafa0000fafa0000fafa0000fafafcfc0000fcfc0000fcfc0000fcfc0000a8a80000a8a80000a8a80000a8a803030000030300000303000003030000030300000303000003030000000000000000000000000000000000000000fcfc0000fcfc0000fcfc0000fcfc555500005555000055550000555500005050000050500000505000005050ffff0000ffff0000f0f00000f0f00000000000000000000000000000000000000000000000000000000000000000ffff0000ffff0000ffff0000aaaa000000000000000000000000000000000000000000000000ffff0000aaaa0000000000ff00000000000000ff00000000000000000000000000000000aaaa0000aaaa0000afaf0000afaf0000aaaa0000aaaa0000aaaa0000aaaaaaaa0000aaaa0000aaaa0000ffff0000aaaa0000aaaa0000aaaa0000aaaa00ab000000ab000000ab000000ab000000aa000000aa000000aa000000aa33330000333300003333000033330000333300003333000032320000323202020000020200000202000002020000fafa0000fafa0000fafa0000fafa000000000000000000000000ffff00000000000000000000000000000000ffff0000ffff000000000000ffff0000ffff0000ffff00000000000000000000000000000000ffff0000aaaa00000000000000000000ffff0000aaaa0000000000000000ffff0000ffaa00000000000000000000ffff0000ffaa00000000000000000000000000000000ffff0000ff000000ffff0000ff00ffff0000ffaa0000ffff0000ffaa0000ffff0000ffaa0000ffff0000ffaa0000000000000000ffff0000ff0000000000000000000000ffff0000ff00333300003333000000000000333300003333000033330000000000002222
|0,3=>0xffff0000ff000000ffff0000ff000000ffff0000ff000000aaaa0000aa00fafa0000fafa00000000000000000000ffff0000ffff0000000000000000ffff0000ffff0000aaaa0000aaaa0000ffff0000ffff0000aaaa0000aaaa000000000000000054540000545400000000000000000000545400005454ffff0000ffff0000ffff0000ff000000ffff0000ffff00000000000000000f0f00000f0f00000f0f00000f0f00000505000005050000050500000000ffff0000ffff0000ffff0000ffff00000000000000000000ffff0000aaaa00000000ffff000000000000ffff000000000000aaaa000000000000aaaa5555000055550000555500005555000055550000555500005050000050500f0f00000f0f00000f0f00000f0f0000040400000404000004040000040403030000030300000303000003030000000000000000000000000000000003030000030300000303000003030000fcfc0000fcfc0000fcfc0000fcfcff000000ff000000ff000000ff000000ff550000ff550000ff550000ff00ffff000055550000ffff000055550000ffff000055550000ffff000000000000000000000000ffff0000ffff00000000000000000000aaaa0000aaaaaaaa0000aaaa0000afaf0000afaf0000000000000000000000000000000000000000f0ff000000000000f0ff000000000000f0fa000000000000f0faffff0000ffff00000505000005050000ffff0000ffff0000000000000000ffff0000ffff00000000000000ff0000ffff0000ffff0000000000000000ffaa0000ffaa0000ffaa0000ff000000ffff0000ffff0000ffff0000ff00ffff0000ffff00005454000054540000ffff0000ffff0000545400005454ffff0000ffff00005555000055550000ffff0000ffff00005050000050500000000000000000fcfc0000fcfc00000000000000000000fcfc0000fcfc00bb000000bb000000bb000000bb000000bb000000bb000000aa000000aa333300003333000033330000333300003333000033330000000000000000000000000000000000000000000000000000000000000000fafa0000fafa545400005454000054540000545400005454000054540000545400005454ffff0000ffff0000ffff0000ffff00005454000054540000545400005454555500005555000055550000555500000000000000000000000000000000555500005555000055550000555500005454000054540000545400005454ff000000ff000000ff540000ff540000ff000000ff000000ff540000ff54aaaa0000aaaa0000aaaa0000aaaa0000ffff0000ffff0000ffff0000aaaa
|0,4=>0x55550000555500005555000055550000555500005555000055550000000000000000000000000000000000000000ffff0000ffff0000f0f00000f0f0aaaa0000aaaa0000aaaa0000aaaa0000ffff0000ffff0000fafa0000fafaaaaa0000aaaa0000ffff0000ffff0000aaaa0000aaaa0000ffff0000aaaaaaaa0000aaaa0000aaaa000000000000aaaa0000aaaa0000aaaa0000aaaa000000000000000055550000555500000000000000000000000000000000ffff0000ffff0000ffff0000ffff0000ffff0000ff000000ffff0000ff00f3f30000f3f30000f3f30000f3f30000f3f30000f3f30000f0f00000f0f0555500005555000055550000555500005555000055550000000000000000aaaa0000aaaa00000000000000000000ffff0000ffff0000000000000000ffff0000ffff0000ffff0000ffff00000000000000000000ffff0000ff00fefe0000fefe0000fefe0000fefe0000fefe0000fefe0000fefe0000fefefefe0000fefe00000000000000000000fefe0000fefe0000000000000000555500005500000055550000550000005555000055000000555500005500ffff0000aaaa0000ffff0000ffff0000ffff0000aaaa0000ffff0000aaaa0000000000000000ffff0000ffff00000000000000000000000000000000f0f00000f0f00000ffff0000ffff0000f0f00000f0f00000f0f00000f0f0ffff0000ffff0000fafa0000fafa0000ffff0000ffff0000fafa0000fafa00000000ffff000000000000ffff00000000000000000000000000000000ffff000000ff0000ffff000000ff0000ffff000000000000ffff00000000ffff0000ffff0000ffff000000ff0000ffff0000ffff0000ffff00000000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000ffff0000ffccffff0000ffff0000ffff0000ffff0000ffff000000000000ffff00000000aaaa0000aaaa0000a0a00000a0a00000ffff0000ffff0000f0f00000f0f0000000000000000000000000000000000000000000000000ffff0000ff0000000000ffff000000000000ffff000000000000ffff000000000000fafa3333000033330000333300003333000011110000111100001111000000003333000033330000333300003333000033330000333300003333000022220000000000ff00000000000000ff00000000000000aa00000000000000aa333300003333000003030000030300003333000033330000020200000202cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000ffff0000eeeef0ff0000f0ff0000f0ff0000f0ff0000f0fa0000f0fa0000f0fa0000f0fa
|0,5=>0x5555000055550000505000005050000055550000555500005050000050500000000000000000fefe0000fefe00000000000000000000fefe0000fefeffff0000ffff0000fafa0000fafa0000aaaa0000aaaa0000aaaa0000aaaa333300003333000033330000333300003333000033330000303000003030ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000f0f00000f0f000000000000000000000000000000000ffff0000aaaa0000ffff0000aaaaaaaa0000ffff0000aaaa0000ffff0000aaaa0000ffff0000aaaa0000aaaa0000000000000000ffff0000ffff00000000000000000000f0f00000f0f0f5f50000f5f50000f5f50000f5f50000f0f00000f0f00000f0f00000f0f000ff000000ff000000ff000000ff000000ff000000aa000000ff000000aaf3f30000f3f30000f3f30000f3f30000f0f00000f0f00000f0f00000f0f000000000000000000000000000000000555500005555000050500000505000000000000000000000000000000000ffff0000ffff0000fafa0000fafaffff0000aaaa00000000000000000000ffff0000aaaa0000ffff0000aaaa000000000000000005050000050500000000000000000000000000000000ffff000033330000ffff000033330000ffff000033330000ffff00000000ffff000055550000ffff000055550000ffff000000000000ffff0000000000000000000000000000000000000000ffff0000ffff0000ffff000000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000a0a00000a0a0f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000000000000000afaf0000afaf0000afaf0000afaf0000afaf0000afaf0000aaaa0000aaaa00000000ffff000000000000ffff000000000000ffff0000000000000000050500000505000005050000050500000000000000000000000000000000ffff0000aaaa00000000000000000000ffff0000ffff000000000000000003030000030300000000000000000000ffff0000ffff000000000000000000000000000000000f0f00000f0f00000000000000000000000000000000cccc0000cccc0000ffff0000ffcc0000cccc0000cccc0000ffff0000ffcc0000000000000000000000000000000055550000555500005555000000000000000000000000ffff0000ffff00000000000000000000ffff0000aaaa000000005555000000000000555500000000000000000000000000000000ffff0000ffff0000fafa0000fafa00000000000000000000000000000000000000005555000000000000555500000000000055550000000000000000
|0,6=>0xffff0000ffff0000ffff0000ff000000ffff0000ffff0000ffff0000ff000f0f00000f0f00000f0f00000f0f00000a0a00000a0a00000a0a00000a0aaaaa0000ffff0000aaaa0000ffff0000aaaa0000aaaa0000aaaa0000aaaaffff000000000000ffff0000ffff0000ffff000000000000ffff00000000ffff0000ffff0000ffff0000aaaa0000ffff0000ffff0000ffff0000aaaa000000000000000055550000555500000000000000000000555500000000ffff0000ffff0000ffff0000ffff00005555000055550000505000005050f5f50000f5f50000f5f50000f5f50000f5f50000f5f50000f0f00000f0f0bbbb0000bbbb0000bbbb0000bbbb0000bbbb0000bbbb0000aaaa0000aaaa555500005555000054540000545400005555000055550000545400005454ffff0000aaaa0000ffff0000aaaa00000000000000000000000000000000f0f00000f0f00000ffff0000ffff0000f0f00000f0f00000fafa0000fafaffff0000ffff0000fcfc0000fcfc0000ffff0000ffff0000fcfc0000fcfc0f0f00000f0f00000f0f00000f0f00000c0c00000c0c00000c0c00000c0c000000000000000000000000ffff0000000000000000000000000000aaaaaaaa0000aaaa0000ffff0000ffaa0000aaaa0000aaaa0000ffff0000ffaaffff000000ff0000ffff000000ff0000ffff000000aa0000ffff000000aaffff0000ffff00000000000055550000ffff0000ffff0000000000000000afaf0000afaf0000afaf0000afaf0000aaaa0000aaaa0000aaaa0000aaaa00af000000af000000af000000af000000aa000000aa000000aa000000aaffff0000ffff0000fafa0000fafa0000ffff0000ffff0000000000000000fafa0000fafa0000fafa0000fafa00000000000000000000000000000000aaaa0000aaaa00000000000000000000aaaa0000aaaa0000aaaa0000aaaaffff0000ff000000ffff0000ff000000ffff0000ff000000000000000000ffff0000ffff0000afaf0000afaf0000ffff0000ffff0000aaaa0000aaaaffff000000000000ffff000055550000ffff000000000000ffff000000000000000000000000000000000000000054540000545400005454000054540000000000ff00000000000000000000ffff0000ffff0000000000000000ffff0000ffff00000f0f00000f0f0000ffff0000ffff00000000000000000f0f00000f0f00000f0f00000f0f00000000000000000000000000000000333300003333000003030000030300003333000033330000000000000000cccc0000cccc0000cccc0000cccc0000fefe0000fefe0000fefe0000fefe
|0,7=>0xffff0000ffff0000ffff0000000000000000000000000000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0xe030217060a0e0d0301230a090e0d03020106220e0d21010a100e0d0c200a100e0d1b1a011f0e0d0c021e061d040302010a1c0d1b1a010a160d0302190618030201120a08040302170616030212060a08040315010608140302010613030201120a0e0d1101100908040f0201060e0d0c0b0a09080703020106050403020100
|1=>0x908040302320109083703020136090e351b26010a090e1b2601340a090e0d0302011e0608040201330a0908310302010a090e0d1b110106090e0d1b302f0a090302012e2d0a09082c0302010a090e0d1b2b010a090e0d1b012a0a090e0d1b01290a0908280302010a090e0d1b27010a090e0d2602012509240e0302010a0908
|2=>0x4c0a09080e0301390a090e0d03024b0a090e1b03014a0a090e0d0301490a090e0d1b48010a090804030201460908450302010609440804030201090e1b1a01340a0908430403020106424104030201090e0d0301400a09080302013e0a09080403023d0a090e0d1b1a010a3c0e3b1b0c010a090e0302013a0a090e030139380a
|3=>0x2015c0a090813030220010a040302015b0a090e0d1b01590a090e0d1b0c580a090e0d570c010a3c08040301560a090e0d1b55010a09030201342d0a090e0d1b0c540a090e1b21012e0a090e0d0133530a090e0d1b5201510a0e0d0c02010650084f0302010a09084e0302010a090d1b1a012d0a094104030201094d0e0d0302
|4=>0x90e0d1b0151060a0e0d1b016a0a090e0d1b691101090e0301680a67090e351b21010a090e1b2101340a090e0d1b66010a090e0d1b0c640a0908040f02010a09080403020106630e0d0301620a3c0e0d0320010a100e611b03010a0908600302010a0908070302010a090e5e0302010a09160302120a09040d0302015d090803
|5=>0x3010a08040302170a090e0d03020119060e730302010a0908720302010a090e0d1b0c710a090e3b1b0320010a0e0d0302200a70030201346f0a0908040301066709070e0d030201060e0d1b0c016e0908040302016d090e030139340a090e0d0201330a096c0e0302010a090d1b21012d0a090816030220060a0e0d1b0c6b0a
|6=>0xe0d0301840a090e0d1b0c20060a04030201830a090e0d0301820a09810e0d03010a090e1b8001340a090e0302017f0a090e0d1b0c017e090e0d1b521a010a0e0d1b0c7c0a091c0d1b21010a43040302010a4d08040302017b090e0d02017a0a0908790302010a090d03023f780a090e0d1b01770a090e0d1b01760a090e0d74
|7=>0x630e0d260301066709040d030220010a8d088b0302010a090e0301340a67098a080e03010a0908130301560a0904030201120a0908890302170a080e0f0201060a0e0d88030201060887040302010908130302010a630e0d0c260220060d030201860a090e0d1b1a010a090e0d0301850a090804030201060008050403020109
|8=>0xe0302017b0908160302920a09910e0d0302580a09130e0d0302010a090e0d2103010a67090e0d1b03580a09890e03022001340a0e0d1b0c010a09900e26030201340a090e0d5703010a3c0e03023201340a090e0d0c26020106090e0d1b8f010a090e0d1b8e010a090e0d110302010609085f160302010a09080e030201060a
|9=>0x2016d0a099c0e0d0302010a09040e0d03022001060e0d1b21010a900e0d03029b0a090e0d0302580a099908040302010a090e0d9803010a6709040e0d03020197090e1a030201340a09080e03020196090e0d26030201360908950e0302010a090e0d1b0301710a090e0d1b520320010a0e0d1b03019309430e0302010a4d08
|10=>0xe0d0201330a090e0d030201a40a09a30e0d0302010a095f0e0d0302010a090e210302012e0a09080e0301060a67090e0d1b0c7d0a09040e0d03029b0a090e0d0302010a09a10e0d0302010aa0090e030201830a090e0d1b8e0c010a090e0d0302019f0a090e0d9d0302010a09130e0d0302010a63130e0d0201330a09080e03
|11=>0x201060a0908890302010a000e0d030201a8090e0d0302010a0922080e030201360a09040e0d03024b0a090e0d1b03017c0a090e0d1b0301a7090e03020134060a090e0d0c0302580a090e0d03022001460a0e0d550302010a090e0d1b690c010a090e0d03024c0a09a5080e03010a090813030201060a090e0d03024b0a0989
|12=>0xaf0d0302010a090e0d0302011e0a090e0d1b0c010a093c16040d03020106090e0d1b1a21010a09080403020106090e0d033201390a09088903027d010a0908ae0302010a090e0d030201ad0a090e0d1b032f010a090e0d1b032001060a130e0d0301560a090e0d0302ab010a090e0d030220010aaa0e0d030201060aa9088903
|13=>0x8e26010a09890e030201b60a090e0d1b01510a09ae0d0302010a8d0e0d03020151060a0843040302010a090889030220010a0e0d1bb5010a090e0d030201b40a090e0db30302010a090e0d9803010a09080e0302580a09910e0d0302010a090e21030201340a09b20e0d0302010a090e0d0302010a09b1b00e0d03010a670916
|14=>0x301bc0a090e0d1bbb010a09080e030201060a000e0d0201330a0908ba0302010a0908050e0302010a090e030201120a090e0d0c02010a09500e0d2603022001065f0e030201b60a090e0d0302b9010a090e0d1bb8010a090e0d1bb7010a091c0d1b03010a090e0db7030201060a0e0d1b0c010a09a908160302200a090e0d1b
|15=>0xc50a09040e0d0302014609450e0d03020106090e0d2603024c0a090e0d032001060a67080e030201c4090e0d03010ac1090e0dc003010a090e0d0302013e0a090e0d1b01bf0a090e0dbe1b030109040e0d0302320109370e0d03020136090e0d0302bd010a09040e0d0201330a09310e0d0302010a09160e0d030201a8090e0d
|16=>0x130e0d030220010a040e0d0301560a090e0d030201cb0a090e0d0302200aca080e0302c90a09080e0302010ac8090e0d0302c7010a090e0d0301560a09084104030201090e0dbb03010a67090e0d0302016e0a090841890302010a090e0d0c02010aac09c60e0d0302010a090e0d0cb702010a090e030201380a090e0d1b0301
|17=>0xa09750e0d26030201c3090e0d030201190a090843890302010a0e0d1b2601650a09cf0e030220010a09040e0d03020106630e0d1b03011f090e0d030201ce0a09085f890302010a09600e0d0302010a09070e0d0302010a090e0d0c03010a67090e030201cc0a090e0d1b2620010a090e0d0302015c0a090e0d1b0332010a09
|18=>0x813040302010a090e0d0c02010a09a6040e0d03010667090e0d0302200ad5040d03027d01098d0e0dd40302010a090e0d1b1a010a090e0d0302010a09700e0dd31b0c010a090e0d1b01d20a090e0d030201d10a090d030220012d0a09d0080e0302010a090e1b0301340a09080302013f0a090e0d260301bc0a090e0d1b0c01
|19=>0x9008040302010a090e0d0302010a09d5890e0d030220010a090e0d0302013f0a090e0d030201da0a090e0d1b0c01060a09080e0315010a09410e0302010a094d0e0d032001390a090e0d030201d90a090e0dd80302010a0942410e0302010a09160e0d0302200a900e0d0c0201c30a090e0d03d7010a67090e0d1b0301d60a09
|20=>0x2010a09470e0d030201710a09080e0302010a09900e0d0302580a090e0d0c02010a09c20e0d0c03027d0a0913040e0d0302010a090e0d1b03010a093c0e0d260302010a09630e0d8e0c0302010a090e0d03023201060a095f0e0d030220010a09130e0d0302010a0916040d0302010a09db0e0d0302010a090e0d210302010a
|21=>0x10a090e180d0302010a09450e0d0302010a09080e0302010a094ddc0e0d0302010a09db160e0d0302010a0908410e0302010a0908160302010a0942080e0302010a090e0d1a210302010a090e0d571b03010a090e0d030201780a090e0d1b0320010a09040e0d0302010a0947080e030201920a095f0e0d0302010a090e0d03
|22=>0xd030220010a8d0e0d9e0302010a09130e0d030201060a090e0d030201de0a09080e030220010a090e0d030220010a900e0d03027d010a09c25f160e0d0302010a090e0d2103027d010a090e0d0302c90a090e0d0302010a09a20e0d0302dd010a090e0d0302cd010a090e0d03b802010a090e0d03022001060a040e0d030220
|23=>0x10a09e00e0d1b037d010a090e0d03022001060a090e03022001340a09df080e0302010a09160e0d0302200a09890e0d030220010a0e0d030232010a09af0e0d0302010a09890e0d030201060a090e0d1b5203010a090e0d26030220010a090e0d0c0302200a09160e0d0302010a09a20e0d5a0302010a090e0d03010a67090e
|24=>0xe0d0302010a090e0d0302010a09c20e0d03027d010a090e0d0302010a0963160e0d0302010a09040e0d0302010a090e0d1b03010a090e0d030220010a09890e0d0302010a090e0d030258010a090e0dbb210302010a090e0d1b03010a09900e0d0302010a099a040e0d0302010a096308890302010a090e0d0302
|_=>0
def stOffB : Nat → Nat → Nat
|5,0=>0x60605a6054604e60486042603c60366030602a6024601e60186012600c600660006
|6,0=>0x21d7216720f7209620271fb71f471ed71e671df71d871d171ca71c371bc71b571ae71a771a071997192718b7184717d7176716f71687161715a7153714c7145713e7137713071297122711b7114710d710670ff70f870f170ea70e370dc70d570ce70c770c070b970b270ab70a4709d7096708f70887081707a7073706c70666
|6,1=>0x3da73d373cc73c663bf73b873b173aa73a3739c7395738e7387738073797372736b7364735d7356734f73487341733a7334632d7326731f73187311730a730372fd62f672ef72e872e172da72d372cc72c572be72b772b072a972a2729b7294728d7286727f72787271726a7263725c7255724e7247724072397232722b72247
|6,2=>0x3e873e17
|7,0=>0x5d585cd85c675be85b685ae85a6859e8597759075888581757985718569856185598551854a7542853a8532852b7523851b8513850b850384fb84f384eb84e474dd74d674ce84c684be84b684af74a7849f8497848f84887481747a7473746b8463845b8454744c8444843c8435742d8425841e7417740f840783ff83f783ef8
|7,1=>0x7c087b977b277aa87a2879a8792878a8782877b7774776c8765775e7756874f7747873f8737872f87287721771a7712870a870376fb86f386ec76e576dd86d586ce76c776bf86b786b076a976a18699869186898681867986718669866186598652764a8642863b7633862b8623861b8613860b860385fb85f475ed75e585dd8
|7,2=>0x9b089a889a08998899089888980897889708968896179598951894a7942893a8933792b8923891b8914790d790588fd88f588ed88e678de88d688ce88c778bf88b788af88a7889f88987890888888808878887088688861785a7852884a8843783c7834882c8824881c8814880c880577fd87f587ed87e587dd87d677cf77c87
|7,3=>0x9d789cf89c879c089b88
|8,0=>0xbe38bdb8bd38bcb8bc38bbb8bb29baa8ba19b998b909b888b817b798b718b689b608b588b508b479b3e9b359b2e7b268b1e8b168b0e8b068afd9af58aed8ae58add8ad49acc8ac57abd8ab49aac8aa48a9c8a939a8b8a838a7b8a738a6b8a647a5c8a548a4b9a438a3a9a319a289a1f9a178a0f8a0789ff89f879f089e799df8
|8,1=>0xc2d8c249c1c8c148c0b9c047bfc8bf48beb9
|9,0=>0xc6c8c648c5c8c548c4c8c457c3d8c358
|10,0=>0xc747
|_,_=>0
def dictMask : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def wireSAt (i : Nat) : Nat := if i < 225 then (dictB (i / 512) (i / 32 % 16) >>> (240 * (i % 32))) &&& dictMask else 0
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
|0=>0x30a568250c09c34820109420c8060142825030146df7010a40c090309438f11b0900c094509549d51b09c6c260302438350e0a428250e0a42935080983835650940c091b0600c090a0957cd30e20404250e01420800e0d404251b5ac30270302484050309438350a47410260e0a4348201094fc250401c38290601438350a09438c90601428251b0600c25030242825
|1=>0x809038350e01420070e0d406410a098111d0409838290206828250302406410a09834820109438250a0980c09030143482010946c241b0940c090d2088029010940c290a0940c09039042826037d4042903024302b0301428251609438050109838350206828250e09804258c0a420260213a24290820038350109404010e09420240e0d438290806c38350a0942825
|2=>0x1609838050d1a884050206838350a0940c090a0140c050147c10260e3483482010940c090301678052609c4c0f890a438250a4d420260e0d438290a0940c250302428260147c10260e0a406697d09828050809438350206828250601c28250d20804250e0d4298f01098298d010990425080ac383503024802b010946c270302650281b0140c090809c20260e0d42801
|3=>0x200a40425013c46c24030242825010944c0b890a43825ac0140c1a0a094381a0a09430260301438350a09438250e09420240e0d42a8b1609838050a63404260147410261b7dc04290302428f31b0900c090a09434820109406410a0982a350e0980c051b0ac0c0901a649826030a50409080ac38350e06438350a094051d0409838290313a24290420c3829010945a89
|4=>0x109838050e0d40425030240c295f0de24050302484070309438260409c38292101c0c250809c38350e0a438250e0d40425037546c26030249883010940c2903674081a0a09406410e0d428260d20804251690c28260206828250ea2458260e0146c24030240c050e01438290a0940c09210140c250e0d438290a09408ca200a404250e0d438250409c38350e0a40cca
|5=>0xac240c265a024302703014fc250401c3829030249807030a6502b1b0140c090601438290a094298d010984c0f0409625f5010a438250aa2c5826bb02c9825030a40c190302428250809038351303e24290e09438351609c3805990ac2025082003835010949824030a40c290a09458250e016a8050e068282503024842b030940c090363404260e3c46c24030240d8d
|6=>0xe096b8050409c118f0e0a404260206828250dcd80709030980c29030240425200a40c090109438190a0944c0b0409430240301404250e0d406430a09820180a0970c050ac240c261302e24290e094202b0e0d438290e094202b0e0d40c1a0a0940ea50c0980c050d32818050a0946c830302404250a47410260e0a4069926098081a0a09404250a00c20240e0d40b0e
|7=>0xac240c2601674081a0a0974c071b0a40c090409438350e0a49826030a4081a0e0a428250109458240e0143826030248405030946c29030240c055703c6c2503024683b03204042541014202b0d2080c090109410070e0d43829bb02c98251b0980c090aa649826030a410800e0a404250e09420270e0d46c07030240c290e34434820109428f11b0900c090e0d62405
|8=>0x1b0940c090e20804250302404250409838290801c3835160943805040983829200ac04250e0d42826019042826030140c260a0140c050409438291b0900c09010980c290c0a40c050601428250e2040425890a438250e0a43805160a438050309428260e0d438291609038050109438250401c3829030240c050a094080108090383502328802901096fc252601c0c29
|9=>0xa09438251b09c0c09010940c290301404251609838050c09c0c050206828250e09804252609c0c290e06428250320804250e0d40425010942826010a40c261609438050a0140c250190c2826160983805018d4382601c240c26210ac0c250a09404250e0a40425890ac3825160ac38050809838350e9042826160a43805080ac38350e0d43805080143835210140c25
|10=>0x309804290109838050e0a40c09010943825019042826210a40c250302428267d09804290e0a404260e0d43825040903829010a40c090a09404250d2080425080a43835010943805010943825200a404250e6340426
|_=>0
def opOffB : Nat → Nat → Nat
|6,0=>0x70c18400000000000000058800000000000000000000000000000000000000000013300000000000000000000000000f400000000348000000000002c80000000000000000001d000000000000000000010c0000000000000000000000000000000000000000000000000004
|6,1=>0x4c2124c454000000010500000fc80000f4800000000000000000000000000003b20e0c00000003440c1000000000000bc400000000000ad00000000000000000000000000000283000000009100000000000000000000000000000000000000000000000888000000000007cc000
|6,2=>0x1388000
|7,0=>0x3888df3370cd9335c8d520000d2333cccc3324cc633108c130000be32f08b932d8cb4200000002c4caf20000ad20000aa329cc0002948a2327cc9c326889822588942244c8f2230c89321c8843204c7e31ecc7921d8c7421c4c6e31acc692198c63318485e316cc58315885421488502
|7,1=>0x5e0d7535c8d6f35b480005ac96835989633580d5e256cd583558953354494f253494a351cd443504d3f200013c34e893824d4d3234c092d34a8d273490c000484d1e300011c246880004609153000112343cd0c3424d06341090133f8cfc23e4cf633cccf123bc8ec33a4ce630000e42
|7,2=>0x800c00000000007f89fb37e0df537cc9f037b4dec10001e930001e6378cc000780dde276cdd837589d42744dce372cdc83714c000708c0006fcdbd26e8db826d4db230001af36b49ab20001a83694da32680d9d3668c00000019736548000648d8f3630d8930001872610d8135f8d7b3
|7,3=>0x824e0630002033
|8,0=>0xa28a882a18a842a08a8029f8a7c29e8a7829d8a7429c8a7029b8a6c29a8a682998a642988a602978a5c2968a582958a542948a502938a4c2928a482918a442908a4028f8a3c28e8a3828d8a3428c8a3028b8a2c28a8a282898a242888a202878a1c2868a182858a142848a102838a0c2
|8,1=>0x29c2a68a982a58a942a48a902a38a8c2
|9,0=>0xa946a41a8c6a21a846a01a7c69e1
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
|0=>0xf80800000628400000290a00000108100000084000000040040000020000000008a1000000440800000220000000104a0000008200000004080000002010000001002000000800000000242800000121000000080000000020400000010000000003f400000010800000008100000004000000000800000000200000000050000000020000000008000000002000000000
|1=>0x800080000400010000200002000100000000030c408000107204000045100000022800000011000000008020000002420a000012001000008c4280000400000000120000000050010000020408000010010000008000000003081000001840000000c00000000510800000280100000140000000090100000045000000021050000010408000008014000004002000002000
|2=>0x1820008000c0e61400060712a0003038850001818468000c0c21400046110a000223985000111c40800080e2140004051080002028040001010008000805a040004010020001830810000c084000006000000002c710a000143a01000091c428000440000000209100000104000000081c46800040e2140002070020001010810000808400000404004000201100000100800
|3=>0x581c428002c062040010071120008018880004000000001d8ea14000e4510a000706885000381f400001c0ee14000e0750a000703085000381840800188ec14000c45300000601f81000291442800101220400080810200040200000020040000010002000008000020004000000001c1c4a8000e0e2140006869020003238850001914428000c8420400060f132000304804
|4=>0x12081c02808000800002070714a0103830890081c18408040c1e2d402060e16a01010389500418207a8010c4e614008426202004202000002100842801040e21400820600a004017105002001882801000c014008002202003103884001081c48800840e22000300710a001800800000c000020004c0423400240213800111000d000881c42800404c234001643110000b21885
|5=>0x800081f42a21040e215108001008801800804400480c42a002406211000c4110a8003008004000c3c42a0004ca21500020710a80010080040001a442a000000000800001002200103084088041840821000e214100c01000080543885040290c00820118e0041008453000802238850401104c0020048e61410020710a0800209800400100c0010040c230080001008040000800
|6=>0xa000a1d42c08040ea16000a8790b000343885
|_=>0
def pmB : Nat → Nat → Nat
|6,0=>0x19031f0b2d0100100019000000000000000019070000070a00000002000000500d000000000500000100000100000000000000000000000000140d000010000000073b00000000190000000000000000000000002000000000000006010000310000001900000600000100000000001b00000000000000000000000b000033
|6,1=>0x1900
|7,0=>0x1a8c8b282000201c6b44820c23ab204d40103607a261972e7baa88378a93030e729c07004f74683c6b002a51001e117c8e171091013c121a2f1003247056002020085a043c10001544b08f2c2009006a3c22ba2000004c870003003d21001085566d034e20315c48263e139865733a6c303f5a38123c9bb1405b8901a3034a03
|7,1=>0x12770016112d00681016a08d103457b2007d00a1af00169e459f4a105f27521839009900a403551042160049102000625c256e2b1d32000f106851690853004812744343
|8,0=>0x7984677854765cb75963c3a858b65e359a4180ad7f66a883904b7ab9b8a7b45c5c64644759295ea5c05ebdbfacc2819d4b5d94c1a65c6f75647ebb959a60bcb3a996aebe86925c7192
|9,0=>0x5cb55ca59246645e
|10,0=>0x46
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 8 (j % 128); fld (pmPalB (k / 32)) 37 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_237,9,runOps true dom_237 (0,roots_237) ops)] else [])++(if pm.testBit 1 then [(dom_166,5,runOps true dom_166 (0,roots_166) ops)] else [])++(if pm.testBit 2 then [(dom_175,8,runOps true dom_175 (0,roots_175) ops)] else [])++(if pm.testBit 3 then [(dom_107,5,runOps true dom_107 (0,roots_107) ops)] else [])++(if pm.testBit 4 then [(dzo_109_2,5,runOps true dzo_109_2 (0,roots_109) ops)] else [])++(if pm.testBit 5 then [(dom_233,5,runOps true dom_233 (0,roots_233) ops)] else [])++(if pm.testBit 6 then [(dom_201,4,runOps true dom_201 (0,roots_201) ops)] else [])++(if pm.testBit 7 then [(dom_231,9,runOps true dom_231 (0,roots_231) ops)] else [])++(if pm.testBit 8 then [(dom_79,5,runOps true dom_79 (0,roots_79) ops)] else [])++(if pm.testBit 9 then [(dzo_103_8,5,runOps true dzo_103_8 (0,roots_103) ops)] else [])++(if pm.testBit 10 then [(dom_199,5,runOps true dom_199 (0,roots_199) ops)] else [])++(if pm.testBit 11 then [(dom_238,8,runOps true dom_238 (0,roots_238) ops)] else [])++(if pm.testBit 12 then [(dom_203,7,runOps true dom_203 (0,roots_203) ops)] else [])++(if pm.testBit 13 then [(dom_207,8,runOps true dom_207 (0,roots_207) ops)] else [])++(if pm.testBit 14 then [(dzo_45_2,4,runOps true dzo_45_2 (0,roots_45) ops)] else [])++(if pm.testBit 15 then [(dom_227,7,runOps true dom_227 (0,roots_227) ops)] else [])++(if pm.testBit 16 then [(dom_45,4,runOps true dom_45 (0,roots_45) ops)] else [])++(if pm.testBit 17 then [(dom_102,4,runOps true dom_102 (0,roots_102) ops)] else [])++(if pm.testBit 18 then [(dzo_230_8,5,runOps true dzo_230_8 (0,roots_230) ops)] else [])++(if pm.testBit 19 then [(dzo_173_2,5,runOps true dzo_173_2 (0,roots_173) ops)] else [])++(if pm.testBit 20 then [(dom_235,8,runOps true dom_235 (0,roots_235) ops)] else [])++(if pm.testBit 21 then [(dom_111,7,runOps true dom_111 (0,roots_111) ops)] else [])++(if pm.testBit 22 then [(dzo_102_8,4,runOps true dzo_102_8 (0,roots_102) ops)] else [])++(if pm.testBit 23 then [(dom_234,5,runOps true dom_234 (0,roots_234) ops)] else [])++(if pm.testBit 24 then [(dom_171,5,runOps true dom_171 (0,roots_171) ops)] else [])++(if pm.testBit 25 then [(dom_236,6,runOps true dom_236 (0,roots_236) ops)] else [])++(if pm.testBit 26 then [(dom_143,5,runOps true dom_143 (0,roots_143) ops)] else [])++(if pm.testBit 27 then [(dom_205,7,runOps true dom_205 (0,roots_205) ops)] else [])++(if pm.testBit 28 then [(dzo_237_2,6,runOps true dzo_237_2 (0,roots_237) ops)] else [])++(if pm.testBit 29 then [(dom_230,6,runOps true dom_230 (0,roots_230) ops)] else [])++(if pm.testBit 30 then [(dom_173,6,runOps true dom_173 (0,roots_173) ops)] else [])++(if pm.testBit 31 then [(dom_206,5,runOps true dom_206 (0,roots_206) ops)] else [])++(if pm.testBit 32 then [(dom_109,5,runOps true dom_109 (0,roots_109) ops)] else [])++(if pm.testBit 33 then [(dom_165,5,runOps true dom_165 (0,roots_165) ops)] else [])++(if pm.testBit 34 then [(dom_167,6,runOps true dom_167 (0,roots_167) ops)] else [])++(if pm.testBit 35 then [(dom_174,6,runOps true dom_174 (0,roots_174) ops)] else [])++(if pm.testBit 36 then [(dzo_231_8,6,runOps true dzo_231_8 (0,roots_231) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_239 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_237 _ g hchk
    · exact cpcs (by decide +kernel) lowS_166 _ g hchk
    · exact cpcs (by decide +kernel) lowS_175 _ g hchk
    · exact cpcs (by decide +kernel) lowS_107 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_109_2_45 _ g hchk
    · exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · exact cpcs (by decide +kernel) lowS_201 _ g hchk
    · exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · exact cpcs (by decide +kernel) lowS_79 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_103_8_102 _ g hchk
    · exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_45_2_45 _ g hchk
    · exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_230_8_102 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_173_2_45 _ g hchk
    · exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · exact cpcs (by decide +kernel) lowS_111 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_102_8_102 _ g hchk
    · exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · exact cpcs (by decide +kernel) lowS_143 _ g hchk
    · exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_237_2_45 _ g hchk
    · exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · exact cpcs (by decide +kernel) lowS_167 _ g hchk
    · exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_231_8_102 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_237 9 s (0, roots_237) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_239 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_237 h

def symsG : List (List (Nat × Nat)) := [[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_239 == dom_239) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_239 goalM v ys) : RunD true dom_239 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_239 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 17 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 17 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 130 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 130 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 197 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 197 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 73 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 73 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 8 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 10) : ∀ i < NN s, bar true dom_239 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
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
  scr true dom_239 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 6 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 10) (h : RunD true dom_239 goalM s xsM) : False := by
  have hmin : 6 ≤ s := by
    have hl := run_len h; change 7 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_239 roots_239 goal_239 11 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_239

theorem lowS_239 : Lower true dom_239 roots_239 goal_239 11 := S_239.noCircuit

theorem lowS_247 : Lower true dom_247 roots_247 goal_247 11 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 32, 36)] (by decide +kernel) (by decide +kernel) lowS_243

theorem lowS_251 : Lower true dom_251 roots_251 goal_251 11 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00, 1, 9)] (by decide +kernel) (by decide +kernel) lowS_243

def dzo_118_8:=0x55005500550055005500550055005500
def gzo_118_8:=0x55005400550054005400500044000000
def gsh_118_8:=0x550054005500540054005000440000
theorem lowS_zo_118_8_118:Lower true dzo_118_8 roots_118 gzo_118_8 7:=lower_iso (d1:=dom_118) (roots1:=roots_118) (T1:=gsh_118_8) [(dom_118,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_118_8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [] (by decide +kernel) (by decide +kernel) lowS_118)
def dzo_82_32:=0x50005000000000005000500000000
def gzo_82_32:=0x50004000000000004000000000000
def gsh_82_32:=0x500040000000000040000
theorem lowS_zo_82_32_82:Lower true dzo_82_32 roots_82 gzo_82_32 4:=lower_iso (d1:=dom_82) (roots1:=roots_82) (T1:=gsh_82_32) [(dom_82,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_82_32) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [] (by decide +kernel) (by decide +kernel) lowS_82)
def dzo_210_8:=0x5000500000000000500050000000000050005000000000005000500
def gzo_210_8:=0x5000500000000000500050000000000050004000000000004000000
def gsh_210_8:=0x50005000000000005000500000000000500040000000000040000
theorem lowS_zo_210_8_82:Lower true dzo_210_8 roots_210 gzo_210_8 5:=lower_iso (d1:=dom_210) (roots1:=roots_210) (T1:=gsh_210_8) [(dom_210,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_210_8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x50005000000000005000500000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_82)
def dzo_246_8:=0x5500550055005500550055005500550055005500550055005500550055005500
def gzo_246_8:=0x5500550055005500550055005500550055005400550054005400500044000000
def gsh_246_8:=0x55005500550055005500550055005500550054005500540054005000440000
theorem lowS_zo_246_8_118:Lower true dzo_246_8 roots_246 gzo_246_8 8:=lower_iso (d1:=dom_246) (roots1:=roots_246) (T1:=gsh_246_8) [(dom_246,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_246_8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x55005500550055005500550055005500000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_118)
def dzo_244_8:=0x1100110011001100110011001100110011001100110011001100110011001100
def gzo_244_8:=0x1100110011001100110011001100110011001000110010001000100000000000
def gsh_244_8:=0x11001100110011001100110011001100110010001100100010001000000000
theorem lowS_zo_244_8_116:Lower true dzo_244_8 roots_244 gzo_244_8 5:=lower_iso (d1:=dom_244) (roots1:=roots_244) (T1:=gsh_244_8) [(dom_244,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_244_8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x11001100110011001100110011001100000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_116)
def dzo_214_40:=0x5500550000000000550055000000000055005500000000005500550000000000
def gzo_214_40:=0x5500550000000000550055000000000055005400000000005400500000000000
def gsh_214_40:=0x550055000000000055005500000000005500540000000000540050
theorem lowS_zo_214_40_82:Lower true dzo_214_40 roots_214 gzo_214_40 6:=lower_iso (d1:=dom_214) (roots1:=roots_214) (T1:=gsh_214_40) [(dom_214,40)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_214_40) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x500050000000000050005000000000005000500000000000500050,0,4),(0x550055000000000055005500000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_82)
def dzo_214_32:=0x55005500000000005500550000000000550055000000000055005500000000
def gzo_214_32:=0x55005500000000005500550000000000550054000000000054005000000000
def gsh_214_32:=0x550055000000000055005500000000005500540000000000540050
theorem lowS_zo_214_32_82:Lower true dzo_214_32 roots_214 gzo_214_32 6:=lower_iso (d1:=dom_214) (roots1:=roots_214) (T1:=gsh_214_32) [(dom_214,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_214_32) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x500050000000000050005000000000005000500000000000500050,0,4),(0x550055000000000055005500000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_82)
def dzo_86_32:=0x550055000000000055005500000000
def gzo_86_32:=0x550054000000000054005000000000
def gsh_86_32:=0x5500540000000000540050
theorem lowS_zo_86_32_82:Lower true dzo_86_32 roots_86 gzo_86_32 5:=lower_iso (d1:=dom_86) (roots1:=roots_86) (T1:=gsh_86_32) [(dom_86,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_86_32) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x5000500000000000500050,0,4)] (by decide +kernel) (by decide +kernel) lowS_82)
def dzo_214_8:=0x55005500000000005500550000000000550055000000000055005500
def gzo_214_8:=0x55005500000000005500550000000000550054000000000044000000
def gsh_214_8:=0x550055000000000055005500000000005500540000000000440000
theorem lowS_zo_214_8_86:Lower true dzo_214_8 roots_214 gzo_214_8 6:=lower_iso (d1:=dom_214) (roots1:=roots_214) (T1:=gsh_214_8) [(dom_214,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_214_8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x550055000000000055005500000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_86)
def dzo_210_32:=0x5000500000000000500050000000000050005000000000005000500000000
def gzo_210_32:=0x5000500000000000500050000000000050004000000000004000000000000
def gsh_210_32:=0x50005000000000005000500000000000500040000000000040000
theorem lowS_zo_210_32_82:Lower true dzo_210_32 roots_210 gzo_210_32 5:=lower_iso (d1:=dom_210) (roots1:=roots_210) (T1:=gsh_210_32) [(dom_210,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_210_32) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x50005000000000005000500000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_82)
namespace S_254
def pairsG : List (Nat × Nat) := [(2,18), (2,66), (2,130), (4,36), (4,68), (4,132), (6,22), (6,38), (6,70), (6,134), (8,136), (10,26), (10,74), (10,138), (12,44), (12,76), (12,140), (14,30), (14,46), (14,78), (14,142), (16,18), (16,80), (16,144), (20,22), (20,52), (20,84), (20,148), (24,26), (24,88), (24,152), (28,30), (28,60), (28,92), (28,156), (32,36), (32,160), (34,38), (34,50), (34,98), (34,162), (40,44), (40,168), (42,46), (42,58), (42,106), (42,170), (48,50), (48,52), (48,112), (48,176), (56,58), (56,60), (56,120), (56,184), (64,66), (64,68), (64,80), (72,74), (72,76), (72,88), (72,200), (96,98), (96,100), (96,112), (96,224), (104,106), (104,108), (104,120), (104,232), (128,130), (128,132), (128,136), (128,144), (128,160), (192,194), (192,196), (192,200), (192,208), (192,224)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xffffffffffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_254.map (· &&& dom_254)
def goalM : Nat := goal_254 &&& dom_254
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
|3,0=>0x5af2f
|4,0=>0xca193abc06a3b0b
|5,0=>0xa67a6891137d3eb765e3491953f32025ce61ae6a191d708e1f08879015f6
|6,0=>0xfc5eaf0864e97f3e5e25dc71fd78e5d3766d14f4ce0c2c0576bc618b48e4aafc8a7bdc9c95c93db7935608fff7862db858658003f7f4a27ca057ab067501273b7c739a36a81769f8d67dfd623a760ec55fadb5af55522cd4f6d64f1d74b5194b24c496e6485ff45b734584042c9b3f62b3e73d39bb837dfc36dd336c4c36ab33618c35c7f35540314a330f132b6d327643249e6244cd217ee1eb961eb5e1eb0c1cdfa13a25110ba0f9b30db3f0b4060ad1809c61084dd0316e00cc1
|7,0=>0xf0325e7a52e771edfe5dd89b5d88d5d4a5cd0179cbdbdc7bc8c782dc326abf3aabb147b8674b7255b477ab0914ad2f9ace0fac570abc2cab6aaaa8b2a8dc6a7bdca3ac39eb4d9babd9b437922ab91e4a91a2189e3b8945c884aa850e08257280caf7f5f47e17775457751a46d9b5672fa667d16164c610ec5e8675c0dd5b9ef5a921571975708a54f6c52eec522b64ed304d2b84c61a4c12b4bf61492824845d478644662a465a0444b43c4bb3b33c3841f37fb33766536afc35bbe351cf34d402c53a2b7852a1e226e972559e239b121e312109f1eddc1e3f81d8db1d6091c49518ce4186bc182f815d5113db00e9950e2690d8b90bdb30b72106bee04d9700cbf
|8,0=>0xec227e1de1e0d9edead1d7549d3e6bbcb78b74a89af51954498fc6c8c725887bf7ec2b762756f0336e5dd66ea46603f653e1608545feb35fa4753fce4d03246870442fd4238840f6939fb03709331f25315c1305d72f3d02491d1bfbf1ac6d18ddc1767c16d7714bbd13e9610e6e0bed404697
|9,0=>0xeae9ba661d6dca76d25169e1c64cb3640555eb271c5cf0b7500a4a9
|10,0=>0x1b243
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a00000a0a00000000000000000001555400015554000000000000000000015555515155555152aaaaaa82aaaaaa82aaaaaa82aaaaaa82aaaaaa82aaaaaa82aaaaaa82aaaaaa800000000000000005555545455555454000000000000000055555454555554540000000000000000aaaaaaaaaaaaaaaa0000000000000000aaaaa8a8aaaaa8a80000000000000000000000000000000000000000000000015555515155555152a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a00002a2a00002a2a00002a2a00005555555555555555555555555555555555550000555500005555000055550000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0a0a0a0a0a0a0a15555515155555151555551515555515155555151555551515555515155555152a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a555555555555555500000000000000005555555555555555000000000000000000008a8a00008a8a00008a8a00008a8a00008a8a00008a8a00008888000088895555515155555151555551515555515155555151555551500000000000000002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa22222222222222222222222222222225555545455555454555554545555545455555454555554545555000055550000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa88888888888888880154015401540155555551555555515400000000000000015555515155555152aaa80002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80002aaa80004444444444444444444444444444444444444444444444444444444444444444aaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a155555555555555555555555555555555555555555555555400000000000000022222222222222222222222222222222222222222222222222220000222200005555505055555050555550505555505055555050555550500000000000000000a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a15555555555555555555555555555555400000000000000000000000000000002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa80002aaa80005555545455555454555554545555545455555454555554544444444444444444aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa000000015401540154015401540154015401540154015401540154015401540154015402aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa82828282828282828282828282828285555545455555454555554545555545455555454555554544444000044440000
|0,1=>0xa0a080a0a0a080a0a0a080a0a0a080a0a0a08080a0a08080a0a08080a0a080915151515151515151515151515151515151515151515151511111111111111102828282828282828282828282828282828282828282828280000000000000000000050500000505000005050000050500000505000005050000000000000000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000000000000aaaaa8a8aaaaa8a9151400011514000115140001151400011514000115140001111000011110000088880808888808088888080888880808888808088888080888880000888800000000000505550550000000050555055000000005050505000000000505050500000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000888800008889515151515151515151515151515151515151515151515150000000000000000000008888000088880000888800008888000088880000888800000000000000001010101010101010101010101010101010100000101000001010000010100000000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000a8a80000a8a8015401540154015401540154015401540000000000000000000000000000000282aa82aa82aa82aa82aa82aa82aa82aa82828282828282828282828282828280000545400005454000054540000545400005454000054540000545400005454aaaa8888aaaa8888aaaa8888aaaa8888aaaa8888aaaa8888aaaa8888aaaa88880001115400011154000111540001115400011110000111100001111000011110080800000808000008080000080800000808000008080002aaa80002aaa8000444455554444555544445555444455554444555544445555444444444444444402020202020202020202020202020202020202020202020200000000000000000001555400015554000155540001555400015554000155540000000000000002a2aaa2aaa2aaa2aaa2aaa2aaa2aaa2aaa2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a11111010111110101111101011111010111110101111101011111010111110100000aaaa0000aaaa0000aaaa0000aaaa0000a8a80000a8a80000a8a80000a8a844444444444444444444444444444444444444444444444444440000444400028a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a82828a8a82828a8a82828a8a8285050545550505455505054555050545550505454505054545050545450505454aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000888800008888000044444444444444444444444444444444444444444444444400000000000000008888888888888888888888888888888888888888888888888080808080808084455445544554455445544554455445544444444444444444444444444444444
|0,2=>0xaaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa0155555554141414015555555414141401555555541414140155555554141414002828282828282828282828282828282820202020202020202020202020202025555111155551111555511115555111155551111555511115555000055550000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a95555415555554155555541555555415555554141555541415555414155554142aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa2222aaaa2222aaaa2222aaaa222000000000000000000000000000000005555505055555050555550505555505088888888888888888888888888888888aaaaa8a8aaaaa8a8aaaaa8a8aaaaa8a80001555400015554000155540001555400015554000155540001414000014140282800282828002828280028282800282828000028280000282800002828000555544555555445555554455555544555555444455554444555544445555444400000000000000000000000000000000aaaaaaaaaaaaaaaaa8a8a8a8a8a8a8a81414141414141414141414141414141414141010141410101414101014141012aaaaa2aaaaaaa2aaaaaaa2aaaaaaa2aaaaaaa2a2aaaaa2a2aaaaa2a2aaaaa2a5555555555555555555555555555555555555050555550505555505055555050aaaaaaa8aaaaaaa8aaaaaaa8aaaaaaa8aaaaaaa8aaaaaaa8aaaaaaa8aaaaaaa95554000155540001555400015554000155540001555400015150000151500002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa80000000000000002a2a2a2a2a2a2a2a5555505055555050555550505555505044444040444440404444404044444040222220222222202222222022222220222222202022222020222220202222202145454545454545454545454545454545454545454545454541414141414141400000202800002028000020280000202800002020000020200000202000002025555555555555555555555555555555500005454000054540000545400005454aaaa080aaaaa080aaaaa080aaaaa080aaaaa0808aaaa0808aaaa0808aaaa080954015401540154015555555155555551540154015401540155555551555555508888888888888888888888888888888888880000888800008888000088880001155105511551055115510551155105511111010111110101111101011111010aaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0aaaaa0808aaaa0808aaaa0808aaaa08080001555400015554000155540001555400011110000111100001111000011112aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa2a2aaaaa2a2aaaaa2a2aaaaa2a5555005555550055555500555555005555550000555500005555000055550000
|0,3=>0xaaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa155555555555555555555555555555555555555540000000155555554000000008888888888008800888888888800880088888888880088008888888888008805555555555550000555555555555000055555555555500005555555555550000222222222222000022222222222200002222222222220000222222222222000014141414141414141414141414141414141400001414000014140000141400000002aaa80002a8000002aaa80002a8000002aaa80002a8000002aaa80002a804444555544445544444455554444554444445555444455444444555544445544aaaaaaaa00aa00aaaaaaaaaa00aa00aaaaaaaaaa00000000aaaaaaaa000000000000000000000000000000000000000151515151515151515151515151515152a88aa882a88aa882a88aa882a88aa882a88aa882a88aa882a88aa882a88aa8855445544554455445544554455445544554455445544554455445544554455440000aa880000aa880000aa880000aa880000aa880000aa880000aa880000aa8955515551555155515551555155515551555155515551555155515551555155500002aaa00002aaa00002aaa00002aaa00002aaa00002aaa00002aaa00002aaa555555555500550055555555550055005555555555005500555555555500550000002222000022000000222200002200000022220000220000002222000022015555555555555555555555555555555555555555555555555555111155551112aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa8282aaaa8285555555555554444555555555555444455555555555544445555555555554444aaaaaaaaaaaaaa88aaaaaaaaaaaaaa88aaaaaaaaaaaaaa88aaaaaaaaaaaaaa8800000000000000000000000000000001555551515555515155555151555551508888880088888800888888008888880088888800888888008888880088888805151515051515150515151505151515051515150515151505151515051515150000000000000000000000000000000000000000000000000a8a8a8a8a8a8a8a95555555555115511555555555511551155555555551155115555555555115512aaaaaaaa22222222aaaaaaaa22222222aaaaaaaa22222222aaaaaaaa22222220000555500005544000055550000554400005555000055440000555500005544000000000000000000000000000000000000a8a80000a8a80000a8a80000a8a8444400444444004444440044444400444444000044440000444400004444000000000002aaaaaaa800000002aaaaaaa800000002828282800000000282828280505050005050500050505000505050005050500050505000505050005050500
|0,4=>0x2aaaaaa22aaaaaa22aaaaaa22aaaaaa22aaaaaa22aaaaaa22aaaaaa22aaaaaa20000000055445544000000005544554400000000554455440000000055445544
|_,_=>0
def stPool : Nat → Nat
|0=>0x1f0a030d0215010f0a031e0d02070c06031d1c0d070c06031b0d02070c06031a0d02070c06030b02191114031802170c08030d02010c120302010c130a030d02071112030d0201040a03100207110a030207090806031002070f06030502010c08030e0d070c06030b0201090a03020109080302070006030502010403020100
|1=>0x2070f06030b070c2e1406032d02070c0a06031802072c0c0a030d02010c0a2b030b02190c1406030d020711222a030b0d290c1406030d02010c280a030d02070c270a030b0d0215110a030d020711260a030d0225070c0a030d24070c1406030201070c230a030207230a2206030d020711210a03160d07201406030d02010c
|2=>0xd02013e0c0a030b0207090a06031802070c0a3c033b0d02070c06031802070f0c2a030d0207110a36030b18021511140302070c3a0a06030d0207390a062f0d070c381406032f050207110a030201070c370a030d02070f360603161802070c0a031802070c0a35030d02070c340a0302070c330a06030d310c301406032f05
|3=>0x32030d024a07110a030d070c491406030d0207040a0603160d310c1406030d02070c480a03470d070c1406030d02010c0a3603461c0d070c06030b0d15201406030d0207450a22030d070c44140603430d02070c0a030b02070c420a03410d02070c0a0340070c281406030d020711300a030d02170c3606030d070c3f140603
|4=>0x1406030d021707110c0a030b0d310c140603540d070c1406030d0253070c0a030d02070c520a03510d070c140603160d02010c0a0316180207111403500d02150c0a034f1c0d070c0603024e070c0a06030d02070c1206030b1802170c0a030d024d070c0a031802070c4c14030d070c4b1406030d0207260a06031c0d070c06
|5=>0x70c0a06030b0d025b0c140603590d02070c0a035a400d070c1406030b0d150c140632031c0b0d02070c06031d160d070c1406030d024a070c0a06030d0201070f0c0a030d02070c521406030d02070f0a220603570d02070c140603180d02070c0a3d030d02070c560a0603160d02010c140603050d0207090a06030d070c55
|6=>0x70c14060d070c381406030d070c6214062f0d02070c611406032f0d0201070c0a0350180d02070c0a0354400d070c140603160d02070c0a065e0d070c1406030d02070c5d0a030d02070c0a3506030b0d0207110c0a030d02070c450a030d0201070c0a2a034f0d15070c1406030d0215010c0a03180d02070f0c0a035c0d02
|7=>0xd0215070f0a06030d0267070c0a06030d025b15070c0a030b180207110c14030d0207110c0a2a031c0d02070c06030d0219070c1406030d070c641406030d1507201406030d02070c0a3c06030d02070c631406030d02010c281406030d02070c271406030d02070f0c2a06030d02070c370a06030b0d0215111406030d0225
|8=>0x301406031d0b0d150c1406030b0d07200c140603050d02070f0c06030d2915070c14066b030d070c1406036a0d02070c1406030d0215170c0a06030d68070c1406030d02070c280a060359180d02070c0a032f0d0207110a030d02010c0a3d03161802070c1406030d070c30140632030d02070c341406030d02070c1f0a0603
|9=>0x3160d070c140632030d02070c481406030d070c6f1406030d02070c222a06030d02073e0c0a06030d0207110a22036e0d02070c0a06036d0d02070c0a06030d0207260a06030b0d02150c0a0603161c0d02070c06034f0d070c140603430d02070c1406030b02070c421406032f180207111403410d02070c1406030d020711
|10=>0x6030d07780c1406035a0d070c1406034f160d070c140677032f0d070c1406030b0d02760c1406032f0d31070c14060302070f0c370a06030d02070c0a3606030d025b070c0a032f0502070c0a060302070c230a06032f0d07201406030d02170c0a3d06030d75070c1406030b1802070c0a030b070c731406030d070c711406
|11=>0xc611406030d0201070c0a03400d070c140603160b0d02070c1406030d02070c0a2206030b0d070c140632030d02070c7b1406030d02070c42140603050d02070c0a06030d021507111406030d02070c301406032f1802070c140666030d070c1406030d72070c140603500d02070c140603580d02070c1406030d02070c7a14
|12=>0x15070c1406030d0215070c0a06032f0d7f070c14067e032f0d02070c140603160d02070c1406032f0d070c14063270032f0d070c1406030d070c7d1406032f0d0201070c14060350180d02070c1406030b0d0207110c1406030d0215010c140603590d02070c1406030d070c60140603180d02070c0a030d070c7314060d0207
|13=>0x32f0d02070c14067c030d02070c1406030d74070c1406032f0d02070c0a066c030d02070c140603180d0207110c1477030d070c1406030d31070c1406030b0d02150c140603810d070c1406030d02070c0a3d06031d0b0d070c14060359180d02070c1406030d0217070c0a06030d070c801406035f0d15070c1406030d025b
|14=>0x30d02070c1406030d02070c0a06030d0215070c1406030d7f070c14067e030d02070c140603180d02070c1406030d070c14063270030d070c1406030d0201070c1406
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>4
|4,0=>0x39404a8045
|5,0=>0xaac13d824b043607ac0dd818b02b604ac07d80cb0136
|6,0=>0x428e835d0339ff73f0e7c5cf539e373b8e755ce739c77380e6e5cd939ab7348e675ccb398f7310e605cbd397372d8e595caf395772a0e525ca1393b7268e4b5c93391f7230e445c85390371f8e3d5c7738e771c0e365c6938cb7188e2f5c5b38af7150e285c4d38937118e215c3f387770e0e1a5c31385b7
|6,1=>0x985d2d3a537498e915d1f3a377460e8a5d113a1b7
|7,0=>0x89d111a21fbc37885f10a1e10bc1988231026200c3f987e30fa61f0c3d987a4ef2a1e1bbbc77690eb21d2439c87290e321c2437c86eccdbddb3c35f86af0d3e1a3c3416674ecca195432376370c4e1863b0485f90bd2176bae585bb0b56166c2c5857b0ad6156c2a5853b0a56146c28584fce9da137ba687
|7,1=>0x15e1eb8bd698ac315662a8c5498a8314e9e99452b7a48f47228abd0e7a0ef401e7c44f089d2f38626cc4d27995130a25dbcb389571291e4e4494891af21623ec47588db119622ec4567
|8,0=>0x370c6d98da31b29f61bebb8d68fab2352469b9d271a31f42467b9ce719ae3314e5a8ca5192a321be3a9c6338a271046188c22f829f01bdfc7beaf7b9ef2cddd8bab17362e2c5bd8b6b16b62d2c59e7b2ef63e2c3c57f8
|9,0=>0x1cd5f96c7267e3d1c5a387bf087e011be237846e97
|10,0=>0x73c7
|_,_=>0
def dictMask : Nat := 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def wireSAt (i : Nat) : Nat := if i < 130 then (dictB (i / 512) (i / 32 % 16) >>> (255 * (i % 32))) &&& dictMask else 0
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
|0=>0xc0a81cc9070d4081a150a01c3114064bc050d0c41c190d1581c310c3d41c2a0d3d81c2a0c0a45019150a01c311406434190d0740cc607324081a0d0a450190f0dc30290c0b41c350d228302a073245437070c4081a0c0a434291406430a90d0a81c8a0c0a8501907064302e070d430160d0a480370f0d03029170cc1c290507c34290c0a450190706458280d1545019
|1=>0xc0b41c350b0c4082d070d41c890c0a850190c0a41c1914065641f180c434190c224302a1406560310b06c1c35070a83419140645c37070a450190d1541c310706414300d0a450194007c34c9020681c290c0645019073241c350206900310d324081a0b0c450190d1541c3107064bc1d0d0c434192f0743431160a03455070c45019070a43419140642c44070d41c89
|2=>0x745460330d0640cc607324081a400cc34c9020683431030181c190d0c41c1914064601d0d06450190d324081a0d1541c31140640d815f07c08351107c301914064348a0c0a85019070d430191406460330d064501907064342a1406458090d1541c31070c41c191406430290d06450190d224302a1406430050706460310d06450190d324081a070c41c35020685853
|3=>0x1406430350c0645019070a81c1914064302d0d0743419150dc1c31020685462070c434190507c342914064302914064542b070c45019140645419070c41c350d06430190d0a850191614cbc1d0d0c45460070c43419660dd9409030c430c9070c4081a072a8342a140645463070c4341907064302e070d56c37010c41c190c0a4342a140643c370c0a450190c0743019
|4=>0x70a850190c064302a1406414310d0a450190507434291406414330d0a450190d0741c311406458532f074343116024bc1d0d0c435751107c30190d11830190d0c430190d064bc050d0c41c190d1581c31070c4082d070d430c9070d4081a0c0a434291406454c9070c4081a6c0240cbd0d0c4581b2f0743431070a4501907694317e020d450190c0b81c35180c43419
|5=>0x1807c34190c795c037030242cc9070d4081a16024bc1d0d0c4343103324081a1506c1c310d0c41cc9020683c370c0a45019150a01c311406404310706450190d0a450190f0d030291406430350c324081a070a81c291406408a10c0b81c350d074341914065d0370d07408310d7280855070c42c31070d4081a300643456070c5c0bf0d0c40c090d0a8302a1406430f5
|6=>0x150641c31070c450190d0c4081d0d0c40c192f07434310d0c4081a0d0c40c09700cc0c090d0c41c19180743419070d43019070c41c19180c434195f07c08350d06450190d7480831030181c190706450190d324081a0c0b41c350c0a85019070d4081a7c0cc0c35110dc30190d0a450190c07430190d1581c310d0c43419650240c31021541c31010d41c190b06c1c35
|7=>0x5019070c4081d030643419020680c09070643431030d408310d0c45019032f434310c064341903324081a07324081a0d0741c312f0243431070a85019020b41c35180c43419070a450190374808310c0740835
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0x800000000000000000000000000000
|6,0=>0x20900000000001f900000003c3000000072600000000000000000000d8c000342000000064400018100005c42b3149000000026312108880002020f100000001a40b98000000152099000000000007a00000000d2000030414400004100000c40420000000000000
|6,1=>0x53127a130c0004a20001190866000
|7,0=>0x851c20a0a70237f9bf0df26f63799bc0dda6eb2741b94dc64e036e9b68dae6d43689b38d966c83629b08d804bd35d1adcd686b13571ab09526a63519a80d3a69a34b9a50d2268e3459a2490c68424099f8cf667833a99c8cde66c3349998cc666032e9968cae6543
|7,1=>0x5ecef07753b91dc0ada76a3b39d90ec455f3ae1d64eac7533a81d34e947473a21d04e7c73b39c1cd4e6472f3961ca4e4c7242909c78e3851938b1c4ce2070d3
|8,0=>0x3b05d62ea1748ba05ce2e61728b905c62e21708b805be2de16e8b705b62da16c8b605ae2d616a8b505a62d21688b4059e2ce1668b305962ca1648b2058e2c61628b105862c21608b0057e2
|9,0=>0x7907c63e21f08f807be3de1ee8f707b63da1
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
|0=>0x28800000004d400000008a800000010600000002080000000400000000040000000006d00000000b6000000013c0000000240000000047000000008a00000001080000000208000000040000000005e000000009c00000001280000000230000000044000000008000000000c0000000016000000001400000000200000000038000000006000000000a00000000100000000010000000000
|1=>0x8001e000010000c000010002800001820f000003005e000006001c00000623f800000c45d000000e8e400000171ec000002b3f800000547f000000a8fc00000151ec00000233d800000447f00000088f6000000e408000000e3d000000147f00000028fc000000412000000081100000008420000000aee00000010bc00000020b0000000407000000080c00000010100000002000000000202
|2=>0x400001e0008000034000c0023c000110547b000220485600044010a80008010010001000d7900020012a000020151fc000202a3f800040447f00008088fc0000c011bc000180235800010566b000020a8fe00004151ec000081b15000009040700001202ee000022055400004223f800008045f00001004ae00002001d4000040023800004800f000008081a000010011c0000200228000040040
|3=>0x24000a8fe044200002808000023f008010547f010000a0fc01c000008c010002a3f801000002300100200ae00200115fc0040000ab800800011700100000a20020000048004000006800600446f0008608cf60010c111ec00200e337800401842f00080288de001004183c00200623f800400862f0008008cde00100111fc002002237800400062f000800004e00080010b40010001010002000045
|4=>0x100008111fe000102103a40000467b48000080f6900000098d00004828ba00008447f40000288fe80000111ec800102237880430447b0a2100a8fe10002315fc2000440ae840000447f050000a8fe08008151ec1001020010130000002
|_=>0
def pmB : Nat → Nat → Nat
|5,0=>0x1000000000000000000
|6,0=>0x1a04230019000b0900210000001b00000100001f0000000000000a0002000002000200061c010000012002000202000015070000020200000004000002001a02000200021000000000
|7,0=>0x53587a8106283f274b61264d732c387b2b2903540741633d1d62070c2b0510641e227e12072e330d727d243a6a46232a036040034c040f172433370d1308030743061d515a05454a592452770e14441880483f5f093b570711787442033e0d1871255e5d752d5b
|8,0=>0x676f6c82368f7930873c7683798d305691905035554785168c6d7f697c89495c8e6532886b708b8a683434868439
|9,0=>0x668a5692694e3449316e4f
|10,0=>0x2f
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 8 (j % 128); fld (pmPalB (k / 32)) 39 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_246,9,runOps true dom_246 (0,roots_246) ops)] else [])++(if pm.testBit 1 then [(dom_252,8,runOps true dom_252 (0,roots_252) ops)] else [])++(if pm.testBit 2 then [(dzo_118_8,7,runOps true dzo_118_8 (0,roots_118) ops)] else [])++(if pm.testBit 3 then [(dom_238,8,runOps true dom_238 (0,roots_238) ops)] else [])++(if pm.testBit 4 then [(dom_218,7,runOps true dom_218 (0,roots_218) ops)] else [])++(if pm.testBit 5 then [(dom_190,9,runOps true dom_190 (0,roots_190) ops)] else [])++(if pm.testBit 6 then [(dom_250,8,runOps true dom_250 (0,roots_250) ops)] else [])++(if pm.testBit 7 then [(dom_182,8,runOps true dom_182 (0,roots_182) ops)] else [])++(if pm.testBit 8 then [(dzo_82_32,4,runOps true dzo_82_32 (0,roots_82) ops)] else [])++(if pm.testBit 9 then [(dom_236,6,runOps true dom_236 (0,roots_236) ops)] else [])++(if pm.testBit 10 then [(dom_118,7,runOps true dom_118 (0,roots_118) ops)] else [])++(if pm.testBit 11 then [(dzo_210_8,5,runOps true dzo_210_8 (0,roots_210) ops)] else [])++(if pm.testBit 12 then [(dzo_246_8,8,runOps true dzo_246_8 (0,roots_246) ops)] else [])++(if pm.testBit 13 then [(dzo_244_8,5,runOps true dzo_244_8 (0,roots_244) ops)] else [])++(if pm.testBit 14 then [(dom_222,8,runOps true dom_222 (0,roots_222) ops)] else [])++(if pm.testBit 15 then [(dom_102,4,runOps true dom_102 (0,roots_102) ops)] else [])++(if pm.testBit 16 then [(dom_116,4,runOps true dom_116 (0,roots_116) ops)] else [])++(if pm.testBit 17 then [(dom_172,5,runOps true dom_172 (0,roots_172) ops)] else [])++(if pm.testBit 18 then [(dom_188,6,runOps true dom_188 (0,roots_188) ops)] else [])++(if pm.testBit 19 then [(dom_82,4,runOps true dom_82 (0,roots_82) ops)] else [])++(if pm.testBit 20 then [(dzo_214_40,6,runOps true dzo_214_40 (0,roots_214) ops)] else [])++(if pm.testBit 21 then [(dzo_214_32,6,runOps true dzo_214_32 (0,roots_214) ops)] else [])++(if pm.testBit 22 then [(dom_214,6,runOps true dom_214 (0,roots_214) ops)] else [])++(if pm.testBit 23 then [(dom_242,7,runOps true dom_242 (0,roots_242) ops)] else [])++(if pm.testBit 24 then [(dzo_230_8,5,runOps true dzo_230_8 (0,roots_230) ops)] else [])++(if pm.testBit 25 then [(dom_174,6,runOps true dom_174 (0,roots_174) ops)] else [])++(if pm.testBit 26 then [(dzo_86_32,5,runOps true dzo_86_32 (0,roots_86) ops)] else [])++(if pm.testBit 27 then [(dom_186,6,runOps true dom_186 (0,roots_186) ops)] else [])++(if pm.testBit 28 then [(dom_226,4,runOps true dom_226 (0,roots_226) ops)] else [])++(if pm.testBit 29 then [(dom_228,5,runOps true dom_228 (0,roots_228) ops)] else [])++(if pm.testBit 30 then [(dom_240,4,runOps true dom_240 (0,roots_240) ops)] else [])++(if pm.testBit 31 then [(dom_244,6,runOps true dom_244 (0,roots_244) ops)] else [])++(if pm.testBit 32 then [(dom_230,6,runOps true dom_230 (0,roots_230) ops)] else [])++(if pm.testBit 33 then [(dzo_214_8,6,runOps true dzo_214_8 (0,roots_214) ops)] else [])++(if pm.testBit 34 then [(dom_234,5,runOps true dom_234 (0,roots_234) ops)] else [])++(if pm.testBit 35 then [(dom_206,5,runOps true dom_206 (0,roots_206) ops)] else [])++(if pm.testBit 36 then [(dzo_210_32,5,runOps true dzo_210_32 (0,roots_210) ops)] else [])++(if pm.testBit 37 then [(dom_248,5,runOps true dom_248 (0,roots_248) ops)] else [])++(if pm.testBit 38 then [(dom_86,5,runOps true dom_86 (0,roots_86) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_254 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_118_8_118 _ g hchk
    · exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_82_32_82 _ g hchk
    · exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_210_8_82 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_246_8_118 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_244_8_116 _ g hchk
    · exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · exact cpcs (by decide +kernel) lowS_102 _ g hchk
    · exact cpcs (by decide +kernel) lowS_116 _ g hchk
    · exact cpcs (by decide +kernel) lowS_172 _ g hchk
    · exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · exact cpcs (by decide +kernel) lowS_82 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_214_40_82 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_214_32_82 _ g hchk
    · exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_230_8_102 _ g hchk
    · exact cpcs (by decide +kernel) lowS_174 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_86_32_82 _ g hchk
    · exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · exact cpcs (by decide +kernel) lowS_226 _ g hchk
    · exact cpcs (by decide +kernel) lowS_228 _ g hchk
    · exact cpcs (by decide +kernel) lowS_240 _ g hchk
    · exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_214_8_86 _ g hchk
    · exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_210_32_82 _ g hchk
    · exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · exact cpcs (by decide +kernel) lowS_86 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_246 9 s (0, roots_246) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_254 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_246 h

def symsG : List (List (Nat × Nat)) := [[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_254 == dom_254) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_254 goalM v ys) : RunD true dom_254 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_254 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 12 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 75 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 75 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 103 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 103 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 46 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 46 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 11 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 11 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 10) : ∀ i < NN s, bar true dom_254 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
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
  scr true dom_254 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 6 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 10) (h : RunD true dom_254 goalM s xsM) : False := by
  have hmin : 6 ≤ s := by
    have hl := run_len h; change 7 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_254 roots_254 goal_254 11 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_254

theorem lowS_254 : Lower true dom_254 roots_254 goal_254 11 := S_254.noCircuit

def isoMvS_253 : List (Nat × Nat) := [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)]
theorem lowS_253 : Lower true dom_253 roots_253 goal_253 11 :=
  lower_iso isoMvS_253 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_239

namespace S_255
def pairsG : List (Nat × Nat) := [(1,9), (1,33), (1,65), (2,18), (2,66), (2,130), (3,11), (3,19), (3,35), (3,67), (3,131), (4,36), (4,68), (4,132), (5,13), (5,37), (5,69), (5,133), (6,22), (6,38), (6,70), (6,134), (7,15), (7,23), (7,39), (7,71), (7,135), (8,9), (8,136), (10,11), (10,26), (10,74), (10,138), (12,13), (12,44), (12,76), (12,140), (14,15), (14,30), (14,46), (14,78), (14,142), (16,18), (16,80), (16,144), (17,19), (17,25), (17,49), (17,81), (17,145), (20,22), (20,52), (20,84), (20,148), (21,23), (21,29), (21,53), (21,85), (21,149), (24,25), (24,26), (24,88), (24,152), (28,29), (28,30), (28,60), (28,92), (28,156), (32,33), (32,36), (32,160), (34,35), (34,38), (34,50), (34,98), (34,162), (40,41), (40,44), (40,168), (42,43), (42,46), (42,58), (42,106), (42,170), (48,49), (48,50), (48,52), (48,112), (48,176), (56,57), (56,58), (56,60), (56,120), (56,184), (64,65), (64,66), (64,68), (64,80), (72,73), (72,74), (72,76), (72,88), (72,200), (96,97), (96,98), (96,100), (96,112), (96,224), (104,105), (104,106), (104,108), (104,120), (104,232), (128,130), (128,132), (128,136), (128,144), (128,160), (129,131), (129,133), (129,137), (129,145), (129,161), (129,193), (192,193), (192,194), (192,196), (192,200), (192,208), (192,224)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3ffffffffffffffffffffffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_255.map (· &&& dom_255)
def goalM : Nat := goal_255 &&& dom_255
def NN : Nat → Nat
|12=>1
|_=>0
def HT : Nat → Nat → Nat
|12,0=>0xd511d
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0xfac688
|_=>0
def stOffB : Nat → Nat → Nat
|12,0=>8
|_,_=>0
def dictMask : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def wireSAt (i : Nat) : Nat := if i < 8 then (dictB (i / 512) (i / 32 % 16) >>> (256 * (i % 32))) &&& dictMask else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 3 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 8 (j % 64)
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
|0=>0x3f80
|_=>0
def pmB : Nat → Nat → Nat
|12,0=>1
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 1 (j % 128); fld (pmPalB (k / 32)) 7 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_254,11,runOps true dom_254 (0,roots_254) ops)] else [])++(if pm.testBit 1 then [(dom_191,11,runOps true dom_191 (0,roots_191) ops)] else [])++(if pm.testBit 2 then [(dom_253,11,runOps true dom_253 (0,roots_253) ops)] else [])++(if pm.testBit 3 then [(dom_251,11,runOps true dom_251 (0,roots_251) ops)] else [])++(if pm.testBit 4 then [(dom_247,11,runOps true dom_247 (0,roots_247) ops)] else [])++(if pm.testBit 5 then [(dom_239,11,runOps true dom_239 (0,roots_239) ops)] else [])++(if pm.testBit 6 then [(dom_223,11,runOps true dom_223 (0,roots_223) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_255 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · exact cpcs (by decide +kernel) lowS_223 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_254 11 s (0, roots_254) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_255 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_254 h

def symsG : List (List (Nat × Nat)) := [[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_255 == dom_255) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_255 goalM v ys) : RunD true dom_255 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_255 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
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
private theorem z10 : ∀ i, 0 ≤ i → i < 0 → Z 10 i = true := by omega
private theorem z11 : ∀ i, 0 ≤ i → i < 0 → Z 11 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z12 : ∀ i, 0 ≤ i → i < 1 → Z 12 i = true := span_ok (by decide +kernel : span (Z 12) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 12) : ∀ i < NN s, bar true dom_255 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
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
  · exact z11 i (Nat.zero_le i) hi
  · exact z12 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_255 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 6 7 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 12) (h : RunD true dom_255 goalM s xsM) : False := by
  have hmin : 7 ≤ s := by
    have hl := run_len h; change 8 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_255 roots_255 goal_255 13 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_255

theorem lowS_255 : Lower true dom_255 roots_255 goal_255 13 := S_255.noCircuit

theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
    (hhas : ∃ g ∈ gates, isNotGate g = true) : 14 ≤ gates.length := by
  obtain ⟨g, hg, hgn⟩ := hhas
  have hout : (execN gates xs256).getD o 0 &&& mask256 = goal_255 &&& mask256 := by
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
  have hL := lowS_255 p bank hr (avail_of_eq hout hav_out)
  have hlt := countP_not_lt hg hgn
  omega

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [8, 4] }, { op := GateOp.or, inputs := [6, 7] }, { op := GateOp.and, inputs := [9, 10] }, { op := GateOp.or, inputs := [0, 7] }, { op := GateOp.or, inputs := [3, 5] }, { op := GateOp.and, inputs := [12, 13] }, { op := GateOp.and, inputs := [0, 6] }, { op := GateOp.and, inputs := [1, 4] }, { op := GateOp.and, inputs := [2, 5] }, { op := GateOp.or, inputs := [11, 14] }, { op := GateOp.or, inputs := [18, 15] }, { op := GateOp.or, inputs := [19, 16] }, { op := GateOp.or, inputs := [20, 17] }]

theorem wit_mono : ∀ g ∈ witGates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def b2n (b : Bool) : Nat := if b then 1 else 0
theorem b2n_le (b : Bool) : b2n b ≤ 1 := by cases b <;> decide
theorem b2n_testBit0 (b : Bool) : (b2n b).testBit 0 = b := by cases b <;> rfl
theorem testBit0_b2n_add (b : Bool) (m : Nat) : (b2n b + 2 * m).testBit 0 = b := by
  cases b <;> simp [b2n, Nat.testBit_zero]
theorem testBit_succ_b2n_add (b : Bool) (m k : Nat) : (b2n b + 2 * m).testBit (k + 1) = m.testBit k := by
  cases b <;> simp [b2n, Nat.testBit_succ]
  have : (1 + 2 * m) / 2 = m := by omega
  rw [this]

def natOfBits8 (x : Fin 8 → Bool) : Nat :=
  b2n (x 0) + 2 * (b2n (x 1) + 2 * (b2n (x 2) + 2 * (b2n (x 3) + 2 * (b2n (x 4) + 2 * (b2n (x 5) + 2 * (b2n (x 6) + 2 * b2n (x 7)))))))

theorem natOfBits8_lt (x : Fin 8 → Bool) : natOfBits8 x < 256 := by
  have h0 := b2n_le (x 0); have h1 := b2n_le (x 1); have h2 := b2n_le (x 2); have h3 := b2n_le (x 3)
  have h4 := b2n_le (x 4); have h5 := b2n_le (x 5); have h6 := b2n_le (x 6); have h7 := b2n_le (x 7)
  unfold natOfBits8; omega

theorem pt8_natOfBits8 (x : Fin 8 → Bool) : pt8 (natOfBits8 x) = x := by
  funext i
  fin_cases i <;> simp only [pt8, natOfBits8, testBit0_b2n_add, testBit_succ_b2n_add, b2n_testBit0] <;> rfl

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 21⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
  have hwit : (execN witGates xs256).getD 21 0 &&& mask256 = goal_255 &&& mask256 := by decide +kernel
  intro x
  have hlt : natOfBits8 x < 256 := natOfBits8_lt x
  have hpt : pt8 (natOfBits8 x) = x := pt8_natOfBits8 x
  generalize hr : natOfBits8 x = r at hlt hpt
  have h1 := execN_bit witGates xs256 r hlt (fun g hg => by
    have hm := wit_mono g hg
    rcases hm.1 with h | h <;> simp [h])
  have h2 := congrArg (fun l => l.getD 21 false) h1
  rw [xs256_bits ⟨r, hlt⟩, hpt] at h2
  have hgd : ((execN witGates xs256).map (·.testBit r)).getD 21 false =
      ((execN witGates xs256).getD 21 0).testBit r := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases (execN witGates xs256)[21]? with | none => simp | some v => rfl
  rw [hgd] at h2
  have hbit : ((execN witGates xs256).getD 21 0).testBit r = goal_255.testBit r := by
    have hb := congrArg (fun v => v.testBit r) hwit
    simp only [Nat.testBit_and, mask256_bit, hlt, decide_true, Bool.and_true] at hb
    exact hb
  have hres := h2.symm.trans (hbit.trans (goal_eq_f ⟨r, hlt⟩))
  rw [hpt] at hres
  exact hres

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o hfan _h1not hev
  by_cases hhas : ∃ g ∈ gates, isNotGate g = true
  · have hfan' : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      obtain ⟨h1, h2⟩ := hfan g hg
      refine ⟨?_, h2⟩
      rcases h1 with h1 | h1 | h1 <;> simp [h1]
    have hlb : 14 ≤ gates.length := lb_with_not gates o hfan' hev hhas
    refine ⟨witGates, 21, wit_mono, ?_, wit_eval⟩
    have hlen : witGates.length = 14 := rfl
    omega
  · push Not at hhas
    refine ⟨gates, o, ?_, le_rfl, hev⟩
    intro g hg
    obtain ⟨h1, h2⟩ := hfan g hg
    refine ⟨?_, h2⟩
    rcases h1 with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exfalso; have := hhas g hg; simp [isNotGate, h1] at this

end PEqualNP.Outside.L_meta_32798_aux

theorem PEqualNP.Outside.L_meta_32798 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_32798_aux.main
