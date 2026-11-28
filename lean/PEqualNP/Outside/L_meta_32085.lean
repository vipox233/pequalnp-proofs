import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_32085_aux
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
  · push_neg at hhas
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
def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def roots_255 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_255 : Nat := 0xfffffffffffffffeffffffffffffffeefffffffefffffefcffeeffaaeeccaa00
def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_251 : Nat := 0xf0f0f0f0f0f0f0e0f0f0f0f0f0f0f0e0f0f0f0e0f0f0e0c0f0e0f0a0e0c0a00
def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_187 : Nat := 0xf0f0f0f0f0f0f0e00000000000000000f0e0f0a0e0c0a00
def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_186 : Nat := 0x50505050505050400000000000000000504050004040000
def dom_184 : Nat := 0x10101010101010100000000000000000101010101010101
def roots_184 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_184 : Nat := 0x10101010101010000000000000000000100010000000000
def dom_168 : Nat := 0x1010000010100000000000000000000010100000101
def roots_168 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_168 : Nat := 0x1010000010000000000000000000000010000000000
def dom_178 : Nat := 0x500050005000500000000000000000005000500050005
def roots_178 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_178 : Nat := 0x500050005000400000000000000000004000000040000
def dom_146 : Nat := 0x5000500000000000000000000000000050005
def roots_146 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]
def goal_146 : Nat := 0x5000400000000000000000000000000040000
def dom_170 : Nat := 0x5050000050500000000000000000000050500000505
def roots_170 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_170 : Nat := 0x5050000050400000000000000000000050000000000
def dom_154 : Nat := 0x505050500000000000000000000000005050505
def roots_154 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]
def goal_154 : Nat := 0x505050400000000000000000000000004040000
def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_185 : Nat := 0x30303030303030200000000000000000302030202000200
def dom_169 : Nat := 0x3030000030300000000000000000000030300000303
def roots_169 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_169 : Nat := 0x3030000030200000000000000000000030200000200
def dom_161 : Nat := 0x30000000300000000000000000000000300000003
def roots_161 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_161 : Nat := 0x30000000200000000000000000000000200000000
def dom_137 : Nat := 0x30300000000000000000000000000000303
def roots_137 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 7 0]
def goal_137 : Nat := 0x30200000000000000000000000000000200
def dom_41 : Nat := 0x30300000303
def roots_41 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0]
def goal_41 : Nat := 0x30200000200
def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_179 : Nat := 0xf000f000f000e0000000000000000000e000a000c0000
def dom_177 : Nat := 0x300030003000300000000000000000003000300030003
def roots_177 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_177 : Nat := 0x300030003000200000000000000000002000200000000
def dom_163 : Nat := 0xf0000000f00000000000000000000000f0000000f
def roots_163 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_163 : Nat := 0xf0000000e00000000000000000000000a00000000
def dom_147 : Nat := 0xf000f000000000000000000000000000f000f
def roots_147 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]
def goal_147 : Nat := 0xf000e000000000000000000000000000c0000
def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_171 : Nat := 0xf0f00000f0e000000000000000000000f0a00000a00
def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]
def goal_155 : Nat := 0xf0f0f0e0000000000000000000000000e0c0a00
def dom_153 : Nat := 0x303030300000000000000000000000003030303
def roots_153 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]
def goal_153 : Nat := 0x303030200000000000000000000000002000200
def dom_139 : Nat := 0xf0f00000000000000000000000000000f0f
def roots_139 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 7 0]
def goal_139 : Nat := 0xf0e00000000000000000000000000000a00
def goal_185_l144 : Nat := 0x30303030303030300000000000000000303030203030200
def goal_169_l128 : Nat := 0x3030000030300000000000000000000030200000200
def dzo_185_2 : Nat := 0xc0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0c
def gzo_185_2_144 : Nat := 0xc0c0c0c0c0c0c0c00000000000000000c0c0c080c0c0800
def goal_171_l130 : Nat := 0xf0f00000f0f000000000000000000000f0e00000e0c
def dzo_171_16 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f0000
def gzo_171_16_130 : Nat := 0xf0f00000f0f000000000000000000000f0e00000e0c0000
def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]
def goal_59 : Nat := 0xf0e0f0a0e0c0a00
def dom_57 : Nat := 0x303030303030303
def roots_57 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]
def goal_57_l16 : Nat := 0x303030203030200
def dzo_57_2 : Nat := 0xc0c0c0c0c0c0c0c
def gzo_57_2_16 : Nat := 0xc0c0c080c0c0800

namespace S_168
def pairsG : List (Nat × Nat) := [(8,40), (8,136), (32,40), (32,160), (128,136), (128,160)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_168.map (· &&& dom_168)
def goalM : Nat := goal_168 &&& dom_168
def NN : Nat → Nat
|2=>0x1
|3=>0x1
|_=>0
def HT : Nat → Nat → Nat
|2,0=>0xa17dd
|3,0=>0xa17dd
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x4040000040400000000000000000000000000000002020000000000000000000000000000020200000001000000010000000000000000000000010000000100
|_,_=>0
def stPool : Nat → Nat
|0=>0x924
|_=>0
def stOffB : Nat → Nat → Nat
|2,0=>0x3
|3,0=>0x33
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 3 then fld (dictB (i / 512) (i / 32 % 16)) 169 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 2 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 6 (j % 64)
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

def mkPools (_ _ : Nat) : List (Nat × Nat × (Nat × List Nat)) := []
def mkCut (_ _ : Nat) (_ : Nat × Nat × Nat) (_ : List Nat) : Bool := false
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_168 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_168 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0xffffffff00000000ffffffff00000000, 96)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120)], [(0xff00ff00ff00ff00ff00ff00ff00ff00, 120), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xff00ff00ff00ff00ff00ff00ff00ff00, 120)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_168 == dom_168) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_168 goalM v ys) : RunD true dom_168 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_168 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_168 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_168 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_168 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_168 roots_168 goal_168 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_168

theorem low_168 : Lower true dom_168 roots_168 goal_168 4 := S_168.noCircuit

theorem low_184 : Lower true dom_184 roots_184 goal_184 5 :=
  lower_slice (d:=dom_184) (dSub:=dom_168) (T:=goal_184) (TSub:=goal_168) (roots:=roots_184) (rootsSub:=roots_168)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x10100000101000000000000000000000101000001010000, 128, 144)] (by decide +kernel) (by decide +kernel) low_168

namespace S_146
def pairsG : List (Nat × Nat) := [(2,18), (2,130), (16,18), (16,144), (128,130), (128,144)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_146.map (· &&& dom_146)
def goalM : Nat := goal_146 &&& dom_146
def NN : Nat → Nat
|2=>0x1
|3=>0x1
|_=>0
def HT : Nat → Nat → Nat
|2,0=>0x1c470
|3,0=>0x1c470
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x140014000000000000000000000000000000028000000000000000000000000000000280004000400000000000000000000000000040004
|_,_=>0
def stPool : Nat → Nat
|0=>0x924
|_=>0
def stOffB : Nat → Nat → Nat
|2,0=>0x3
|3,0=>0x33
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 3 then fld (dictB (i / 512) (i / 32 % 16)) 147 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 2 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 6 (j % 64)
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

def mkPools (_ _ : Nat) : List (Nat × Nat × (Nat × List Nat)) := []
def mkCut (_ _ : Nat) (_ : Nat × Nat × Nat) (_ : List Nat) : Bool := false
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_146 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_146 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0xffff0000ffff0000ffff0000ffff0000, 112)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xcccccccccccccccccccccccccccccccc, 126)], [(0xcccccccccccccccccccccccccccccccc, 126), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccccccccccccccccccccccccccccccc, 126)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_146 == dom_146) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_146 goalM v ys) : RunD true dom_146 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_146 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_146 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_146 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_146 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_146 roots_146 goal_146 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_146

theorem low_146 : Lower true dom_146 roots_146 goal_146 4 := S_146.noCircuit

theorem low_178 : Lower true dom_178 roots_178 goal_178 5 :=
  lower_slice (d:=dom_178) (dSub:=dom_146) (T:=goal_178) (TSub:=goal_146) (roots:=roots_178) (rootsSub:=roots_146)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x500050000000000000000000000000005000500000000, 128, 160)] (by decide +kernel) (by decide +kernel) low_146

theorem low_170 : Lower true dom_170 roots_170 goal_170 5 :=
  lower_slice (d:=dom_170) (dSub:=dom_168) (T:=goal_170) (TSub:=goal_168) (roots:=roots_170) (rootsSub:=roots_168)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x4040000040400000000000000000000040400000404, 128, 130)] (by decide +kernel) (by decide +kernel) low_168

theorem low_154 : Lower true dom_154 roots_154 goal_154 5 :=
  lower_slice (d:=dom_154) (dSub:=dom_146) (T:=goal_154) (TSub:=goal_146) (roots:=roots_154) (rootsSub:=roots_146)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x500050000000000000000000000000005000500, 128, 136)] (by decide +kernel) (by decide +kernel) low_146

namespace S_186
def pairsG : List (Nat × Nat) := [(2,18), (2,130), (8,40), (8,136), (10,26), (10,42), (10,138), (16,18), (16,144), (24,26), (24,56), (24,152), (32,40), (32,160), (34,42), (34,50), (34,162), (48,50), (48,56), (48,176), (128,130), (128,136), (128,144), (128,160)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_186.map (· &&& dom_186)
def goalM : Nat := goal_186 &&& dom_186
def NN : Nat → Nat
|3=>0x1
|4=>0x4
|5=>0xa
|6=>0x4
|7=>0x1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0x31788
|4,0=>0x25d551c18c0ee180bc15
|5,0=>0x481f52ee801c65b198281588e12bc4066ab05e6d027af0243e
|6,0=>0x54d664de4722d7509523
|7,0=>0x54d66
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x5000500050005000000000000000000000000000000000000a0a00000a0a00000000000000000000080800000809414141414140000000000000000000014141414141400028282828282800000000000000000000000000000000000000000005050505000000000000000000000000000000000020002000200020000000000000000000000000000000141414141414141400000000000000001414000014140000808080808080808000000000000000008080000080800000000000000000000000000000000000504050405040504a0a0a000a0a0a0000000000000000000a0a0a000a0a0a01414141414141414000000000000000014141400141414000002828000028280000000000000000000000000000000505050500000505000000000000000005050505000000000000a0a00000a0a000000000000000000000a0a00000001414141410101010000000000000000000000000000000028282828282828280000000000000000202020202020202500050005000500000000000000000005000500050005002020000020202020000000000000000020200000202000141414140000000000000000000000001414141400000002828282828282828000000000000000000000000000000000500050005000500000000000000000005000500040004a0a00000a0a000000000000000000000a0a00000a0a000101010101010101000000000000000001010101010101012828282828282828000000000000000028282828000000050505050504050400000000000000000500050005000500
|_,_=>0
def stPool : Nat → Nat
|0=>0x14c3408a61a045408c3b0d0229823308a8c190515d0230cb53090f2c8681143430d022ccc828e5130d022c0c240cae408a3330482986b188c5020665250530ce3118a418820
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>0x4
|4,0=>0x26a3944a845
|5,0=>0x272c8684cf19b330654c918f3186
|6,0=>0xcab7dacb536
|7,0=>0x6a5
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 25 then fld (dictB (i / 512) (i / 32 % 16)) 187 (i % 32) else 0
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
|0=>0x30d2992a32d830d28d40d09b29990b28d2bd40d33528f
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0xa28262004200220200
|6,0=>0xf0e1d1c1
|7,0=>0xf0
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 12 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 31), wireSAt ((code >>> 7) &&& 31)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 8 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmB : Nat → Nat → Nat
|5,0=>0x3c4a8005030800
|6,0=>0x3ffb6f
|7,0=>0x3b
|_,_=>0
def PM (s j : Nat) : Nat := fld (pmB s (j / 128)) 6 (j % 128)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_184,5,runOps true dom_184 (0,roots_184) ops)] else [])++(if pm.testBit 1 then [(dom_178,5,runOps true dom_178 (0,roots_178) ops)] else [])++(if pm.testBit 2 then [(dom_170,5,runOps true dom_170 (0,roots_170) ops)] else [])++(if pm.testBit 3 then [(dom_154,5,runOps true dom_154 (0,roots_154) ops)] else [])++(if pm.testBit 4 then [(dom_168,4,runOps true dom_168 (0,roots_168) ops)] else [])++(if pm.testBit 5 then [(dom_146,4,runOps true dom_146 (0,roots_146) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_186 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_184 _ g hchk
    · exact cpcs (by decide +kernel) low_178 _ g hchk
    · exact cpcs (by decide +kernel) low_170 _ g hchk
    · exact cpcs (by decide +kernel) low_154 _ g hchk
    · exact cpcs (by decide +kernel) low_168 _ g hchk
    · exact cpcs (by decide +kernel) low_146 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_184 5 s (0, roots_184) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_186 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_184 h

def symsG : List (List (Nat × Nat)) := [[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_186 == dom_186) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_186 goalM v ys) : RunD true dom_186 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_186 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 7) : ∀ i < NN s, bar true dom_186 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
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
  scr true dom_186 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD true dom_186 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_186 roots_186 goal_186 8 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_186

theorem low_186 : Lower true dom_186 roots_186 goal_186 8 := S_186.noCircuit

namespace S_161
def pairsG : List (Nat × Nat) := [(1,33), (1,129), (32,33), (32,160), (128,129), (128,160)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_161.map (· &&& dom_161)
def goalM : Nat := goal_161 &&& dom_161
def NN : Nat → Nat
|2=>0x1
|3=>0x1
|_=>0
def HT : Nat → Nat → Nat
|2,0=>0xed650
|3,0=>0xed650
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x30000000300000000000000000000000000000000c0000000000000000000000000000000c000000020000000200000000000000000000000200000002
|_,_=>0
def stPool : Nat → Nat
|0=>0x924
|_=>0
def stOffB : Nat → Nat → Nat
|2,0=>0x3
|3,0=>0x33
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 3 then fld (dictB (i / 512) (i / 32 % 16)) 162 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 2 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 6 (j % 64)
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

def mkPools (_ _ : Nat) : List (Nat × Nat × (Nat × List Nat)) := []
def mkCut (_ _ : Nat) (_ : Nat × Nat × Nat) (_ : List Nat) : Bool := false
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_161 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_161 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0xffffffff00000000ffffffff00000000, 96)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_161 == dom_161) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_161 goalM v ys) : RunD true dom_161 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_161 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_161 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_161 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_161 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_161 roots_161 goal_161 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_161

theorem low_161 : Lower true dom_161 roots_161 goal_161 4 := S_161.noCircuit

namespace S_137
def pairsG : List (Nat × Nat) := [(1,9), (1,129), (8,9), (8,136), (128,129), (128,136)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_137.map (· &&& dom_137)
def goalM : Nat := goal_137 &&& dom_137
def NN : Nat → Nat
|2=>0x1
|3=>0x1
|_=>0
def HT : Nat → Nat → Nat
|2,0=>0x965fd
|3,0=>0x965fd
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x30300000000000000000000000000000000c0000000000000000000000000000000c020200000000000000000000000000000202
|_,_=>0
def stPool : Nat → Nat
|0=>0x924
|_=>0
def stOffB : Nat → Nat → Nat
|2,0=>0x3
|3,0=>0x33
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 3 then fld (dictB (i / 512) (i / 32 % 16)) 138 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 2 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 6 (j % 64)
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

def mkPools (_ _ : Nat) : List (Nat × Nat × (Nat × List Nat)) := []
def mkCut (_ _ : Nat) (_ : Nat × Nat × Nat) (_ : List Nat) : Bool := false
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_137 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_137 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0xff00ff00ff00ff00ff00ff00ff00ff00, 120)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_137 == dom_137) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_137 goalM v ys) : RunD true dom_137 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_137 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_137 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_137 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_137 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_137 roots_137 goal_137 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_137

theorem low_137 : Lower true dom_137 roots_137 goal_137 4 := S_137.noCircuit

namespace S_41
def pairsG : List (Nat × Nat) := [(1,9), (1,33), (8,9), (8,40), (32,33), (32,40)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_41.map (· &&& dom_41)
def goalM : Nat := goal_41 &&& dom_41
def NN : Nat → Nat
|2=>0x1
|3=>0x1
|_=>0
def HT : Nat → Nat → Nat
|2,0=>0xbcb
|3,0=>0xbcb
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x30300000000c0000000c020200000202
|_,_=>0
def stPool : Nat → Nat
|0=>0x924
|_=>0
def stOffB : Nat → Nat → Nat
|2,0=>0x3
|3,0=>0x33
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 3 then fld (dictB (i / 512) (i / 32 % 16)) 42 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 2 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 6 (j % 64)
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

def mkPools (_ _ : Nat) : List (Nat × Nat × (Nat × List Nat)) := []
def mkCut (_ _ : Nat) (_ : Nat × Nat × Nat) (_ : List Nat) : Bool := false
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_41 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_41 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_41 == dom_41) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_41 goalM v ys) : RunD true dom_41 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_41 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_41 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_41 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_41 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_41 roots_41 goal_41 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_41

theorem low_41 : Lower true dom_41 roots_41 goal_41 4 := S_41.noCircuit

namespace S_169
def pairsG : List (Nat × Nat) := [(1,9), (1,33), (1,129), (8,9), (8,40), (8,136), (32,33), (32,40), (32,160), (128,129), (128,136), (128,160)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_169.map (· &&& dom_169)
def goalM : Nat := goal_169 &&& dom_169
def NN : Nat → Nat
|3=>0x3
|4=>0x3
|5=>0x2
|6=>0x1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0x9c2c63901d21fd5
|4,0=>0x1d4141410202b7e
|5,0=>0xde1e401733
|6,0=>0xde1e4
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x30200000000000000000000000000000302c0c00000c08000000000000000000000c0c00000c09010000010100000000000000000000010100000100c0c00000c0c00000000000000000000000000000003030000020200000000000000000000030300000202c0c00000c00000000000000000000000c0c00000c03020000030200000000000000000000030200000302c0000000c00000000000000000000000c0000000c02020000020200000000000000000000020200000202c0c00000000000000000000000000000c0c00000003030000030200000000000000000000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x7132713271324726357321a73219137876543210
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>0x8411004
|4,0=>0x165454c5
|5,0=>0x811b5
|6,0=>0x244
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 11 then fld (dictB (i / 512) (i / 32 % 16)) 170 (i % 32) else 0
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
|0=>0x324c5214c931485
|_=>0
def opOffB : Nat → Nat → Nat
|3,0=>0x180
|4,0=>0xc8000
|5,0=>0x3051
|6,0=>0x60
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 10 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 15), wireSAt ((code >>> 6) &&& 15)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 7 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmB : Nat → Nat → Nat
|3,0=>0x30
|4,0=>0x300
|5,0=>0x7f
|6,0=>0xf
|_,_=>0
def PM (s j : Nat) : Nat := fld (pmB s (j / 128)) 4 (j % 128)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_168,4,runOps true dom_168 (0,roots_168) ops)] else [])++(if pm.testBit 1 then [(dom_161,4,runOps true dom_161 (0,roots_161) ops)] else [])++(if pm.testBit 2 then [(dom_137,4,runOps true dom_137 (0,roots_137) ops)] else [])++(if pm.testBit 3 then [(dom_41,4,runOps true dom_41 (0,roots_41) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_169 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_168 _ g hchk
    · exact cpcs (by decide +kernel) low_161 _ g hchk
    · exact cpcs (by decide +kernel) low_137 _ g hchk
    · exact cpcs (by decide +kernel) low_41 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_168 4 s (0, roots_168) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_169 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_168 h

def symsG : List (List (Nat × Nat)) := [[(0xffffffff00000000ffffffff00000000, 96)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120)], [(0xff00ff00ff00ff00ff00ff00ff00ff00, 120), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xff00ff00ff00ff00ff00ff00ff00ff00, 120)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xffffffff00000000ffffffff00000000, 96)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_169 == dom_169) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_169 goalM v ys) : RunD true dom_169 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_169 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 3 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 2 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, bar true dom_169 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_169 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 3 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_169 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_169 roots_169 goal_169 7 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_169

theorem low_169 : Lower true dom_169 roots_169 goal_169 7 := S_169.noCircuit

theorem low_185 : Lower true dom_185 roots_185 goal_185 8 :=
  lower_slice (d:=dom_185) (dSub:=dom_169) (T:=goal_185) (TSub:=goal_169) (roots:=roots_185) (rootsSub:=roots_169)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x30300000303000000000000000000000303000003030000, 128, 144)] (by decide +kernel) (by decide +kernel) low_169

theorem low_177 : Lower true dom_177 roots_177 goal_177 5 :=
  lower_slice (d:=dom_177) (dSub:=dom_161) (T:=goal_177) (TSub:=goal_161) (roots:=roots_177) (rootsSub:=roots_161)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x300000003000000000000000000000003000000030000, 128, 144)] (by decide +kernel) (by decide +kernel) low_161

theorem low_163 : Lower true dom_163 roots_163 goal_163 5 :=
  lower_slice (d:=dom_163) (dSub:=dom_161) (T:=goal_163) (TSub:=goal_161) (roots:=roots_163) (rootsSub:=roots_161)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0000000c00000000000000000000000c0000000c, 128, 130)] (by decide +kernel) (by decide +kernel) low_161

theorem low_147 : Lower true dom_147 roots_147 goal_147 5 :=
  lower_slice (d:=dom_147) (dSub:=dom_146) (T:=goal_147) (TSub:=goal_146) (roots:=roots_147) (rootsSub:=roots_146)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa000a000000000000000000000000000a000a, 128, 129)] (by decide +kernel) (by decide +kernel) low_146

namespace S_179
def pairsG : List (Nat × Nat) := [(1,33), (1,129), (2,18), (2,130), (3,19), (3,35), (3,131), (16,18), (16,144), (17,19), (17,49), (17,145), (32,33), (32,160), (34,35), (34,50), (34,162), (48,49), (48,50), (48,176), (128,129), (128,130), (128,144), (128,160)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_179.map (· &&& dom_179)
def goalM : Nat := goal_179 &&& dom_179
def NN : Nat → Nat
|3=>0x1
|4=>0x4
|5=>0xa
|6=>0x4
|7=>0x1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0x14762
|4,0=>0x2b6e91b71918c150ecff
|5,0=>0x789e365aae586183448d33c2425b1f227e21cf300fa5c07b37
|6,0=>0x7c7134d5051d4371933c
|7,0=>0x1d437
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf000a000f000a0000000000000000000f000a000f000a30003000300030000000000000000000200020002000200000000000000000000000000000000f000a000f000af000f000c000c0000000000000000000f000f000c000cf000f000c000c00000000000000000000000000000000f000f000f00000000000000000000000f000f000f0000f000f000f000f0000000000000000000f000f000f00000000f0000000f00000000000000000000000c0000000c000000000000f00000000000000000000000000000000e000e000e000e0000000000000000000e000e000e000ef000f000f000f0000000000000000000f0000000f00003000300030003000000000000000000030000000300000000f0000000f00000000000000000000000000000000a000f000a000f0000000000000000000a000a000a000af000f000f000c0000000000000000000c000c000c000cf000f000f000000000000000000000000000000000000f000f000f000f0000000000000000000f000f00000000c000c000c000c0000000000000000000c000c000c000c00000000f000f000000000000000000000000000e000ef000f000f000f00000000000000000000000000000000f0000000f00000000000000000000000f0000000f0000300000003000300000000000000000003000000030000a000a000a000a0000000000000000000a000a000a000af000f000000000000000000000000000f000f00000000f000f000f000f0000000000000000000c000c000c000cf000f000f000c0000000000000000000f0000000f0000
|_,_=>0
def stPool : Nat → Nat
|0=>0x184540d02198ad28866404c22a066120a3c88a61a30241466b946241aa8188a69886644903114d1408667b4a21c0c110cc57b9023146c1944658d05524a3418e3308a418820
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>0x4
|4,0=>0x26a3944a845
|5,0=>0x26b47682ced9b2b0654c918f3186
|6,0=>0xc8d79acad36
|7,0=>0x6a5
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 26 then fld (dictB (i / 512) (i / 32 % 16)) 180 (i % 32) else 0
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
|0=>0x31732128d3581213511157973153211a17a33151b5317
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0xa282000062422202
|6,0=>0xe1d1d0c1
|7,0=>0xf0
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 12 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 31), wireSAt ((code >>> 7) &&& 31)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 8 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmB : Nat → Nat → Nat
|5,0=>0xeb0000921190
|6,0=>0xbeb3fc
|7,0=>0x37
|_,_=>0
def PM (s j : Nat) : Nat := fld (pmB s (j / 128)) 6 (j % 128)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_178,5,runOps true dom_178 (0,roots_178) ops)] else [])++(if pm.testBit 1 then [(dom_177,5,runOps true dom_177 (0,roots_177) ops)] else [])++(if pm.testBit 2 then [(dom_163,5,runOps true dom_163 (0,roots_163) ops)] else [])++(if pm.testBit 3 then [(dom_147,5,runOps true dom_147 (0,roots_147) ops)] else [])++(if pm.testBit 4 then [(dom_146,4,runOps true dom_146 (0,roots_146) ops)] else [])++(if pm.testBit 5 then [(dom_161,4,runOps true dom_161 (0,roots_161) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_179 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_178 _ g hchk
    · exact cpcs (by decide +kernel) low_177 _ g hchk
    · exact cpcs (by decide +kernel) low_163 _ g hchk
    · exact cpcs (by decide +kernel) low_147 _ g hchk
    · exact cpcs (by decide +kernel) low_146 _ g hchk
    · exact cpcs (by decide +kernel) low_161 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_178 5 s (0, roots_178) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_179 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_178 h

def symsG : List (List (Nat × Nat)) := [[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_179 == dom_179) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_179 goalM v ys) : RunD true dom_179 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_179 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
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

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
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

theorem low_179 : Lower true dom_179 roots_179 goal_179 8 := S_179.noCircuit

theorem low_171 : Lower true dom_171 roots_171 goal_171 8 :=
  lower_slice (d:=dom_171) (dSub:=dom_169) (T:=goal_171) (TSub:=goal_169) (roots:=roots_171) (rootsSub:=roots_169)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c00000c0c000000000000000000000c0c00000c0c, 128, 130)] (by decide +kernel) (by decide +kernel) low_169

theorem low_153 : Lower true dom_153 roots_153 goal_153 5 :=
  lower_slice (d:=dom_153) (dSub:=dom_137) (T:=goal_153) (TSub:=goal_137) (roots:=roots_153) (rootsSub:=roots_137)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x303000000000000000000000000000003030000, 128, 144)] (by decide +kernel) (by decide +kernel) low_137

theorem low_139 : Lower true dom_139 roots_139 goal_139 5 :=
  lower_slice (d:=dom_139) (dSub:=dom_137) (T:=goal_139) (TSub:=goal_137) (roots:=roots_139) (rootsSub:=roots_137)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c00000000000000000000000000000c0c, 128, 130)] (by decide +kernel) (by decide +kernel) low_137

namespace S_155
def pairsG : List (Nat × Nat) := [(1,9), (1,129), (2,18), (2,130), (3,11), (3,19), (3,131), (8,9), (8,136), (10,11), (10,26), (10,138), (16,18), (16,144), (17,19), (17,25), (17,145), (24,25), (24,26), (24,152), (128,129), (128,130), (128,136), (128,144)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_155.map (· &&& dom_155)
def goalM : Nat := goal_155 &&& dom_155
def NN : Nat → Nat
|3=>0x1
|4=>0x4
|5=>0xa
|6=>0x4
|7=>0x1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0x4cbc
|4,0=>0x1e56d1e01d0cf51039b1
|5,0=>0x3d5ae3342d2f5a3289052564214a5a14499089fa073fd05a61
|6,0=>0xb131518ef0066db019f3
|7,0=>0xb1315
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x303030300000000000000000000000000000000f0f0f0f0000000000000000000000000f000f00000050500000000000000000000000000000000f0f0f0f0000000000000000000000000c0c0c0c0000f0f00000000000000000000000000000c0c00f000f000000000000000000000000000c000c30303030000000000000000000000000303000000000000000000000000000000000000f0f0f0000f000f00000000000000000000000000000000c0f0c0f0000000000000000000000000c0c0c0cf0f0f000000000000000000000000000f0f0f00e0e0e0e0000000000000000000000000e0e0e0ef0f0f0f0000000000000000000000000e0e0e0ef0f0a0a0000000000000000000000000f0f0a0af0f0e0e0000000000000000000000000f0f0000303030300000000000000000000000003030202f0f0f0f000000000000000000000000000000000000c0f00000000000000000000000000000c0ca0a0a0a0000000000000000000000000a0a0a0af000f000000000000000000000000000f000f00f0f0f0000000000000000000000000000000000f0f0f0f0000000000000000000000000f0f0000c0c0c0c0000000000000000000000000c0c0c0cf0f00000000000000000000000000000f0f0000f0f0f0f0000000000000000000000000a0a0a0af0f0f0a0000000000000000000000000f000f00
|_,_=>0
def stPool : Nat → Nat
|0=>0x244619d2230ce611d23c984748ec911867708e34e223308e9b98e91daa712466a18e914c671193211d261c06711925118674b4661312131c69598e24a8e930d07198a418820
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>0x4
|4,0=>0x26a3944a845
|5,0=>0x26b47682ced9b2b0654c918f3186
|6,0=>0xcab7dacb536
|7,0=>0x6a5
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 26 then fld (dictB (i / 512) (i / 32 % 16)) 156 (i % 32) else 0
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
|0=>0x48f48d19dc1b499b0b48d1c549b4bc1194b919d49d11d
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0xa2008200000062422202
|6,0=>0xf0e1d1c1
|7,0=>0xf0
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 12 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 31), wireSAt ((code >>> 7) &&& 31)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 8 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmB : Nat → Nat → Nat
|5,0=>0x50028000083cc18
|6,0=>0x3ef9fc
|7,0=>0x3b
|_,_=>0
def PM (s j : Nat) : Nat := fld (pmB s (j / 128)) 6 (j % 128)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_154,5,runOps true dom_154 (0,roots_154) ops)] else [])++(if pm.testBit 1 then [(dom_153,5,runOps true dom_153 (0,roots_153) ops)] else [])++(if pm.testBit 2 then [(dom_147,5,runOps true dom_147 (0,roots_147) ops)] else [])++(if pm.testBit 3 then [(dom_139,5,runOps true dom_139 (0,roots_139) ops)] else [])++(if pm.testBit 4 then [(dom_146,4,runOps true dom_146 (0,roots_146) ops)] else [])++(if pm.testBit 5 then [(dom_137,4,runOps true dom_137 (0,roots_137) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_155 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_154 _ g hchk
    · exact cpcs (by decide +kernel) low_153 _ g hchk
    · exact cpcs (by decide +kernel) low_147 _ g hchk
    · exact cpcs (by decide +kernel) low_139 _ g hchk
    · exact cpcs (by decide +kernel) low_146 _ g hchk
    · exact cpcs (by decide +kernel) low_137 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_154 5 s (0, roots_154) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_155 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_154 h

def symsG : List (List (Nat × Nat)) := [[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_155 == dom_155) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_155 goalM v ys) : RunD true dom_155 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_155 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 7) : ∀ i < NN s, bar true dom_155 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
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
  scr true dom_155 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD true dom_155 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_155 roots_155 goal_155 8 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_155

theorem low_155 : Lower true dom_155 roots_155 goal_155 8 := S_155.noCircuit

theorem low_169_l128 : Lower true dom_169 roots_169 goal_169_l128 5 :=
  lower_slice (d:=dom_169) (dSub:=dom_41) (T:=goal_169_l128) (TSub:=goal_41) (roots:=roots_169) (rootsSub:=roots_41)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x3030000030300000000000000000000000000000000, 0, 128)] (by decide +kernel) (by decide +kernel) low_41

theorem low_185_l144 : Lower true dom_185 roots_185 goal_185_l144 6 :=
  lower_slice (d:=dom_185) (dSub:=dom_169) (T:=goal_185_l144) (TSub:=goal_169_l128) (roots:=roots_185) (rootsSub:=roots_169)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x30300000303000000000000000000000303000003030000, 0, 16)] (by decide +kernel) (by decide +kernel) low_169_l128

theorem lowZ_185_2_144 : Lower true dzo_185_2 roots_185 gzo_185_2_144 6 :=
  lower_iso (d1:=dom_185) (roots1:=roots_185) (T1:=goal_185_l144) [(dom_185, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_185_l144

theorem low_171_l130 : Lower true dom_171 roots_171 goal_171_l130 6 :=
  lower_slice (d:=dom_171) (dSub:=dom_169) (T:=goal_171_l130) (TSub:=goal_169_l128) (roots:=roots_171) (rootsSub:=roots_169)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c00000c0c000000000000000000000c0c00000c0c, 0, 2)] (by decide +kernel) (by decide +kernel) low_169_l128

theorem lowZ_171_16_130 : Lower true dzo_171_16 roots_171 gzo_171_16_130 6 :=
  lower_iso (d1:=dom_171) (roots1:=roots_171) (T1:=goal_171_l130) [(dom_171, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_171_l130

theorem low_57_l16 : Lower true dom_57 roots_57 goal_57_l16 5 :=
  lower_slice (d:=dom_57) (dSub:=dom_41) (T:=goal_57_l16) (TSub:=goal_41) (roots:=roots_57) (rootsSub:=roots_41)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x303000003030000, 0, 16)] (by decide +kernel) (by decide +kernel) low_41

theorem lowZ_57_2_16 : Lower true dzo_57_2 roots_57 gzo_57_2_16 5 :=
  lower_iso (d1:=dom_57) (roots1:=roots_57) (T1:=goal_57_l16) [(dom_57, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_57_l16

theorem low_59 : Lower true dom_59 roots_59 goal_59 6 :=
  lower_slice (d:=dom_59) (dSub:=dzo_57_2) (T:=goal_59) (TSub:=gzo_57_2_16) (roots:=roots_59) (rootsSub:=roots_57)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c0c0c0c0c0c0c, 16, 18)] (by decide +kernel) (by decide +kernel) lowZ_57_2_16

namespace S_187
def pairsG : List (Nat × Nat) := [(1,9), (1,33), (1,129), (2,18), (2,130), (3,11), (3,19), (3,35), (3,131), (8,9), (8,40), (8,136), (10,11), (10,26), (10,42), (10,138), (16,18), (16,144), (17,19), (17,25), (17,49), (17,145), (24,25), (24,26), (24,56), (24,152), (32,33), (32,40), (32,160), (34,35), (34,42), (34,50), (34,162), (48,49), (48,50), (48,56), (48,176), (128,129), (128,130), (128,136), (128,144), (128,160)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3ffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_187.map (· &&& dom_187)
def goalM : Nat := goal_187 &&& dom_187
def NN : Nat → Nat
|4=>0x33
|5=>0x129
|6=>0x29a
|7=>0x149
|8=>0x34
|9=>0x7
|10=>0x1
|_=>0
def HT : Nat → Nat → Nat
|4,0=>0x7ce2c6df9d54a974f3b84bbc747e65404c83f33239ae4364612f3492aecf26f7f22f1122985219571e2041dda61cedc1b2a91b2541a36319fca17fe117c8d1622013ecf133fa0f6c60e72e0ceaa0c81e0c0160bfec0bc2e0b6ac09d6b065ca05874051cd03f6b03d6b039e803411033270319002c1a0284d028040201b01f44
|5,0=>0x13eea137b713780135bf13421133f312c5112c4b12ac8123b8123a9123a61232d1230b12210120ee11bb61146a1122d10f7110cdc10721105e3103b8101390ff050fa9e0f2860ecfd0ec9b0e67a0e2b10e25a0e0280e0020df410d4a90d49b0cbbb0c97c0c8e60c7200c4c80c4950c1220c0160bff00beb30be010bb870bac80b2f90afea0af7e0ab290aad00a6490a5250a51d0a43809e8809af209623093c009153090970907508d6608c5308946085e40846507f8407f6807e4307b3307ae307a7b078d5075e2075d307508074e9070aa0703706c3a06bac05f42053aa04edd04e4d04e3404dd304d57044d5042be040e403dbe038510376a03694036830357c033a20312d02c6c02a29029470260a024b301e2501dc401cda01a1d017f0013fd013fc0115f01106010ae00f4700df300bc200a8e009f700847005a100410
|5,1=>0x4f81c4e7c84e5b04d5a84d4ac4877947de746a66449ea4492e4456e434ee41b5440bb83f66a3eeea3bfc53ba4a3990a397de38fde371e336eed36be835faa35bba359263576534bef3498c346f432659319ac3165a3127730ec62ff372fcec2fada2f2772e7622e0452d57d2d3a52cd8f2cc232bc052b33c2aa162a32629a7a293e52917b28d9a28ae427f5b274ee26fc226f9d2644a2618925ab424fa2249c42343721eba21957213ff20f6e20a0f209962090720611203af202701ff0f1fc791fae41f8b21f1d61ee4c1ec0f1e62e1e2b21d2961d2011d18c1c7751c4d01c3d01c3371c1e61bf8a1ba9a1b95d1b0361a9401a85e1a44819d101931018d0f187f7187ca1879f17fe117fd417df41784316ea4168d3167c6166fd16659164cb161e315b9a15b2215aee159ec158be1508414f4b14b5a148071467c1454913f69
|5,2=>0xf605ebd89ab7a23b4899a15a18beff877468527784f0782d0d7834977df176da57250b71c786bd456b2496a02469b896903b689ea6822f6788b66fd365637613f860f135f4b85d5895cb6c5c9825c2855bcef5a84d59f6958ec9576685632453577534d552bcd
|6,0=>0x6321060aa0609905ee405d9105d3305cf805c8505b3a059e40576c055d405541054e8054960534a0530e052e5052e00529b0528f051f1050c8050600504b04ff704e2c04dd504da504d2404cd004afb04ad804ad3049f6049c4049c30491f048ba047290471b046ff0469d0463f0457904506041df041ae0410303dcd03aee03ad803aac03a0a039980378603694034ba033b3030980302602f4c02da502d7702d4b02d4902d2f02c7602c1702b61029880288c028680276a026da025c202542024820243202404023800230b01ff101f6901ece01e2501e0801c6601bd401bcd01aaf01a9b018c3017e50173e0170c01663015b70143d01416012900113200d9900d5e00c6d00c2700b3e00aa0009e3009d5009ba009af0089e00814005fc005f4005f3004df004b7004100039a00387003830035b0025d001ec001940006b
|6,1=>0x10c2a1047f102d5101550fff10ffbf0fe220fe010fda60fb600fb010fa490fa1c0f9ea0f8c30f8af0f7d60f6130f48b0f3aa0f23f0edf90edf20ea580e91e0e8f20e74e0e53f0e4940e2360e1f90e1f70e0ed0e03d0de8b0dcd40daf50d54e0d3a80d39e0d2e00d2810d2590cdc40cd340ca880ca000c82e0c77a0c74a0c6950c4b80c2f30c2a00c1280c0f40c0800c0210be170bb190ba560b9c90b9c80b6f70b6060b5ce0b2220afe70ace60ab660ab360a97d0a94a0a8e00a6490a6200a4540a2210a1ce09f9c09f2209e9d09e7009cda0991e0991509722095420939809172090ec090990909708f6908e6208e3708df408bf408b8208b7408a8d0896308715086a10825907fba07d9707d8d07d7607b3207adb078e6078880786c07869074e907109070600703906e5206c2e06c0306a10069800674d0644b063dc06352
|6,2=>0x1f0871edfd1e7851e74a1e7321e4be1de371dbcf1d3f31d2691d2081d1bb1d18c1d0541ce831ce751ccbb1cb841ca4d1c9761c6331c4661c0f41be221bc251ba4c1b95d1b95c1b93a1b7e61b4d71b1711b1451b1011ac531ac501ac3b1aada1aabc1a75e1a69b1a43a1a3e51a35c1a1861a17919fe019eb919cab19c1019a38196fc1932e1919e18d31189411890918880187c8186441830f17fe117d1217a1a1762c176211752c16dd416c9516a1f16880166fd1619315d3f15c1815b8b15b07159c0154da1513d14fea14b4d1480f14748145931432713fd613f6913f4d13e2513d7513c1013a90139f213745136b6136ae1362d131d6131c71319f130aa1308912e7812a5a129d91270b1267411f7b11ea411ddd11bf011b8f11b18119fb11800117ee117b91179c11784115f7111e3111b71114810f9e10f7110ee610e4a
|6,3=>0x327383259c31f2631d0f31a69316c4315da313b23137a312773103e30db0307f33067e3043f300da2f92b2f5242f2772ee302e8ed2e4e52e2862e18e2dd982dd3b2dc962dbb82db932da962cc132cb032c8de2c4c92c2182c1742bb4e2b97e2b8832b64e2b3a42b3102b1ad2afc02aeed2aa3c2a9d42a6822a23e2a20f29f7229e9729cef29c3b29a22298f6298ce2973a295f3294c8293c7292122919628e522870e28595278ef27807277912730726e6126d7326cde26b2e2674f2673f2623125c12259362586f2586b258412578c252b1251ae2510b24ee424e8d24daf2428023d0d23cc4236b7232bb22a7f2271b22656223e92233421fb621eba21e6b21d34216d42169620e5c20e3820d7920c64203dd202e8202cd2023c2020c200802006c1fd8a1fd4b1fc791fb681fae01fad51f9211f91b1f8d61f5a71f4a01f3ab
|6,4=>0x70db0701376ff0b6f3026e74d6d6ad6cdff6c5a06ad386a26b6982e695c568f5965090624ad616f56137a60edd607fc5cb6c5bcb35b5f75aea75abb45a29559ef75958a5947759373576c95732a55ef455ef355adc555c15486c53b5453577534d5523d451d8a51b26512584fd004f2404f1104e9fb4e3294dedc4c5904c5694c2414b6dc4911948e9648d92483ec48042478dc464f145c494597c4589d44ef744e9b44972448ef4456e4403843e9142aec422f74226941b54410b540aa5407e5400863fcb63f7943f7933f31a3ee4c3e4ed3dd9c3db963dab63ca073c07d3b5533ab9e399643951b38ff138e07389453871c3863838436381ad3814937d0537b16376ec3739536eed36af63698b3694f3694a36508362883617d3609b3607435f5735f4135d8035bb9358c53566634851347c833e1f33d273389d337fb32c47
|6,5=>0xee80acdf7ab60f6ac858a6577a317ba2b27a0e789f0419d2419a4289829f96aae8de6883b18829277e3a97b1b67ac3278ac376da57676174bc0731ff72730710fb
|7,0=>0x13b6c13a951381b132d8131ae12e6512674120541200e11324111f01043b101b60fff10fc430fa300f9c60f5120f4ff0edb50e5c20e36c0e1250e04d0deb00dc260dbb00db200daf50d6e50d5120d2630d0290d0280cedf0cd430c8540c5370c4a80bff30be5c0bd2d0bbff0b6fd0b4c30b2010ad8f0a6f60a6200a4540a4230a2ec0a2e60a1ce09cd909ad4098de0958c0940f093350925f090da08da908b0b08374082220796b06ff50672e065c3064520639a0632f062a406223061920609a0602505f7405ce505a520579f056f8056380500304fd104b12048c5045a5043dc04304041ae03be903437033b30333502e9102d2f02bf002b2e02a4b0299102860026c20245b021710201601fc801d8601953016450151b00d5500be200b3e00b2a00a9700918008bf007dc007c7005f3004f0003fb003c60037f0020500063
|7,1=>0x3d2413c63f3c3643c0f73b53b39e5539e3739ddc38f433611931d0d31aa43148d3127730ee3307f330468300da2f9242f8e92f7182f41d2f0c62e26d2dc712da312d5ac2b48f2a95d2a64929a222956b290dd28e2628c2f28a86285a027e1b27841275202748f273d1272ac26fe726bb4267e42623125cb625ac425926254ca24c8c24b5523930231972308223058229be226a2221ad21eba21b2e21ae321958216962125720c611fe3f1fd8a1fc791fb4b1f4f01f4a01f11f1efcb1e5a41e44b1dc1c1da0c1d9d01d8d51d4751d0ae1cd841cd6e1c16e1bbcc1b69c1b6111b2371acdf1a8f91a10619db819cf119c79189ed18802187c8186501844117f6b17c67176c1175a31749e171e4170c21707716a0f169531674a164b11648c15b2215adc1595a154ae153bc14ebc14e8114a86148651466d1445a13faa13f7413e42
|7,2=>0xc99cdb674bb4cc2b0e65aebd2a3c65a2b279d24197433926218b4a37fe347cf8c79bb4760d1755ea74b017262c713aa701376e74d6d6ad68d5064df5624ad60edd60e5b5e2075dde85c86a5bdd4596b35887b5731956e36566ac55edf54e4c532d652dd05149e509ff4ee714ed594dbfe4da964ca8e4c67a4ad414a68f4a610478f64533d44ef744c414419043ff643e91436a7432bd42b6442aec42a84429f4412cb40f0740d173ff743fc203f6b23ed693ebad3e444
|8,0=>0xab2548cbdc737657038b6b73c6b09e624ad60edd603855031a4de524ab1749c7d49b9046f72442fd3e9a436ba635b6e3080b296d128d8b284ad273bb26312261b82536f22cbd2271e224f5220191daee1c0d21bc581b33b19a4816bc514ae212cae11517114e70d0fb0ad290a02a080960597c0582503dcc031ad02c81022f6012ee
|9,0=>0x8008144c572fdf81cead17b0011d0205e24
|10,0=>0x5e24
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xc0c0f0e0c0c0f0e00000000000000000c0c0f0c0c0c0f0cc0c0f0f0c0c0f0e00000000000000000c0c0f0f0c0c0f0ef0f0f0f0f0a0f0a00000000000000000f000f0000000000f0a0f0a0f0a0f0a00000000000000000000000000000000f0f0f0f0f0f0f0f00000000000000000000000000000000f0a0f0a0f0a0f0a00000000000000000f0a0f0a0f0a0f0af0f0f0f0f0a0f0a00000000000000000f0f0f0f00000000f0f0f0f0f0a0f0a00000000000000000f0a0f0a0a0a0a0af0f0f0f0f0f0f0000000000000000000f0f0a0a0f0f0a00f0f0f0f0f0f0a0a00000000000000000a0a0a0a0a0a0a0af000f000f000f0000000000000000000f000f000a000a00f000f000f000f0000000000000000000f000f000f000f00f0f0f0f0f0f0f0f00000000000000000f0f03020f0f0302f0f0f0e0f0f0f0e00000000000000000c0c0c0c0c0c0c0cf0e0f0e0f0e0f0e00000000000000000f000f000f000f00f0f0f0e0f0f0f0e00000000000000000f0f0a000f0f0a00f0f0f0f0f0f0f0f00000000000000000a0a0a0a0a0a0a0af0f0f0f0f0a0f0a00000000000000000f000f000f000f00f0f03030f0f030200000000000000000f0f03000f0f0300a0a0a0a0a0a0a0a00000000000000000a0a0a0a0a0a0a0af0f0f0f0f0e0f0e00000000000000000c0c0c0c0c0c0c0cf0f0f0f0f0f0f0a00000000000000000f0f00000f0f0000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0000000000f000f000f000f0000000000000000000a000a000a000af0f0f0f0a0a0a0a00000000000000000f000f000a000a00f0f0f0f0000000000000000000000000f0f0f0f00000000f0a0f0a0f0e0f0e00000000000000000a0a0a0a0a0a0a0ac0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0cf0f00000f0f000000000000000000000f0f00000f0f0000f0f0f0f0f0f0f0f00000000000000000f000f000f000f00a0a0a0a0f0f0f0f00000000000000000a0a0a0a0a0a0a0a00000000f0f0f0a0000000000000000000000000f0f0f0a
|0,1=>0xf0f00000f0f000000000000000000000e0e00000e0ea080a080f0c0f0c00000000000000000a080a080a080a08e0e0e0e0e0e0e0e00000000000000000e0e0e0e0e0e0e0ef0f0f0f0f0c0f0c00000000000000000a0a0a0a0a080a08f0f0f0f0a0a0a0a00000000000000000f0f0f0f0a0a0a0af0f0f0f0f000f0000000000000000000f0f0f0f0f000f00f0f0f0f0f0f0f0f00000000000000000c0c0c0c0c0c0c0cf0f0c0f0f0f0c0e00000000000000000f0f00000f0f000000f000f000f000f0000000000000000000f000f0000000050505050505050500000000000000000505050500000000f0f0f0f0f000f0000000000000000000a0a0a0a0a000a0050505050505050500000000000000000505050505000500e0e0e0e0f0e0f0e00000000000000000a0a0a0a0a0a0a0af0f0f0f0a0a0a0a00000000000000000f0a0f0a0a0a0a0a0000000000f000f000000000000000000000000000a000af0f0f0f0f0a0f0a00000000000000000a0a0a0a0a0a0a0af0f0f0f0f0f0f0a00000000000000000f0f0a0a0f0f0000f0f0f0f0f0f0f0000000000000000000f0f0f0f00000000f0f0f0f0f0f0f0000000000000000000f0f0f000f0f0000f0f0f0f0f0f0f0000000000000000000f0a0f0a00000000a0f0a0f0a0f0a0f00000000000000000a0a0a0a0a0a0a0af0f0f0f0f0f0f0a00000000000000000a0a0a0a0a0a0a0af0f0f0f0505050000000000000000000f0f0f0f000000000000000000500000000000000000000050500000f0f000000000000f0f0f0f0000000000000000000000000f0a0f0af0f0f0f0f0c0f0c00000000000000000f000f0000000000f0c0f0c0f0c0f0c00000000000000000000000000000000f0c0f0c0f0c0f0c00000000000000000f0c0f0c0f0c0f0cf0f0f0f0f0c0f0c00000000000000000f0f0f0f00000000f0f0f0f0f0e0f0e00000000000000000f0a0f0a0a0a0a0a000000500000005000000000000000005050505050005000000c0d00000c0d00000000000000000f0f03020f0f0302
|0,2=>0xf0f03030f0f020200000000000000000f0f03030f0f0000f0a0f0a0f0a0f0a00000000000000000f0a0f0a0f000f0000f000f000f000f0000000000000000000f000f000a000a30300030303000300000000000000000303000303030002f0f0a0a0f0f0a0a00000000000000000000000000000000f0f0a0a0f0f0a0a00000000000000000f0f0a0a0f0f0a0af0f0f0a0f0f0f0a00000000000000000f000f000f000f00f0f0f0f0f0f0f0a00000000000000000f0f0f0f0f000f00f030f030f030f0300000000000000000f030f030f000f00c0f0c0f0c0f0c0f00000000000000000c0f0c0f0c0c0c0ce0e0f0f0e0c0f0c00000000000000000e0e0e0e0e0c0e0cf0f0f0f0f0a0f0a0000000000000000000000000000000000000000f050f050000000000000000000000000f0a0f0a00f000f000500050000000000000000000f000f0000000000000000f0f0f0f0000000000000000000000000f000f00f0f0f0f0f0f0c0c00000000000000000f0f00000f0f000000000000f0a0f0a0000000000000000000000000f0a0f0a0050005000500050000000000000000000f000f000a000af0f0f0f0f0f0f0a00000000000000000000000000000000f0f0f0f0f0f0f0a00000000000000000f0f0f0f0f0f0f0af0f0f0f0f0a0f0a00000000000000000f0f0f0f0f0a0f0af0f0f0f0f0f0f0f00000000000000000f0f00000f0f0000f0f0f0f0f0f0f0e00000000000000000c0c0c0c0c0c0c0c00000000000000a0000000000000000000a000a0a0a0a0aa0a0a0a0f0e0f0e00000000000000000a0a0a0a0f0e0f0e00000000f0f0f0f0000000000000000000000000a0a0a0af0f0f0f0f000f0a00000000000000000f0f0f0f0000000000000000004000400000000000000000c0c0c0c0c0c0c0cc0c0c0c0c0c0f0e00000000000000000c0c0c0c0c0c0f0ec0c0f0f0c0c0e0e00000000000000000c0c0f0f0c0c0e0ef0f0f0f000f000f00000000000000000f0f0f0f0000000050505050001000100000000000000000505050505000500
|0,3=>0xa000f000a000f0000000000000000000a000a000a000a5000505050005050000000000000000050005000500050000000000f0b0f0b0000000000000000000000000f0a0f0af000f000f0f0f0f00000000000000000f000f000f000f0000000000f050f050000000000000000000000000f000f00a0f0a0f0a0e0a0e00000000000000000000000000000000c0c0f0f0c0c0f0c00000000000000000c0c0f0f0c0c0f0cf030f000f030f0300000000000000000f000f000f000f00f0f0f0f0a0f0a0a00000000000000000f0f0f0f00000000f0f0f0f0f0e0f0e0000000000000000000000000f0a0f0a00000000f0f0f0f0000000000000000000000000000000000000000000000f0000000000000000000f000f00000000f0f0f0a0f0f0f0a00000000000000000000000000000000f0f0f0a0f0f0f0a00000000000000000f0f0f0a0f0f0f0af0f0f0a0f0f0f0a00000000000000000a0a0a0a0a0a0a0af0f0f000f0f0f0000000000000000000000000000000000f0f0f000f0f0f0000000000000000000f0f0f000f0f0f0000000000f0f0f0a0000000000000000000000000a0a0a0af0f0f000f0f0f0a00000000000000000f0f00000f0f000000000000f0e0f0e00000000000000000000000000000000f0f0f0f0a0a0a0a00000000000000000000000000000000303030303030301000000000000000003030303030303000000000000f000f00000000000000000000000000000000f0f0f0f0f000f0000000000000000000a0a0a0a0a0a0a0af0f0f0f0f0f0f0f00000000000000000f0a0f0a0f0a0f0af0e0f0e0f0e0f0e00000000000000000a0a0a0a0a0a0a0af0f0f0f0e0e0e0e00000000000000000000000000000000f0f0f0f0e0e0e0e00000000000000000f0f0f0f0e0e0e0ef0f0f0f0f0f0e0e00000000000000000f0f00000f0f0000f0f0f0f0f0f0f0000000000000000000f000f000f000f0050505050500050000000000000000000505050505000500a0a0a0a0a0f0a0f00000000000000000a0a0a0a00000000
|0,4=>0x10101010000000000000000000000000a0a0a0aa0a0f0f0a0a0f0f00000000000000000a0a0a0a0a0a0a0a0000f0f00000f0f00000000000000000000000000000000a0a0f0f0a000f0000000000000000000a0a0a0a0a000a00a0a0a0a0a0f0a0f00000000000000000f000f000f000f000000000000500050000000000000000000000000a0a0a0a10101010101010100000000000000000f0f0f0f0a0a0a0af0a0f0a0f0a0f0a00000000000000000f0a0f0a0000000000f000f000f00000000000000000000000f000f000f00000030003000300030000000000000000000000000f000f000000000050505050000000000000000000f000f0000000030303030302030200000000000000000300030003000300f0f0f0f0e0e0e0e00000000000000000f000f000e000e000000505000005000000000000000000000005050000050030303030300030000000000000000000303030303000300f050f050f050f0500000000000000000f000f000f000f0000f000f000f000f00000000000000000000000000000000f0f03030f0f020200000000000000000f0f03030f0f0202f0f0f0f0f0f0e0e00000000000000000c0c0c0c0c0c0c0ca0f0a0f0a0e0a0e00000000000000000a0f0a0f0a0e0a0e00500050005000500000000000000000000000000000000f0f0f0f0f000f0000000000000000000000000000000000f0f0f0f0f0f0a0a00000000000000000f0f0f0f0000000000f000f000f000a0000000000000000000f000f0000000000000000f0f0a0a0000000000000000000000000f000a00f0f0f0f0f0c0f0c00000000000000000e0e0e0e0e0c0e0cf0f0f0f0a0a0a0a00000000000000000f0f0f0f00000000f0f0f050f0f0f0000000000000000000f000f000f000f000000f0f00000f0f000000000000000000000f0f00000f0ca0a0a0a0a0a0a0a00000000000000000a0a0a0a0a000a00f0f0f0f0c0c0c0c00000000000000000f0f0f0f0c0c0c0c10101010101010100000000000000000101010100000000
|0,5=>0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0a0a0a0af000f000f050f0500000000000000000f000f000f000f00c0c0c0f0c0c0c0e00000000000000000c0c0c0f0c0c0c0ef0f0f0f0f0f0f0a00000000000000000f0f0f0f0f0f0000f0f0f0a0f0f0f0a00000000000000000f0f00000f0f0000e0e0e0e0e0e0e0e00000000000000000e0e0e0e00000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0c0c0c0c0000f0f00000f0f000000000000000000000f0f00000c0cf0f0f0f0f0f0f0000000000000000000000000000000000f0f0f0f0f0f0f0000000000000000000f0f0f0f0f0f0f00f0f0f0f0f0f000000000000000000000f0f0f0f0f0f000030303030303030300000000000000000303000303030002000000000000f0f00000000000000000505000005050a0af0f0f0f0f0f0f0f00000000000000000f0f0f0f0f000f00f0f0f0f0f0e0f0e00000000000000000f0f0f0f0a0a0a0af0f000f0f0f000a00000000000000000f0f000f0f0f000a0000000000500050000000000000000000000000f000f00f0c0f0c0f0c0f0c00000000000000000a080a080a080a0850505050404040400000000000000000505050504040404d0d0d0d0d0d0d0d00000000000000000d0c0d0c0d0c0d0cf0f0f0f0f0e0f0e00000000000000000f000f000f000f00a0a0a0a0a0f0a0f00000000000000000f0f0f0f0a0a0a0af0f0f0f0e0e0e0e00000000000000000f0f0f0f0e000e000000f0f00000a0a000000000000000000000a0a00000a0a50505050505050500000000000000000000000000000000f0f0f0f0505050000000000000000000f0f0f0f0505050050505000505050000000000000000000505050005050500f0f0f0f0505050000000000000000000000000000000000f0f0f0f0f0c0f0c00000000000000000c0c0c0c0c0c0c0cf0f0f0f0c0c0c0c00000000000000000000000000000000f0f0f0f0f0c0f0c00000000000000000f000f000f000f00f0f0f0f0e0e0e0e00000000000000000f0f0f0f00000000
|0,6=>0xf0f0f0f0f0f0f0f00000000000000000e0e0e0e0e0e0e0ef000f000f000f0000000000000000000f0f0f0f0a0a0a0a00f000f000e000e0000000000000000000f000f000e000e30303030303030300000000000000000303000003030000f0f0f0f0f0f0f0f00000000000000000f0c0f0c0f0c0f0cf0e0f0e0f0e0f0e00000000000000000f0e0f0e0f0e0f0ef0c0f0c0f0c0f0c00000000000000000f0c0f0c00000000f0f0f0f0f0f0f0000000000000000000f0f01010f0f010000000000505050500000000000000000000000005000500c0c0f0e0c0c0f0e00000000000000000c0c0f0e0c0c0f0ee0e0f0e0e0e0f0e00000000000000000a0a0a0a0a0a0a0a501050105010501000000000000000005000500050005000000f0f00000f0f000000000000000000000c0c00000c0c5050505050005050000000000000000050505050500050400f000f000f000f0000000000000000000f000f000f00005000500050505050000000000000000050005000500050000000000000000000000000000000000f0f03020f0f03020000c0d00000c0d00000000000000000000000000000000a0a0a0a0a0f0a0f000000000000000008080808080c080cb0b0b0b0b0a0b0a00000000000000000a0a0a0a0a0a0a0af0f0a0a0f0f0a0a00000000000000000f0f0a0a0000000000000000005000000000000000000000f0f00000f0f0000f0f0f0f0a0f0a0f00000000000000000f0f0f0f00000000f0a0f0a0f0f0f0f00000000000000000f000f000f000f0000f000f000c000c0000000000000000000f000f000c000cf0f0f0f0003000300000000000000000f0f0f0f0000000000f000f000a000a0000000000000000000f000f000a000a30302020303030300000000000000000303020203030302303000003030303000000000000000003030000030302020050005000500050000000000000000000500050000000030302020303020300000000000000000303000003030000a0a0f0f0a0a0f0a00000000000000000a0a0f0f0a0a0f0a
|0,7=>0xf0f03000f0f020000000000000000000f0f03030f0f02020000c0c00000d0d000000000000000000000c0c00000d0cf0f0f0f00000f0a00000000000000000000000000000000f000f000b000b0000000000000000000f000f000a000a0030300010000000000000000000000000f0f0f0f00000000f0f0f0f0f0e0f0e00000000000000000000000000000000f0f0f0f0f0e0f0e00000000000000000f0f0f0f0f0e0f0ef0f0f0f0f0f0f0e00000000000000000f0f00000f0f000000f000f000f000a0000000000000000000f000f000f000af0f0f0f0302030200000000000000000f0f0f0f030203025050505000500050000000000000000050505050000000000000000505050500000000000000000f0f0a0a0f0f0a0af0f0f0f000f000f00000000000000000f0f0f0f000a000af0f0f0f0f0f0000000000000000000000000000000000000000f0f0000000000000000000000000f0a0f0a00000000f0c0f0c0f0f0f0e00000000000000000c0c0c0c0c0c0c0cf0f03030f0f030200000000000000000f0f00000f0f0000303030303030303000000000000000003030303030303000000000000500050000000000000000000000000000000000000000000000000000000000000000f0e0f0e0f0e0f0e3030303030303030000000000000000030203020302030200f000f000f000f0000000000000000000e000e000e000e30301000303010100000000000000000303010003030100505050505050505000000000000000005050505050c050c0000c0f00000c0f000000000000000000000c0c00000c0c00000000f0c0f0c0000000000000000000000000f0c0f0cf0f0f0f0f0f0f0a00000000000000000f0f0f0f00000000f0f0f0f0f000f0500000000000000000a0a0a0a0a000a0000000000505050500000000000000000a0a0a0a0a0a0a0af0c0f0c0e0c0e0c00000000000000000f0c0f0f0e0c0e0e50505050505050500000000000000000500050005000500f0f0f0f0000000000000000000000000f0a0f0a00000000
|0,8=>0x30301010303010100000000000000000303010103030000f0f03020f0f0302000000000000000000000000000000001010101010101010000000000000000050505050500050030303030303030300000000000000000303030300000000f0f00000f0f0f0a00000000000000000000000000000000a0a0a0a0a000a0a00000000000000000a0a0a0a0a000a08f0f0f0f0f0f0a0a00000000000000000000000000000000f0f0f0f0f0f0a0a00000000000000000f0f0f0f0f0f0a0af0f0f0f0f0f0f0a00000000000000000f000f000f000f00f0f03030f0f030000000000000000000f0f03030f0f0300f0f0b0b0f0f0b0a00000000000000000a0a0a0a0a0a0a0a00000000f0f0f0f0000000000000000000000000c0c0c0cc0c0c0c0f0e0f0e00000000000000000c0c0c0c0f0e0f0e50505050504050400000000000000000505050505000500f000f000f000f0000000000000000000f000f000f050a000000000000f000f00000000000000000f0f0f0f00000000f0f0d0d0f0f0d0c00000000000000000f0f00000f0f00000000f0f00000f0f000000000000000000000f0c00000f0cf0f0f0f0e0e0e0e00000000000000000a0a0a0a0a0a0a0af0f0f0f0f0f0c0c00000000000000000c0c0c0c0c0c0c0cf0f0f0f0f0a0f0a00000000000000000a0a0a0a0000000000000000000050500000000000000000f0f0f0f00000000f000f050f000f0500000000000000000f0a0f0a0f0a0f0af0f0f0f0f0f0f0f00000000000000000505050505050500f0f03020f0f030200000000000000000f0f03020f0f03023030303030303030000000000000000030303020303030200000000505050500000000000000000000000000000000f0a0f0a0f0f0f0f00000000000000000f0a0f0a0f0a0f0a0000f0f00000f0f000000000000000000000f0f00000f0ec0c0c0c0f0f0f0e00000000000000000c0c0c0c0c0c0c0cf0f0f0f0505050500000000000000000f0f0f0f05000500a0a0a0a0f0f0f0f00000000000000000a0a0a0a0f0a0f0a
|0,9=>0xf0f0f0f0f0f0f0f0000000000000000050505050500050000f000f000b000b0000000000000000000f000f000a000ad0d0d0d0d0c0d0c00000000000000000000000000000000a0a0a0a0a0a0a0a00000000000000000505050505000500f0f0f0a0f0f0f0a00000000000000000f0f0f0a00000000f0f0f000505050000000000000000000f0f0f0000000000f0f0f0f0f0f0a0a00000000000000000f0f0f000f0f0a00c0c0f0f0c0c0f0c00000000000000000c0c0e0e0c0c0e0ca0a0a0a0a0f0a0f00000000000000000a0a0a0a0a0a0a0a00a000a000f000f0000000000000000000a000a000a000a0000c0f00000c0f000000000000000000000c0f00000c0ef0f03030f0f030200000000000000000f0f03030f0f0000e0e0e0e000e000e00000000000000000e0e0e0e0000000000000000505050500000000000000000f0f0f0f0000000050505050505050500000000000000000505050505050500f0f0f0c0f0f0f0c00000000000000000f0f00000f0f0000a0a0a0a0a0f0a0f00000000000000000000000000000000f050f050f040f0400000000000000000f000f000f000f00f0f0f0f0f0e0f0e00000000000000000a0a0a0a0a0a0a0af0f0f030f0f0f0200000000000000000f0f00000f0f0000f0f0f0f000000000000000000000000000000000f0a0f0af0f0f0f0505050500000000000000000f0f0f0f00000000f0f03030f0f030200000000000000000f0f02020f0f02020000000000f000f00000000000000000f0a0f0a0f0a0f0aa0a0a0a0a0a0a0a00000000000000000a0a0a0a0a080a08f0f0f0f0000000000000000000000000f0a0f0a0f0a0f0af0a0f0f0000000000000000000000000f0a0f0a0000000000000000005000500000000000000000f000f000f000f00c0c0c0c0808080800000000000000000f0f0f0f0a0a0a0a30303030303030300000000000000000000000000000000f0f0f0f0b0b0b0b00000000000000000f0f0f0f0a0a0a0af0b0f0b0f0a0f0a00000000000000000a0a0a0a0a0a0a0a
|0,10=>0xf0f0f0f00000f0a00000000000000000f0f0f0f00000f0a0000f0a00000f0a000000000000000000000f0a00000f0a00000000f0f000500000000000000000000000000000000f0f0f0f0f0f0f0f0000000000000000000f000f000f00000000f0f00000f0f00000000000000000f0a0f0a0f0a0f0af0f00000f00000000000000000000000f0f05050f000500f0f0f0f0f0d0f0d00000000000000000f0f0f0f0f0c0f0cf0a0f0a0f0a0a0a00000000000000000f0f0f0f0f0f0a0a50505050504050400000000000000000505050505040504f0f0f0f0f0c0f0c00000000000000000f0f0f0f0f0c0f0c5050505050405040000000000000000000000000000000000000000505050000000000000000000f0f0f000f0f0f00f0f0f0f0f0e0f0e00000000000000000e0e0e0e0e0e0e0ef0f0f0f0a0f0a0f00000000000000000f0f0f0f0a0a0a0af0f0a0a0f000a0000000000000000000f0f0a0a0f0f0a0a00000000005000500000000000000000a0a0a0a0a0a0a0a00000000005000500000000000000000f0f0f0f0f0a0f0af0f03030f0f000000000000000000000f0f03030f0f030200000000000000000000000000000000f0f0f0f0a0a0a0a00000000000000000000000000000000f0f0f0f0f0a0f0a303030303020302000000000000000003030303030203020000f0f00000f0a000000000000000000000f0f00000f0a0000000000f000f000000000000000005050505000a000af0f0f0f0f0f0f0f0000000000000000000000000f0a0f0ac0c0c0c0c0c0c0c00000000000000000c0c0f0f0c0c0f0e00f000f000a000a0000000000000000000a000a000a000ac0f0c0f0c0f0c0f00000000000000000c0c0c0c0c0c0c0cf0f0f0f0c0c0c0c00000000000000000f0a0f0a0c080c08f0f0f0f0e0e0e0e00000000000000000f0c0f0c0e0c0e0c00500050005000500000000000000000f000f000f000f000000e0e00000e0f000000000000000000000e0e00000e0e00000000000000000000000000000000f0a0f0a0f0a0f0a
|0,11=>0x302030200000000000000000000000003020302f0f0f0f0c0d0c0d0000000000000000000000000000000030203020302030200000000000000000302030203020302f0f0f0f030203020000000000000000000000000000000000000000000000000000000000000000f0f0f0f0f0e0f0e505010105050100000000000000000005050101050501000000000000000000000000000000000050505050404040400e000e000000000000000000000000000e000e000e000e50505050505050500000000000000000505050504040404f050f050f050f0500000000000000000f050f050f040f04b0b0b0b0b0b0b0b00000000000000000b0b0b0b0a0a0a0a00000000504050400000000000000000000000005040504c0f0c0f0c0f0c0f00000000000000000c0e0c0e0c0e0c0e0000c0f00000c0f000000000000000000000c0e00000c0ef0f0f0f0f000f0500000000000000000f0f0f0f0000000000000000f0f0a0a0000000000000000000000000f0f0a0a3030303030303030000000000000000030303030300030000000000000050500000000000000000000000000000500f0f0f0f0f050f0500000000000000000f0f0f0f0f000f0030303030303030300000000000000000300030003000300b0b0b0b0b0b0b0b00000000000000000a0a0a0a0a0a0a0ac0c0c0c0c0c0c0c00000000000000000f0e0f0e0f0e0f0e00000000e0e0e0e0000000000000000000000000e000e00f0f0f0f0303030300000000000000000f0f0f0f03030000b0b0b0b0b0b0b0b00000000000000000b0b0a0a0b0b0a0ae000e000e000e0000000000000000000e000e000e0e0e0e00000000000000000000000000000000f0f0a0a0f0f0a0af0f0f0f0f000f0000000000000000000000050500000500f0f0f0f0f0f0f0f000000000000000000000f0f00000f00f0f0f0f0504050400000000000000000f0f0f0f050405045040504050405040000000000000000050405040504050400000000a0b0a0b00000000000000000000000000000000
|0,12=>0xf0f0f0f0f0f0f0f00000000000000000f0e0f0e0f0e0f0ef0f0f0f0f0f0f0f0000000000000000000000000f0f0a0a0000f0a00000f0a000000000000000000000f0a0000000000f000f000a000a00000000000000000000000000000000c0f0c0f0c0e0c0e00000000000000000c0c0c0c0c0c0c0c0000a0a00000f0f000000000000000000000a0a00000f0ac0c0c0c0d0d0d0d00000000000000000c000c000d000d0000000000000000000000000000000000f000f0f0f000f0ae0e0e0e0e0e0e0e00000000000000000e000e000e000e0000f000f000d000d0000000000000000000f000f000c000cf0d0f0d0f0d0f0d00000000000000000f0c0f0c0f0c0f0cf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f00f0f0f0f0f0f0f0f000000000000000000000000000f000a0000f0f00000f00000000000000000000000f0f00000f0000000000000000000000000000000000e0e0e0e0e0e0e0ef000f000f000f0000000000000000000f0e0f0e0f0e0f0ef0f0f0f0f000f0f00000000000000000f0f0f0f0f000f0000000000f000f0f0000000000000000000000000f000f0000000000000000000000000000000000000000005050500f0b0f0b0f0b0f0b00000000000000000f0a0f0a0f0a0f0af0f0f0f00000f0f00000000000000000f0f0f0f00000000f0f0f0f0f0f0f0f0000000000000000000f000f000a000a0000f0f00000f0f000000000000000000000f0f00000000f0f000f0f0f000f00000000000000000f0f000f0f0f0000f0f0f0f0003000300000000000000000f0f0f0f000200020000000000000000000000000000000000000000f0f0f0af0e0f0e0f0e0f0e00000000000000000f0e0f0e0f000f00f0f000f0f0f000f00000000000000000f0f00000f0f0000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0a0f0a00f000f000f000f00000000000000000005000500050000f0f0f0f0000000000000000000000000f0f0f0f0f0f0f0af0f0f0f0c0c0c0c00000000000000000f000f000c000c00
|0,13=>0x30303030303030300000000000000000303030003030300f0f0f0f0f0a0f0a00000000000000000f0f0f0f0c080c08c080c080c080c0800000000000000000f0a0f0a0f0a0f0af0f00000f0f050500000000000000000f0f00000f0f000030300000303010100000000000000000303000003030000c0c0c0c0f0f0f0f00000000000000000c0c0c0c0f0c0f0cf0f0f0f0f0f0f0000000000000000000f0f00000f0f0000f0f0a0a0f000a0000000000000000000f0f0a0a0f000a00f0f0f0f0f0f0f0f00000000000000000f0f0a0a0f000a0050505050500050500000000000000000505050505000500f0f0f000f0f0f0000000000000000000f0f0f0000000000f0f0f0f0303030300000000000000000f0f0f0f0000000000f000f000300030000000000000000000f000f000000000000f0f00000f0f000000000000000000000f0000000f00c0c0c0c0c0c0c0c00000000000000000c0c0f0f0c0c0f0cf0f00000f0f000000000000000000000f0f0f0a0f0f0f0aa0a0a0a0b0b0b0b00000000000000000a0a0a0a000000000000f0f00000f0f000000000000000000000a0a00000a0af000f0f0f000f0f00000000000000000f000f0a0f000f0af0f0f0f0f0f0f0f0000000000000000000f000f000f000a00500050005000000000000000000000005000500050000f050f050f050f0000000000000000000f050f050f050f00f0a0f0f0f0a0f0f00000000000000000f0a0f0a0f0a0f0a00000000f0a0f0f0000000000000000000000000f0a0f0a505050505050505000000000000000001010101010001000030003000300030000000000000000000300030000000050505050505050500000000000000000505000005050000f0f0f0f0f0f0f0f000000000000000000000f0f00000f0af0f00000f0f0f0500000000000000000f0f00000f0f0f00a0a0a0a0a0a0a0a00000000000000000a0a0a0a0a0a0a0000f000f0000000f0000000000000000000f000f00000000f030f030f030f0300000000000000000f000f000f000f00
|0,14=>0xf0f0f0f0f0f000f00000000000000000f0f0f0f0f0f00000000f0f0000000f000000000000000000000f0f00000000e0e0e0e0e0e0e0e00000000000000000e0e0e0e0e000e000000000000f000f000000000000000000000000000c000cf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0c0f0c5050505050505050000000000000000050505050504050430303030003000300000000000000000303030300000000f0f0f0f0f0f0f0f00000000000000000f0f03030f0f0300f0f00000f0f000000000000000000000f0f0f0f0a0a0a0af0f0f0f0005000500000000000000000f0f0f0f00000000d0d0d0d0d0d0d0d00000000000000000d0d0d0d0c0c0c0c0000d0d00000d0d000000000000000000000d0d00000c0cf0f00000f0f0f0f00000000000000000f0f00000f0f0f00000000000000f0f00000000000000000000000000000f00e0e0e0e0e0e0e0e00000000000000000f0f0f0f0f0e0f0ef0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0000505050505050505000000000000000005050505050500000000f0f00000f0a000000000000000000000f0f00000000a0a0a0a0a0f0a0f00000000000000000a000a000a000a00e0e0e0e0e0e0e0e0000000000000000000000000000000000300030003000300000000000000000003000300020002707070707050705000000000000000003030303030003003030303030203020000000000000000000000000000000000a000a000a000a0000000000000000000f000f000f000a0000f0f00000f0a000000000000000000000a0a00000a0a3030303030003000000000000000000030303030000000030303030303030300000000000000000003000300020002d0d0d0d0d0d0d0d00000000000000000c0c0c0c0c0c0c0cf0f0a0a000f000a00000000000000000f0f0a0a00000000a0a0a0a0a0a0a0a00000000000000000f0f0f0f0f000f00f0f0f0f0505050500000000000000000f0f0f0f0404040400f000f000f000f0000000000000000000f000f000e000e
|0,15=>0xa0f0a0f0a0f0a0f00000000000000000a0f0a0f0a0a0a0af0f0f0f0f0f0a0a00000000000000000f000f000f000a000000f0a00000f0a00000000000000000000000000000000c0c0f0e0c0c0f0e00000000000000000c0c0c0c0c0c0c0c00005050000050500000000000000000000050000000500f000f000f000f0000000000000000000f0f0f0f0f0a0f0a3000300030003000000000000000000030303030302030230303030300030000000000000000000000000000000000a0a0a0a0a0a0a0a00000000000000000a0a0a0a0f0e0f0ef0f0f0f0f0f0f0c00000000000000000c0c0c0c0c0c0c0c00000000000000000000000000000000f0f0f0f0f0f0a0a00000000f0f0f0f0000000000000000000000000e0e0e0ef000f000f050f0500000000000000000f0000000f05000000000000302030200000000000000000f0a0f0a0f0a0f0a00000000f0f0f000000000000000000000000000f000f000000000000c000c000000000000000004040404040c040cf0a0f0a0f0a0f0a00000000000000000f0a0f0a0f0a0000005000500050f0f0000000000000000000000000000000000000000e0e0e0e0000000000000000000000000e0e0e0e10101010100010000000000000000000101010101000100f0f01010f0f010000000000000000000f0f01010f0f010000000000303030300000000000000000000000000000000f000f000f030f0300000000000000000f000f000f000f00f0b0f0b0000000000000000000000000f0a0f0a0000000000f000a000f000a0000000000000000000f000a000f000af000f050f000f0500000000000000000f000f050000000000005050000050500000000000000000000050500000404f000f0f0f000f0f00000000000000000f000f0f0f000f0a00000000f0f0f0f0000000000000000000000000f0e0f0e00000000000000000000000000000000f0f0f000f0f0f00f000f000f010f0100000000000000000f000f000f000f00f0f0f0f0f0f0f0f00000000000000000f0f0a0a0f0f0a0a
|1,0=>0xa0a0a0a0f0f0f0a00000000000000000a0a0a0a0f0f0f0af0f05050f0f050000000000000000000f0f05050f0f0500f0f05050f0f0500000000000000000000000000000000003030303020202020000000000000000030303030202020200500050005000500000000000000000005000000050000a0f0a0f0a0f0a0f00000000000000000a0f0a0a0a0f0a0ac0c0c0c0c0f0c0f00000000000000000c0c0c0c0c0c0c0c00000000303030300000000000000000000000003020302f0f0f0f0a0a0f0f00000000000000000f0f0f0f0a0a0a0a00f000f000a000f0000000000000000000f000f000a000af0f0f0f0303030300000000000000000f0f0f0f020202023030303030303030000000000000000020202020202020250505050101010100000000000000000505050500000000f0f0f0f0f0f0f0f00000000000000000f0f0f0a0f0f0f0a00000000000000000000000000000000f0f0f0a0f0f0f0af000f0f0f000f0f00000000000000000f000f000f000f00f0f0f0f0f0f0f0f00000000000000000f0f0f0f05050500f0f0f0f0a0a0a0a00000000000000000f000f000f000f000000f0f00000a0a000000000000000000000f0f00000a0af000f000f0f0f0f00000000000000000f000f000f0a0f0af0f0f0f0d0d0d0d00000000000000000f0f0f0f0d0c0d0c30303030303030300000000000000000303020203030202f0f0f0f0303030300000000000000000f0f0f0f0303020200a000a000a000f0000000000000000000a000a000a000a10101010101010100000000000000000100010001000100a0a0f0f0a0a0f0f00000000000000000a0a0f0f0a0a0a0af0f0f0f0f0f0f0f00000000000000000f0f0f0f0e0e0e0ee0e0e0e0f0f0f0f00000000000000000e0e0e0e0e0e0e0e0000e0e00000f0f000000000000000000000e0e00000e0ed0d0d0d0d0d0d0d00000000000000000d0d0d0d0d0c0d0cf0c0f0c0f080f0800000000000000000f0f0f0f0f0a0f0a00000000d0d0d0d0000000000000000000000000d0c0d0c
|1,1=>0xf0000000f00050000000000000000000f000f000f000f00f0f0f0f0f0c0f0c0000000000000000000000000000000000f000f000f000f0000000000000000000c000c000c000c0000f0f000000050000000000000000000000000000000000000000f0f0f0f0000000000000000000000000f0c0f0c00000000000000000000000000000000f0f0f0f0504050400000000000000000000000000000000f0f00000f0f0f0ac0c0c0c0d0d0d0d00000000000000000c0c0c0c0c0c0c0c00f0000000a00000000000000000000000f000f000a000a00f000f000f000a0000000000000000000a000a000a000a00000000f050f050000000000000000000000000f050f00f0f0f0f0005000500000000000000000f0f0f0f00050000f0f0f0f0f0f0f0f00000000000000000f030f030f020f02f0f0f0f0f0f0f0f000000000000000000000f0a00000f0af0f0f0f0f050f0500000000000000000f0f0f0f0f040f04000000002030203000000000000000000000000020202023030303030301010000000000000000030303030303000000000000000000000000000000000000f0f0f0f0c0c0c0cf000f000f000f0000000000000000000f0f0f0f0f0c0f0c0000c0c00000c0f000000000000000000000c0c00000c0c00000000000000000000000000000000f0f0f0f0f000f0050505050505050000000000000000000505050505050500a0a0a0a0a0a0a0f00000000000000000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f000f0f0f00f0f0f0f0000000000000000000000000f0f0f000f0f0f005050505000005050000000000000000050505050000050000500050005000500000000000000000f0f0f0f00000000f000f0f0f000f0f00000000000000000f000f0f0f000f0000000000000000000000000000000000c0c0f0f0c0c0e0e00000000c0c0c0c0000000000000000000000000f0e0f0ef0f0f0f0f0f0f0f0000000000000000000300030002000200000000303030300000000000000000000000003000300
|1,2=>0xf0a0f0f0f0a0f0f00000000000000000f0a0f0e0f0a0f0e50f050f050f05050000000000000000000f000f000f0000f0f0f0f0f0f0f0a00000000000000000f0f0f000f0f0f00000000000000000000000000000000005050505050005000000f0000000a00000000000000000000000f0f00000a0a00000000a0a0f0f0000000000000000000000000a0a0e0e0000000000000000000000000000000000000000f0a0f0af0f00000f0f000000000000000000000f0f00000f0f0f0a00f0f0f000a0f0f0000000000000000000f000f000a000af030f030f020f0200000000000000000f000f000f000f0000000000303030300000000000000000f0f0f0f00000000e0e0e0e0e000e0000000000000000000f0f0f0f0f000f0000000000f0f0f0f0000000000000000000000000f0f0f0af0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0a0af000f000f000f0000000000000000000f000f000f000a00c0c0c0c0f0f0f0f00000000000000000c0c0c0c0e0e0e0ef0f0f0f00000f0f00000000000000000f0f0f0f00000f0000000000f0f0f000000000000000000000000000f0f0f00f0f03030f0f030200000000000000000f0f03030f0f030200000000a0f0a0f0000000000000000000000000a0a0a0aa0a0a0a0a0a0a0a00000000000000000b0b0b0b0b0a0b0a00100010001000100000000000000000000000000000000f010f010f010f0100000000000000000f000f000f000f0000000000000000000000000000000000505050005050500f0f0f0f0f0f0f0f0000000000000000050505000505050000000000f0a0f0a0000000000000000000000000f000f00f0c0f0c0f0d0f0d00000000000000000f0c0f0c0f0c0f0c0000d0d00000d0d000000000000000000000d0c00000d0cf0f00000f0f000000000000000000000f0f0f0f0f0f0f0af0f0f0f0000000000000000000000000f0f0f0f0f0a0f0ac0c0c0c0f0f0f0f00000000000000000c0c0c0c0f0e0f0ef0f0f0f0a0a0f0f00000000000000000f0f0f0f0a0a0f0a
|1,3=>0xa0a0a0a0f0e0f0e0000000000000000000000000000000000500000005000000000000000000000f0f00000f0f0000f0f0f0f0f030f0300000000000000000f0f0f0f0f000f00a0a0a0a0a020a0200000000000000000a0a0a0a0a000a00f0f0f000f0f0f0000000000000000000a0a0a000a0a0a00f0f0f0f0f0e0f0e00000000000000000f0f0f0f00000000f0f0f0f0f0f0f0f00000000000000000c0f0c0f0c0e0c0ef0a0f0a0f0a0f0a00000000000000000f0f0f0f00000000f0f0f0f0301030100000000000000000f0f0f0f03000300f0c0f0c0f0c0f0c0000000000000000000000000504050400000000505050500000000000000000000000005040504f0f0f0f0f050f0500000000000000000f0f0f0f00000000505050505050000000000000000000005050505050500000000f0f00000a0f000000000000000000000f0f00000a0a00000000b0b0b0b0000000000000000000000000a0a0a0af000f000f0b0f0b00000000000000000f000f000f0a0f0af0f0a0a0f0f0a0f00000000000000000a0a0a0a0a0a0a0aa0a0a0a0a000a0a00000000000000000a0a0a0a0a000a00f0f00000f0f050500000000000000000000000000000000f000f000f00000000000000000000000f0f0f0f0f0f0000c0c0c0c0f0f0f0f00000000000000000c0c0c0c0c0c0c0c0000c0c00000f0f000000000000000000000c0c00000c0cf0e0f0e0f0e0f0e0000000000000000000000000000000000100010000000000000000000000000f0f0f0f0000000030303030303030300000000000000000303030303020302a0a00000a0f000000000000000000000f0f00000f0f00000000f0f00000f0f000000000000000000000f0f00000f00f0f0f0f0a0a0a0f00000000000000000f0f0f0f0a0a0a0a0000f0f00000005000000000000000000000f0f00000000f0f00000a0a000000000000000000000f0f03030a0a0202f000f000f050f0500000000000000000000000000000000f0c0f0c0f0d0f0d00000000000000000c0c0c0c0c0c0c0c
|1,4=>0xf0500000f05000000000000000000000f0000000f00000000005050505000000000000000000000000040404040000a0f00000a0f000000000000000000000a0a00000a0af0f0a0a0f0f0a0a00000000000000000f000a000f000a00e0f0e0f0e0f0e0f00000000000000000e0e0e0e0e0e0e0e00000000f0f0f0f00000000000000000f0a0f0a0f0a0f0ac0c0c0c0c0d0c0d000000000000000000000000000000000000000000500050000000000000000000000000004000400000000001000100000000000000000000000000000000f0f00000f0a000000000000000000000f0f0f0f0f0a0f0af0e0f0e0c0c0c0c00000000000000000f0e0f0e0f0e0f0e00000000500050500000000000000000000000005000500f0f0f0f0f0a0f0a00000000000000000f0f00000f0a0000000000000000000000000000000000000000f0f00000f0a0000000000f000f00000000000000000f000f000f000f00f0f0f0f0f0f0f0f000000000000000000000f0f00000a0a00e000e000e000e0000000000000000000e000e000e000ef0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0af0f0f030f0f0f0200000000000000000f0f0f030f0f0f02f0f0f0f0f0a0f0f00000000000000000f0f0f0f0f0a0f0af0a0f0a00000f0a00000000000000000f0a0f0a00000000f0f00000f0f000f00000000000000000f0f00000f0f000af050f050f050f0500000000000000000f050f050f000f005050505050505000000000000000000050005000500050030303030303030300000000000000000303030302020202f0f0f0f0a0a0a0a00000000000000000f0f0f0f0f0f0f0af000f000e000e0000000000000000000f0f0f0f0e0e0e0ef0f0f0f0a0b0a0b00000000000000000000000000000000000000f0000000f0000000000000000000000000000000050505050505050500000000000000000404040404040404a0a0a0a0a000a0000000000000000000b0b0b0b0b000b00f0f0e0e0f0f0e0e00000000000000000c0c0c0c0c0c0c0c
|1,5=>0xf0c0f0c0a080a0800000000000000000f0c0f0c0a080a08c0c0c0c0c0c0c0c00000000000000000f0f0f0f0f0c0f0c0000f0f00000f0f000000000000000000000f0a00000f0a00000000505050000000000000000000000000005050500c0c0c0c0c000c0000000000000000000f0f0f0f0f000f00f000f000f000f0000000000000000000f0f0f0f0f0f0f00f0a0f0a0f0a0f0a00000000000000000f0a00000f0a0000a0a0a0a0a000a0000000000000000000f0f0f0f0f000f00f0f0f0f0000050500000000000000000f0f0f0f0000000000000000505050500000000000000000000000005050000e0e0e0e0000000000000000000000000e0e0e0e0e0e0e0ed0d0d0d0d0c0d0c00000000000000000d0d0d0d0d0c0d0c0000000000e000e000000000000000000000000000e000e0030003000300030000000000000000000200020002000200000000000000000000000000000000f0f0f0f0f0f0000f0f00050f0f00050000000000000000000000000000000000f000f000f000f0000000000000000000f0000000f000000300030000000000000000000000000f0f0f0f00000000f0f00000f0f0f0f00000000000000000f0f00000f0f0a0a0000000000005050000000000000000000000000000000000005050000050500000000000000000000000000000000f000f000f0f0f0a00000000000000000f000f000f0f0f0af0f0f0f0101010100000000000000000000000000000000f0f05050f0f050500000000000000000f0f00000f0f000030301010303010100000000000000000303000003030000a0a0f0f0a0a0f0f00000000000000000a0a0f0a0a0a0f0a00000000101010100000000000000000000000000000000f000f0f0f000f0f00000000000000000f000f0c0f000f0c000000000000000000000000000000000000f0a00000f0a0000000000000000000000000000000000f000a000f000af0f0f0f0505050500000000000000000f0f0f0f05050000f0f0f000f0f0f0f00000000000000000f0f0f000f0f0f00
|1,6=>0x500050000000000000000000f000f000f000f00f000f000a000a0000000000000000000f0f0f0f0a0a0a0a
|_,_=>0
def stPool : Nat → Nat
|0=>0x82e0d003008060103300c0406c320c404050090c02f030040082e0b40400c020302c00c040242b01c0400c060082a010030080c0a4040500f0642800c0403c0e09c030100208c220100300806084060500c010200180f0080307c020240c00c1e00c04008190600400809030170100302416054060500c04c120180403c110400603c0e0100d018020300b02803010090200700c04018050080400c0200400
|1=>0x150030100f0505300c040240e0c0030100f148510e4500500c13c030100f0184e00c0401c1b0d4060304a05049010030082e1200301047118020100c00c02114030300903844010020240c028030184303c0203c031081410403010020184000c040081903c030100703c310180f0103f038030083d0183e00c3d008060f003030090380b00c040d40201c06030390503800c040240c03803010370d83501003
|2=>0xc140301b1dc030101b0500c1d803010021d40113c0c01003024141d004018031640f010030080c0186e0100c0181406c6d00c040500f0186c00c041ac0f0502700c1406c0c0186a00c040180203068018030100219c66050060303918c0400c091880c068030100203009180140301b0240417c030100606c34178060301b00c5d1700400c0f018591600c00c1b01857158060501b00c0c154030100603c14
|3=>0x2400603c031081423c140180c06c8e23403010062301b02003010140ac0615003018020300f2180301006008670c00400c0f050892200400c0f0500621c030500906c0c218030101b05034214040180c00c1b210060501b01083208030100c0241a0381400c810248003c060101b00c7f1f8030101b0500c1f4030180f0505402c03010061f00c1a0030101b030371ec03010060507a03c0c0180306c791e004
|4=>0x241401c6703003008a3024030500c0181b02c030100f0ec1406403010090303628403010810500f0641400c0403ca027c040181a06c0327003010060300226c030101403c062681400c0403c06264030180203054110030100c0085126004050970240f1680c00c0401802258030100c05009254040181406c30028030180f03804250030100603c1424c03050241900903c0400c0c2480202403024042440c
|5=>0x2f0040500f2ec060241400c0f018ba2e41b01804030b80540400c060a80200c040187c12c0f0180c06c03050b4050040181b030b300c040e85103c1a00c81024240309000c0400806030b10100f0241400cb000c0403002064af018030f4ae06c0200c062b41b050ac00c040300606cab00c0405009030aa00c0403c14018a9050040240f00ca800c0406ca00506100c040180229c3501003030062900200c04
|6=>0x10020303002414010b532c0f010060501b0c0ca00c040301b324c800c0431c090300800c0406cc6030c500c040680f0247c00c0c06c14018c40500c03c03024c300c0406cb23083b00c042040203098018140301b00cc1010031c802018010500400c0f1188900c14010092800f03002024031e4040080900c0c300030100c2fc310080400c0c0001b1f003010142f80f02403050062f41b03c040500f06403
|7=>0x388030101406ce1380140186b03c040fc03010060305d378030100603c8f374060680f008033700c00c04024a10980303002010db06403204090080c3680c00c020e406364040301b01814360030100903c1435c060500306cd63540600c1b010d4020060501b010d33480400c700080c09c040181b00cd12080301009050d003c1b030040503f09c060500c010cf338030f41b01814334030501b0100633003
|8=>0x10090300e00c040ec9806c0200c0406cb2308d7010033c80903015010140301b00cf100c0c0181406cf00180c06c04050ef030060501b00cee00c0403c02018ed00c250e406030c5018030500c3acec00c04068070240600c0c06ceb3a81b01814030033a4030103a0d802384030181406c043a006030c506c0439c030100611c0f0080403002068033940400c1b01814390030100638c14020060301b00c14
|9=>0x40c03030140181b4080606c0203003078030180c0501b110030101b05101400060301b050043fc03010020240c150060301b050043f8030100c00854064040500c00cfd02403010060201b01c030180c06c043f0030103b024c2008040180c12814134140300306cd63ec04018140301b3e00400c0f024143dc0303002010f60240600c4206c140ac03010460508f3d4140100603c033d0030101a06cf311803
|10=>0x30bf00d17018140101b4591500c140301b4511300c140300406ce000c040081903c030101b28014448040180c06c0344403010144400c03c060500c0101b43c0c0e8090080443803010140243003c030103b06c3519c0301009050b24340306c140304f430040180c06c0317403010140243042c040500303009428060100303c144240400c140190829c060500c06d07418030101b0ed040e804030060501b
|11=>0xc04050e1019260500c06c0434ce00100c06c031fd2500c040180c06d2400c040680201c0900c040240c12c0e0180c06c0434c5d00c3a0681b0112300c3a0681b0112100c060101406d2005003204092e80f0501b03c0600d1f01814030044781300c04050514040f00c060501b0111d00c04030090dc0e00c0c024044700e00c040dc51030a7010140304a0191b0181406c0434d1a00c040181b0ac0701006
|12=>0x113400c0c2041b0513305003010094c80f010030500606d31050394c0060303b00c04008090312f00c0403c1b1f04f00c040180c06d2e00c0403c0212c0900c040500c4b40900c140240c06c0b0180c0101406d2c00c040500c06d2b00c040ed2a0081a0181406c300112900c040181b0300e00c04018020312800c040f4610240200c042c85103c1a0100303c020184c00c060501b01127050060303b2344a
|13=>0x1006050a74fc030180c06c394f80305009030044f40600c0f0083936803010024a86100c041841b4a89000c040e8513840f00c040240f020c500c040181429d3c00c040080903035010b506c140313b010030080c0193a010060301b0513900c040e81b38436030030101b0dc510181406c0c00d380500f06c0900c4200c04024370303500c04018144dc5400c0406c064d8d00180c06c14011350500c06c06
|14=>0xd0030101a03c510240301014031484ac030100f0084f1d4060301b00c1451c030101403009498030100903c14518030180c06d45374030100903014510031bc1b0180c50c030101b0ec31308140301b00d0609c030100906c0c038030100c06c19038030101b0d8460540c010020e8030b8030100c508062c80400c090500c13414024031e40c03c04030060501b504030100900414384030100c19c3a02403
|15=>0xc040180c06c025480301014008060d00f01003030060501b54403010060500f540060301406c0b32803010060301453c060301406c0a02c030103611814008030101b0dc510d0030107c1040c03c3b0683a06c0434c030100603054490030101b068d70e8140301b0180453803010060305d150030101b2fc1a0e803010060305d53003008090300452c1b01006030f7528030101406c0c524030100606c5d
|16=>0x181400c1b58c140100316c0f0184600c04030090500201c030100f29c140185100c04018090305d23c03010140300606d6001014030030181b5740600c1403c1b0e4da00c040506106d2a0100c00cb6008090300400c060501b57006010140301b00d5b010060501b03003568030100603c14150030101406c0c01959010030181b0500c56003010140180c06d5501003050060301b550030181406c3001153
|17=>0xc0406c020180c5d00606c0c03c14011720500400cf20240c2fc0400c0c0501b01971010030197006c140ac030181406c045bc82010030301b050065b8030101406c0c5b47b030030e809008045b01400c810251c030a7050030183b06c395ac0600c140316a06c3900c040301b050065a41406c03019680316700c0406c0f050063d4040500c06c031c82700c040301b018145980400c0c06c060516403004
|18=>0x180c06c146080400c0c0501b01981030030181b0518036c0400cb506c090301500c04018370300f020030101b0302b0185d00c04018140301b5f8030500c0100606d7c018030100c06c0250803010060500c06d7b06c0605004031165e803050240181b0317900c040080903061010032d40903014240030100c06c06051780300301002144090dc060100303c5900c040181b030145d81400c8106c0903175
|19=>0x15003010140080c4000900c04050b21440c03c0600c040319006c02030040501b00d8f6380400c140180c06d8d00c140301b0107d030040501b00d8b14403010060301406d8a0300406c066241462003090020303d0180900c040501b0300661c0400c0c0501b01986010032d4140301b520030100c06c060518501006030c506c0361003010140301b0198300c040180c2fc0223c040305a1bc1b0187c01003
|20=>0x500603003668030180c0101b05199010030301b05006160040180c00c1406d98018030901b0319706c060303b05003078030100c06c021444f00c040181b03014658030188106c0c0519500c04018020304b1500c010031bc021440900c04050240306b0240c00c1406c06024ee01003030060501b64c030103b0241402003010060501b2c83400c04050e103c06144040500900d920300f00c04030090ec14
|21=>0x31a5018030500c19c043b00301081050020312a00c040300923cc5010060301400c1b6900406c0c0500600da3010030181b050026880c00c060516f06c39030040181b00c3a6840c0100606c3a00cd1030040501b018094380c00c1422809010b900c040501b03c06308030183a06c04030d4018030301b19c043a8040300606d9e0506f010140301b0180367404018b50500c06cbb00c060301b0519b0101b
|22=>0xe81b011b46cc0400c0c1683a00809030040188a008036c80c0181406c036c404018b50500c06db000c140100c06c096bc03010060e837030a700c06031610081b0e4060101b030036b40801003030060501b6b0030101b0502b018f505006024040300f2e01b010030180c069aa0180306c1436c0c3ac040500c06c03275a800c040303b4a81400803018140101b031a7030032041b02414698040181406cb6
|23=>0xe87b00c140901b03006704030100c06c06051c00181b05003030e16fc1b01003030140e80000c040501b144b2208030500c06c04019be00c040503a1a43b03c030183b0501b011bd050060301b00dbb0300305002011ba02404018146e41b0300f01003030060501b6dc0600c3d03c1b050db010060501b00c0c6d8040500c06c036a5250103b0683a06c03128040506f0311806c090300400c02019b503003
|24=>0x181b0ec030580400cb50240c0500800c060500406c0c728030180c06c04051c9010030181b0301472003010143680f0180900c060301406c0b00c140301a0181b110040181406c3000dc700c040303b024370080c00c1406c09011c60183a0301a06c0434c030180c0501b011c500c14018e606c0c7100400c0c06c14019c300c040900c3141b0240c00c041d4090dc0200c04018090500c708030101406c0c
|25=>0x11d40300406c14019d3748030100c0181406dd1030030100905002600140103b06c0900dcf00c0403c14384061d40600c0c06c90010da00c040300606cab00c040181406c0c0c403010060301b2fc150101406c032780613c03010140306701809010140301b0180373803010060081b29c6100c040181b03002734030100f0080612c030188106c0c050ea00c040301b044060e8030180c06c04175cb05004
|26=>0x500306c0f018047540301006050b20314c0501b03004018bf0fc030181406cb2011da00c040301a1441b0240c00c8106c14105d9030060500406d167600600c0f008045f414010060301b00dd70100606c4a030141fc030100c06c3b051d600c040301b06806174030102406c02030270500400c0f0188900c04204140301b7580400c6f008090303b00c04018090dc0c2400400c0c5c01b050510501b0180c
|27=>0x24140ac0400c0c0501b019e6050040181b030b8794040180c06c03051e400c040301b0500278c030101a0081b0184600c040301b01809174030100c024020ec4b00c060301b05145190040501b788060311800c060301b01014784030100c13c1b1d47c0501b0180c010367501400c0c0181b234060106f0080c03de00300406c14019df778030100c0181406ddd00c040301419c46024030303d06c06051dc
|28=>0xe80400c70008060303b010140301b00c4a09c030100c06c3b118150300400c1b008067c4030181406c0c03df000c040501b198062c40400c0606c14031ef030030108a0080901003018140301b7b803010060e8b203c1a00c04019ed03c1423c1b0100c018147ac030100c5840201809010031680f050062c8030100603c1412d4c00c040e80906c0c240030100606de90301a00c1b0100c5ac147a0030103b
|29=>0x8060310500c040188a0080c384060100306c0f051fb00c060301b050047e4030181406c04330030101406c06031f700c2406c020180c1900c018140e80306df601014030062981b128140100c0243b00df500c0406c09030461740600c140301b010eb050030100c7d01b024040180c06c03051f30180c06c030500837003010060e87c030a700c040181b0500c7c8030501b0e4060317400c040314d06c02
|30=>0x43003010060301b2f84b00c060ec1a06c0468003010140306709c75010140681b018038181400c060301b0120500c04018142c80c150140100c06c0680c030181406c040d20200c060301b010148040306c140300401a0006c030500c3680652c030101b018140d9ff010030300606c147f80400c064601b0502b00c040e8020240c0d8060500c06c037f0030101b2fc360503a00c04030460508f1040301024
|31=>0x101b0ec360503a00c040181a06c0f0c40306c140116c030e000c040501b384e000c04050b20ec1b03c03010140243a0314c0500606c0f00c4200c040301b2fc148300600c140308b010ec00c040181b0500c82c030101a06ce1018b20181400804030a74381400c0c06c0682a09010030181b030148200600c1406c390320700c040500c06c27410030100c019ec06c0200c040180f0500e00c0606c140301a
|32=>0x1122010030180c87c1b00804018140300306e1d0180c0108e06c14008030100c06c3b0520c00c1b0500436c0c09c0c00c1406c063b803010240180c06c5d018040501b00c1a8680c00c060501b865560100c16c4a018140e803010060500c06e18010060301b00c3b8581400c1b03c0401a13050040ec0f0240327406010030301400a110100c06c038400612c0400c140300606e0f00c040180c06c1483803
|33=>0x101b050030180c898030101b0080c09c3100c040500c06c068940c0101b019d005224050030100603ce300c8106c390500c13c03010060ec36050020500403c1b02403834140180c00c1b10a2300c140301b010068881400c810243d06c0f00c040500c22c060240403014788b506c090101b00c0662c146d8030100c0240e00c04050060301b884030103b03c460508f0300306c1436c06880030ec1a0e81b
|34=>0x30143e54b00c1b018042e40c0541406c0c0192a00e2f00c040180203035030040e81b00e1062c0c0181406cb20108300c0606c148b40c0f4060101b00e100307f030060501b0e8048b01400c0403c464140900c0406e2b0683b00c0406c8f008060d00301002030080180900c06050c70301b64403030090121c0508f01003050060301b8a40c010140080301a27030030181406ddb5bc060500c0101b41cce
|35=>0x12803010060301b1758a00c040300611831008030180c0501b110030100c06c1a0180e00c0403c090ec1412c040500c06c0301a3400c060301406c4b02c03010060301b60c5d06c040680600c3a8a8030180c0101406e3300c040501b0ec6709c040500c00e320187500c060501b0100c8c4030101a06c060053600c0406c06024372080600c2406c0c0099700c060301b010fc00c040181b0500c8c01b00c06
|36=>0xc068f0030101a008e10180900c040ec1b118140200c00c14008048ec0900c040500c0181b8e80c00c040241400a2000c040180c4141453003010060501b0313700c040500c06c19024040500c0180306e3900c14090060301b8e0040180c06c0305237010030181b058148d8030100c1181b0504103003204090e414008030101406c1a01952010062d4140301b8480406c030301401a35050040180c0ed19
|37=>0x380030500c06c06012410180403002068031cc030103a06c0c2fc6700c040181b2c80c0680600c1a03c0201039010060301b05003900040181425c5a06c0f010060301b00e3f00c140301b0112209c030103b03c090500200c060109106c0c240040506f0180c06df506c040180c00cf712c040180c06c0312815050030101b4a80f11803030040181b28403030067b41b0523d00c040180c06c5d010140301b
|38=>0x501b19c2735c03010140180c06e4500c040306b02414008140301b010d30184b0100c06c060503a0fc03010060310505054010060501b00d94208040181b03c1400cb0010060501b00cb6208030501b0240c0114b0181b0500c010ac910060501a06c0f0103f00c0403c1424006024040180c0501b00e4300c040181b0500719c0c00c0606c0228c030101b288140304f00c040500c9081b02403010140301b
|39=>0xc040681b0185135c040180c06cbf00e5100c140901b030069400c0101401a4f06c4a00c04090060301b03803010140ec1b03c35010030500687c1b03c1b0180c0500452e4d00c04050690240c03c03010090500c23e4c010140301b12806000040181b00803030c000c040181406c0c3b40301006050be06c0f00c060501b0100c92c0600c0c06c1a012490180400c140300f91c030100c06c0201a4600c04
|40=>0x180c06c1400e5b0501b0100c34c0696803010140300602548010140301b0180396003010062c837030a700c040181b0080c0c00600c0406c0f020e1010060301b00c1495c030100606c3b2f81a030040181406db900c060301b01014958030100c024146700600c140301b3acda0500303c090ec041901400c0c0100995414010b50245a03c030100c06c0605254010140301b0680394c060105a03dae05002
|41=>0x3c140183b03c1b010d300c0406c3a2c83b068030180c0501b01260018140301b010d397c0306c0c012140185d010030181406c0c978030180c06c048145d00c040501b0e80c3d4030101406c0c0c4f3018030101a0ac1b008040180c06c4a0504c010060303b0501b0280400c140180c06e5d010060301b0ec039440301006050b212c0f00c060301b0123d31403010060501b29e5c010060501b0300305c04
|42=>0x100c0ec090088f00c040181b0300e00c040e8090300f19c030180c0501b12c44050030180c06c04484060500c0101b41d1e010060501b1280c878040500c06c0600e63050060301b010d3988040180c06c0385e1600c040501b0192700c040181a06c0700c040180c4144b008030100c0241b0500700c040301b024143741401006030bf00d19010140301b00c9d38014030033581b0187500c04018140d01b
|43=>0xe6d0500200c060101406c0f198040305a0181b0526c00c04018020301b150140301a06c060126a06c06030140124d00c140301a0101b9a0030181406ca30315300c040180c06c5d12c030500c06c06012670106f008062d40c29c040181406c0c998040181406c039943400c040301b0206709c030181406c0c7c00400c1406c060326406c030e804068da0ec030101b024140310000c040180c0508f37803
|44=>0x540600c0406c1a384080101400d1803c1b02403010140180c06e7600c040501b0180c9d4030101b03c060d81500c040301406e619d00400c1406c064c4040327306c090506f00c040301b4a8142f8030101406cb203027010060301b050039c80306c040300605270010060500306c0c9bc03010060500c03d4c00c04018020300f0c4040181400cc006c0f0100600c0c1cc02010060501b00c9d9b8040180c
|45=>0x180c06e7f010140327e06c06024030181406c040ea7c00c040180c06c14378030103b0e80203c03010020180c00536018040504a06c0c9ec030100c0501b01a7a00c060301b010149e40301014030060267801006204140301b2ec030101406c1a018d700c040e8020240c29c03010140700f018bf00c0403c1b0241431403010140314806c7500c1b03014010069dc0c00c040241b0518000c0406c750240c
|46=>0x180ca18030100c0181b0528500c040500c06c0609c030100606c0c12c0e00c04030640241423c030100606c140ed00010060301b0513901003030063dc1b23c1400c040181b2fc360180400c0c0501b84403010140180c06e84030060522b06c0434c0c00c0406c371440400c1ba0c06030c500c0406c3b4143a068030181406c040328100c040180c06c5d3b4040301a0181b00d8f018140304aa000301014
|47=>0x3003018140e63e00c04018020301b4bc03010141a4410300f00c0403c1b0080612c040180c0501b1500a010060503a00c1b0a8060101a0080f00de0010140301b00c06a2c040181406c0c00e8a018030101a22c0203c030103b06c0905289010030181b0500ca201400c8106c090328706c060301412c04934030100c0501b9a0030100606c3a0d01a050030101b0d8bf118030103b0241423c2b010030501b
|48=>0x6c020180c3e403010060301b4141500c040501a06c09004030101a0080f018bf00c0c0528f06c062e403010060301b1748f010060301406c543280400c0c0181406e8e05003011050240f00c040181b0041412c03010140300660d4c00c040e81a06c0f2fc1b0180c0101423a8d00c04030670e80900c04018144fca7010060301406c03028040180c06c030528c00c040501b0240c3b4030101b0e8410301a
|49=>0x515200c0406c0f01814148060500c19c1b010d300c040180c0ec54008030103d06c060525c00c040183706c0c0200301006030bf17402010060301b00c14a4c0600c1a0081b0116b00c04018140301b1a4040180c06c0305292018040500c06c4a6a40600c140300406c6700c040501b068e109c030100c06c090380c00c040181ba44040180c06c140093900c040180c0505460c040180c00e900500200c04
|50=>0x301b01014a60030180c06c040529700c040ec3a0081b03c030100603014150ed00c040ec1b050410ac030101406cb2030d700c040180c0514c3b4030101b2fc1a0e8060301b010d3050c500c040901b0180c01c0400c060500c06c4d010060301b00c14a58030500c06c060129500c040180c050bf3780301006030bf0508f010060301b00c14a501400c0406c3b0052a00c040500c06c1a09c03010060301b
|51=>0x6c061d47c030030503a0241b01039018040305a1281b05002010030301b780060503a0180306c140302b0129b030030101b1f04100c040180c06c5403803010060301b23c0700c040181406c690d00c0181406c3a00cee00c040500c06c06a6803010060301406c5400c040501b0e83435c030103b06c0f0502700c040500c0181b530030180c0500406e990500c03c040180934c0301006030144160e00c06
|52=>0x6c020180406c0c0509000e9f00c14090062041b030a700c040501b0e8b20303b050030180c06c040ee9e00c04050061040c29c060101b0500c00e9d00c140301a06c060111c030040181400c1b58c1400c0c0121406c06024060106f06c020305a0180400c0c06c1400a9c00c140301a06c04019b4018030100c6441b0500200c0c0101431c1b02404030030181406d5c050030100c06c060260500c040301a
|53=>0x508f0300400c1406c06a8003010060501b2c834010030500c2941b0187500c040180c06c140ecd700c040180c0501b6280c0101b01809050036200c010060503a2d81b12803010140301b0198300c040180c06c1401c060100c06c02068031c8030101b018141d40c3401b00c0403006050dd050040180c06c036f00600c040501b0688b0ac030100c0184606c1423c0c00c040901b008061440600c040308b
|54=>0xc040183a0081b0300f018040500c06c03a8c0c0101406c031280614406010030301b052a2018040305a06c148a00400c060509706c0c03c030101b05006031000500306c06010b9030bf0100c06c030189d051a10180400c6f06c020306700c060303b06c14011450500406c0303006a840c00c14008040e4060240600c0c06c14008db5b0030101b030064a8145b403010140301a22c060240600c040f40f
|55=>0x5f41b018090500306c060100c471750180306c14030042b0040183a0301a06c03274060501b03003a9c1400c040ec0f024030102406c020180c0ec1400c040181b4140100c060301b01122050c500c0406c1403006930060101b0500200c0ca981400c060301b0ec04a94060301b0101434ea401803010140701b03c0600c140314006c040e41400c062041b031c400c040501b500060ec1b010060301400d4a
|56=>0x500c0681b00c060301412c0452c030101b03014240061ec0600c1b0300f010143a8140101b018036240c2fc0400c062d4140301b50003010140681b03c062fc1b01006032730506f06c040180c0ec03050f700c140100c0181baa403010060501b0303100c040180c06cbf054140100c0ec1b00d8b050040180c2fc1b00c4a018030100c03c08008030101403067018090180406c03052100309e00c1403004
|57=>0x6eab018140e81400c040306b024060100c03c036b8140080301006204140681b03c03010060e802030a700c040501a03c1b01875030030181406cb2011db00c0406c060240c1740c00c1b0181401037698030100606c0f050c500c040180c06c3b0540600c0c06c39051a00300306c14010db0185106c0400c0c01814aa80c00c040181b051800101400c064601b03c0400c0c1681b018140dc030188106c39
|58=>0x10062d4140301a1c8140101b0300600c46ab41400c040301b01a0500c04050061440c03c03010140301b068063b403010060301b0ecbf17414010060301b00eac05003030042880900c040500c06c061d504018030500c06c043ac1400c060241b0100c5ac03010140195606c0c29c030180c0528f06c3900c040301a06c06024b2018030500c7303900c04050240300f018750500400cb50240c03c0400c0c
|59=>0x501b00c4a03061030030183a06c04489a000c040181b288140301a0500301809010b90300f00c0406c1403067018b2018140300f06c03370060100c051b206c4a00c040301b0ed050503a00c04018148ac1b0300f018040500c00c1bac00c010062d41b052af050040181b00c9d03036050040180c06c030ee1700c060503a06c0403282030030101406eae00c0403014020061d40400c0c1681b050061041b
|60=>0x500c22c060240600c0c0681b0080436c14010060301b00eb6050030100c06c06ad40c010060501b0e8036501b00c060500c012b400c0406c06050370303600c040180c0ec1406d4c0180c0101406d0e06c030100c018140eab30500306c060111c03036018030101406c0c03eb200c040180c0501b12d830180400c1406c0c03e48018030103d06c140ac0c00c040181406cb21a4040300606eb10506f01006
|61=>0x18040305a06c1400a2800c040180c0ec1406c5400c0406c140080603100050030308106c09470040500c00d5e06c061d403010060501b0e80c0d003010060301b2fc14174030101b05002018b20d01400c06030bf06c044880c00c060e81b008045b003010060501b0300f97003010060301b0500260c14010030301b01ab700c040180c06c1400807018030500c06c67010da030030181406cb20116f00c04
|62=>0x2c80c06803010140080c19c060240c00c040181b0e837018040500c06c03ae40c00c040181b28403010060301b174060101b00c0c0507f0500306c0c03c060128700c040181406c0c4dc03010060303606c1400803010060501b0303a5b40301006030c506c8f0500406c030309e01a1703003010140e86906c09050030101b03c064a803010060501b030a7ae00301014090060301b1ac03010060ec1b05008
|63=>0x30030195f00c0406c0c0506701846010060301b00c9d0504b0300400c0606c14ae80601014008036c80c29c1400c040ec1b03c4600c0406c0c0181411a0c018140301a06c03370030100c0f4060501b2c80c00c060501b011f800c0406c0c03c1401827050030101b1d409030bf018030301a0081b0112200c040500c06ce0030030101406c068ec0c00c040181b05220050030101b03c062fc3600c040181b
|64=>0x3c0c010060501b6e414010060303b00c1b7d40301014008061440c03c030100c0683a06c090180406c03052100307e0180400c0c06c141640600c040f40f06c1400806010140300f6b81b128060101406c0c781ae050030301b0240487003010060ec1b0502b06c04018b50500c1c814030030181b4300600c140301b22c043680600c040680f06c0200c040180c0ec4b06c0200c040181406c0c3b41b01014
|65=>0x37c3f00c040180c06c0e050030180c06c0448c1400c060301b01121030030181406c0448abb018030500c0681b0e52200c04050020300f0187501803030240081b0e40600c0406c02030e122c030100c0f4060241400803010060503a2c80c29c060301b050020110e030030181406c0428c030100c068020180906c030303b050040e95606c0400c060500c0684c030030100606c3a1f01400c06024044880c
|66=>0xc060500c1300600c040501b068673840600c140301a0101b9a403010060306b06c14008030100c0186406c1400803010060501b0325c00c060e80c0681b01039018140301a06c040e4d30300406c1400c0693c03010060301406c4b3b403010060303b4141423c1b00c06030041901412c030101b05002030e000c040181b03c3b0504b050030101b018092fc3600c040300f018141d47c0181406c0c03c04
|67=>0xc040501b0240c12c03010140301b0182700c0406c06024142c88205003010091d40c03c1b018140300441c1400c040181b2fc36030030101b23c020185106c0400c140180caf003010060301b0519c0100600c0c0501b8440c010060522b06c032741b010032d4140304f00c040500c5001b01875050030180c06c3b01238018040300f00de00508f00c04018141a41b0300f00c040500c06c1a019d606c04
|68=>0x50040180c06c4a46003010060e81b0080c3841b00c0405006032bf06c040180c0504b00c4c00c060100c0501b9a406010140301b9f803010140301b018093080600c040300f0201b00803010140306706c06024030100c03c062fc1423c03010140080c0192a00c0406c0c050900192a030030181406c04af806010140301b06803af403010060301b051052f803010060303b06c0223c030100605069030a7
|69=>0x52c0600c0406c020300800c040180c2fc1423c03010140301b0682700c040180c06c1454803010140301b06867380030101b0180c050363080c00c040181406c6901803010140301b19c030100606e2e0500c0681401003031e006c0602403010140301b19c0660c1b00c04018140317f0100c168141bc1b01809010030305a0181406c6900c060301b010390504b00c040180c06c147e803010060301b052c0
|70=>0x803010060301406c4b1500301006030bf06c1423c03010060301406c4b53003010060301406e6100c0401809050020300f00c040180c0501b15003010060301406d4c00c040181406c0c0c003010140081b030064a803010060301bb040c00c060501b011229f403010060301b0ec1460c1b00c040ec1a0e803010060501b1a40c12c0301014008061440c29c03010140301b19c0612c1b00c060303b05004
|71=>0x12c1b03004018140e8032d81400c0c06c04019b4018030501b030048500600c140103d06c0f018140301b010d3050040180c0ec1b00c4a03003010060241b05002018030301b01014489a0050030101b0180c0d80c010030506f06c060241b00c040500c0680612c060100c0506f06c4a030030101b0180905037050030301b018090111c01803010140080c29c0600c0406c0c050a724003010060303b2fc14
|72=>0x18b50500c0681b00c040183b0501a05003030040181b288060100c0500206c032741b0100c00c060509705003010060301b1ac0600c040502406c0c29c1b00c140100c01864018040501b00c0c6940600c04030a70508f018030500c03c1b0103905003010060ec1b03c060100c06c1400d84050030180c0ec1b01122030030101b050061041b018030500c0117d018030100c03c1b0508f06c030100603014
|73=>0x5003010060240c03c03010060503a06c0c03c060101400c0c06de000c040500c0681b0187506c0301006030143140c00c040181406c6901803010140301b19c060100c00c1406e83018140301b0103934c060101406c0c03c037801b00c140303d0188103003010060501b0e8b201804030030501b7881400c040180c06c3b4140600c140301b0e522018030101b0300f0506703003010060501b8ac1b01003
|74=>0x1b01803050040301b05003010060303b018030500c06c040e40600c140101b030a7018030300406c140081b01804030030506f018040500c06c032741b01803050040301400c0c0101b02475
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>0xfa503d540f0503ad40e65038540dc5035d40d25033540c85030d40be502e540b4502bd40aa5029540a05026d409650245408c5021d4082501f54078501cd406e501a540645017d405a5015540505012d404650105403c500dd4032500b540285008d401e5006540145003d400a5001540005
|5,0=>0x9dd4271609ad82656097d82596094d824d6091d8241608ed8235608bd82296088d821d6085d82116082d8205607fd81f9607cd81ed6079d81e16076d81d56073d81c96070d81bd606dd81b1606ad81a56067d81996064d818d6061d8181605ed8175605bd816960591415e60561815260531814660501813a604d5412f604a5812360475811760445810b6041580ff6
|5,1=>0xfcd83ed60f9d83e160f6d83d560f3d83c960f0d83bd60edd83b160ead83a560e7d839960e4d838d60e1d838160ded837650dc1836a60d91835e60d61835260d31834660d01833a60cd1832e60ca1832350c75831760c45830b60c1582ff60be582f360bb582e850b8982dc60b5982d060b2982c460af982b860ac982ac60a9982a060a69829460a39828860a09827c6
|5,2=>0x15c1856a61595455f61565855361535854761505853b614d5852f614a5852361475851761445850b6141584ff613e584f3613b584e76138584db6135584cf6132584c3612f584b7612c584ab61295849f61265849361235848761205847c511d98470611a9846461179845861149844c611198440610ed4435610bd84296108d841d6105d84116102d840560ffd83f96
|5,3=>0x1bbd86e961b9146de61b6186d261b3186c661b0186ba61ad186ae61aa186a261a71869661a41868a61a11867e619e18672619b1866661981865a61951864e619218642618f18636618c1862a61891861e6186186126183186066180185fa617d185ee617a185e26177185d66174185ca6171185be616e185b2616b185a661681859a61651858e616218582615f185766
|5,4=>0x7e561f7d87d961f4d87cd61f1d87c161eed87b561ebd87a961e8d879d61e5d879161e2d878561dfd877961dcd876d61d9d876161d6d875561d3d874961d0d873d61cdd873161cad872561c7d871961c4d870d61c1d870161bed86f56
|6,0=>0x2679c99772641c98972609c97b725d1c96d72599c95f72561c95172529c943724f1c935724b9c92862485c91a7244dc90e5241dc900723e5c8f2723adc8e472375c8d67233dc8c872305c8ba722cdc8ac72295c89e7225dc89072225c882721edc874721b5c8667217dc85872145c84a72111883e620ddc830720a5c82362071c81572039c80772001c7f971fc9c7eb7
|6,1=>0x2d65cb5272d2dcb4472cf5cb3672cbdcb2872c85cb1a72c4dcb0c72c15cafe72bddcaf072ba98ae372b71cad572b39cac772b01cab972ac9caab72a91ca9d72a59ca8f72a21ca82629edca74729b5ca66729818a5972949ca4b72911ca3d728d9ca2f728a1ca217286d8a1472835ca06727fdc9f8727c5c9ea7278dc9dc7275989cf72721c9c1726e9c9b3726b1c9a57
|6,2=>0x3449cd0b73411ccfe633ddccf0733a5cce27336dccd4733398cc773301ccb9732c9ccab73291cc9d7325d8c9073225cc82731edcc74731b5cc667317dcc58731498c4b73111cc3d730d9cc2f730a1cc2173069cc1373031cc0572ff9cbf772fc1cbe972f89cbdb72f51cbcd72f19cbc062ee5cbb272eadcba472e75cb9672e3dcb8872e098b7b72dd1cb6d72d9d8b607
|6,3=>0x3b31cec573af9ceb773ac1cea973a89ce9b73a51ce8d73a19ce7f739e1ce71739a9ce6373971ce5573939ce4863905ce3a738cdce2d63899ce1f73861ce1173829ce03737f58df6737bdcde873785cdda7374dcdcc73715cdbe736ddcdb0736a5cda363671cd9573639cd8773601cd79735c9cd6b73591cd5d73559cd4f735258d42734edcd34734b5cd26734818d197
|6,4=>0x4215d07e741ddd070741a5d0627416dd05564139d04774101d039740c9d02b74091d01d74059d00f74021d00173fe9cff373fb1cfe663f7dcfd873f498fcb73f11cfbd73ed9cfaf73ea1cfa173e69cf9373e31cf8663dfdcf7873dc5cf6a73d8dcf5c73d55cf4f63d21cf4173ce9cf3373cb1cf2573c79cf1773c458f0a73c0dcefc73bd5ceee73b9dcee163b69ced37
|6,5=>0x48f9d237748c1d22974889d21b74851d20d74819d1ff747e1d1f1747ad91e474775d1d67473dd1c874705d1ba746cdd1ac74695d19e7465dd190746299183745f1d175745b9d16864585d15a7454dd14c74515d13e744e19131744a9d12374471d11574439d10774401d0f9743c9d0eb74391d0de6435dd0d074325d0c2742edd0b4742b5d0a67427dd09a5424dd08c7
|6,6=>0x4fe5d3f274fadd3e474f75d3d674f3dd3c874f05d3ba74ecdd3ac74e95d39e74e5dd39074e25d38274dedd37474db5d36674d7dd35874d45d34a74d0dd33c74cd5d32e74c9dd32074c65d31364c31d30574bfd92f874bc5d2ea74b8dd2dc74b55d2ce74b2192c174ae9d2b374ab1d2a574a79d29774a45928a74a11927d749d9d26f749a1d26174969d25374931d2457
|6,7=>0x56c595aa7568dd59d65659d58f75621d581755e9d574655b5d5667557dd55875545d54a7550dd53c754d99530654a5d5227546dd51475435d506753fdd4f8753c5d4ea7538dd4dc75355d4ce7531dd4c0752e5d4b2752add4a475275d4967523dd48875205d47a751cdd46c75195d45e7515dd45075125d442750f19435750bd942875085d41b65055940e7501dd4007
|6,8=>0x5da1d76175d69d75465d35d74675cfdd73875cc5d72b65c91d71d75c59d70f75c21d70355bf1d6f575bb9d6e775b8596da75b4dd6cc75b15d6be75addd6b075aa5d6a275a6dd69475a35d686759fdd678759c5d66a7598dd65c75955d64f65921d641758e9d633758b1d62575879d61775841d60a6580dd5fc757d5d5ee7579dd5e07576995d375731d5c5756f9d5b77
|6,9=>0x6485d91a7644dd90c76415d8fe763ddd8f0763a5d8e27636dd8d476335d8c6762fdd8b8762c5d8aa7628dd89d6625d989076225d882761edd874761b5d8667617dd85876145d84a76111983d760d9d82f760a1d82266071981576039d80776001d7fa65fcdd7ec75f95d7de75f5dd7d075f25d7c275eedd7b475eb5d7a675e7dd79965e49d78b75e11d77d75dd9d76f7
|6,10=>0x675999cf76721d9c1766e9d9b3766b1d9a576679d99776641d98976609d97b765d1d96d76599d95f76561d9517652d9944764f5d936764bdd9287
|7,0=>0x6eeddbb386eae1ba476e75db9586e39db8776e01db7886dc5db6986d89db5b76d4e1b4c76d121b3c86cd21b2c86c95db1d86c561b0d86c161afe76bdddaf076ba21ae086b65dad186b261ac276aeddab386aae1aa476a75da9586a361a85869f9da76869ba1a668697a1a5776941da4886905da39868c9da2a8688a1a1a8684dda0c7681219fc867d219ec8679219dc8
|7,1=>0x765a1d9067625dd81875e61d71875a9dd637756e1d5387531dd46674fa1d37774be1d2787481dd18874499d0a8740ddcfb873d59ced873961cde7735a1cce8731ddcbf872e1dcb1772a9dca28726ddc9477235dc85871f61c75871b61c65871761c55871361c46770fa1c37770c1dc2977089dc1a8704ddc0c770121bfc86fd21bed76f961bdf66f659bd186f29dbc28
|7,2=>0x7df5df7587db9df6777d859f5b67d51df4c87d15df3d87cd61f2e77c9a1f1e87c5ddf0f87c1e1f0077be21ef087ba21ee177b661ed187b261ec187ae61eb187aa61ea187a69de9287a2a1e82879edde73879b1de65779761e567793a1e46879019e38878c21e28878821e1887845de0987809ddfa877ca1dea8778a1dda8774dddcc777121dbc876d5ddae7769a1d9e8
|7,3=>0x856e2154785322144884f5e135884b6212588479e1168843a2106883fa20f8683c5e0ea7838a20da8834a20cb7830e20bb882ce20ac78295e09e7825a208e8821de07f881e5a071881a620627816a20537812e2043880f1e035780b9e02778085a01988049e00a8800ddffc77fd21fec87f95dfdd87f59dfce87f1ddfbf87ee1dfb087ea21fa087e699f9377e31df848
|7,4=>0x8cee233568cb6232588c7da31788c3e230788bfe22f878bc5e2ea78b8de2db88b4e22cc78b15e2bd88ad622ad88a99e29e88a5a228e88a1de280789e5e271889a9e2628896de255689362245888f62235888b9e2268887de2178883e220788801e1f9787c9e1ea8878de1dd68759e1ce8871de1c0786e5e1b1886a9e1a28866a21928862a2182885ede173885ae21638
|7,5=>0x237f88dde236f88d9e236078d62235178d29e3437
|8,0=>0x9401e4f9793c624ea7938a24db79351e4cd79319e4bf792de24b0792a224a17926624927922a2483791ee2474791b5e46589179e4577913e244879105e43a790ca242b79091e41c89055e40e7901a23ff78fde23f078fa5e3e278f71a3d488f3223c488ef5e3b588eb623a678e7a239688e3de3878
|9,0=>0x2530794a5e5227946de51479435e5076
|10,0=>0x25376
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 706 then fld (dictB (i / 512) (i / 32 % 16)) 188 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 10 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 18 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))

def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 11 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 1 zs)
def opPool : Nat → Nat
|0=>0x1c00c41b05106c6f00305119c06c0f05106c0c41b0ec0180c40f1a706c0c41b05106c3ac060510940c40203106c1441b0900101446500d06c6403b01106c0440603102461c3a03306c0641b0510181440616516c1441b03106c5a00303103c3a01b0310083b01b0510500640c0191340441b13012c0343b05106c034060310083b01b05103c3a01b031030064140190980c40208c0940641b05106c240040510740c4020640700641b05106c1a00c051
|1=>0x18a540c1be00c144020310083b01b05106c0640c0190244b03b05106c0641b0310180c4a20510240cc1b01906c810040190e89e00c27506c03c0c0510181440e0131ac1441b03106c3b0060310086401b05106c0c40c2050100641b12c0680640c22d06c1ac140310308a40203106c1441b0e80181441422616c0641b03106c5a00303106c0c4040da0240cc1b0190100640f1a706c0c4141a506c3ac0605106c0c47305106c7201416900c0c47101b
|2=>0x6c1440405119c3bc0f05106c0c41b0190300641b0311f00cc141d502406c1b01906c0c4091680300341b01900c06406031030378b205306c3a4060510307541b01b06c1441416900c0c41b051050468bf01b06c3b40c0190640341c01906c0c41b0680500c4090110243d01b01906c0c40403106c1440c2dd06cb60142d500c0641b0310e80c4141a506c3ac060510500c41b0312c806c1b0e9050064230310940641b05106c2400405106c1441b298
|3=>0x180c40c35d018d74020ef06c1440c0191500641b12c0680641b0510301441b0510241ac1b0190180c41403106c4c04b00d0ec1441b00d0180c4fa00d06cf90810690500c40401903c06c0602103c14c1b0310500c41b0190083b01b0510500c40603106c1441b031030e6406092010144df00f03c0441b03106c3b00603112804c1b00d06c1441b0310500c4092842881441b01906c810040190700640201106c1441b0680301440909006c0641b011
|4=>0x6c61c0c0ea06c0641b0510181441403106c1440641506c3bc0c0190500c41b0312c806c1b0e90500641b00d0111941b4600ec034060310084b03a03106c1441b0190500643b48906c04c06031030144060511ac1440901306c0641b0ec0300651905106d1803b00d06c3b40603136c03c0201106c1441b0190500640f05103c3a01b031030064140192880c40905106c0641b204010064090c02280c41b01906c3a014019050064010510310541b0ef
|5=>0x185d8bf05306c3b40c0190084b00c0e906c1441b019050064540511500641b12c0680640c051024b603a00d06c0641b051018144020190081cc1b05106c1a00c05106c0640605106d4041b06a030144144860ed2243901306c044060310680441b01106c1441b0310500c41429d018a741b0330e80cc1401903c3a01b03106c0641b0510181446f4a8018a741b03306c144030510240cc0203306c1441b0190500640603100c2541b01106c24004051
|6=>0x6d5fc0657906803c140310680441b01106c0c414031018a741b0330e80cc1401906c0641b051050b54030192754041b00f06c1a81403106c4b03b05106c0c4060314a82440629d06c0cc0405106d57156033018244040511ac6f81b0ec0180c4030510c00448a03106c3a0060510ec8f40205306c1440603106c0c4b20330080641b0510e403c1b011018144140310180c406051018e186703306c1a4140310181441403106d4d41b0ee0180c40c176
|7=>0xec2480603106c144040515cc03c0402103c14c1b0310240c41b01906cb50030195b406c3a29d06c0cc1401900804c1b05106c064140190312243901306c0440603106c0440450106c1a8140310f45100201b06c14404031030dc40637112804c1b00d030f380602103c14c1b0310e965c0605106c5a80303103c06c1b03106c5a0030310083b01b05106c0640c01900806c1b05103c0cc1b03106c5d0bf0530240c41b01906d62c0658503024804051
|8=>0xc3740905302403c1b01906c0640c01106c1440405106c4f40606a0500c4030192e8144090f406c0640403100814c1b05106c3b4060310080440220406c144040192fc1400903106c0640301903c14c1b03102414c1b01906d7fc8106a0500c40401906cf60065f506804c140310081cc1b05106c1a00c051031168032450e804c060510e80cc1b01906c1440605102414c1b01900806c1b05116c1441b03106c5a003031051774b903306c81404019
|9=>0x2400441429d06c0cc0401906c4b03a03106c1440605106c0640201b06c1440305106c0641b0ec0300640405165004c091bd06c0640305103c14c1b03106c0640c0192c882cb203006c3a40605100806c1b0310080cc1b05106c4b03b05106c0640c01906c0640c14500806c1b05106c0c4b201b06c3a41401906c1441464506c3d80403163c06c3a27506c03c140192fc6f81b0ed0180c40305163006c1a48906c04c1403100806c0627506c03c1b051
|10=>0x6500c0022d506c1440301906c044b201306c3a40605163c14c3a27506c03c0605165014cb200d06c3a40605136c03c1b01906c244040510240441b01906c3a0140192fc1ac0f01906c0c4140316800cc1448906c04c0605167c14c6701106c1a40c0510698900900f06c064140310700341b0680500c4030190119c43b23c06c14c060310185945b05106c5a0030310083d00c01106c144040510114a44b00f0ec1440603106806c0201b06c1440c051
|11=>0xd4041b06a0500c403019024adc1b0190308180401906c0ccb205306c3a40605106c0441b0510302480405103c14c146b903c03c1b03106cf75180530185a4030315480cc2b0190308f41b0532e403c1b0310240441b019051ab4b506b0301440301919c04c020310080441b0516a406c1a27506c03c1403106c1440641506c3bc0c0190103780905306c0640401967c1bc6701106c1a4140310ec14c1b05306c0640c01900c7b49001b050a741b033
|12=>0x2c8a7c1b0330241441b0195b406c3a29d06c0cc1401913006c5a0e9050064030312c80c0b201b06c3a41401906c0c40c01906c3ac1401906922c1b0130500c4060316f004c0341506c3bc0603106c0640414500806c1b05106c0c48a00d06c3a00605106db845a0e8018144030310080441b05106c0c40403106c034060510500c4060310246f01b01906c144030516d014c0648906c04c1401906c0641b0510181440303100803c1b05106c3a006051
|13=>0x6403c1c01906c1a0140310303a81b03306c1440605100861c3a03306c144060510680641b05106c0c414031018145cc05106c3d0040310105d8bf05306c3b40603103d1803b00d06c0c40603112d2203b05106c04c0603106c0641b031030244040511500441b12c0ec144060311500481b12c068064140310c003c8a03106c3a0060510e403c1b01103014406051010a741b033018248040511045a00623d06c14c0303106c1440905302406c1b019
|14=>0x509e80c27512803c1b00d018ed41441606c3bc0c01960c14c6701906c1a40c05119c06c0203106c1440405116c0641b03106c5a0030310188b41b06b0500c404019050a741b03302414c1b01900dd58040d90240cc1b01974c03c0314500806c1b0510088101b05106c064040197400cc0900d06c0640c01906c06c6703303c1441b0310680441422d06c1ac0c0510506541b1900183d40403160c3acb203106c3a40605106c0641b50106c1a814031
|15=>0x60c14c0906906c0640c0510503b41b05106c0640c0190ec0440423d06c14c060310507541b01b06806c0c0510111941b4600185a40303103c0341b03106c1440305100c4184100d0188f41b0532c83d01b0e90181440403106c0640f01b03c1441b0310e43ac0605106c0440403160c1bcb203106c3a40605176c0ccb201106c3a40605106c0640201b06c1440c0510104180623d06c14c0401906d164032450e804c0605106804c1b05106c0c414031
|16=>0x7401a01403106cb540301906c0641b05106c3a0060510500c41b03106c3a41401906c14c1b0310183d80403100dec43d0ea0181440403106c0641b051030248040510080641b05106c0c40303106c4b83b05106c0c406031050a741b03306c064140190500c4147a906c81c040196300616b0510312241b0130308f41b05306c0640c019025e7c1b0190505a803031030b88b900f06c8140401967c06c020f506c1440403103c06c1b03106c1440c051
|17=>0x31f843a48806c04c06051010b741b2d80e80340605106c034062950306f80305106d1883b00d06c0640c0192fc14cbf01b0240c41b01906c064df01b06c3d40403106c0cc141a506c3ac060512881a81403106c810040190903bc0603106c044040510181441b05106c3b80c0190180c41b05106c6f00305119c06c1b00d06c1a4140312fc140bf01b06c3b40c0191bc5100201b06c144030510d40480f0e806c0c4060511980642503106c24004051
|18=>0x318940900f06c064140312fc0441b53506c3b80603106c4b03a03106c3a40605181003c3d1d506c06c04031010344b203306c3a40605112c04c1a01906804414031030c24140da0240cc1b0190091801b0510185a4030310308f41b053030b54030190240cc1b01906c14406051011fd41a27406c03c14031018144bf03306c3b40603106c3bc0603106c144040510080cc1b05106c3a00605119c5ac0f05106c0c403031011fa81453506c3b806031
|19=>0x18144bf03306c3b40603103c3ac1b0310301440605119c0606703306c1a41403106c0c40c01906c3a41401906c4b83a03106c064140190120d43b00f06c0c406031050464bf01b06c3b40c019204e140203306c144040190080640203306c1440c05136c03c1b0330080441b05101a0a5e001306c5a403031010e180203306c0441b0511ac1441b03106c3b0060313c80441403106cb50030190503b41441506c3bc0603106c2706701b06c1a414031
|20=>0x6c14c0f01b06c0c4060310105180201b0080441b05106c04c060510500c40603106e1e0031850e80cc0605106c144038710ec04c06031050464bf01b06c3b40c01919c06c020310080441b0512fc14c1b0ed0180c4040510321b44a06b06c034140310e8044041a506c3ac060510181441b00d06c5a00303185c14c3b27506c03c060310321580685103c04c1b03106c03c1b01906c0c4060318481bc0216906c1440303100905c1b05106c3bc06031
|21=>0x2c80cc0201900814c1b05106c064670530080c41b05106e2acb60330186f4030518a075c1b01b0080341b0512c804cb201106c3a40605106d07c035f506804c140310502786701b0080c41b0510241cc1b01906c1a0140310518940900f0240341b01903c6bc1b03106c3b0060310181a81403106c0440401906c144bf03306c3b40603100c3b81b01906c0c40603106c0641b07306c1a01403106c0640600d06c6f8030511ac1441b01906c3b00c019
|22=>0x1500441b12c0ec1440603160c14cbf05106c3b4060312d80cc030e90181440c05119c06c0603106c1a4140310500180c1d506c06c140312c80c0b20530241441b0194841403b48906c04c0603112c04c4b0110ec144060312fc140090310240441b01903c3a01b03106c144060510189d41427506c03c060510100c4148b906c818040196a414e100310509d41b00f00e198041a506c3ac0605106c0640c11a03c06c1b0310300641403106c3a806051
|23=>0x6c0640203306c1440c05103c14c0f01b06c0c40603106c064db01b0080441b05100881c1b05106c0640401906c1941c01906c1a0140310110541b0ef0180c40405105814cf203106cb50030190188f41b05303c06c1b03106c1441b01106c064040190ac0640c22d06c1ac1403119c0341b0690500c40301906c0341b4600ec0340603106c5d4bf05306c3b40603106c1441411a03c06c1b0310084b01a01906c1440c0510ec1441b01906c0c406031
|24=>0x6c0640650106c1a81403119c0601b50106c1a8140310102746701b06c1a41403106c7201a00d06c1440c05103c1440f01906c0c4140190301441b8ad06c3a80605106c0441b05106c0c4140310edb240200f06c1440603119c06c1b01306c1a41403106c1441b01906c0c40603106d188030ed0180c4030510ec145180530ec034060312fc1401b00d06c3b40603103c06c0629d03c0cc1b0318f81441b558050814040192744fc1a01b06c03c14031
|25=>0x524a40422e06c1ac0c05106e4840f1be06c0c4030510685100201b06c1440c0510302786701b06c1a4140310910541b0ef0180c40405106c1441b01906c3b00c01937c03c0605106c3d40403106c4b03b05106c3bc060312c80c0b200d06c3a4060512c80c03a00d06c3a40605100cac8043850080cc1b05137c03c0f01106c0c41403106c0641429d03c0cc1b0310080c4020ec06c144060310108a41b05106c3a0060510181a81403106c81004019
|26=>0x24a2c1b01906c8100401906c0c40c00d06c0640301984806c6700d06c1a41403106c1440f00f06c0c4030310305180201b06c1440c051948140bf00d06c3b4060310104640f01b06c0c40405106c034066c900803c1b0511ac1441b0ec0180c40405103c3a01b0310300641401906c0c40c9390186f80305100d4b44b0130ec1440603106c0c41b01906c3ac140190ac06c0c23d06c14c1b0191c806c1a00d06c0341403106c0c41441506c3bc06031
|27=>0x183140f0eb06c0c41401906c1440c22d06c1ac1403112c0343b05106c034060311500341b12c0ec144060311ac6f41b0ec0180c403051948140bf00d06c3b40603106c0c43a03106c3a4060510ed84c0323d06c14c0603106e5940906a06c0641403106c0ccb205306c3a4060510308a41b05106c3a0060510500c41441506c3bc06031128b603a00d06c034060510ec8f01b05306c0640c0190101a46701306c1a4140310ec0441b01906c0c406031
|28=>0x6d070035f506804c1403100c6143a03306c0340605185c14c3b27506c03c0603176c0c00909106c064040510083b01b0510500c40603106c1443b05106c3bc060310083b01b05106c0640c01906d1803b00d06c3b40603119c0601b00f06c1a41403106c06c0457906803c1403106c0c4b203306c3a4060510e403c1b01106c0c4060310500c40603106c3a4140190126141b3170ec14c060312fc14cbf01106c3b4060311040cc061a506c3ac14019
|29=>0x3cda01b031030244040512d48fc1b0530180340303106c4b03a03106c1440605100e6b8041d506c06c1403100d4b44b0130ec1440603101a69c1b3680680441403128c0c48a01106c3a0060510ec144bf05306c3b40603119c06c6705306c1a40c0510d40480f0e806c0c4060510300640406903014406051030514b201b0241441b0192fc8fc1b05306c3b40603100814c1b05106c0640c0190084b03a03106c1440605103c1441b03106c06414019
|30=>0x2fc1400903102406c1b01919c14c6703306c1a41403106c0641b031030b54030190914dc1b0ee0180c4040510323b8db01b06c244040512fc140bf03303c0641b03101a6141b3170ec14c060310510540641506c3bc0c01960c06cb203106c3a4140190527156b01b0312241b01360c1bc0f0e906c0c40605103c3ac1b03106c1440605106c0c40c6490e803c0605106c1441b1c80505a40303163c0c03a27506c03c0605106c1441b8370ec03c06031
|31=>0x105b41b00d06c5a00303106c4700c3990182480405106c0641c00e06c1a0140319f40c03a48906c04c060512fc8fc1b05306c3b40603106c0c41b0510500640c01900414c0c1d506c06c1b05103c6f01b03106c034030510e4c543b05306c044060310248bc1b01906c1ac140310700341b0680500c404019018e186703306c1a41403106c0cc1b01906c1440605103c0641b03106c1a0140310503b81b01906c0c4060310088101b05106c06404019
|32=>0x30628f205106cb50030192fc04c0903106c0640401900d4b44b0130ec144060310500c4b203306c3a4060512fc06cbf03306c3b4060310308f41b05306c0640c0190084b03a03106c1440605106c14c1b0190183d404031030d74020ef06c1440603101c034020ec06c1440603106c14d180530185a4030312fc0cc1b53506c3b80603106d74c240ef0180c4040510500c41401906c3bc0c0190ea82c3903306c044060510e89d41b00f0181440c051
|33=>0x60c1bc6701906c1a41403103c0641b031030144060510508e4038710ec04c0603106c0640605106c1a40c0510500c4061a506c3ac1401906d5603a01106c0440605106c61c3a03306c1440605106c0c4061a506c3ac140190181a41b05106c0c4140311500341b12c0ec14406031030b741b2d80e80340605103c0341b03106c1440c05162c1a00627506c03c1403100c3140f0eb06c0c40605106c0c41b05106c1ac0c0510503640903306c0640c019
|34=>0x1284b83b05106c034060310689d44a00f06c0341403119c06c6703306c1a4140310506b41b01906c3b00c0190088ac1b05106c3a00605101c034020ec06c1440603106c1441b8350ec03c060312fc140bf0ef06c3b4060310307540901b06c0641403103c0641b03106c1440c0510240441b0190503d80403106c5d0bf05306c3b4060311500381b12c0ec144060312c85a41b0e90181440303106c0c41b01906c3bc0c0190ec1440c41506c3bc06031
|35=>0x308f40623d06c14c0c019030518b201b06c3a4140190181441403106c3b4060310083b00603106c1440405106c4c0b50690500c40301906c14c1b53506c3b8060318403bc1427506c03c060310190540c41506c3bc0603119ce0c6701806c1a4140310eced41441606c3bc060314a814c0629d03c0cc1b03106c1441b12c0ec1440603103c3a80605106c0c40403103c14c1b03102414c1b01906c144bf05306c3b4060310312241b01306c1440c051
|36=>0x100c4141d506c06c0c05106c0441b0190500641b05106c034030310181441b16900c0c42b0110308f41b053018694141a506c3ac060511501441b12c0ec144060310083b00205306c1440603165004cb200d06c3a4060511d54041b01b06c1a814031018348b203306c3a41401919c06c0f05106c0c40603106d4bc4b0130ec144060310e403c1b01906c0441b03100905c1b05106c3bc0603106c0c41b0510500640c01906c54c1b12c0ec14406031
|37=>0x183d40403100d0541b0ef0180c40c22d06c1ac1403106c14c0f01b06c0c40201b06c1440405106c1441b06b0301449000f050a741b03306c0cc060110101440603106c3a4140190e43bc1b0110180c41b0330188f41b0530ac03c0c23d06c14c0901306c0641403106d9243a00f0181441b01903c04c1b0310300341b05100c1440216806c144030310192241b0130500c41b05106c3d80403106c064142060100641b25d050b58030190243d41b019
|38=>0x240c40901106c0641462e0189d41b00f0080c41b05100c1440423d06c14c06031019a544a03306c0341b01906c0441b05136c04c0201106c1452a051018a741b03306c0641b06b0500c41b05306c0c4040311bc7541b01b00c144b203306c3a40605106c06c0c1be00c144020ef06c1440603106cc543b0530180c4030dd02414c1b01906c0343a00d0181446701906c1a4140310083b01b0510180c41a00d06c1440c0510307c8141d506c06c64053
|39=>0x18146a801300ca741b03306c0641b0310180c40603106c144040510310541b0ef0180c43b05306c04c060310ac06c0c23d06c14c0c6c900803c1b0510110581b0ef0180c41434d0e403c1b01106c0c41b0680500c41b01106c1a814031010a741b0330100640c01906c1a81403112c03c3b0510180c41b03106c144060511281a81b00d0500c40201b06c0341b0510085a81b05100c0c40200d06c1440303106c0c4142d600c0640c14500806c1b051
|40=>0x6c064030310500c41b0110100644b0130ec1440603124006c1429d06c0ccdf05303c0441b0310240c40900f06c0641b06a0500c40301903c0641b0310500c403051030b580301946014c3b00d0180c41b7b70183d80403103c3ac1b031018144bf05006c3b4060310189d41b00f0300641b00d06c3b40603106c1440f05306c0c41b01906c1a4140310309d41427506c03c1b01906804c140310311c40901306c064043850080cc1b05106c03c0c051
|41=>0x6c044140f60100c40905106c0640c05106c0441b0f40100c41b01b06c0c40405106c0c41b01900c0640605106c5ac0303106c0641b0ec0300641b05103c03c1b03106c0c4140310100641b03306c1440605106c06c1b0310500c4b201106c3a4060512fc14c0903106c064040de02414c1b0190ec14c1b0310180c4bf05006c3b4060310512243901306c0440201b0080441b0510517040616a00c0c40220406c1440401906c0c40c2d500c06409053
|42=>0x300641b03106c3a80605106d5ec1a00f0500c44a05306c034030190240cc1b00f06c0643b27506c03c060310e40cc1b0110181442501a06c2400405106c06c0f05306c0c40623d06c14c0303100c1a41403100c0640311903c06c1b0310243d41b0190100c41b03100806c1b0510188b81b06b0500c4bf05306c3b40603100d0581b0ef0180c41b01906c810040190687541b01b0500c46701306c1a4140310312241b01306c0641b03301824404051
|43=>0x6c034060310f475c1b01b0100c4b200d06c3a4060510106143a0330181440903302414c1b01906c4b83b0510180c4db00f06c244040510f43ac060510100c40903302404c1b01903c24c1b0310101440f1be06c0c4030510308f41b0530100c4b20eb06c3a4060510500341b2d600c0643a03306c034060510512241b0130181441403106c8100401906c0c40901106c064020190080c41b05112804c1b00d06c0c41b00d00803c1b0510500641b0ef
|44=>0xe8a7c1b0330181441b0ec0180c40405103c14c1b0310180c40200d06c1440303106c4b03b0510180c40c14500806c1b05102404c1b0190100641b01b06803c140312c80cc1b0e9018144bf05306c3b4060312c80cc0201906c1441b01306c3b40603100804c1b0510181440f0ea06c0c4060510083b41b0510180c406aad06c5ac030310083b01b0510180c41a01106c1a4140312c804c1b0e90181441b01906c1ac140310080441b0510301444a0ef
|45=>0x6c0c40903102406c1b01906c04c1b0510301446701806c1a41403136c06c1b0910101440220706c144040192fc0cc0f01906c0c40c05106c3a40605106c0640203106c144b205306c3a4060511281a01b00d0500c4a205106c810040192fc14c1b0ed0180c49e0530309d41b00f2fc04c0f01906c0c40c1a506c3ac0605106c1440903306c0643a29d06c0cc0605106c14c3b0530180c49e0190309d41b00f06c0641b0eb0500640629d03c0cc1b031
|46=>0x6c0c40403106c0340f00f06c0c40f00f03c0341b0310ec04c1b0190300640c23d06c14c0603100c1a41403100c064f201106cb50030190680441b06b0500c41b05106c0c41403106c1443b0510180c40c1a606c3ac060510195e41a00f0500c40f01b03c1441b0310ec1441b00f0180c414ac506cb580301906c0cc0200f06c1440f01b06c0c4060310504640f01b06c0c44a01306c0341403106c3a4060510100c43a48806c04c0605119c06c0f051
|47=>0xed2241b0130180c43a48b06c04c060510e404c1b0110500c41b01b06c0c41b05106c0441b051010144143860080cc1b05106c1441b0190100c41b03306c3a40605136c03c0201106c1448a01106c3a00605106c0641b051030144040e90500640c0192d41a41403100c064141a506c3ac0605106c0c41b01306c0648a00d06c3a00605106d1883b00d0180c41b03100806c1b05106c06406051030146100330509d41b00f16c1441b16800c0c41b051
|48=>0x6c0c41b03106c3ac060510188b41b06b0500c4b50690500c40301919c0cc1b0690500c41b3680680441403106c1441b0ec0180c41b0510183d40403103c3a81b0310181441b011030144060510e403c1b0110500c4066c900803c1b05106c4bc3b0510180c41b05306c3bc060310ec1443b0110180c4670180080c41b0510ec1441b0310180c4bf0330240c41b0190507541b01b06c0c4df00f03c0441b0311ac1441b0ec0180c43b48b06c04c06031
|49=>0x6c0cc1b051018a741429d06c0cc048ad06c3a80605119c03c1b0690500c41441506c3bc0603100814c1b0510180c41b03306c3ac060510e80c41b0190500646701b06c1a4140312c80c00905106c0641b03102406c1b01900d7d41a0130500c4bf03306c3b40603100806c0205306c1446f0ef0180c4030510ec8f01b0530180c41b1ca0505a40303106c03c1b0ea0181440606a0500c40301906c06c1b06a0500c40441506c3bc0603106c14c0f00d
|50=>0x6c8ac1b0e80181441b50106c1a8140310500c41b2060100641b01906c5a40303119c0641b0690500c48106a0500c40401906c0641400d00c0c41b0eb018144030310ec1441b0110180c41453506c3b8060310ec8fc1b0530180c43b00d06c034060310080cc1b051018144240ec0180c40405112c0343b0510180c41b3680503d4040310700381b0680500c40906b06c0641403106c1440f05306c0c41b01906c1a41403106c14c0f01906c0c40629d
|51=>0x180c41b12e0ec1440603106cc5c3b0530180c41b03106c1441b01906c4b03b0510180c41b12e0ec144060312280c41b0e80181440629d06c0cc1b0511ac1481b0ec0180c43a48906c04c060512fc1441b0ed0180c4060510500c4060310e80c41b0eb0181441b03300806c1b0510680641b0690500c44b0130ec1440603119c14c0203106c1441b05306c3b40603119c06c1b0690500c43b23d06c14c0603119c0601b0690500c4140da0240cc1b019
|52=>0x6c0cc040510183d4040311280cc1b00d06c14c1b03306c0441b03106c0c40603100c8f41b05306c04c060310188f41b05306804c1403106c14c1b0310ec144060310e8034060510192241b01303c04c1b03106c0c4040310e403c1b01106c0340603106c1441b0190512241b0130240cc1b01906c064030510680641403106c0340305102414c1b01902404c1b01906c0cc1b051050a741b03306c1441b0ed0180c41b12c0ec1440603106c14c1b0ed
|53=>0x180c41b01106c0cc1b05100c1441b00f02406c1b01906c0c41b01906c0c40605106c5a40303106c06c140310ec14c0603106c3ac0605106c1a41403106c6fc030510e403c1b01103c0341b0310180440403106c3a40605106c6f80305106c3bc060310e404c1b01103c1441b03106c3a8060510500c4030190500c40603106c8100401906c03c1b051050b580301906c3b006031
|_=>0
def opOffB : Nat → Nat → Nat
|4,0=>0x18601260000000000000000000000000000000000000000000000000000000000c600000000000000000000000000000000000000000000000000000000006600000000000000000006000000000000000000000000000000000000
|5,0=>0x73506e5000000000695000000000000000000000000000000000000064505f500000000000000000000000005a500000555050500000000000000000000000004b500000000000004650000000000000000000000000000041503c50000000003750000032502d502850000023500000000000001e5000000000000
|5,1=>0xd25000000000cd50c850c3500000be500000b95000000000000000000000b45000000000000000000000af500000000000000000000000000000aa5000000000a5500000000000000000a0500000000000009b5000009650000091508c500000000087500000825000000000000000000000000000000000000000007d50785
|5,2=>0x1135000010e5109500000000104500000000000000000ff500000000000000000fa50000000000000f550000000000000f050eb500000e65000000000000000000000e15000000000000000000000000000000000000000000000dc5000000000000000000000d7500000000000000000000
|5,3=>0x15950000154500000000000014f5000014a50000145500000000000000000000000000000000000000000000140513b500000000000000000000000000001365000000000000000013150000000012c5000000000000000000001275000000001225000000000000000000000000000011d5000000000000000011850000
|5,4=>0x18b5000018650000000018150000000000000000000000000000000000000000000000000000000017c5000017751725000016d5168500000000000000001635000015e5
|6,0=>0x23040000000022c4000000000000228422442204000021c42184214400002104000020c40000000020842044200400001fc41f841f4400000000000000001f041ec400001e841e441e041dc41d84000000001d4400001d041cc41c841c441c041bc41b841b441b0400001ac400001a841a4400001a0419c41984194419040000
|6,1=>0x2f842f442f042ec42e842e442e042dc42d842d442d0400002cc400002c8400002c4400002c042bc42b842b442b042ac42a842a442a0429c400002984294429040000000028c40000288428442804000027c427842744270426c40000268426442604000025c425842544250424c4248424442404000023c42384000000002344
|6,2=>0x3a4400003a0439c4000039843944390438c43884384400000000380437c4378437443704000036c436843644000000003604000035c43584354435040000000034c40000348434440000340433c4338400000000000033443304000032c432843244320431c431843144000000003104000030c430843044300400002fc4
|6,3=>0x47844744470446c400004684000000004644460445c445844544450444c444844444440443c4438400004344430442c442844244420441c441844144410440c440840000404440043fc43f843f44000000003f0400003ec43e843e443e043dc43d8400003d4400003d043cc43c843c443c0400003bc43b843b443b043ac43a84
|6,4=>0x538453440000530452c4528452440000520451c4518451440000510450c4508450440000000050044fc44f8400004f444f044ec44e844e4400004e044dc44d844d4400004d04000000004cc44c844c4400004c044bc44b844b444b044ac4000000004a844a444a0449c4498449444904000048c448844844480447c400000000
|6,5=>0x5e8400005e445e045dc45d845d4400005d045cc45c8400005c445c0400005bc45b845b4400005b04000000005ac45a8400005a4400005a0459c40000598459440000590458c458845844580457c45784000000005744570456c4568400005644560455c455845544550454c40000000000005484544400005404000053c4
|6,6=>0x6ac46a846a446a0469c469846944690468c468846844000000006804000067c467846744670466c4668400006644660465c40000658400006544650464c4000064846444640463c463846344630462c46284624462040000000061c4618400006144610460c4608460440000000060045fc45f845f4400005f04000000005ec4
|6,7=>0x75c4758400007544750474c47484744474040000000073c47384000000007344730472c4728472440000720471c471847144710470c47084000000000000704470046fc46f846f446f046ec46e846e440000000000006e0400006dc400006d846d44000000006d046cc400006c846c446c046bc46b8400006b446b04
|6,8=>0x8244820481c4818481448104000080c400000000000080848044000080047fc47f847f447f047ec47e847e447e0400007dc47d847d447d047cc47c847c44000000007c047bc47b847b447b047ac47a847a44000000007a0479c40000798400007944790478c478847844780477c477847744770476c476847644760400000000
|6,9=>0x8e848e448e048dc48d848d4400008d048cc48c848c4400008c0400008bc48b8400008b448b048ac48a8400008a4400008a0489c489848944890488c488848844880487c4878487448704000000000000000086c486848644860485c485848544850484c484848444840483c4838483440000830482c48284000000000000
|6,10=>0x92c4928492440000920491c40000918491440000910490c4908400000000904490048fc48f8400008f4400008f048ec400000000
|7,0=>0x9ed39ea39e739e439e139de39db39d839d539d239cf39cc39c939c639c339c039bd39ba39b739b439b139ae39ab39a839a539a2399f399c3999399639933990398d398a398739843981397e397b397839753972396f396c3969396639633960395d395a395739543951394e394b394839453942393f393c39393936393339303
|7,1=>0xaad3aaa3aa73aa43aa13a9e3a9b3a983a953a923a8f3a8c3a893a863a833a803a7d3a7a3a773a743a713a6e3a6b3a683a653a623a5f3a5c3a593a563a533a503a4d3a4a3a473a443a413a3e3a3b3a383a353a323a2f3a2c3a293a263a233a203a1d3a1a3a173a143a113a0e3a0b3a083a053a0239ff39fc39f939f639f339f03
|7,2=>0xb6a3b673b643b613b5e3b5b3b583b553b523b4f3b4c3b493b463b433b403b3d3b3a3b373b343b313b2e3b2b3b283b253b223b1f3b1c3b193b163b133b103b0d3b0a3b073b043b013afe3afb3af83af53af23aef3aec3ae93ae63ae330000ae03add3ada3ad73ad43ad13ace3acb3ac83ac53ac23abf3abc3ab93ab63ab33ab03
|7,3=>0xc2a3c273c243c213c1e3c1b3c183c153c123c0f3c0c3c093c063c033c003bfd3bfa3bf73bf43bf13bee3beb3be83be53be23bdf3bdc3bd93bd63bd33bd03bcd3bca3bc73bc43bc13bbe3bbb3bb83bb53bb23baf3bac3ba93ba63ba33ba03b9d3b9a3b973b943b913b8e3b8b3b883b853b823b7f3b7c3b793b763b733b703b6d3
|7,4=>0xcea3ce73ce43ce13cde3cdb3cd83cd53cd23ccf3ccc3cc93cc63cc33cc03cbd3cba3cb73cb43cb13cae3cab3ca83ca53ca23c9f3c9c3c993c963c933c903c8d3c8a3c873c843c813c7e3c7b3c783c753c723c6f3c6c3c693c663c633c603c5d3c5a3c573c543c513c4e3c4b3c483c453c423c3f3c3c3c393c363c333c303c2d3
|7,5=>0xd053d023cff3cfc3cf93cf63cf33cf03ced3
|8,0=>0xd6e2d6c2d6a2d682d662d642d622d602d5e2d5c2d5a2d582d562d542d522d502d4e2d4c2d4a2d482d462d442d422d402d3e2d3c2d3a2d382d362d342d322d302d2e2d2c2d2a2d282d262d242d222d202d1e2d1c2d1a2d182d162d142d122d102d0e2d0c2d0a2d082
|9,0=>0xd751d741d731d721d711d701d700
|10,0=>0xd760
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 22 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 1023), wireSAt ((code >>> 12) &&& 1023)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 16 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmB : Nat → Nat → Nat
|4,0=>0x2000002000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000080000000000000000000000000000000000000000000
|5,0=>0x2000000000000050004c00088000000060000000004400000000000000000000000000100000000000000000000000000200400000000000000000000000000000000000004000000000800000000000000000000000000100000000000000000020000000020000000000882008000000000400000000000010000000000000000000000000000000000000000000000004000000100000000000080200001000000000000028000000000000000000000000000000000000000000000400010000000000000000000000000000000080000000000880004000000000000000000000000000000100000000000000000008000000000000000000000000000000000000001000100000000000000080000002000000400300000020000000000000000000002000000000000000
|5,1=>0x1000800000000010000000000000000004000010000000000000100000000000000000000000000000000000000000000000000000000520000000000000000000000000000000000000220000000000000000000000000040000000000000200000000000000000000000080000000000000000100000000000000000000000000000000000000800000000000000000000000800000000000000000000000000000000000000001400000000400002000000000000014000000000000000000000028000000000000000000000010000000000000000001000000000000000040000040000000020000000000000000000000000020000000000000000000000000000000000000000000000000000000020020000000000000000000000001000000000000000000000000000
|5,2=>0x2800000000a000000000000040000000000000000000000000000000000000000000000000000000000000000000000880000000020005000000000400002000000000000000000000040000000020
|6,0=>0x80004000010100000100100010040008800110004200020080000000040000000000008000020002000000010000040004400010000200010000640101000080000100000000d400080010000000000000002800000048a04014000200000000604100200000001200020000008802800010000200000080000010000020001400020000c000140001000006002000080000000000000080000200000000000004000000000000000002400012000040000000050084400004000000001000004000400000000000008000f8000200000040000000400008000000000000000000000018002c00000001000023000020004402020000000000000a400000001000022010000008000010000b000800002000a8000000001400000001400040000000030000040000400010000280000
|6,1=>0x8000810800000110000000044000000000202000000400110000410002000a008008000400002000500040c0100000004000401000001404000000040a00001150000200010888a8000400002000000002000110002044002001000000000000001400004008080049000100000900100000200000000080000000060000400010000280844000000010010010000200008009e00002000000040000000000100048000000009200010000300002000880004000000000000080002800820400008a08000000002200008000c0000000000000800000000400002a00004001000000000000004400000002080002000008002000100000a000000000000002000a40004000010000000210000200000000100002000840000000000005a000004009000040002a00030000000010
|6,2=>0x900000000040000300180000200030000000000400020000400000010448a02000002280000004400080000008200000000000000400028000000002000000004200084000010005000380000000008000100008000448a0a0000420020000000000000010000800088000180000008200004000100001100064040120800000000000000000000800010000000009c000000400000600001c0000100210000800004001000000000040000600100000500000000040101001010000a0000000000010002808400040000000100000244000000880004000000008008008000400020000000110800000000000478000890401000000004000020002020009000000010000000000000084080000080800000005400800100400001000000002808080004000400000000000
|6,3=>0x20880002000000884c0008000042020000044000800000000000001c8010000000000000010000081405228080005400000000100010000540000c00102000a00080000000000000000008000020000500202000800802800040000240014000000000000000009000000001100000000040088800000000000012000000000002280000429010002a0010000000000080080000020001000120002000004000544000000080020000050001000000000000040000000000100002000100208000200002000000000201000000400000000020000000010000100800000000000b00458000800011000200008800040001500003000840002000000000000008000a800000000841004001400001800200000000000000500008000420008000000808000000000000010
|6,4=>0x1000008110100002040000080000000000a00008000280004000000041c00000002000040000000200c0115002280001000000000400000000040080010150004000010001000020800220101000008100400008010440000000000000000000080040000200000040000080001d80009020b4001e800200000a400040000800022280000000000881000002200000000000000020801000000000800150010000004000000006000000000000000100500042000000000c00b504042000400002000042200000410005080000000400044000010001400208000540802000000000100058000880401801100004c00008001102008000000000001000000200000000200000000024000080004000100010000100000800010002200044000a800010000200004000000000
|6,5=>0x80000150000a0000000020040000000000140208000000000400044008000000000000000400008011500002000000802000000000e00280000000000
|7,0=>0x8000b000fc080a8001911832000a0003b810150082204014009e8402d00820010fc2089c0057804c640054013a00003c016200254081b4000d0000c41444088a000220203e0000808020101f002cc10088041f0407d8017200030003891422002210081c04000040802028802bd0406c02142003e0407c00dd810280000a0105400068043000082080d4000cc011d0206e0000e0888810060023e000340000c20b58022a0008a0039814150007e00054005aa002c010682029500028041f00046000700204c0025c002b000d2101300005008230181240489001f900200004408076003c700580007c080f88c080022a001f6009e80401008290005a028280108000aa400040020c01058027e00014005f840130014a00234000a800448806c8009c0118001158004d002b0005640020
|7,1=>0x8c4002c0019c004b2017e450000882904060003e45010080881105804970045c081f8103f000040018c0082c006600802000548082c001f8022e010543003a04112000800446008aa18090002a410540040c01958000d002a60450c10220222a002de005ac000200a3e45016008a800b72002a00075005f8010c0202200012000e80003002ea010540808821030006e081f4203a810112002a01054800ac041880222040fc009f800130023e0105480820101500020400120088900010206e040564056810050082a001ea0208100050202a400540001400120000204012008a800158000600008008ac20238203a009f200121003d0002a45016101a90047000060810c0000000818024e40011005f10029000ac100de2019800158003b002b00802000018012b00279000480081
|7,2=>0x10052282a000108a0a8100e0002a0007c000f8011f00a2b0005c8001000012285e05004028a000110204e00054000a8040f0203e010040002401150003e10004045800010000ea002560004800220203c0403a005c800150207a45022003a8013f0082a0041402080001500a2a00454801fc00090020800414008a914050083e400520888800170202a00050401cc01150016e00020021c004100004700024008a800110017e01006021080015
|8,0=>0x8002e000dc800fc08b500a3e040ba800f804379016b0017e041e8007f2003f202f40807801770083e400ad025f8143f800ee204f50056c101f840ae001de004ec01278026e040de005e8117f8022e010ca028a914377005e005fe003fc02778003f042f4008f8017f0007f202f48a0dc00bd0003f000de028ac001d
|9,0=>0x40de003bc001f0006e202f400df8001f
|10,0=>0x3f
|_,_=>0
def PM (s j : Nat) : Nat := fld (pmB s (j / 128)) 19 (j % 128)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_186,8,runOps true dom_186 (0,roots_186) ops)] else [])++(if pm.testBit 1 then [(dom_185,8,runOps true dom_185 (0,roots_185) ops)] else [])++(if pm.testBit 2 then [(dom_179,8,runOps true dom_179 (0,roots_179) ops)] else [])++(if pm.testBit 3 then [(dom_171,8,runOps true dom_171 (0,roots_171) ops)] else [])++(if pm.testBit 4 then [(dom_155,8,runOps true dom_155 (0,roots_155) ops)] else [])++(if pm.testBit 5 then [(dom_169,7,runOps true dom_169 (0,roots_169) ops)] else [])++(if pm.testBit 6 then [(dzo_185_2,6,runOps true dzo_185_2 (0,roots_185) ops)] else [])++(if pm.testBit 7 then [(dzo_171_16,6,runOps true dzo_171_16 (0,roots_171) ops)] else [])++(if pm.testBit 8 then [(dom_59,6,runOps true dom_59 (0,roots_59) ops)] else [])++(if pm.testBit 9 then [(dom_184,5,runOps true dom_184 (0,roots_184) ops)] else [])++(if pm.testBit 10 then [(dom_178,5,runOps true dom_178 (0,roots_178) ops)] else [])++(if pm.testBit 11 then [(dom_170,5,runOps true dom_170 (0,roots_170) ops)] else [])++(if pm.testBit 12 then [(dom_154,5,runOps true dom_154 (0,roots_154) ops)] else [])++(if pm.testBit 13 then [(dom_177,5,runOps true dom_177 (0,roots_177) ops)] else [])++(if pm.testBit 14 then [(dom_153,5,runOps true dom_153 (0,roots_153) ops)] else [])++(if pm.testBit 15 then [(dom_163,5,runOps true dom_163 (0,roots_163) ops)] else [])++(if pm.testBit 16 then [(dom_147,5,runOps true dom_147 (0,roots_147) ops)] else [])++(if pm.testBit 17 then [(dom_139,5,runOps true dom_139 (0,roots_139) ops)] else [])++(if pm.testBit 18 then [(dom_41,4,runOps true dom_41 (0,roots_41) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_187 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_186 _ g hchk
    · exact cpcs (by decide +kernel) low_185 _ g hchk
    · exact cpcs (by decide +kernel) low_179 _ g hchk
    · exact cpcs (by decide +kernel) low_171 _ g hchk
    · exact cpcs (by decide +kernel) low_155 _ g hchk
    · exact cpcs (by decide +kernel) low_169 _ g hchk
    · exact cpcs (by decide +kernel) lowZ_185_2_144 _ g hchk
    · exact cpcs (by decide +kernel) lowZ_171_16_130 _ g hchk
    · exact cpcs (by decide +kernel) low_59 _ g hchk
    · exact cpcs (by decide +kernel) low_184 _ g hchk
    · exact cpcs (by decide +kernel) low_178 _ g hchk
    · exact cpcs (by decide +kernel) low_170 _ g hchk
    · exact cpcs (by decide +kernel) low_154 _ g hchk
    · exact cpcs (by decide +kernel) low_177 _ g hchk
    · exact cpcs (by decide +kernel) low_153 _ g hchk
    · exact cpcs (by decide +kernel) low_163 _ g hchk
    · exact cpcs (by decide +kernel) low_147 _ g hchk
    · exact cpcs (by decide +kernel) low_139 _ g hchk
    · exact cpcs (by decide +kernel) low_41 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_186 8 s (0, roots_186) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_187 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_186 h

def symsG : List (List (Nat × Nat)) := [[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_187 == dom_187) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 1 zs symsG zs (hk 1 zs)
theorem ori_ok {v ys} (h : RunD true dom_187 goalM v ys) : RunD true dom_187 goalM v (ori ys) :=
  pickMin_runD 1 ys h symsG ys (hk 1 ys) symsG_ok h

def Z (s : Nat) := barP true dom_187 goalM mpG SD SS NN htAt idxH ori 1 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_0 : ∀ i, 0 ≤ i → i < 12 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_12 : ∀ i, 12 ≤ i → i < 24 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 12 12 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_24 : ∀ i, 24 ≤ i → i < 36 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 12 24 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_36 : ∀ i, 36 ≤ i → i < 48 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 12 36 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_48 : ∀ i, 48 ≤ i → i < 51 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 48 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 51 → Z 4 i = true := (range_split (range_split (range_split (range_split z4_0 z4_12) z4_24) z4_36) z4_48)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_0 : ∀ i, 0 ≤ i → i < 12 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_12 : ∀ i, 12 ≤ i → i < 24 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 12 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_24 : ∀ i, 24 ≤ i → i < 36 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 24 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_36 : ∀ i, 36 ≤ i → i < 48 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 36 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_48 : ∀ i, 48 ≤ i → i < 60 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 48 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_60 : ∀ i, 60 ≤ i → i < 72 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 60 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_72 : ∀ i, 72 ≤ i → i < 84 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 72 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_84 : ∀ i, 84 ≤ i → i < 96 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 84 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_96 : ∀ i, 96 ≤ i → i < 108 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 96 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_108 : ∀ i, 108 ≤ i → i < 120 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 108 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_120 : ∀ i, 120 ≤ i → i < 132 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 120 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_132 : ∀ i, 132 ≤ i → i < 144 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 132 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_144 : ∀ i, 144 ≤ i → i < 156 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 144 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_156 : ∀ i, 156 ≤ i → i < 168 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 156 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_168 : ∀ i, 168 ≤ i → i < 180 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 168 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_180 : ∀ i, 180 ≤ i → i < 192 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 180 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_192 : ∀ i, 192 ≤ i → i < 204 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 192 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_204 : ∀ i, 204 ≤ i → i < 216 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 204 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_216 : ∀ i, 216 ≤ i → i < 228 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 216 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_228 : ∀ i, 228 ≤ i → i < 240 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 228 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_240 : ∀ i, 240 ≤ i → i < 252 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 240 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_252 : ∀ i, 252 ≤ i → i < 264 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 252 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_264 : ∀ i, 264 ≤ i → i < 276 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 264 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_276 : ∀ i, 276 ≤ i → i < 288 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 276 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_288 : ∀ i, 288 ≤ i → i < 297 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 9 288 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 297 → Z 5 i = true := (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split z5_0 z5_12) z5_24) z5_36) z5_48) z5_60) z5_72) z5_84) z5_96) z5_108) z5_120) z5_132) z5_144) z5_156) z5_168) z5_180) z5_192) z5_204) z5_216) z5_228) z5_240) z5_252) z5_264) z5_276) z5_288)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 12 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_12 : ∀ i, 12 ≤ i → i < 24 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 12 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_24 : ∀ i, 24 ≤ i → i < 36 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 24 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_36 : ∀ i, 36 ≤ i → i < 48 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 36 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_48 : ∀ i, 48 ≤ i → i < 60 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 48 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_60 : ∀ i, 60 ≤ i → i < 72 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 60 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_72 : ∀ i, 72 ≤ i → i < 84 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 72 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_84 : ∀ i, 84 ≤ i → i < 96 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 84 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_96 : ∀ i, 96 ≤ i → i < 108 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 96 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_108 : ∀ i, 108 ≤ i → i < 120 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 108 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_120 : ∀ i, 120 ≤ i → i < 132 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 120 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_132 : ∀ i, 132 ≤ i → i < 144 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 132 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_144 : ∀ i, 144 ≤ i → i < 156 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 144 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_156 : ∀ i, 156 ≤ i → i < 168 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 156 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_168 : ∀ i, 168 ≤ i → i < 180 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 168 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_180 : ∀ i, 180 ≤ i → i < 192 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 180 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_192 : ∀ i, 192 ≤ i → i < 204 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 192 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_204 : ∀ i, 204 ≤ i → i < 216 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 204 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_216 : ∀ i, 216 ≤ i → i < 228 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 216 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_228 : ∀ i, 228 ≤ i → i < 240 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 228 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_240 : ∀ i, 240 ≤ i → i < 252 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 240 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_252 : ∀ i, 252 ≤ i → i < 264 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 252 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_264 : ∀ i, 264 ≤ i → i < 276 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 264 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_276 : ∀ i, 276 ≤ i → i < 288 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 276 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_288 : ∀ i, 288 ≤ i → i < 300 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 288 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_300 : ∀ i, 300 ≤ i → i < 312 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 300 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_312 : ∀ i, 312 ≤ i → i < 324 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 312 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_324 : ∀ i, 324 ≤ i → i < 336 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 324 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_336 : ∀ i, 336 ≤ i → i < 348 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 336 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_348 : ∀ i, 348 ≤ i → i < 360 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 348 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_360 : ∀ i, 360 ≤ i → i < 372 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 360 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_372 : ∀ i, 372 ≤ i → i < 384 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 372 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_384 : ∀ i, 384 ≤ i → i < 396 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 384 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_396 : ∀ i, 396 ≤ i → i < 408 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 396 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_408 : ∀ i, 408 ≤ i → i < 420 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 408 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_420 : ∀ i, 420 ≤ i → i < 432 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 420 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_432 : ∀ i, 432 ≤ i → i < 444 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 432 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_444 : ∀ i, 444 ≤ i → i < 456 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 444 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_456 : ∀ i, 456 ≤ i → i < 468 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 456 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_468 : ∀ i, 468 ≤ i → i < 480 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 468 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_480 : ∀ i, 480 ≤ i → i < 492 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 480 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_492 : ∀ i, 492 ≤ i → i < 504 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 492 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_504 : ∀ i, 504 ≤ i → i < 516 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 504 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_516 : ∀ i, 516 ≤ i → i < 528 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 516 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_528 : ∀ i, 528 ≤ i → i < 540 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 528 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_540 : ∀ i, 540 ≤ i → i < 552 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 540 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_552 : ∀ i, 552 ≤ i → i < 564 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 552 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_564 : ∀ i, 564 ≤ i → i < 576 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 564 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_576 : ∀ i, 576 ≤ i → i < 588 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 576 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_588 : ∀ i, 588 ≤ i → i < 600 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 588 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_600 : ∀ i, 600 ≤ i → i < 612 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 600 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_612 : ∀ i, 612 ≤ i → i < 624 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 612 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_624 : ∀ i, 624 ≤ i → i < 636 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 624 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_636 : ∀ i, 636 ≤ i → i < 648 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 636 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_648 : ∀ i, 648 ≤ i → i < 660 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 648 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_660 : ∀ i, 660 ≤ i → i < 666 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 660 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 666 → Z 6 i = true := (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split z6_0 z6_12) z6_24) z6_36) z6_48) z6_60) z6_72) z6_84) z6_96) z6_108) z6_120) z6_132) z6_144) z6_156) z6_168) z6_180) z6_192) z6_204) z6_216) z6_228) z6_240) z6_252) z6_264) z6_276) z6_288) z6_300) z6_312) z6_324) z6_336) z6_348) z6_360) z6_372) z6_384) z6_396) z6_408) z6_420) z6_432) z6_444) z6_456) z6_468) z6_480) z6_492) z6_504) z6_516) z6_528) z6_540) z6_552) z6_564) z6_576) z6_588) z6_600) z6_612) z6_624) z6_636) z6_648) z6_660)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 12 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_12 : ∀ i, 12 ≤ i → i < 24 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 12 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_24 : ∀ i, 24 ≤ i → i < 36 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 24 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_36 : ∀ i, 36 ≤ i → i < 48 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 36 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_48 : ∀ i, 48 ≤ i → i < 60 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 48 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_60 : ∀ i, 60 ≤ i → i < 72 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 60 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_72 : ∀ i, 72 ≤ i → i < 84 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 72 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_84 : ∀ i, 84 ≤ i → i < 96 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 84 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_96 : ∀ i, 96 ≤ i → i < 108 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 96 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_108 : ∀ i, 108 ≤ i → i < 120 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 108 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_120 : ∀ i, 120 ≤ i → i < 132 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 120 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_132 : ∀ i, 132 ≤ i → i < 144 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 132 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_144 : ∀ i, 144 ≤ i → i < 156 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 144 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_156 : ∀ i, 156 ≤ i → i < 168 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 156 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_168 : ∀ i, 168 ≤ i → i < 180 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 168 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_180 : ∀ i, 180 ≤ i → i < 192 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 180 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_192 : ∀ i, 192 ≤ i → i < 204 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 192 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_204 : ∀ i, 204 ≤ i → i < 216 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 204 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_216 : ∀ i, 216 ≤ i → i < 228 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 216 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_228 : ∀ i, 228 ≤ i → i < 240 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 228 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_240 : ∀ i, 240 ≤ i → i < 252 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 240 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_252 : ∀ i, 252 ≤ i → i < 264 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 252 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_264 : ∀ i, 264 ≤ i → i < 276 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 264 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_276 : ∀ i, 276 ≤ i → i < 288 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 276 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_288 : ∀ i, 288 ≤ i → i < 300 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 288 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_300 : ∀ i, 300 ≤ i → i < 312 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 300 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_312 : ∀ i, 312 ≤ i → i < 324 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 312 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_324 : ∀ i, 324 ≤ i → i < 329 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 5 324 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 329 → Z 7 i = true := (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split z7_0 z7_12) z7_24) z7_36) z7_48) z7_60) z7_72) z7_84) z7_96) z7_108) z7_120) z7_132) z7_144) z7_156) z7_168) z7_180) z7_192) z7_204) z7_216) z7_228) z7_240) z7_252) z7_264) z7_276) z7_288) z7_300) z7_312) z7_324)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 12 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_12 : ∀ i, 12 ≤ i → i < 24 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 12 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_24 : ∀ i, 24 ≤ i → i < 36 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 24 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_36 : ∀ i, 36 ≤ i → i < 48 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 36 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_48 : ∀ i, 48 ≤ i → i < 52 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 4 48 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 52 → Z 8 i = true := (range_split (range_split (range_split (range_split z8_0 z8_12) z8_24) z8_36) z8_48)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 7 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 10) : ∀ i < NN s, bar true dom_187 goalM mpG SD SS NN htAt idxH ori 1 pool6G mkCut s i = true := by
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
  scr true dom_187 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 6 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 10) (h : RunD true dom_187 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_187 roots_187 goal_187 11 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_187

theorem low_187 : Lower true dom_187 roots_187 goal_187 11 := S_187.noCircuit

theorem low_251 : Lower true dom_251 roots_251 goal_251 12 :=
  lower_slice (d:=dom_251) (dSub:=dom_187) (T:=goal_251) (TSub:=goal_187) (roots:=roots_251) (rootsSub:=roots_187)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000, 2, 66)] (by decide +kernel) (by decide +kernel) low_187

theorem low_255 : Lower true dom_255 roots_255 goal_255 13 :=
  lower_slice (d:=dom_255) (dSub:=dom_251) (T:=goal_255) (TSub:=goal_251) (roots:=roots_255) (rootsSub:=roots_251)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 64, 68)] (by decide +kernel) (by decide +kernel) low_251

theorem lowS_255 : Lower true dom_255 roots_255 goal_255 13 := low_255

theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 0, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 0, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [0, 3] }, { op := GateOp.or, inputs := [5, 7] }, { op := GateOp.and, inputs := [8, 9] }, { op := GateOp.or, inputs := [1, 4] }, { op := GateOp.or, inputs := [5, 11] }, { op := GateOp.and, inputs := [7, 12] }, { op := GateOp.or, inputs := [2, 11] }, { op := GateOp.and, inputs := [6, 14] }, { op := GateOp.and, inputs := [0, 3] }, { op := GateOp.and, inputs := [1, 4] }, { op := GateOp.or, inputs := [10, 13] }, { op := GateOp.or, inputs := [15, 18] }, { op := GateOp.or, inputs := [16, 19] }, { op := GateOp.or, inputs := [17, 20] }]

theorem wit_mono : ∀ g ∈ witGates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 21⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 0, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
  decide +kernel

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
  · push_neg at hhas
    refine ⟨gates, o, ?_, le_rfl, hev⟩
    intro g hg
    obtain ⟨h1, h2⟩ := hfan g hg
    refine ⟨?_, h2⟩
    rcases h1 with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exfalso; have := hhas g hg; simp [isNotGate, h1] at this

end PEqualNP.Outside.L_meta_32085_aux

theorem PEqualNP.Outside.L_meta_32085 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_32085_aux.main
