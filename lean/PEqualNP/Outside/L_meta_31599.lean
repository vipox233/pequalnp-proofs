import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_31599_aux
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
def dom_85 : Nat := 0x3300330000000000330033
def goal_85 : Nat := 0xfafafafafafafafaaaaa0000aaaa0000fafafafafafafafaaaaa0000aaaa0000
def roots_85 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_86 : Nat := 0x5500550000000000550055
def goal_86 : Nat := 0xfcfcfcfcfcfcfcfccccc0000cccc0000fcfcfcfcfcfcfcfccccc0000cccc0000
def roots_86 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_102 : Nat := 0x55000000550000005500000055
def goal_102 : Nat := 0xfcfcfcfcfcfcfcfcf0f0f0f000000000fcfcfcfcfcfcfcfcf0f0f0f000000000
def roots_102 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_103 : Nat := 0xff000000ff000000ff000000ff
def goal_103 : Nat := 0xfefefefefefefefef0f0f0f000000000fefefefefefefefef0f0f0f000000000
def roots_103 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_108 : Nat := 0x1111000011110000111100001111
def goal_108 : Nat := 0xfff0fff0f0f0f0f0fff0fff000000000fff0fff0f0f0f0f0fff0fff000000000
def roots_108 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xfffafffafafafafafff0fff000000000fffafffafafafafafff0fff000000000
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xfffcfffcfcfcfcfcfff0fff000000000fffcfffcfcfcfcfcfff0fff000000000
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfafafafafafafafafafaf0f0aaaa0000fafafafafafafafafafaf0f0aaaa0000
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfcfcfcfcfcfcfcfcfcfcf0f0cccc0000fcfcfcfcfcfcfcfcfcfcf0f0cccc0000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffafffafafafafafffafff0aaaa0000fffafffafafafafafffafff0aaaa0000
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffcfffcfcfcfcfcfffcfff0cccc0000fffcfffcfcfcfcfcfffcfff0cccc0000
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_145 : Nat := 0x3000300000000000000000000000000030003
def goal_145 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaaaaaa0000aaaa0000aaaa0000aaaa0000
def roots_145 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_147 : Nat := 0xf000f000000000000000000000000000f000f
def goal_147 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaaeeee0000eeee0000eeee0000eeee0000
def roots_147 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_149 : Nat := 0x33003300000000000000000000000000330033
def goal_149 : Nat := 0xfffffafafffffafafffffafafffffafaaaaa0000aaaa0000aaaa0000aaaa0000
def roots_149 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_150 : Nat := 0x55005500000000000000000000000000550055
def goal_150 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0cccc0000cccc0000cccc0000cccc0000
def roots_150 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_151 : Nat := 0xff00ff00000000000000000000000000ff00ff
def goal_151 : Nat := 0xfffffafafffffafafffffafafffffafaeeee0000eeee0000eeee0000eeee0000
def roots_151 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_158 : Nat := 0x5555555500000000000000000000000055555555
def goal_158 : Nat := 0xfffffff0fffffff0fffffff0fffffff0cccc0000cccc0000cccc0000cccc0000
def roots_158 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_164 : Nat := 0x110000001100000000000000000000001100000011
def goal_164 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f000000000f0f0f0f000000000
def roots_164 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_168 : Nat := 0x1010000010100000000000000000000010100000101
def goal_168 : Nat := 0xffffffffff00ff00ffffffffff00ff00ff00ff0000000000ff00ff0000000000
def roots_168 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_170 : Nat := 0x5050000050500000000000000000000050500000505
def goal_170 : Nat := 0xffffffffff00ff00ffffffffff00ff00ff00ff0000000000ff00ff0000000000
def roots_170 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_172 : Nat := 0x11110000111100000000000000000000111100001111
def goal_172 : Nat := 0xfffffffffff0fff0fffffffffff0fff0fff0fff000000000fff0fff000000000
def roots_172 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xfffffffffffafffafffffffffffafffafff0fff000000000fff0fff000000000
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_174 : Nat := 0x55550000555500000000000000000000555500005555
def goal_174 : Nat := 0xfffffffffff0fff0fffffffffff0fff0fff0fff000000000fff0fff000000000
def roots_174 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_178 : Nat := 0x500050005000500000000000000000005000500050005
def goal_178 : Nat := 0xffffffffffff0000ffffffffffff0000cccc0000cccc0000cccc0000cccc0000
def roots_178 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_180 : Nat := 0x1100110011001100000000000000000011001100110011
def goal_180 : Nat := 0xfffffffffffff0f0fffffffffffff0f0f0f0f0f000000000f0f0f0f000000000
def roots_180 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_182 : Nat := 0x5500550055005500000000000000000055005500550055
def goal_182 : Nat := 0xfffffffffffff0f0fffffffffffff0f0fcfcf0f0cccc0000fcfcf0f0cccc0000
def roots_182 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_184 : Nat := 0x10101010101010100000000000000000101010101010101
def goal_184 : Nat := 0xffffffffffffff00ffffffffffffff00ff00ff0000000000ff00ff0000000000
def roots_184 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def goal_186 : Nat := 0xffffffffffffff00ffffffffffffff00ffccff00cccc0000ffccff00cccc0000
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_188 : Nat := 0x111111111111111100000000000000001111111111111111
def goal_188 : Nat := 0xfffffffffffffff0fffffffffffffff0fff0fff000000000fff0fff000000000
def roots_188 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xfffffffffffffff0fffffffffffffff0fffcfff0cccc0000fffcfff0cccc0000
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_198 : Nat := 0x55000000000000005500000000000000550000000000000055
def goal_198 : Nat := 0xfcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f0fcfcfcfcfcfcfcfc0000000000000000
def roots_198 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_204 : Nat := 0x1111000000000000111100000000000011110000000000001111
def goal_204 : Nat := 0xfff0fff0fff0fff0fff0fff0fff0fff0f0f0f0f0f0f0f0f00000000000000000
def roots_204 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_206 : Nat := 0x5555000000000000555500000000000055550000000000005555
def goal_206 : Nat := 0xfffcfffcfffcfffcfff0fff0fff0fff0fcfcfcfcfcfcfcfc0000000000000000
def roots_206 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_210 : Nat := 0x50005000000000005000500000000000500050000000000050005
def goal_210 : Nat := 0xffffccccffffccccffff0000ffff0000cccccccccccccccccccc0000cccc0000
def roots_210 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_212 : Nat := 0x110011000000000011001100000000001100110000000000110011
def goal_212 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0f0f0f0f0f0f0f0f00000000000000000
def roots_212 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffcfcfffffcfcfffff0f0fffff0f0fcfcfcfcfcfcfcfccccc0000cccc0000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffccffffffccffffff00ffffff00cccccccccccccccccccc0000cccc0000
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_220 : Nat := 0x11111111000000001111111100000000111111110000000011111111
def goal_220 : Nat := 0xfffffff0fffffff0fffffff0fffffff0f0f0f0f0f0f0f0f00000000000000000
def roots_220 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffcfffffffcfffffff0fffffff0fcfcfcfcfcfcfcfccccc0000cccc0000
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_228 : Nat := 0x1100000011000000110000001100000011000000110000001100000011
def goal_228 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000
def roots_228 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffcfcfcfcfffffffff0f0f0f0fcfcfcfcfcfcfcfcf0f0f0f000000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_232 : Nat := 0x10100000101000001010000010100000101000001010000010100000101
def goal_232 : Nat := 0xffffffffff00ff00ffffffffff00ff00ff00ff0000000000ff00ff0000000000
def roots_232 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffaaffaaffffffffffaaffaaffaaffaaaaaaaaaaff00ff0000000000
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffccffccffffffffff00ff00ffccffccccccccccff00ff0000000000
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffeeffeeffffffffffaaffaaffeeffeeeeeeeeeeff00ff0000000000
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_236 : Nat := 0x111100001111000011110000111100001111000011110000111100001111
def goal_236 : Nat := 0xfffffffffff0fff0fffffffffff0fff0fff0fff0f0f0f0f0fff0fff000000000
def roots_236 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xfffffffffffcfffcfffffffffff0fff0fffcfffcfcfcfcfcfff0fff000000000
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffccccffffffffffff0000cccccccccccccccccccc0000cccc0000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_244 : Nat := 0x11001100110011001100110011001100110011001100110011001100110011
def goal_244 : Nat := 0xfffffffffffff0f0fffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f000000000
def roots_244 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffcfcfffffffffffff0f0fcfcfcfcfcfcfcfcfcfcf0f0cccc0000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_248 : Nat := 0x101010101010101010101010101010101010101010101010101010101010101
def goal_248 : Nat := 0xffffffffffffff00ffffffffffffff00ff00ff0000000000ff00ff0000000000
def roots_248 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffccffffffffffffff00ffccffccccccccccffccff00cccc0000
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def goal_252 : Nat := 0xfffffffffffffff0fffffffffffffff0fff0fff0f0f0f0f0fff0fff000000000
def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffcfffffffffffffff0fffcfffcfcfcfcfcfffcfff0cccc0000
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffefffffffffffffffafffefffefefefefefffefff0eeee0000
def roots_255 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

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
def dictMask : Nat := 0x3ffffffffffffffffffffffffffffffffffff
def wireSAt (i : Nat) : Nat := if i < 3 then (dictB (i / 512) (i / 32 % 16) >>> (146 * (i % 32))) &&& dictMask else 0
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

def symsG : List (List (Nat × Nat)) := [[(0xffff0000ffff0000ffff0000ffff0000, 112)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xffff0000ffff0000ffff0000ffff0000, 112), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xffff0000ffff0000ffff0000ffff0000, 112), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_145 == dom_145) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_145 goalM v ys) : RunD true dom_145 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_145 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_145 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_145 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
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

def isoMvS_164 : List (Nat × Nat) := [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_164 : Lower true dom_164 roots_164 goal_164 4 :=
  lower_iso isoMvS_164 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_145

def isoMvS_168 : List (Nat × Nat) := [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_168 : Lower true dom_168 roots_168 goal_168 4 :=
  lower_iso isoMvS_168 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_145

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
def dictMask : Nat := 0x3fffffffffffffffffffff
def wireSAt (i : Nat) : Nat := if i < 4 then (dictB (i / 512) (i / 32 % 16) >>> (86 * (i % 32))) &&& dictMask else 0
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

def symsG : List (List (Nat × Nat)) := [[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_85 == dom_85) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_85 goalM v ys) : RunD true dom_85 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_85 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_85 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_85 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
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
    [(0xc000c000000000000000000000000000c000c, 16, 18)] (by decide +kernel) (by decide +kernel) lowS_145

theorem lowS_172 : Lower true dom_172 roots_172 goal_172 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x10100000101000000000000000000000101000001010, 32, 36)] (by decide +kernel) (by decide +kernel) lowS_168

def isoMvS_86 : List (Nat × Nat) := [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_86 : Lower true dom_86 roots_86 goal_86 4 :=
  lower_iso isoMvS_86 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_85

def isoMvS_102 : List (Nat × Nat) := [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_102 : Lower true dom_102 roots_102 goal_102 4 :=
  lower_iso isoMvS_102 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_85

def isoMvS_108 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_108 : Lower true dom_108 roots_108 goal_108 4 :=
  lower_iso isoMvS_108 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_85

def isoMvS_149 : List (Nat × Nat) := [(0xffff0000ffff0000ffff0000ffff0000, 112), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_149 : Lower true dom_149 roots_149 goal_149 5 :=
  lower_iso isoMvS_149 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_147

def isoMvS_150 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_150 : Lower true dom_150 roots_150 goal_150 4 :=
  lower_iso isoMvS_150 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_85

def isoMvS_178 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_178 : Lower true dom_178 roots_178 goal_178 4 :=
  lower_iso isoMvS_178 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_85

def isoMvS_180 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_180 : Lower true dom_180 roots_180 goal_180 5 :=
  lower_iso isoMvS_180 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_147

def isoMvS_184 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_184 : Lower true dom_184 roots_184 goal_184 5 :=
  lower_iso isoMvS_184 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_147

def isoMvS_198 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_198 : Lower true dom_198 roots_198 goal_198 4 :=
  lower_iso isoMvS_198 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_85

def isoMvS_204 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff00000000ffffffff00000000, 96), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_204 : Lower true dom_204 roots_204 goal_204 4 :=
  lower_iso isoMvS_204 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_85

def isoMvS_210 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_210 : Lower true dom_210 roots_210 goal_210 4 :=
  lower_iso isoMvS_210 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_85

def isoMvS_212 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff00000000ffffffff00000000, 96), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_212 : Lower true dom_212 roots_212 goal_212 4 :=
  lower_iso isoMvS_212 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_85

def isoMvS_228 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_228 : Lower true dom_228 roots_228 goal_228 5 :=
  lower_iso isoMvS_228 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_147

theorem lowS_103 : Lower true dom_103 roots_103 goal_103 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaa000000aa000000aa000000aa, 64, 65)] (by decide +kernel) (by decide +kernel) lowS_102

theorem lowS_109 : Lower true dom_109 roots_109 goal_109 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x2222000022220000222200002222, 64, 65)] (by decide +kernel) (by decide +kernel) lowS_108

theorem lowS_151 : Lower true dom_151 roots_151 goal_151 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc00cc00000000000000000000000000cc00cc, 16, 18)] (by decide +kernel) (by decide +kernel) lowS_149

theorem lowS_173 : Lower true dom_173 roots_173 goal_173 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x22220000222200000000000000000000222200002222, 128, 129)] (by decide +kernel) (by decide +kernel) lowS_172

def dzo_180_2:=0x4400440044004400000000000000000044004400440044
def gzo_180_2:=0x4400440044004000000000000000000044004000440000
def gsh_180_2:=0x1100110011001000000000000000000011001000110000
theorem lowS_zo_180_2_164:Lower true dzo_180_2 roots_180 gzo_180_2 5:=lower_iso (d1:=dom_180) (roots1:=roots_180) (T1:=gsh_180_2) [(dom_180,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_180_2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x1100000011000000000000000000000011000000110000,0,16)] (by decide +kernel) (by decide +kernel) lowS_164)
namespace S_182
def pairsG : List (Nat × Nat) := [(2,18), (4,36), (4,132), (6,22), (6,38), (6,134), (16,18), (16,144), (20,22), (20,52), (20,148), (32,36), (32,160), (34,38), (34,50), (34,162), (48,50), (48,52), (48,176), (128,132), (128,144), (128,160), (130,134), (130,146), (130,162)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_182.map (· &&& dom_182)
def goalM : Nat := goal_182 &&& dom_182
def NN : Nat → Nat
|4=>2
|5=>3
|6=>1
|_=>0
def HT : Nat → Nat → Nat
|4,0=>0x3ef0f28a68
|5,0=>0xfd5e71e9560a009
|6,0=>0x5584c
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x2a802a802800280000000000000000002a802a802800285500550055005500000000000000000055005500000000aa00aa00000000000000000000000000aa00aa00000000140014001400140000000000000000000000000000000000000002a802a800000000000000000000000002800285500000055000000000000000000000055000000550000a000a000a000a0000000000000000000a000a000a000a154015400000000000000000000000001400140000000022002200220022000000000000000000220022002200225500550055005500000000000000000000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x743109743108743107431064315043210
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>0x15405
|5,0=>0x166418a6
|6,0=>0x1c5
|_,_=>0
def dictMask : Nat := 0x7fffffffffffffffffffffffffffffffffffffffffffff
def wireSAt (i : Nat) : Nat := if i < 10 then (dictB (i / 512) (i / 32 % 16) >>> (183 * (i % 32))) &&& dictMask else 0
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
|0=>0xc2
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>1
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
|5,0=>0x8b
|6,0=>4
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 3 (j % 128); fld (pmPalB (k / 32)) 5 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_180,5,runOps true dom_180 (0,roots_180) ops)] else [])++(if pm.testBit 1 then [(dom_150,4,runOps true dom_150 (0,roots_150) ops)] else [])++(if pm.testBit 2 then [(dom_178,4,runOps true dom_178 (0,roots_178) ops)] else [])++(if pm.testBit 3 then [(dzo_180_2,5,runOps true dzo_180_2 (0,roots_180) ops)] else [])++(if pm.testBit 4 then [(dom_164,4,runOps true dom_164 (0,roots_164) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_182 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_180 _ g hchk
    · exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_180_2_164 _ g hchk
    · exact cpcs (by decide +kernel) lowS_164 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_180 5 s (0, roots_180) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_182 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_180 h

def symsG : List (List (Nat × Nat)) := [[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_182 == dom_182) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_182 goalM v ys) : RunD true dom_182 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_182 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, bar true dom_182 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_182 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_182 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_182 roots_182 goal_182 7 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_182

theorem lowS_182 : Lower true dom_182 roots_182 goal_182 7 := S_182.noCircuit

namespace S_214
def pairsG : List (Nat × Nat) := [(2,18), (2,66), (4,68), (4,132), (6,22), (6,70), (6,134), (16,18), (16,144), (20,22), (20,84), (20,148), (64,66), (64,68), (80,82), (80,84), (80,208), (128,132), (128,144), (130,134), (130,146), (130,194), (192,194), (192,196), (192,208)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_214.map (· &&& dom_214)
def goalM : Nat := goal_214 &&& dom_214
def NN : Nat → Nat
|4=>2
|5=>3
|6=>1
|_=>0
def HT : Nat → Nat → Nat
|4,0=>0x2aa030bc9b
|5,0=>0xfec1e489530a71e
|6,0=>0xfec1e
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x550044000000000055004400000000005500440000000000550044aa00aa0000000000aa00aa00000000008800880000000000880089540000000000000154000000000000011000000000000001100002a802a800000000000000000000000002a802a80000000000000005500000000000000550000000000000055000000000000005500000000000000000000a800a800000000000000000000000000a800a940014000000000014001400000000001400140000000000140014220022000000000022002200000000002200220000000000220022550055000000000055005500000000000000000000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x42150421508421504271502165043210
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>0x15405
|5,0=>0x165418a6
|6,0=>0x1b5
|_,_=>0
def dictMask : Nat := 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffff
def wireSAt (i : Nat) : Nat := if i < 9 then (dictB (i / 512) (i / 32 % 16) >>> (215 * (i % 32))) &&& dictMask else 0
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
|0=>0x7c20
|_=>0
def pmB : Nat → Nat → Nat
|5,0=>5
|6,0=>2
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 2 (j % 128); fld (pmPalB (k / 32)) 5 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_212,4,runOps true dom_212 (0,roots_212) ops)] else [])++(if pm.testBit 1 then [(dom_150,4,runOps true dom_150 (0,roots_150) ops)] else [])++(if pm.testBit 2 then [(dom_86,4,runOps true dom_86 (0,roots_86) ops)] else [])++(if pm.testBit 3 then [(dom_210,4,runOps true dom_210 (0,roots_210) ops)] else [])++(if pm.testBit 4 then [(dom_198,4,runOps true dom_198 (0,roots_198) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_214 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_212 _ g hchk
    · exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · exact cpcs (by decide +kernel) lowS_198 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_212 4 s (0, roots_212) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_214 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_212 h

def symsG : List (List (Nat × Nat)) := [[(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 124)], [(0xffff0000ffff0000ffff0000ffff0000, 112), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xffffffffffffffff0000000000000000, 64), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62)], [(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60), (0xcccccccccccccccccccccccccccccccc, 126)], [(0xffffffffffffffff0000000000000000, 64), (0xffff0000ffff0000ffff0000ffff0000, 112), (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 124), (0xcccccccccccccccccccccccccccccccc, 126)], [(0xffffffffffffffff0000000000000000, 64), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 124), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_214 == dom_214) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_214 goalM v ys) : RunD true dom_214 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_214 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, bar true dom_214 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_214 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_214 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_214 roots_214 goal_214 7 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_214

theorem lowS_214 : Lower true dom_214 roots_214 goal_214 7 := S_214.noCircuit

theorem lowS_234 : Lower true dom_234 roots_234 goal_234 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x40400000404000004040000040400000404000004040000040400000404, 64, 66), (0x50500000505000000000000000000000505000005050000000000000000, 2, 66)] (by decide +kernel) (by decide +kernel) lowS_168

def dzo_172_64:=0x111100001111000000000000000000001111000011110000000000000000
def gzo_172_64:=0x111100001110000000000000000000001110000010100000000000000000
def gsh_172_64:=0x11110000111000000000000000000000111000001010
theorem lowS_zo_172_64_168:Lower true dzo_172_64 roots_172 gzo_172_64 5:=lower_iso (d1:=dom_172) (roots1:=roots_172) (T1:=gsh_172_64) [(dom_172,64)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_172_64) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x10100000101000000000000000000000101000001010,0,4)] (by decide +kernel) (by decide +kernel) lowS_168)
namespace S_236
def pairsG : List (Nat × Nat) := [(4,36), (4,68), (4,132), (8,40), (8,136), (12,44), (12,76), (12,140), (32,36), (32,40), (32,160), (64,68), (72,76), (72,104), (72,200), (96,100), (96,104), (96,224), (128,132), (128,136), (128,160), (192,196), (192,200), (192,224)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_236.map (· &&& dom_236)
def goalM : Nat := goal_236 &&& dom_236
def NN : Nat → Nat
|4=>1
|5=>1
|6=>1
|_=>0
def HT : Nat → Nat → Nat
|4,0=>0xd8bc9
|5,0=>0x9a558
|6,0=>0x525c1
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x4444000044440000444400004444000044440000000000004444000000022000000220000002200000022000000220000002200000022000000220111100000000000011110000000000001111000000000000111100000000808000008080000080800000808000008080000080800000808000008080044000000440000004400000044000000440000000000000044000000022220000222200000000000000000000222200002222000000000000000111100001111000011110000111100000000000000000000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x9591a5644688
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>5
|5,0=>0x56
|6,0=>0xb5
|_,_=>0
def dictMask : Nat := 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def wireSAt (i : Nat) : Nat := if i < 7 then (dictB (i / 512) (i / 32 % 16) >>> (237 * (i % 32))) &&& dictMask else 0
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
    (if pm.testBit 0 then [(dom_228,5,runOps true dom_228 (0,roots_228) ops)] else [])++(if pm.testBit 1 then [(dom_204,4,runOps true dom_204 (0,roots_204) ops)] else [])++(if pm.testBit 2 then [(dzo_172_64,5,runOps true dzo_172_64 (0,roots_172) ops)] else [])++(if pm.testBit 3 then [(dom_172,5,runOps true dom_172 (0,roots_172) ops)] else [])++(if pm.testBit 4 then [(dom_168,4,runOps true dom_168 (0,roots_168) ops)] else [])++(if pm.testBit 5 then [(dom_108,4,runOps true dom_108 (0,roots_108) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_236 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_228 _ g hchk
    · exact cpcs (by decide +kernel) lowS_204 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_172_64_168 _ g hchk
    · exact cpcs (by decide +kernel) lowS_172 _ g hchk
    · exact cpcs (by decide +kernel) lowS_168 _ g hchk
    · exact cpcs (by decide +kernel) lowS_108 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_228 5 s (0, roots_228) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_236 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_228 h

def symsG : List (List (Nat × Nat)) := [[(0xffffffff00000000ffffffff00000000, 96)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_236 == dom_236) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_236 goalM v ys) : RunD true dom_236 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_236 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, bar true dom_236 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_236 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_236 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_236 roots_236 goal_236 7 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_236

theorem lowS_236 : Lower true dom_236 roots_236 goal_236 7 := S_236.noCircuit

def isoMvS_110 : List (Nat × Nat) := [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_110 : Lower true dom_110 roots_110 goal_110 5 :=
  lower_iso isoMvS_110 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_109

def isoMvS_117 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)]
theorem lowS_117 : Lower true dom_117 roots_117 goal_117 5 :=
  lower_iso isoMvS_117 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_109

def isoMvS_118 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_118 : Lower true dom_118 roots_118 goal_118 5 :=
  lower_iso isoMvS_118 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_109

def isoMvS_158 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]
theorem lowS_158 : Lower true dom_158 roots_158 goal_158 5 :=
  lower_iso isoMvS_158 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_103

def isoMvS_186 : List (Nat × Nat) := [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem lowS_186 : Lower true dom_186 roots_186 goal_186 7 :=
  lower_iso isoMvS_186 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_182

def isoMvS_188 : List (Nat × Nat) := [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_188 : Lower true dom_188 roots_188 goal_188 6 :=
  lower_iso isoMvS_188 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_173

def isoMvS_206 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_206 : Lower true dom_206 roots_206 goal_206 5 :=
  lower_iso isoMvS_206 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_109

def isoMvS_218 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff00000000ffffffff00000000, 96), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_218 : Lower true dom_218 roots_218 goal_218 5 :=
  lower_iso isoMvS_218 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_109

def isoMvS_220 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff00000000ffffffff00000000, 96), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]
theorem lowS_220 : Lower true dom_220 roots_220 goal_220 5 :=
  lower_iso isoMvS_220 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_103

def isoMvS_230 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 124)]
theorem lowS_230 : Lower true dom_230 roots_230 goal_230 7 :=
  lower_iso isoMvS_230 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_182

def isoMvS_233 : List (Nat × Nat) := [(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]
theorem lowS_233 : Lower true dom_233 roots_233 goal_233 7 :=
  lower_iso isoMvS_233 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_182

def isoMvS_242 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_242 : Lower true dom_242 roots_242 goal_242 5 :=
  lower_iso isoMvS_242 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_109

def isoMvS_244 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 124), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]
theorem lowS_244 : Lower true dom_244 roots_244 goal_244 6 :=
  lower_iso isoMvS_244 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_151

def dzo_109_16:=0x33330000333300003333000033330000
def gzo_109_16:=0x33320000323200003332000022220000
def gsh_109_16:=0x3332000032320000333200002222
theorem lowS_zo_109_16_108:Lower true dzo_109_16 roots_109 gzo_109_16 5:=lower_iso (d1:=dom_109) (roots1:=roots_109) (T1:=gsh_109_16) [(dom_109,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_109_16) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x2222000022220000222200002222,0,1)] (by decide +kernel) (by decide +kernel) lowS_108)
def dzo_117_8:=0x33003300330033003300330033003300
def gzo_117_8:=0x33003300320032003300330022000000
def gsh_117_8:=0x330033003200320033003300220000
theorem lowS_zo_117_8_85:Lower true dzo_117_8 roots_117 gzo_117_8 5:=lower_iso (d1:=dom_117) (roots1:=roots_117) (T1:=gsh_117_8) [(dom_117,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_117_8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x330033000000000033003300000000,0,32)] (by decide +kernel) (by decide +kernel) lowS_85)
namespace S_125
def pairsG : List (Nat × Nat) := [(1,17), (1,65), (4,36), (4,68), (5,21), (5,37), (5,69), (8,40), (9,25), (9,41), (9,73), (12,44), (12,76), (13,29), (13,45), (13,77), (16,17), (20,21), (20,52), (20,84), (24,25), (24,56), (28,29), (28,60), (28,92), (32,36), (32,40), (33,37), (33,41), (33,49), (33,97), (48,49), (48,52), (48,56), (64,65), (64,68), (72,73), (72,76), (72,104), (80,81), (80,84), (88,89), (88,92), (88,120), (96,97), (96,100), (96,104), (112,113), (112,116), (112,120)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3ffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_125.map (· &&& dom_125)
def goalM : Nat := goal_125 &&& dom_125
def NN : Nat → Nat
|6=>1
|_=>0
def HT : Nat → Nat → Nat
|6,0=>0x3a50
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xcccccccc00000000cccccccc000000033330000333300003333000033330000cc00cc00cc00cc00cc00cc00cc00cc0303030303030303030303030303030308888888888888888888888888888888b3333333333333330000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x2c688
|_=>0
def stOffB : Nat → Nat → Nat
|6,0=>6
|_,_=>0
def dictMask : Nat := 0x3fffffffffffffffffffffffffffffff
def wireSAt (i : Nat) : Nat := if i < 6 then (dictB (i / 512) (i / 32 % 16) >>> (126 * (i % 32))) &&& dictMask else 0
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
    (if pm.testBit 0 then [(dom_117,5,runOps true dom_117 (0,roots_117) ops)] else [])++(if pm.testBit 1 then [(dzo_109_16,5,runOps true dzo_109_16 (0,roots_109) ops)] else [])++(if pm.testBit 2 then [(dom_109,5,runOps true dom_109 (0,roots_109) ops)] else [])++(if pm.testBit 3 then [(dzo_117_8,5,runOps true dzo_117_8 (0,roots_117) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_125 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_117 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_109_16_108 _ g hchk
    · exact cpcs (by decide +kernel) lowS_109 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_117_8_85 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_117 5 s (0, roots_117) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_125 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_117 h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_125 == dom_125) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_125 goalM v ys) : RunD true dom_125 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_125 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, bar true dom_125 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_125 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_125 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_125 roots_125 goal_125 7 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_125

theorem lowS_125 : Lower true dom_125 roots_125 goal_125 7 := S_125.noCircuit

theorem lowS_190 : Lower true dom_190 roots_190 goal_190 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x505050505050505000000000000000005050505050505050, 32, 36)] (by decide +kernel) (by decide +kernel) lowS_186

theorem lowS_222 : Lower true dom_222 roots_222 goal_222 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x55005500000000005500550000000000550055000000000055005500, 128, 136)] (by decide +kernel) (by decide +kernel) lowS_214

theorem lowS_235 : Lower true dom_235 roots_235 goal_235 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c, 64, 66)] (by decide +kernel) (by decide +kernel) lowS_233

theorem lowS_238 : Lower true dom_238 roots_238 goal_238 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x444400004444000044440000444400004444000044440000444400004444, 64, 66)] (by decide +kernel) (by decide +kernel) lowS_236

def dzo_244_2:=0x44004400440044004400440044004400440044004400440044004400440044
def gzo_244_2:=0x44004400440044004400440044004000440044004400440044004000440000
def gsh_244_2:=0x11001100110011001100110011001000110011001100110011001000110000
theorem lowS_zo_244_2_164:Lower true dzo_244_2 roots_244 gzo_244_2 6:=lower_iso (d1:=dom_244) (roots1:=roots_244) (T1:=gsh_244_2) [(dom_244,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_244_2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x11000000110000001100000011000000110000001100000011000000110000,0,16),(0x11001100110011000000000000000000110011001100110000000000000000,0,64)] (by decide +kernel) (by decide +kernel) lowS_164)
namespace S_246
def pairsG : List (Nat × Nat) := [(2,18), (2,66), (4,36), (4,68), (4,132), (6,22), (6,38), (6,70), (6,134), (16,18), (16,144), (20,22), (20,52), (20,84), (20,148), (32,36), (32,160), (34,38), (34,50), (34,98), (34,162), (48,50), (48,52), (48,176), (64,66), (64,68), (80,82), (80,84), (80,208), (96,98), (96,100), (96,224), (112,114), (112,116), (112,240), (128,132), (128,144), (128,160), (130,134), (130,146), (130,162), (130,194), (192,194), (192,196), (192,208), (192,224)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3fffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_246.map (· &&& dom_246)
def goalM : Nat := goal_246 &&& dom_246
def NN : Nat → Nat
|4=>3
|5=>5
|6=>9
|7=>3
|8=>1
|_=>0
def HT : Nat → Nat → Nat
|4,0=>0x9d17b917df6187d
|5,0=>0xdb099b1f0f793064159c27488
|6,0=>0xd7245c2bc09d5ca98d708d98b8902f4eaea4159c3ebe1
|7,0=>0xd7245ae27b6ca6f
|8,0=>0x8ae56
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x4000400040004000400040004000400440044004400440044004400440044a800a800a800a800a800a800a800a80088008800880088008800880088008800000000000000000000000000000001400140014001400140014001400140280028002800280028002800280028000000000000000000000000000000055005000550050005500500055005000550000005500000055000000550000aa00aa00a000a000aa00aa00a000a000aa00aa0000000000aa00aa0000000140014001400140014001400140014000000000000000000000000000000002800280028002800280028002800280028002800280028002800280028002855005500550055005500550055005500000000000000000000000000000000aa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa000000001400140014001400140014001400140140014001400140014001400140014000000002a802a80000000002a802a8000000000280028000000000028002855000000550000005500000055000000550000005500000055000000550000aa00aa00aa00aa00aa00aa00aa00aa00a000a000a000a000a000a000a000a110011001100110011001100110011001100110011001100110011001100110000000002800280000000000280028000000000280028000000000028002855005500550055000000000000000000550055005500550000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0xe448808390691010722440428e44880869c83488083906202964488083913002083488a041c89781072384069122281076244041c861016418804188a0511222810720cc2010c2080861140418820
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>0x2942a805
|5,0=>0x26542a6d8ab0f6
|6,0=>0x5c7acd41a534377acdd98b2b6
|7,0=>0x1c5f53e37
|8,0=>0x786
|_,_=>0
def dictMask : Nat := 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def wireSAt (i : Nat) : Nat := if i < 17 then (dictB (i / 512) (i / 32 % 16) >>> (247 * (i % 32))) &&& dictMask else 0
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
|0=>0x4a14a04a24b54a24a04a14a11ab4a04a14a04a11ab4a04a1
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0x53190000003
|6,0=>0xb2490000081000000000
|7,0=>0x3c5c2d1
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 12 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 31), wireSAt ((code >>> 7) &&& 31)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 9 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmPalB : Nat → Nat
|0=>0x1ff5941e18100
|_=>0
def pmB : Nat → Nat → Nat
|5,0=>0x1201
|6,0=>0x2701104
|7,0=>0x1b6
|8,0=>5
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 3 (j % 128); fld (pmPalB (k / 32)) 7 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_230,7,runOps true dom_230 (0,roots_230) ops)] else [])++(if pm.testBit 1 then [(dom_214,7,runOps true dom_214 (0,roots_214) ops)] else [])++(if pm.testBit 2 then [(dom_242,5,runOps true dom_242 (0,roots_242) ops)] else [])++(if pm.testBit 3 then [(dom_182,7,runOps true dom_182 (0,roots_182) ops)] else [])++(if pm.testBit 4 then [(dom_118,5,runOps true dom_118 (0,roots_118) ops)] else [])++(if pm.testBit 5 then [(dom_244,6,runOps true dom_244 (0,roots_244) ops)] else [])++(if pm.testBit 6 then [(dzo_244_2,6,runOps true dzo_244_2 (0,roots_244) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_246 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_244_2_164 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_230 7 s (0, roots_230) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_246 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_230 h

def symsG : List (List (Nat × Nat)) := [[(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 124)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_246 == dom_246) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_246 goalM v ys) : RunD true dom_246 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_246 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 5 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 9 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 3 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
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

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
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

theorem lowS_252 : Lower true dom_252 roots_252 goal_252 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x1111000011110000111100001111000011110000111100001111000011110000, 128, 144)] (by decide +kernel) (by decide +kernel) lowS_236

def isoMvS_126 : List (Nat × Nat) := [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_126 : Lower true dom_126 roots_126 goal_126 7 :=
  lower_iso isoMvS_126 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_125

def isoMvS_250 : List (Nat × Nat) := [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_250 : Lower true dom_250 roots_250 goal_250 8 :=
  lower_iso isoMvS_250 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_235

def dzo_110_16:=0x55550000555500005555000055550000
def gzo_110_16:=0x55540000545400005554000044440000
def gsh_110_16:=0x5554000054540000555400004444
theorem lowS_zo_110_16_108:Lower true dzo_110_16 roots_110 gzo_110_16 5:=lower_iso (d1:=dom_110) (roots1:=roots_110) (T1:=gsh_110_16) [(dom_110,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_110_16) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x4444000044440000444400004444,0,2)] (by decide +kernel) (by decide +kernel) lowS_108)
def dzo_86_8:=0x550055000000000055005500
def gzo_86_8:=0x540054000000000044000000
def gsh_86_8:=0x5400540000000000440000
theorem lowS_zo_86_8_86:Lower true dzo_86_8 roots_86 gzo_86_8 4:=lower_iso (d1:=dom_86) (roots1:=roots_86) (T1:=gsh_86_8) [(dom_86,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_86_8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [] (by decide +kernel) (by decide +kernel) lowS_86)
def dzo_214_8:=0x55005500000000005500550000000000550055000000000055005500
def gzo_214_8:=0x55005500000000005500550000000000540054000000000044000000
def gsh_214_8:=0x550055000000000055005500000000005400540000000000440000
theorem lowS_zo_214_8_86:Lower true dzo_214_8 roots_214 gzo_214_8 5:=lower_iso (d1:=dom_214) (roots1:=roots_214) (T1:=gsh_214_8) [(dom_214,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_214_8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x550055000000000055005500000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_86)
def dzo_246_8:=0x5500550055005500550055005500550055005500550055005500550055005500
def gzo_246_8:=0x5500550055005500550055005500550055005500540054005500550044000000
def gsh_246_8:=0x55005500550055005500550055005500550055005400540055005500440000
theorem lowS_zo_246_8_86:Lower true dzo_246_8 roots_246 gzo_246_8 6:=lower_iso (d1:=dom_246) (roots1:=roots_246) (T1:=gsh_246_8) [(dom_246,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_246_8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x55005500000000005500550000000000550055000000000055005500000000,0,32),(0x55005500550055005500550055005500000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_86)
def dzo_118_8:=0x55005500550055005500550055005500
def gzo_118_8:=0x55005500540054005500550044000000
def gsh_118_8:=0x550055005400540055005500440000
theorem lowS_zo_118_8_86:Lower true dzo_118_8 roots_118 gzo_118_8 5:=lower_iso (d1:=dom_118) (roots1:=roots_118) (T1:=gsh_118_8) [(dom_118,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_118_8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x550055000000000055005500000000,0,32)] (by decide +kernel) (by decide +kernel) lowS_86)
def dzo_238_16:=0x5555000055550000555500005555000055550000555500005555000055550000
def gzo_238_16:=0x5555000055550000555500005555000055540000545400005554000044440000
def gsh_238_16:=0x555500005555000055550000555500005554000054540000555400004444
theorem lowS_zo_238_16_108:Lower true dzo_238_16 roots_238 gzo_238_16 6:=lower_iso (d1:=dom_238) (roots1:=roots_238) (T1:=gsh_238_16) [(dom_238,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_238_16) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x444400004444000044440000444400004444000044440000444400004444,0,2),(0x555500005555000055550000555500000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_108)
def dzo_248_2:=0x404040404040404040404040404040404040404040404040404040404040404
def gzo_248_2:=0x404040404040404040404040404040004040404040404040404040004040000
def gsh_248_2:=0x101010101010101010101010101010001010101010101010101010001010000
theorem lowS_zo_248_2_168:Lower true dzo_248_2 roots_248 gzo_248_2 6:=lower_iso (d1:=dom_248) (roots1:=roots_248) (T1:=gsh_248_2) [(dom_248,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_248_2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x101000001010000010100000101000001010000010100000101000001010000,0,16),(0x101010101010101000000000000000001010101010101010000000000000000,0,64)] (by decide +kernel) (by decide +kernel) lowS_168)
def dzo_252_2:=0x4444444444444444444444444444444444444444444444444444444444444444
def gzo_252_2:=0x4444444444444444444444444444444044444444444444444444444044440000
def gsh_252_2:=0x1111111111111111111111111111111011111111111111111111111011110000
theorem lowS_zo_252_2_172:Lower true dzo_252_2 roots_252 gzo_252_2 7:=lower_iso (d1:=dom_252) (roots1:=roots_252) (T1:=gsh_252_2) [(dom_252,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_252_2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x1111000011110000111100001111000011110000111100001111000011110000,0,16),(0x1111111111111111000000000000000011111111111111110000000000000000,0,64)] (by decide +kernel) (by decide +kernel) lowS_172)
def dzo_184_64:=0x101010101010101000000000000000001010101010101010000000000000000
def gzo_184_64:=0x101010101010100000000000000000001000100000000000000000000000000
def gsh_184_64:=0x10101010101010000000000000000000100010000000000
theorem lowS_zo_184_64_184:Lower true dzo_184_64 roots_184 gzo_184_64 5:=lower_iso (d1:=dom_184) (roots1:=roots_184) (T1:=gsh_184_64) [(dom_184,64)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_184_64) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [] (by decide +kernel) (by decide +kernel) lowS_184)
def dzo_186_64:=0x505050505050505000000000000000005050505050505050000000000000000
def gzo_186_64:=0x505050505050504000000000000000005040504040404040000000000000000
def gsh_186_64:=0x50505050505050400000000000000000504050404040404
theorem lowS_zo_186_64_184:Lower true dzo_186_64 roots_186 gzo_186_64 6:=lower_iso (d1:=dom_186) (roots1:=roots_186) (T1:=gsh_186_64) [(dom_186,64)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_186_64) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x40404040404040400000000000000000404040404040404,0,2)] (by decide +kernel) (by decide +kernel) lowS_184)
def dzo_170_64:=0x50500000505000000000000000000000505000005050000000000000000
def gzo_170_64:=0x50500000504000000000000000000000504000004040000000000000000
def gsh_170_64:=0x5050000050400000000000000000000050400000404
theorem lowS_zo_170_64_168:Lower true dzo_170_64 roots_170 gzo_170_64 5:=lower_iso (d1:=dom_170) (roots1:=roots_170) (T1:=gsh_170_64) [(dom_170,64)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_170_64) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x4040000040400000000000000000000040400000404,0,2)] (by decide +kernel) (by decide +kernel) lowS_168)
def dzo_232_2:=0x40400000404000004040000040400000404000004040000040400000404
def gzo_232_2:=0x40400000404000004040000040000000404000004040000040000000000
def gsh_232_2:=0x10100000101000001010000010000000101000001010000010000000000
theorem lowS_zo_232_2_168:Lower true dzo_232_2 roots_232 gzo_232_2 5:=lower_iso (d1:=dom_232) (roots1:=roots_232) (T1:=gsh_232_2) [(dom_232,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_232_2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x10100000101000000000000000000000101000001010000000000000000,0,64)] (by decide +kernel) (by decide +kernel) lowS_168)
def dzo_172_2:=0x44440000444400000000000000000000444400004444
def gzo_172_2:=0x44440000444000000000000000000000444000000000
def gsh_172_2:=0x11110000111000000000000000000000111000000000
theorem lowS_zo_172_2_172:Lower true dzo_172_2 roots_172 gzo_172_2 5:=lower_iso (d1:=dom_172) (roots1:=roots_172) (T1:=gsh_172_2) [(dom_172,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_172_2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [] (by decide +kernel) (by decide +kernel) lowS_172)
def dzo_236_2:=0x444400004444000044440000444400004444000044440000444400004444
def gzo_236_2:=0x444400004444000044440000444000004444000044440000444000000000
def gsh_236_2:=0x111100001111000011110000111000001111000011110000111000000000
theorem lowS_zo_236_2_172:Lower true dzo_236_2 roots_236 gzo_236_2 6:=lower_iso (d1:=dom_236) (roots1:=roots_236) (T1:=gsh_236_2) [(dom_236,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_236_2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x111100001111000000000000000000001111000011110000000000000000,0,64)] (by decide +kernel) (by decide +kernel) lowS_172)
def dzo_190_64:=0x5555555555555555000000000000000055555555555555550000000000000000
def gzo_190_64:=0x5555555555555554000000000000000055545554545454540000000000000000
def gsh_190_64:=0x555555555555555400000000000000005554555454545454
theorem lowS_zo_190_64_184:Lower true dzo_190_64 roots_190 gzo_190_64 7:=lower_iso (d1:=dom_190) (roots1:=roots_190) (T1:=gsh_190_64) [(dom_190,64)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_190_64) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x444444444444444400000000000000004444444444444444,0,2),(0x505050505050505000000000000000005050505050505050,0,4)] (by decide +kernel) (by decide +kernel) lowS_184)
def dzo_188_2:=0x444444444444444400000000000000004444444444444444
def gzo_188_2:=0x444444444444444000000000000000004444444044440000
def gsh_188_2:=0x111111111111111000000000000000001111111011110000
theorem lowS_zo_188_2_172:Lower true dzo_188_2 roots_188 gzo_188_2 6:=lower_iso (d1:=dom_188) (roots1:=roots_188) (T1:=gsh_188_2) [(dom_188,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_188_2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x111100001111000000000000000000001111000011110000,0,16)] (by decide +kernel) (by decide +kernel) lowS_172)
def dzo_174_64:=0x555500005555000000000000000000005555000055550000000000000000
def gzo_174_64:=0x555500005554000000000000000000005554000054540000000000000000
def gsh_174_64:=0x55550000555400000000000000000000555400005454
theorem lowS_zo_174_64_168:Lower true dzo_174_64 roots_174 gzo_174_64 6:=lower_iso (d1:=dom_174) (roots1:=roots_174) (T1:=gsh_174_64) [(dom_174,64)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_174_64) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x44440000444400000000000000000000444400004444,0,2),(0x50500000505000000000000000000000505000005050,0,4)] (by decide +kernel) (by decide +kernel) lowS_168)
namespace S_254
def pairsG : List (Nat × Nat) := [(2,18), (2,66), (4,36), (4,68), (4,132), (6,22), (6,38), (6,70), (6,134), (8,40), (8,136), (10,26), (10,42), (10,74), (10,138), (12,44), (12,76), (12,140), (14,30), (14,46), (14,78), (14,142), (16,18), (16,144), (20,22), (20,52), (20,84), (20,148), (24,26), (24,56), (24,152), (28,30), (28,60), (28,92), (28,156), (32,36), (32,40), (32,160), (34,38), (34,42), (34,50), (34,98), (34,162), (48,50), (48,52), (48,56), (48,176), (64,66), (64,68), (72,74), (72,76), (72,104), (72,200), (80,82), (80,84), (80,208), (88,90), (88,92), (88,120), (88,216), (96,98), (96,100), (96,104), (96,224), (112,114), (112,116), (112,120), (112,240), (128,132), (128,136), (128,144), (128,160), (130,134), (130,138), (130,146), (130,162), (130,194), (192,194), (192,196), (192,200), (192,208), (192,224)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3ffffffffffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_254.map (· &&& dom_254)
def goalM : Nat := goal_254 &&& dom_254
def NN : Nat → Nat
|5=>7
|6=>54
|7=>172
|8=>101
|9=>19
|10=>1
|_=>0
def HT : Nat → Nat → Nat
|5,0=>0xfad3dd9957971ea6da63515fd4272c3b971
|6,0=>0xffb7afb051fad3df9dccf8380f511fefd65e2a89e0b96c7edebabeaba701a8cdf9b80f9981d97c0c9032e8dd4b8dd2d8c6488670c84020828c781bf77c43c76a9675a9b724d070cbb66461639725b2905ac60565d6542214bb224ab4e49da243370378b4376892e0ec224b61bd7c1ae251aaf2166970fba109dab090ca0790f074fd02e2a02534
|7,0=>0xaca70ab358ab312aa6b1a9a87a72ada2bafa233ca1117a0773a00639dbc89c7f99c45b9b8259647195cb594af290d0a8c3698bfbe8a6c88a1238858b8670c8656d8602983b80812cb7edc37da3a7d1777b6ca790c973c6d6efde6e8486de1c6cb466c7e26ba8b6b7326b4cf67280650de633506329561eb861d5960986604285f9b25f2cb5d4e55ce9a5b2ba5a1fc58d3d5895c581d4562a755ef454610534d152c8a50abd503e84ec344948c4917e453a340a3c401b43f58a3ed763ddcb3cf693c2fe3a1d039ee738292373ef36d1435feb3455f33fab2f9562f77f2f5142ed642ecd72e9ca2e4b12c91a2b67b2b1692801c2716926e9c26e6b2504924286230e521ecc21bc42081d206271f50d1f1ab1efd81deec1d15f1c77319c9619b9c1491f13f34118db10ce90fba10d29e0b8c10a3e50a2e7072b004bc903519022bf
|7,1=>0xfe050fd685fc50efa985f78edf7859f14bdee8d9e7b59e6c97e671ae25eadefbfdea37dab3dd94aed81b6d63b2d515bd3935d2466ced1ccc963cc1f6cc0dbcadedc6b01c5689c3a19c21ddc1992bc93bb874fb6c3ab5dddb3745af8ffaf80baf4c6af098ae1c0ad304acda2acac1
|8,0=>0xf9503f871af862bf820ff5d28edfd8ed01aec7a7e4407e0108dff09db8bfd5ec7d4ce0c7b8ec78d2bfcb5be285bc880bc1a6bbe2abb322b9f71b9449b8f9db5551b16ebb0b35ae78dadf50ad700a9736a7859a4667a31a89b19a9af28978f98c3758c1628bfd38abbe89904826a481a3c804567c55d7282b71bdb6bd8c669c66410163059625b26200960a685f6255e1b45c77f5c1b25bd46547525448c53763523554f8c04f4424f0344d9844918c445e342f5c42ae4404bf3f8363b92839ead3796e3759d342662a54f290f923a002279c216912081d19d7e197241960c177b1146bc12eb410e6e0fe300b6590a4360a0a0092c3060ac05ef804697
|9,0=>0xed828e5960dfbf9d2646c6d6fa661da4f0b9dbce923f98d4a5898b17b1716dca76d25169e1c5eb27149b80fb4e0b750
|10,0=>0x1b243
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa000088880000aaaa00008888001400140014001400140014001400154141414141414141414141414141414002a802a802a802a802a802a802a802a802a802a80000000002a802a800000000000555500005555000055550000555500004444000044440000444400004444aaaaaaaaaaaa0000aaaaaaaaaaaa0000a0a0a0a0a0a00000a0a0a0a0a0a000015555555555554141555555555555414155555555555541415555555555554142aaaaaaaaaaaa8282aaaaaaaaaaaa828000000000000000000000000000000000000000055555555000000005555555500000000555055500000000055505550000000000a0a0a0a000000000a0a0a0aa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a15401540154015401540154015401540154015401540154015401540154015402aaaaaaaaaaaa8282aaaaaaaaaaaa828282828282828282828282828282828280000000055555555000000005555555500000000505050500000000050505050aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0000000000000000000000000000000015555555555415541555555555541554155555554000000015555555400000002aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa82aa82aa82aa82aa82aa82aa82aa85555555555555550555555555555555055005500550055005500550055005500aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000aaaaaaaa0000000155555555555554015555555555555401554155415541540155415541554154028282828282828282828282828282828282828282828282828282828282828280000000000000000000000000000000055505550555055505550555055505550000a000a000a000a000a000a000a000a000000000000000000000000000000015541554155415541554155415541554155415541554155415541554155415542aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa800000000000000000000000000000005555555500000000555555550000000055555555000000005555555500000000000a000a000a000a000a000a000a000aaaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa15151515151515151515151515151515151515151515151515151515151515152aaaaaaaaaaa80002aaaaaaaaaaa80002aaaaaaaaaaa80002aaaaaaaaaaa80005555000055550000555500005555000055550000555500005555000055550000aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa000000000aaa0aaa00000000155555555555555555555555555555555414141414141414141414141414141422222222222222222222222222222222222222222222222222222222222222225555555555555555000000000000000055555555555555550000000000000000
|0,1=>0xaaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa00000aaa0aaa0aaa00000015401540154015401540154015401540154015401540140015401540154014002a802a80000002802a802a80000002802a802a80000000002a802a800000005555555555555555555555555555555555555555505050505555555550505050aaaaaaaaaaaaaa00aaaaaaaaaaaaaa00aa00aa00aa00aa00aa00aa00aa00aa01415541554155415541554155415541554155415541554141415541554155414282aa82aa828282aa82aa82aa828282aa82aa82aa8282828282aa82aa82828285555555055555550555555505555555055550000555500005555000055550000aaaaaaaa00000000aaaaaaaa00000000aaa0aaa000000000aaa0aaa000000001555555555554000155555555555400000000000000000000000000000000000002a802a80028002802a802a80028002802a802a80028000002a802a800280000055005500550055005500550055005500050005000500000005000500050000aaaaaaaaaaaaa0a0aaaaaaaaaaaaa0a0aaaa0000aaaa0000aaaa0000aaaa000000000000000000015151515151515150000000000000000151515151515151500028002800280028002800280028002800280028002800000028002800280000505050505050505050505050505050505050505050505050505050500000000000088aa000088aa000088aa000088aa000088aa00008888000088aa00008889555555555555555555555555555555555554000155540001555400015554000088888888888888888888000088880000888888888888888888880000888800000550055000000550055005500000055005500550000005000550055000000500000aaaa0000a0a00000aaaa0000a0a00000aaaa0000a0a00000aaaa0000a0a0141414141414141400140014001400141414141414141414001400140000000000280028000000000028002800000002aaaaaaa800000002aaaaaaa800000005555555555555555555055505550555055555555555555550000000000000000aaaaaaaa0000aaaaaaaaaaaa0000aaaaaaaaaaaa00000000aaaaaaaa000000000001555400015554000155540001555400000000000000000000000000000002aaaaaaaaaaaaaaaaaaa80002aaa80002aaaaaaaaaaaaaaaaaaa80002aaa80000055005500000055005500550000005500550055000000000055005500000000000a000a000a000a000a000a000a000a000a000a00000000000a000a000000015555555541414141555555554141414000000000000000000000000000000002aaaaaaaa82828282aaaaaaaa82828282aaaaaaaa82828282aaaaaaaa82828285555555555505550555555555550555055005500550055005500550055005500
|0,2=>0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000155555555554155415555555555415541555555555541554155555555554155400000000000002828000000000000282800000000000000000000000000000000505050505050505050505050505050505050505000000000505050500000000aaaa0000aaaaaaaaaaaa0000aaaaaaaaaaaa0000aaaaa0a0aaaa0000aaaaa0a14155415541554155415541554155415541554155414141414155415541414142aaaaaaaaaaaaaaaaaaaaaaaaaaa80002aaaaaaaaaaaaaaa8000000000000000555555555555555555555555555555555555555544444444555555554444444400000000aaa0aaa000000000aaa0aaa000000000aaa0aaa000000000aaa0aaa1555400015554000155540001555400015555555555554141555555555555414088888888888888888888888888888888888888880000000088888888000000044444444444444440000000000000000444444445555555500000000000000000a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a00000a0a00000a0a00000a0a000155555554141414155555555414141415555555541414000155555554141400000000000028282828000000002828282800000000000000000000000000000000000000000000000000000000000000000005550000055500000555000005550000a0000000a0000000a0000000a0000aaaa0000aaaa0000aaaa0000aaaa000155555555555555555555555555555555555555555555414155555555555541400002aa800002aa800002aa800002aa800002aa800002aa800002aa800002aa80004000400040004000400040004000444444444444444444444444444444444aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa88888888888888888888888888888888000000000001414000000000000141414141414141414141414141414141414000000000000000000000000000000002aaaaaaaaaaa80002aaaaaaaaaaa8000444444445555555544444444555555554444444444444444444444444444444400000000aaaaaaaa00000000aaaaaaaa00000000000000000000000000000000000111100001555400011110000155540001111000011110000111100001111002a802a802a802a802a802a802a802a802a802a80280028002a802a802800285555555555555555555555555555555555555050555550505555505055555050000000000000aaaa000000000000aaaa000000000000a0a0000000000000a0a00001555400015554000155540001555400014140000141400001414000014142aaaa8282aaaa8282aaaa8282aaaa8282aaaa8282aaaa8282aaaa8282aaaa8280000000055555555000000005555555500000000555500000000000055550000
|0,3=>0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a000a000a000a000a000a000a000a015554000155541415555400015554141555540001555400015554000155540002aaa80002aaa8282aaaa80002aaa8282800000000000000000000000000000005555005555550055555500555555005555550055555500005555005555550000000000000000000000000000000000000a0a0a0a0a0a00000a0a0a0a0a0a00015555555551515151555555555151515111111111111111111111111111111112aaaaaaaaaaaaaaaaaaaaaaaa82828282aaaaaaaaaaaaaaa8000000000000000000000000404040400000000040404044444444444444444444444444444444400000000aaaaaaaa00000000aaaaaaaa00000000aaaaa0a000000000aaaaa0a0000155540001555400015554000155540001554000015540000155400001554002a802a802a802a802a802a802a802a802a802a802a8000002a802a802a80000000000000000000000000000000000055555555505050505555555550505050aaaa000aaaaa000aaaaa000aaaaa000aaaaa0000aaaa0000aaaa0000aaaa000155555554141414155555555414141415555555540000000155555554000000002828282828282828282828282828282800000000000000000000000000000000055005500050005005500550005000500550055000000000055005500000000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0a0a0a0a0a0a00000a0a0a0a0a0a00015554141555541415555414155554141555541415555400015554141555540002aaa80002aaaaaaaaaaa80002aaaaaaaaaaa80002aaa80002aaa80002aaa80005555555555555555555555555555555555555555555500005555555555550000aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa00000aaa00000aaa00000aaa000015555555555555555111111111111111155555555555555551111111111111112aaa8000282800002aaa8000282800002aaaaaaaa82828282aaaaaaaa82828285555555555555555111111111111111155555555555555551111111100000000000000000a0a0a0a000000000a0a0a0a000000000a0a0000000000000a0a0001414141414141555541414141414155554141414141414141414141414141414000000000282800000000000028280002aaa80002aaa80002aaa80002aaa80005050555550505555505055555050555550505050505050505050505050505050aaaaaaaaa0a0aaaaaaaaaaaaa0a0aaaaaaaaaaaaa0a0a0a0aaaaaaaaa0a0a0a11155115511551155115511551155115511551155111111111155115511111112aaaaaaaa82828282aaaaaaaa82828282aaa8000282800002aaa8000282800000505050505050000050505050505000005050505050500000505050505050000
|0,4=>0xaaaaaaaaaaaaaaaaaaaaaaaa00000000aaaaaaaaaaaaaaaaaaaaaaaa000000000000000000000000000000000000000155555555555555555555555400000002aaaaaa82aaaaaa82aaaaaa82aaaaaa82aaaaaa82aaaaaa82aaaaaa82aaaaaa80000000000000000555555555555555500000000000000000000000000000000aaaaaaaa00000000aaaaaaaaaaaaaaaaaaaaaaaa00000000aaaaaaaa00000001555555551111111155555555111111115555555511111111555555551111111000000000000000000000000000000002aaaaaaaa22222222aaaaaaaa222222200000000555555550000000055555555000000004444444400000000444444440000aaaa0000aaaa0000aaaa0000aaaa0000aaaa000000000000aaaa000000000000000000015554000000000001555400000000000000000000000000000002aaaaaaa80002aaaaaaaaaaa80002aaaaaaaaaaa800028282aaaaaaa800028280505050505050505050505050505050505050505050500000505050505050000000000000000aaaa0000000000000000aaaaaaaaaaaaaaaa00000000000000000154015401540154015401540154015401540154011001100154015401100112aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa80002aaa8000282800002aaa80002828555555555555444455555555555544444444444444444444444444444444444400aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa000000000000000000000000000000000000000000015554000141400001555400014142aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa80002aa800002aa800002aa800002aa80000050500000505000005050000050500000000000000000000000000000000aaaaaaaa00000a0aaaaaaaaa00000a0aaaaaaaaa00000000aaaaaaaa000000014141555541415555414155554141555541415555414141414141555541414142aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa800000000000000000000000555555550000000055555555000000005555555500000000000000000000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000a0a00000aaaa0000a0a0000000000000000000000000000000015555555555554141555555555555414282828282aaaaaaaa82828282aaaaaaaa82828282aaaa828282828282aaaa8285554555455545554555455545554555444444444444444444444444444444444a0a0a0a0aaaaaaaaa0a0a0a0aaaaaaaaa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a14155415541554155415541554155415541414141414141414141414141414140000000028282aaa8000000028282aaa800000002828282800000000282828285555555555555555005500550055005555555555555555550055005500000000
|0,5=>0x15554141555541415555414155554141555540001555400015554000155540002aaaaaaaaaaaaaaaaaaaaaaa800000000000000000000000000000000000000055555555555555550000000055555555555555555555555500000000000000000000000000000000aaaaaaaaaaaaaaaa0000000000000000aaaaaaaa000000011111111111111111555555555555555511111111111111111111111111111112aaaaaaa88888888aaaaaaaa88888888aaaaaaaa800000002aaaaaaa800000004444444444444444000000000000000055555555555555550000000000000000888888888888888800000000000000008888888888888888888888888888888955555555111111115555555511111110000000000000000000000000000000008888888888888888888888888888888800000000000000000000000000000005555555555555555111111111111111155555555555555550000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x2012808040c0601000b08250d01240009080406012300090f04200d0100080d011d1f00090804161501000908040a021e0100080d011d1c00090f04160d1b010008041602010019040a0601180009080416021701000f04161501000403020114001204110601000f04100d01000f040e0d0100080407060100050403020100
|1=>0x921040301000908040d0131000912040a06010009080401301d000921040a01140009210f0402011d0008040e0d010009080d011d2f0009082e160d01001908040d2d1d000908040d012c00090804070d01000f041602012b001a0f04160201000804011d2a00090f04160d01001912040a02010029040a0601000908040a
|2=>0x8040d013d00093c040a01140009050f040a0201000f043b0d010008043a0d0100090804390d01000908040302010008380a060100091204110d0100040a3706010009080411060100130f0416150d010008040d013500090f040a0201140008040d013400090504030d0100090833160d0100090804320d011d090804100d01
|3=>0x1c0009040a0d011800090804164a01000908040a020100474908040a0d0100090804161501000908160d014600090804030d0100090804020d014500090844040a020100090804160d014300090508040a0201000908040a02014200090841160d0140000908043f0d01000908040d013e00090f041615010008040306010009
|4=>0x841040d011d0009210f0416020100090f04160d01003621040a01570009560804160d0100090804160d015409520804160d0100093c0804160d0100090838040a0d01000908040a0d01500009084f0a0d0100094e0804160d0100090804110d014d000908040a0d4c00090804160d1b0100093c08040a020100090f08160d01
|5=>0x80416320d0109470f04160d01600009210f040a0100090804160130000908040c0d01000b0804200d010009210f0416020100050f040d011d00090825040d011d000905040a0d015700095e08040a060100090804160d0100095d08040d01230009085b04160d01000908045a0d0100090804160d0159090f08160d011f0009
|6=>0x167000908040a0601000947080416660d010009082e160d016000092108040d0145000929040a0d0100090865160d010009050f040a0d010009630804160d0100093c04160d0114000908040d62011d000908040a060100090b082e160d010036212704160d010009050f0416020d010008040a02010013080461160d010009
|7=>0x8040d011d000908041602012b00090804160d016f00091a0804160201000908040a01140009086e04160d010009086d040a0d0100096c08040d011d000908040a640100093c2108040a01000905082e0a0d0100090804160d0100091908040a6b0d01000908040d6a011d0009690804160d0100090804160d0168090804160d
|8=>0x5a0d0100090804160d78000908040a0601000913217204160d0100090f08040a0201000804160d0177000908040a0d0176000908040d017500096c08040a0d0100095f08040d011d00090f0804160d2d000908040a0c0201007408040a0100090873040a0d0100092104160201140009082e040a0201000908040d017000093c
|9=>0x1000908040a017f0009087e04160d0100090f080416320d01090804160d0100097d08045a0d011d00090f04160d011400095808040d011d0009210804166401000912040a0d0100090833160d0100090f08041601300009087c040d011d00090804160d017b00090804160d7a000908040a0d0128090804160d0179090f0804
|10=>0xa8201000908040a02014d0009080416150d010009082e040d011d00090804110d01001308040a0c060100090804160d01810009270825160d01000908040a020114000921082e040a01000908040d01801d00090508160d015300090804020d011d000908040d012400090f04160d012b000908040a06015700091a0f04160d
|11=>0x1d000908040d014500098b0804160d0100090804168a0d01000908041602010022210f040d011d00092104160d011400090f04160d010088090804160d0187000908041606015c00091a082e160d010009860804160d010009080416850d01000908040a0d84000908040a830100090f08040a06010009040a370d0100090804
|12=>0xf084104160201000804110a060100090804160d01910009210804168301000908040a0d01400009083304160d0100090804160d9000090f0416020d0114003c08040a01000908160d011f000908040d011d89000908040d018f00090804160d018e000908040a0d018d000908380a0d0100093c08040d0145000908040d4b01
|13=>0x9260825160d01000926086d04160d0100090804160d014200090804160d6a0100094708040a0d014d000905082e160d0100090804160d015300090f04160d010022950804160d0100090804160d019400090f0804020d011d0008043b0d0100090804160d0193091a2108040a01000908040d019200090804060d011d0009
|14=>0xd0100090804160d015500099b0804160d0100095f0804160d010009270804160d010009990804160d0100090804160d019800090f0804160d0100713c0804160d0100096c0804160d0100090804160d2d00090804160d019700090804160d0100099608040a020100090804160d01000922084404160d010009210804160d01
|15=>0x90804160d016000092108040a0100090804160d0100095108040a0d0100090b9e0804160d01000905080416020d010009080416020d01420009580804160d0100092108041602010009089d040a0d010009080416320d01095e08040a0d0100090f082504160d0100091a210804160d0100090804160d010009360f08410416
|16=>0xf0804160d0100093c0f0804160d0100090804160da300096c0f0804160d0100090f0804160d6a0100093c080416020d0100090804160d010009a208040a0d010009470804160d01a009720804160d0100090804160d480100090508040a0d01000908040d011d000908040a06010009080416020d01004708440416020d0100
|17=>0x16020d0100090804160d0114000908a704160d010009080416640d0100093c210804160d010009580f0804160d010009080416060d010009470804160da600090841041602010009a50804160d0100090804160d0140000908040a0d01000913050825160d0100090804160d01a409050841160d010009210f04160d0100095f
|18=>0x1c00090804160d015c00090f08040a0d010009490804160d010009082e040a0d01000908040a0c0d0100090f082e04160d0100090804160d010009a90804160d012b00090f080416020d01001a0804160d0100090804160d01a80009740804160d0100090f080416020d0100090f08040d011d000908040a0d01570009082e04
|19=>0x4160d010009080416830d01000908aa04160d0100090f080416060d0100090804110a0d0100090804160d0100098c050f04160d010009080416020d0114000921082e04160d0100090f0804160d0189000908412e160d01000908040a0d010009260f0804160d4b0100090804160d01008809210804160d0100095108160d01
|20=>0x4160d010009a19a0804160d0100090804160d01000971080416060d0100099f0804160d010009210804160d0100090804160d018900090804160d010009260804160d4b0100090804160d0100099c08040a0d0100090f0804160d010009082e04160d010009080416020d0100090804160d6a0100090804160d010009470508
|21=>0x804160d010009082504160d010009084104160d01000908
|_=>0
def stOffB : Nat → Nat → Nat
|5,0=>0x24601e60186012600c600660006
|6,0=>0x194718d7187618071797172716b7165615e71577151614a7144613d7136712f71287121711a7113710c710570fe70f860f170ea70e370dc70d570ce70c770c070b970b270ac60a5709e70977090708a6083707d6076706f70687062605b7054704d7046703f70387031702a7
|7,0=>0x37c8374836c8364835c8355734e7346833e8336832e8326831f7317830f8308730082f882f082e972e272db72d472cd72c582bd82b582ad82a5829e7296828f728872808278827082697262725a8253724b8243823b8233822c7224821c8215720d820581fd81f671ef71e871e081d971d271cb71c381bb81b381ab81a3819b8
|7,1=>0x56b8563855c7554854c8544853c8534852c8524851c8515750d850584fd84f674ee84e684de84d684ce84c684be84b774b074a884a084988491748a7483747b8474746c8464845d7455844d8446743e8436842e84277420741884108408840173f983f183e983e183da73d283ca83c283bb73b383ab83a3839b8393838b83847
|7,2=>0x6bd76b586ad86a5869e7697768f8688768086788670866886608658865086497641863a7633762b8624761c8614860d760585fd85f675ee85e685df75d785cf85c785bf85b785af85a7859f8598759175898582757b75738
|8,0=>0x8c078b888b088a888a088988891788988818878986f9868785f9856984d9845883d8836782e8826881e88177810780887ff97f787f077e887e087d887cf97c697be87b687ae87a7779f8796978d9785877c9774876c8764875c8754874c8744873c8734872d7725871d8716770e870686fd96f586ed86e586dc96d486cc86c48
|8,1=>0x9f289ea89e199d989d189c989c099b799ae99a6899e8995998d8984997d7975896d8965895d8955894c9944893c8934892c8924891c8913990b890388fa98f288ea88e288d998d098c79
|9,0=>0xa898a818a798a718a698a618a598a518a498a418a398a318a2a7a228a1a8a128a0a8a0289fa8
|10,0=>0xa917
|_,_=>0
def dictMask : Nat := 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def wireSAt (i : Nat) : Nat := if i < 171 then (dictB (i / 512) (i / 32 % 16) >>> (255 * (i % 32))) &&& dictMask else 0
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
|0=>0x809458d90509020110d0943c280809458350413428240a094204d0a09058350811028250a09028250809434d9050902011080d43c280809458350813428240d0943c5b08094302d0a0982827160d42025081342824160d434250813c28240a09828272716c20990f0ac20250809458892109020350213c28240d09468240811828250813428240a094302d0a0982827
|1=>0x80a85835550083c0708094214d2e0dc1025215148426080d4104f0a09058353c04420090d094044f0a09058350502020110d0942009160d4342508094112e0109420460a09458350d36c14240804458350809834250d36414240804411220147420260f0a02025160d4f05b0802458350d09458350d09458350d09420250d3641424080443c2808094f023210942035
|2=>0x809421910d264102608144200a0d0943c5b080942826160d410250509020110826410260a09058350d09418030d0142025160d57c370f00420250a0982827160d458892109020350d0942025080d43c5b080943c5b08094202a160d42029160d43405165c83c37080943c5b0809400d90509020115804c3c05080943c5b080943425080942035080941424080442035
|3=>0x80d42824160d43405085148426080d42025160d434250f16c20252501c2025040042827160d434252109c2035160d4200a0d09458350d095c85b087158025050dc20110802858350d09411710f0dc20250809458350d26410262109420350409458351a0908411080d43c5b0809554010f01c2025160d420260d014f05b21094204f0a09058350422c8424080d45835
|4=>0xa09c58350d014209904098200a160d43425080d458350f16c20250f16c20252716c2099040983405080a858350809444370a09458350600c20250d014ac262104c20350f16c20250802820250d0943c5b08094349904098204d0a0905835042248424080d57c370f00420250f16c2025012248424080d4004d0a0905835002248424080d434750f16c20250122c8424
|5=>0x8044200a0d0948425080d458355804c3c05080943c5b080957c5b08094104d0a09058350802434250f16c20253c16c20090d09422314109810350d0948424080d43c5b08094f023210942035080942226000943c3708094044d0a0905835160d4351d080985835080943405081102825160d4342d0a0985835160d434250d3641424080443c5b0809428240a0945835
|6=>0x809420090d0941425080449407040043c130809414260804458350d0948424080d410090d0941026080d4102604004111d08098100a0d094202601004102a160d4102508044b83704094202521090203508424100a0d095b0370509420110d0943c5b0809458d90509020110036c1424080442035160d420250f16c2025080942825160d43545210982035013641424
|7=>0x80142026160d402850109821c50d098051d080982011160d43c5b0809458350d01420260d09410090d0941437080442035160d48426080d42826160d67c270800420110d094100a0d0943c050809420350d0941029160d418030d0142029160d42025040048411080d41424080441035080943c07080942271000983c010809420990409a682708014212e010943426
|8=>0x80967c24080048413080d420250d0948411080d4011d080988427080d420250d0943c5b08094202a160d410250d094200a0d0943c03080943499040988425080d43c050809420260d01406710009810350d09422850109820ba040942824160d42011040040287010981035080442025080d43c01080943c35080940673000983c110809404010809420090d0966824
|9=>0x400410350109820050d0983405080042035000941026010940026160d4202504094342501004202608044351d0809811c50d09820250d0142825160d50426040d4202508044200a0d0941025080d42025000941025040d41026160d40425080942226000948426080d4112e010943c37080942025160d41427080441025160d42827160d41025
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0x330000000000c000
|6,0=>0x1150432000040300003c400000000e103620c903020b882a4000000000000000000000000026400002420000000084c000000000000000000750000070400000001840588000050812204080c40000000024c00000000810188000
|7,0=>0xc93000000031c8c43304cbf22f0cb932dc8b522c8cb020000ad30000ab20000a92298ca33280c9d326c899225c8943000091300008f2230c89321c8843204c7e300007b31e0c75300000001c8c6f300006c31a4c66318cc603174c5a30000573150c51313c84d200004b21248000
|7,1=>0x514d432500d3d300013b24e0d3624d080004c892f300012c34ac52830001253488d202474d1b2464916344cd103438800042cd083414d0233fccfc33e4cf63000000000000003d08f133b8ceb30000e9239c8e520000000388c00037ccdc30000db1360cd623508d130000cf20000cc3
|7,2=>0x670d993658d933640d8d362c98a162098716148000608c00000017f35f497a35dcd7525cc800000017035b896c25a4d663000163358495e356cc00056480000000000558d533540d4d3528d482
|8,0=>0x874a1b2864a172854a132844a0f2834a0b2824a072814a0328049ff27f49fb27e49f727d49f327c49ef27b49eb27a49e727949e327849df27749db27649d727549d327449cf27349cb27249c727149c327049bf26f49bb26e49b726d49b326c49af26b49ab26a49a726949a3268499f2
|8,1=>0x2672994a632984a5f2974a5b2964a572954a532944a4f2934a4b2924a472914a432904a3f28f4a3b28e4a3728d4a3328c4a2f28b4a2b28a4a272894a232884a1f2
|9,0=>0x27b19e867919e067719d867519d067319c867119c066f19b866d19b066b19a86691
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
|0=>0x94080000000420400000002002000000010000000000070180000000280c00000001100000000008000000000038180000000102000000000602000000002a1000000001100000000008140000000040200000000200000000000840000000003f40000000017a00000000088000000000408000000002000000000005000000000021000000000100000000000480000000002000000000008000000000020000000000080000000000200000000000
|1=>0x1671d8000000b087c000000584360000002800000000010008000000080020000000400000000001c80000000006200800000030a000000001001600000008002000000040000000000188340000000bd04000000052a1000000029408000000140040000000880000000004281000000021400000000108000000000810200000004080000000020100000000100300000000801000000004001000000020000000000080200000000400800000002000
|2=>0x86280800000430a6400000218402000001052870000008294180000041481c0000020a4060000010508100000082810000000410a840000020850600000104228000000821018000004108040000020840000000104021000000820060000004100040000020800000000100b030000008013e0000004008f400000200400000000af21b00000043804000000200000000000f96360000004c401000000220000000001000000000005c43e0000002d21b
|3=>0x20694d80000103486c000008185360000040c21b00000204940800001000004000008000000000032601f00000190114800000ab087c0000044c43e000001a021d000000b611d8000005b086c0000028950400000141202000000a0081800000500060000002590020000012c61b0000009614d8000004b087c000002584360000012c03b0000009300f800000480af4000002396020000011ca010000008e201800000433a0c000002194020000010c811
|4=>0x240010900001117286c000088184400000382001300000c801090000060b086c00003008426000018002120000048640080000202004c0000100042600000800013000004000090000015b08ec00000ab96360000054cebb000002a630d80000153080400000a5843e0000052c21b0000028e58d800001471c6c00000a38c360000051c4010000028614f80000143087c00000a184360000045c73b00000216f1d8000010b486c000008584360000040da20
|5=>0x800009610d8400000b08f412000a58432090000242190410028610d8200034b086c10001a5843208000c2c21b0400061610c8200014b086c10000a58432050000082230100011610d8080004b087c0400010045a0200002e21f010000030060080000100300400000041a0100000820100800000100802001061004008000f8c3600400000000001a000000480080203087c0010420900200080000002000300110018000800000040002000000200008020000
|6=>0x1800008202318400061610ca200030b0865000010404224100022c21f2080009600d9040000b087c8200005041a200009002101000041610d8800020008443a0000184361900012c21b0c80008610d8640000b086c320000184361820090c21b0c00009610d86000043086c240006584361200022c2190900009610e840000cb08e42000064043a100002ac21f0800015610e840000ab0864200002585721000012c23d
|_=>0
def pmB : Nat → Nat → Nat
|5,0=>0x200000200
|6,0=>0xd02001d000e00001a02380202080000000a0000001b0002001c2a00000000004400200000150200023902290000010003200200
|7,0=>0x8046394073c2a043400436e009520aa0011252d14a010655211040024a5242c249c507100000707a4116f80002a044d190001009d0800a8681e13a34205077a00980700285d2409081e3b937727034c00104631a15f51530c3a169f0036002da211235166170096010800006d011860121f11372470004a7a62282200040400
|7,1=>0x5501012b4b352279062193004e0000a7497b7a33020000610b3b24010753282eab0006000000978e9864880f
|8,0=>0x86b2998a69745125ac7873d9cd57bb7d90c37291adcf405548cf7e565e84ae7ccd6958dc9bcc67b5c88bd869755bb43069b1d22fb98fbd87b93f6c9a5aaf76838589cd264fdb59a9bc9ed547c032b7cad1c1b7da5c7fc2a6bec69285b054d7c73ed445c5b3
|9,0=>0xd641b6b88d9ace82d0bfbacb816bc98cd36ac4
|10,0=>0x3d
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 8 (j % 128); fld (pmPalB (k / 32)) 45 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_246,9,runOps true dom_246 (0,roots_246) ops)] else [])++(if pm.testBit 1 then [(dom_186,7,runOps true dom_186 (0,roots_186) ops)] else [])++(if pm.testBit 2 then [(dzo_110_16,5,runOps true dzo_110_16 (0,roots_110) ops)] else [])++(if pm.testBit 3 then [(dom_238,8,runOps true dom_238 (0,roots_238) ops)] else [])++(if pm.testBit 4 then [(dom_252,8,runOps true dom_252 (0,roots_252) ops)] else [])++(if pm.testBit 5 then [(dzo_86_8,4,runOps true dzo_86_8 (0,roots_86) ops)] else [])++(if pm.testBit 6 then [(dom_198,4,runOps true dom_198 (0,roots_198) ops)] else [])++(if pm.testBit 7 then [(dom_86,4,runOps true dom_86 (0,roots_86) ops)] else [])++(if pm.testBit 8 then [(dom_242,5,runOps true dom_242 (0,roots_242) ops)] else [])++(if pm.testBit 9 then [(dom_222,8,runOps true dom_222 (0,roots_222) ops)] else [])++(if pm.testBit 10 then [(dzo_214_8,5,runOps true dzo_214_8 (0,roots_214) ops)] else [])++(if pm.testBit 11 then [(dom_210,4,runOps true dom_210 (0,roots_210) ops)] else [])++(if pm.testBit 12 then [(dom_218,5,runOps true dom_218 (0,roots_218) ops)] else [])++(if pm.testBit 13 then [(dom_234,6,runOps true dom_234 (0,roots_234) ops)] else [])++(if pm.testBit 14 then [(dom_250,8,runOps true dom_250 (0,roots_250) ops)] else [])++(if pm.testBit 15 then [(dom_190,8,runOps true dom_190 (0,roots_190) ops)] else [])++(if pm.testBit 16 then [(dzo_246_8,6,runOps true dzo_246_8 (0,roots_246) ops)] else [])++(if pm.testBit 17 then [(dom_236,7,runOps true dom_236 (0,roots_236) ops)] else [])++(if pm.testBit 18 then [(dzo_118_8,5,runOps true dzo_118_8 (0,roots_118) ops)] else [])++(if pm.testBit 19 then [(dom_206,5,runOps true dom_206 (0,roots_206) ops)] else [])++(if pm.testBit 20 then [(dom_126,7,runOps true dom_126 (0,roots_126) ops)] else [])++(if pm.testBit 21 then [(dzo_238_16,6,runOps true dzo_238_16 (0,roots_238) ops)] else [])++(if pm.testBit 22 then [(dzo_248_2,6,runOps true dzo_248_2 (0,roots_248) ops)] else [])++(if pm.testBit 23 then [(dzo_252_2,7,runOps true dzo_252_2 (0,roots_252) ops)] else [])++(if pm.testBit 24 then [(dom_184,5,runOps true dom_184 (0,roots_184) ops)] else [])++(if pm.testBit 25 then [(dzo_184_64,5,runOps true dzo_184_64 (0,roots_184) ops)] else [])++(if pm.testBit 26 then [(dom_214,7,runOps true dom_214 (0,roots_214) ops)] else [])++(if pm.testBit 27 then [(dom_244,6,runOps true dom_244 (0,roots_244) ops)] else [])++(if pm.testBit 28 then [(dzo_186_64,6,runOps true dzo_186_64 (0,roots_186) ops)] else [])++(if pm.testBit 29 then [(dzo_170_64,5,runOps true dzo_170_64 (0,roots_170) ops)] else [])++(if pm.testBit 30 then [(dzo_232_2,5,runOps true dzo_232_2 (0,roots_232) ops)] else [])++(if pm.testBit 31 then [(dom_182,7,runOps true dom_182 (0,roots_182) ops)] else [])++(if pm.testBit 32 then [(dzo_172_2,5,runOps true dzo_172_2 (0,roots_172) ops)] else [])++(if pm.testBit 33 then [(dzo_236_2,6,runOps true dzo_236_2 (0,roots_236) ops)] else [])++(if pm.testBit 34 then [(dom_230,7,runOps true dom_230 (0,roots_230) ops)] else [])++(if pm.testBit 35 then [(dom_118,5,runOps true dom_118 (0,roots_118) ops)] else [])++(if pm.testBit 36 then [(dzo_190_64,7,runOps true dzo_190_64 (0,roots_190) ops)] else [])++(if pm.testBit 37 then [(dom_110,5,runOps true dom_110 (0,roots_110) ops)] else [])++(if pm.testBit 38 then [(dom_158,5,runOps true dom_158 (0,roots_158) ops)] else [])++(if pm.testBit 39 then [(dzo_188_2,6,runOps true dzo_188_2 (0,roots_188) ops)] else [])++(if pm.testBit 40 then [(dzo_174_64,6,runOps true dzo_174_64 (0,roots_174) ops)] else [])++(if pm.testBit 41 then [(dom_188,6,runOps true dom_188 (0,roots_188) ops)] else [])++(if pm.testBit 42 then [(dom_172,5,runOps true dom_172 (0,roots_172) ops)] else [])++(if pm.testBit 43 then [(dom_108,4,runOps true dom_108 (0,roots_108) ops)] else [])++(if pm.testBit 44 then [(dom_220,5,runOps true dom_220 (0,roots_220) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_254 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_110_16_108 _ g hchk
    · exact cpcs (by decide +kernel) lowS_238 _ g hchk
    · exact cpcs (by decide +kernel) lowS_252 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_86_8_86 _ g hchk
    · exact cpcs (by decide +kernel) lowS_198 _ g hchk
    · exact cpcs (by decide +kernel) lowS_86 _ g hchk
    · exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_214_8_86 _ g hchk
    · exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_246_8_86 _ g hchk
    · exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_118_8_86 _ g hchk
    · exact cpcs (by decide +kernel) lowS_206 _ g hchk
    · exact cpcs (by decide +kernel) lowS_126 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_238_16_108 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_248_2_168 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_252_2_172 _ g hchk
    · exact cpcs (by decide +kernel) lowS_184 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_184_64_184 _ g hchk
    · exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_186_64_184 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_170_64_168 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_232_2_168 _ g hchk
    · exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_172_2_172 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_236_2_172 _ g hchk
    · exact cpcs (by decide +kernel) lowS_230 _ g hchk
    · exact cpcs (by decide +kernel) lowS_118 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_190_64_184 _ g hchk
    · exact cpcs (by decide +kernel) lowS_110 _ g hchk
    · exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_188_2_172 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_174_64_168 _ g hchk
    · exact cpcs (by decide +kernel) lowS_188 _ g hchk
    · exact cpcs (by decide +kernel) lowS_172 _ g hchk
    · exact cpcs (by decide +kernel) lowS_108 _ g hchk
    · exact cpcs (by decide +kernel) lowS_220 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_246 9 s (0, roots_246) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_254 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_246 h

def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {v ys} (h : RunD true dom_254 goalM v ys) : RunD true dom_254 goalM v (ori ys) := h
def Z (s : Nat) := barP true dom_254 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 7 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 54 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 54 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 172 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 172 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 101 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 101 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 19 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 19 0 = true)
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

theorem lowS_255 : Lower true dom_255 roots_255 goal_255 12 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 16, 17)] (by decide +kernel) (by decide +kernel) lowS_254

theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
    (hhas : ∃ g ∈ gates, isNotGate g = true) : 13 ≤ gates.length := by
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [0, 1] }, { op := GateOp.or, inputs := [4, 6] }, { op := GateOp.and, inputs := [8, 9] }, { op := GateOp.or, inputs := [2, 3] }, { op := GateOp.or, inputs := [5, 7] }, { op := GateOp.and, inputs := [11, 12] }, { op := GateOp.or, inputs := [0, 4] }, { op := GateOp.or, inputs := [14, 5] }, { op := GateOp.and, inputs := [7, 15] }, { op := GateOp.and, inputs := [2, 6] }, { op := GateOp.or, inputs := [10, 13] }, { op := GateOp.or, inputs := [18, 16] }, { op := GateOp.or, inputs := [19, 17] }]

theorem wit_mono : ∀ g ∈ witGates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 20⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
  have hwit : (execN witGates xs256).getD 20 0 &&& mask256 = goal_255 &&& mask256 := by decide +kernel
  intro x
  have hlt : natOfBits8 x < 256 := natOfBits8_lt x
  have hpt : pt8 (natOfBits8 x) = x := pt8_natOfBits8 x
  generalize hr : natOfBits8 x = r at hlt hpt
  have h1 := execN_bit witGates xs256 r hlt (fun g hg => by
    have hm := wit_mono g hg
    rcases hm.1 with h | h <;> simp [h])
  have h2 := congrArg (fun l => l.getD 20 false) h1
  rw [xs256_bits ⟨r, hlt⟩, hpt] at h2
  have hgd : ((execN witGates xs256).map (·.testBit r)).getD 20 false =
      ((execN witGates xs256).getD 20 0).testBit r := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases (execN witGates xs256)[20]? with | none => simp | some v => rfl
  rw [hgd] at h2
  have hbit : ((execN witGates xs256).getD 20 0).testBit r = goal_255.testBit r := by
    have hb := congrArg (fun v => v.testBit r) hwit
    simp only [Nat.testBit_and, mask256_bit, hlt, decide_true, Bool.and_true] at hb
    exact hb
  have hres := h2.symm.trans (hbit.trans (goal_eq_f ⟨r, hlt⟩))
  rw [hpt] at hres
  exact hres

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
  · push Not at hhas
    refine ⟨gates, o, ?_, le_rfl, hev⟩
    intro g hg
    obtain ⟨h1, h2⟩ := hfan g hg
    refine ⟨?_, h2⟩
    rcases h1 with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exfalso; have := hhas g hg; simp [isNotGate, h1] at this

end PEqualNP.Outside.L_meta_31599_aux

theorem PEqualNP.Outside.L_meta_31599 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_31599_aux.main
