import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_32095_aux
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
def dom_73 : Nat := 0x3030000000000000303
def goal_73 : Nat := 0xffaaffaaffaaffaaaa00aa00aa00aa00ffaaffaaffaaffaaaa00aa00aa00aa00
def roots_73 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_75 : Nat := 0xf0f0000000000000f0f
def goal_75 : Nat := 0xffeeffeeffeeffeeaa00aa00aa00aa00ffeeffeeffeeffeeaa00aa00aa00aa00
def roots_75 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_83 : Nat := 0xf000f00000000000f000f
def goal_83 : Nat := 0xeeeeeeeeeeeeeeeecccc0000cccc0000eeeeeeeeeeeeeeeecccc0000cccc0000
def roots_83 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_87 : Nat := 0xff00ff0000000000ff00ff
def goal_87 : Nat := 0xeeeeeeeeeeeeeeeecccc0000cccc0000eeeeeeeeeeeeeeeecccc0000cccc0000
def roots_87 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_90 : Nat := 0x50505050000000005050505
def goal_90 : Nat := 0xffccffccffccffcccccc0000cccc0000ffccffccffccffcccccc0000cccc0000
def roots_90 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffeeffeeffeeffeeeeccaa00eeccaa00ffeeffeeffeeffeeeeccaa00eeccaa00
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xeeeeeeeeeeeeeeeecccc0000cccc0000eeeeeeeeeeeeeeeecccc0000cccc0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfefefefeeeeeeeeefcfcf0f0cccc0000fefefefeeeeeeeeefcfcf0f0cccc0000
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_137 : Nat := 0x30300000000000000000000000000000303
def goal_137 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_137 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_141 : Nat := 0x333300000000000000000000000000003333
def goal_141 : Nat := 0xfffafffafffafffafffafffafffafffaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_141 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_147 : Nat := 0xf000f000000000000000000000000000f000f
def goal_147 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaacccc0000cccc0000cccc0000cccc0000
def roots_147 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_150 : Nat := 0x55005500000000000000000000000000550055
def goal_150 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0cccc0000cccc0000cccc0000cccc0000
def roots_150 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_151 : Nat := 0xff00ff00000000000000000000000000ff00ff
def goal_151 : Nat := 0xfffffafafffffafafffffafafffffafacccc0000cccc0000cccc0000cccc0000
def roots_151 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_153 : Nat := 0x303030300000000000000000000000003030303
def goal_153 : Nat := 0xffffffaaffffffaaffffffaaffffffaaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_153 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_154 : Nat := 0x505050500000000000000000000000005050505
def goal_154 : Nat := 0xffffff00ffffff00ffffff00ffffff00cccc0000cccc0000cccc0000cccc0000
def roots_154 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffffffaaffffffaaffffffaaffffffaaeeccaa00eeccaa00eeccaa00eeccaa00
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_157 : Nat := 0x3333333300000000000000000000000033333333
def goal_157 : Nat := 0xfffffffafffffffafffffffafffffffaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_157 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_158 : Nat := 0x5555555500000000000000000000000055555555
def goal_158 : Nat := 0xfffffff0fffffff0fffffff0fffffff0cccc0000cccc0000cccc0000cccc0000
def roots_158 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_159 : Nat := 0xffffffff000000000000000000000000ffffffff
def goal_159 : Nat := 0xfffffffafffffffafffffffafffffffaeeccaa00eeccaa00eeccaa00eeccaa00
def roots_159 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_164 : Nat := 0x110000001100000000000000000000001100000011
def goal_164 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f000000000f0f0f0f000000000
def roots_164 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_165 : Nat := 0x330000003300000000000000000000003300000033
def goal_165 : Nat := 0xfffffffffafafafafffffffffafafafaf0f0f0f000000000f0f0f0f000000000
def roots_165 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_169 : Nat := 0x3030000030300000000000000000000030300000303
def goal_169 : Nat := 0xffffffffffaaffaaffffffffffaaffaaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_169 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_172 : Nat := 0x11110000111100000000000000000000111100001111
def goal_172 : Nat := 0xfffffffffff0fff0fffffffffff0fff0f0f0f0f000000000f0f0f0f000000000
def roots_172 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xfffffffffffafffafffffffffffafffafaf0faf0aa00aa00faf0faf0aa00aa00
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_178 : Nat := 0x500050005000500000000000000000005000500050005
def goal_178 : Nat := 0xffffffffffff0000ffffffffffff0000cccc0000cccc0000cccc0000cccc0000
def roots_178 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def goal_179 : Nat := 0xffffffffffffaaaaffffffffffffaaaacccc0000cccc0000cccc0000cccc0000
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_180 : Nat := 0x1100110011001100000000000000000011001100110011
def goal_180 : Nat := 0xfffffffffffff0f0fffffffffffff0f0f0f0f0f000000000f0f0f0f000000000
def roots_180 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_181 : Nat := 0x3300330033003300000000000000000033003300330033
def goal_181 : Nat := 0xfffffffffffffafafffffffffffffafaf0f0f0f000000000f0f0f0f000000000
def roots_181 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_182 : Nat := 0x5500550055005500000000000000000055005500550055
def goal_182 : Nat := 0xfffffffffffff0f0fffffffffffff0f0fcfcf0f0cccc0000fcfcf0f0cccc0000
def roots_182 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def goal_183 : Nat := 0xfffffffffffffafafffffffffffffafafcfcf0f0cccc0000fcfcf0f0cccc0000
def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def goal_186 : Nat := 0xffffffffffffff00ffffffffffffff00cccc0000cccc0000cccc0000cccc0000
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffffffffffaaffffffffffffffaaeeccaa00eeccaa00eeccaa00eeccaa00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333
def goal_189 : Nat := 0xfffffffffffffffafffffffffffffffafaf0faf0aa00aa00faf0faf0aa00aa00
def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xfffffffffffffff0fffffffffffffff0fcfcf0f0cccc0000fcfcf0f0cccc0000
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffffffffffafffffffffffffffafefcfaf0eeccaa00fefcfaf0eeccaa00
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_193 : Nat := 0x3000000000000000300000000000000030000000000000003
def goal_193 : Nat := 0xffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000000000000
def roots_193 : List Nat := [xs256.getD 0 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_195 : Nat := 0xf000000000000000f000000000000000f000000000000000f
def goal_195 : Nat := 0xffffffffffffffffaaaaaaaaaaaaaaaaeeeeeeeeeeeeeeee0000000000000000
def roots_195 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_197 : Nat := 0x33000000000000003300000000000000330000000000000033
def goal_197 : Nat := 0xfffffffffffffffffafafafafafafafaaaaaaaaaaaaaaaaa0000000000000000
def roots_197 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_198 : Nat := 0x55000000000000005500000000000000550000000000000055
def goal_198 : Nat := 0xfffffffffffffffff0f0f0f0f0f0f0f0cccccccccccccccc0000000000000000
def roots_198 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_199 : Nat := 0xff00000000000000ff00000000000000ff00000000000000ff
def goal_199 : Nat := 0xfffffffffffffffffafafafafafafafaeeeeeeeeeeeeeeee0000000000000000
def roots_199 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_200 : Nat := 0x101000000000000010100000000000001010000000000000101
def goal_200 : Nat := 0xffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff000000000000000000
def roots_200 : List Nat := [xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303
def goal_201 : Nat := 0xffffffffffffffffffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00aa00aa00
def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffffffffffffffffffaaffaaffaaffaaffeeffeeffeeffeeaa00aa00aa00aa00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := 0x3333000000000000333300000000000033330000000000003333
def goal_205 : Nat := 0xfffffffffffffffffffafffafffafffaffaaffaaffaaffaaaa00aa00aa00aa00
def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xfffffffffffffffffffafffafffafffaffeeffeeffeeffeeaa00aa00aa00aa00
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_209 : Nat := 0x30003000000000003000300000000000300030000000000030003
def goal_209 : Nat := 0xffffffffffffffffffffaaaaffffaaaaaaaaaaaaaaaaaaaa0000000000000000
def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffffffffffffffffffaaaaffffaaaaeeeeeeeeeeeeeeeecccc0000cccc0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := 0x330033000000000033003300000000003300330000000000330033
def goal_213 : Nat := 0xfffffffffffffffffffffafafffffafaaaaaaaaaaaaaaaaa0000000000000000
def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffffffffffffffffff0f0fffff0f0cccccccccccccccccccc0000cccc0000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffffffffffffffffffafafffffafaeeeeeeeeeeeeeeeecccc0000cccc0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def goal_217 : Nat := 0xffffffffffffffffffffffaaffffffaaffaaffaaffaaffaaaa00aa00aa00aa00
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffffffffffffffffff00ffffff00ffccffccffccffcccccc0000cccc0000
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffffffffffffffffffaaffffffaaffeeffeeffeeffeeeeccaa00eeccaa00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffffffffffffffffffffffafffffffaffaaffaaffaaffaaaa00aa00aa00aa00
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffffffffffffffffff0fffffff0ffccffccffccffcccccc0000cccc0000
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffffffffffffffffffafffffffaffeeffeeffeeffeeeeccaa00eeccaa00
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffffffffffffffffffaaaaaaaaeeeeeeeeeeeeeeee0000000000000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033
def goal_229 : Nat := 0xfffffffffffffffffffffffffafafafafafafafaaaaaaaaaf0f0f0f000000000
def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffffffffffffffffff0f0f0f0fcfcfcfcccccccccf0f0f0f000000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xfffffffffffffffffffffffffafafafafefefefeeeeeeeeef0f0f0f000000000
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffffffffffffffffffaaffaaffaaffaaffaaffaaaa00aa00aa00aa00
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_236 : Nat := 0x111100001111000011110000111100001111000011110000111100001111
def goal_236 : Nat := 0xfffffffffffffffffffffffffff0fff0fff0fff0ff00ff00f0f0f0f000000000
def roots_236 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffffffffffffffffffafffafffafffaffaaffaafaf0faf0aa00aa00
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffffffffffffffffffafffafffefffeffeeffeefaf0faf0aa00aa00
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffffffffffffffffff0000cccccccccccccccccccc0000cccc0000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffffffffffffffffffaaaaeeeeeeeeeeeeeeeecccc0000cccc0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_244 : Nat := 0x11001100110011001100110011001100110011001100110011001100110011
def goal_244 : Nat := 0xfffffffffffffffffffffffffffff0f0f0f0f0f000000000f0f0f0f000000000
def roots_244 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xfffffffffffffffffffffffffffffafafafafafaaaaaaaaaf0f0f0f000000000
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffffffffffffffffff0f0fcfcfcfcccccccccfcfcf0f0cccc0000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffffffffffffffffffafafefefefeeeeeeeeefcfcf0f0cccc0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffffffffffffffffffaaffeeffeeffeeffeeeeccaa00eeccaa00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffffffffffffffffffafffafffaffaaffaafaf0faf0aa00aa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffffffffffffffffff0fffcfffcffccffccfcfcf0f0cccc0000
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffffffffffffffffffafffefffeffeeffeefefcfaf0eeccaa00
def roots_255 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

namespace S_73
def pairsG : List (Nat × Nat) := [(1,9), (1,65), (8,9), (8,72), (64,65), (64,72)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_73.map (· &&& dom_73)
def goalM : Nat := goal_73 &&& dom_73
def NN : Nat → Nat
|2=>1
|3=>1
|_=>0
def HT : Nat → Nat → Nat
|2,0=>0xbc96e
|3,0=>0xbc96e
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x3000000000000000300808000000000000080b030000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x924
|_=>0
def stOffB : Nat → Nat → Nat
|2,0=>3
|3,0=>0x33
|_,_=>0
def dictMask : Nat := 0x3ffffffffffffffffff
def wireSAt (i : Nat) : Nat := if i < 3 then (dictB (i / 512) (i / 32 % 16) >>> (74 * (i % 32))) &&& dictMask else 0
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
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_73 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_73 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)], [(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)], [(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_73 == dom_73) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_73 goalM v ys) : RunD true dom_73 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_73 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_73 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_73 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_73 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_73 roots_73 goal_73 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_73

theorem lowS_73 : Lower true dom_73 roots_73 goal_73 4 := S_73.noCircuit

def isoMvS_137 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64)]
theorem lowS_137 : Lower true dom_137 roots_137 goal_137 4 :=
  lower_iso isoMvS_137 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_73

def isoMvS_164 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_164 : Lower true dom_164 roots_164 goal_164 4 :=
  lower_iso isoMvS_164 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_73

def isoMvS_193 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff00000000ffffffff00000000, 96), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem lowS_193 : Lower true dom_193 roots_193 goal_193 4 :=
  lower_iso isoMvS_193 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_73

def isoMvS_200 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff00000000ffffffff00000000, 96), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_200 : Lower true dom_200 roots_200 goal_200 4 :=
  lower_iso isoMvS_200 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_73

theorem lowS_75 : Lower true dom_75 roots_75 goal_75 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c0000000000000c0c, 64, 66)] (by decide +kernel) (by decide +kernel) lowS_73

namespace S_83
def pairsG : List (Nat × Nat) := [(1,65), (2,18), (2,66), (3,19), (3,67), (16,18), (17,19), (17,81), (64,65), (64,66), (80,81), (80,82)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_83.map (· &&& dom_83)
def goalM : Nat := goal_83 &&& dom_83
def NN : Nat → Nat
|3=>1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0xbce70
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf000000000000000f0000c000c00000000000c000ca000a00000000000a000af000f0000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0xe4
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>4
|_,_=>0
def dictMask : Nat := 0xfffffffffffffffffffff
def wireSAt (i : Nat) : Nat := if i < 4 then (dictB (i / 512) (i / 32 % 16) >>> (84 * (i % 32))) &&& dictMask else 0
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
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_83 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_83 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0xcccccccccccccccc0000000000000000cccccccccccccccc, 62), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_83 == dom_83) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_83 goalM v ys) : RunD true dom_83 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_83 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_83 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_83 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_83 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_83 roots_83 goal_83 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_83

theorem lowS_83 : Lower true dom_83 roots_83 goal_83 4 := S_83.noCircuit

namespace S_201
def pairsG : List (Nat × Nat) := [(1,9), (1,65), (1,129), (8,9), (8,72), (8,136), (64,65), (64,72), (64,192), (128,129), (128,136), (128,192)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_201.map (· &&& dom_201)
def goalM : Nat := goal_201 &&& dom_201
def NN : Nat → Nat
|3=>3
|4=>6
|5=>3
|6=>1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0x3dc473864600378
|4,0=>0x4a63240e5e374e42b7b90d6e208fb8
|5,0=>0x3a37e346871b461
|6,0=>0x34687
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x303000000000000020200000000000003030000000000000202c0c0000000000000c000000000000000c0c0000000000000c030300000000000003020000000000000303000000000000030240400000000000004040000000000000404000000000000000003000000000000000300000000000000030000000000000000c0c0000000000000c0c0000000000000c0c000000000000000302000000000000030200000000000003020000000000000302c0c0000000000000c0c0000000000000c000000000000000c030300000000000003030000000000000202000000000000020200c000000000000000c000000000000000c000000000000000b03000000000000000000000000000003030000000000000000c000000000000000c000000000000000c000000000000000c0202000000000000020200000000000002020000000000000202c0c00000000000000000000000000000c08000000000000000303000000000000030300000000000000000000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x32403e240324032940d72408d240c3240324b0324a073294876425403210
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>0x8411004
|4,0=>0x956056d565454c5
|5,0=>0x335bd2a5
|6,0=>0x384
|_,_=>0
def dictMask : Nat := 0x3ffffffffffffffffffffffffffffffffffffffffffffffffff
def wireSAt (i : Nat) : Nat := if i < 15 then (dictB (i / 512) (i / 32 % 16) >>> (202 * (i % 32))) &&& dictMask else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 4 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 10 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))

def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 4 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
|0=>0x425013050d234d130501204c1
|_=>0
def opOffB : Nat → Nat → Nat
|3,0=>0x20000
|4,0=>0x624200000022
|5,0=>0x910081
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 10 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 15), wireSAt ((code >>> 6) &&& 15)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 8 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmPalB : Nat → Nat
|0=>0xfc76530
|_=>0
def pmB : Nat → Nat → Nat
|3,0=>0x40
|4,0=>0x2a003
|5,0=>0x1a6
|6,0=>6
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 3 (j % 128); fld (pmPalB (k / 32)) 4 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_200,4,runOps true dom_200 (0,roots_200) ops)] else [])++(if pm.testBit 1 then [(dom_193,4,runOps true dom_193 (0,roots_193) ops)] else [])++(if pm.testBit 2 then [(dom_137,4,runOps true dom_137 (0,roots_137) ops)] else [])++(if pm.testBit 3 then [(dom_73,4,runOps true dom_73 (0,roots_73) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_201 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_200 _ g hchk
    · exact cpcs (by decide +kernel) lowS_193 _ g hchk
    · exact cpcs (by decide +kernel) lowS_137 _ g hchk
    · exact cpcs (by decide +kernel) lowS_73 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_200 4 s (0, roots_200) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_201 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_200 h

def symsG : List (List (Nat × Nat)) := [[(0xffffffffffffffff0000000000000000, 64)], [(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56)], [(0xff00ff00ff00ff00ff00ff00ff00ff00, 120)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xffffffffffffffff0000000000000000, 64), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_201 == dom_201) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_201 goalM v ys) : RunD true dom_201 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_201 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 3 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 6 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 6 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, bar true dom_201 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_201 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 3 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_201 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_201 roots_201 goal_201 7 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_201

theorem lowS_201 : Lower true dom_201 roots_201 goal_201 7 := S_201.noCircuit

def isoMvS_90 : List (Nat × Nat) := [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_90 : Lower true dom_90 roots_90 goal_90 4 :=
  lower_iso isoMvS_90 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_141 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_141 : Lower true dom_141 roots_141 goal_141 5 :=
  lower_iso isoMvS_141 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_75

def isoMvS_147 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)]
theorem lowS_147 : Lower true dom_147 roots_147 goal_147 4 :=
  lower_iso isoMvS_147 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_150 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_150 : Lower true dom_150 roots_150 goal_150 4 :=
  lower_iso isoMvS_150 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_153 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_153 : Lower true dom_153 roots_153 goal_153 5 :=
  lower_iso isoMvS_153 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_75

def isoMvS_154 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_154 : Lower true dom_154 roots_154 goal_154 4 :=
  lower_iso isoMvS_154 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_165 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_165 : Lower true dom_165 roots_165 goal_165 5 :=
  lower_iso isoMvS_165 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_75

def isoMvS_169 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_169 : Lower true dom_169 roots_169 goal_169 5 :=
  lower_iso isoMvS_169 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_75

def isoMvS_172 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_172 : Lower true dom_172 roots_172 goal_172 5 :=
  lower_iso isoMvS_172 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_75

def isoMvS_178 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_178 : Lower true dom_178 roots_178 goal_178 4 :=
  lower_iso isoMvS_178 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_180 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_180 : Lower true dom_180 roots_180 goal_180 5 :=
  lower_iso isoMvS_180 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_75

def isoMvS_195 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem lowS_195 : Lower true dom_195 roots_195 goal_195 5 :=
  lower_iso isoMvS_195 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_75

def isoMvS_197 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff00000000ffffffff00000000, 96), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_197 : Lower true dom_197 roots_197 goal_197 5 :=
  lower_iso isoMvS_197 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_75

def isoMvS_198 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_198 : Lower true dom_198 roots_198 goal_198 4 :=
  lower_iso isoMvS_198 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_209 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff00000000ffffffff00000000, 96), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_209 : Lower true dom_209 roots_209 goal_209 5 :=
  lower_iso isoMvS_209 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_75

def dzo_75_16:=0xf0f0000000000000f0f0000
def gzo_75_16:=0xf0e0000000000000e0c0000
def gsh_75_16:=0xf0e0000000000000e0c
theorem lowS_zo_75_16_73:Lower true dzo_75_16 roots_75 gzo_75_16 5:=lower_iso (d1:=dom_75) (roots1:=roots_75) (T1:=gsh_75_16) [(dom_75,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_75_16) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xc0c0000000000000c0c,0,2)] (by decide +kernel) (by decide +kernel) lowS_73)
namespace S_91
def pairsG : List (Nat × Nat) := [(1,9), (1,65), (2,18), (2,66), (3,11), (3,19), (3,67), (8,9), (8,72), (10,11), (10,26), (10,74), (16,18), (17,19), (17,25), (17,81), (24,25), (24,26), (24,88), (64,65), (64,66), (64,72), (80,81), (80,82), (80,88)]
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
|4,0=>0x462f83dd0c
|5,0=>0xad6c826e500ef3f
|6,0=>0x3f37a
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf0a0f0a000000000f0a0f0af0f0f0f000000000f000f0050505050000000000000000a0a0a0a000000000a0a0a0a00f000f00000000000a000af0f0000000000000f0f0000f000f00000000000f000f00c0c0c0c000000000c0c0c0ca0a0a0a000000000a000a00f0f0f0f0000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x432604932604832604326074265043210
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
|0=>0x182
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
|0=>0x1f41c80
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
    (if pm.testBit 0 then [(dom_75,5,runOps true dom_75 (0,roots_75) ops)] else [])++(if pm.testBit 1 then [(dzo_75_16,5,runOps true dzo_75_16 (0,roots_75) ops)] else [])++(if pm.testBit 2 then [(dom_90,4,runOps true dom_90 (0,roots_90) ops)] else [])++(if pm.testBit 3 then [(dom_83,4,runOps true dom_83 (0,roots_83) ops)] else [])++(if pm.testBit 4 then [(dom_73,4,runOps true dom_73 (0,roots_73) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_91 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_75_16_73 _ g hchk
    · exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · exact cpcs (by decide +kernel) lowS_73 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_75 5 s (0, roots_75) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_91 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_75 h

def symsG : List (List (Nat × Nat)) := [[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]]
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

theorem lowS_151 : Lower true dom_151 roots_151 goal_151 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaa00aa00000000000000000000000000aa00aa, 128, 129)] (by decide +kernel) (by decide +kernel) lowS_150

theorem lowS_157 : Lower true dom_157 roots_157 goal_157 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x3030303000000000000000000000000030303030, 128, 132)] (by decide +kernel) (by decide +kernel) lowS_153

namespace S_173
def pairsG : List (Nat × Nat) := [(1,9), (1,129), (4,36), (4,132), (5,13), (5,37), (5,133), (8,9), (8,136), (12,13), (12,44), (12,140), (32,36), (32,160), (33,37), (33,41), (33,161), (40,41), (40,44), (40,168), (128,129), (128,132), (128,136), (128,160)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_173.map (· &&& dom_173)
def goalM : Nat := goal_173 &&& dom_173
def NN : Nat → Nat
|3=>1
|4=>4
|5=>10
|6=>4
|7=>1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0x348e
|4,0=>0x49cc3159a8128240d79e
|5,0=>0x64403371912ebb41e6af1d5d0142771055702c1101e9200159
|6,0=>0x346f630d2f2127b10f60
|7,0=>0x30d2f
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x3232000032320000000000000000000032320000323200000000cccc00000000000000000000000000000003333000033330000000000000000000033000000330000cc000000cc0000000000000000000000000000000333300003333000000000000000000003232000032320000000000cc000000000000000000000000000000033300000333000000000000000000000333000003330cccc0000cccc00000000000000000000c0c00000c0c0303000003030000000000000000000003030000000000000000000000000000000000000000c8c80000c8cb3330000330000000000000000000000333300003300cccc000000cc00000000000000000000cccc000000000000000333300000000000000000000000000002222cccc0000c8c800000000000000000000cccc000000000220000003300000000000000000000002200000022cccc0000cccc00000000000000000000cccc000000033000000330000000000000000000000330000003300cccc0000cc0000000000000000000000000000000002222000022220000000000000000000022220000222200cc000000cc0000000000000000000000cc0000008b3330000333300000000000000000000000000000000cccc0000000000000000000000000000cccc000000033320000333200000000000000000000330000003300c0c00000c0c000000000000000000000c0c00000c0c33330000333300000000000000000000222200002222
|_,_=>0
def stPool : Nat → Nat
|0=>0xd0131068c04c41a02620ec809883404c4b8ec1312a34502620d01312639222620d068112341a041a1e1310680988768d0131068099845a02620c2651128098e3098a418820
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>4
|4,0=>0x26a3944a845
|5,0=>0x26b47682ced9b2b0654c918f3186
|6,0=>0xc8d7d6cb536
|7,0=>0x6a5
|_,_=>0
def dictMask : Nat := 0x3fffffffffffffffffffffffffffffffffffffffffff
def wireSAt (i : Nat) : Nat := if i < 25 then (dictB (i / 512) (i / 32 % 16) >>> (174 * (i % 32))) &&& dictMask else 0
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
|0=>0x99411192005311091487191710412
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0x520041002200110100
|6,0=>0x91008171
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
|0=>0x3feb7c287d85c8180
|_=>0
def pmB : Nat → Nat → Nat
|5,0=>0x7604010920
|6,0=>0xa385
|7,0=>0xa
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 4 (j % 128); fld (pmPalB (k / 32)) 6 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_172,5,runOps true dom_172 (0,roots_172) ops)] else [])++(if pm.testBit 1 then [(dom_141,5,runOps true dom_141 (0,roots_141) ops)] else [])++(if pm.testBit 2 then [(dom_169,5,runOps true dom_169 (0,roots_169) ops)] else [])++(if pm.testBit 3 then [(dom_137,4,runOps true dom_137 (0,roots_137) ops)] else [])++(if pm.testBit 4 then [(dom_165,5,runOps true dom_165 (0,roots_165) ops)] else [])++(if pm.testBit 5 then [(dom_164,4,runOps true dom_164 (0,roots_164) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_173 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_172 _ g hchk
    · exact cpcs (by decide +kernel) lowS_141 _ g hchk
    · exact cpcs (by decide +kernel) lowS_169 _ g hchk
    · exact cpcs (by decide +kernel) lowS_137 _ g hchk
    · exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · exact cpcs (by decide +kernel) lowS_164 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_172 5 s (0, roots_172) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_173 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_172 h

def symsG : List (List (Nat × Nat)) := [[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_173 == dom_173) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_173 goalM v ys) : RunD true dom_173 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_173 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 7) : ∀ i < NN s, bar true dom_173 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
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
  scr true dom_173 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD true dom_173 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_173 roots_173 goal_173 8 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_173

theorem lowS_173 : Lower true dom_173 roots_173 goal_173 8 := S_173.noCircuit

theorem lowS_199 : Lower true dom_199 roots_199 goal_199 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc00000000000000cc00000000000000cc00000000000000cc, 64, 66)] (by decide +kernel) (by decide +kernel) lowS_197

theorem lowS_203 : Lower true dom_203 roots_203 goal_203 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c0000000000000c0c0000000000000c0c0000000000000c0c, 64, 66)] (by decide +kernel) (by decide +kernel) lowS_201

theorem lowS_211 : Lower true dom_211 roots_211 goal_211 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc000c00000000000c000c00000000000c000c00000000000c000c, 16, 18)] (by decide +kernel) (by decide +kernel) lowS_209

theorem lowS_214 : Lower true dom_214 roots_214 goal_214 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x550000000000000055000000000000005500000000000000550000, 2, 18)] (by decide +kernel) (by decide +kernel) lowS_198

def isoMvS_155 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)]
theorem lowS_155 : Lower true dom_155 roots_155 goal_155 7 :=
  lower_iso isoMvS_155 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_91

def isoMvS_158 : List (Nat × Nat) := [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]
theorem lowS_158 : Lower true dom_158 roots_158 goal_158 5 :=
  lower_iso isoMvS_158 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_151

def isoMvS_179 : List (Nat × Nat) := [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem lowS_179 : Lower true dom_179 roots_179 goal_179 5 :=
  lower_iso isoMvS_179 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_151

def isoMvS_181 : List (Nat × Nat) := [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_181 : Lower true dom_181 roots_181 goal_181 6 :=
  lower_iso isoMvS_181 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_157

def isoMvS_182 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_182 : Lower true dom_182 roots_182 goal_182 7 :=
  lower_iso isoMvS_182 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_91

def isoMvS_186 : List (Nat × Nat) := [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]
theorem lowS_186 : Lower true dom_186 roots_186 goal_186 5 :=
  lower_iso isoMvS_186 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_151

def isoMvS_205 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_205 : Lower true dom_205 roots_205 goal_205 8 :=
  lower_iso isoMvS_205 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_203

def isoMvS_213 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]
theorem lowS_213 : Lower true dom_213 roots_213 goal_213 6 :=
  lower_iso isoMvS_213 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_157

def isoMvS_217 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_217 : Lower true dom_217 roots_217 goal_217 8 :=
  lower_iso isoMvS_217 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_203

def isoMvS_218 : List (Nat × Nat) := [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_218 : Lower true dom_218 roots_218 goal_218 6 :=
  lower_iso isoMvS_218 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_211

def isoMvS_227 : List (Nat × Nat) := [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem lowS_227 : Lower true dom_227 roots_227 goal_227 6 :=
  lower_iso isoMvS_227 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_199

def isoMvS_229 : List (Nat × Nat) := [(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem lowS_229 : Lower true dom_229 roots_229 goal_229 8 :=
  lower_iso isoMvS_229 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_173

def isoMvS_230 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff0000ffff0000ffff0000ffff0000, 112), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_230 : Lower true dom_230 roots_230 goal_230 7 :=
  lower_iso isoMvS_230 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_91

def isoMvS_233 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_233 : Lower true dom_233 roots_233 goal_233 8 :=
  lower_iso isoMvS_233 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_203

def isoMvS_236 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_236 : Lower true dom_236 roots_236 goal_236 8 :=
  lower_iso isoMvS_236 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_173

def isoMvS_242 : List (Nat × Nat) := [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem lowS_242 : Lower true dom_242 roots_242 goal_242 5 :=
  lower_iso isoMvS_242 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_214

def isoMvS_244 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_244 : Lower true dom_244 roots_244 goal_244 6 :=
  lower_iso isoMvS_244 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_157

theorem lowS_119 : Lower true dom_119 roots_119 goal_119 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf000f000f000f000f000f000f000f0, 32, 36), (0xff00ff0000000000ff00ff00000000, 4, 36)] (by decide +kernel) (by decide +kernel) lowS_83

theorem lowS_159 : Lower true dom_159 roots_159 goal_159 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f0f0f0000000000000000000000000f0f0f0f0, 128, 132)] (by decide +kernel) (by decide +kernel) lowS_155

theorem lowS_189 : Lower true dom_189 roots_189 goal_189 9 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x333300003333000000000000000000003333000033330000, 128, 144)] (by decide +kernel) (by decide +kernel) lowS_173

theorem lowS_207 : Lower true dom_207 roots_207 goal_207 9 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcccc000000000000cccc000000000000cccc000000000000cccc, 64, 66)] (by decide +kernel) (by decide +kernel) lowS_205

def dzo_83_4:=0xf000f00000000000f000f0
def gzo_83_4:=0xe000e00000000000c00000
def gsh_83_4:=0xe000e00000000000c0000
theorem lowS_zo_83_4_83:Lower true dzo_83_4 roots_83 gzo_83_4 4:=lower_iso (d1:=dom_83) (roots1:=roots_83) (T1:=gsh_83_4) [(dom_83,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_83_4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [] (by decide +kernel) (by decide +kernel) lowS_83)
def dzo_211_4:=0xf000f00000000000f000f00000000000f000f00000000000f000f0
def gzo_211_4:=0xf000f00000000000f000f00000000000e000e00000000000c00000
def gsh_211_4:=0xf000f00000000000f000f00000000000e000e00000000000c0000
theorem lowS_zo_211_4_83:Lower true dzo_211_4 roots_211 gzo_211_4 5:=lower_iso (d1:=dom_211) (roots1:=roots_211) (T1:=gsh_211_4) [(dom_211,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_211_4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xf000f00000000000f000f00000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_83)
namespace S_215
def pairsG : List (Nat × Nat) := [(1,65), (1,129), (2,18), (2,66), (3,19), (3,67), (3,131), (4,132), (5,69), (5,133), (6,22), (6,70), (6,134), (7,23), (7,71), (7,135), (16,18), (16,144), (17,19), (17,81), (17,145), (20,22), (20,148), (21,23), (21,85), (21,149), (64,65), (64,66), (64,192), (68,69), (68,70), (68,196), (80,81), (80,82), (80,208), (84,85), (84,86), (84,212), (128,129), (128,132), (128,144), (128,192), (130,131), (130,134), (130,146), (130,194)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3fffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_215.map (· &&& dom_215)
def goalM : Nat := goal_215 &&& dom_215
def NN : Nat → Nat
|3=>1
|4=>4
|5=>10
|6=>7
|7=>1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0x18040
|4,0=>0xee6dfacc27527ab0977d
|5,0=>0xf43cbe8347d932da85cd832c66aa36617de4040c0601a006f3
|6,0=>0xfe849cc743c8475afbe5a08eb94ea32b05a
|7,0=>0xda052
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xff00ff0000000000f000f00000000000ff00ff0000000000f000f0ff00ff0000000000ff00ff0000000000aa00aa0000000000aa00aafa00fa0000000000fa00fa0000000000fa00fa0000000000fa00faff00ff0000000000ff00f00000000000ff00ff0000000000ff00f03300330000000000330000000000000033003300000000003300000f000f00000000000f000f000000000000000000000000000000005500550000000000550055000000000055005500000000000000000000ff00000000000000ff00000000000000cc00000000000000ccaf00af0000000000af00af0000000000aa00aa0000000000aa00aaff00ff0000000000ff00ff0000000000cc00cc0000000000cc00ccff00000000000000ff00000000000000ff00000000000000ff0000ff00ff00000000000000000000000000ff00ff0000000000000000550055000000000005000500000000005500550000000000000000ff00ff0000000000ff00000000000000ff00ff0000000000ff0000cc00cc0000000000cc00cc0000000000cc00cc0000000000cc00ccff00ff00000000000f000f0000000000ff00ff0000000000000000ff00ff0000000000ff00ff00000000000000000000000000000000f000f00000000000f000f00000000000f000f00000000000f000f0ff00ff0000000000ff00000000000000cc00cc0000000000cc0000aa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aaff00ff0000000000ff00ff0000000000ff00ff0000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x550c14914334c292286b0a48a305247aa460a48719829228660812451825492273052450d61024e30c12438d61490e60a48f50cc9710e3304041ac2d491466052438d6100c41491464a087304a418820
|1=>0x14330524
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>4
|4,0=>0x1350e5095045
|5,0=>0x4e64864263c63663062a62461e6186
|6,0=>0x7a67376d66766165b6547
|7,0=>0x806
|_,_=>0
def dictMask : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffff
def wireSAt (i : Nat) : Nat := if i < 21 then (dictB (i / 512) (i / 32 % 16) >>> (216 * (i % 32))) &&& dictMask else 0
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
|0=>0x1a509131119218552549138d525
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0x20000000000000000
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
|0=>0xf56fedbcb395c298c9503201001401000
|_=>0
def pmB : Nat → Nat → Nat
|5,0=>0x210000300
|6,0=>0xb467a85
|7,0=>9
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 4 (j % 128); fld (pmPalB (k / 32)) 11 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_213,6,runOps true dom_213 (0,roots_213) ops)] else [])++(if pm.testBit 1 then [(dzo_83_4,4,runOps true dzo_83_4 (0,roots_83) ops)] else [])++(if pm.testBit 2 then [(dom_195,5,runOps true dom_195 (0,roots_195) ops)] else [])++(if pm.testBit 3 then [(dom_150,4,runOps true dom_150 (0,roots_150) ops)] else [])++(if pm.testBit 4 then [(dom_214,5,runOps true dom_214 (0,roots_214) ops)] else [])++(if pm.testBit 5 then [(dom_211,6,runOps true dom_211 (0,roots_211) ops)] else [])++(if pm.testBit 6 then [(dom_83,4,runOps true dom_83 (0,roots_83) ops)] else [])++(if pm.testBit 7 then [(dzo_211_4,5,runOps true dzo_211_4 (0,roots_211) ops)] else [])++(if pm.testBit 8 then [(dom_151,5,runOps true dom_151 (0,roots_151) ops)] else [])++(if pm.testBit 9 then [(dom_199,6,runOps true dom_199 (0,roots_199) ops)] else [])++(if pm.testBit 10 then [(dom_147,4,runOps true dom_147 (0,roots_147) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_215 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_83_4_83 _ g hchk
    · exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_211_4_83 _ g hchk
    · exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · exact cpcs (by decide +kernel) lowS_147 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_213 6 s (0, roots_213) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_215 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_213 h

def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {v ys} (h : RunD true dom_215 goalM v ys) : RunD true dom_215 goalM v (ori ys) := h
def Z (s : Nat) := barP true dom_215 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 7 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 7) : ∀ i < NN s, bar true dom_215 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
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
  scr true dom_215 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD true dom_215 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_215 roots_215 goal_215 8 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_215

theorem lowS_215 : Lower true dom_215 roots_215 goal_215 8 := S_215.noCircuit

theorem lowS_219 : Lower true dom_219 roots_219 goal_219 9 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c, 16, 18)] (by decide +kernel) (by decide +kernel) lowS_217

theorem lowS_221 : Lower true dom_221 roots_221 goal_221 9 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x30303030000000003030303000000000303030300000000030303030, 128, 132)] (by decide +kernel) (by decide +kernel) lowS_217

theorem lowS_231 : Lower true dom_231 roots_231 goal_231 9 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc000000cc000000cc000000cc000000cc000000cc000000cc000000cc, 64, 66)] (by decide +kernel) (by decide +kernel) lowS_229

namespace S_237
def pairsG : List (Nat × Nat) := [(1,9), (1,65), (1,129), (4,36), (4,132), (5,13), (5,37), (5,69), (5,133), (8,9), (8,72), (8,136), (12,13), (12,44), (12,76), (12,140), (32,36), (32,160), (33,37), (33,41), (33,97), (33,161), (40,41), (40,44), (40,104), (40,168), (64,65), (64,72), (64,192), (68,69), (68,76), (68,100), (68,196), (96,97), (96,100), (96,104), (96,224), (128,129), (128,132), (128,136), (128,160), (128,192)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3ffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_237.map (· &&& dom_237)
def goalM : Nat := goal_237 &&& dom_237
def NN : Nat → Nat
|9=>1
|_=>0
def HT : Nat → Nat → Nat
|9,0=>0x18b09
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xcccc000000000000cccc000000000000cccc000000000000cccc0000000330000003300000033000000330000003300000033000000330000003300c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c222200002222000022220000222200002222000022220000222200002222cccc0000cccc00000000000000000000cccc0000cccc000000000000000333300003333000033330000333300000000000000000000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x2c688
|_=>0
def stOffB : Nat → Nat → Nat
|9,0=>6
|_,_=>0
def dictMask : Nat := 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def wireSAt (i : Nat) : Nat := if i < 6 then (dictB (i / 512) (i / 32 % 16) >>> (238 * (i % 32))) &&& dictMask else 0
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
|0=>0x3e0
|_=>0
def pmB : Nat → Nat → Nat
|9,0=>1
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 1 (j % 128); fld (pmPalB (k / 32)) 5 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_236,8,runOps true dom_236 (0,roots_236) ops)] else [])++(if pm.testBit 1 then [(dom_173,8,runOps true dom_173 (0,roots_173) ops)] else [])++(if pm.testBit 2 then [(dom_233,8,runOps true dom_233 (0,roots_233) ops)] else [])++(if pm.testBit 3 then [(dom_229,8,runOps true dom_229 (0,roots_229) ops)] else [])++(if pm.testBit 4 then [(dom_205,8,runOps true dom_205 (0,roots_205) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_237 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_236 _ g hchk
    · exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · exact cpcs (by decide +kernel) lowS_233 _ g hchk
    · exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · exact cpcs (by decide +kernel) lowS_205 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_236 8 s (0, roots_236) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_237 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_236 h

def symsG : List (List (Nat × Nat)) := [[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)], [(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_237 == dom_237) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_237 goalM v ys) : RunD true dom_237 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_237 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
private theorem z6 : ∀ i, 0 ≤ i → i < 0 → Z 6 i = true := by omega
private theorem z7 : ∀ i, 0 ≤ i → i < 0 → Z 7 i = true := by omega
private theorem z8 : ∀ i, 0 ≤ i → i < 0 → Z 8 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 9) : ∀ i < NN s, bar true dom_237 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
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
  scr true dom_237 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD true dom_237 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_237 roots_237 goal_237 10 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_237

theorem lowS_237 : Lower true dom_237 roots_237 goal_237 10 := S_237.noCircuit

theorem lowS_246 : Lower true dom_246 roots_246 goal_246 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x55000000550000005500000055000000550000005500000055000000550000, 2, 18)] (by decide +kernel) (by decide +kernel) lowS_230

def isoMvS_183 : List (Nat × Nat) := [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_183 : Lower true dom_183 roots_183 goal_183 8 :=
  lower_iso isoMvS_183 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_159

def isoMvS_187 : List (Nat × Nat) := [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)]
theorem lowS_187 : Lower true dom_187 roots_187 goal_187 8 :=
  lower_iso isoMvS_187 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_159

def isoMvS_190 : List (Nat × Nat) := [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]
theorem lowS_190 : Lower true dom_190 roots_190 goal_190 8 :=
  lower_iso isoMvS_190 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_159

def isoMvS_222 : List (Nat × Nat) := [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]
theorem lowS_222 : Lower true dom_222 roots_222 goal_222 8 :=
  lower_iso isoMvS_222 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_215

def isoMvS_243 : List (Nat × Nat) := [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem lowS_243 : Lower true dom_243 roots_243 goal_243 8 :=
  lower_iso isoMvS_243 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_215

def isoMvS_245 : List (Nat × Nat) := [(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56)]
theorem lowS_245 : Lower true dom_245 roots_245 goal_245 9 :=
  lower_iso isoMvS_245 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_189

def dzo_189_2:=0xcccccccccccccccc0000000000000000cccccccccccccccc
def gzo_189_2:=0xccccccccccccccc80000000000000000ccccc8c0cccc8800
def gsh_189_2:=0x333333333333333200000000000000003333323033332200
theorem lowS_zo_189_2_173:Lower true dzo_189_2 roots_189 gzo_189_2 9:=lower_iso (d1:=dom_189) (roots1:=roots_189) (T1:=gsh_189_2) [(dom_189,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_189_2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x333300003333000000000000000000003333000033330000,0,16)] (by decide +kernel) (by decide +kernel) lowS_173)
namespace S_191
def pairsG : List (Nat × Nat) := [(1,9), (1,129), (2,18), (3,11), (3,19), (3,131), (4,36), (4,132), (5,13), (5,37), (5,133), (6,22), (6,38), (6,134), (7,15), (7,23), (7,39), (7,135), (8,9), (8,136), (10,11), (10,26), (10,138), (12,13), (12,44), (12,140), (14,15), (14,30), (14,46), (14,142), (16,18), (16,144), (17,19), (17,25), (17,145), (20,22), (20,52), (20,148), (21,23), (21,29), (21,53), (21,149), (24,25), (24,26), (24,152), (28,29), (28,30), (28,60), (28,156), (32,36), (32,160), (33,37), (33,41), (33,161), (34,38), (34,50), (34,162), (35,39), (35,43), (35,51), (35,163), (40,41), (40,44), (40,168), (42,43), (42,46), (42,58), (42,170), (48,50), (48,52), (48,176), (49,51), (49,53), (49,57), (49,177), (56,57), (56,58), (56,60), (56,184), (128,129), (128,132), (128,136), (128,144), (128,160), (130,131), (130,134), (130,138), (130,146), (130,162)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x1ffffffffffffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_191.map (· &&& dom_191)
def goalM : Nat := goal_191 &&& dom_191
def NN : Nat → Nat
|5=>2
|6=>16
|7=>33
|8=>19
|9=>3
|10=>1
|_=>0
def HT : Nat → Nat → Nat
|5,0=>0x364050c313
|6,0=>0x55d46456534201537fa4309a02001f1516213db0103fe0e5510cd9a0934e071d9066f60477203cdb
|7,0=>0x7c6045f2fa5128e40ad13f4a6391542fd802f1da2d4422c6a529d6027bba23fc5221da1c564184c715cfd1516214d14140be12fa812c220e4080dd880bedf0afe909c5207573073050488a02dc3027bc0005c
|8,0=>0x7e28a7c60455ebc520f75048f390b62e5932df972a6f21ec0a1dee319afa197221691b15270109e40ff0d0fcba02dc3
|9,0=>0x2038317e330180e
|10,0=>0xe26d2
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xfffffffffafafafa0000000000000000f0f0f0f0f0f0f0f05555555555555555000000000000000055555555550055005555555555555555000000000000000050505050505050500f0f0f0f0f0f0f0f00000000000000000a0a0a0a0a0a0a0a00000000ffffffff000000000000000000000000fff0fff055555555555555550000000000000000550055005500550000000000ffffffff000000000000000000000000f0f0f0f00000000000ff00ff0000000000000000ffffffff0000000000ff00ff00ff00ff000000000000000000aa00aa00aa00aa00000000f0fff0ff000000000000000000000000f0faf0fafffffff0fffffff00000000000000000ffff0000ffff0000ffffffffffffffff0000000000000000ffffffff00000000ffffffffff00ff0000000000000000000000000000000000ffffffffff00ff000000000000000000ffffffffff00ff00ffffffffffaaffaa0000000000000000aaaaaaaaaaaaaaaafafafafafafafafa00000000000000000000000000000000fafafafafafafafa0000000000000000fafafafafafafafafffafffafffafffa0000000000000000ff00ff00ff00ff00ffffffffffffffff0000000000000000aaaaaaaaaaaaaaaafff0fff0fff0fff000000000000000000000000000000000fff0fff0fff0fff00000000000000000fff0fff0fff0fff0ff00ff00ff00ff000000000000000000ff00ff00ff00ff00ffffffffffffffff00000000000000000000000000000000fffffffffff0fff00000000000000000ffffffff00000000ffffffffffffffff0000000000000000f0f0f0f0f0f0f0f0aaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaaffffffff000000000000000000000000ffffffff00000000ffff0000ffff00000000000000000000ffff0000ffff0000ffffffffffffffff0000000000000000ff00ff00ff00ff00f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0cccccccccccccccc0000000000000000cccccccccccccccc000500050005000500000000000000005500550055005500
|0,1=>0xff00ff00ff00ff000000000000000000ff00ff00aa00aa5555555555555555000000000000000000000000000000000000000000ff00ff00000000000000000000000000000000ff00ff00ffffffff0000000000000000ff00ff00ff00ff0000ff00ff00ff00ff000000000000000000ff00ff00000000ffffffffffffffff0000000000000000ffffffffff00ff00005500550055005500000000000000000000000000000000fffafffafffafffa0000000000000000aaaaaaaaaaaaaaaa050505050505050500000000000000000000000000000000f5f5f5f5f5f5f5f50000000000000000f0f0f0f0f0f0f0f000000000ffffffff000000000000000000000000aaaaaaaaffffffffffffffff0000000000000000fafafafafafafafa00000000ffffffff0000000000000000000000000000000000aa00aa00ff00ff000000000000000000aa00aa00aa00aaf0fff0fff0fff0ff0000000000000000f0faf0faf0faf0faffffffffffffaaaa0000000000000000ffff0000ffff000000ff00ff00ff00ff000000000000000000f000f000f000f0000000005555555500000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffaaaaaaaaff0fff0fff0fff0f0000000000000000ff00ff00ff00ff005505550555055505000000000000000055005500550055000f0f0f0f0f0f0f0f0000000000000000000000000000000000ff00ff00ff00ff000000000000000000fa00fa00fa00fa00000000ffffffff000000000000000000000000fafafafaffffffff555555550000000000000000ffffffff00000000aaaaaaaaffffffff0000000000000000aaaaaaaaaaaaaaaaffffffff00ff00ff0000000000000000ffffffff0000000000ff00ff00ff00ff000000000000000000000000000000000f0f0f0f000f000f00000000000000000f0f0f0f0000000000000000555555550000000000000000ffffffff00000000ffffffffaaaaaaaa00000000000000000000000000000000ffffffffaaaaaaaa0000000000000000ffffffffaaaaaaaa
|0,2=>0xffffffffff00ff00ffffffffffffffff0000000000000000fff0fff0fff0fff00f0f0f0f0f0f0f0f00000000000000000f000f000f000f000f0f0f0f0f0f0f0f00000000000000000f0f0f0f00000000050505050505050500000000000000000505050500000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x140432312101010ca54094e105020298485080c08646242840404697425110414080860a1051f023448508281013c242841404e9c12105020268d890828101346449808281010c242020218b961214a83040430928101820218985080c10122242841c0808d101018702182840608080
|1=>0x121420a04046895c1420a0404f090a1050202344a10a101011a5c4b90a1050202e048508287b602184ad08281010cd4485080808d0ca448508080866425285080c1010c2420a040431d322428462080862e242b014080861214203040432f12b42841408086121420a04055895494284
|2=>0xc24284140808612b820314080863224a04140808626105340404328121420a021a0c01280a04140808d1280284040433f1250284040433f129420a04043097a1053404043191280284040469712142020234b897c1420a0404d09661423c04043094848a04040433b121420a1e0431c
|3=>0x21848508281010c25524241420a04043097a142020218b894e1420a04043090a1018a0404309541420a0404309261422c140808612a8284860c5020218485080c50704043090a10502021a1090a1050702184aa241420304043090a1050202184aa6e14203140808684256850828101
|4=>0x508281010c24284141c1010c2428416281010c242841408086129028404046862e24284140808612b8284862c50202184c40a10502
|_=>0
def stOffB : Nat → Nat → Nat
|5,0=>0x198006
|6,0=>0x1d1c6d7199c5f7161c517129c4370f1c3570b9c277081c197049c0c6
|7,0=>0x17685ba167757e157853e14784fe13784be127847e117843e10783fe0f783c1ce883820d973460c983060ba72ca0aa828a09b724e08b820e07b8
|8,0=>0x216883a20597f61f497ae5e477721d3972e1c296e65b096a21a0866218f961a57e8
|9,0=>0x22e889a21e8
|10,0=>0x2367
|_,_=>0
def dictMask : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffff
def wireSAt (i : Nat) : Nat := if i < 69 then (dictB (i / 512) (i / 32 % 16) >>> (192 * (i % 32))) &&& dictMask else 0
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
|0=>0x14250c2540240a190c5e14360c250c311624042904dd1e260c090ad51a170c25682b1a090c254c2b0ccd0a260a9114360c25088540240a190e2b0425142540b94026581b14a904260a9114264a0b0a9104854024284f0a252424142508311624042924240a25142514250c4d24240a290c2514411e2404190a31162414250425
|1=>0x14a904260609142514250425060b142504a90426141514250caa0426060b142528190a255a8340250c150a1e04250a252424141568170e19042504520a250a250c255a2b402514b628190a910a9214260e1704251a2b0c150c2514360cf90c260a260c0e142514f50a92142614520a25680b1e2504190cce0c250a26741b0615
|2=>0x4250429142614360c250cce0a26162524270a290426142624260a2914360c250af90c261425042624240a29
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0x4000
|6,0=>0x1820000001620000000000001330000f40c3084044
|7,0=>0x6b36926636336125f25d25b25835625335034d34a34824534233f33c33933633333032d32a32910002722432131f21c31a2
|8,0=>0x9128f28e18c28a28828628428228027e27c27a27827627427227026e2
|9,0=>0x951941931
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
|0=>0x284041407c80d3018c02a00450089010001cc038805300a201200220042007600e4018802e00540090010001200220030005800a001000180010000
|1=>0x287fc03b805d009900118ff31be47fc87f90fd21f241d440c880508f20ac41428281
|_=>0
def pmB : Nat → Nat → Nat
|5,0=>0x80
|6,0=>0x400010000000c0202516
|7,0=>0x712b4176d7464b5261314681f1dc66385e69504029d142349
|8,0=>0x27aaeb0e968a70b0fbcca66b222ea
|9,0=>0x29c69
|10,0=>0x29
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 6 (j % 128); fld (pmPalB (k / 32)) 15 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_189,9,runOps true dom_189 (0,roots_189) ops)] else [])++(if pm.testBit 1 then [(dom_182,7,runOps true dom_182 (0,roots_182) ops)] else [])++(if pm.testBit 2 then [(dom_155,7,runOps true dom_155 (0,roots_155) ops)] else [])++(if pm.testBit 3 then [(dom_183,8,runOps true dom_183 (0,roots_183) ops)] else [])++(if pm.testBit 4 then [(dzo_189_2,9,runOps true dzo_189_2 (0,roots_189) ops)] else [])++(if pm.testBit 5 then [(dom_187,8,runOps true dom_187 (0,roots_187) ops)] else [])++(if pm.testBit 6 then [(dom_159,8,runOps true dom_159 (0,roots_159) ops)] else [])++(if pm.testBit 7 then [(dom_190,8,runOps true dom_190 (0,roots_190) ops)] else [])++(if pm.testBit 8 then [(dom_158,5,runOps true dom_158 (0,roots_158) ops)] else [])++(if pm.testBit 9 then [(dom_186,5,runOps true dom_186 (0,roots_186) ops)] else [])++(if pm.testBit 10 then [(dom_178,4,runOps true dom_178 (0,roots_178) ops)] else [])++(if pm.testBit 11 then [(dom_151,5,runOps true dom_151 (0,roots_151) ops)] else [])++(if pm.testBit 12 then [(dom_173,8,runOps true dom_173 (0,roots_173) ops)] else [])++(if pm.testBit 13 then [(dom_154,4,runOps true dom_154 (0,roots_154) ops)] else [])++(if pm.testBit 14 then [(dom_179,5,runOps true dom_179 (0,roots_179) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_191 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_189 _ g hchk
    · exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_189_2_173 _ g hchk
    · exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · exact cpcs (by decide +kernel) lowS_190 _ g hchk
    · exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · exact cpcs (by decide +kernel) lowS_173 _ g hchk
    · exact cpcs (by decide +kernel) lowS_154 _ g hchk
    · exact cpcs (by decide +kernel) lowS_179 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_189 9 s (0, roots_189) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_191 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_189 h

def symsG : List (List (Nat × Nat)) := [[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_191 == dom_191) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_191 goalM v ys) : RunD true dom_191 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_191 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 2 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 16 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 33 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 33 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 19 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 19 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 3 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 3 0 = true)
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

def dzo_91_4:=0xf0f0f0f000000000f0f0f0f0
def gzo_91_4:=0xf0e0f0e000000000e0c0a000
def gsh_91_4:=0xf0e0f0e000000000e0c0a00
theorem lowS_zo_91_4_91:Lower true dzo_91_4 roots_91 gzo_91_4 7:=lower_iso (d1:=dom_91) (roots1:=roots_91) (T1:=gsh_91_4) [(dom_91,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_91_4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [] (by decide +kernel) (by decide +kernel) lowS_91)
def dzo_218_4:=0x50505050000000005050505000000000505050500000000050505050
def gzo_218_4:=0x50505050000000005050505000000000504050400000000040400000
def gsh_218_4:=0x5050505000000000505050500000000050405040000000004040000
theorem lowS_zo_218_4_90:Lower true dzo_218_4 roots_218 gzo_218_4 5:=lower_iso (d1:=dom_218) (roots1:=roots_218) (T1:=gsh_218_4) [(dom_218,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_218_4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x5050505000000000505050500000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_90)
def dzo_219_4:=0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0
def gzo_219_4:=0xf0f0f0f000000000f0f0f0f000000000f0e0f0e000000000e0c0a000
def gsh_219_4:=0xf0f0f0f000000000f0f0f0f000000000f0e0f0e000000000e0c0a00
theorem lowS_zo_219_4_91:Lower true dzo_219_4 roots_219 gzo_219_4 8:=lower_iso (d1:=dom_219) (roots1:=roots_219) (T1:=gsh_219_4) [(dom_219,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_219_4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xf0f0f0f000000000f0f0f0f00000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_91)
def dzo_203_20:=0xf0f0000000000000f0f0000000000000f0f0000000000000f0f00000
def gzo_203_20:=0xf0f0000000000000f0f0000000000000f0e0000000000000e0c00000
def gsh_203_20:=0xf0f0000000000000f0f0000000000000f0e0000000000000e0c
theorem lowS_zo_203_20_73:Lower true dzo_203_20 roots_203 gzo_203_20 6:=lower_iso (d1:=dom_203) (roots1:=roots_203) (T1:=gsh_203_20) [(dom_203,20)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_203_20) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xc0c0000000000000c0c0000000000000c0c0000000000000c0c,0,2),(0xf0f0000000000000f0f00000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_73)
def dzo_203_16:=0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0000
def gzo_203_16:=0xf0f0000000000000f0f0000000000000f0e0000000000000e0c0000
def gsh_203_16:=0xf0f0000000000000f0f0000000000000f0e0000000000000e0c
theorem lowS_zo_203_16_73:Lower true dzo_203_16 roots_203 gzo_203_16 6:=lower_iso (d1:=dom_203) (roots1:=roots_203) (T1:=gsh_203_16) [(dom_203,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_203_16) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xc0c0000000000000c0c0000000000000c0c0000000000000c0c,0,2),(0xf0f0000000000000f0f00000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_73)
def dzo_221_2:=0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc
def gzo_221_2:=0xcccccccc00000000ccccccc800000000cccccccc00000000cccc8800
def gsh_221_2:=0x33333333000000003333333200000000333333330000000033332200
theorem lowS_zo_221_2_141:Lower true dzo_221_2 roots_221 gzo_221_2 7:=lower_iso (d1:=dom_221) (roots1:=roots_221) (T1:=gsh_221_2) [(dom_221,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_221_2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x33330000000000003333000000000000333300000000000033330000,0,16),(0x33333333000000000000000000000000333333330000000000000000,0,64)] (by decide +kernel) (by decide +kernel) lowS_141)
def dzo_157_2:=0xcccccccc000000000000000000000000cccccccc
def gzo_157_2:=0xccccccc8000000000000000000000000cccc8800
def gsh_157_2:=0x3333333200000000000000000000000033332200
theorem lowS_zo_157_2_141:Lower true dzo_157_2 roots_157 gzo_157_2 6:=lower_iso (d1:=dom_157) (roots1:=roots_157) (T1:=gsh_157_2) [(dom_157,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_157_2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x3333000000000000000000000000000033330000,0,16)] (by decide +kernel) (by decide +kernel) lowS_141)
def dzo_205_2:=0xcccc000000000000cccc000000000000cccc000000000000cccc
def gzo_205_2:=0xcccc000000000000ccc8000000000000cccc0000000000008800
def gsh_205_2:=0x3333000000000000333200000000000033330000000000002200
theorem lowS_zo_205_2_141:Lower true dzo_205_2 roots_205 gzo_205_2 6:=lower_iso (d1:=dom_205) (roots1:=roots_205) (T1:=gsh_205_2) [(dom_205,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_205_2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x3333000000000000000000000000000033330000000000000000,0,64)] (by decide +kernel) (by decide +kernel) lowS_141)
def dzo_201_16:=0x3030000000000000303000000000000030300000000000003030000
def gzo_201_16:=0x3030000000000000303000000000000030200000000000002000000
def gsh_201_16:=0x303000000000000030300000000000003020000000000000200
theorem lowS_zo_201_16_73:Lower true dzo_201_16 roots_201 gzo_201_16 5:=lower_iso (d1:=dom_201) (roots1:=roots_201) (T1:=gsh_201_16) [(dom_201,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_201_16) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x303000000000000030300000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_73)
namespace S_223
def pairsG : List (Nat × Nat) := [(1,9), (1,65), (1,129), (2,18), (2,66), (3,11), (3,19), (3,67), (3,131), (4,132), (5,13), (5,69), (5,133), (6,22), (6,70), (6,134), (7,15), (7,23), (7,71), (7,135), (8,9), (8,72), (8,136), (10,11), (10,26), (10,74), (10,138), (12,13), (12,76), (12,140), (14,15), (14,30), (14,78), (14,142), (16,18), (16,144), (17,19), (17,25), (17,81), (17,145), (20,22), (20,148), (21,23), (21,29), (21,85), (21,149), (24,25), (24,26), (24,88), (24,152), (28,29), (28,30), (28,92), (28,156), (64,65), (64,66), (64,72), (64,192), (68,69), (68,70), (68,76), (68,196), (80,81), (80,82), (80,88), (80,208), (84,85), (84,86), (84,92), (84,212), (128,129), (128,132), (128,136), (128,144), (128,192), (130,131), (130,134), (130,138), (130,146), (130,194)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xffffffffffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_223.map (· &&& dom_223)
def goalM : Nat := goal_223 &&& dom_223
def NN : Nat → Nat
|3=>1
|4=>2
|5=>16
|6=>86
|7=>108
|8=>49
|9=>9
|10=>1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0x2766c
|4,0=>0xc5ac643e62
|5,0=>0xe1c8edb4639bb7b9ac9c93fca8e2ce8957e88ad1631d45817650bb129d432500b13df00c66a04786
|6,0=>0xefee2e8714e791bd1145cf3aec63fbc06ffbed32baf02b9596b945bb9367b801fb377eb0706aee79ac131aa496a64eca55d7a4b1fa3ef2a3c6ba3817972109658d956057e5557b9c777d2a7709472b3e6da886a79f6538363e32634a45fec05c3435c174548cc5310a50bb1501044ce16463404538f42d943ea9b3c9a839ac6383fc37e2b377f736c0a338ad32f3932ee031ca62f2ca2deb829a4e27efe27041269fd24ac1239f121d401da6f1d1bd1cad11c36518474171e70eb150e71f0c9f60beea0a9ee09651094ef0949d086250552b03deb0279e
|7,0=>0xfa4a7f64d4f3830ed613ea548ea450e44f4e35e4dff35dc8c7d609cd5623d318ad1038d0a83c8c47c5da5c3954c1686bdb14b940bb107cad649a95e7a4f6fa2b28958d5957459497e921568e7748e6318c0a6898f7832857bf86759686fd116edd96903b67fb065cde6447f61d975e0325ac175a3c358e2e5852653915538555308b52b275243b4dff94bf9c4af88496184954f48e6d48bfc46a1645d5243e9d42bd640f263c52f3c06f3b02939585388a33706c36fe33621c34bcf345e8342e3308e12eff12e3b22d27029ee6278802647c26104249ce2423522ebf1df701ab5c1aa4119d4c19687187fb1840b134c8124a811fd0113d310c1a0e71f0d6c00d61b09cf307a45049a003eae00ced
|8,0=>0xf8091f0e9eeeac8ed6fbeb83ce0f3fdfa7ac9b81c6d10c0a62bc038b1958ae3b7a7113a18598efb0849d182b6c802ee79c7c7709568da466d055db9654d75547f14d3df48e3244a5242dc13f15c3a894352a234f1a33ef02a54c2a237225af1fa441ce731aad40dc950be8c0b02e096d008dac07a54027ef00ae1
|9,0=>0xe40f2d9544b2a2f88b044b76c2a8e706d92059e002883
|10,0=>0xfc3d7
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xafafafaf00000000afafafaf00000000aaaaaaaa00000000aaaaaaaaffffffff00000000ffffffff00000000ffffffff00000000ff00ff00ff00ff0000000000af00af0000000000ff00ff0000000000aa00aa00555555550000000005050505000000005555555500000000000000000000000000000000ffaaffaa000000000000000000000000ffaaffaaffffffff00000000ffffffff00000000ff00ff0000000000ff00ff00ffffffff00000000ffffffff00000000aaaaaaaa00000000aaaaaaaa0000000000000000ffafffaf000000000000000000000000ffaaffaaffafffaf00000000ffafffaf00000000ffaaffaa00000000ffaaffaaffffffff00000000ff00ff0000000000ffffffff00000000ff00ff00555555550000000055055505000000005555555500000000550055000f0f0f0f00000000ffafffaf000000000000000000000000ffaaffaaffaaffaa00000000ffaaffaa00000000ffaaffaa00000000ffaaffaaffffffff00000000ff0fff0f00000000ffffffff00000000ff00ff00ffffffff00000000aaaaaaaa00000000ffffffff00000000aaaaaaaaaaaaaaaa00000000aa0aaa0a00000000aaaaaaaa00000000aa00aa00ffffffff000000000f0f0f0f00000000ffffffff0000000000000000ffffffff00000000ffff000000000000ffffffff00000000ffff0000ffffffff00000000ffffffff00000000cccccccc00000000cccccccccccccccc00000000cccccccc00000000cccccccc00000000ccccccccffff000000000000ffff000000000000ffff000000000000ffff0000ffffffff000000000000000000000000ffffffff0000000000000000ffffffff00000000ffffffff0000000000000000000000000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0055555555000000005555555500000000555555550000000055005500ffffffff00000000ffff000000000000cccccccc00000000cccc0000ff00ff0000000000ff00ff0000000000ff00ff0000000000aa00aa00f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0ffffffff00000000ffffff0000000000ffccffcc00000000eeccaa00aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaaffffffff00000000ffffffff00000000ffffffff0000000000000000
|0,1=>0xaaffaaff00000000aaffaaff00000000aaffaaff00000000aaaaaaaaffffffff00000000fffff0f000000000ffffffff00000000fffff0f000ff00ff0000000000af00af0000000000ff00ff0000000000aa00aa5555555500000000550055000000000055555555000000005500550000ff00ff0000000000ff00ff0000000000aa00aa0000000000aa00aaaaaaaaaa00000000ffafffaf00000000aaaaaaaa00000000ffaaffaa00550055000000000005000500000000005500550000000000000000aaffaaff00000000aaafaaaf00000000aaffaaff00000000aaaaaaaaffffffff000000005505550500000000ffffffff0000000055005500ffffffff00000000ffafffaf00000000ffffffff00000000ffaaffaa00af00af0000000000af00af0000000000aa00aa0000000000aa00aa5505550500000000550555050000000055005500000000005500550033333333000000003333000000000000333333330000000033330000fffafffa00000000fffafffa00000000fffafffa00000000fffafffa0000000000000000fffafffa000000000000000000000000fffafffa0fff0fff000000000faf0faf0000000000ff00ff0000000000aa00aaffffffff00000000ffffffff00000000ffffffff00000000aaaaaaaa555555550000000055555555000000005555555500000000000000000000000000000000ffffffff000000000000000000000000ffaaffaaaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aa00aa00ffffffff00000000ffaaffaa00000000ffffffff00000000ffaaffaa000000000000000000af00af00000000000000000000000000aa00aa0000000000000000ff0fff0f000000000000000000000000ff00ff00ffffffff00000000afafafaf00000000ffffffff00000000aaaaaaaa5555555500000000555555550000000055005500000000005500550000ff00ff00000000000f000f0000000000ff00ff00000000000000000f0f0f0f000000000f0f0f0f000000000000000000000000000000000000000000000000ffffffff000000000000000000000000ff00ff00ff0fff0f00000000ff0fff0f00000000ff00ff0000000000ff00ff0000ff00ff0000000000aa00aa0000000000ff00ff0000000000aa00aaffffffff00000000ffffffff00000000ffaaffaa00000000ffaaffaaffffffff00000000ffffffff000000000000000000000000ffaaffaa
|0,2=>0xffaaffaa00000000ffaaffaaffffffff00000000f0f0f0f000000000ffffffff00000000f0f0f0f000000000000000000000000000000000ffffffff00000000aaaaaaaaffffffff00000000fff0fff000000000ffffffff00000000fff0fff000550055000000000055005500000000005500550000000000000000ffffffff00000000fafafafa00000000ffffffff00000000fafafafa00ff00ff0000000000fa00fa0000000000ff00ff0000000000fa00fa55505550000000005550555000000000555055500000000055505550ffffffff000000005550555000000000ffffffff00000000555055500000ffff000000000000ffff000000000000cccc000000000000cccc00fa00fa0000000000fa00fa0000000000fa00fa0000000000fa00faf0f0f0f000000000fffafffa00000000f0f0f0f000000000fffafffa0000000000000000fff0fff0000000000000000000000000fff0fff0fff0fff000000000fff0fff000000000fff0fff000000000fff0fff0aaaaaaaa00000000fffafffa00000000aaaaaaaa00000000fffafffaffffffff00000000ffffffff00000000ffffffff00000000ffaaffaaaaaaaaaa00000000ffffffff00000000aaaaaaaa00000000ffaaffaaffffffff000000005555555500000000ffffffff0000000055005500f0fff0ff00000000f0faf0fa00000000f0fff0ff00000000f0faf0faffffffff00000000ffffffff0000000000ff00ff0000000000aa00aa0000000000000000ffffffff000000000000000000000000aaaaaaaa00ff00ff0000000000ff00ff0000000000ff00ff0000000000aa00aafafafafa00000000fafafafa00000000fafafafa00000000fafafafa000000000000000000fa00fa00000000000000000000000000fa00faffffffff00000000fffafffa00000000ffffffff00000000fffafffa000000000000000000ff00ff00000000000000000000000000aa00aa
|_,_=>0
def stPool : Nat → Nat
|0=>0x3e885091c84383180400e401c18c02249870614080361c185022471b0e30f893c1c185020070718547891c1c18d0c0058c3a28e091c6cd0318647180e30089165cb0c222458718545091c5038c022459324308891c1c6101e247031a042000e0c28100203830a180030a042000608080
|1=>0xe308814c245a30e30a8a124c3830a04509165818d020040b26a46011424713463008a122c98718a0509165818c029c00e0e3008f4c245960e30a8a122c3831818509164d203186450b266818c2200587180510f122c38c223ce09164cf03184448b0e0c619440059b463008a122c38c
|2=>0x322d18c0229309160c681080050e361c60112945970e3088a122c9961804789164c3831a4400e0630084002470706340805c396870630089164cb0c3e2848b063160a102458c027478a122c99618444a51658601149848b18a009d14245ab0e0c681002c38c02a85091c1c628023c48b
|3=>0xe3008a1238d9a0630089161c6116a2848e0e0c61900b87071805a0a1238d87060598916ac38c023c48b561c18c320071e0e0c681002d587187c5091cc438c02245940e3008a122d0960630080161c601602848b0e30a8a122c907184408916acd03186450b0e30095142459e0e0c611
|4=>0x3e247070630300122c3831a05e001c1c18c02ec0070614080161c628147048b0e0c61132207170e3008a123898706340801658d031844c8b741c60114245871804539122c38c70045091c6c3831a0448b461c61014245871805b8a122c9960634889166038c022848e266818c02005b6
|5=>0x63030a122c38c507c08a122c3831a0510a122c38318fc08a1238383180538a122cb1a0630080161c18c021850916ac38c02284a51684b0318444be1c6c38c02247130e3008f122c62802f45091c4cd03186450b0e30a8f14245870634300142c99e0630c8a166cd03186450b2c1c611
|6=>0x14245932c0c601002458706300c8142458318640c41424587063160014245878e3008a122c383180630a122cd0706300c5142c987180478a122c18c031000a122c9870630c80142c38c0308509164d18c022848b821c601142459b0e0c619142458706300c014245930e3088a1294587
|7=>0x340c60114245932c0c68114245960e0c6015c24587180451c122c38c227c509166838318440801684383180400a1680383180450916783831844089166838318b050916583831a0403e1c4c38c022848b0f0c63c142459e0e0c62c14245c90e0c601142459a0e0c62f02287130e0c619
|8=>0x18bc50916ac3831804009161d48c022848e461c6011424587063088a5c24593340c6111424596340c6190228587180478a4c245870630ca214245ce0e3008a122cb031804008122c987063228a122c38318b05091c843831804509172c38c022848b941c18c022848b0e308811e245ab
|9=>0x261c601142528e0e0c681002cba30e3008a122c38c504408a122cd8718045094a2c3831a0400a5c2d587063408a122d687063008a122c38c02d05091c1c18c0201709165838c3e04509160c62f0310509165838c22044a5161c628023c509165818c029c509161c18c3204508164c383
|10=>0xe300d314245960e0c6910224587180688a123838c023c48e261c181662848e0e0c61902005870630c8a5c245870630c8014b85970e3008a122cf070634080142cb1a0630881122d096063008a122c38c02f05094a2d88718045091c783831804009261c18d03405091c1c6019e2848e
|11=>0xe0c6190228587063008aaa243830a045091c6c383180448e261c18d022848b0e0c601760050b0e0c601780048b0e3140114245932c0c611122c9870634080142cd87063408a1238987063008012399071804509165c9871804509167818c0228409160c6110310509164cd03186450b
|12=>0x195c08a1238987063008a122c383180400a1024587063088100245a10e0c619022848b361c18c022848b261c18c322848b0e0c62f022848b0e0c6018a2848e981c60114245960e0c61102245960e3008a12945d60e3008a122c98706300801424587063179902284be1c1c601142471a
|13=>0x123838302cc509161c6019e2848b261c601142528b341c18c22045091684987063008a122e68718045090e0c681a02848e0e3008a12945d90e0c6011424587063008a10245a30e3008a122cb1a063008a122c3831805e0a122c3831a4408a122d087063008a122c987b03008a122c383
|14=>0x18045091668383186408a161c18c02ec5091c1c18c3204509161c6011e2848b261c18d022848b0e0c619020050b641c60114245d62c1c601142459e0e0c601002848e0e0c68114245ab0e0c60114245870634080143838318040091678b07063008a122e607184408a122c996063008a
|15=>0x587063008a122c383186408a122c383180400a122c3831a04509161c18c2204509161c601142528b261c18c022848b0f606011424707063008a122e607180450916c8987
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>4
|4,0=>0x4a8045
|5,0=>0xd0c18982e305660a0c129822303e6070c0c981630266040c06980a300e6
|6,0=>0x44ae879d0bba107412e809cfdb9f473dae799cefb9d873a2e729ce1b9bc736cc6bdcd439a17336c651cc6b98672fee5e1cb8b96a72c6e571caab94e728ee501c9cb9327256e491c8eb916721ee421c80b8fa71e6e3b1c72b8de71aee341c64b8c27176e2d1c56b8a6713ee261c48b88a7106e1f1c3ab86e7
|6,1=>0x15ebab6755eeaa1d50ba9a7526ea31d42ba7e74eee9c1d34ba6454bae959d27ba487482e8e9d19ba2c7
|7,0=>0x959129224e44948919121223e447488daf199e2f4456889d111a21f4437785f109e2103c188822f0262013bfa87e50faa1f1bbdc77a90f321e243bc87690eb5dd2c39e772d0e3a1c3437e86ed0dba1b3435e86aeed3e1a3c33f866f0cbe1943b217634ec4a185430285f6ebce175c2e385b70b51d6642c48
|7,1=>0xbf517ca2f635e57bbb17562e6c5c67b7ef6de2d7c5a78b40f6622c845888b02f5e9eb9456b7acad5762ab3d4e8a8d14fde9bc52f8a4f147e28c3d108a111405e7cc4f369d7138e26dc4d38997130e25e3cb48
|8,0=>0x77c8ee91db23b2475d7eab1d363a33f3e8e6b3cb9f93471f7e30fc3e783c6ff8df0fbc5f74c6e09daf3b41f64bec27d751aca355bea38d371a4e345c6838cf719ce3354e628cb33946324c6418c7318c9f1546228c36f84a704ce027
|9,0=>0x7bf8f6f1ec1fd447a17f331e49fc5bf847
|10,0=>0x7c77
|_,_=>0
def dictMask : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def wireSAt (i : Nat) : Nat := if i < 90 then (dictB (i / 512) (i / 32 % 16) >>> (224 * (i % 32))) &&& dictMask else 0
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
|0=>0xe0534050e25221f0229024a2c9506260e290e4502290e0114255e1c02015e1c1629142502021825162914250e290626022926290e051629149506260e3e149506260e051c3416291825162914950626024a2c95062634290e25221f022926250e051c341629182514250e051c3418250e01162914251c340e02182516291425
|1=>0x14250e29027a2c250e292c050e2934050e251c0d1629262b0e051629149506260e250e05162902253c070e012c250e29262b0e052c070e291c341825162914251629182514250e05263e149506260e3e1495062646070e95062602290e2918251629021d0e7e029506260202162926290e0518250e01162914251629642b260d
|2=>0x291342b0e25222502290e05162902254e29026a0e250ebe322902253c040e01142506890e46022944250e460229322b02250e05149506265e1f020114250e05865b020d0e290e050e950626560d0e450229262b0e05325b02250e29021d06260229027a2c250e29029506260e460229182502210e021425026a16290e250e25
|3=>0xe290e3e149506260e460229360d262b0e050e021425322b022502782c250e290e65162902259a05982b061d260114250e051495062602290e450229021d0e29182502021425023e14950626029506260229022926250e053625262b0e052c250e29027834290e25182514250e290e051c0d1629025a020d0e2902782c250e29
|4=>0x1629142516360e0518251629861f06050e05162906261825162914250e950626229506260229262b0e051825020214250e4502291825422b0e65022546070e950626162902021425029506260e290ebe22250229022906260e2914950626026a0e250e0214250201142526290e05462b0e9506260e95162906265e0722250229
|5=>0xe050e290229182514250e051825262b0e05162914250e051629260d0e05269506260e050e210e0214255e1f222502290e050e250225a81f0645022918250e290229a4299807061d1629149506260e051c3316291425162902255e07322902250202142546050e95062618250e011425321d02252c070e29642b260d0e050e01
|6=>0xe250e29025a0e29022918250e6502250e0506292227022916290e050e021425142502290e650225262b0e050e05022522250229322b02251629061d0e29022906260e2906590e2914250e05322902251c0d16290e2516290225260214250e051c34162918251629262b0e05182516290e050e660225025a0e29229506260229
|7=>0x14251825022906260e0506291629061d260d0e050e2502250e66022516290225149506260e05182514250225260d0e0506590e290e011425162918250e45022914251825162914252c250e290e0d0229021d0e291c331629861f060506260e050e25022926250e05982b061d163618251629062626270e050e0214250e950626
|8=>0x225
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0x2940000000055000000000000000000000000000000000000000005
|6,0=>0x14cc50300004e2000000012cc4920000000000047210d00000fd00000f483b20dd00000d480000cc80000c48000000000000002e30a900000000000000027300000000948000088c1f300001b4000000000000000000183054c0000000000000000004c8112000000003c8000
|6,1=>0x1dc87341c0c0001b100001a88682198800000006420000604000000000005c40000000164c563
|7,0=>0x464d16344cd11243c90d242c9092418d033400c0003fc4fc33e88f733d48f323c0ced33a8ce73390ce2237ccdd2368cd733584d42344ccf2330cc93318cc33300cbd32ec8b830000b532c8caf32b0ca9329c8a43284ca01274c9a325cc952248c8f3230c8a221cc843204c7e31ecc792
|7,1=>0x64cd903634d8a361cd85260c98035f4d7a35dcd7435c4d6e35acd683594d62357cd5c3564d56354cd50353894b3520c0005189442504d3e34ecd3834d4d3234c092d34ac9283494d22347cd1c3
|8,0=>0x1f627d09f227c09ee27b09ea27a09e627909e227809de27709da27609d627509d227409ce27309ca27209c627109c227009be26f09ba26e09b626d09b226c09ae26b09aa26a09a626909a2268099e267099a26609962
|9,0=>0x20017fc5fe17f45fc17ec5fa17e45f81
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 16 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 127), wireSAt ((code >>> 9) &&& 127)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 14 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmPalB : Nat → Nat
|0=>0x30e0000028000000216000002100000020e000002080000020600000204000002000000013600000116000001140000010c0000010600000104000000d000000090000000800000004000000024000000200000001c000000180000001600000014000000100000000e0000000c00000008000000060000000400000000
|1=>0xaf1f0000af1d0000af1b0000af0b0000401f000022120000201d0000100100000f9100000f5b00000f1f00000f1d00000f1b00000f1100000f0f00000d5900000b9300000b5900000b1f00000b1b00000b1900000b0f00000b0100000a3b000009db0000091e00000610000004d00000049000000408000004000000033e
|2=>0x4200a3b04000f3f04000b3f04000b3b04000b170400001102220f3f02000f1f02000b490100cb1f0100c31700809f1f0080161100600b0f0060020e0060012e006000010040000e00200b1b0020000e001ccb1f00104b1f000ccb1f000c0b1f000c0b0e00020f1f00020b1d0001af1f00010f1f00010b1f0000cb1b0000bf1b
|3=>0x800c0b1f80040b1f410cab1b200c0b1f18400b1f184001161840001e1800091f14200b3b10200a3b10030f3f1000cb3b10000b3f10000b3b10000b1b1000081b0c000b1f0c0002160840091e08000b1f08000b1708000015
|_=>0
def pmB : Nat → Nat → Nat
|5,0=>0x1000005000000000000000000005
|6,0=>0xbb80c005000218080000403b1c0000816003060000b8900300002e0400000442807200ba152008800c34080000000610000000024000020030600740000000003060000b00003010000b80
|7,0=>0x14225663a608af50741167c927884cd04c580eaae0289e70b2e85a4c11112cb208d095040971d121448f2e1c191aef2d0b18888b5340d6198a09911380d5b718601060b1e9b10408213166441b6a4821c3232130684411a547810804a8121
|8,0=>0x6bc78ab33e985a59a3276c8ad42f6ce70d9a0e11b93dd2b5b529b238d8bba8fdbdf9f765c4fefb36883254
|9,0=>0x625bd6e33d1620b5
|10,0=>0x2c
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 7 (j % 128); fld (pmPalB (k / 32)) 32 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_221,9,runOps true dom_221 (0,roots_221) ops)] else [])++(if pm.testBit 1 then [(dom_219,9,runOps true dom_219 (0,roots_219) ops)] else [])++(if pm.testBit 2 then [(dzo_91_4,7,runOps true dzo_91_4 (0,roots_91) ops)] else [])++(if pm.testBit 3 then [(dom_215,8,runOps true dom_215 (0,roots_215) ops)] else [])++(if pm.testBit 4 then [(dom_222,8,runOps true dom_222 (0,roots_222) ops)] else [])++(if pm.testBit 5 then [(dom_150,4,runOps true dom_150 (0,roots_150) ops)] else [])++(if pm.testBit 6 then [(dzo_211_4,5,runOps true dzo_211_4 (0,roots_211) ops)] else [])++(if pm.testBit 7 then [(dzo_218_4,5,runOps true dzo_218_4 (0,roots_218) ops)] else [])++(if pm.testBit 8 then [(dom_91,7,runOps true dom_91 (0,roots_91) ops)] else [])++(if pm.testBit 9 then [(dom_159,8,runOps true dom_159 (0,roots_159) ops)] else [])++(if pm.testBit 10 then [(dzo_219_4,8,runOps true dzo_219_4 (0,roots_219) ops)] else [])++(if pm.testBit 11 then [(dom_207,9,runOps true dom_207 (0,roots_207) ops)] else [])++(if pm.testBit 12 then [(dom_203,8,runOps true dom_203 (0,roots_203) ops)] else [])++(if pm.testBit 13 then [(dzo_203_20,6,runOps true dzo_203_20 (0,roots_203) ops)] else [])++(if pm.testBit 14 then [(dom_141,5,runOps true dom_141 (0,roots_141) ops)] else [])++(if pm.testBit 15 then [(dzo_203_16,6,runOps true dzo_203_16 (0,roots_203) ops)] else [])++(if pm.testBit 16 then [(dom_218,6,runOps true dom_218 (0,roots_218) ops)] else [])++(if pm.testBit 17 then [(dom_211,6,runOps true dom_211 (0,roots_211) ops)] else [])++(if pm.testBit 18 then [(dzo_221_2,7,runOps true dzo_221_2 (0,roots_221) ops)] else [])++(if pm.testBit 19 then [(dzo_157_2,6,runOps true dzo_157_2 (0,roots_157) ops)] else [])++(if pm.testBit 20 then [(dom_205,8,runOps true dom_205 (0,roots_205) ops)] else [])++(if pm.testBit 21 then [(dom_151,5,runOps true dom_151 (0,roots_151) ops)] else [])++(if pm.testBit 22 then [(dom_83,4,runOps true dom_83 (0,roots_83) ops)] else [])++(if pm.testBit 23 then [(dom_137,4,runOps true dom_137 (0,roots_137) ops)] else [])++(if pm.testBit 24 then [(dzo_75_16,5,runOps true dzo_75_16 (0,roots_75) ops)] else [])++(if pm.testBit 25 then [(dom_155,7,runOps true dom_155 (0,roots_155) ops)] else [])++(if pm.testBit 26 then [(dom_158,5,runOps true dom_158 (0,roots_158) ops)] else [])++(if pm.testBit 27 then [(dom_90,4,runOps true dom_90 (0,roots_90) ops)] else [])++(if pm.testBit 28 then [(dom_214,5,runOps true dom_214 (0,roots_214) ops)] else [])++(if pm.testBit 29 then [(dzo_205_2,6,runOps true dzo_205_2 (0,roots_205) ops)] else [])++(if pm.testBit 30 then [(dzo_201_16,5,runOps true dzo_201_16 (0,roots_201) ops)] else [])++(if pm.testBit 31 then [(dom_73,4,runOps true dom_73 (0,roots_73) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_223 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_221 _ g hchk
    · exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_91_4_91 _ g hchk
    · exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · exact cpcs (by decide +kernel) lowS_222 _ g hchk
    · exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_211_4_83 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_218_4_90 _ g hchk
    · exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · exact cpcs (by decide +kernel) lowS_159 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_219_4_91 _ g hchk
    · exact cpcs (by decide +kernel) lowS_207 _ g hchk
    · exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_203_20_73 _ g hchk
    · exact cpcs (by decide +kernel) lowS_141 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_203_16_73 _ g hchk
    · exact cpcs (by decide +kernel) lowS_218 _ g hchk
    · exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_221_2_141 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_157_2_141 _ g hchk
    · exact cpcs (by decide +kernel) lowS_205 _ g hchk
    · exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · exact cpcs (by decide +kernel) lowS_137 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_75_16_73 _ g hchk
    · exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · exact cpcs (by decide +kernel) lowS_158 _ g hchk
    · exact cpcs (by decide +kernel) lowS_90 _ g hchk
    · exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_205_2_141 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_201_16_73 _ g hchk
    · exact cpcs (by decide +kernel) lowS_73 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_221 9 s (0, roots_221) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_223 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_221 h

def symsG : List (List (Nat × Nat)) := [[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_223 == dom_223) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_223 goalM v ys) : RunD true dom_223 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_223 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 86 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 86 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 108 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 108 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 49 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 49 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 9 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
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

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
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

theorem lowS_239 : Lower true dom_239 roots_239 goal_239 11 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 64, 66)] (by decide +kernel) (by decide +kernel) lowS_237

def dzo_165_2:=0xcc000000cc0000000000000000000000cc000000cc
def gzo_165_2:=0xcc000000c80000000000000000000000c000000000
def gsh_165_2:=0x330000003200000000000000000000003000000000
theorem lowS_zo_165_2_165:Lower true dzo_165_2 roots_165 gzo_165_2 5:=lower_iso (d1:=dom_165) (roots1:=roots_165) (T1:=gsh_165_2) [(dom_165,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_165_2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [] (by decide +kernel) (by decide +kernel) lowS_165)
def dzo_243_4:=0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0
def gzo_243_4:=0xf000f000f000f000f000f000f000f000f000f000e000e000f000f000c00000
def gsh_243_4:=0xf000f000f000f000f000f000f000f000f000f000e000e000f000f000c0000
theorem lowS_zo_243_4_83:Lower true dzo_243_4 roots_243 gzo_243_4 6:=lower_iso (d1:=dom_243) (roots1:=roots_243) (T1:=gsh_243_4) [(dom_243,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_243_4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xf000f00000000000f000f00000000000f000f00000000000f000f00000000,0,32),(0xf000f000f000f000f000f000f000f00000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_83)
def dzo_181_2:=0xcc00cc00cc00cc000000000000000000cc00cc00cc00cc
def gzo_181_2:=0xcc00cc00cc00c8000000000000000000cc00c000cc0000
def gsh_181_2:=0x3300330033003200000000000000000033003000330000
theorem lowS_zo_181_2_165:Lower true dzo_181_2 roots_181 gzo_181_2 6:=lower_iso (d1:=dom_181) (roots1:=roots_181) (T1:=gsh_181_2) [(dom_181,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_181_2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x3300000033000000000000000000000033000000330000,0,16)] (by decide +kernel) (by decide +kernel) lowS_165)
def dzo_87_32:=0xff00ff0000000000ff00ff00000000
def gzo_87_32:=0xfe00fe0000000000fc00f000000000
def gsh_87_32:=0xfe00fe0000000000fc00f0
theorem lowS_zo_87_32_83:Lower true dzo_87_32 roots_87 gzo_87_32 5:=lower_iso (d1:=dom_87) (roots1:=roots_87) (T1:=gsh_87_32) [(dom_87,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_87_32) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xf000f00000000000f000f0,0,4)] (by decide +kernel) (by decide +kernel) lowS_83)
def dzo_245_2:=0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc
def gzo_245_2:=0xcc00cc00cc00cc00cc00cc00cc00c800cc00cc00cc00cc00cc00c000cc0000
def gsh_245_2:=0x33003300330033003300330033003200330033003300330033003000330000
theorem lowS_zo_245_2_165:Lower true dzo_245_2 roots_245 gzo_245_2 7:=lower_iso (d1:=dom_245) (roots1:=roots_245) (T1:=gsh_245_2) [(dom_245,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_245_2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x33000000330000003300000033000000330000003300000033000000330000,0,16),(0x33003300330033000000000000000000330033003300330000000000000000,0,64)] (by decide +kernel) (by decide +kernel) lowS_165)
def dzo_115_4:=0xf000f000f000f000f000f000f000f0
def gzo_115_4:=0xf000f000e000e000f000f000c00000
def gsh_115_4:=0xf000f000e000e000f000f000c0000
theorem lowS_zo_115_4_83:Lower true dzo_115_4 roots_115 gzo_115_4 5:=lower_iso (d1:=dom_115) (roots1:=roots_115) (T1:=gsh_115_4) [(dom_115,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_115_4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xf000f00000000000f000f00000000,0,32)] (by decide +kernel) (by decide +kernel) lowS_83)
def dzo_244_2:=0x44004400440044004400440044004400440044004400440044004400440044
def gzo_244_2:=0x44004400440044004400440044004000440044004400440044004000440000
def gsh_244_2:=0x11001100110011001100110011001000110011001100110011001000110000
theorem lowS_zo_244_2_164:Lower true dzo_244_2 roots_244 gzo_244_2 6:=lower_iso (d1:=dom_244) (roots1:=roots_244) (T1:=gsh_244_2) [(dom_244,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_244_2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x11000000110000001100000011000000110000001100000011000000110000,0,16),(0x11001100110011000000000000000000110011001100110000000000000000,0,64)] (by decide +kernel) (by decide +kernel) lowS_164)
def dzo_211_32:=0xf000f00000000000f000f00000000000f000f00000000000f000f00000000
def gzo_211_32:=0xf000f00000000000f000f00000000000e000e00000000000c000000000000
def gsh_211_32:=0xf000f00000000000f000f00000000000e000e00000000000c0000
theorem lowS_zo_211_32_83:Lower true dzo_211_32 roots_211 gzo_211_32 5:=lower_iso (d1:=dom_211) (roots1:=roots_211) (T1:=gsh_211_32) [(dom_211,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_211_32) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xf000f00000000000f000f00000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_83)
def dzo_215_32:=0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000
def gzo_215_32:=0xff00ff0000000000ff00ff0000000000fe00fe0000000000fc00f000000000
def gsh_215_32:=0xff00ff0000000000ff00ff0000000000fe00fe0000000000fc00f0
theorem lowS_zo_215_32_83:Lower true dzo_215_32 roots_215 gzo_215_32 6:=lower_iso (d1:=dom_215) (roots1:=roots_215) (T1:=gsh_215_32) [(dom_215,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_215_32) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xf000f00000000000f000f00000000000f000f00000000000f000f0,0,4),(0xff00ff0000000000ff00ff00000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_83)
def dzo_229_2:=0xcc000000cc000000cc000000cc000000cc000000cc000000cc000000cc
def gzo_229_2:=0xcc000000cc000000cc000000c8000000cc000000cc000000c000000000
def gsh_229_2:=0x3300000033000000330000003200000033000000330000003000000000
theorem lowS_zo_229_2_165:Lower true dzo_229_2 roots_229 gzo_229_2 6:=lower_iso (d1:=dom_229) (roots1:=roots_229) (T1:=gsh_229_2) [(dom_229,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_229_2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x3300000033000000000000000000000033000000330000000000000000,0,64)] (by decide +kernel) (by decide +kernel) lowS_165)
def dzo_83_32:=0xf000f00000000000f000f00000000
def gzo_83_32:=0xe000e00000000000c000000000000
def gsh_83_32:=0xe000e00000000000c0000
theorem lowS_zo_83_32_83:Lower true dzo_83_32 roots_83 gzo_83_32 4:=lower_iso (d1:=dom_83) (roots1:=roots_83) (T1:=gsh_83_32) [(dom_83,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_83_32) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [] (by decide +kernel) (by decide +kernel) lowS_83)
namespace S_247
def pairsG : List (Nat × Nat) := [(1,65), (1,129), (2,18), (2,66), (3,19), (3,67), (3,131), (4,36), (4,132), (5,37), (5,69), (5,133), (6,22), (6,38), (6,70), (6,134), (7,23), (7,39), (7,71), (7,135), (16,18), (16,144), (17,19), (17,81), (17,145), (20,22), (20,52), (20,148), (21,23), (21,53), (21,85), (21,149), (32,36), (32,160), (33,37), (33,97), (33,161), (34,38), (34,50), (34,98), (34,162), (35,39), (35,51), (35,99), (35,163), (48,50), (48,52), (48,176), (49,51), (49,53), (49,113), (49,177), (64,65), (64,66), (64,192), (68,69), (68,70), (68,100), (68,196), (80,81), (80,82), (80,208), (84,85), (84,86), (84,116), (84,212), (96,97), (96,98), (96,100), (96,224), (112,113), (112,114), (112,116), (112,240), (128,129), (128,132), (128,144), (128,160), (128,192), (130,131), (130,134), (130,146), (130,162), (130,194)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfffffffffffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_247.map (· &&& dom_247)
def goalM : Nat := goal_247 &&& dom_247
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
|3,0=>0xb7c40
|4,0=>0xbeb17a8fa254f33369471d2eb1851e
|5,0=>0xe91ecc2cebbb7a6b48c2a645398dbd877ed7bee17933f6e9685d44b4ee7d4629543def3b47b2a5c327ca923dac21d641e3851423413f1c13c8902755
|6,0=>0xfc600f5d7ff3ab7f37e4ea473de1cad4ba1cb1e7c3b8dc26a7baf4cb321fb23acb1b8bb06fdae703ae504ae2f1ad2c9a8f01a7096a5c24a29e5a1e02a11fc939d391b48914568bcab8a8fc81fd07ed307c34b762ee759e27441e71e37702e66f25b6b7c06218e61f7f5da155a4a257dfa54da1533b7514e2510c7504934fade4e7ad4caca49e754699442ff03e2f83879837e8636f38356fc354dc30fac2925920c362043f1e6191ccef1b9251a56e1984c17e4317112156451510e14bff13bf41241c107d60fcf00fc680e0e90dfcc0adaf08da5087e3086a6082cb04feb0264a00c5e
|7,0=>0xcfc7ccf9f0ce458c6f46c297fc1bbdbf27ebee63bb746b8407b7c14b579cb4730b2b9eb26f5b1582ac2aea5c22a57ec9edab973c496ff596a7c965dd9508b941bf94159919e78f48e8f4718ce3f87cf585bdf85999827b8819908196b805c57f3487e9937e5757da8c7c3b27c15e76442760676f1f06db3565ab36437d61efa5b3dc5a2f059afd58935569f756016555244e9a94aeb54ae3b49d4049162482084744e4709b462a04515e42f524293d42429405d73dc453daf13d1873c1d43ac1e39e32385cb3708736f3835a90350eb341ee305c92ef5a2e4f12d4552cf472ac5e2a3d029aca2744b2635c232d11fdf91fcf91df4a1d2f01c8831c49f1c08d1b0651aa241a5bb1a0d41754815c831521614e35145ee1428b13dfb10f77107810e6050c5530c4ab0b8d00981407f6807c8b06f9806e90069a70433f0405a0061e
|7,1=>0xf7be6f77c6f01aedb7d5d7c83d53cdd33e7d0720
|8,0=>0xfd9a1ecedce53d3da29ed9aabcf21cc4421c38f8be656bae23b8407b8322b6176b4eb3b2efab00e0ae45cab890a6367a5619a28e4a12c89eaa39dd859ba8a96fd8904988d97a8d8158b08c8a61f88cee8835f8552983a2282fb57ed687ed137ce1a7622f75a276ee1c6ebb06ce066abc66621760ed15e6245de3155f91525b64f11a4dbf74db4c4841543b673eed23d1f93c19d35b8f3406d30e052d5362abb428edd259632098e1f4c11e5691d911169aa1655a15b9d15683156281095d0cdbc074b90500e0481802d46022d900665
|9,0=>0xeaa64d5667ac0838b06f84215837a872daa6b740363822492811668
|10,0=>0x6bf33
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xff00ff00ff00ff0000000000000000003300000033000055005500550055005500550055005500110011001100110011000000110000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff00000000ff00ff00ff00ff00ff00ff00ff00f000f000f000f000f000f000f000f000f000000000ff00ff0000000000ff00ff0000000000ff00ff000000000000000000000000ff00ff0000000000ff00ff00000000000000000000000000000000f000f000f000f000f000f000f000f000f000f00000000000f000f000000000cc00cc00cf00cf00cc000000cf000000cc00cc00cc00cc00cc000000cc0000ff00ff0000000000ff00ff0000000000ff00ff0000000000f000f00000000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000f000f0ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f000f000f000f0ff00ff00ff00ff00ff00ff00ff000000000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff00ff00ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00aa00aa00aa00aa00aa00aa00aa00aa00aaff00ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000ff0000ff00ff00ff00ff00ff00ff00ff00ff00cc00cc00cc00cc00cc00cc00cc00cccc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00ccff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000ff00ff00f000f000ff00ff00f000f000ff00ff00f000f000ff00ff00f000f0f000f000f000f000f000f000f000f000f000f000f000f000f000f000000000ff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000ff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000ff00ff0000000000ff00ff0000000000f000f00000000000f000f0000000000f000f000f000f000f000f000f000f000f000f00000000000f000f00000000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f055005500550055005500550055005500550055005500550055005500000000ff00ff00ff00ff00ff000000ff000000cc00cc00cc00cc00cc000000cc00000f000f000f000f000f000f000f000f000f000f000f000f000f000f00000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000ff00ff00ff00ff00ff00f000ff00f000fc00fc00cc00cc00fc00f000cc0000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aaff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000
|0,1=>0xf0000000000ff00ff0000000000ff00ff000000000000ff000000ff000000ff000000ff000000cc000000cc000000cc000000cc0f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0000af00af00af00af00af00af00af00af00aa00aa00aa00aa00aa00aa00aa00aa0000000000000000ff00ff00ff00ff000000000000000000ff00f000ff00f00000000000000000ff000f00ff000f000000000000000000ff000000ff000055005500550055005500000055005500550055005500550055000000550000ff00ff00ff00ff00ff00f000ff00f000ff00ff00ff00ff00ff00f000ff00f000000000000000000000ff000000ff00000000000000000000000000000000ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000000000000055005500550055000000550000005500550055005500550000000000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff0000ff00ff00ff00ff00ff00f000ff00f000000000000000000000000000000000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00000fa00fa00fa00fa00fa00fa00fa00fa00000000000000000000000000000000fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00faff00ff00fa00fa00ff00ff00fa00fa00ff00ff0000000000ff00ff00000000ff00ff00ff00ff00ff00ff00ff00ff00330033003300330033000000330000cc00cc00ff00ff00cc00cc00ff00ff00cc00cc00cc00cc00cc00cc00cc00cccc00cc00ff00ff00cc000000ff000000cc00cc00cc00cc00cc000000cc00005500550055005500000000005500550055005500550055000000000000000033003300330033003300000033000000330033003300330033000000330000ff00ff00ff00ff000f000f000f000f00ff00ff00ff00ff0000000000000000cf00cf00cf00cf00cf00cf00cf00cf00cc00cc00cc00cc00cc00cc00cc00cc0f000f000f000f000f000f000f000f00000000000000000000000000000000cf00cf00cf00cf00cf000000cf000000cc00cc00cc00cc00cc000000cc0000ff00ff00ff00ff00ff00ff00ff00ff00f000f000f000f000f000f000f000f0000000000000000000000000550055005500550055005500000000000000005500550055005500050005000500050055005500550055000000000000000055005500550055005500550055005500550055005500550000000000000000ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff0000000000000000
|0,2=>0xff00ff0000000000ff00ff0000000000f000f00000000000f000f00f000f000f000f000f000f000f000f000f000f000f000f000f0000000f0000ff00ff00ff00ff005500550055005500ff00ff00ff00ff0055000000550000f000f00000000000f000f0000000f000f000f00000000000f000f000000000ff00ff00ff00ff00ff00ff00ff00f000ff00ff0000000000ff00ff00000000ff00ff00ff00ff00fa00fa00fa00fa00aa00aa00aa00aa00aa00aa00aa00aa5500550055005500550055005500550055005500550055005500500055005033003300ff00ff0033000000ff00ff00330033003300330033000000330000ff00ff00ff00ff00000000000f000f00ff00ff00ff00ff0000000000000000000000000f000f00000000000f000f0000000000000000000000000000000055005500550055000000000005000500550055005500550000000000000000ff00ff00ff00ff00ff00ff00ff000000ff00ff00ff00ff000000000000000000000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff0000cc00cc00cf00cf00cc00cc00cf00cf00cc00cc00cc00cc00cc00cc00cc00cc0000cc000000cf000000cc000000cf000000cc000000cc000000cc000000cc05000500050005000500050005000500aa00aa00aa00aa00aa00aa00aa00aaf000f00050005000f000f00050005000f000f00050005000f000f000000000f000f000f000f000f000ff00f000ff00f000f000f000f000f000f000f000f000000000f000f00000000000f000ff0000000000f000f00000000000f000f000000000000000005500550055005500000000000000000000000000000000ff00ff00ff00ff00f000f000f000f000000000000000000000000000000000ff00ff00ff00ff00f000f000f000f000ff00ff00ff00ff00f000f000f000f0ff00ff00ff00ff00ff00ff00f000f000ff00ff0000000000ff00ff000000000f000f00050005000f000f00050005000f000f00050005000f000f000000000000000000000000ff00ff00ff00ff000000000000000000ff000000ff000055005500550055005500550055005500550055005500550055000000550000ff00ff00ff00ff0000000f0000000f00ff00ff00ff00ff0000000000000000ff00ff00ff00ff00ff00ff00ff00ff00aa00aa00aa00aa00aa00aa00aa00aaff00ff00ff00ff00fa00fa00fa00fa00ff00ff00ff00ff0000000000000000000000000000000000000000ff00ff00ff00ff00ff00ff0000000000000000ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000f0000000f00000000000000000ff00ff00ff00ff00000000000000000000000000000000
|0,3=>0xff00ff0000000000ff00f00000000000ff00ff0000000000ff00f0f500f50000000000f500f50000000000f000f00000000000f000f000000000ff00ff0000000000ff00ff000000ff00ff00ff0000000000ff00ff00000000ff00fa00ff00fa00ff00fa00ff00fa00ff000000ff000000ff000000ff00000f000f000f000f000f000f000f000f000f000f000f000f00000000000000000f000f000f000f000f000f000f000f000f000f000a000a000f000f000a000aaa00aa00ff00ff00aa00aa00ff00ff00aa00aa00aa00aa00aa00aa00aa00aaff00ff00ff00ff00ff000000ff00ff00ff00ff00ff00ff00ff000000ff0000000000000000000000000f0000000f00000000000000000000000000000000ff00ff00ff00ff00ff00f000ff00f000ff000000ff000000ff000000ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f000f000ff00ff00f000f000000000550055000000000055005500000000000000000000000000000000cc00cc00dd00dd00cc00cc00dd00dd00cc00cc00cc00cc00cc00cc00cc00cc000000000000000000000000f000f000f000f000f000f000f000f000f000f00000cf000000cf000000cf000000cf000000cc000000cc000000cc000000ccf000f000f000f000ff00ff00ff00ff00f000f000f000f000f000f000f000f0f000f00000000000ff00ff0000000000f000f00000000000f000f000000000ff00ff00ff00ff00ff00ff00ff00f000ff00ff00ff00ff00ff00ff00ff00f0ff00ff00ff00ff00fc00fc00fc00fc00cc00cc00cc00cc00cc00cc00cc00cc05000500050005000500050005000500050005000500050000000000000000f000f000ff00ff00f000f000ff00ff00f000f000f000f000f000f000f000f0f500f500f500f500f500f500f500f500f000f000f000f000f000f000f000f05500550055005500550055005500550000000000000000000000000000000000000000f500f50000000000f500f50000000000f000f00000000000f000f0ff00ff00aa00aa00ff00ff00aa00aa00000000000000000000000000000000ff00ff00ff00ff00ff00ff0000000000000000000000000000000000000000ff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff00000000ff00ff00ff00ff00ff00ff00f000f000f000f000f000f000f000f000f000f00000cc000000ff000000cc000000ff000000cc000000cc000000cc000000ccff00ff00aa00aa00ff00ff00aa00aa00ff00ff00aa00aa00ff00ff00aa00aaff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00aa00ff00ff00aa00aaf000f000f000f000f000f000f000f000f000f000a000a000f000f000a000a0
|0,4=>0xff00ff00fa00fa00ff00ff00fa00fa00ff00ff00fa00fa00ff00ff00fa00faff00ff00ff00ff00ff00ff00ff00ff00fa00fa00fa00fa00fa00fa00fa00fa55005500550055005500550055005500500050005000500050005000500050cc00cc00cc00cc00ff00ff00ff00ff00cc00cc00cc00cc00cc00cc00cc00cc00000000000000000000000000000000ff00ff00ff00ff00ff00ff0000000000000000fa00fa0000000000fa00fa0000000000fa00fa0000000000fa00fa00000000ff00ff0000000000ff00ff0000000000aa00aa0000000000aa00aa0f000f000f000f000f000f00000000000f000f000f000f000f000f0000000005000500050005000500050005000500000000000000000000000000000000ff00ff0055005500ff00ff0055005500ff00ff0000000000ff00ff00000000ff00ff00ff00ff00ff00ff00f000f000ff00ff00ff00ff00ff00ff00f000f00000000000000000ff00ff00ff00ff000000000000000000ff00ff0000000000000000000000000000000000000000fa00fa00fa00fa00fa00fa00fa00fadd00dd00dd00dd00dd00dd00dd00dd00cc00cc00cc00cc00cc00cc00cc00cc0f000f000f000f000f000f000f000f000c000c000c000c000c000c000c000caa00aa00af00af00aa00aa00af00af00aa00aa00aa00aa00aa00aa00aa00aa00000000000000000000ff000000ff0000000000000000000000ff00000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000ff00ff00fa00fa00ff00ff00fa00fa00f000f000f000f000f000f000f000f000000000000000000f000f000f000f00000000000000000000000000000000cc00cc00cc00cc00cf00cf00cf00cf00cc00cc00cc00cc00cc00cc00cc00ccff00ff0000000000ff00ff00ff00ff00ff00ff0000000000ff00ff000000000f000f00000000000f000f000f000f000f000f00000000000f000f00000000fe00fe00fe00fe00fe00fe00fe00fe00cc00cc00cc00cc00cc00cc00cc00cc00000000500050000000000050005000f000f000f000f000f000f000f000f0ff00ff0055005500ff00ff0055005500ff00ff0055005500ff00ff00000000
|_,_=>0
def stPool : Nat → Nat
|0=>0xf01200a0311071f1e0a0311100108001d111c0f010b070905010b0a03110710060003070501001b03070501001a030501080b0a031119100100030718010b0a1107171001001107100116000315070501000311070f12000d0307050100030c0501000302010b0a070905010003050108000307050600030501040003020100
|1=>0x1200a0333070f010b320311310f010b0a2e0e240f010b0e07170f0b210a0311072d1e0b0a03072b010b0a1a0311070f202a0a11070f0116000a0311070f120b0a03110129080b0a0e070f160b210a03070501200a03072501280a03072501000a032407050100030e070f00230e090f0b220a03070500210a03070500211119
|2=>0x240f010b32030e072c0b2a0a0d03110710010011070901290b0a03110f013d0b0a0e090f3c010b0a033b11070f010a030705010b0a1a1d03110710010003113a070f010a0311190f01000a0311070f390b0a0311070f01003203111910010b0a0311070f36350a340311071001001107170f01000a030e190f0b210a03110710
|3=>0xa0311070f01450a030e070f44430e090f01280b0a030e0c1001000b03110f0108000a0311071001001a030e070f0100421311190f010b0a03111001080b0a0311070f01410a030e0f080b210a0311240f01280a030e07100021403f11070f010b0a031910013e0b0a0311070f06000a03110f01080b0a11090f010b0a260311
|4=>0x25010b0a030e07100b2a0a030e191001000b530311070f0100030e070f00214b030e4a071000210e07100116000b03075201510b0a031107012d1f0a030e070f44500b030e4f0f0b210a11070f014d0b0a031001083e0b0a030e071000214c490e240f010b030e0f480b210a0311072900210a0311071001001b031147070f46
|5=>0xb0a0311070f01570a030e100108000b0311070129200a5b11070f010b0a030e070f5a000311070f590b0a03110701580b0a030e071006000b030e070f0b550a0311072701000a0311070f01540a0311071000210a0311072c01200a0d1d11240f010b030e07270b210a03240705010b0a03110710002103110752010b0a0307
|6=>0xf01280a1124070f015f0b0a1d03110710010b0a0311070f015e0b0a030e070f01430a340311070f01000a1d030e070f0b210a1d0311190f010b0a0311070f010b0a3203110727010b0a260311070f010b0a5634030e070f0b210a0311070f5d460a03070501000a0d030705010b0a1d0e070f0b2a0a030705010003115c0f01
|7=>0x11071001000a030e072701000b0a030e0710000b210a030e072c01200b0a030e640f010b0a0d03110710010b0a030e240f010b4b03072c01630b0a0d030e070f0b210a030e07100b210a030e072744010b0a030e600f010b0a0311070f460b0a030e600f44010b0a031107100100030e0710000b211d0311070f01000a031107
|8=>0x3072701710b0a26031147070f010a0311070f01360a1d030710013e0b0a030e070f0b220a260e076f0f010b0a0e190f010b0a1a6e0311070f010b0a0d1d0e240f010b030e076d010b0a030e070f0b216c0a03110701290b0a26030e0752010b0a03116b070f010b0a0e070f01680b0a030e070f440b670d0311070f01000a03
|9=>0x76070f010b0a131d11070f010b0a0311070f01000a1a750311070f010b0a030e070f01570b0a03110710010b0a1a030e0c0f010b0a0d030710013e0b0a030e070f0b210a1a0d0311240f010b0a030e070f010066030e0773010b0a1d0e070f010b670311070f01200a1a030e070f00210a4003110f01080b0a030e720f010b0a
|10=>0xb0a1a030e070f00210a4c030e071001000b7b030e07103c010b0a030e0f017a0b0a030e0f44017a0b0a1d0311070f010b261d0e070f79010b0a0311070f01001b0a1107090f010b0a030e070f0b211b0a037811070f010b0a65030e071001000311070f010b0a77030e24071001000b0e2f090f010b0a030e0c0f01000b0a03
|11=>0xe190f01000b0a80030e070f0b210a530311070f010b0a34030e071001000b0311070f017f0b0a0311240701290b0a0e077e0f010b0a030e4a070f00210a030e190f44010b0a030e071001200b0a7d0311070f010b0a030e070f0b2a0a030e070f200b2a0a0e070f0116000b0a0e070f01160b0a037c070f010b0a030710013e
|12=>0xa030e0710010040030e070f5a0b0a030e070f06000b0a650e190f010b0a030e070f060b0a0311070f01000a370d030e071001000b0311070f00210a030e1910010b0a0311240f010b0a26030e072c79010b0a03110727010b0a0333070f010b0a370311070f010b261a030e0f01830b0a030e0782010b0a030e810f010b0a03
|13=>0x11070f01890b0a0311070129000a030e1001080b0a033833070f010b0a0d03110701290b0a0311070f01080b0a0311070f01360a37031107012d0b0a030e0f0108000b0a030e071001000b1a880311070f010b0a030e0f01080b0a030e0f4401080b0a030e870f010b0a030e240f01280b0a1d031124070f010b030e0785010b
|14=>0xf010b0a030e8d070f010b0a030e0727010b0a030e070f010b261a030e4a240f010b0a030e078c010b0a690311070f01000a030e070f000b210a0d0311070f010b0a03110710010b0a030e0710018b0b0a03331147070f010a030e070f8a010b0a130338070f010b0a030705010b0a033311070f460b0a033811070f01000a03
|15=>0xa030e24070f01000b0a65030e0710010b0a030e24070f44010b0a1d030e24070f010b030e070f440b0a69030e070f010b0a660311070f010b0a1a62030e0710010b0a030710013e0b0a90030e070f010b0a030e070f79010b0a1a030e70070f010b0a8f030e070f010b0a030e070f010b0a86030e240f010b0a26038e0e07
|16=>0x62030e2f070f0b0a34030e070f010b0a62030e070f440b0a030e24070f010b1a030e070f01200b0a030e072c010b0a1a030e070f01930b0a030e070f4401930b0a030e070f01000b7b0a030e070f01920b0a030e070f010b7b0a030e240710010b0a030e070f010b0a91030e070f01080b0a030e070f3c010b0a65030e070f01
|17=>0x30e0710010b40030e070f010b0a300e24070f015f0b0a95030e070f010b0a0d030e070f01000b0a030e071001000b0a621d0e070f010b0a1d030e190f010b0a030e070f010b0a560d030e070f44010b0a030e071044010b0a030e190f010b0a030e071001000b0311070f010b0a37030e070f01940b0a34030e070f01000b0a
|18=>0xa033811070f010b0a030e0f01080b0a030e070f01970b0a03110701290b0a031124070f010b0a030e070f01000b0a1a030e0796010b0a033311070f010b0a030e070f44010b0a1a030e070f01200b0a1a030e070f01000a40030e0710010b0a40030e6b070f010b0a65030e4a070f010a030e078c010b0a0d030e0710010b0a
|19=>0xa400d030e070f010b0a030e0710010b0a030e070f01000b0a030e070f44010b0a030e24070f010b0a65030e070f010b0a62030e070f010b0a030e070f0b210a030e0710010b0a6999030e070f010b0a030e98070f010b0a030e98070f44010b0a030e0796010b0a4075030e070f010b0a030e0710010b0a1a0d030e240f010b
|20=>0x30e070f010b0a0311070f010b0a030e070f010b0a69030e070f010b0a1a030e070f010b
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>4
|4,0=>0x1d50185013500e500950045
|5,0=>0xab60a5609f60996093608d60876082507c60766070606a6064605e60586052604c60466040603a6034602e602860226
|6,0=>0x267726072597252724b7244723d7236722f72287221721b6214720d720671ff71f871f261eb71e471dd71d671cf71c871c171ba71b371ac71a5719e7197719071897182717b7174716d7166715f71587151714a7143713c7135712e7127712071197112710b710470fd70f670ef70e960e270db70d470cd70c670bf70b870b17
|6,1=>0x31e73186311730a730552fe72f772f072e972e272dc62d572ce72c772c072b972b272ab72a4729d7296728f72896282727c6275726e7
|7,0=>0x50184fa74f284ea84e284da84d284cb74c384bb84b384ac74a5749e7496848e8487748074788471746a7462845a8453744c7444843d7436742e8426841f741784107409740183fa73f283ea83e283db73d383cc73c573bd83b673ae83a773a073988392638b7383837c7374836c8364835d7355834d8345833d8335832d83258
|7,1=>0x6eb76e386db86d386cb86c476bc86b486ac86a5769d8696768e8686867f7678767176698662765b7653864b8644763d7635862d8626761e8616860f7608760175f985f185e985e185d985d185ca75c285ba85b285aa85a3759b8593858c7585757d8575856d8565855e7556854e8546853e8537752f852785207518851085097
|7,2=>0x727871f871787116709870186f986f27
|8,0=>0x927891f8917890f8908790088f978f188e988e188d898d088c888c088b888af98a788a078997891888988809878887088688860885888508848883f9836982e8826881e8816880e880687fe87f597ed87e497dc87d487cc87c487bc87b577ad87a4979c8794878c8784877c8774876d7765875d8755874e7746873e8737772f8
|8,1=>0x9c079b889b089a8899f9997898f8987897f897789707968896179598950994979418938992f9
|9,0=>0xa167a0e8a0689fe89f689ef79e789df89d789cf89c78
|10,0=>0xa1d7
|_,_=>0
def dictMask : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def wireSAt (i : Nat) : Nat := if i < 154 then (dictB (i / 512) (i / 32 % 16) >>> (248 * (i % 32))) &&& dictMask else 0
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
|0=>0xb1a40c2a033041c292f0a01c05112c03c690e0b40c2a0b1a4382d030a8540f070040451130a0440d0e0b444400e0b43c290b1a40c2a0b264449c0f264382d070a8449c0f2641c2a11100382d0f0a42c29111003c290e0b404020b0a40c29071444c2811034382d111003c290e0b42c2911100382d0f0a41c010b0a40451130a02c2911034382d0b0a444400f0a4382d
|1=>0x4e03c1cdd110a8382d0f0a41c29034b52828070b4443f0e0b404020b0a43c290e0b42c293301c449a070a82cc1010a4bc28070141c76030a4741c030a4440d0e0b44492070a404020e0b40c010b0a41c29380a0441d0e0b43c290b0a4382d030a844400f0a4382d071d00c29380a02c2911074382d013682cdd110a8382d0e0b43c29030042c29150301c010e0b43c29
|2=>0x70a81c6a0e0b40c2a111002c290f0a4382d111003c290e0b42c29111003c290e0b42d59071a8382d030a8443f030a80cc9380a0441d0e0b4052d4a0a01c2d0b0a4055e0b5640c2a0f2642c290e0b41c2a130002c2911034382d0e0b43c290b0a4382d0b1a43c69030a8382d030a41c29111003c290e0b43c290e0b404020b0a4449c0f264382d070a84c2b2d0bc382d
|3=>0x10082c290b1a43c69030a81d99650a00c2d0f0a4382d070a52828070b438b20f1a40c2a010082c290f0a404020b0a43c99070a81d84620a40c053301c44290e0b41d840344404290b0a43c290e0b43c29010082c290e0b40c290b0a42c990e0b41c2a0e0b40c92070a43c290e0b42cc12f0a01c050e0b40c010b0a404020b0a41c740e0b4e02811074382d0f264382d
|4=>0xb0a804020b0a4382d071d80c290766d9428030b4389e0f2641c2a330bc44290e0b42cdd110a8382d0e1083c29012882c99070a80dc0074042c2a071d00c69030a8344503074382d030a41c29030743d2d4a0a01c2d010082c29070a8443f0e0b43d59071a80c2a0e0b40c2a6a03c1da5010a80429620a00c050b0a40c1d0e0b42c290f0a4382d0b0a43c99070a83c29
|5=>0x30a4382d070a8382d030082c290e0b40c90070a444690e0b40c2a0f0a40c2d0b0a4449a0e0b41c2a0f0a41c290b0a41c05032401c29340700c010b0a4392d4a0a01c2d030a4440d0e0b42c290e0b40c2a0b5641c6a030a83c290e0b40c2a340700c010b0a438420f0a40c2a010082c29070a4382d650a00c2d0b0a43dd1011a80c2a030a58828030142c690e0b40c2a
|6=>0xe0b40c2a078480d010b0a83cc12f0a01c050767d8828030141c74030a42c29010082c29130ac440d0e0b43c29030042c2903388441d0e0b4443f0e0b5a80c07694042a010082c29010a41c74030a43c290b1a40c2a03374442a0e0b404820b1a40c2a0b1a40c2a1503c1c011503c1c010b0a438c12f0a01c050e1083c29010083c290b0a41d86620a40c05076180d11
|7=>0xb374442a0e0b4a429110fc382d071d80c29030a83c29130a4440d0e0b5d41f0d0a40c1d071d80c2907675882803014382d030a41c290f8642c9a070a82c290f0a42c2a014b52828070b4d007030042c29030b41c74030a4d007030042c290b0a4442a0e0b40c1d0f0a42c290e0b404020b0a41c74030a43c2907264382d070a83c990e0b41c2a110a844290e0b41c2a
|8=>0x10a80469030a81d010b0a8342d030742c9a070a81c99070a8742f030a4bc2b070143c99070a81c2a030a81c29070b43da5010a82c290e0b404020b0a40c1d0e0b43c290e0b41c420f0a4cc2f110a4382d015640c2a03114441d0e0b444400f0a4382d3301c44290e0b42c2911074382d111d80c290e0b42c29110fc382d071d80c290f0a4442911074382d110fc382d
|9=>0x307404290f0a41c74030a43c290b0a4442a0e0b4bc0f070140c010b0a41c05030140c010b0a40429030141c29030a82c69030a83c69030a80d12010a40d12010a41c020b0a5941f030b41c020b0a41c290f0a4049a070a81c76030a40499070a80c2d0b0a41c290b0a40c2d0f0a40429070a40c29070a405a5010a99428030b4382d030a83c290301438420f0a40da5
|10=>0x3074bc29070141d11010a43d010b0a83429030743c29030a81c2903074441d0e0b41c76030a49007070a4443f0e0b41c290e0b42c29030a83d010b0a844290e0b40429030a82c69030a82d010b0a83c290b0a81c69030a81c2d030b43da5010a83c29030743c290b0a8bc28070140c92070a5942b030b42c29030743c290b0a40c29030141c74030a41c6a030a80429
|11=>0xe0b4042a030a82c2a030743c290b0a40429070a40c2d0301404020b0a4042a0f0a43405
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0xa14235080c0000000000071017500000000000125000000003900000000000000000000000950114004
|6,0=>0x20840000000000000080200000001f100001ec477400007341c0c6f11b48694000000019c8000000063400006120000000180400000005d300000001650000158c00000000000000524000000014080001310000121044410880000f9000000003a400000000d903330c482d40000000
|6,1=>0x2e10b530000b140000ad40000ab229d0a3400000000000a032710984254c914238c00022cc87400008340000000
|7,0=>0x594d62357cd5c30001593558d53354494e35309493518d433500d3d34e8d3734d0d3134b8d2c24a4d26348cd203474d1a34609153448d102434d0a341cd043404cfe33eccf833d88f333c0cee23acce92398ce33380cdd3368cd73350cd1333c8000330cc9331c8c52308cbf32f0c000
|7,1=>0x814e02380080007f4dfa37e09f627ccdf037b89eb30001e83794de2377cddc3764dd6374cdd03734dca371cc000710dc136f8dbb36e0db536c8db026b4daa369cda52688da02674d9a365cd9436489902634d8a362098716148000608d8025f4c0005e8d77300017435c4d6e35acd683
|7,2=>0x870e1a285ce143844e0e382ce083
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
|0=>0x142000000024c0000000488000000090000000010c0000000210000000041000000008100000000c20000000164000000028800000004d000000009200000001100000000208000000040000000007e00000000c80000000180000000023000000004400000000840000000100000000012000000002200000000400000000068000000004000000000600000000080000000008000000000
|1=>0x230200000044dc0000008888000001092000000200c00000040000000004ff800000098500000013020000002280000000406000000080400000008200000000e540000001c000000001ff00000003ba00000007340000000df80000001b7000000034e000000068c0000000ce800000018d000000030a00000006040000000ac800000014d0000000222000000040400000007c80000000bf
|2=>0x200100000040004800008000380000801b30000100026000020004800002409380000403b7000008034600001006540000200c08000040101000008016e00001002c000002005180000400a0000008004000000804dc000008000000000812200000093fe00000126fc0000024db800000498d000000800000000083040000010048000002001000000236e00000046cc0000008cb8000001183
|3=>0x200022200020127fc0004024ce800080419d000100037e00010007fc00020003c80002811b7000050236600009006dc0001108db80002059b7000040b36400008046dc0000c004980001559b700002a336e00005464440000a2cdb80001419b7000028236e00005046540000a08c880001401b70000280366000050069c0000a009b8000120007000020236e000040448c0000800918000100093
|4=>0x23008034e042050069c0840200db8108040122020020064604004006dc0800201d980410049b70080001202008050069c0100000410020000002003004032e00600046dc00a0008d380140001b70020002366001050469c00204084900040403a70008080160001010028000202001200040003b7000800002400080001840009224d380012051b7000228a36e00045046dc000882cdb80010049b7
|5=>0x10410100ede0080408dbc0100211b7400228a36e4620a002cc8080408db89082201b7120048076e2400100edc4020201db8804040024100048076e10000000001800a009182100403b7040808074e080040069c1000220d38200040323040008036e08001002c01000200120200000322040000037e08000000080c00001d881182801b7
|_=>0
def pmB : Nat → Nat → Nat
|5,0=>0x80d060000000405000000010000020000000000000d0109
|6,0=>0x2009000f000d0006010e00000009070104080b0009350029003a10000000004700000100333100340210064c000006000044000600004d0000040000010009000000001900000600110012080600080000320000190406010000
|7,0=>0x54170900167c1c5f15540441000b376e571b8f3f255028620a0048130b55233d3c024687030965093b5e012a041c5553941c4f003d040b00082c001573118a583c51455b000d95420903a25c7f931e18273f0a242f020a676186a42609362209564e0d391d1a084009a1970938043e2e3b7e38082c0b0200595a0202211f1fae
|7,1=>0x16090c7b1479117d
|8,0=>0x2bb7acb2b06cab96a87a9d884a2d716d306460696f9eb683a970b18cb5a66c9291aaa582434930b38db47875ad6866723b52a0768e9a9f63778b74899c6ab52d84986b5d6bac9a9b90af816199832d2ba34b85
|9,0=>0x2d6b686ba7802c2cbab9b8
|10,0=>0x2c
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 8 (j % 128); fld (pmPalB (k / 32)) 39 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_245,9,runOps true dom_245 (0,roots_245) ops)] else [])++(if pm.testBit 1 then [(dom_215,8,runOps true dom_215 (0,roots_215) ops)] else [])++(if pm.testBit 2 then [(dom_246,8,runOps true dom_246 (0,roots_246) ops)] else [])++(if pm.testBit 3 then [(dom_165,5,runOps true dom_165 (0,roots_165) ops)] else [])++(if pm.testBit 4 then [(dom_182,7,runOps true dom_182 (0,roots_182) ops)] else [])++(if pm.testBit 5 then [(dom_243,8,runOps true dom_243 (0,roots_243) ops)] else [])++(if pm.testBit 6 then [(dzo_165_2,5,runOps true dzo_165_2 (0,roots_165) ops)] else [])++(if pm.testBit 7 then [(dom_183,8,runOps true dom_183 (0,roots_183) ops)] else [])++(if pm.testBit 8 then [(dom_231,9,runOps true dom_231 (0,roots_231) ops)] else [])++(if pm.testBit 9 then [(dzo_243_4,6,runOps true dzo_243_4 (0,roots_243) ops)] else [])++(if pm.testBit 10 then [(dom_180,5,runOps true dom_180 (0,roots_180) ops)] else [])++(if pm.testBit 11 then [(dzo_181_2,6,runOps true dzo_181_2 (0,roots_181) ops)] else [])++(if pm.testBit 12 then [(dzo_87_32,5,runOps true dzo_87_32 (0,roots_87) ops)] else [])++(if pm.testBit 13 then [(dom_199,6,runOps true dom_199 (0,roots_199) ops)] else [])++(if pm.testBit 14 then [(dzo_245_2,7,runOps true dzo_245_2 (0,roots_245) ops)] else [])++(if pm.testBit 15 then [(dom_178,4,runOps true dom_178 (0,roots_178) ops)] else [])++(if pm.testBit 16 then [(dom_181,6,runOps true dom_181 (0,roots_181) ops)] else [])++(if pm.testBit 17 then [(dom_214,5,runOps true dom_214 (0,roots_214) ops)] else [])++(if pm.testBit 18 then [(dzo_115_4,5,runOps true dzo_115_4 (0,roots_115) ops)] else [])++(if pm.testBit 19 then [(dom_151,5,runOps true dom_151 (0,roots_151) ops)] else [])++(if pm.testBit 20 then [(dom_119,6,runOps true dom_119 (0,roots_119) ops)] else [])++(if pm.testBit 21 then [(dzo_83_4,4,runOps true dzo_83_4 (0,roots_83) ops)] else [])++(if pm.testBit 22 then [(dom_227,6,runOps true dom_227 (0,roots_227) ops)] else [])++(if pm.testBit 23 then [(dom_229,8,runOps true dom_229 (0,roots_229) ops)] else [])++(if pm.testBit 24 then [(dzo_244_2,6,runOps true dzo_244_2 (0,roots_244) ops)] else [])++(if pm.testBit 25 then [(dom_195,5,runOps true dom_195 (0,roots_195) ops)] else [])++(if pm.testBit 26 then [(dom_83,4,runOps true dom_83 (0,roots_83) ops)] else [])++(if pm.testBit 27 then [(dzo_211_32,5,runOps true dzo_211_32 (0,roots_211) ops)] else [])++(if pm.testBit 28 then [(dzo_215_32,6,runOps true dzo_215_32 (0,roots_215) ops)] else [])++(if pm.testBit 29 then [(dom_213,6,runOps true dom_213 (0,roots_213) ops)] else [])++(if pm.testBit 30 then [(dzo_229_2,6,runOps true dzo_229_2 (0,roots_229) ops)] else [])++(if pm.testBit 31 then [(dom_179,5,runOps true dom_179 (0,roots_179) ops)] else [])++(if pm.testBit 32 then [(dzo_211_4,5,runOps true dzo_211_4 (0,roots_211) ops)] else [])++(if pm.testBit 33 then [(dom_211,6,runOps true dom_211 (0,roots_211) ops)] else [])++(if pm.testBit 34 then [(dom_150,4,runOps true dom_150 (0,roots_150) ops)] else [])++(if pm.testBit 35 then [(dom_242,5,runOps true dom_242 (0,roots_242) ops)] else [])++(if pm.testBit 36 then [(dom_147,4,runOps true dom_147 (0,roots_147) ops)] else [])++(if pm.testBit 37 then [(dom_244,6,runOps true dom_244 (0,roots_244) ops)] else [])++(if pm.testBit 38 then [(dzo_83_32,4,runOps true dzo_83_32 (0,roots_83) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_247 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_245 _ g hchk
    · exact cpcs (by decide +kernel) lowS_215 _ g hchk
    · exact cpcs (by decide +kernel) lowS_246 _ g hchk
    · exact cpcs (by decide +kernel) lowS_165 _ g hchk
    · exact cpcs (by decide +kernel) lowS_182 _ g hchk
    · exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_165_2_165 _ g hchk
    · exact cpcs (by decide +kernel) lowS_183 _ g hchk
    · exact cpcs (by decide +kernel) lowS_231 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_243_4_83 _ g hchk
    · exact cpcs (by decide +kernel) lowS_180 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_181_2_165 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_87_32_83 _ g hchk
    · exact cpcs (by decide +kernel) lowS_199 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_245_2_165 _ g hchk
    · exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · exact cpcs (by decide +kernel) lowS_181 _ g hchk
    · exact cpcs (by decide +kernel) lowS_214 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_115_4_83 _ g hchk
    · exact cpcs (by decide +kernel) lowS_151 _ g hchk
    · exact cpcs (by decide +kernel) lowS_119 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_83_4_83 _ g hchk
    · exact cpcs (by decide +kernel) lowS_227 _ g hchk
    · exact cpcs (by decide +kernel) lowS_229 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_244_2_164 _ g hchk
    · exact cpcs (by decide +kernel) lowS_195 _ g hchk
    · exact cpcs (by decide +kernel) lowS_83 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_211_32_83 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_215_32_83 _ g hchk
    · exact cpcs (by decide +kernel) lowS_213 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_229_2_165 _ g hchk
    · exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_211_4_83 _ g hchk
    · exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · exact cpcs (by decide +kernel) lowS_150 _ g hchk
    · exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · exact cpcs (by decide +kernel) lowS_147 _ g hchk
    · exact cpcs (by decide +kernel) lowS_244 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_83_32_83 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_245 9 s (0, roots_245) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_247 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_245 h

def symsG : List (List (Nat × Nat)) := [[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_247 == dom_247) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_247 goalM v ys) : RunD true dom_247 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_247 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
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

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
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

theorem lowS_253 : Lower true dom_253 roots_253 goal_253 11 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x3333000033330000333300003333000033330000333300003333000033330000, 128, 144)] (by decide +kernel) (by decide +kernel) lowS_237

def isoMvS_251 : List (Nat × Nat) := [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)]
theorem lowS_251 : Lower true dom_251 roots_251 goal_251 11 :=
  lower_iso isoMvS_251 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_223

def isoMvS_254 : List (Nat × Nat) := [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]
theorem lowS_254 : Lower true dom_254 roots_254 goal_254 11 :=
  lower_iso isoMvS_254 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_247

def dzo_253_2:=0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
def gzo_253_2:=0xccccccccccccccccccccccccccccccc8ccccccccccccccccccccc8c0cccc8800
def gsh_253_2:=0x3333333333333333333333333333333233333333333333333333323033332200
theorem lowS_zo_253_2_173:Lower true dzo_253_2 roots_253 gzo_253_2 10:=lower_iso (d1:=dom_253) (roots1:=roots_253) (T1:=gsh_253_2) [(dom_253,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_253_2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x3333000033330000333300003333000033330000333300003333000033330000,0,16),(0x3333333333333333000000000000000033333333333333330000000000000000,0,64)] (by decide +kernel) (by decide +kernel) lowS_173)
namespace S_255
def pairsG : List (Nat × Nat) := [(1,9), (1,65), (1,129), (2,18), (2,66), (3,11), (3,19), (3,67), (3,131), (4,36), (4,132), (5,13), (5,37), (5,69), (5,133), (6,22), (6,38), (6,70), (6,134), (7,15), (7,23), (7,39), (7,71), (7,135), (8,9), (8,72), (8,136), (10,11), (10,26), (10,74), (10,138), (12,13), (12,44), (12,76), (12,140), (14,15), (14,30), (14,46), (14,78), (14,142), (16,18), (16,144), (17,19), (17,25), (17,81), (17,145), (20,22), (20,52), (20,148), (21,23), (21,29), (21,53), (21,85), (21,149), (24,25), (24,26), (24,88), (24,152), (28,29), (28,30), (28,60), (28,92), (28,156), (32,36), (32,160), (33,37), (33,41), (33,97), (33,161), (34,38), (34,50), (34,98), (34,162), (35,39), (35,43), (35,51), (35,99), (35,163), (40,41), (40,44), (40,104), (40,168), (42,43), (42,46), (42,58), (42,106), (42,170), (48,50), (48,52), (48,176), (49,51), (49,53), (49,57), (49,113), (49,177), (56,57), (56,58), (56,60), (56,120), (56,184), (64,65), (64,66), (64,72), (64,192), (68,69), (68,70), (68,76), (68,100), (68,196), (80,81), (80,82), (80,88), (80,208), (84,85), (84,86), (84,92), (84,116), (84,212), (96,97), (96,98), (96,100), (96,104), (96,224), (112,113), (112,114), (112,116), (112,120), (112,240), (128,129), (128,132), (128,136), (128,144), (128,160), (128,192), (130,131), (130,134), (130,138), (130,146), (130,162), (130,194)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfffffffffffffffffffffffffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_255.map (· &&& dom_255)
def goalM : Nat := goal_255 &&& dom_255
def NN : Nat → Nat
|11=>1
|12=>1
|_=>0
def HT : Nat → Nat → Nat
|11,0=>0xd3cf5
|12,0=>0xd511d
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ffffffffffffffffffffffffffffffffccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x7654821076543210
|_=>0
def stOffB : Nat → Nat → Nat
|11,0=>8
|12,0=>0x88
|_,_=>0
def dictMask : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def wireSAt (i : Nat) : Nat := if i < 9 then (dictB (i / 512) (i / 32 % 16) >>> (256 * (i % 32))) &&& dictMask else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 4 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 9 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))

def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
|0=>0x201
|_=>0
def opOffB : Nat → Nat → Nat
|11,0=>1
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
|0=>0xff7f00
|_=>0
def pmB : Nat → Nat → Nat
|11,0=>2
|12,0=>1
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 2 (j % 128); fld (pmPalB (k / 32)) 8 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_254,11,runOps true dom_254 (0,roots_254) ops)] else [])++(if pm.testBit 1 then [(dom_191,11,runOps true dom_191 (0,roots_191) ops)] else [])++(if pm.testBit 2 then [(dom_253,11,runOps true dom_253 (0,roots_253) ops)] else [])++(if pm.testBit 3 then [(dom_251,11,runOps true dom_251 (0,roots_251) ops)] else [])++(if pm.testBit 4 then [(dom_247,11,runOps true dom_247 (0,roots_247) ops)] else [])++(if pm.testBit 5 then [(dom_239,11,runOps true dom_239 (0,roots_239) ops)] else [])++(if pm.testBit 6 then [(dom_223,11,runOps true dom_223 (0,roots_223) ops)] else [])++(if pm.testBit 7 then [(dzo_253_2,10,runOps true dzo_253_2 (0,roots_253) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_255 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_254 _ g hchk
    · exact cpcs (by decide +kernel) lowS_191 _ g hchk
    · exact cpcs (by decide +kernel) lowS_253 _ g hchk
    · exact cpcs (by decide +kernel) lowS_251 _ g hchk
    · exact cpcs (by decide +kernel) lowS_247 _ g hchk
    · exact cpcs (by decide +kernel) lowS_239 _ g hchk
    · exact cpcs (by decide +kernel) lowS_223 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_253_2_173 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_254 11 s (0, roots_254) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_255 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_254 h

def symsG : List (List (Nat × Nat)) := [[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]]
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
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
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

theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [0, 3] }, { op := GateOp.or, inputs := [6, 7] }, { op := GateOp.and, inputs := [8, 9] }, { op := GateOp.or, inputs := [1, 7] }, { op := GateOp.or, inputs := [4, 6] }, { op := GateOp.and, inputs := [11, 12] }, { op := GateOp.or, inputs := [5, 7] }, { op := GateOp.and, inputs := [2, 14] }, { op := GateOp.and, inputs := [0, 3] }, { op := GateOp.and, inputs := [5, 7] }, { op := GateOp.or, inputs := [10, 13] }, { op := GateOp.or, inputs := [18, 15] }, { op := GateOp.or, inputs := [19, 16] }, { op := GateOp.or, inputs := [20, 17] }]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 21⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
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

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_32095_aux

theorem PEqualNP.Outside.L_meta_32095 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_32095_aux.main
